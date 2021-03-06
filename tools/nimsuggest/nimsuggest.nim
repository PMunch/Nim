#
#
#           The Nim Compiler
#        (c) Copyright 2016 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Nimsuggest is a tool that helps to give editors IDE like capabilities.

import strutils, os, parseopt, parseutils, sequtils, net, rdstdin, sexp
# Do NOT import suggest. It will lead to wierd bugs with
# suggestionResultHook, because suggest.nim is included by sigmatch.
# So we import that one instead.
import compiler / [options, commands, modules, sem,
  passes, passaux, msgs, nimconf,
  extccomp, condsyms,
  sigmatch, ast, scriptconfig,
  idents, modulegraphs, compilerlog, vm]

when defined(windows):
  import winlean
else:
  import posix

const DummyEof = "!EOF!"
const Usage = """
Nimsuggest - Tool to give every editor IDE like capabilities for Nim
Usage:
  nimsuggest [options] projectfile.nim

Options:
  --port:PORT             port, by default 6000
  --address:HOST          binds to that address, by default ""
  --stdin                 read commands from stdin and write results to
                          stdout instead of using sockets
  --epc                   use emacs epc mode
  --debug                 enable debug output
  --log                   enable verbose logging to nimsuggest.log file
  --v2                    use version 2 of the protocol; more features and
                          much faster
  --refresh               perform automatic refreshes to keep the analysis precise
  --tester                implies --v2 and --stdin and outputs a line
                          '""" & DummyEof & """' for the tester

The server then listens to the connection and takes line-based commands.

In addition, all command line options of Nim that do not affect code generation
are supported.
"""
type
  Mode = enum mstdin, mtcp, mepc

var
  gPort = 6000.Port
  gAddress = ""
  gMode: Mode
  gEmitEof: bool # whether we write '!EOF!' dummy lines
  gLogging = false
  gRefresh: bool

const
  seps = {':', ';', ' ', '\t'}
  Help = "usage: sug|con|def|use|dus|chk|mod|highlight|outline|known file.nim[;dirtyfile.nim]:line:col\n" &
         "type 'quit' to quit\n" &
         "type 'debug' to toggle debug mode on/off\n" &
         "type 'terse' to toggle terse mode on/off"

type
  EUnexpectedCommand = object of Exception

proc parseQuoted(cmd: string; outp: var string; start: int): int =
  var i = start
  i += skipWhitespace(cmd, i)
  if cmd[i] == '"':
    i += parseUntil(cmd, outp, '"', i+1)+2
  else:
    i += parseUntil(cmd, outp, seps, i)
  result = i

proc sexp(s: IdeCmd|TSymKind): SexpNode = sexp($s)

proc sexp(s: Suggest): SexpNode =
  # If you change the order here, make sure to change it over in
  # nim-mode.el too.
  result = convertSexp([
    s.section,
    s.symkind,
    s.qualifiedPath.map(newSString),
    s.filePath,
    s.forth,
    s.line,
    s.column,
    s.doc
  ])

proc sexp(s: seq[Suggest]): SexpNode =
  result = newSList()
  for sug in s:
    result.add(sexp(sug))

proc listEpc(): SexpNode =
  # This function is called from Emacs to show available options.
  let
    argspecs = sexp("file line column dirtyfile".split(" ").map(newSSymbol))
    docstring = sexp("line starts at 1, column at 0, dirtyfile is optional")
  result = newSList()
  for command in ["sug", "con", "def", "use", "dus", "chk", "mod"]:
    let
      cmd = sexp(command)
      methodDesc = newSList()
    methodDesc.add(cmd)
    methodDesc.add(argspecs)
    methodDesc.add(docstring)
    result.add(methodDesc)

proc findNode(n: PNode): PSym =
  #echo "checking node ", n.info
  if n.kind == nkSym:
    if isTracked(n.info, n.sym.name.s.len): return n.sym
  else:
    for i in 0 ..< safeLen(n):
      let res = n.sons[i].findNode
      if res != nil: return res

proc symFromInfo(graph: ModuleGraph; gTrackPos: TLineInfo): PSym =
  let m = graph.getModule(gTrackPos.fileIndex)
  #echo m.isNil, " I knew it ", gTrackPos.fileIndex
  if m != nil and m.ast != nil:
    result = m.ast.findNode

proc execute(cmd: IdeCmd, file, dirtyfile: string, line, col: int;
             graph: ModuleGraph; cache: IdentCache) =
  if gLogging:
    logStr("cmd: " & $cmd & ", file: " & file & ", dirtyFile: " & dirtyfile & "[" & $line & ":" & $col & "]")
  gIdeCmd = cmd
  if cmd == ideUse and suggestVersion != 2:
    graph.resetAllModules()
  var isKnownFile = true
  let dirtyIdx = file.fileInfoIdx(isKnownFile)

  if dirtyfile.len != 0: msgs.setDirtyFile(dirtyIdx, dirtyfile)
  else: msgs.setDirtyFile(dirtyIdx, nil)

  gTrackPos = newLineInfo(dirtyIdx, line, col)
  gErrorCounter = 0
  if suggestVersion < 2:
    graph.usageSym = nil
  if not isKnownFile:
    graph.compileProject(cache)
  if suggestVersion == 2 and gIdeCmd in {ideUse, ideDus} and
      dirtyfile.len == 0:
    discard "no need to recompile anything"
  else:
    let modIdx = graph.parentModule(dirtyIdx)
    graph.markDirty dirtyIdx
    graph.markClientsDirty dirtyIdx
    if gIdeCmd != ideMod:
      graph.compileProject(cache, modIdx)
  if gIdeCmd in {ideUse, ideDus}:
    let u = if suggestVersion >= 2: graph.symFromInfo(gTrackPos) else: graph.usageSym
    if u != nil:
      listUsages(u)
    else:
      localError(gTrackPos, "found no symbol at this position " & $gTrackPos)

proc executeEpc(cmd: IdeCmd, args: SexpNode;
                graph: ModuleGraph; cache: IdentCache) =
  let
    file = args[0].getStr
    line = args[1].getNum
    column = args[2].getNum
  var dirtyfile = ""
  if len(args) > 3:
    dirtyfile = args[3].getStr(nil)
  execute(cmd, file, dirtyfile, int(line), int(column), graph, cache)

proc returnEpc(socket: Socket, uid: BiggestInt, s: SexpNode|string,
               return_symbol = "return") =
  let response = $convertSexp([newSSymbol(return_symbol), uid, s])
  socket.send(toHex(len(response), 6))
  socket.send(response)

template sendEpc(results: typed, tdef, hook: untyped) =
  hook = proc (s: tdef) =
    results.add(
      # Put newlines to parse output by flycheck-nim.el
      when results is string: s & "\n"
      else: s
    )

  executeEpc(gIdeCmd, args, graph, cache)
  let res = sexp(results)
  if gLogging:
    logStr($res)
  returnEpc(client, uid, res)

template checkSanity(client, sizeHex, size, messageBuffer: typed) =
  if client.recv(sizeHex, 6) != 6:
    raise newException(ValueError, "didn't get all the hexbytes")
  if parseHex(sizeHex, size) == 0:
    raise newException(ValueError, "invalid size hex: " & $sizeHex)
  if client.recv(messageBuffer, size) != size:
    raise newException(ValueError, "didn't get all the bytes")

var
  requests: Channel[string]
  results: Channel[Suggest]

proc toStdout() {.gcsafe.} =
  while true:
    let res = results.recv()
    case res.section
    of ideNone: break
    of ideChk: echo res.doc
    of ideKnown: echo res.quality == 1
    else: echo res

proc toSocket(stdoutSocket: Socket) {.gcsafe.} =
  while true:
    let res = results.recv()
    case res.section
    of ideNone: break
    of ideChk: stdoutSocket.send(res.doc & "\c\L")
    of ideKnown: stdoutSocket.send($(res.quality == 1) & "\c\L")
    else: stdoutSocket.send($res & "\c\L")

proc toEpc(client: Socket; uid: BiggestInt) {.gcsafe.} =
  var list = newSList()
  while true:
    let res = results.recv()
    case res.section
    of ideNone: break
    of ideChk:
      list.add sexp(res.doc)
    of ideKnown:
      list.add sexp(res.quality == 1)
    else:
      list.add sexp(res)
  returnEpc(client, uid, list)

proc writelnToChannel(line: string) =
  results.send(Suggest(section: ideChk, doc: line))

proc sugResultHook(s: Suggest) =
  results.send(s)

template setVerbosity(level: typed) =
  gVerbosity = level
  gNotes = NotesVerbosity[gVerbosity]

proc connectToNextFreePort(server: Socket, host: string): Port =
  server.bindaddr(Port(0), host)
  let (_, port) = server.getLocalAddr
  result = port

type
  ThreadParams = tuple[port: Port; address: string]

proc replStdin(x: ThreadParams) {.thread.} =
  if gEmitEof:
    echo DummyEof
    while true:
      let line = readLine(stdin)
      requests.send line
      toStdout()
      echo DummyEof
      flushFile(stdout)
  else:
    echo Help
    var line = ""
    while readLineFromStdin("> ", line):
      requests.send line
      toStdout()
      echo ""
      flushFile(stdout)

proc replTcp(x: ThreadParams) {.thread.} =
  var server = newSocket()
  server.bindAddr(x.port, x.address)
  var inp = "".TaintedString
  server.listen()
  while true:
    var stdoutSocket = newSocket()
    accept(server, stdoutSocket)

    stdoutSocket.readLine(inp)
    requests.send inp
    toSocket(stdoutSocket)
    stdoutSocket.send("\c\L")
    stdoutSocket.close()

proc argsToStr(x: SexpNode): string =
  if x.kind != SList: return x.getStr
  doAssert x.kind == SList
  doAssert x.len >= 4
  let file = x[0].getStr
  let line = x[1].getNum
  let col = x[2].getNum
  let dirty = x[3].getStr
  result = x[0].getStr.escape
  if dirty.len > 0:
    result.add ';'
    result.add dirty.escape
  result.add ':'
  result.add line
  result.add ':'
  result.add col

proc replEpc(x: ThreadParams) {.thread.} =
  var server = newSocket()
  let port = connectToNextFreePort(server, "localhost")
  server.listen()
  echo port

  var client = newSocket()
  # Wait for connection
  accept(server, client)
  while true:
    var
      sizeHex = ""
      size = 0
      messageBuffer = ""
    checkSanity(client, sizeHex, size, messageBuffer)
    let
      message = parseSexp($messageBuffer)
      epcApi = message[0].getSymbol
    case epcApi
    of "call":
      let
        uid = message[1].getNum
        args = message[3]

      gIdeCmd = parseIdeCmd(message[2].getSymbol)
      case gIdeCmd
      of ideChk:
        setVerbosity(1)
        # Use full path because other emacs plugins depends it
        gListFullPaths = true
        incl(gGlobalOptions, optIdeDebug)
      of ideSug, ideCon, ideDef, ideUse, ideDus, ideOutline, ideHighlight:
        setVerbosity(0)
      else: discard
      let cmd = $gIdeCmd & " " & args.argsToStr
      if gLogging:
        logStr "MSG CMD: " & cmd
      requests.send(cmd)
      toEpc(client, uid)
    of "methods":
      returnEpc(client, message[1].getNum, listEpc())
    of "epc-error":
      # an unhandled exception forces down the whole process anyway, so we
      # use 'quit' here instead of 'raise'
      quit("recieved epc error: " & $messageBuffer)
    else:
      let errMessage = case epcApi
                       of "return", "return-error":
                         "no return expected"
                       else:
                         "unexpected call: " & epcAPI
      quit errMessage

proc execCmd(cmd: string; graph: ModuleGraph; cache: IdentCache) =
  template sentinel() =
    # send sentinel for the input reading thread:
    results.send(Suggest(section: ideNone))

  template toggle(sw) =
    if sw in gGlobalOptions:
      excl(gGlobalOptions, sw)
    else:
      incl(gGlobalOptions, sw)
    sentinel()
    return

  template err() =
    echo Help
    sentinel()
    return

  var opc = ""
  var i = parseIdent(cmd, opc, 0)
  case opc.normalize
  of "sug": gIdeCmd = ideSug
  of "con": gIdeCmd = ideCon
  of "def": gIdeCmd = ideDef
  of "use": gIdeCmd = ideUse
  of "dus": gIdeCmd = ideDus
  of "mod": gIdeCmd = ideMod
  of "chk":
    gIdeCmd = ideChk
    incl(gGlobalOptions, optIdeDebug)
  of "highlight": gIdeCmd = ideHighlight
  of "outline": gIdeCmd = ideOutline
  of "quit": quit()
  of "debug": toggle optIdeDebug
  of "terse": toggle optIdeTerse
  of "known": gIdeCmd = ideKnown
  else: err()
  var dirtyfile = ""
  var orig = ""
  i = parseQuoted(cmd, orig, i)
  if cmd[i] == ';':
    i = parseQuoted(cmd, dirtyfile, i+1)
  i += skipWhile(cmd, seps, i)
  var line = -1
  var col = 0
  i += parseInt(cmd, line, i)
  i += skipWhile(cmd, seps, i)
  i += parseInt(cmd, col, i)

  if gIdeCmd == ideKnown:
    results.send(Suggest(section: ideKnown, quality: ord(fileInfoKnown(orig))))
  else:
    execute(gIdeCmd, orig, dirtyfile, line, col-1, graph, cache)
  sentinel()

proc recompileFullProject(graph: ModuleGraph; cache: IdentCache) =
  echo "recompiling full project"
  resetSystemArtifacts()
  vm.globalCtx = nil
  graph.resetAllModules()
  GC_fullcollect()
  compileProject(graph, cache)
  echo GC_getStatistics()

proc mainThread(graph: ModuleGraph; cache: IdentCache) =
  if gLogging:
    for it in searchPaths:
      logStr(it)

  proc wrHook(line: string) {.closure.} =
    if gMode == mepc:
      if gLogging: logStr(line)
    else:
      writelnToChannel(line)

  msgs.writelnHook = wrHook
  suggestionResultHook = sugResultHook
  graph.doStopCompile = proc (): bool = requests.peek() > 0
  var idle = 0
  while true:
    let (hasData, req) = requests.tryRecv()
    if hasData:
      msgs.writelnHook = wrHook
      suggestionResultHook = sugResultHook

      execCmd(req, graph, cache)
      idle = 0
    else:
      os.sleep 250
      idle += 1
    if idle == 20 and gRefresh:
      # we use some nimsuggest activity to enable a lazy recompile:
      gIdeCmd = ideChk
      msgs.writelnHook = proc (s: string) = discard
      suggestionResultHook = proc (s: Suggest) = discard
      recompileFullProject(graph, cache)

var
  inputThread: Thread[ThreadParams]

proc serveStdin(graph: ModuleGraph; cache: IdentCache) {.deprecated.} =
  if gEmitEof:
    echo DummyEof
    while true:
      let line = readLine(stdin)
      execCmd line, graph, cache
      echo DummyEof
      flushFile(stdout)
  else:
    echo Help
    var line = ""
    while readLineFromStdin("> ", line):
      execCmd line, graph, cache
      echo ""
      flushFile(stdout)

proc serveTcp(graph: ModuleGraph; cache: IdentCache) {.deprecated.} =
  var server = newSocket()
  server.bindAddr(gPort, gAddress)
  var inp = "".TaintedString
  server.listen()

  while true:
    var stdoutSocket = newSocket()
    msgs.writelnHook = proc (line: string) =
      stdoutSocket.send(line & "\c\L")

    accept(server, stdoutSocket)

    stdoutSocket.readLine(inp)
    execCmd inp.string, graph, cache

    stdoutSocket.send("\c\L")
    stdoutSocket.close()

proc serveEpc(server: Socket; graph: ModuleGraph; cache: IdentCache) {.deprecated.} =
  var client = newSocket()
  # Wait for connection
  accept(server, client)
  if gLogging:
    for it in searchPaths:
      logStr(it)
    msgs.writelnHook = proc (line: string) = logStr(line)

  while true:
    var
      sizeHex = ""
      size = 0
      messageBuffer = ""
    checkSanity(client, sizeHex, size, messageBuffer)
    let
      message = parseSexp($messageBuffer)
      epcAPI = message[0].getSymbol
    case epcAPI:
    of "call":
      let
        uid = message[1].getNum
        args = message[3]

      gIdeCmd = parseIdeCmd(message[2].getSymbol)
      case gIdeCmd
      of ideChk:
        setVerbosity(1)
        # Use full path because other emacs plugins depends it
        gListFullPaths = true
        incl(gGlobalOptions, optIdeDebug)
        var hints_or_errors = ""
        sendEpc(hints_or_errors, string, msgs.writelnHook)
      of ideSug, ideCon, ideDef, ideUse, ideDus, ideOutline, ideHighlight:
        setVerbosity(0)
        var suggests: seq[Suggest] = @[]
        sendEpc(suggests, Suggest, suggestionResultHook)
      else: discard
    of "methods":
      returnEpc(client, message[1].getNum, listEPC())
    of "epc-error":
      stderr.writeline("recieved epc error: " & $messageBuffer)
      raise newException(IOError, "epc error")
    else:
      let errMessage = case epcAPI
                       of "return", "return-error":
                         "no return expected"
                       else:
                         "unexpected call: " & epcAPI
      raise newException(EUnexpectedCommand, errMessage)

proc mainCommand(graph: ModuleGraph; cache: IdentCache) =
  clearPasses()
  registerPass verbosePass
  registerPass semPass
  gCmd = cmdIdeTools
  incl gGlobalOptions, optCaasEnabled
  isServing = true
  wantMainModule()
  add(searchPaths, options.libpath)
  #if gProjectFull.len != 0:
    # current path is always looked first for modules
  #  prependStr(searchPaths, gProjectPath)

  # do not stop after the first error:
  msgs.gErrorMax = high(int)
  # compile the project before showing any input so that we already
  # can answer questions right away:
  compileProject(graph, cache)

  open(requests)
  open(results)

  case gMode
  of mstdin: createThread(inputThread, replStdin, (gPort, gAddress))
  of mtcp: createThread(inputThread, replTcp, (gPort, gAddress))
  of mepc: createThread(inputThread, replEpc, (gPort, gAddress))
  mainThread(graph, cache)
  joinThread(inputThread)
  close(requests)
  close(results)

  when false:
    case gMode
    of mstdin:
      compileProject(graph, cache)
      #modules.gFuzzyGraphChecking = false
      serveStdin(graph, cache)
    of mtcp:
      # until somebody accepted the connection, produce no output (logging is too
      # slow for big projects):
      msgs.writelnHook = proc (msg: string) = discard
      compileProject(graph, cache)
      #modules.gFuzzyGraphChecking = false
      serveTcp(graph, cache)
    of mepc:
      var server = newSocket()
      let port = connectToNextFreePort(server, "localhost")
      server.listen()
      echo port
      compileProject(graph, cache)
      serveEpc(server, graph, cache)

proc processCmdLine*(pass: TCmdLinePass, cmd: string) =
  var p = parseopt.initOptParser(cmd)
  while true:
    parseopt.next(p)
    case p.kind
    of cmdEnd: break
    of cmdLongoption, cmdShortOption:
      case p.key.normalize
      of "port":
        gPort = parseInt(p.val).Port
        gMode = mtcp
      of "address":
        gAddress = p.val
        gMode = mtcp
      of "stdin": gMode = mstdin
      of "epc":
        gMode = mepc
        gVerbosity = 0          # Port number gotta be first.
      of "debug": incl(gGlobalOptions, optIdeDebug)
      of "v2": suggestVersion = 2
      of "tester":
        suggestVersion = 2
        gMode = mstdin
        gEmitEof = true
      of "log": gLogging = true
      of "refresh": gRefresh = true
      else: processSwitch(pass, p)
    of cmdArgument:
      options.gProjectName = unixToNativePath(p.key)
      # if processArgument(pass, p, argsCount): break

proc handleCmdLine(cache: IdentCache; config: ConfigRef) =
  if paramCount() == 0:
    stdout.writeline(Usage)
  else:
    processCmdLine(passCmd1, "")
    if gMode != mstdin:
      msgs.writelnHook = proc (msg: string) = discard
    if gProjectName != "":
      try:
        gProjectFull = canonicalizePath(gProjectName)
      except OSError:
        gProjectFull = gProjectName
      var p = splitFile(gProjectFull)
      gProjectPath = canonicalizePath p.dir
      gProjectName = p.name
    else:
      gProjectPath = canonicalizePath getCurrentDir()

    # Find Nim's prefix dir.
    let binaryPath = findExe("nim")
    if binaryPath == "":
      raise newException(IOError,
          "Cannot find Nim standard library: Nim compiler not in PATH")
    gPrefixDir = binaryPath.splitPath().head.parentDir()
    #msgs.writelnHook = proc (line: string) = logStr(line)
    if gLogging:
      logStr("START " & gProjectFull)

    loadConfigs(DefaultConfig, cache, config) # load all config files
    # now process command line arguments again, because some options in the
    # command line can overwite the config file's settings
    options.command = "nimsuggest"
    let scriptFile = gProjectFull.changeFileExt("nims")
    if fileExists(scriptFile):
      runNimScript(cache, scriptFile, freshDefines=false, config)
      # 'nim foo.nims' means to just run the NimScript file and do nothing more:
      if scriptFile == gProjectFull: return
    elif fileExists(gProjectPath / "config.nims"):
      # directory wide NimScript file
      runNimScript(cache, gProjectPath / "config.nims", freshDefines=false, config)

    extccomp.initVars()
    processCmdLine(passCmd2, "")

    let graph = newModuleGraph(config)
    graph.suggestMode = true
    mainCommand(graph, cache)

when false:
  proc quitCalled() {.noconv.} =
    writeStackTrace()

  addQuitProc(quitCalled)

condsyms.initDefines()
defineSymbol "nimsuggest"
handleCmdline(newIdentCache(), newConfigRef())
