#
#
#            Nim's Runtime Library
#        (c) Copyright 2015 Nim Contributors
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Abstract
## ========
##
## This module implements types which encapsulate an optional value.
##
## A value of type ``Option[T]`` either contains a value `x` (represented as
## ``some(x)``) or is empty (``none(T)``).
##
## This can be useful when you have a value that can be present or not. The
## absence of a value is often represented by ``nil``, but it is not always
## available, nor is it always a good solution.
##
##
## Tutorial
## ========
##
## Let's start with an example: a procedure that finds the index of a character
## in a string.
##
## .. code-block:: nim
##
##   import options
##
##   proc find(haystack: string, needle: char): Option[int] =
##     for i, c in haystack:
##       if c == needle:
##         return some(i)
##     return none(int)  # This line is actually optional,
##                       # because the default is empty
##
## .. code-block:: nim
##   optionCase "abc".find('c'):
##     some x: assert(x == 2)
##     none: assert false # This will not be reached, because the string
##                        # contains 'c'
##
## This pattern assures that you only access the value of on option in a safe
## way. If you want to use a more familiar exception pattern you can use:
##
## .. code-block:: nim
##
##   try:
##     assert("abc".find('c').get() == 2)  # Immediately extract the value
##   except UnpackError:  # If there is no value
##     assert false  # This will not be reached, because the value is present
##
## The ``get`` operation demonstrated above returns the underlying value, or
## raises ``UnpackError`` if there is no value. There is another option for
## obtaining the value: ``unsafeGet``, but you must only use it when you are
## absolutely sure the value is present (e.g. after checking ``isSome``). If
## you do not care about the tiny overhead that ``get`` causes, you should
## simply never use ``unsafeGet``.
##
## To compare an option manually you can use ``none(T)`` to create an empty
## value to compare against:
##
## .. code-block:: nim
##
##   let result = "team".find('i')
##
##   # Nothing was found, so the result is `none`.
##   assert(result == none(int))
##   # It has no value:
##   assert(result.isNone)
##
##   try:
##     echo result.get()
##     assert(false)  # This will not be reached
##   except UnpackError:  # Because an exception is raised
##     discard
##
## This module also implements common mapping functionality to use a procedure
## on an optional value, carrying over the absence state if there is no value:
##
## .. code-block:: nim
##
##   let
##     x = some(10)
##     y = none(int)
##   assert(map(x, proc(x: int): int = x + 10) == some(20))
##   assert(map(y, proc(x: int): int = x + 10) == none(int))
##
## To help with safe evaluations of Options this module also implements some
## special forms for creating what would otherwise be branching and boolean
## structures. There is a general purpose ``optCmp`` which takes an option and
## a value, along with a comparator function. When the option is a none it will
## return a none. Otherwise it will compare the value of the option with the
## value, using the comparator function, and return the option if the comparator
## returns true. This means that we can insert checks in a stream of options:
##
## ..code-block:: nim
##   proc leq(x, y: int): bool =
##     x <= y
##   proc geq(x, y: int): bool =
##     x >= y
##   assert optCmp(some(10), 20, leq) == some(10)
##   assert optCmp(some(30), 20, leq) == none(int)
##   assert optCmp(none(int), 20, leq) == none(int)
##   let x = 10
##   assert optCmp(optCmp(x, 5, geq), 20, leq) == some(x)
##   # This only returns some if x is in the range 5..20
##
## But maybe more importantly there are also ``and`` and ``or`` equivalents that
## early terminate in a similar way to regular ``and `` and ``or``. These are
## called ``optOr`` and ``optAnd``. They don't compare values but work on the
## state of the option. ``optOr`` checks each argument until one of them is an
## option with a value, then it returns that value. If none of the options have
## a value it return an options without a value. ``optAnd`` checks each
## argument until one of them is an option without a value then returns it. If
## all the options have a value it returns the last one.
##
## ..code-block:: nim
##   var evaluated = false
##   proc shouldntHappen(): Option[int] =
##     evaluated = true
##     none(int)
##   # optOr terminates early so shouldntHappen is never run
##   assert optOr(10, shouldntHappen()) == some(10)
##   assert evaluated == false
##   # optAnd terminates early so shouldntHappen is never run
##   assert optAnd(none(int), shouldntHappen()) == none(int
##   assert evaluated == false
##   # We can also compose as deep as we want
##   assert(
##     optOr(none(int), none(int),
##       optAnd(10, 20),
##       shouldntHappen()
##     ) == some(20))
##   assert evaluated == false
##
## This can be used to create boolean expressions
##
## .. code-block:: Nim
##   proc eq(x, y: string): bool = x == y
##   let x = "green"
##   # This will print out "5"
##   echo either(optAnd(optCmp(x, "green", eq), 5), 3)
##   # This will print out "3"
##   echo either(optAnd(optCmp("blue", "green", eq), 5), 3)
##
## In the first example ``optAnd`` runs it's first expression, ``optCmp`` which
## returns an option with the value "green", since it has a value ``optAnd``
## runs the second expression ``5`` which is automatically converted to
## ``some(5)``. Since both of these have a value ``optAnd`` returns the last one
## ``some(5)``, the ``either`` procedure is just an alias for ``get`` with a
## default value, since it's first argument has a value it returns that value.
##
## In the second example ``optAnd`` runs it's first expression, ``optCmp`` which
## return an option without a value since the comparisson fails. ``optAnd`` then
## returns an option without a value, and the ``either`` procedure uses the
## default value of 3.
##
## This example is the same as a ``if x == "green": 5 else: 3`` but where x
## might not be set at all.

import typetraits
import macros

type
  SomePointer = ref | ptr | pointer

type
  Option*[T] = object
    ## An optional type that stores its value and state separately in a boolean.
    when T is SomePointer:
      val: T
    else:
      val: T
      has: bool

  UnpackError* = ref object of ValueError

proc some*[T](val: T): Option[T] =
  ## Returns a ``Option`` that has this value.
  when T is SomePointer:
    assert val != nil
    result.val = val
  else:
    result.has = true
    result.val = val

proc option*[T](val: T): Option[T] =
  ## Can be used to convert a pointer type to an option type. It
  ## converts ``nil`` to the none-option.
  result.val = val
  when T isnot SomePointer:
    result.has = true

proc none*(T: typedesc): Option[T] =
  ## Returns an ``Option`` for this type that has no value.
  # the default is the none type
  discard

proc none*[T]: Option[T] =
  ## Alias for ``none(T)``.
  none(T)

proc isSome*[T](self: Option[T]): bool {.inline.} =
  when T is SomePointer:
    self.val != nil
  else:
    self.has

proc isNone*[T](self: Option[T]): bool {.inline.} =
  when T is SomePointer:
    self.val == nil
  else:
    not self.has

proc unsafeGet*[T](self: Option[T]): T =
  ## Returns the value of a ``some``. Behavior is undefined for ``none``.
  assert self.isSome
  self.val

proc get*[T](self: Option[T]): T =
  ## Returns contents of the Option. If it is none, then an exception is
  ## thrown.
  if self.isNone:
    raise UnpackError(msg : "Can't obtain a value from a `none`")
  self.val

proc get*[T](self: Option[T], otherwise: T): T =
  ## Returns the contents of this option or `otherwise` if the option is none.
  if self.isSome:
    self.val
  else:
    otherwise

template either*(self, otherwise: untyped): untyped =
  get(self, otherwise)

proc map*[T](self: Option[T], callback: proc (input: T)) =
  ## Applies a callback to the value in this Option
  if self.isSome:
    callback(self.val)

proc map*[T, R](self: Option[T], callback: proc (input: T): R): Option[R] =
  ## Applies a callback to the value in this Option and returns an option
  ## containing the new value. If this option is None, None will be returned
  if self.isSome:
    some[R]( callback(self.val) )
  else:
    none(R)

proc flatten*[A](self: Option[Option[A]]): Option[A] =
  ## Remove one level of structure in a nested Option.
  if self.isSome:
    self.val
  else:
    none(A)

proc flatMap*[A, B](self: Option[A], callback: proc (input: A): Option[B]): Option[B] =
  ## Applies a callback to the value in this Option and returns an
  ## option containing the new value. If this option is None, None will be
  ## returned. Similar to ``map``, with the difference that the callback
  ## returns an Option, not a raw value. This allows multiple procs with a
  ## signature of ``A -> Option[B]`` (including A = B) to be chained together.
  map(self, callback).flatten()

proc filter*[T](self: Option[T], callback: proc (input: T): bool): Option[T] =
  ## Applies a callback to the value in this Option. If the callback returns
  ## `true`, the option is returned as a Some. If it returns false, it is
  ## returned as a None.
  if self.isSome and not callback(self.val):
    none(T)
  else:
    self

proc `==`*(a, b: Option): bool =
  ## Returns ``true`` if both ``Option``s are ``none``,
  ## or if they have equal values
  (a.isSome and b.isSome and a.val == b.val) or (not a.isSome and not b.isSome)

proc `$`*[T](self: Option[T]): string =
  ## Get the string representation of this option. If the option has a value,
  ## the result will be `Some(x)` where `x` is the string representation of the contained value.
  ## If the option does not have a value, the result will be `None[T]` where `T` is the name of
  ## the type contained in the option.
  if self.isSome:
    "Some(" & $self.val & ")"
  else:
    "None[" & name(T) & "]"

macro optionCase*[T](m: Option[T], body: untyped): untyped =
  ## A macro which provides a safe access pattern to
  ## the Option type. In branches where the Option is not ``some`` then the
  ## value is not available.
  ##
  ## ``optionCase`` makes the following conversion
  ##
  ## optionCase returnsOption():
  ##    some x:
  ##      <expr1 using x>
  ##    none:
  ##      <expr2 that does not use x>
  ##
  ## converts to --->
  ## let m = returnsOption()
  ## if m.isSome:
  ##   let x = m.unsafeGet()
  ##   <expr1 using x>
  ## else:
  ##   <expr2>
  ##
  assert body.len == 2
  let
    justHead = body[0][0]
    nothingHead = body[1][0]

  assert $justHead == "some",
    "First block must be `some`: keyword not found"
  assert $nothingHead == "none",
    "Second block must be `none`: keyword not found"

  let
    mVal = genSym(nskLet)
    validExpr = newDotExpr(mVal, ident("isSome"))
    valueExpr = newDotExpr(mVal, ident("unsafeGet"))
    justClause = nnkStmtList.newTree(
      nnkLetSection.newTree(
        nnkIdentDefs.newTree(
          body[0][1],
          newEmptyNode(),
          valueExpr
        )
      ),
      body[0][2]
    )
    nothingClause = body[1][1]

  var ifExpr = newNimNode(nnkIfExpr)
  ifExpr.add(newNimNode(nnkElifExpr).add(validExpr, justClause))
  ifExpr.add(newNimNode(nnkElseExpr).add(nothingClause))

  result = nnkStmtList.newTree(
    nnkLetSection.newTree(
      nnkIdentDefs.newTree(
        mVal,
        newEmptyNode(),
        m
      )
    ),
    ifExpr
  )

proc `>>=`*[T,U](self: Option[U], p: proc(value: U): Option[T]): Option[T] =
  ## Used for chaining monadic computations together. Will create a none if
  ## ``self`` is none, or if ``p`` returns a none. Otherwise it will return the
  ## some created by ``p``.
  if self.has:
      result = p(self.val)
  else:
      result = none(T)

proc optCmp*[T](self: Option[T], value: T, cmp: proc (val1, val2: T): bool):
  Option[T] =
  ## Comparison operation that return a some iff ``self`` is a some and the value
  ## of ``cmp`` applied to ``self`` and ``value`` returns true. The returned
  ## some has the value of ``self``
  if self.has:
    if cmp(self.val, value):
      self
    else:
      none(T)
  else:
    none(T)

template optCmp*[T](value: T, self: Option[T], cmp: proc (val1, val2: T): bool):
  Option[T] =
  optCmp(self, value, cmp)

template optCmp*[T](self: T, value: T, cmp: proc (val1, val2: T): bool):
  Option[T] =
  optCmp(some(self), value, cmp)

proc toOpt*[T](value: Option[T]): Option[T] =
  ## Procedure with overload to automatically convert something to an option if
  ## it's not already an option.
  return value

proc toOpt*[T](value: T): Option[T] =
  ## Procedure with overload to automatically convert something to an option if
  ## it's not already an option.
  some(value)

macro optOr*(options: varargs[untyped]): untyped =
  ## Goes through the options until one of them is a some. If none of the
  ## options are a some a none is returned. Note that if some of the options are
  ## a procedure that returns an Option they won't get evaluated if an earlier
  ## option is a some. If any of the options is not an option but another type
  ## they will be converted to an option of that type automatically.
  var procName = genSym(nskProc)
  result = nnkProcDef.newTree(procName, newEmptyNode(), newEmptyNode(),
    nnkFormalParams.newTree(newIdentNode("auto")),
    newEmptyNode(), newEmptyNode(), newStmtList())
  for option in options:
    result[6].add quote do:
      let opt = toOpt(`option`)
      if opt.has: return opt
  result = nnkStmtList.newTree(result, nnkCall.newTree(procName))

macro optAnd*(options: varargs[untyped]): untyped =
  ## Goes through all options until one of them is not a some. If one of the
  ## options is not a some it returns a none, otherwise it returns the last
  ## option. Note that if some of the options are a procedure that returns an
  ## Option they won't get evaluated if an earlier option is a none. If any of
  ## the options is not an option but another type they will be converted to an
  ## option of that type automatically.
  var procName = genSym(nskProc)
  result = nnkProcDef.newTree(procName, newEmptyNode(), newEmptyNode(),
    nnkFormalParams.newTree(newIdentNode("auto")),
    newEmptyNode(), newEmptyNode(), newStmtList())
  var lastOpt: NimNode
  for option in options:
    lastOpt = genSym(nskLet)
    result[6].add quote do:
      let `lastOpt` = toOpt(`option`)
      if not `lastOpt`.has: return
  result[6].add quote do:
    return `lastOpt`
  result = nnkStmtList.newTree(result, nnkCall.newTree(procName))

when isMainModule:
  import unittest, sequtils

  suite "options":
    # work around a bug in unittest
    let intNone = none(int)
    let stringNone = none(string)

    test "example":
      proc find(haystack: string, needle: char): Option[int] =
        for i, c in haystack:
          if c == needle:
            return some i

      check("abc".find('c').get() == 2)

      let result = "team".find('i')

      check result == intNone
      check result.isNone

    test "some":
      check some(6).get() == 6
      check some("a").unsafeGet() == "a"
      check some(6).isSome
      check some("a").isSome

    test "none":
      expect UnpackError:
        discard none(int).get()
      check(none(int).isNone)
      check(not none(string).isSome)

    test "equality":
      check some("a") == some("a")
      check some(7) != some(6)
      check some("a") != stringNone
      check intNone == intNone

      when compiles(some("a") == some(5)):
        check false
      when compiles(none(string) == none(int)):
        check false

    test "get with a default value":
      check(some("Correct").get("Wrong") == "Correct")
      check(stringNone.get("Correct") == "Correct")

    test "$":
      check($(some("Correct")) == "Some(Correct)")
      check($(stringNone) == "None[string]")

    test "map with a void result":
      var procRan = 0
      some(123).map(proc (v: int) = procRan = v)
      check procRan == 123
      intNone.map(proc (v: int) = check false)

    test "map":
      check(some(123).map(proc (v: int): int = v * 2) == some(246))
      check(intNone.map(proc (v: int): int = v * 2).isNone)

    test "filter":
      check(some(123).filter(proc (v: int): bool = v == 123) == some(123))
      check(some(456).filter(proc (v: int): bool = v == 123).isNone)
      check(intNone.filter(proc (v: int): bool = check false).isNone)

    test "flatMap":
      proc addOneIfNotZero(v: int): Option[int] =
        if v != 0:
          result = some(v + 1)
        else:
          result = none(int)

      check(some(1).flatMap(addOneIfNotZero) == some(2))
      check(some(0).flatMap(addOneIfNotZero) == none(int))
      check(some(1).flatMap(addOneIfNotZero).flatMap(addOneIfNotZero) == some(3))

      proc maybeToString(v: int): Option[string] =
        if v != 0:
          result = some($v)
        else:
          result = none(string)

      check(some(1).flatMap(maybeToString) == some("1"))

      proc maybeExclaim(v: string): Option[string] =
        if v != "":
          result = some v & "!"
        else:
          result = none(string)

      check(some(1).flatMap(maybeToString).flatMap(maybeExclaim) == some("1!"))
      check(some(0).flatMap(maybeToString).flatMap(maybeExclaim) == none(string))

    test "SomePointer":
      var intref: ref int
      check(option(intref).isNone)
      intref.new
      check(option(intref).isSome)

      let tmp = option(intref)
      check(sizeof(tmp) == sizeof(ptr int))

    test "none[T]":
      check(none[int]().isNone)
      check(none(int) == none[int]())

    test "$ on typed with .name":
      type Named = object
        name: string

      let nobody = none(Named)
      check($nobody == "None[Named]")

    test "$ on type with name()":
      type Person = object
        myname: string

      let noperson = none(Person)
      check($noperson == "None[Person]")

    test "optionCase":
      let x = some(100)
      optionCase x:
        some y:
          check y == 100
        none: discard

    test "compare":
      proc leq(x, y: int): bool =
        x <= y
      check optCmp(10, 20, leq) == some(10)
      check optCmp(30, 20, leq) == none(int)

    test "or and and":
      check optAnd(none(int), some(20)) == none(int)
      check optAnd(some(10), some(20)) == some(20)
      check optOr(none(int), some(20)) == some(20)
      check optOr(some(10), some(20)) == some(10)

      var evaluated = false
      proc shouldntHappen(): Option[int] =
        evaluated = true
        none(int)
      # Checks that optOr terminates early so shouldntHappen is never run
      check optOr(some(10), shouldntHappen()) == some(10)
      check(evaluated == false)
      # Checks that optAnd terminates early so shouldntHappen is never run
      check optAnd(none(int), shouldntHappen()) == none(int)
      check(evaluated == false)
      # Check composability
      check(
        optOr(none(int), none(int),
          optAnd(some(10), some(20)),
          shouldntHappen()
        ) == some(20))
      check(evaluated == false)
      # Check that optOr can auto-convert literals
      check optOr(10, 20, some(30)) == some(10)
      # Check that optAnd can auto-convert literals
      check optAnd(10, 20, some(30)) == some(30)

