#
# Copyright (c) 2017 Gerd Mathar
#

## This module provides explicit concepts and an ``implements``-relation
## between concepts and implementing types.
##
## Motivation
## ==========
##
## A type satisfies a regular concept if it matches the requirements defined
## by the concept. This is an implicit match, the creator of the type did
## not declare intent to make the type satisfy the concept. While this is often
## useful, in other cases, stating an ``implements``-relation between the
## type and the concept in the source code to make the intention clear produces
## more readable and safer code: An explicit concept is only satisfied by a
## type if such an ``implements``-relation exists.
##
## Use
## ====
##
## .. code-block:: nim
##   implements C, ExC: X
## Defines ``implements``-relations for an existing type and existing concepts:
## ``X`` implements concepts ``C`` and ``ExC``.
##
## .. code-block:: nim
##   explicit:
##     type
##       ExD = concept d
##         d.x is float
## Defines an explicit concept ``ExD``.
##
## .. code-block:: nim
##   implements ExD:
##     type
##       Xx = object
##         x: float
##   
##       Y = object
##         x: float
##
##   type
##     Y2 = object
##       x: float
##
##   echo(Y is ExD)   # -> true
##   echo(Y2 is ExD)  # -> false
## Defines ``implements``-relations for new types: ``Xx`` and ``Y``
## implement concept ``ExD``. Note that, despite the fact that it fulfills
## the requirement in the body of ``ExD``, ``Y2`` does not satisfy ``ExD``
## because ``ExD`` is explicit and there is no ``implements``-relation
## defined between the two. 
##
## The ``implements``-relation between a type and a concept automatically
## extends to aliases of the two and to derivatives of the type, but not to
## distinct aliases of the two and to refinements of the concept.
##
## For details see the source files in the ``tests`` directory.

import strutils, macros, hashes

const
  magic = "9F08B7C91364CDF2"
  implFmt = "implements: $#"
  explFmt = "explicit: $#"

type
  ConceptId = tuple[sym, def: NimNode]

  # TODO: can ConceptId itself be used here instead of its hash?
  ConceptCompanion[id: static[Hash]] = distinct auto

proc`$`(cie: ConceptId): string =
  cie.sym.treeRepr & " | " & cie.def.treeRepr

proc resolveConcept(cid: ConceptId): ConceptId =
  var ti = getImpl(cid.def.symbol)

  if not ti.findChild(nnkBracketExpr == it.kind).isNil:
    error(implFmt % "generic concepts are not yet supported.", cid.sym)

  case ti[2].kind
  of nnkSym:          # type alias: resolve original type instead.
    (ti[2], ti[2]).resolveConcept
  of nnkDistinctTy:   # distinct type: resolve original type with distinct name.
    (cid.sym, ti[2][0]).resolveConcept
  of nnkTypeClassTy:  # actual concept definition: return it.
    (cid.sym, ti)
  else:
    error(implFmt % "concept expected.", cid.sym)
    (nil, nil)

proc structuredId(c: NimNode): ConceptId =
  # Returns a unique id for the passed concept symbol node.
  (c, c).resolveConcept

proc id(c: NimNode): Hash =
  hash($c.structuredId)

template implProcCall(c, t: untyped): untyped =
  implementedBy(c, t)

template flagProcDef(t: untyped, cId: Hash): untyped =
  var m = magic

  # The existence of this proc signlas an ``implemements``-relation.
  proc `explImpl m`*(Ty: typedesc[t], Co: typedesc[ConceptCompanion[cid]]): bool
    {.compileTime.} = true

template flagProcCall(t: untyped, cId: Hash): untyped =
  var m = magic
  `explImpl m`(t, ConceptCompanion[cId])

macro checkImplements*(t, c: typed): untyped =
  ## Produces the code to check wether there is an ``implemements``-relation
  ## between the type and the concept bound to the passed symbol nodes ``t``
  ## and ``c``, respectively.
  newStmtList(newCall("compiles", getAst flagProcCall(t, c.id)))

proc standIn(sym, def: NimNode): NimNode =
  # Analyzes an AST generated by ``explConcDef`` to find the symbol node
  # bound to the stand-in concept.
  result = def.findChild(nnkTypeClassTy == it.kind)
  if not result.isNil:
    result = result.findChild(nnkStmtList == it.kind)
    if not result.isNil and result.len > 0:
      var lst = result.last
      result = nil
      if nnkCall == lst.kind:
        if "checkImplements" == $lst[0].symbol:
          lst = lst.last
          if $sym.symbol & magic == $lst.symbol:
            result = lst

template explConcDef(co, standIn): untyped =
  type co = concept c, type T
    c is standIn
    checkImplements(T, standIn)

template procDef(cid: Hash, t: typed, warn: bool): untyped =
  when compiles(flagProcCall(t, cid)):
    when warn:
      {.warning: implFmt % "ignored redundant statement.".}
  else:
    flagProcDef(t, cid)

macro implementedBy*(c, t: typed): typed =
  ## Establishes an ``implements``-relation between the type and the
  ## concept given by the symbol nodes ``t`` and ``c``, respectively.
  var
    csid = c.structuredId
    standInType = standIn(c, csid.def)

  result = newStmtList()
  result.add getAst procDef(hash($csid), t, true)
  if standInType.isNil:
    warning implFmt %
      $c.symbol & " is not explicit, the implements-relation will not" &
      " be checked on use of implementing type."
  else:
    result.add getAst procDef(standInType.id, t, false)

template checkMatch(c, t: untyped): untyped =
  when not(t is c):
    {.fatal: explFmt % "concept not satisfied.".}

macro implements*(args: varargs[untyped]): untyped =
  ## Establishes an ``implements``-relation between concepts given
  ## as leading arguments and an existing type or the types defined in a type
  ## section given as a trailing block argument.
  result = newStmtList()
  args.expectKind(nnkArglist)
  var stmts = args.findChild(nnkStmtList == it.kind)
  if isNil(stmts):
    error(implFmt % "implementing type expected.", args)
  if nnkTypeSection == stmts[0].kind:
    stmts = stmts[0]
    result.add stmts
  if args.len == 0 or nnkStmtList == args[0].kind:
    error(implFmt % "error in concepts list.", args)
  for c in args:
    if c.kind in {nnkStmtList}:
      break
    if stmts.len == 0:
      error(implFmt % "error in implementations spec.", stmts)
    for i in stmts:
      var im = if nnkTypeDef == i.kind: i[0] else: i
      result.add getAst implProcCall(c, im)
      result.add getAst checkMatch(c, im)

macro explicit*(args: untyped): untyped =
  ## Makes the concepts defined in the type section passed as a block argument
  ## explicit.
  result = args
  args.expectKind(nnkStmtList)
  args[0].expectKind(nnkTypeSection)
  for td in args[0]:
    if td.findChild(nnkTypeClassTy == it.kind and
        nnkArglist == it[0].kind).isNil:
      error(explFmt % "not a concept.", td[0])
    var
      sc = td[0].copy
    td[0].basename = $td[0].basename & magic
    result.add getAst explConcDef(sc, td[0].basename)
