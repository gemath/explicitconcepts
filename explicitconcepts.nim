#[
   Explicit Concepts.
   
   Copyright 2017 Gerd Mathar

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
]#

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

import strutils, macros

const
  magic = "9F08B7C91364CDF2"

type
  ConceptId = tuple[loc: string, sym: string]
  ConceptCompanion[id: static[ConceptId]] = distinct auto
  ConceptInfo = tuple[sym, def: NimNode]

proc toConceptId(ci: ConceptInfo): ConceptId =
  #(ci.def.lineInfo, ci.sym.treeRepr)
  (ci.def.lineInfo, ci.sym.repr)
 
proc standInName(base: string): string =
  base & magic

proc conceptInfo(ci: ConceptInfo): ConceptInfo =
  let ti = getImpl(ci.def.symbol)

  if not ti.findChild(nnkBracketExpr == it.kind).isNil:
    error("generic concepts are not yet supported.", ci.sym)

  case ti[2].kind
  of nnkSym:
    # type alias: resolve original symbol and definition instead.
    (ti[2], ti[2]).conceptInfo
  of nnkDistinctTy:
    # distinct type: keep the distinct name, resolve original type.
    (ci.sym, (ci.sym, ti[2][0]).conceptInfo.def)
  of nnkTypeClassTy:
    # actual concept definition: return it.
    (ci.sym, ti)
  else:
    # not even a concept.
    (ci.sym, nil)

proc conceptInfo(c: NimNode): ConceptInfo =
  # Returns a tuple containing the resolved actual symbol and definition nodes
  # of the passed concept symbol node.
  (c, c).conceptInfo

proc toId(ci: ConceptInfo): ConceptId =
  ci.toConceptId

proc id(c: NimNode): ConceptId =
  let ci = c.conceptInfo
  if ci.def.isNil:
    error($c.symbol & " is not a concept.", c)
  ci.toId

template flagProcDef(t: untyped, cid: ConceptId): untyped =
  let m = magic

  # The existence of this proc signals an ``implemements``-relation.
  proc `impl m`*(Ty: typedesc[t], Co: typedesc[ConceptCompanion[cid]])
    {.compileTime.} = discard

template flagProcCall(t: untyped, cid: ConceptId): untyped =
  let m = magic
  `impl m`(t, ConceptCompanion[cid])

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

          # TODO: Is eqIdent even required for comparing two symbols?
          if eqIdent(standInName($sym.symbol), $lst.symbol):
            result = lst

template explConcDef(co, standIn: untyped): untyped =
  type co = concept c, type T
    c is standIn
    checkImplements(T, standIn)

template procDef(cid: ConceptId, t: typed, warn: bool, cName: string): untyped =
  when compiles(flagProcCall(t, cid)):
    when warn:
      {.warning: "redundant implements-relation for " &
        cName & " is ignored.".}
  else:
    flagProcDef(t, cid)

macro implementedBy9F08B7C91364CDF2*(c, t: typed): typed =
  ## Establishes an ``implements``-relation between the type and the
  ## concept given by the symbol nodes ``t`` and ``c``, respectively.
  let ci = c.conceptInfo
  if ci.def.isNil:
    error($c.symbol & " is not a concept.", c)
  let standInConc = standIn(c, ci.def)

  result = newStmtList()
  result.add getAst procDef(ci.toId, t, true, c.repr)
  if standInConc.isNil:
    warning(("$# is not explicit, the implements-relation with $# will not " &
      "be checked from here onwards.") % [c.repr, t.repr])
  else:
    result.add getAst procDef(standInConc.id, t, false, standInConc.repr)

proc implStmts(args, t: NimNode): seq[NimNode] {.compileTime.} =
  result = @[]
  for c in args:
    let msg = "$# does not satisfy $#." % [t.repr, c.repr]
    if c.kind in {nnkStmtList}:
      break
    result.add quote do:
      implementedBy9F08B7C91364CDF2(`c`, `t`)
    result.add quote do:
      when not(`t` is `c`):
        {.fatal: `msg`.}

macro implements*(args: varargs[untyped]): untyped =
  ## Establishes an ``implements``-relation between concepts given
  ## as leading arguments and an existing type or the types defined in type
  ## sections given as a trailing block argument.
  result = newStmtList()
  args.expectKind(nnkArglist)
  if args.len == 0 or nnkStmtList == args[0].kind:
    error("implemented concepts expected.", args)
  let stmts = args.findChild(nnkStmtList == it.kind)
  if isNil(stmts) or stmts.len == 0:
    error("implementing type or type sections expected.", args)
  if stmts.len == 1 and nnkTypeSection != stmts[0].kind:
    result.add implStmts(args, stmts[0])
  else:
    for ts in stmts:
      ts.expectKind(nnkTypeSection)
      result.add ts
      for td in ts:
        result.add implStmts(args, td[0])

macro checkConc9F08B7C91364CDF2*(c, sc: typed): typed =
  let sci = sc.conceptInfo
  if sci.def.isNil:
    error($c.symbol & " is not a concept.", c)
  if sc.symbol != sci.sym.symbol:
    error($c.symbol & " is an alias and cannot be explicit.", c)

template checkConceptCall(c, sc: untyped): untyped =
  checkConc9F08B7C91364CDF2(c, sc)

macro explicit*(args: untyped): untyped =
  ## Makes the concepts defined in the type sections passed as a block argument
  ## explicit.
  args.expectKind(nnkStmtList)
  if args.len == 0:
    error("concept definitions expected.", args)
  result = newStmtList()
  for ts in args:
    ts.expectKind(nnkTypeSection)
    for td in ts:
      let
        c = td[0].copy
      td[0].basename = standInName($td[0].basename)
      result.add newTree(nnkTypeSection, td)
      result.add getAst(explConcDef(c, td[0].basename))[0]
      result.add getAst(checkConceptCall(c.basename, td[0].basename))[0]
