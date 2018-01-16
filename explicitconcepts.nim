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
  concVarTyName = "T" & magic

type
  ConceptId = string
  ConceptCompanion[id: static[ConceptId]] = distinct auto
  ConceptInfo = tuple[tdef, cdef: NimNode]

template typeDefId(td: untyped): string = td.lineInfo

proc toId(ci: ConceptInfo): ConceptId =
  # TODO: probably include cdef itself for generic instantiations.
  ci.tdef.typeDefId

proc conceptInfo(c: NimNode): ConceptInfo

proc conceptInfo(ci: ConceptInfo): ConceptInfo =
  let
    ti = getImpl(ci.cdef[0].symbol)
  if nnkNilLit == ti.kind:
    error("no type implementation found.", ci.cdef[0])
  if not ti.findChild(nnkBracketExpr == it.kind).isNil:
    error("generic concepts are not yet supported.", ci.cdef[0])

  case ti[2].kind
  of nnkSym:
    # type alias: resolve original type definition instead.
    ti[2].conceptInfo
  of nnkDistinctTy:
    # distinct type: keep the distinct def, resolve original type.
    (ti, ti[2][0].conceptInfo.cdef)
  of nnkTypeClassTy:
    # actual concept definition: return it.
    (ti, ti)
  else:
    # not even a concept.
    (ci.tdef, nil)

proc conceptInfo(c: NimNode): ConceptInfo =
  # Returns a tuple containing the resolved actual symbol and definition nodes
  # of the passed concept symbol node.
  let cd = c.symbol.getImpl
  (cd, cd).conceptInfo

proc id*(c: NimNode): ConceptId =
  let ci = c.conceptInfo
  if ci.cdef.isNil:
    error($c.symbol & " is not a concept.", c)
  ci.toId

template flagProcDef(t: typed, cid: ConceptId): untyped =
  let m = magic

  # The existence of this proc signals an ``implemements``-relation.
  proc `impl m`*(Ty: typedesc[t], Co: typedesc[ConceptCompanion[cid]])
    {.compileTime.} = discard

template flagProcCall(t: typed, cid: ConceptId): untyped =
  let m = magic
  `impl m`(t, ConceptCompanion[cid])

macro checkImplements*(t, c: typed): untyped =
  ## Produces the code to check wether there is an ``implemements``-relation
  ## between the type and the concept bound to the passed symbol nodes ``t``
  ## and ``c``, respectively.
  newStmtList(newCall("compiles", getAst flagProcCall(t, c.id)))

template procDef(t: typed, cid: ConceptId, warn: bool, cName: string): untyped =
  when compiles(flagProcCall(t, cid)):
    when warn:
      {.warning: "redundant implements-relation for " &
        cName & " is ignored.".}
  else:
    flagProcDef(t, cid)

proc baseConcepts(cDef: NimNode): NimNode =
  cDef.findChild(nnkTypeClassTy == it.kind)
    .findChild(nnkOfInherit == it.kind)

proc isExplicit(ci: ConceptInfo): bool =
  result = false
  if ci.cdef.isNil:
    error($ci.tdef[0].symbol & " is not a concept.", ci.tdef[0])
  let args = ci.cdef.last[0]
  for arg in args:
    result = nnkTypeOfExpr == arg.kind and concVarTyName == $arg[0].ident
    if result:
      break

proc isExplicit(c: NimNode): bool =
  c.conceptInfo.isExplicit

proc implBy(c, t, stmts: NimNode, warn: bool = true) =
  let ci = c.conceptInfo
  if ci.cdef.isNil:
    error($c.symbol & " is not a concept.", c)
  # TODO: do I want this here?
 #let bases = baseConcepts(ci.cdef)
 #if not bases.isNil:
 #  for b in bases:
 #    if b.isExplicit:
 #      implBy(b, t, stmts, false)
  stmts.add getAst procDef(t, ci.toId, warn, c.repr)
  if not ci.isExplicit:
    if warn:
      warning(("$# is implicit, the implements-relation with $# will not " &
        "be checked.") % [c.repr, t.repr])

macro implementedBy(c, t: typed): untyped =
  ## Establishes an ``implements``-relation between type ``t`` and concept
  ## ``c`` and all of its base concepts.
  result = newStmtList()
  implBy(c, t, result)
  #echo result.repr

proc implStmts(args, t: NimNode): seq[NimNode] {.compileTime.} =
  result = @[]
  for c in args:
    if nnkStmtList == c.kind:
      break
    let msg = "$# does not (yet) satisfy $#." % [t.repr, c.repr]
    result.add quote do:
      implementedBy(`c`, `t`)
      when not(`t` is `c`):
        {.warning: `msg`.}

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
 #echo result.repr

template refinedConc(ty, base: untyped): untyped =
  type ty = concept c of base
    c is base  # TODO: seems to be necessary?

proc identNode(typeDef: NimNode): NimNode =
  case typeDef[0].kind
  of nnkPragmaExpr:
    typeDef[0].identNode   # this is not a nnkTypeDef node, but the recursion works
  else:
    typeDef[0].basename

proc expl(typeSects: NimNode): NimNode =
  ## Makes the concepts defined in the type sections passed as a block argument
  ## explicit.
  typeSects.expectKind(nnkStmtList)
  if typeSects.len == 0:
    error("concept type definitions expected.", typeSects)
  result = newStmtList()

  for ts in typeSects:
    ts.expectKind(nnkTypeSection)
    for td in ts:
      var concDef: NimNode
      let
        ty = td[0]
        tidn = td.identNode
        tSpec = td.last
      case tSpec.kind
      of nnkIdent:
        error($tidn.ident & " is an alias and cannot be explicit.", ty)
      of nnkDistinctTy:
        # replace distinct concept with refined one.
        let
          refiConc = getAst refinedConc(ty, tSpec[0].ident)
        concDef = td
        concDef[2] = refiConc[0][0][2]
      of nnkTypeClassTy:
        concDef = td
      else:
        error($tidn.ident & " is not a concept.", ty)

      let
        tc = concDef.last
        concVarTy = !concVarTyName
      if nnkEmpty == tc.last.kind:
        # add a concept body where necessary.
        tc.del tc.len-1
        tc.add newStmtList()

      # add a matched type variable..
      tc[0].add newTree(nnkTypeOfExpr, newIdentNode concVarTy)
      # ..and the check for an implements-relation.
      let 
        tdid = td.typeDefId
        implCheck = getAst flagProcCall(`concVarTy`, `tdid`)
      tc.last.add implCheck

      result.add newTree(nnkTypeSection, concDef)

macro explicit*(typeSects: untyped): untyped =
  result = expl typeSects
  #echo result.repr

macro explicit*(typeSects, post: untyped): untyped =
  result = expl typeSects
  for stmt in post:
    result.add stmt
