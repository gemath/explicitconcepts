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
  flagProcName = "impl" & magic

type
  ConceptId* = tuple[loc: string, sym: string]
  ConceptCompanion*[id: static[ConceptId]] = distinct auto
  ConceptInfo = tuple[sym, def: NimNode]

proc toId(ci: ConceptInfo): ConceptId =
  # TODO: probably include def itself for generic instantiations.
  (ci.sym.lineInfo, ci.sym.repr)
 
#[
proc standInName(base: string): string =
  base & magic
]#

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
    (ti[0], (ci.sym, ti[2][0]).conceptInfo.def)
  of nnkTypeClassTy:
    # actual concept definition: return it.
    (ti[0], ti)
  else:
    # not even a concept.
    (ci.sym, nil)

proc conceptInfo(c: NimNode): ConceptInfo =
  # Returns a tuple containing the resolved actual symbol and definition nodes
  # of the passed concept symbol node.
  (c, c).conceptInfo

proc id(c: NimNode): ConceptId =
  let ci = c.conceptInfo
  if ci.def.isNil:
    error($c.symbol & " is not a concept.", c)
  ci.toId

#[
template flagProcDef(t: untyped, cid: ConceptId): untyped =
  let m = magic

  # The existence of this proc signals an ``implemements``-relation.
  proc `impl m`*(Ty: typedesc[t], Co: typedesc[ConceptCompanion[cid]])
    {.compileTime.} = discard
]#

proc flagProcDef(t: NimNode, cid: ConceptId): NimNode =
  let
    flagProcIdent = !flagProcName
    (loc, sym) = cid
    # The existence of this proc signals an ``implemements``-relation.
    fpd = quote do:
      proc `flagProcIdent`*(Ty: typedesc[`t`],
        Co: typedesc[ConceptCompanion[(`loc`, `sym`)]]) = discard
  result = fpd[0]

#[
template flagProcCall(t: untyped, cid: ConceptId): untyped =
  let m = magic
  `impl m`(t, ConceptCompanion[cid])
]#

proc flagProcCall(ts: string, cid: ConceptId): NimNode =
  let
    flagProcIdent = !flagProcName
    (loc, sym) = cid
    fpc = quote do:
      `flagProcIdent`(bindSym`ts`, ConceptCompanion[(`loc`, `sym`)])
  result = fpc[0]

macro checkImplements*(t, c: untyped): untyped =
  ## Produces the code to check wether there is an ``implemements``-relation
  ## between the type and the concept bound to the passed symbol nodes ``t``
  ## and ``c``, respectively.
  newStmtList(newCall("compiles", flagProcCall($t.ident, c.id)))

#[
proc standInConc(sym, def: NimNode): NimNode =
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
  type co = concept c, type T of standIn
    c is standIn
    checkImplements(T, standIn)
]#

template procDef(t, fpc, fpd: typed, warn: bool, cName: string): typed =
  when compiles(fpc):
    when warn:
      {.warning: "redundant implements-relation for " &
        cName & " is ignored.".}
  else:
  #[
  ]#
    fpd

proc baseConcepts(cDef: NimNode): NimNode =
  cDef.findChild(nnkTypeClassTy == it.kind)
    .findChild(nnkOfInherit == it.kind)

proc isExplicit(ci: ConceptInfo): bool =
  result = false
  let args = ci.def.last[0]
  for arg in args:
    result = nnkTypeOfExpr == arg.kind and concVarTyName == $arg[0].ident
    if result:
      break

proc isExplicit(c: NimNode): bool =
  c.conceptInfo.isExplicit

proc implementedBy(c, t: NimNode, stmts: var seq[NimNode], warn = true) =
  let ci = c.conceptInfo
  if ci.def.isNil:
    error($c.symbol & " is not a concept.", c)
  let bases = baseConcepts(ci.def)
  if not bases.isNil:
    for b in bases:
      if b.isExplicit:
        implementedBy(b, t, stmts, false)
 #let standIn = standInConc(c, ci.def)
  let cid = ci.toId
  stmts.add getAst(procDef(t, flagProcCall($t.ident, cid), flagProcDef(t, cid), warn, c.repr))[0]
 #if standIn.isNil:
  if not ci.isExplicit:
    if warn:
      warning(("$# is implicit, the implements-relation with $# will not " &
        "be checked from here onwards.") % [c.repr, t.repr])
 #else:
 #  stmts.add getAst procDef(standIn.id, t, false, standIn.repr)


#[
macro implementedBy9F08B7C91364CDF2*(c, t: typed): typed =
  ## Establishes an ``implements``-relation between type ``t`` and concept
  ## ``c`` and all of its base concepts.
  result = newStmtList()
  implementedBy(c, t, result)
]#

proc implStmts(args, t: NimNode): seq[NimNode] {.compileTime.} =
  #echo args.treeRepr
  #echo t.treeRepr

  result = @[]
  for c in args:
    let msg = "$# does not satisfy $#." % [t.repr, c.repr]
    if c.kind in {nnkStmtList, nnkStmtListExpr}:
      break
    var res: seq[NimNode] = @[]
    implementedBy(c, t, res)
    result.add res
    let satCheck = quote do:
      when not(`t` is `c`):
        {.fatal: `msg`.}
    result.add satCheck[0]

macro implements*(args: varargs[typed]): typed =
  ## Establishes an ``implements``-relation between concepts given
  ## as leading arguments and an existing type or the types defined in type
  ## sections given as a trailing block argument.
  result = newStmtList()
  args.expectKind(nnkBracket)
  if args.len == 0 or args[0].kind in {nnkStmtList, nnkStmtListExpr}:
    error("implemented concepts expected.", args)
  let stmts = args.findChild(it.kind in {nnkStmtList, nnkStmtListExpr})
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
  echo result.treeRepr

#[
macro checkConc9F08B7C91364CDF2*(c, sc: typed): typed =
  let sci = sc.conceptInfo
  if sci.def.isNil:
    error($c.symbol & " is not a concept.", c)
  if sc.symbol != sci.sym.symbol:
    error($c.symbol & " is an alias and cannot be explicit.", c)

template checkConceptCall(c, sc: untyped): untyped =
  checkConc9F08B7C91364CDF2(c, sc)
]#

template refinedConc(ty, base: untyped): untyped =
  type ty = concept c of base
    c is base  # TODO: seems to be necessary?

proc expl(typeSects: NimNode): NimNode =
  ## Makes the concepts defined in the type sections passed as a block argument
  ## explicit.
  typeSects.expectKind(nnkStmtList)
  if typeSects.len == 0:
    error("concept definitions expected.", typeSects)
  result = newStmtList()
  for ts in typeSects:
    ts.expectKind(nnkTypeSection)
    var nts = newTree(nnkTypeSection)
    for td in ts:
      let cs = td[0]
      let ci = cs.conceptInfo
      if ci.def.isNil:
        error($cs.symbol & " is not a concept.", cs)
      if nnkSym == td.last.kind:
        error($cs.symbol & " is an alias and cannot be explicit.", cs)

      var concDef: NimNode
      if nnkDistinctTy == td.last.kind:
        # replace distinct concept with refined one.
        let
          ty = td[0]
          base = td.last[0].symbol
          refiConc = getAst refinedConc(ty, base)
        concDef = refiConc[0][0]
      else:
        concDef = td

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
      tc.last.add flagProcCall(concVarTyName, ci.toId)
     #tc.last.add implCheck[0]
     # for stmt in getAst(flagProcCall(concVarTy.ident, ci.toId)):
     #  tc.last.add stmt
      nts.add concDef
    result.add nts

macro explicit*(typeSects: typed): typed =
  result = expl typeSects
  echo result.treeRepr

macro explicit*(typeSects, post: typed): typed =
  result = expl typeSects
  for stmt in post:
    result.add stmt
