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

proc resolveTypeInfo(cid: ConceptId): ConceptId =
  var ti = getImpl(cid.def.symbol)

  if not ti.findChild(nnkBracketExpr == it.kind).isNil:
    error(implFmt % "generic concepts are not yet supported.", cid.sym)

  case ti[2].kind
  of nnkSym:          # type alias: resolve original type instead.
    (ti[2], ti[2]).resolveTypeInfo
  of nnkDistinctTy:   # distinct type: resolve original type with distinct name.
    (cid.sym, ti[2][0]).resolveTypeInfo
  of nnkTypeClassTy:  # actual concept definition: return it.
    (cid.sym, ti)
  else:
    error(implFmt % "concept expected.", cid.sym)
    (nil, nil)

proc structuredId(t: NimNode): ConceptId =
  (t, t).resolveTypeInfo

proc id(t: NimNode): Hash =
  hash($t.structuredId)

template implProcCall(c, t: untyped): untyped =
  implementedBy(c, t)

template flagProcDef(t: untyped, cId: Hash): untyped =
  var m = magic
  proc `explImpl m`*(Ty: typedesc[t], Co: typedesc[ConceptCompanion[cid]]): bool
    {.compileTime.} = true

template flagProcCall(t: untyped, cId: Hash): untyped =
  var m = magic
  `explImpl m`(t, ConceptCompanion[cId])

macro explicitlyImplements*(t, c: typed): untyped =
  newStmtList(newCall("compiles", getAst flagProcCall(t, c.id)))

proc standIn(sym, def: NimNode): NimNode =
  result = def.findChild(nnkTypeClassTy == it.kind)
  if not result.isNil:
    result = result.findChild(nnkStmtList == it.kind)
    if not result.isNil and result.len > 0:
      var lst = result.last
      result = nil
      if nnkCall == lst.kind:
        if "explicitlyImplements" == $lst[0].symbol:
          lst = lst.last
          if $sym.symbol & magic == $lst.symbol:
            result = lst

proc procDef(cid: Hash, t: NimNode): NimNode =
  nnkWhenStmt.newTree(
    nnkElifBranch.newTree(
      nnkPrefix.newTree(
        newIdentNode(!"not"),
        newCall("compiles", getAst(flagProcCall(t, cid)))
      ),
      getAst(flagProcDef(t, cid))
    )
  )

macro implementedBy*(c, t: typed): typed =
  var
    csid = c.structuredId
    standInType = standIn(c, csid.def)

  result = newStmtList()
  result.add procDef(hash($csid), t)
  if standInType.isNil:
    warning implFmt %
      $c.symbol & " is not explicit, the implements-relationship will not" &
      " be checked on use of implementing type."
  else:
    result.add procDef(standInType.id, t)

template checkMatch(c, t: untyped): untyped =
  when not(t is c):
    {.fatal: explFmt % "concept not satisfied.".}

macro implements*(args: varargs[untyped]): untyped =
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

template explConcDef(co, standIn): untyped =
  type co = concept c, type T
    c is standIn
    explicitlyImplements(T, standIn)

macro explicit*(args: untyped): untyped =
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
