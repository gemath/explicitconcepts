import strutils, macros, hashes

const
  implFmt = "implements: $#"
  magic = "9F08B7C91364CDF2"

template err(msg: string, n:NimNode) =
  error(implFmt % msg, n)

template warn(msg: string) =
  warning(implFmt % msg)

type
  ConceptId = tuple[sym, def: NimNode]

  # TODO: can ConceptId itself be used here instead of its hash?
  ConceptCompanion[id: static[Hash]] = distinct auto

proc`$`(cie: ConceptId): string =
  cie.sym.treeRepr & " | " & cie.def.treeRepr

proc resolveTypeInfo(cid: ConceptId): ConceptId =
  var ti = getImpl(cid.def.symbol)
  if not ti.findChild(nnkBracketExpr == it.kind).isNil:
    err("generic concepts are not yet supported.", cid.sym)

  var tt = cid.def.getType

  if nnkEmpty == cid.sym.kind:
    echo "<EMPTY>"
  else:
    echo cid.sym
  echo cid.def.treerepr
  echo tt.treeRepr
  echo ti.treeRepr
  echo "-----------------------------"

  var t = tt[1]
  case t.typeKind
  of ntyDistinct:       # distinct type: get the original type definition.
    ( (if nnkEmpty == cid.sym.kind: t else: cid.sym) , t ).resolveTypeInfo
  of ntyUserTypeClass:  # actual concept definition: return it.
    (cid.sym, t)
  else:
    err("concept expected.", cid.sym)
    (nil, nil)

proc structuredId(t: NimNode): ConceptId =
  result = (newEmptyNode(), t).resolveTypeInfo

  echo "+++++++++++++++++++++++++++++"

  if nnkEmpty == result.sym.kind:
    result.sym = t

proc id(t: NimNode): Hash =
  hash($t.structuredId)

template implProcCall(c, t: untyped): untyped =
  implementedBy(c, t)

template flagProcDef(t: untyped, cId: Hash): untyped =
  proc explImpl(Ty: typedesc[t], Co: typedesc[ConceptCompanion[cid]]): bool
    {.compileTime.} = true

template flagProcCall(t: untyped, cId: Hash): untyped =
  explImpl(t, ConceptCompanion[cId])

macro explicitlyImplements*(t, c: typed): untyped =
  newStmtList(newCall("compiles", getAst flagProcCall(t, c.id)))

template checkMatch(c, t: untyped): untyped =
  when not(t is c):
    {.fatal: "concept not satisfied!".}

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

proc implementedId(c: NimNode): Hash =
  var
    csid = c.structuredId
    standInType = standIn(c, csid.def)

  if standInType.isNil:
    result = hash($csid)
    warn $c.symbol & " is not explicit, the implements-relationship will not" &
      " be checked on use of implementing type."
  else:
    result = standInType.id

macro implementedBy*(c, t: typed): typed =
  var cid = c.implementedId

  result = newStmtList()
  result.add nnkWhenStmt.newTree(
      nnkElifBranch.newTree(
        nnkPrefix.newTree(
          newIdentNode(!"not"),
          newCall("compiles", getAst(flagProcCall(t, cid)))
        ),
        getAst(flagProcDef(t, cid))
      )
    )

macro implements*(args: varargs[untyped]): untyped =
  result = newStmtList()
  args.expectKind(nnkArglist)
  var stmts = args.findChild(nnkStmtList == it.kind)
  if isNil(stmts):
    err("implementing type expected.", args)
  if nnkTypeSection == stmts[0].kind:
    stmts = stmts[0]
    result.add stmts
  if args.len == 0 or nnkStmtList == args[0].kind:
    err("error in concepts list.", args)
  for c in args:
    if c.kind in {nnkStmtList}:
      break
    if stmts.len == 0:
      err("error in implementations spec.", stmts)
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
    if td.findChild(nnkTypeClassTy == it.kind and nnkArglist == it[0].kind).isNil:
      error("not a concept.", td[0])
    var
      iden = td[0].ident
      co = iden
      standInType = newIdentNode($iden & magic)
    td.del 0
    td.insert(0, standInType)
    result.add getAst explConcDef(co, standInType)
