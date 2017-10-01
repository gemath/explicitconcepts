import strutils, macros, hashes

const msgFmt = "implements: $#"

proc err(msg: string, n:NimNode) =
  error(msgFmt % msg, n)

type
  ConceptId = tuple[sym, def: NimNode]

  # TODO: can ConceptId itself be used here instead of its hash?
  ConceptIdTyClass[id: static[Hash]] = distinct auto

proc`$`(cie: ConceptId): string =
  cie.sym.treeRepr & " | " & cie.def.treeRepr

proc resolveTypeInfo(cid: ConceptId): ConceptId =
  if not getImpl(cid.def.symbol).findChild(nnkBracketExpr == it.kind).isNil:
    err("generic concepts are not yet supported.", cid.sym)
  var t = cid.def.getType[1]
  case t.typeKind
  of ntyDistinct:       # distinct type: get the original type definition.
    ( (if nnkEmpty == cid.sym.kind: t else: cid.sym) , t ).resolveTypeInfo
  of ntyUserTypeClass:  # actual concept definition: return it.
    (cid.sym, t)
  else:
    err("concept expected.", cid.sym)
    (nil, nil)

proc structuredId(t: NimNode): ConceptId =
  (newEmptyNode(), t).resolveTypeInfo

proc id(t: NimNode): Hash =
  hash($t.structuredId)

template implProcCall(c, t: untyped): untyped =
  implementedBy(c, t)

template flagProcDef(t: untyped, cId: Hash): untyped =
  proc explImpl*(Ty: typedesc[t], Co: typedesc[ConceptIdTyClass[cid]]): bool = true

template flagProcCall(t: untyped, cId: Hash): untyped =
  explImpl(t, ConceptIdTyClass[cId])

macro explicitlyImplements*(t, c: typed): untyped =
  newStmtList(newCall("compiles", getAst flagProcCall(t, c.id)))

proc expectKind(n: NimNode, k: NimNodeKind, msg: string) =
  if k != n.kind:
    err(msg, n)

macro implementedBy*(c, t: typed): typed =
# TODO: implement this:
#  if not compiles(var dummy = c.isAbsolutelyExplicitish):
#    warning msgFmt % $c.symbol & " is not explicit, statement regarding it " &
#      "is purely informational and will be ignored."
  #echo flagProcQuery(t, c)
#  if flagProcQuery(t, c.id):
#    newStmtList()
#  else:
  var csid = c.id
  result = newStmtList(
    nnkWhenStmt.newTree(
      nnkElifBranch.newTree(
        nnkPrefix.newTree(
          newIdentNode(!"not"),
          newCall("compiles", getAst(flagProcCall(t, csid)))
        ),
        getAst(flagProcDef(t, csid))
      )
    )
  )

macro implements*(args: varargs[untyped]): untyped =
  result = newStmtList()
  args.expectKind(nnkArglist)
  var stmts = args.findChild(it.kind in {nnkStmtList})
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
