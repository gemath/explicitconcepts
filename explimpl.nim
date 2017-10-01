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

proc hash(cie: ConceptId): Hash =
  hash($cie)

proc resolveTypeInfo(cid: ConceptId): ConceptId =
  echo $cid
  if not getImpl(cid.def.symbol).findChild(nnkBracketExpr == it.kind).isNil:
    err("generic concepts are not yet supported.", cid.sym)
  var n = cid.def.getType[1]
  case n.kind
  of nnkSym:          # distinct type: get the original type definition.
    ( (if nnkEmpty == cid.sym.kind: n else: cid.sym) , n ).resolveTypeInfo
  of nnkBracketExpr:  # actual type definition: return it.
    (cid.sym, n)
  else:
    err("concept expected.", cid.sym)
    (nil, nil)

proc id(t: NimNode): ConceptId =
  result = (newEmptyNode(), t).resolveTypeInfo

template implProcCall(c, t: untyped): untyped =
  implementedBy(c, t)

template flagProcDef(t: untyped, cId: Hash): untyped =
  proc explImpl(Ty: typedesc[t], Co: typedesc[ConceptIdTyClass[cid]]): bool = true

template flagProcCall(t: untyped, cId: Hash): untyped =
  explImpl(t, ConceptIdTyClass[cId])

macro explicitlyImplements*(t, c: typed): untyped =
  newStmtList(newCall("compiles", getAst flagProcCall(t, hash(c.id))))

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
  var
    csid = c.id
    csidh = hash(csid)
  result = newStmtList(
    nnkWhenStmt.newTree(
      nnkElifBranch.newTree(
        nnkPrefix.newTree(
          newIdentNode(!"not"),
          newCall("compiles", getAst(flagProcCall(t, csidh)))
        ),
        getAst(flagProcDef(t, csidh))
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
  for c in args:
    if c.kind in {nnkStmtList}:
      break
    expectKind(c, nnkIdent, "syntax error in concepts list.")
    for i in stmts:
      var im = if nnkTypeDef == i.kind: i[0] else: i
      expectKind(im, nnkIdent, "syntax error in implementations spec.")
      result.add getAst implProcCall(c, im)
