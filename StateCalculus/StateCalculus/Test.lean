import StateCalculus.State

inductive Res (α ε ν : Type) where
| ok : α → State → Res α ε ν
| except : ε → State → Res α ε ν
| failure : Res α ε ν

def M (α : Type) : Type := State → Res α Value Value

-- Maybe implement Lawful instances

instance : Monad M where
  pure := λ a σ => Res.ok a σ
  bind := λ x f σ =>
    match x σ with
    | Res.ok a σ => f a σ
    | Res.except e σ => Res.except e σ
    | Res.failure => Res.failure

instance : MonadState State M where
  get := λ σ => Res.ok σ σ
  set := λ σ _ => Res.ok () σ
  modifyGet := λ f σ =>
    let (x, σ) := f σ
    Res.ok x σ

instance : Alternative M where
  failure := λ _ => Res.failure
  orElse := λ i f σ =>
    match i σ with
    | Res.failure => f () σ
    | res => res

instance : MonadExcept Value M where
  throw := λ v σ => Res.except v σ
  tryCatch := λ x h σ =>
    match x σ with
    | Res.except e σ => h e σ
    | res => res

instance : MonadFinally M where
  tryFinally' := λ x f σ =>
    match x σ with
    | Res.ok a σ =>
      match f (Option.some a) σ with
      | Res.ok b σ => Res.ok (a, b) σ
      | Res.except e σ => Res.except e σ
      | Res.failure => Res.failure
    | Res.except e σ =>
      match f Option.none σ with
      | Res.ok _ σ => Res.except e σ
      | Res.except e σ => Res.except e σ
      | Res.failure => Res.failure
    | Res.failure => Res.failure

def add (q : Qual) : M Unit :=
  modifyGet (λ σ => ((), addQual σ q))

def contains (e : Elem) : M Bool := do
  let c := containsElem (← get) e
  match c with
  | Option.some c => pure c
  | Option.none => failure

def attrGet (a : Attr) : M Value := do
  let x := getAttr (← get) a
  match x with
  | Option.some x => pure x
  | Option.none => failure

def M.run {α : Type} (f : M α) (σ : State) : Res α Value Value := f σ

-- Everything above are utilities the generated Lean code needs
-- Below here are actual examples showing how we compile things

def example1 : M Unit := do
  if (← contains (Elem.ElemAccess "file" (Value.Literal (Lit.PathLit "/foo/bar"))))
  then
    let o ← attrGet (Attr.NestedAttr "file" (Value.Literal (Lit.PathLit ("/foo/bar"))) (Attr.AttrAccess "owner"))
    if (o == Value.Literal (Lit.StringLit "me"))
    then
      add (Qual.PosElement "file" (Value.Literal (Lit.PathLit "/foo/bar/baz")) (Option.some (Qual.SetAttribute "owner" (Value.Literal (Lit.StringLit "you")))))
    else
      add (Qual.PosElement "file" (Value.Literal (Lit.PathLit "/foo/bar/baz")) (Option.some (Qual.SetAttribute "owner" o)))
  else
    add (Qual.NegElement "file" (Value.Literal (Lit.PathLit "/foo/bar/baz")))

  let x ← attrGet (Attr.AttrAccess "os")
  match x with
  | Value.Left _v =>
      add (Qual.PosElement "os" (Value.Literal (Lit.StringLit "Debian")) Option.none)
  | Value.Right _v =>
      add (Qual.PosElement "os" (Value.Literal (Lit.StringLit "RedHat")) Option.none)
  | _ => failure

#eval (example1.run emptyState)

def example2 : M Unit := do
  add (Qual.PosElement "file" (Value.Literal (Lit.PathLit "/foo/bar")) (Option.some (Qual.SetAttribute "owner" (Value.Literal (Lit.StringLit "me")))))
  add (Qual.SetAttribute "os" (Value.Left (Value.Literal Lit.UnitLit)))
  example1

def example2' : M Unit := do
  add (Qual.PosElement "file" (Value.Literal (Lit.PathLit "/foo/bar")) (Option.some (Qual.SetAttribute "owner" (Value.Literal (Lit.StringLit "us")))))
  add (Qual.SetAttribute "os" (Value.Right (Value.Literal Lit.UnitLit)))
  example1

def example3 : M Unit := do
  add (Qual.NegElement "file" (Value.Literal (Lit.PathLit "/foo/bar")))
  add (Qual.SetAttribute "os" (Value.Right (Value.Literal Lit.UnitLit)))
  example1

#eval (example2.run emptyState)
#eval (example2'.run emptyState)
#eval (example3.run emptyState)

def test2 : M Unit := do
  let x ← attrGet (Attr.AttrAccess "os")
  match x with
  | Value.Left _v =>
      add (Qual.PosElement "os" (Value.Literal (Lit.StringLit "Debian")) Option.none)
  | Value.Right _v =>
      add (Qual.PosElement "os" (Value.Literal (Lit.StringLit "RedHat")) Option.none)
  | _ => failure

def test2_1 : M Unit := do
  add (Qual.SetAttribute "os" (Value.Left (Value.Literal Lit.UnitLit)))
  test2

def test2_2 : M Unit := do
  add (Qual.SetAttribute "os" (Value.Right (Value.Literal Lit.UnitLit)))
  test2

def test2_3 : M Unit := do
  add (Qual.SetAttribute "os" (Value.Literal Lit.UnitLit))
  test2

#eval (test2.run emptyState)
#eval (test2_1.run emptyState)
#eval (test2_2.run emptyState)
#eval (test2_3.run emptyState)

def exceptTest : M Unit := do
  add (Qual.SetAttribute "os" (Value.Literal (Lit.StringLit "Linux")))
  let e ← attrGet (Attr.AttrAccess "ok")
  match e with
  | Value.Literal (Lit.BoolLit true) =>
    add (Qual.SetAttribute "distro" (Value.Literal (Lit.StringLit "Debian")))
  | Value.Literal (Lit.BoolLit false) =>
    throw (Value.Literal (Lit.BoolLit False))
  | _ => failure

def exceptRunner (b : Bool) : M Unit := do
  add (Qual.SetAttribute "ok" (Value.Literal (Lit.BoolLit b)))
  exceptTest

def catchTest (b : Bool) : M Int := do
  try
    exceptRunner b
  catch
  | e =>
    add (Qual.SetAttribute "other" e)
    return 7
  finally
    add (Qual.SetAttribute "finally" (Value.Literal (Lit.IntLit 42)))
    -- The feedback window says this block doesn't support return (or continue/break)
    -- I also had issues trying to add a throw here
    -- We might have to just make something ourselves (TODO)
  return 9

#eval ((exceptRunner true).run emptyState)
#eval ((catchTest true).run emptyState)
#eval ((exceptRunner false).run emptyState)
#eval ((catchTest false).run emptyState)

def returnTest : M Value := do
  let x <- attrGet (Attr.AttrAccess "x")
  let c <- attrGet (Attr.AttrAccess "return")
  match c with
  | Value.Literal (Lit.BoolLit true) =>
    return x
  | Value.Literal (Lit.BoolLit false) =>
    pure ()
  | _ => failure
  add (Qual.SetAttribute "x" (Value.Literal (Lit.IntLit 7)))
  return x

def setupReturnTest (x : Int) (ret : Bool) : M Value := do
  add (Qual.SetAttribute "x" (Value.Literal (Lit.IntLit x)))
  add (Qual.SetAttribute "return" (Value.Literal (Lit.BoolLit ret)))
  returnTest

#eval ((setupReturnTest 3 false).run emptyState)
#eval ((setupReturnTest 3 true).run emptyState)

def mutTest : M Unit := do
  let mut x := Value.Literal Lit.UnitLit
  let e ← attrGet (Attr.AttrAccess "which")
  match e with
  | Value.Literal (Lit.BoolLit true) =>
    x <- attrGet (Attr.AttrAccess "foo")
  | Value.Literal (Lit.BoolLit false) =>
    x <- attrGet (Attr.AttrAccess "bar")
  | _ => failure
  add (Qual.SetAttribute "x" x)

def setupMutTest (foo bar : Int) (which : Bool) : M Unit := do
  add (Qual.SetAttribute "foo" (Value.Literal (Lit.IntLit foo)))
  add (Qual.SetAttribute "bar" (Value.Literal (Lit.IntLit bar)))
  add (Qual.SetAttribute "which" (Value.Literal (Lit.BoolLit which)))
  mutTest

#eval ((setupMutTest 7 12 true).run emptyState)
#eval ((setupMutTest 7 12 false).run emptyState)

def listOfValue (v : Value) : M (List Value) := do
  match v with
  -- nil case
  | Value.Left (Value.Literal Lit.UnitLit) => pure []
  -- cons case
  | Value.Right (Value.Pair hd tl) =>
    let res_tl <- listOfValue tl
    pure (hd :: res_tl)
  | _ => failure

def valueOfList (vs : List Value) : Value :=
  match vs with
  | [] => Value.Left (Value.Literal Lit.UnitLit)
  | hd :: tl => Value.Right (Value.Pair hd (valueOfList tl))

def valueOfListMap {α} (vs : List α) (f : α → Value) : Value :=
  valueOfList (vs.map f)

def loopTest (lst : Value) : M Value := do
  let mut lstTmp := []
  for v in (← listOfValue lst) do
    if (← contains (Elem.ElemAccess "file" v))
    then
      let c ← attrGet (Attr.NestedAttr "file" v (Attr.AttrAccess "contents"))
      add (Qual.NegElement "file" v)
      -- yield c is compiled into...
      lstTmp := c :: lstTmp
      continue
    else
      return Value.Literal (Lit.StringLit "error")
  let loopRes := valueOfList (lstTmp.reverse)
  return loopRes

def loopTestSetup (files : List (String × Bool)) : M Value := do
  for (v, c) in files do
    if c
    then
      add (Qual.PosElement "file" (Value.Literal (Lit.PathLit v)) (Option.some (Qual.SetAttribute "contents" (Value.Literal (Lit.StringLit ("Content of " ++ v))))))
    else
      add (Qual.NegElement "file" (Value.Literal (Lit.PathLit v)))
  loopTest (valueOfListMap files (λ (f, _) => Value.Literal (Lit.PathLit f)))

#eval ((loopTestSetup [("a", true), ("c", true), ("b", true)]).run emptyState)
