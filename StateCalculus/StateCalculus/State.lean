import Std.Data

open Std renaming HashMap → Map

instance [Ord τ] : BEq τ where
  beq := λ x y =>
    match compare x y with
    | Ordering.eq => True
    | _ => False

def AttrLabel : Type := String
def ElemLabel : Type := String

deriving instance Ord, Hashable, Repr for AttrLabel
deriving instance Ord, Hashable, Repr for ElemLabel

inductive Lit where
  | IntLit : Int → Lit
  | BoolLit : Bool → Lit
  | StringLit : String → Lit
  | PathLit : String → Lit
  | UnitLit : Lit

deriving instance Ord, Hashable, Repr for Lit

inductive Value where
  | Literal : Lit → Value
  | Pair : Value → Value → Value
  | Left : Value → Value
  | Right : Value → Value

deriving instance Ord, Hashable, Repr for Value

instance [Ord α] [Ord β] : Ord (α × β) where
  compare := λ (a, b) (x, y) =>
    match compare a x with
    | Ordering.eq => compare b y
    | r => r

mutual
  inductive State : Type where
    | S : Map AttrLabel Value → Map.Raw (ElemLabel × Value) Nested → State

  inductive Nested : Type where
    | Absent : Nested
    | Present : State → Nested
end

deriving instance Repr for State

def emptyState : State := State.S Map.emptyWithCapacity Map.Raw.emptyWithCapacity

inductive Attr : Type where
  | AttrAccess : AttrLabel → Attr
  | NestedAttr : ElemLabel → Value → Attr → Attr

def getAttr (σ : State) (a : Attr) : Option Value :=
  match σ with
  | State.S attrs elems =>
    match a with
    | Attr.AttrAccess a => attrs[a]?
    | Attr.NestedAttr e v a' =>
        match elems[(e, v)]? with
        | Option.some (Nested.Present σ') => getAttr σ' a'
        | _ => Option.none

inductive Elem : Type where
  | ElemAccess : ElemLabel → Value → Elem
  | NestedElem : ElemLabel → Value → Elem → Elem

def containsElem (σ : State) (e : Elem) : Option Bool :=
  match σ with
  | State.S _ elems =>
    match e with
    | Elem.ElemAccess e v =>
      match elems[(e, v)]? with
      | Option.some (Nested.Present _) => Option.some True
      | Option.some Nested.Absent => Option.some False
      | Option.none => Option.none
    | Elem.NestedElem e v e' =>
      match elems[(e, v)]? with
      | Option.some (Nested.Present σ') => containsElem σ' e'
      | Option.some Nested.Absent => Option.some False
      | Option.none => Option.none

inductive Qual : Type where
  | SetAttribute : AttrLabel → Value → Qual
  | PosElement : ElemLabel → Value → Option Qual → Qual
  | NegElement : ElemLabel → Value → Qual

def addQual (σ : State) (q : Qual) : State :=
  match σ with
  | State.S attrs elems =>
    match q with
    | Qual.SetAttribute a v => State.S (attrs.insert a v) elems
    | Qual.NegElement e v => State.S attrs (elems.insert (e, v) Nested.Absent)
    | Qual.PosElement e v q' =>
      let elems' :=
        let bind :=
          match elems[(e, v)]? with
          | Option.some (Nested.Present σ') =>
              match q' with
              | Option.some q' => Nested.Present (addQual σ' q')
              | Option.none => Nested.Present σ'
          | _ =>
              match q' with
              | Option.some q' => Nested.Present (addQual emptyState q')
              | Option.none => Nested.Present emptyState
        elems.insert (e, v) bind
      State.S attrs elems'
