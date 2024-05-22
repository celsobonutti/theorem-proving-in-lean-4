import «TheoremProving»

def main : IO Unit :=
  IO.println s!"memes"

abbrev M : Type := Nat
abbrev N : Type := Nat

def x : M → N
  | x => x

/- comment -/

#check Nat → Nat

def m : Nat × String := (5, "memes")

def test : List Type := [Nat, String, Bool]

def y := List.map List test

def to_product (x : List Type) (p : x.length > 0 := by decide) : Type :=
  match x, p  with
  | t :: ts, _ =>
    if proof : ts.length > 0 then
      t × (@to_product ts proof)
    else
      t

#reduce to_product y

def T : Type := to_product y

def memes : T := ([1, 2, 3, 4] , ["memes"] , [])

-- universe u

-- def F (α : Type u) : Type u := Prod α α

def F.{u} (α : Type u) : Type u := Prod α α

#reduce F Type

#check λ (x : Nat) => x + 5

def double {α : Type} [Add α] : α → α
  | x =>
    let db := x + x
    db

section useful
  variable (α β γ : Type)
end useful

namespace Foo
  def a : Nat := 5
end Foo

#check Foo.a

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a := ⟨ a, b ⟩

inductive Lambda : Type where
  | var : String → Lambda
  | app : Lambda → Lambda → Lambda
  | lam : String → Lambda → Lambda
  deriving Repr

instance : Coe String Lambda where
  coe := Lambda.var

notation:10 "λ" x "⇒" n => Lambda.lam x n
notation:11 f "(" x ")" => Lambda.app f x

#eval (λ "memes" ⇒ "boo" ("memes"))

example : Lambda :=
 (λ "memes" ⇒ "boo" ("memes"))
