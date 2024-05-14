variable {p q : Prop}

theorem t1 (hp : p) (_ : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

example (h : p ∧ q) : p := h.left
example (h : p ∧ q) : q := h.right
example (h : p ∧ q) : q ∧ p := h.symm
example (h : p ∨ q) (not_q : ¬q) : p := h.resolve_right not_q

example (h : p ∨ q) (not_q : ¬q) : p :=
  match h with
  | Or.inl p => p
  | Or.inr q => absurd q not_q

theorem symm : x = y → y = x
  | rfl => rfl

theorem trans : x = y → y = z → x = z
  | rfl, rfl => rfl

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    And.symm
    And.symm

#check and_swap p q

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

section
  open Classical

  theorem dne (p : Prop) (h : ¬¬p) : p :=
    Or.elim (em p)
      id
      (λ not_p => absurd not_p h)

  theorem step (p : Prop) (h : ¬ (p ∨ ¬ p)) : ¬p :=
    λ h₁ => absurd (Or.inl h₁) h

  theorem my_em (p : Prop) : p ∨ ¬p :=
    dne (p ∨ ¬p) $
      λ h₁ =>
        have h₂ := step p h₁
        absurd (Or.inr h₂) h₁

  example (h : ¬¬p) : p :=
    byCases
      (λ h₁ : p => h₁)
      (λ h1 : ¬p => absurd h1 h)

  example (h : ¬¬p) : p :=
    byContradiction
      (λ h₁ : ¬p => show False from h h₁)

  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    Or.elim (em p)
      (λ hp : p =>
        Or.inr $
          λ hq : q => absurd (And.intro hp hq) h)
      (λ hp : ¬p => Or.inl hp)
end

namespace Exercises
  variable {p q r : Prop}

  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      And.symm
      And.symm

  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      Or.symm
      Or.symm

  theorem and_associative_left (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
    have hp := h.left.left
    have hq := h.left.right
    have hr := h.right
    And.intro hp (And.intro hq hr)

  theorem and_associative_right (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
    have hp := h.left
    have hq := h.right.left
    have hr := h.right.right
    And.intro (And.intro hp hq) hr

  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      and_associative_left
      and_associative_right

  theorem or_assoc_left (h : (p ∨ q) ∨ r) : p ∨ (q ∨ r) :=
    h.elim
      (λ hpq : p ∨ q =>
        hpq.elim
          (λ hp : p => Or.inl hp)
          (λ hq : q => Or.inr (Or.inl hq)))
      (λ hr : r => Or.inr (Or.inr hr))

  theorem or_assoc_right (h : p ∨ (q ∨ r)) : (p ∨ q) ∨ r :=
    h.elim
      (λ hp : p => Or.inl (Or.inl hp))
      (λ hqr : q ∨ r =>
        hqr.elim
          (λ hq : q => Or.inl (Or.inr hq))
          (λ hr : r => Or.inr hr))

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
      or_assoc_left
      or_assoc_right


  namespace a
    theorem left (f : p → (q → r)) : ((p ∧ q) → r) :=
      λ hpq : p ∧ q =>
        f (hpq.left) (hpq.right)

    theorem right (f : (p ∧ q) → r) : p → q → r :=
      λ hp hq => f (And.intro hp hq)

    example : (p → (q → r)) ↔ (p ∧ q → r) :=
      Iff.intro left right
  end a

  namespace b
    theorem left (f : (p ∨ q) → r) : (p → r) ∧ (q → r) :=
      And.intro
        (λ hp : p => f $ Or.inl hp)
        (λ hq : q => f $ Or.inr hq)

    theorem right (f : (p → r) ∧ (q → r)) : (p ∨ q) → r :=
      λ hpq : p ∨ q =>
        hpq.elim
          f.left
          f.right

    example : (p ∨ q) → r ↔ (p → r) ∧ (q → r) :=
      Iff.intro
        left
        right
  end b

  namespace c
    theorem left (f : ¬(p ∨ q)) : ¬p ∧ ¬q :=
      And.intro
        (λ hp : p => absurd (Or.inl hp) f)
        (λ hq : q => absurd (Or.inr hq) f)

    theorem right (f : ¬p ∧ ¬q) : ¬(p ∨ q) :=
      λ nhpq =>
        nhpq.elim
          (λ hp : p => absurd hp f.left)
          (λ hq : q => absurd hq f.right)

    example : ¬(p ∨ q) ↔ (¬p ∧ ¬q) :=
      Iff.intro
        left
        right
  end c

  example (f : ¬p ∨ ¬q) : ¬(p ∧ q) :=
    λ hpq =>
      f.elim
        (λ np => absurd hpq.left np)
        (λ nq => absurd hpq.right nq)

  example : ¬(p ∧ ¬p) :=
    λ hpnp => absurd hpnp.left hpnp.right

  example (f : p ∧ ¬q) : ¬(p → q) :=
    λ hpiq => absurd (hpiq f.left) f.right

  example (f : ¬p) : (p → q) :=
    λ hp => absurd hp f

  example (f : ¬p ∨ q) : (p → q) :=
    λ hp => f.neg_resolve_left hp

  namespace d
    theorem left (f : p ∨ False) : p :=
      f.elim
        id
        False.elim

    example : p ∨ False ↔ p :=
      Iff.intro
        left
        Or.inl
  end d

  example : p ∧ False ↔ False :=
    Iff.intro
      And.right
      False.elim

  example (f : p → q) : (¬q → ¬p) :=
    λ nfq hp => absurd (f hp) nfq

  namespace classical
    open Classical

    theorem n₁ (f : ¬(p → q)) : ¬q :=
      Or.elim (em q)
        (λ hq => absurd (λ_ => hq) f)
        id

    example (f : p → q ∨ r) : ((p → q) ∨ (p → r)) :=
      Or.elim (em p)
      (λ hp => match f hp with
                | Or.inl hq => Or.inl (λ_ => hq)
                | Or.inr hr => Or.inr (λ_ => hr)
      )
      (λ nhp => Or.inl $ λ hp => absurd hp nhp)
    example (f : ¬(p ∧ q)) : ¬p ∨ ¬q :=
      Or.elim (em p)
        (λ hp => Or.inr $
          λ hq => absurd (And.intro hp hq) f)
        Or.inl
    example (f : ¬(p → q)) : p ∧ ¬q :=
      Or.elim (em p)
        (λ hp => And.intro hp $ λ hq => absurd (λ_ => hq) f)
        (λ nhp => f.elim $ λ hp => absurd hp nhp)
    example (f : p → q) : (¬p ∨ q) :=
      Or.elim (em p)
        (λ hp => Or.inr $ f hp)
        Or.inl
    example (f : ¬q → ¬p) : (p → q) :=
      λ hp =>
        Or.elim (em q)
        id
        (λ nhq => absurd hp (f nhq))
    example : p ∨ ¬p := em p
    example (f : (p → q) → p) : p :=
      Or.elim (em p)
        id
        λ nhp => f (λ hp => absurd hp nhp)

  end classical
end Exercises
