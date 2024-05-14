example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  λ f =>
  λ y =>
    show p y from (f y).left

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}

section

  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)

  example : a = d :=
    Eq.trans hab (Eq.trans (Eq.symm hcb) hcd)

  variable (α β : Type)

  example (f : α → β) (a : α) : (λ x => f x) a = f a := rfl
  example (a : α) (b : β) : (a, b).1 = a := rfl
  example : 2 + 3 = 5 := rfl

  example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
    Eq.subst h1 h2

  example (α : Type) (a b : α) (p : α → Prop) : a = b → p a → p b
    | Eq.refl a, pa => pa


  example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
    h1 ▸ h2

end

section

  variable (α : Type)
  variable (a b : α)
  variable (f g : α → Nat)
  variable (h₁ : a = b)
  variable (h₂ : f = g)

  example : f a = f b := congrArg f h₁
  example : f a = g a := congrFun h₂ a
  example : f a = g b := congr h₂ h₁

  variable (a b c d e : Nat)
  variable (h₁ : a = b)
  variable (h₂ : b = c + 1)
  variable (h₃ : c = d)
  variable (h₄ : e = 1 + d)

  theorem T : a = e :=
    calc a
      _ = b     := h₁
      _ = c + 1 := h₂
      _ = d + 1 := congrArg Nat.succ h₃
      _ = 1 + d := Nat.add_comm d 1
      _ = e     := Eq.symm h₄

  theorem T' : a = e :=
    calc
      a = e := by simp [h₁, h₂, h₃, Nat.add_comm, h₄]

  def divides (x y : Nat) : Prop :=
    ∃ k, k*x = y

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc (x + y) * (x + y)
      _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    ⟨ 1, h ⟩

end

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (λ w =>
     λ hpq => ⟨ w, hpq.right, hpq.left ⟩)

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

variable (a b : Nat)

theorem even_plus_even (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
  Exists.elim h₁ (λ w₁ hw₁ =>
  Exists.elim h₂ (λ w₂ hw₂ =>
    Exists.intro (w₁ + w₂)
      (calc a + b
        _ = 2 * w₁ + 2 * w₂ := by rw [hw₁, hw₂]
        _ = 2 * (w₁ + w₂)   := by rw [Nat.mul_add])))

theorem even_plus_even₁ (h₁ : is_even a) (h₂ : is_even b) : is_even (a + b) :=
  match h₁, h₂ with
  | ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ => ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

namespace classic
  open Classical
  variable (p : α → Prop)


  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    byContradiction $
      λ h₁ : ¬ ∃ x, p x =>
        have h₂ : ∀ x, ¬ p x :=
          λ x =>
          λ hp =>
          have h₃ : ∃ x, p x := ⟨x, hp⟩
          h₁ h₃
        h h₂
end classic

namespace Exercise
  open Classical

  variable {α : Type} {p q : α → Prop}
  variable {r : Prop}

  example : (∃ _ : α, r) → r
    | ⟨_, hr⟩ => hr

  example (a : α) : r → (∃ _ : α, r)
    | hr => ⟨a, hr⟩

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    Iff.intro
      (λ ⟨x, hp, hr⟩ => ⟨⟨x, hp⟩, hr⟩)
      (λ ⟨⟨x, hp⟩, hr⟩ => ⟨x, hp, hr⟩)

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    Iff.intro
      (λ ⟨x, hpq⟩ => match hpq with
      | Or.inl hp => Or.inl ⟨x, hp⟩
      | Or.inr hq => Or.inr ⟨x, hq⟩)
      (λ
      | Or.inl ⟨x, hp⟩ => ⟨x, Or.inl hp⟩
      | Or.inr ⟨x, hq⟩ => ⟨x, Or.inr hq⟩)

  theorem s₁ (h : ¬ (∀ x, p x)) : ∃ x, ¬ p x :=
    byContradiction $
      λ h₁ : ¬ ∃ x, ¬ p x =>
        have h₂ : ∀ x, p x :=
          λ x =>
          byContradiction $ λ npx => absurd ⟨x, npx⟩ h₁
        h h₂

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    Iff.intro
    (λ hp ⟨x, nhp⟩ => absurd (hp x) nhp)
    (λ nhp => byContradiction $ λ nforall => absurd (s₁ nforall) nhp)

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    Iff.intro
    (λ ⟨x, hp⟩ nforall => absurd hp (nforall x))
    (λ h =>
      byContradiction $
        λ h₁ : ¬ ∃ x, p x =>
          have h₂ : ∀ x, ¬ p x :=
            λ x =>
            λ hp =>
            have h₃ : ∃ x, p x := ⟨x, hp⟩
            h₁ h₃
          h h₂)

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    Iff.intro
    (λ nexists x px => absurd ⟨x, px⟩ nexists)
    (λ hforall ⟨x, px⟩ => absurd px (hforall x))

  theorem s₂ (h : ¬ ∃ x, ¬p x) : ∀ x, p x :=
    λ x => byContradiction $ λ nhp => absurd ⟨x, nhp⟩ h

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    Iff.intro
    (λ nforall => byContradiction $ λ nexists => absurd (s₂ nexists) nforall)
    (λ ⟨x, nhp⟩ hforall => absurd (hforall x) nhp)

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    Iff.intro
    (λ hf ⟨x, hpx⟩ => hf x hpx)
    (λ hf x px => hf ⟨x, px⟩)

  -- example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  --   Iff.intro
  --     (λ ⟨b, hb⟩ hf => hb (hf b))
  --     (λ h1 : (∀ x, p x) → r =>
  --       show ∃ x, p x → r from
  --         byCases
  --           (λ hap : ∀ x, p x => ⟨a, λ _ => h1 hap⟩)
  --           (λ hnap : ¬(∀ x, p x) =>
  --             byContradiction $ λ hnp : ¬ ∃ x, p x → r => _))

  -- example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  --   Iff.intro
  --     (λ ⟨x, fr⟩ hr => ⟨x, fr hr⟩)
  --     (λ ex => ⟨a, λ hr => let ⟨_, hpa⟩ := (ex hr)
  --                  _⟩)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (λ hf => And.intro (λ hp => (hf hp).left) (λ hq => (hf hq).right))
    (λ ⟨hp, hq⟩ x => ⟨hp x, hq x⟩)
example (f : ∀ x, p x → q x) (g : ∀ x, p x) : (∀ x, q x) :=
  λ _ => f _ (g _)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x
  | Or.inl hp, x => Or.inl (hp x)
  | Or.inr hq, x => Or.inr (hq x)

example : α → ((∀ _ : α, r) ↔ r)
  | x => Iff.intro (λ f => f x) (λ r _ => r)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (λ f =>
      byCases
        (λ hr : r => Or.inr hr)
        (λ nhr : ¬r => Or.inl $ λ x : α => Or.resolve_right (f x) nhr))
    (λ
      | Or.inl hf, x => Or.inl (hf x)
      | Or.inr hr, _ => Or.inr hr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ hf hr x => hf x hr)
    (λ hf _ hr => hf hr _)

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h_barber : shaves barber barber ↔ ¬ shaves barber barber := h barber
  iff_not_self h_barber

end Exercise
