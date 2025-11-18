
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

theorem eq1 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  by
    apply Iff.intro
    intro h1
    intro x
    intro hp
    apply h1
    exact ⟨x, hp⟩
    intro h2 hp
    let ⟨x, hp⟩ := hp
    exact h2 x hp

theorem eq2 : (r → ∀ x, p x) ↔ (∀ x, r → p x) :=
  by
    apply Iff.intro
    intro h1 x r
    exact h1 r x
    intro h2 r x
    exact h2 x r

theorem eq3 : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) := by
  apply Iff.intro
  intro ⟨hr, ⟨x, hp⟩⟩
  apply Exists.intro x ⟨ hr, hp ⟩
  intro ⟨x, ⟨r, px⟩⟩
  constructor
  exact r
  exists x

theorem eq4 : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  by
    intro h x
    cases h
    case inl hr => exact Or.inl hr
    case inr hx => exact Or.inr (hx x)


-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical
#check Classical.byContradiction
#check Classical.em

theorem eq5 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
 by
  apply Iff.intro
  intro notforallx
  apply Classical.byContradiction
  intro h
  apply notforallx
  intro x
  apply Classical.byContradiction
  intro notpx
  apply h
  exact ⟨x, notpx⟩
  intro existsnotpx forallx
  obtain ⟨x, notpx⟩ := existsnotpx
  apply notpx
  exact forallx x

theorem eq6 : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  by
    apply Iff.intro
    intro h x
    cases h with
    | inl hr => exact Or.inl hr
    | inr px => exact Or.inr (px x)
    intro h
    have x := Classical.em r
    cases x with
    | inl hr => exact Or.inl hr
    | inr px =>
      right
      intro x
      have xx := h x
      cases xx with
      | inl hr => contradiction
      | inr hx => exact hx
