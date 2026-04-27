import TopologyProject.Definitions.NatTopologiesBase

theorem intersection_of_downClosures {X : Type} (P : Preorder X) (U V : Subset X) : ∀ b c, (b ∈ U) → (c ∈ V) → (b ≤[P] c) → b ∈ U↓[P] ∩ V↓[P] := by
  intro b c hbU hcV b_le_c
  constructor
  · exists b
    constructor
    · exact hbU
    · exact P.refl b
  · exists c

theorem even_not_odd (n : ℕ) : even n → odd n → False := by
  intro he ho
  induction he with
  | zero =>
      cases ho
  | step he ih =>
      cases ho with
      | step ho =>
          exact ih ho

theorem odd_not_even (n : ℕ) : odd n → even n → False := by
  intro ho he
  exact even_not_odd n he ho

theorem even_plus_one_odd (n : ℕ) : even n → odd (n + 1) := by
  intro he
  induction he with
  | zero =>
      exact odd.one
  | step he ih =>
      exact odd.step ih

theorem odd_plus_one_even (n : ℕ) : odd n → even (n + 1) := by
  intro ho
  induction ho with
  | one =>
      exact even.step even.zero
  | step ho ih =>
      exact even.step ih

theorem odd_or_even (n : ℕ) : odd n ∨ even n := by
  induction n with
  | zero =>
      right
      exact even.zero
  | succ n ih =>
      cases ih with
      | inl ho =>
          right
          exact odd_plus_one_even n ho
      | inr he =>
          left
          exact even_plus_one_odd n he

theorem odd_even_opposite (n : ℕ) : odd n ↔ ¬even n := by
  constructor
  · intro ho he
    exact even_not_odd n he ho
  · intro hne
    have h : ¬even n → odd n := by
      intro ha
      by_cases ho : odd n
      · exact ho
      · have h : odd n ∨ even n := odd_or_even n
        cases h with
        | inl ho =>
            exact ho
        | inr he =>
            have hcontra : False := hne he
            exact False.elim hcontra
    exact h hne

theorem even_odd_opposite (n : ℕ) : even n ↔ ¬odd n := by
  constructor
  · intro he ho
    exact odd_not_even n ho he
  · intro hno
    have h : ¬odd n → even n := by
      intro ha
      by_cases he : even n
      · exact he
      · have h : odd n ∨ even n := odd_or_even n
        cases h with
        | inl ho =>
            have hcontra : False := hno ho
            exact False.elim hcontra
        | inr he =>
            exact he
    exact h hno
