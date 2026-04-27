import TopologyProject.Definitions.Subspaces

notation "ℕ" => Nat

def natPreorder : Preorder ℕ :=
  { le := Nat.le,
      refl := Nat.le_refl,
      trans := Nat.le_trans }

def natCover : ℕ → Subset ℕ → Prop :=
  λ m U => ∃ n, (n ∈ U) ∧ Nat.le m n

inductive even : ℕ → Prop
| zero : even 0
| step : even n → even (n + 2)

inductive odd : ℕ → Prop
| one : odd 1
| step : odd n → odd (n + 2)
