def Subset (S : Type) := S → Prop
notation x " ∈ " S => S x


--C is our covering relation that will be used to define a FormalTopology
def covers {S : Type} (C : S → Subset S → Prop) (a : S) (U : Subset S) : Prop :=
  C a U
notation a " ◁[" C"]" U => covers C a U


def subsetCovers {S : Type} (C : S → Subset S → Prop) (U V : Subset S) : Prop :=
  ∀ a, (a ∈ U) → a ◁[C] V
notation U " ◁ₛ[" C"]" V => subsetCovers C U V

--Order which is reflexive and transitive
structure Preorder (X : Type) where
  le : X → X → Prop
  refl: ∀ x, le x x
  trans: ∀ {x y z}, le x y → le y z → le x z
def leOf {X : Type} (P : Preorder X) (x y : X) : Prop :=
  P.le x y
notation x " ≤[" P"]" y => leOf P x y

def downwardClosure {X : Type} (P : Preorder X) (U : Subset X) : Subset X :=
  λ x => ∃ y, U y ∧  x ≤[P] y
notation U "↓[" P"]" => downwardClosure P U


def principalDownset {X : Type} (P : Preorder X) (a : X) : Subset X :=
  (λ x => x = a)↓[P]
notation a"↓[" P"]" => principalDownset P a

def intersection {X : Type} (U V : Subset X) : Subset X :=
  λ x => (x ∈ U) ∧ (x ∈ V)
notation U " ∩ " V => intersection U V

def singleton {X : Type} (a : X) : Subset X :=
  λ x => x = a
notation "{" a "}" => singleton a

/-
  A formal topology is a set S with a preorder (S, ≤) and a cover relation ◁ satisfying:
  Reflexivity: If a ∈ U, then a ◁ U
  Transitivity: If a ◁ U and U ◁ V, then a ◁ V
  Localization: If a ◁ U and a ◁ V then a ◁ U≤ ∩ V≤
  Extensionality: If a ≤ b, then a ◁ {b}.
  If a ◁ b we say a is covered by b or equivalently b covers a.
-/
structure FormalTopology (S : Type) where
  preorder : Preorder S
  cover : S → Subset S → Prop
  refl : ∀ {U : Subset S} {a : S}, (a ∈ U) → a ◁[cover] U
  trans : ∀ {U V : Subset S} {a : S}, (a ◁[cover] U) → (U ◁ₛ[cover] V) → (a ◁[cover] V)
  loc : ∀ {U V : Subset S} {a : S}, (a ◁[cover] U) → (a ◁[cover] V) → a◁[cover] (U↓[preorder] ∩ V↓[preorder])
  ext : ∀ {a b : S}, (a ≤[preorder] b) → (a ◁[cover] {b})


notation "ℕ" => Nat
/-
  I have decided to write verbose proofs as to make it more readable, and to reflect a a more usual approach.
-/


theorem intersection_of_downClosures {X : Type} (P : Preorder X) (U V : Subset X) : ∀ b c, (b ∈ U) → (c ∈ V) → (b ≤[P] c) → b ∈ U↓[P] ∩ V↓[P] := by
  intro b c hbU hcV b_le_c
  constructor
  · exists b
    constructor
    · exact hbU
    · exact P.refl b
  · exists c





def natPreorder : Preorder ℕ :=
  { le := Nat.le,
      refl := Nat.le_refl,
      trans := Nat.le_trans }
def natCover : ℕ → Subset ℕ → Prop :=
  λ m U => ∃ n, (n ∈ U) ∧ Nat.le m n



def natFormalTopology: FormalTopology ℕ :=
  { preorder := natPreorder
    cover := natCover,
    refl := by -- This can be shorter, but this makes it very clear.
      intro U m hmU
      have hmle : Nat.le m m :=  Nat.le_refl m
      have hn : ∃ n, (n ∈ U) ∧ Nat.le m n := by
        exists m
      exact hn,
    trans := by
      intro U V a haU hUV
      have a_le_b : ∃ b, (b ∈ U) ∧ Nat.le a b := haU
      have hbV : ∀ b, (b ∈ U) → (b ◁[natCover] V) := hUV --This isn't necessary, but going explicitly through the definitions makes it more clear.
      have b_le_c : ∀ b, (b ∈ U) → (∃ c, (c ∈ V) ∧ Nat.le b c) := hbV
      obtain ⟨b, a_le_b⟩ := a_le_b
      obtain ⟨c, b_le_c⟩ := b_le_c b a_le_b.1
      have a_le_c : a ≤[natPreorder] c := natPreorder.trans a_le_b.right b_le_c.right
      exists c
      constructor
      · exact b_le_c.left
      · exact a_le_c
    loc := by
      intro U V a haU haV
      obtain ⟨b, hbU⟩ := haU
      obtain ⟨c, hcV⟩ := haV
      cases Nat.le_total b c with
        |inl h =>
          have intersection := intersection_of_downClosures natPreorder U V b c hbU.left hcV.left h
          exists b
          constructor
          · exact intersection
          · exact hbU.right
        |inr h =>
          have intersection := intersection_of_downClosures natPreorder V U c b hcV.left hbU.left h
          exists c
          constructor
          · exact intersection.symm
          · exact hcV.right
    ext := by
      intro a b a_le_b
      exists b
  }


example : 3 ◁[natFormalTopology.cover] (λ n => n ≤ 5) := by
  exists 5
  simp

example : 3 ◁[natFormalTopology.cover] {3} := by
  have h : 3 ≤ 3 := Nat.le_refl 3
  exact natFormalTopology.ext h

example : (λ n => n ≤ 10 ∧ n ≠ 5)◁ₛ[natFormalTopology.cover] (λ n => n ≥ 11) := by
  intro n h
  exists 11
  constructor
  · exact Nat.le_of_ble_eq_true rfl
  · refine Nat.le.step ?_
    exact h.left
