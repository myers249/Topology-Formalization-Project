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

def union {X : Type} (U V : Subset X) : Subset X :=
  λ x => (x ∈ U) ∨ (x ∈ V)
notation U " ∪ " V => union U V

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
