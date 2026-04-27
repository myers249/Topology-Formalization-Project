import TopologyProject.Definitions.Base

/-
  Closed subspace topology S_U on the same base set/preorder:
    a ◁_U V  iff  a ◁ (U ∪ V)
-/
def closedSubspaceCover {X : Type} (S : FormalTopology X) (U : Subset X) :
    X → Subset X → Prop :=
  λ a V => a ◁[S.cover] (U ∪ V)

def closedSubspaceTopology {X : Type} (S : FormalTopology X) (U : Subset X) :
    FormalTopology X where
  preorder := S.preorder
  cover := closedSubspaceCover S U
  refl := by
    intro V a haV
    exact S.refl (Or.inr haV)
  trans := by
    intro V W a haV hVW
    apply S.trans haV
    intro b hbUV
    cases hbUV with
    | inl hbU =>
      exact S.refl (Or.inl hbU)
    | inr hbV =>
      exact hVW b hbV
  loc := by
    intro V W a haV haW
    apply S.trans (S.loc haV haW)
    intro b hb
    rcases hb with ⟨hbUV, hbUW⟩
    rcases hbUV with ⟨c, hcUV, hbc⟩
    rcases hbUW with ⟨d, hdUW, hbd⟩
    cases hcUV with
    | inl hcU =>
      exact S.trans (S.ext hbc) (by
        intro x hx
        subst hx
        exact S.refl (Or.inl hcU))
    | inr hcV =>
      cases hdUW with
      | inl hdU =>
        exact S.trans (S.ext hbd) (by
          intro x hx
          subst hx
          exact S.refl (Or.inl hdU))
      | inr hdW =>
        apply S.refl
        right
        constructor
        · exact ⟨c, hcV, hbc⟩
        · exact ⟨d, hdW, hbd⟩
  ext := by
    intro a b hab
    apply S.trans (S.ext hab)
    intro x hx
    subst hx
    exact S.refl (Or.inr rfl)

def SU {X : Type} (S : FormalTopology X) (U : Subset X) : FormalTopology X :=
  closedSubspaceTopology S U

def isDownwardClosed {X : Type} (P : Preorder X) (G : Subset X) : Prop :=
  ∀ a b : X, P.le a b → G b → G a

def openSubspaceCover {X : Type} (S : FormalTopology X) (G : Subset X) :
    X → Subset X → Prop :=
  fun a U => (a↓[S.preorder] ∩ G) ◁ₛ[S.cover] U

def openSubspaceLe {X : Type} (S : FormalTopology X) (G : Subset X) :
    X → X → Prop :=
  fun a b => a ◁[openSubspaceCover S G] {b}

def PtSet {X : Type} (_S : FormalTopology X) : Subset (Subset X) :=
  fun _ => True

def PtOpenSubspace {X : Type} (S : FormalTopology X) (G : Subset X) : Subset (Subset X) :=
  fun alpha => (∃ a : X, alpha a ∧ G a) ∧ PtSet S alpha

def Erel {X : Type} (S : FormalTopology X) (U : Subset X) : X → X → Prop :=
  fun a b => a ◁[closedSubspaceCover S U] {b}

def Epreimage {X : Type} (S : FormalTopology X) (U : Subset X) (V : Subset X) : Subset X :=
  fun a => ∃ b, V b ∧ Erel S U a b

/-
  Point-level inclusion i = Pt(E): in this set-based model points of S_U and S
  have the same carrier, so i acts as identity on points.
-/
def iMap {X : Type} (_S : FormalTopology X) (_U : Subset X) : Subset X → Subset X :=
  fun alpha => alpha

def pointMonomorphism {X : Type} (i : Subset X → Subset X) : Prop :=
  Function.Injective i

def disjointSubset {X : Type} (A B : Subset X) : Prop :=
  ∀ x, ¬ (A x ∧ B x)

def PtClosedSubspace {X : Type} (_S : FormalTopology X) (U : Subset X) : Subset (Subset X) :=
  fun beta => disjointSubset beta U
