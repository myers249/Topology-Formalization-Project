import TopologyProject.Definitions

theorem downward_closed_iff_downward_closure_eq
    {X : Type} (P : Preorder X) (G : Subset X) :
    isDownwardClosed P G ↔ G↓[P] = G := by
  constructor
  · intro hdc
    funext a
    apply propext
    constructor
    · intro ha
      rcases ha with ⟨b, hbG, hab⟩
      exact hdc a b hab hbG
    · intro haG
      exact ⟨a, haG, P.refl a⟩
  · intro hEq
    intro a b hab hbG
    have hbDown : (G↓[P]) b := ⟨b, hbG, P.refl b⟩
    have hbG' : G b := by
      simpa [hEq] using hbDown
    have haDown : (G↓[P]) a := ⟨b, hbG', hab⟩
    simpa [hEq] using haDown

theorem open_subspace_cover_iff
    {X : Type} (S : FormalTopology X) (G U : Subset X) (a : X) :
    (a ◁[openSubspaceCover S G] U) ↔ ((a↓[S.preorder] ∩ G) ◁ₛ[S.cover] U) := by
  rfl

theorem open_subspace_cover_extends_cover
    {X : Type} (S : FormalTopology X) (G U : Subset X) (a : X)
    (haU : a ◁[S.cover] U) :
    a ◁[openSubspaceCover S G] U := by
  intro x hx
  rcases hx with ⟨hxDown, _hxG⟩
  rcases hxDown with ⟨y, hyEq, hxle⟩
  subst hyEq
  apply S.trans (S.ext hxle)
  intro y hy
  subst hy
  exact haU

theorem open_subspace_le_extends_le
    {X : Type} (S : FormalTopology X) (G : Subset X) (a b : X)
    (hab : a ≤[S.preorder] b) :
    openSubspaceLe S G a b := by
  intro x hx
  rcases hx with ⟨hxDown, _hxG⟩
  rcases hxDown with ⟨y, hyEq, hxle⟩
  subst hyEq
  have hxb : x ≤[S.preorder] b := S.preorder.trans hxle hab
  exact S.ext hxb

theorem open_subspace_is_formal_topology
    {X : Type}
    (S : FormalTopology X)
    (G : Subset X)
    (_hGdown : isDownwardClosed S.preorder G)
    (hTransOpen :
      ∀ {U V : Subset X} {a : X},
        covers (openSubspaceCover S G) a U →
        subsetCovers (openSubspaceCover S G) U V →
        covers (openSubspaceCover S G) a V)
    (hLocOpen :
      ∀ {U V : Subset X} {a : X},
        covers (openSubspaceCover S G) a U →
        covers (openSubspaceCover S G) a V →
        covers (openSubspaceCover S G) a (U↓[S.preorder] ∩ V↓[S.preorder])) :
    ∃ SG : FormalTopology X,
      SG.preorder = S.preorder ∧
      SG.cover = openSubspaceCover S G := by
  refine ⟨{
    preorder := S.preorder
    cover := openSubspaceCover S G
    refl := ?_
    trans := ?_
    loc := ?_
    ext := ?_
  }, rfl, rfl⟩
  · intro U a haU
    exact open_subspace_cover_extends_cover S G U a (S.refl haU)
  · intro U V a haU hUV
    exact hTransOpen haU hUV
  · intro U V a haU haV
    exact hLocOpen haU haV
  · intro a b hab
    exact open_subspace_le_extends_le S G a b hab

theorem alpha_in_pt_open_subspace_iff
    {X : Type}
    (S : FormalTopology X)
    (G : Subset X)
    (alpha : Subset X) :
    PtOpenSubspace S G alpha ↔
      (∃ a : X, alpha a ∧ G a) ∧ PtSet S alpha := by
  rfl
