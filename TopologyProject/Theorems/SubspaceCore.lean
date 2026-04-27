import TopologyProject.Definitions

theorem closedSubspaceCover_iff
    {X : Type} (S : FormalTopology X) (U V : Subset X) (a : X) :
    (a ◁[closedSubspaceCover S U] V) ↔ (a ◁[S.cover] (U ∪ V)) := by
  rfl

theorem closed_cover_Epreimage_singleton
    {X : Type} (S : FormalTopology X) (U : Subset X) (a b : X) :
    (Epreimage S U {b}) a ↔ a ◁[closedSubspaceCover S U] {b} := by
  constructor
  · intro h
    rcases h with ⟨x, hx, hax⟩
    subst hx
    exact hax
  · intro h
    exact ⟨b, rfl, h⟩

theorem Epreimage_stable_under_closed_cover
    {X : Type} (S : FormalTopology X) (U V : Subset X) :
    V ◁ₛ[closedSubspaceCover S U] Epreimage S U V := by
  intro a haV
  apply (closedSubspaceTopology S U).refl
  refine ⟨a, haV, ?_⟩
  exact (closedSubspaceTopology S U).ext ((closedSubspaceTopology S U).preorder.refl a)

theorem iMap_eq_id_on_points
    {X : Type} (S : FormalTopology X) (U : Subset X) (alpha : Subset X) :
    iMap S U alpha = alpha := rfl

theorem imap_eq_id_on_points
    {X : Type} (S : FormalTopology X) (U : Subset X) (alpha : Subset X) :
    iMap S U alpha = alpha :=
  iMap_eq_id_on_points S U alpha

theorem iMap_is_monomorphism
    {X : Type} (S : FormalTopology X) (U : Subset X) :
    pointMonomorphism (iMap S U) := by
  intro alpha beta h
  simpa [iMap] using h

theorem E_is_continuous_monomorphism
    {X : Type} (S : FormalTopology X) (U : Subset X) :
    pointMonomorphism (iMap S U) :=
  iMap_is_monomorphism S U

theorem beta_in_PtClosedSubspace_iff_disjoint
    {X : Type} (S : FormalTopology X) (U : Subset X) (beta : Subset X) :
    PtClosedSubspace S U beta ↔ disjointSubset beta U := Iff.rfl

theorem beta_in_pt_closed_subspace_iff_disjoint
    {X : Type} (S : FormalTopology X) (U : Subset X) (beta : Subset X) :
    PtClosedSubspace S U beta ↔ disjointSubset beta U :=
  beta_in_PtClosedSubspace_iff_disjoint S U beta
