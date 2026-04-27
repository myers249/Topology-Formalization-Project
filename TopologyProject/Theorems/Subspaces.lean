import TopologyProject.Definitions.Subspaces

theorem closed_cover_Epreimage_iff
    {X : Type} (S : FormalTopology X) (U V : Subset X) (a : X) :
    (a ◁[closedSubspaceCover S U] (Epreimage S U V)) ↔
      (a ◁[closedSubspaceCover S U] V) := by
  constructor
  · intro ha
    apply (closedSubspaceTopology S U).trans ha
    intro x hx
    rcases hx with ⟨b, hbV, hxb⟩
    apply (closedSubspaceTopology S U).trans hxb
    intro y hy
    subst hy
    exact (closedSubspaceTopology S U).refl hbV
  · intro ha
    apply (closedSubspaceTopology S U).trans ha
    intro x hxV
    apply (closedSubspaceTopology S U).refl
    refine ⟨x, hxV, ?_⟩
    exact (closedSubspaceTopology S U).ext ((closedSubspaceTopology S U).preorder.refl x)

