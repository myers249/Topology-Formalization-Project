import TopologyProject.Definitions

theorem rel_of_Pt_image_basic_subset
    {X Y : Type}
    {S : FormalTopology X} {T : FormalTopology Y}
    (R : X → Y → Prop) (a : X) (b : Y)
    (h : imageSubset (PtMap S T R) (pointBasicStar a) ⊆ₛ pointBasicStar b) :
    R a b := by
  let α0 : Subset X := {a}
  have hα0 : pointBasicStar a α0 := by
    show α0 a
    rfl
  have himg : imageSubset (PtMap S T R) (pointBasicStar a) (PtMap S T R α0) := by
    refine ⟨α0, hα0, rfl⟩
  have hb : pointBasicStar b (PtMap S T R α0) := h (PtMap S T R α0) himg
  rcases hb with ⟨x, hxα0, hxRb⟩
  have hx_eq_a : x = a := hxα0
  subst hx_eq_a
  exact hxRb

theorem Pt_of_continuous_uniformly_continuous
    {X Y : Type}
    (S : FormalTopology X) (T : FormalTopology Y)
    (G : ContinuousMapping S T)
    (hRelWitness : ∀ b : Y, ∃ a : X, G.rel a b) :
    uniformlyContinuousPtMap S T (PtMapC G) := by
  intro b
  rcases hRelWitness b with ⟨a, hab⟩
  refine ⟨a, ?_⟩
  intro beta hbeta
  rcases hbeta with ⟨alpha, haStar, hEq⟩
  have hb : (PtMapC G alpha) b := ⟨a, haStar, hab⟩
  subst hEq
  exact hb
