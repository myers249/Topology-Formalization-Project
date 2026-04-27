import TopologyProject.Definitions.Continuity

theorem subsetCovers_saturation
  {X : Type}
  (S : FormalTopology X)
  (U : Subset X) :
  U ◁ₛ[S.cover] saturation S U := by
  intro a haU
  exact S.refl (S.refl haU)

theorem saturation_subsetCovers
  {X : Type}
  (S : FormalTopology X)
  (U : Subset X) :
  saturation S U ◁ₛ[S.cover] U := by
  intro a haSat
  exact haSat

theorem saturation_idem
  {X : Type}
  (S : FormalTopology X)
  (U : Subset X) :
  saturation S (saturation S U) = saturation S U := by
  funext a
  apply propext
  constructor
  · intro ha
    exact S.trans ha (saturation_subsetCovers S U)
  · intro ha
    exact S.refl ha

theorem continuous_preimage_subsetCovers
  {X Y : Type}
  {S : FormalTopology X}
  {T : FormalTopology Y}
  (f : ContinuousMapping S T)
  {U V : Subset Y} :
  subsetCovers T.cover U V → subsetCovers S.cover (relPreimage f.rel U) (relPreimage f.rel V) := by
  intro hUV
  intro a haPre
  obtain ⟨b, hbU, haRb⟩ := haPre
  exact f.ax1 a b V haRb (hUV b hbU)

theorem relElemSubset_iff_saturation
  {X Y : Type}
  {S : FormalTopology X}
  {T : FormalTopology Y}
  (f : ContinuousMapping S T)
  (a : X)
  (U : Subset Y) :
  relElemSubset S f.rel a U ↔ relElemSubset S f.rel a (saturation T U) := by
  constructor
  · intro haRU
    exact S.trans haRU (continuous_preimage_subsetCovers f (subsetCovers_saturation T U))
  · intro haRU
    have hBack : relPreimage f.rel (saturation T U) ◁ₛ[S.cover] relPreimage f.rel U := by
      intro x hxPre
      obtain ⟨b, hbSat, hxRb⟩ := hxPre
      exact f.ax1 x b U hxRb hbSat
    exact S.trans haRU hBack

theorem rel_elem_subset_iff_saturation
  {X Y : Type}
  {S : FormalTopology X}
  {T : FormalTopology Y}
  (f : ContinuousMapping S T)
  (a : X)
  (U : Subset Y) :
  relElemSubset S f.rel a U ↔ relElemSubset S f.rel a (saturation T U) :=
  relElemSubset_iff_saturation f a U

theorem continuous_preimage_saturation_eq
  {X Y : Type}
  {S : FormalTopology X}
  {T : FormalTopology Y}
  (f : ContinuousMapping S T)
  (U : Subset Y) :
  saturation S (saturation S (relPreimage f.rel U)) =
    saturation S (relPreimage f.rel (saturation T U)) := by
  rw [saturation_idem S (relPreimage f.rel U)]
  funext a
  apply propext
  exact relElemSubset_iff_saturation f a U

theorem relPreimage_comp_subset
    {X Y Z : Type}
    {S : FormalTopology X}
    (R₁ : X → Y → Prop) (R₂ : Y → Z → Prop)
    (W : Subset Z) :
  relPreimage R₁ (relPreimage R₂ W) ◁ₛ[S.cover] relPreimage (R₂ ∘r[S] R₁) W := by
  intro x hx
  rcases hx with ⟨y, ⟨z, hzW, hyz⟩, hxy⟩
  apply S.refl
  refine ⟨z, hzW, ?_⟩
  apply S.refl
  exact ⟨y, ⟨z, rfl, hyz⟩, hxy⟩
