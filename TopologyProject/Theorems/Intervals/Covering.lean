import TopologyProject.Definitions
import TopologyProject.Theorems.SubspaceCore
import TopologyProject.Theorems.PtFunctor

theorem gamma_in_Ispace_iff_disjoint_C
    (alpha beta gamma : PtR) :
    PtClosedSubspace realFormalTopology (Cset alpha beta) gamma ↔
      disjointSubset gamma (Cset alpha beta) := Iff.rfl

theorem cederquist_negri_partII
    (alpha beta : PtR)
    (V : Subset QInterval)
    (r s : Rat) (hrs : r < s)
    (hToFin : ∀ (I : QInterval) (W : Subset QInterval),
      realCover I W → realCoverFin I W)
    (hcover : (⟨r, s, hrs⟩ : QInterval) ◁[(I(alpha,beta)).cover] V) :
    realCoverFin (⟨r, s, hrs⟩ : QInterval) (Cset alpha beta ∪ V) := by
  have hRaw : (⟨r, s, hrs⟩ : QInterval) ◁[realFormalTopology.cover] (Cset alpha beta ∪ V) :=
    (closedSubspaceCover_iff realFormalTopology (Cset alpha beta) V (⟨r, s, hrs⟩ : QInterval)).1 hcover
  exact hToFin (⟨r, s, hrs⟩ : QInterval) (Cset alpha beta ∪ V) hRaw

theorem cederquist_negri
    (alpha beta : PtR)
    (V : Subset QInterval)
    (r s : Rat) (hrs : r < s)
    (hcover : covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) V)
    (hFinitePart :
      covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) V →
      ∃ V0 : List QInterval,
        listSubset V V0 ∧
        covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) (subsetOfList V0))
    (hToFin : ∀ (I : QInterval) (W : Subset QInterval),
      realCover I W → realCoverFin I W) :
    (∃ V0 : List QInterval,
      listSubset V V0 ∧
        covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) (subsetOfList V0))
    ∧
    realCoverFin (⟨r, s, hrs⟩ : QInterval) (Cset alpha beta ∪ V) := by
  constructor
  · exact hFinitePart hcover
  · exact cederquist_negri_partII alpha beta V r s hrs hToFin hcover

theorem cederquist_negri_finite_interval_union
    (alpha beta : PtR)
    (V : Subset QInterval)
    (r s : Rat) (hrs : r < s)
    (hcover : covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) V)
    (hFinitePart :
      covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) V →
      ∃ V0 : List QInterval,
        listSubset V V0 ∧
        covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) (subsetOfList V0))
    (hUnionInterval :
      ∀ V0 : List QInterval,
        listSubset V V0 →
        covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) (subsetOfList V0) →
        isIntervalSubsetRat (unionOfIntervals V0)) :
    ∃ V0 : List QInterval,
      listSubset V V0 ∧
      covers (Ispace alpha beta).cover (⟨r, s, hrs⟩ : QInterval) (subsetOfList V0) ∧
      isIntervalSubsetRat (unionOfIntervals V0) := by
  rcases hFinitePart hcover with ⟨V0, hsub, hcov⟩
  refine ⟨V0, hsub, hcov, ?_⟩
  exact hUnionInterval V0 hsub hcov

theorem Pt_of_continuous_uniformly_continuous_on_Ispace
    (alpha beta : PtR)
    (G : ContinuousMapping (Ispace alpha beta) realFormalTopology)
    (hRelWitness : ∀ J : QInterval, ∃ I : QInterval, G.rel I J) :
    uniformlyContinuousPtMap (Ispace alpha beta) realFormalTopology (PtMapC G) := by
  exact Pt_of_continuous_uniformly_continuous
    (Ispace alpha beta) realFormalTopology G hRelWitness

theorem lebesgue_number_theorem_schema
    (V0 : List QInterval)
    (hLeb : ∃ δ : Rat,
      0 < δ ∧
      ∀ x y : Rat,
        unionOfIntervals V0 x → unionOfIntervals V0 y → closeBy δ x y →
          pairInSomeInterval V0 x y) :
    ∃ δ : Rat,
      0 < δ ∧
      ∀ x y : Rat,
        unionOfIntervals V0 x → unionOfIntervals V0 y → closeBy δ x y →
          pairInSomeInterval V0 x y := by
  exact hLeb

theorem lebesgue_number_theorem
    (V0 : List QInterval)
    (hLeb : ∃ δ : Rat,
      0 < δ ∧
      ∀ x y : Rat,
        unionOfIntervals V0 x → unionOfIntervals V0 y → closeBy δ x y →
          pairInSomeInterval V0 x y) :
    ∃ δ : Rat, 0 < δ := by
  rcases hLeb with ⟨δ, hδ, _⟩
  exact ⟨δ, hδ⟩

theorem finite_interval_cover_with_neighborhood_labels
    {X : Type}
    (TX : FormalTopology X)
    (alpha beta : PtR)
    (G : ContinuousMapping (Ispace alpha beta) TX)
    (U : Subset X)
    (r s : Rat) (hrs : r < s)
    (V0 : List QInterval)
    (hcover : intervalCoveredByList (⟨r, s, hrs⟩ : QInterval) V0)
    (zOf : QInterval → X)
    (hzU : ∀ I : QInterval, List.Mem I V0 → U (zOf I))
    (hloc : ∀ I : QInterval, List.Mem I V0 →
      imageSubset (PtMapC G) (pointBasicStar I) ⊆ₛ pointBasicStar (zOf I)) :
    ∃ Z0 : List X,
      intervalCoveredByList (⟨r, s, hrs⟩ : QInterval) V0 ∧
      (∀ I : QInterval, List.Mem I V0 →
        ∃ z : X, List.Mem z Z0 ∧ U z ∧
          imageSubset (PtMapC G) (pointBasicStar I) ⊆ₛ pointBasicStar z) := by
  refine ⟨V0.map zOf, hcover, ?_⟩
  intro I hI
  refine ⟨zOf I, ?_, hzU I hI, hloc I hI⟩
  exact List.mem_map.mpr ⟨I, hI, rfl⟩
