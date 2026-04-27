import TopologyProject.Definitions

theorem real_cover_of_forall_inner_fin
    (I : QInterval) (V : Subset QInterval)
    (hconv : ∀ {J : QInterval} {W : Subset QInterval}, realCoverFin J W → realCover J W)
    (hinner : ∀ u v : Rat, I.left < u → (huv : u < v) → v < I.right →
      realCoverFin ⟨u, v, huv⟩ V) :
    realCover I V := by
  apply realCover.trans (realCover.g1 I)
  intro J hJ
  rcases hJ with ⟨hLu, hVb⟩
  exact hconv
    (hinner J.left J.right hLu J.left_lt_right hVb)

theorem real_cover_iff_forall_inner_fin
    (I : QInterval) (V : Subset QInterval)
    (hconv : ∀ {J : QInterval} {W : Subset QInterval}, realCoverFin J W → realCover J W)
    (hdeep : realCover I V →
      ∀ u v : Rat, I.left < u → (huv : u < v) → v < I.right →
        realCoverFin ⟨u, v, huv⟩ V) :
    realCover I V ↔
      (∀ u v : Rat, I.left < u → (huv : u < v) → v < I.right →
        realCoverFin ⟨u, v, huv⟩ V) := by
  constructor
  · intro h
    exact hdeep h
  · intro h
    exact real_cover_of_forall_inner_fin I V hconv h

theorem subset_of_list_finite_union_view
    (I : QInterval) (V0 : List QInterval) :
    intervalCoveredByList I V0 ↔
      (∀ x : Rat, I.left < x → x < I.right →
        ∃ J, subsetOfList V0 J ∧ J.left < x ∧ x < J.right) :=
  Iff.rfl

theorem real_cover_fin_has_finite_subcover_schema
    (hfin : ∀ I U, realCoverFin I U → finiteSubcoverData I U)
    (I : QInterval) (U : Subset QInterval)
    (h : realCoverFin I U) :
    finiteSubcoverData I U :=
  hfin I U h

theorem real_cover_fin_has_finite_subcover_theorem
    (hfin : ∀ I U, realCoverFin I U → finiteSubcoverData I U)
    (a b : Rat) (hab : a < b) (U : Subset QInterval)
    (h : realCoverFin ⟨a, b, hab⟩ U) :
    finiteSubcoverData ⟨a, b, hab⟩ U := by
  exact hfin ⟨a, b, hab⟩ U h

theorem real_cover_fin_iff_interval_covered_by_finite
    (hfinEq : ∀ I : QInterval, ∀ V0 : List QInterval,
      realCoverFin I (subsetOfList V0) ↔ intervalCoveredByList I V0)
    (I : QInterval) (V0 : List QInterval) :
    realCoverFin I (subsetOfList V0) ↔ intervalCoveredByList I V0 :=
  hfinEq I V0

theorem off_zero_intervals_downward_closed :
    isDownwardClosed qIntervalPreorder offZeroIntervals := by
  intro I J hIJ hJ
  rcases hJ with ⟨K, hKG, hJK⟩
  exact ⟨K, hKG, qIntervalPreorder.trans hIJ hJK⟩

theorem reciprocal_key_lemma
    (U : Subset QInterval)
    (u v : QInterval)
    (hu : covers realFormalTopology.cover u U)
    (hvG : offZeroIntervals v)
    (hvu : reciprocalRel v u)
    (hmono : ∀ x : QInterval, qIntervalPreorder.le x v → offZeroIntervals x → reciprocalRel x u)
    (htransport : ∀ x : QInterval,
      reciprocalRel x u →
      covers realFormalTopology.cover u U →
      covers realFormalTopology.cover x (reciprocalPreimage U)) :
    covers (openSubspaceCover realFormalTopology offZeroIntervals) v (reciprocalPreimage U) := by
  intro x hx
  rcases hx with ⟨hxDown, hxG⟩
  rcases hxDown with ⟨y, hyEq, hxy⟩
  subst hyEq
  have hxu : reciprocalRel x u := hmono x hxy hxG
  exact htransport x hxu hu
