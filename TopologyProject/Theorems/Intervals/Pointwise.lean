import TopologyProject.Definitions
import TopologyProject.Theorems.SubspaceCore
import TopologyProject.Theorems.Subspaces

theorem E_preimage_cover_equiv
    {X : Type} (S : FormalTopology X) (U V : Subset X) (a : X) :
  (a ◁[(SU S U).cover] (Epreimage S U V)) ↔ (a ◁[(SU S U).cover] V) :=
  closed_cover_Epreimage_iff S U V a

theorem i_on_points_is_identity
    {X : Type} (S : FormalTopology X) (U : Subset X) (alpha : Subset X) :
    iMap S U alpha = alpha :=
  iMap_eq_id_on_points S U alpha

theorem beta_in_points_of_SU_iff_disjoint
    {X : Type} (S : FormalTopology X) (U : Subset X) (beta : Subset X) :
    PtClosedSubspace S U beta ↔ disjointSubset beta U :=
  beta_in_PtClosedSubspace_iff_disjoint S U beta

theorem ptAf_bar_subset_bar_image (f : Rat → Rat) (x : Rat) :
  ptAf f (barOfRat x) ⊆ₛ barOfRat (f x) := by
  intro J hJ
  rcases hJ with ⟨I, hIx, hAf⟩
  rcases hIx with ⟨hL, hR⟩
  exact hAf x hL hR

theorem ptAf_bar_eq_bar_image_of_local_continuity
    (f : Rat → Rat)
    (hcont : ∀ x : Rat, ∀ J : QInterval,
      barOfRat (f x) J → ∃ I : QInterval, barOfRat x I ∧ Af f I J)
    (x : Rat) :
    ptAf f (barOfRat x) = barOfRat (f x) := by
  funext J
  apply propext
  constructor
  · exact ptAf_bar_subset_bar_image f x J
  · intro hJ
    rcases hcont x J hJ with ⟨I, hIx, hAf⟩
    exact ⟨I, hIx, hAf⟩

theorem Pt_Af_represents_f
    (f : Rat → Rat)
    (hcont : ∀ x : Rat, ∀ J : QInterval,
      barOfRat (f x) J → ∃ I : QInterval, barOfRat x I ∧ Af f I J) :
    ∀ x : Rat, ptAf f (barOfRat x) = barOfRat (f x) := by
  intro x
  exact ptAf_bar_eq_bar_image_of_local_continuity f hcont x

theorem id_local_interval_witness
    (x : Rat) (J : QInterval)
    (hxJ : barOfRat x J) :
    ∃ I : QInterval, barOfRat x I ∧ Af (fun t => t) I J := by
  refine ⟨J, hxJ, ?_⟩
  intro t htL htR
  exact ⟨htL, htR⟩

theorem Pt_Af_represents_id
    (x : Rat) :
    ptAf (fun t => t) (barOfRat x) = barOfRat x := by
  exact ptAf_bar_eq_bar_image_of_local_continuity
    (fun t => t)
    (fun x J hxJ => id_local_interval_witness x J hxJ)
    x

theorem Af_comp
    (f g : Rat → Rat)
    (I J K : QInterval)
    (hfg : Af f I J)
    (hgh : Af g J K) :
    Af (fun x => g (f x)) I K := by
  intro x hxL hxR
  rcases hfg x hxL hxR with ⟨hJ1, hJ2⟩
  exact hgh (f x) hJ1 hJ2

theorem af_comp
    (f g : Rat → Rat)
    (I J K : QInterval)
    (hfg : Af f I J)
    (hgh : Af g J K) :
    Af (fun x => g (f x)) I K :=
  Af_comp f g I J K hfg hgh
