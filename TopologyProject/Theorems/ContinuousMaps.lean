import TopologyProject.Definitions

theorem continuous_rel_whole
  {X Y : Type}
  {S : FormalTopology X}
  {T : FormalTopology Y}
  (f : ContinuousMapping S T) :
  ∀ a : X, a R[S|f.rel|T] := by
  intro a
  exact f.ax3 a

theorem ContinuousMapping_eq_of_rel_biIncl
    {X Y : Type}
    {S : FormalTopology X}
    {T : FormalTopology Y}
    (F G : ContinuousMapping S T)
    (hFG : ∀ a b, F.rel a b → G.rel a b)
    (hGF : ∀ a b, G.rel a b → F.rel a b) :
    F = G := by
  cases F with
  | mk Frel Fax1 Fax2 Fax3 Fax4 =>
    cases G with
    | mk Grel Gax1 Gax2 Gax3 Gax4 =>
      have hRel : Frel = Grel := by
        funext a b
        apply propext
        constructor
        · intro h
          exact hFG a b h
        · intro h
          exact hGF a b h
      subst hRel
      simp

theorem continuous_maps_to_R_eq_of_rel_biIncl
    {A : Type}
    (SA : FormalTopology A)
    (F G : ContinuousMapping SA realFormalTopology)
    (hFG : ∀ a I, F.rel a I → G.rel a I)
    (hGF : ∀ a I, G.rel a I → F.rel a I) :
    F = G := by
  exact ContinuousMapping_eq_of_rel_biIncl F G hFG hGF
