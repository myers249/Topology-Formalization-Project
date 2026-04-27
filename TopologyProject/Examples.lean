-- Examples and executable checks.
import TopologyProject.Theorems

example (I : QInterval) : Af (fun x => x) I I := by
  intro x hxL hxR
  exact ⟨hxL, hxR⟩

example (I : QInterval) :
    I ◁[realFormalTopology.cover] G1Family I := by
  exact realCover.g1 I

example (I : QInterval) (d c : Rat)
    (hAd : I.left < d) (hDc : d < c) (hCb : c < I.right) :
    I ◁[realFormalTopology.cover] G2Family I d c (show I.left < c from by
      calc
        I.left < d := hAd
        _ < c := hDc) (show d < I.right from by
      calc
        d < c := hDc
        _ < I.right := hCb) := by
  exact realCover.g2 I d c hAd hDc hCb

example (I J : QInterval) (hIJ : I ≤[qIntervalPreorder] J) :
    I ◁[realFormalTopology.cover] {J} := by
  exact realCover.ext hIJ

example (I : QInterval) :
    I ◁[realFormalTopology.cover] (fun _ => True) := by
  apply realCover.trans (realCover.g1 I)
  intro K hK
  exact realCover.refl trivial

example (I : QInterval) :
    I ◁[realFormalTopology.cover] (G1Family I↓[qIntervalPreorder] ∩ G1Family I↓[qIntervalPreorder]) := by
  exact realCover.loc (realCover.g1 I) (realCover.g1 I)

example (x : Rat) (I : QInterval) (hL : I.left < x) (hR : x < I.right) :
    barOfRat x I := by
  exact ⟨hL, hR⟩

example (f : Rat → Rat) (I J K : QInterval)
    (hIJ : Af f I J) (hJK : Af (fun x => x) J K) :
    Af f I K := by
  have hcomp := Af_comp f (fun x => x) I J K hIJ hJK
  simpa using hcomp

def I02 : QInterval := ⟨0, 2, by decide⟩
def I13 : QInterval := ⟨1, 3, by decide⟩
def I01 : QInterval := ⟨0, 1, by decide⟩
def I12 : QInterval := ⟨1, 2, by decide⟩
def I03 : QInterval := ⟨0, 3, by decide⟩

example : I12 ≤[qIntervalPreorder] I02 := by
  constructor
  · show (I02.left : Rat) ≤ I12.left
    decide
  · show (I12.right : Rat) ≤ I02.right
    decide

example :
    I12 ◁[realFormalTopology.cover] {I02} := by
  exact realCover.ext (show I12 ≤[qIntervalPreorder] I02 by
    constructor
    · show (I02.left : Rat) ≤ I12.left
      decide
    · show (I12.right : Rat) ≤ I02.right
      decide)

example :
    I02 ◁[realFormalTopology.cover] G1Family I02 := by
  exact realCover.g1 I02

example :
    I03 ◁[realFormalTopology.cover] G2Family I03 (1 : Rat) (2 : Rat)
      (show (I03.left : Rat) < 2 by decide)
      (show (1 : Rat) < I03.right by decide) := by
  exact realCover.g2 I03 1 2
    (show I03.left < (1 : Rat) by decide)
    (show (1 : Rat) < (2 : Rat) by decide)
    (show (2 : Rat) < I03.right by decide)

example : barOfRat (1 : Rat) I02 := by
  exact ⟨by decide, by decide⟩

example : ¬ barOfRat (3 : Rat) I02 := by
  intro h
  have h23 : ¬ ((3 : Rat) < 2) := by decide
  exact h23 h.2

example : Af (fun x : Rat => x) I02 I02 := by
  intro x hx0 hx2
  exact ⟨hx0, hx2⟩
