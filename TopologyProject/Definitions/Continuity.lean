import TopologyProject.Definitions.NatTopologies

def relPreimage {X Y : Type} (R : X → Y → Prop) (V : Subset Y) : Subset X :=
  λ a => ∃ b, V b ∧ R a b

/- Saturation closes a subset under the cover relation. -/
def saturation {X : Type} (S : FormalTopology X) (U : Subset X) : Subset X :=
  λ a => a ◁[S.cover] U

def relElemSubset {X Y : Type} (S : FormalTopology X) (R : X → Y → Prop) (a : X) (V : Subset Y) : Prop :=
  a ◁[S.cover] (relPreimage R V)

notation a " R[" S "|" R "] " V => relElemSubset S R a V

def relSubsetElem {X Y : Type} (R : X → Y → Prop) (U : Subset X) (b : Y) : Prop :=
  ∀ a : X, U a → R a b

notation U " Rₛ[" R "] " b => relSubsetElem R U b

def topSubset {Y : Type} (_T : FormalTopology Y) : Subset Y :=
  λ _ => True

def relElemWhole {X Y : Type} (S : FormalTopology X) (R : X → Y → Prop) (a : X) (T : FormalTopology Y) : Prop :=
  relElemSubset S R a (topSubset T)

notation a " R[" S "|" R "|" T "]" => relElemWhole S R a T

/- A continuity witness is a relation satisfying the four cover axioms below. -/
structure ContinuousMapping
  {X Y : Type}
  (S : FormalTopology X)
  (T : FormalTopology Y) where
  rel : X → Y → Prop
  ax1 : ∀ (a : X) (b : Y) (V : Subset Y), rel a b → T.cover b V → relElemSubset S rel a V
  ax2 : ∀ (a : X) (U : Subset X) (b : Y), S.cover a U → relSubsetElem rel U b → rel a b
  ax3 : ∀ a : X, a R[S|rel|T]
  ax4 : ∀ (a : X) (V W : Subset Y), relElemSubset S rel a V → relElemSubset S rel a W →
    relElemSubset S rel a (V↓[T.preorder] ∩ W↓[T.preorder])

def IsContinuousRel
  {X Y : Type}
  (S : FormalTopology X)
  (T : FormalTopology Y)
  (R : X → Y → Prop) : Prop :=
  ∃ f : ContinuousMapping S T, f.rel = R

def Econtinuous {X : Type} (S : FormalTopology X) (U : Subset X) :
    ContinuousMapping (closedSubspaceTopology S U) S where
  rel := Erel S U
  ax1 := by
    intro a b V hab hbV
    apply (closedSubspaceTopology S U).trans hab
    intro x hx
    subst hx
    change x ◁[S.cover] (U ∪ relPreimage (Erel S U) V)
    apply S.trans hbV
    intro y hyV
    apply S.refl
    right
    refine ⟨y, hyV, ?_⟩
    exact (closedSubspaceTopology S U).ext ((closedSubspaceTopology S U).preorder.refl y)
  ax2 := by
    intro a V b haV hVb
    exact (closedSubspaceTopology S U).trans haV hVb
  ax3 := by
    intro a
    apply (closedSubspaceTopology S U).refl
    refine ⟨a, trivial, ?_⟩
    exact (closedSubspaceTopology S U).ext ((closedSubspaceTopology S U).preorder.refl a)
  ax4 := by
    intro a V W haV haW
    have hV : a ◁[closedSubspaceCover S U] V := by
      apply (closedSubspaceTopology S U).trans haV
      intro x hx
      rcases hx with ⟨b, hbV, hxb⟩
      apply (closedSubspaceTopology S U).trans hxb
      intro y hy
      subst hy
      exact (closedSubspaceTopology S U).refl hbV
    have hW : a ◁[closedSubspaceCover S U] W := by
      apply (closedSubspaceTopology S U).trans haW
      intro x hx
      rcases hx with ⟨b, hbW, hxb⟩
      apply (closedSubspaceTopology S U).trans hxb
      intro y hy
      subst hy
      exact (closedSubspaceTopology S U).refl hbW
    have hloc : a ◁[closedSubspaceCover S U] (V↓[S.preorder] ∩ W↓[S.preorder]) :=
      (closedSubspaceTopology S U).loc hV hW
    apply (closedSubspaceTopology S U).trans hloc
    intro x hxVW
    apply (closedSubspaceTopology S U).refl
    refine ⟨x, hxVW, ?_⟩
    exact (closedSubspaceTopology S U).ext ((closedSubspaceTopology S U).preorder.refl x)


def natToEvenOddLeRel : ℕ → ℕ → Prop :=
  λ a b => evenOddPreorder.le a b

def natToEvenOddParityImpRel : ℕ → ℕ → Prop :=
  λ a b => (even a → even b) ∧ (odd a → odd b)

def natAddRel (k : ℕ) : ℕ → ℕ → Prop :=
  λ a b => b = a + k


def emptyPreorder : Preorder Empty :=
  { le := λ _ _ => False
    refl := by
      intro a
      cases a
    trans := by
      intro a b c hab hbc
      exact False.elim hab
  }

def emptyCover : Empty → Subset Empty → Prop :=
  λ _ _ => False

def emptyFormalTopology : FormalTopology Empty :=
  { preorder := emptyPreorder
    cover := emptyCover
    refl := by
      intro U a haU
      cases a
    trans := by
      intro U V a haU hUV
      cases a
    loc := by
      intro U V a haU haV
      cases a
    ext := by
      intro a b hab
      cases a
  }

def emptyToNatRel : Empty → ℕ → Prop :=
  λ _ _ => False

def emptyToNatContinuous : ContinuousMapping emptyFormalTopology natFormalTopology :=
  { rel := emptyToNatRel
    ax1 := by
      intro a b V hab hbV
      cases a
    ax2 := by
      intro a U b haU hUb
      cases a
    ax3 := by
      intro a
      cases a
    ax4 := by
      intro a V W haV haW
      cases a
  }



def boolPreorder : Preorder Bool :=
  { le := λ a b => a = false ∨ b = true
    refl := by
      intro a
      cases a with
      | false =>
          left
          rfl
      | true =>
          right
          rfl
    trans := by
      intro a b c hab hbc
      cases a <;> cases b <;> cases c <;> simp at hab hbc ⊢
  }

def boolCover : Bool → Subset Bool → Prop :=
  λ a U => ∃ b, U b ∧ boolPreorder.le a b

def boolFormalTopology : FormalTopology Bool :=
  { preorder := boolPreorder
    cover := boolCover
    refl := by
      intro U a haU
      exact ⟨a, haU, boolPreorder.refl a⟩
    trans := by
      intro U V a haU hUV
      obtain ⟨b, hbU, ha_le_b⟩ := haU
      obtain ⟨c, hcV, hb_le_c⟩ := hUV b hbU
      exact ⟨c, hcV, boolPreorder.trans ha_le_b hb_le_c⟩
    loc := by
      intro U V a haU haV
      obtain ⟨b, hbU, ha_le_b⟩ := haU
      obtain ⟨c, hcV, ha_le_c⟩ := haV
      refine ⟨a, ?_, boolPreorder.refl a⟩
      constructor
      · exact ⟨b, hbU, ha_le_b⟩
      · exact ⟨c, hcV, ha_le_c⟩
    ext := by
      intro a b ha_le_b
      exact ⟨b, rfl, ha_le_b⟩
  }

def boolToNatContinuous : ContinuousMapping boolFormalTopology natFormalTopology :=
  { rel := λ _ _ => True
    ax1 := by
      intro a b V hab hbV
      obtain ⟨n, hnV, hb_le_n⟩ := hbV
      exact boolFormalTopology.refl (a := a) (by
        exact ⟨n, hnV, trivial⟩)
    ax2 := by
      intro a U b haU hUb
      trivial
    ax3 := by
      intro a
      exact boolFormalTopology.refl (a := a) (by
        exact ⟨0, trivial, trivial⟩)
    ax4 := by
      intro a V W haV haW
      obtain ⟨xV, hxV_pre, ha_le_xV⟩ := haV
      obtain ⟨xW, hxW_pre, ha_le_xW⟩ := haW
      obtain ⟨v, hvV, hxV_rel⟩ := hxV_pre
      obtain ⟨w, hwW, hxW_rel⟩ := hxW_pre
      have hInter : Nat.min v w ∈ (V↓[natFormalTopology.preorder] ∩ W↓[natFormalTopology.preorder]) := by
        constructor
        · exact ⟨v, hvV, Nat.min_le_left v w⟩
        · exact ⟨w, hwW, Nat.min_le_right v w⟩
      exact boolFormalTopology.refl (a := a) (by
        exact ⟨Nat.min v w, hInter, trivial⟩)
  }


def natToBoolTrueRel : ℕ → Bool → Prop :=
  λ _ b => b = true

def natToBoolTrueContinuous : ContinuousMapping natFormalTopology boolFormalTopology :=
  { rel := natToBoolTrueRel
    ax1 := by
      intro a b V hab hbV
      rw [natToBoolTrueRel] at hab
      subst hab
      obtain ⟨c, hcV, htrue_le_c⟩ := hbV
      have hc_true : c = true := by
        cases c with
        | false =>
          cases htrue_le_c with
          | inl h =>
            cases h
          | inr h =>
            cases h
        | true =>
            rfl
      subst hc_true
      exact natFormalTopology.refl (a := a) (by
        exact ⟨true, by exact hcV, rfl⟩)
    ax2 := by
      intro a U b haU hUb
      have hb_true : b = true := by
        by_cases hb : b = true
        · exact hb
        · cases b with
          | false =>
              exfalso
              have hU_nonempty : ∃ u, u ∈ U := by
                obtain ⟨u, huU, ha_le_u⟩ := haU
                exact ⟨u, huU⟩
              obtain ⟨u, huU⟩ := hU_nonempty
              have hu_rel : natToBoolTrueRel u false := hUb u huU
              rw [natToBoolTrueRel] at hu_rel
              contradiction
          | true =>
              contradiction
      rw [natToBoolTrueRel]
      exact hb_true
    ax3 := by
      intro a
      exact natFormalTopology.refl (a := a) (by
        exact ⟨true, trivial, rfl⟩)
    ax4 := by
      intro a V W haV haW
      obtain ⟨v, hvPre, ha_le_v⟩ := haV
      obtain ⟨w, hwPre, ha_le_w⟩ := haW
      obtain ⟨bv, hbvV, hv_rel⟩ := hvPre
      obtain ⟨bw, hbwW, hw_rel⟩ := hwPre
      rw [natToBoolTrueRel] at hv_rel hw_rel
      subst hv_rel
      subst hw_rel
      have hInter : true ∈ (V↓[boolFormalTopology.preorder] ∩ W↓[boolFormalTopology.preorder]) := by
        constructor
        · exact ⟨true, hbvV, boolPreorder.refl true⟩
        · exact ⟨true, hbwW, boolPreorder.refl true⟩
      exact natFormalTopology.refl (a := a) (by
        exact ⟨true, hInter, rfl⟩)
  }


def natOrderContinuous : ContinuousMapping natFormalTopology natFormalTopology :=
  { rel := λ a b => a ≤ b
    ax1 := by
      intro a b V hab hbV
      obtain ⟨n, hnV, hb_le_n⟩ := hbV
      refine ⟨n, ?_, Nat.le_trans hab hb_le_n⟩
      exact ⟨n, hnV, Nat.le_refl n⟩
    ax2 := by
      intro a U b haU hUb
      obtain ⟨u, huU, ha_le_u⟩ := haU
      have hu_le_b : u ≤ b := hUb u huU
      exact Nat.le_trans ha_le_u hu_le_b
    ax3 := by
      intro a
      refine ⟨a, ?_, Nat.le_refl a⟩
      exact ⟨a, trivial, Nat.le_refl a⟩
    ax4 := by
      intro a V W haV haW
      obtain ⟨x, hxPre, ha_le_x⟩ := haV
      obtain ⟨y, hyPre, ha_le_y⟩ := haW
      obtain ⟨v, hvV, hx_le_v⟩ := hxPre
      obtain ⟨w, hwW, hy_le_w⟩ := hyPre
      refine ⟨Nat.min v w, ?_, ?_⟩
      · refine ⟨Nat.min v w, ?_, Nat.le_refl _⟩
        constructor
        · exact ⟨v, hvV, Nat.min_le_left v w⟩
        · exact ⟨w, hwW, Nat.min_le_right v w⟩
      · exact (Nat.le_min).2 ⟨Nat.le_trans ha_le_x hx_le_v, Nat.le_trans ha_le_y hy_le_w⟩
  }

def identityRel {X : Type} (S : FormalTopology X) : X → X → Prop :=
  λ a b => a ◁[S.cover] {b}

def identityContinuous {X : Type} (S : FormalTopology X) : ContinuousMapping S S where
  rel := identityRel S
  ax1 := by
    intro a b V hab hbV
    -- hab : a ◁[S] {b},  hbV : b ◁[S] V
    -- need: relElemSubset S (identityRel S) a V = a ◁[S] {x | ∃ y, V y ∧ x ◁[S] {y}}
    apply S.trans hab
    intro x (hx : x = b)
    subst hx
    apply S.trans hbV
    intro y hy
    apply S.refl
    exact ⟨y, hy, S.ext (S.preorder.refl y)⟩
  ax2 := by
    intro a U b haU hUb
    exact S.trans haU hUb
  ax3 := by
    intro a
    apply S.refl
    exact ⟨a, trivial, S.ext (S.preorder.refl a)⟩
  ax4 := by
    intro a V W haV haW
    apply S.trans (S.loc haV haW)
    intro x hx
    rcases hx with ⟨hxV, hxW⟩
    rcases hxV with ⟨y, hy, hxy⟩
    rcases hxW with ⟨z, hz, hxz⟩
    rcases hy with ⟨v, hvV, hyv⟩
    rcases hz with ⟨w, hwW, hzw⟩
    have hxv : x ◁[S.cover] {v} := S.trans (S.ext hxy) (by
      intro t ht
      subst ht
      exact hyv)
    have hxw : x ◁[S.cover] {w} := S.trans (S.ext hxz) (by
      intro t ht
      subst ht
      exact hzw)
    apply S.trans (S.loc hxv hxw)
    intro u hu
    rcases hu with ⟨huv, huw⟩
    rcases huv with ⟨u1, hu1, h_le_u1⟩
    rcases huw with ⟨u2, hu2, h_le_u2⟩
    apply S.refl
    refine ⟨u, ?_, S.ext (S.preorder.refl u)⟩
    constructor
    · refine ⟨u1, ?_, h_le_u1⟩
      have hu1' : u1 = v := hu1
      subst hu1'
      exact hvV
    · refine ⟨u2, ?_, h_le_u2⟩
      have hu2' : u2 = w := hu2
      subst hu2'
      exact hwW

def compRel {X Y Z : Type} (R₁ : X → Y → Prop) (R₂ : Y → Z → Prop)
    (S : FormalTopology X) : X → Z → Prop :=
  λ a c => a ◁[S.cover] (relPreimage R₁ (relPreimage R₂ {c}))

notation R₂ " ∘r[" S "] " R₁ => compRel R₁ R₂ S

def compContinuous {X Y Z : Type}
    {S : FormalTopology X} {T : FormalTopology Y} {U : FormalTopology Z}
    (f : ContinuousMapping S T) (g : ContinuousMapping T U) :
    ContinuousMapping S U where
  rel := g.rel ∘r[S] f.rel
  ax1 := by
    intro a c W hac hcW
    apply S.trans hac
    intro x hx
    rcases hx with ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    have hyW : relElemSubset T g.rel y W := by
      have hcW' : z ◁[U.cover] W := by
        subst hz
        exact hcW
      exact g.ax1 y z W hyz hcW'
    have hxW : relElemSubset S f.rel x (relPreimage g.rel W) :=
      f.ax1 x y (relPreimage g.rel W) hxy hyW
    have hcomp : relPreimage f.rel (relPreimage g.rel W) ◁ₛ[S.cover] relPreimage (g.rel ∘r[S] f.rel) W := by
      intro u hu
      rcases hu with ⟨v, ⟨w, hwW, hvw⟩, huv⟩
      apply S.refl
      refine ⟨w, hwW, ?_⟩
      apply S.refl
      exact ⟨v, ⟨w, rfl, hvw⟩, huv⟩
    exact S.trans hxW hcomp
  ax2 := by
    intro a V c haV hVc
    exact S.trans haV hVc
  ax3 := by
    intro a
    apply S.trans (f.ax3 a)
    intro x hx
    rcases hx with ⟨b, _, hxb⟩
    have hxtop : relElemSubset S f.rel x (relPreimage g.rel (topSubset U)) :=
      f.ax1 x b (relPreimage g.rel (topSubset U)) hxb (g.ax3 b)
    have hcompTop : relPreimage f.rel (relPreimage g.rel (topSubset U)) ◁ₛ[S.cover] relPreimage (g.rel ∘r[S] f.rel) (topSubset U) := by
      intro u hu
      rcases hu with ⟨v, ⟨w, hwTop, hvw⟩, huv⟩
      apply S.refl
      refine ⟨w, hwTop, ?_⟩
      apply S.refl
      exact ⟨v, ⟨w, rfl, hvw⟩, huv⟩
    exact S.trans hxtop hcompTop
  ax4 := by
    intro a V W haV haW
    have haV' : relElemSubset S f.rel a (relPreimage g.rel V) := by
      apply S.trans haV
      intro x hx
      rcases hx with ⟨z, hzV, hxz⟩
      apply S.trans hxz
      intro q hq
      rcases hq with ⟨y, ⟨u, hu, hyu⟩, hqy⟩
      have huV : V u := by
        have hu' : u = z := hu
        subst hu'
        exact hzV
      apply S.refl
      exact ⟨y, ⟨u, huV, hyu⟩, hqy⟩
    have haW' : relElemSubset S f.rel a (relPreimage g.rel W) := by
      apply S.trans haW
      intro x hx
      rcases hx with ⟨z, hzW, hxz⟩
      apply S.trans hxz
      intro q hq
      rcases hq with ⟨y, ⟨u, hu, hyu⟩, hqy⟩
      have huW : W u := by
        have hu' : u = z := hu
        subst hu'
        exact hzW
      apply S.refl
      exact ⟨y, ⟨u, huW, hyu⟩, hqy⟩
    have hloc : relElemSubset S f.rel a ((relPreimage g.rel V)↓[T.preorder] ∩ (relPreimage g.rel W)↓[T.preorder]) :=
      f.ax4 a (relPreimage g.rel V) (relPreimage g.rel W) haV' haW'
    apply S.trans hloc
    intro x hx
    rcases hx with ⟨y, ⟨hyV, hyW⟩, hxy⟩
    rcases hyV with ⟨y1, hy1, hy_le_y1⟩
    rcases hyW with ⟨y2, hy2, hy_le_y2⟩
    rcases hy1 with ⟨v, hvV, hy1v⟩
    rcases hy2 with ⟨w, hwW, hy2w⟩
    have hyv : g.rel y v :=
      g.ax2 y {y1} v (T.ext hy_le_y1) (by
        intro t ht
        subst ht
        exact hy1v)
    have hyw : g.rel y w :=
      g.ax2 y {y2} w (T.ext hy_le_y2) (by
        intro t ht
        subst ht
        exact hy2w)
    have hyV' : relElemSubset T g.rel y V := T.refl ⟨v, hvV, hyv⟩
    have hyW' : relElemSubset T g.rel y W := T.refl ⟨w, hwW, hyw⟩
    have hyVW : relElemSubset T g.rel y (V↓[U.preorder] ∩ W↓[U.preorder]) :=
      g.ax4 y V W hyV' hyW'
    have hxVW : relElemSubset S f.rel x (relPreimage g.rel (V↓[U.preorder] ∩ W↓[U.preorder])) :=
      f.ax1 x y (relPreimage g.rel (V↓[U.preorder] ∩ W↓[U.preorder])) hxy hyVW
    have hcompVW :
        relPreimage f.rel (relPreimage g.rel (V↓[U.preorder] ∩ W↓[U.preorder])) ◁ₛ[S.cover]
          relPreimage (g.rel ∘r[S] f.rel) (V↓[U.preorder] ∩ W↓[U.preorder]) := by
      intro u hu
      rcases hu with ⟨v, ⟨w, hwVW, hvw⟩, huv⟩
      apply S.refl
      refine ⟨w, hwVW, ?_⟩
      apply S.refl
      exact ⟨v, ⟨w, rfl, hvw⟩, huv⟩
    exact S.trans hxVW hcompVW

notation g " ⊚c " f => compContinuous f g
