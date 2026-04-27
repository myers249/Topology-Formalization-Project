import TopologyProject.Definitions.NatTopologiesBase
import TopologyProject.Theorems.NatTopologies

def natFormalTopology: FormalTopology ℕ :=
  { preorder := natPreorder
    cover := natCover,
    refl := by
      intro U m hmU
      have hn : ∃ n, (n ∈ U) ∧ Nat.le m n := by
        exists m
        constructor
        · exact hmU
        · exact Nat.le_refl m
      exact hn,
    trans := by
      intro U V a haU hUV
      have a_le_b : ∃ b, (b ∈ U) ∧ Nat.le a b := haU
      have hbV : ∀ b, (b ∈ U) → (b ◁[natCover] V) := hUV
      have b_le_c : ∀ b, (b ∈ U) → (∃ c, (c ∈ V) ∧ Nat.le b c) := hbV
      obtain ⟨b, a_le_b⟩ := a_le_b
      obtain ⟨c, b_le_c⟩ := b_le_c b a_le_b.1
      have a_le_c : a ≤[natPreorder] c := natPreorder.trans a_le_b.right b_le_c.right
      exists c
      constructor
      · exact b_le_c.left
      · exact a_le_c
    loc := by
      intro U V a haU haV
      obtain ⟨b, hbU⟩ := haU
      obtain ⟨c, hcV⟩ := haV
      cases Nat.le_total b c with
        |inl h =>
          have intersection := intersection_of_downClosures natPreorder U V b c hbU.left hcV.left h
          exists b
          constructor
          · exact intersection
          · exact hbU.right
        |inr h =>
          have intersection := intersection_of_downClosures natPreorder V U c b hcV.left hbU.left h
          exists c
          constructor
          · exact intersection.symm
          · exact hcV.right
    ext := by
      intro a b a_le_b
      exists b
  }

open Classical

def evenOddPreorder : Preorder ℕ :=
  { le := λ a b => (even a ∧ even b ∧ a ≤ b) ∨ (even a ∧ odd b) ∨ (odd a ∧ odd b ∧ Nat.le a b),
    refl := by
      intro a
      by_cases hae : even a
      · left
        constructor
        · exact hae
        · constructor
          · exact hae
          · exact Nat.le_refl a
      right
      right
      constructor
      · exact (odd_even_opposite a).mpr hae
      · constructor
        · exact (odd_even_opposite a).mpr hae
        · exact Nat.le_refl a
    trans := by
      intro a b c hab hbc
      cases hab with
      | inl hab_even =>
        cases hbc with
        | inl hbc_even =>
            left
            constructor
            · exact hab_even.left
            constructor
            · exact hbc_even.right.left
            · exact Nat.le_trans hab_even.right.right hbc_even.right.right
        | inr hbc_odd =>
            right; left
            constructor
            · exact hab_even.left
            · cases hbc_odd with
              | inl h =>
                exact h.right
              | inr h =>
                exact h.right.left
      | inr hab_rest =>
        cases hab_rest with
        | inl hab_even_odd =>
            cases hbc with
            | inl hbc_even =>
              have hbo : odd b := hab_even_odd.right
              have hbe : even b := hbc_even.left
              have hcontra : False := (even_odd_opposite b).mp hbe hbo
              exact False.elim hcontra
            | inr hbc_odd =>
                right; left
                constructor
                · exact hab_even_odd.left
                · cases hbc_odd with
                  | inl h =>
                    exact h.right
                  | inr h =>
                    exact h.right.left
        | inr hab_odd =>
            cases hbc with
            | inl hbc_even =>
              have hbo : odd b := hab_odd.right.left
              have hbe : even b := hbc_even.left
              have hcontra : False := (even_odd_opposite b).mp hbe hbo
              exact False.elim hcontra
            | inr hbc_odd =>
                right; right
                constructor
                · exact hab_odd.left
                constructor
                · cases hbc_odd with
                  | inl h =>
                    exact h.right
                  | inr h =>
                    exact h.right.left
                · cases hbc_odd with
                  | inl h =>
                    have hbo : odd b := hab_odd.right.left
                    have hbe : even b := h.left
                    have hcontra : False := (even_odd_opposite b).mp hbe hbo
                    exact False.elim hcontra
                  | inr h =>
                    exact Nat.le_trans hab_odd.right.right h.right.right
}

def evenOddCover : ℕ → Subset ℕ → Prop :=
  λ m U => ∃ n, (n ∈ U) ∧ evenOddPreorder.le m n

def evenOddFormalTopology: FormalTopology ℕ :=
  { preorder := evenOddPreorder
    cover := evenOddCover,
    refl := by
      intro U m hmU
      exists m
      constructor
      · exact hmU
      · exact evenOddPreorder.refl m
    trans := by
      intro U V a haU hUV
      obtain ⟨b, hbU, ha_le_b⟩ := haU
      obtain ⟨c, hcV, hb_le_c⟩ := hUV b hbU
      exists c
      constructor
      · exact hcV
      · exact evenOddPreorder.trans ha_le_b hb_le_c
    loc := by
      intro U V a haU haV
      obtain ⟨b, hbUin, ha_le_b⟩ := haU
      obtain ⟨c, hcVin, ha_le_c⟩ := haV
      refine ⟨a, ?_, evenOddPreorder.refl a⟩
      constructor
      · exact ⟨b, hbUin, ha_le_b⟩
      · exact ⟨c, hcVin, ha_le_c⟩
    ext := by
      intro a b a_le_b
      refine ⟨b, ?_, a_le_b⟩
      rfl
  }
