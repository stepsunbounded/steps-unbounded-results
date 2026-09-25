import StepsUnboundedResults.HSC.CertPP12Anchored

open scoped Classical
open Finset

set_option maxRecDepth 100000

namespace HSC
namespace CertPP12
namespace Anchored

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## From the anchored system to the finite core -/

/-- The members other than the anchor. -/
def rest (S : Anchored ι) : Finset ι := univ.erase S.anchor

/-- Every point of `H` lies in the trace of a non-anchor member. -/
theorem trace_cover (S : Anchored ι) {p : Fin 60} (hp : p ∈ S.H) :
    ∃ i ∈ S.rest, p ∈ S.trace i := by
  have hpa : p ∈ S.point S.anchor := by rw [S.point_anchor]; exact hp
  rcases S.cover p with h2 | hnone
  · obtain ⟨j, hj, hpj⟩ := Util.exists_ne_of_two_le_card_filter hpa h2
    exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, Finset.mem_inter.mpr ⟨hpj, hp⟩⟩
  · exact absurd hpa (hnone S.anchor)

/-- Reindexing a sum over all members by their sizes. -/
theorem sum_rest_eq_sizeSet (S : Anchored ι) (F : ℕ → ℕ) :
    ∑ i ∈ S.rest, F (S.sz i) = ∑ m ∈ S.sizeSet, F m := by
  rw [rest, sizeSet]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

/-- Reindexing a sum over all members except `i` by their sizes. -/
theorem sum_rest_erase_eq (S : Anchored ι) (i : ι) (F : ℕ → ℕ) :
    ∑ j ∈ S.rest.erase i, F (S.sz j) = ∑ n ∈ S.sizeSet.erase (S.sz i), F n := by
  rw [rest, sizeSet, ← Finset.image_erase S.sz_injective]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

/-- Reindexing a sum over all members except `i` and `j` by their sizes. -/
theorem sum_rest_erase_erase_eq (S : Anchored ι) (i j : ι) (F : ℕ → ℕ) :
    ∑ k ∈ (S.rest.erase i).erase j, F (S.sz k)
      = ∑ n ∈ (S.sizeSet.erase (S.sz i)).erase (S.sz j), F n := by
  rw [rest, sizeSet, ← Finset.image_erase S.sz_injective, ← Finset.image_erase S.sz_injective]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

theorem sum_dval_eq_delta (S : Anchored ι) :
    ∑ i ∈ S.rest, S.dval i = delta S.dOf := by
  have h1 : ∀ i ∈ S.rest, S.dval i = toFun S.dOf (S.sz i) := by
    intro i hi
    have hia : i ≠ S.anchor := (Finset.mem_erase.mp hi).1
    rw [toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨i, hia, rfl⟩)]
    exact (dOf_apply S hia).symm
  rw [Finset.sum_congr rfl h1, sum_rest_eq_sizeSet S (toFun S.dOf)]
  rfl

/-- The lower traces plus their total deficiency equal the total trace capacity. -/
theorem trace_sum_add_delta (S : Anchored ι) :
    (∑ i ∈ S.rest, (S.trace i).card) + delta S.dOf = sizeSum S.sizeSet := by
  have h1 : ∀ i ∈ S.rest, (S.trace i).card = traceCap (S.sz i) - S.dval i := by
    intro i _
    have := trace_card_le S i
    rw [dval]
    omega
  have h2 : ∀ i ∈ S.rest, traceCap (S.sz i) - S.dval i + S.dval i = traceCap (S.sz i) :=
    fun i _ => Nat.sub_add_cancel (Nat.sub_le _ _)
  have h3 : ∑ i ∈ S.rest, S.dval i = delta S.dOf := sum_dval_eq_delta S
  have h4 : ∑ i ∈ S.rest, traceCap (S.sz i) = sizeSum S.sizeSet := sum_rest_eq_sizeSet S traceCap
  rw [Finset.sum_congr rfl h1, ← h3, ← Finset.sum_add_distrib, Finset.sum_congr rfl h2, h4]

/-- The cover of `H` forces the selected size set into the finite core. -/
theorem sizeSum_ge (S : Anchored ι) : 12 ≤ sizeSum S.sizeSet := by
  have h1 := Util.card_le_sum_card_of_subset_biUnion S.rest S.trace S.H
    (fun p hp => trace_cover S hp)
  have h2 := trace_sum_add_delta S
  have h3 : S.H.card = 12 := S.card_H
  omega

theorem dOf_mem_tuples (S : Anchored ι) : S.dOf ∈ tuples S.sizeSet := by
  rw [tuples, Fintype.mem_piFinset]
  intro n
  have hsz : S.sz (S.invOf n.val) = n.val := sz_invOf S n.property
  have hdof : S.dOf n = S.dval (S.invOf n.val) := by simp only [dOf, dval, hsz]
  rw [hdof]
  have h := dval_mem S (S.invOf n.val)
  rwa [hsz] at h

theorem dOf_admissible (S : Anchored ι) : admissible S.dOf := by
  rw [admissible, slack]
  have h1 := Util.card_le_sum_card_of_subset_biUnion S.rest S.trace S.H
    (fun p hp => trace_cover S hp)
  have h2 := trace_sum_add_delta S
  have h3 : S.H.card = 12 := S.card_H
  omega

/-- Every outside point is shared with a second member. -/
theorem b_le_sum_out (S : Anchored ι) (i : ι) :
    S.b i ≤ ∑ j ∈ S.rest.erase i, (S.out i j).card := by
  by_cases hi : i = S.anchor
  · subst hi
    rw [b, point_anchor, Finset.sdiff_self, Finset.card_empty]
    exact Nat.zero_le _
  · have hsub : S.point i \ S.H ⊆ (S.rest.erase i).biUnion (fun j => S.out i j) := by
      intro p hp
      obtain ⟨hpi, hpH⟩ := Finset.mem_sdiff.mp hp
      rcases S.cover p with h2 | hnone
      · obtain ⟨j, hji, hpj⟩ := Util.exists_ne_of_two_le_card_filter hpi h2
        have hja : j ≠ S.anchor := by
          rintro rfl
          exact hpH (by rw [point_anchor] at hpj; exact hpj)
        exact Finset.mem_biUnion.mpr ⟨j,
          Finset.mem_erase.mpr ⟨hji, Finset.mem_erase.mpr ⟨hja, Finset.mem_univ j⟩⟩,
          Finset.mem_inter.mpr ⟨hp, Finset.mem_sdiff.mpr ⟨hpj, hpH⟩⟩⟩
      · exact absurd hpi (hnone i)
    calc S.b i = (S.point i \ S.H).card := rfl
      _ ≤ ((S.rest.erase i).biUnion fun j => S.out i j).card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ S.rest.erase i, (S.out i j).card := Finset.card_biUnion_le

/-- The capacity matrix bounds every outside intersection. -/
theorem out_card_le_cap (S : Anchored ι) {i j : ι} (hij : i ≠ j) :
    (S.out i j).card ≤ min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j))) := by
  have h := S.pair_cap i j hij
  have h1 : S.b i = S.sz i - (S.point i ∩ S.H).card := b_eq S i
  have h2 : S.b j = S.sz j - (S.point j ∩ S.H).card := b_eq S j
  rw [h1, h2]
  exact h

theorem sum_min_eq_rhs (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) :
    ∑ j ∈ S.rest.erase i, min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j)))
      = rhs S.dOf (S.sz i) := by
  have h1 : ∀ j ∈ S.rest.erase i,
      min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j)))
        = min (bval S.dOf (S.sz i)) (min (bval S.dOf (S.sz j)) (pairCap (S.sz i) (S.sz j))) := by
    intro j hj
    have hja : j ≠ S.anchor := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    rw [b_eq_bval S hi, b_eq_bval S hja]
  rw [Finset.sum_congr rfl h1, sum_rest_erase_eq S i
    (fun n => min (bval S.dOf (S.sz i)) (min (bval S.dOf n) (pairCap (S.sz i) n)))]
  rfl

/-- A universally violating member refutes the system. -/
theorem false_of_witness (S : Anchored ι) (m : ℕ) (hm : m ∈ S.sizeSet)
    (hviol : ∀ d ∈ tuples S.sizeSet, admissible d → rhs d m < bval d m) : False := by
  obtain ⟨i, hi, hsz⟩ := (mem_sizeSet_iff S).mp hm
  have h1 := b_le_sum_out S i
  have h3 : rhs S.dOf m < bval S.dOf m :=
    hviol S.dOf (dOf_mem_tuples S) (dOf_admissible S)
  have h4 : bval S.dOf m = S.b i := by
    rw [← hsz]
    exact (b_eq_bval S hi).symm
  have h5 : S.b i ≤ ∑ j ∈ S.rest.erase i, min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j))) :=
    le_trans h1 (Finset.sum_le_sum fun j hj => out_card_le_cap S (Finset.mem_erase.mp hj).1.symm)
  have h2 : ∑ j ∈ S.rest.erase i, min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j)))
      = rhs S.dOf m := by
    rw [← hsz]
    exact sum_min_eq_rhs S hi
  omega

/-! ## The final size-10 case analysis -/

theorem out_card_le_sizeContrib (S : Anchored ι) {i j : ι} (h10 : S.sz i = 10) (hj : j ≠ i)
    (hja : j ≠ S.anchor) : (S.out i j).card ≤ sizeContrib S.dOf (S.sz j) := by
  have hcap : (S.out i j).card ≤ min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j))) :=
    out_card_le_cap S hj.symm
  have hbi : S.b i = 8 := b_of_sz_ten S h10
  have hbj : S.b j = S.sz j - traceCap (S.sz j) + S.dval j := by
    rw [b_eq_bval S hja, bval]
    congr 1
    rw [toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨j, hja, rfl⟩)]
    exact dOf_apply S hja
  have htof : ∀ m : ℕ, S.sz j = m → toFun S.dOf m = S.dval j := by
    intro m hm
    rw [← hm, toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨j, hja, rfl⟩)]
    exact dOf_apply S hja
  have hdj := dval_mem S j
  have hmem := sz_mem_lower S hja
  have hne : S.sz j ≠ 10 := fun h => hj (S.sz_injective (by rw [h, h10]))
  simp only [lowerSizes, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h
  · have hd : S.dval j ≤ 1 := by
      rw [h] at hdj
      simp only [deficiencies, Finset.mem_insert, Finset.mem_singleton] at hdj
      omega
    have hbj1 : S.b j = S.dval j := by rw [hbj, h, traceCap_one]; omega
    have hsc : sizeContrib S.dOf (S.sz j) = S.dval j := by
      rw [h, sizeContrib, if_pos rfl]
      exact htof 1 h
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_one] at h2
    rw [hsc]
    omega
  · have hd : S.dval j ≤ 2 := by
      rw [h] at hdj
      simp only [deficiencies, Finset.mem_insert, Finset.mem_singleton] at hdj
      omega
    have hbj2 : S.b j = S.dval j := by rw [hbj, h, traceCap_two]; omega
    have hsc : sizeContrib S.dOf (S.sz j) = S.dval j := by
      rw [h, sizeContrib, if_neg (by norm_num : (2:ℕ) ≠ 1), if_pos rfl]
      exact htof 2 h
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_two] at h2
    rw [hsc]
    omega
  · have hbj3 : S.b j = S.dval j := by rw [hbj, h, traceCap_three]; omega
    have hsc : sizeContrib S.dOf (S.sz j) = min (S.dval j) 1 := by
      rw [h, sizeContrib, if_neg (by norm_num : (3:ℕ) ≠ 1), if_neg (by norm_num : (3:ℕ) ≠ 2),
        if_pos rfl, htof 3 h]
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_three] at h2
    rw [hsc]
    omega
  · have hbj4 : S.b j = S.dval j := by rw [hbj, h, traceCap_four]; omega
    have hsc : sizeContrib S.dOf (S.sz j) = min (S.dval j) 2 := by
      rw [h, sizeContrib, if_neg (by norm_num : (4:ℕ) ≠ 1), if_neg (by norm_num : (4:ℕ) ≠ 2),
        if_neg (by norm_num : (4:ℕ) ≠ 3), if_pos rfl, htof 4 h]
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_four] at h2
    rw [hsc]
    omega
  · have hd5 : S.dval j = 0 := by
      rw [h] at hdj
      simpa only [deficiencies, Finset.mem_singleton] using hdj
    have hsc : sizeContrib S.dOf (S.sz j) = (if excess S.dOf = 0 then 1 else 4) := by
      rw [h, sizeContrib, if_neg (by norm_num : (5:ℕ) ≠ 1), if_neg (by norm_num : (5:ℕ) ≠ 2),
        if_neg (by norm_num : (5:ℕ) ≠ 3), if_neg (by norm_num : (5:ℕ) ≠ 4), if_pos rfl]
      rfl
    have hbj5 : S.b j = 4 := by rw [hbj, h, traceCap_five, hd5]
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_five] at h2
    by_cases hex : excess S.dOf = 0
    · have hsum : ∑ k ∈ S.rest, (S.trace k).card = S.H.card := by
        have h1 := trace_sum_add_delta S
        have h2 := sizeSum_ge S
        have hadm : delta S.dOf ≤ slack S.sizeSet := dOf_admissible S
        have hge : slack S.sizeSet ≤ delta S.dOf := by
          have h : slack S.sizeSet - delta S.dOf = 0 := by rw [← excess]; exact hex
          omega
        have h4 : delta S.dOf = slack S.sizeSet := le_antisymm hadm hge
        have hsl : slack S.sizeSet = sizeSum S.sizeSet - 12 := rfl
        have h1' : sizeSum S.sizeSet = (∑ k ∈ S.rest, (S.trace k).card) + slack S.sizeSet := by
          rw [← h4]
          exact h1.symm
        have h7 : sizeSum S.sizeSet - slack S.sizeSet = ∑ k ∈ S.rest, (S.trace k).card :=
          Nat.sub_eq_of_eq_add h1'
        rw [S.card_H, ← h7, hsl, Nat.sub_sub_self h2]
      have hia : i ≠ S.anchor := by
        rintro rfl
        rw [S.sz_anchor] at h10
        exact absurd h10 (by norm_num)
      have hdisj : Disjoint (S.trace j) (S.trace i) :=
        Util.disjoint_of_sum_card_eq' S.rest S.trace S.H (fun k _ => trace_subset S k)
          (fun p hp => trace_cover S hp) hsum
          (Finset.mem_erase.mpr ⟨hja, Finset.mem_univ j⟩)
          (Finset.mem_erase.mpr ⟨hia, Finset.mem_univ i⟩) hj
      have h42 : ((S.point j \ S.H) ∩ (S.point i \ S.H)).card ≤ 1 :=
        S.lemma42 j i h h10 hdisj
      rw [hsc, if_pos hex, out_def, Finset.inter_comm]
      exact h42
    · rw [hsc, if_neg hex]
      omega
  · have hd6 : S.dval j = 0 ∨ 1 ≤ S.dval j := by
      rw [h] at hdj
      simp only [deficiencies, Finset.mem_insert, Finset.mem_singleton] at hdj
      omega
    have hsc : sizeContrib S.dOf (S.sz j) = 1 + S.dval j := by
      rw [h, sizeContrib, if_neg (by norm_num : (6:ℕ) ≠ 1), if_neg (by norm_num : (6:ℕ) ≠ 2),
        if_neg (by norm_num : (6:ℕ) ≠ 3), if_neg (by norm_num : (6:ℕ) ≠ 4),
        if_neg (by norm_num : (6:ℕ) ≠ 5), if_pos rfl, htof 6 h]
    have hbj6 : S.b j = 3 + S.dval j := by rw [hbj, h, traceCap_six]
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_six] at h2
    rcases hd6 with hd6 | hd6
    · have hcard3 : (S.trace j).card = 3 := by
        have hle := trace_card_le S j
        rw [h, traceCap_six] at hle
        rw [dval, h, traceCap_six] at hd6
        omega
      have h43 : ((S.point j \ S.H) ∩ (S.point i \ S.H)).card ≤ 1 := S.lemma43 j i h hcard3 h10
      rw [hsc, hd6, out_def, Finset.inter_comm]
      exact h43
    · rw [hsc]
      omega
  · exact absurd h hne

theorem sum_out_le_outsideBound (S : Anchored ι) {i : ι} (h10 : S.sz i = 10) :
    ∑ j ∈ S.rest.erase i, (S.out i j).card ≤ outsideBound S.dOf := by
  calc ∑ j ∈ S.rest.erase i, (S.out i j).card
      ≤ ∑ j ∈ S.rest.erase i, sizeContrib S.dOf (S.sz j) :=
        Finset.sum_le_sum fun j hj =>
          out_card_le_sizeContrib S h10 (Finset.mem_erase.mp hj).1
            ((Finset.mem_erase.mp (Finset.mem_erase.mp hj).2)).1
    _ = ∑ n ∈ S.sizeSet.erase (S.sz i), sizeContrib S.dOf n := sum_rest_erase_eq S i _
    _ = outsideBound S.dOf := by rw [h10]; rfl

theorem dval_eq_toFun (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) {m : ℕ} (hm : S.sz i = m) :
    S.dval i = toFun S.dOf m := by
  rw [← hm, toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨i, hi, rfl⟩)]
  exact (dOf_apply S hi).symm

theorem sum_out_le_outsideBound_sub_three (S : Anchored ι) {i i5 : ι} (h10 : S.sz i = 10)
    (h5 : S.sz i5 = 5) (hi5 : i5 ≠ i) (hfive : (S.out i i5).card ≤ 1)
    (hex : excess S.dOf ≠ 0) :
    ∑ j ∈ S.rest.erase i, (S.out i j).card ≤ outsideBound S.dOf - 3 := by
  have h5a : i5 ≠ S.anchor := by
    rintro rfl
    rw [S.sz_anchor] at h5
    exact absurd h5 (by norm_num)
  have h5mem : S.sz i5 ∈ S.sizeSet.erase 10 :=
    Finset.mem_erase.mpr ⟨by rw [h5]; norm_num, (mem_sizeSet_iff S).mpr ⟨i5, h5a, rfl⟩⟩
  have hi5mem : i5 ∈ S.rest.erase i :=
    Finset.mem_erase.mpr ⟨hi5, Finset.mem_erase.mpr ⟨h5a, Finset.mem_univ i5⟩⟩
  have hsc5 : sizeContrib S.dOf (S.sz i5) = 4 := by
    rw [h5, sizeContrib, if_neg (by norm_num : (5:ℕ) ≠ 1), if_neg (by norm_num : (5:ℕ) ≠ 2),
      if_neg (by norm_num : (5:ℕ) ≠ 3), if_neg (by norm_num : (5:ℕ) ≠ 4), if_pos rfl]
    rw [excess] at hex
    exact if_neg hex
  have hsplit : ∑ j ∈ S.rest.erase i, (S.out i j).card
      = (S.out i i5).card + ∑ k ∈ (S.rest.erase i).erase i5, (S.out i k).card :=
    (Finset.add_sum_erase (S.rest.erase i) (fun j => (S.out i j).card) hi5mem).symm
  have hrest : ∑ k ∈ (S.rest.erase i).erase i5, (S.out i k).card
      ≤ ∑ n ∈ (S.sizeSet.erase (S.sz i)).erase (S.sz i5), sizeContrib S.dOf n := by
    refine le_trans (Finset.sum_le_sum fun k hk => ?_)
      (le_of_eq (sum_rest_erase_erase_eq S i i5 _))
    exact out_card_le_sizeContrib S h10 (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      (Finset.mem_erase.mp ((Finset.mem_erase.mp (Finset.mem_erase.mp hk).2)).2).1
  have hbound : outsideBound S.dOf
      = sizeContrib S.dOf (S.sz i5)
        + ∑ n ∈ (S.sizeSet.erase (S.sz i)).erase (S.sz i5), sizeContrib S.dOf n := by
    rw [outsideBound, h10]
    exact (Finset.add_sum_erase (S.sizeSet.erase 10) (sizeContrib S.dOf) h5mem).symm
  rw [hsplit, hbound, hsc5]
  omega

/-- The `S = 12` anchored certificate is infeasible. -/
theorem no_anchored_system (S : Anchored ι) : False := by
  have hM : S.sizeSet ∈ sizeSets := by
    rw [sizeSets, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨sizeSet_subset S, sizeSum_ge S⟩
  have key : ∀ i : ι, S.sz i = 10 →
      8 ≤ ∑ j ∈ S.rest.erase i, (S.out i j).card ∧
        ∑ j ∈ S.rest.erase i, (S.out i j).card ≤ outsideBound S.dOf := by
    intro i hi
    have h8 : 8 ≤ ∑ j ∈ S.rest.erase i, (S.out i j).card := by
      have h := b_le_sum_out S i
      rwa [b_of_sz_ten S hi] at h
    exact ⟨h8, sum_out_le_outsideBound S hi⟩
  rcases finite_core S.sizeSet hM with ⟨m, hm, hviol⟩ | ⟨h10mem, hbound⟩ | ⟨hMB, h10mem, hbound⟩
  · exact false_of_witness S m hm hviol
  · obtain ⟨i10, -, hi10⟩ := (mem_sizeSet_iff S).mp h10mem
    obtain ⟨h8, hle⟩ := key i10 hi10
    have hb := hbound S.dOf (dOf_mem_tuples S) (dOf_admissible S)
    omega
  · obtain ⟨i10, hi10a, hi10⟩ := (mem_sizeSet_iff S).mp h10mem
    obtain ⟨h8, hle⟩ := key i10 hi10
    obtain ⟨hb8, hbeq⟩ := hbound S.dOf (dOf_mem_tuples S) (dOf_admissible S)
    by_cases hlt : outsideBound S.dOf < 8
    · omega
    · have heq : outsideBound S.dOf = 8 := by omega
      obtain ⟨hd3, hd4, hdelta⟩ := hbeq heq
      have h3mem : (3:ℕ) ∈ S.sizeSet := by rw [hMB]; decide
      have h4mem : (4:ℕ) ∈ S.sizeSet := by rw [hMB]; decide
      have h5mem : (5:ℕ) ∈ S.sizeSet := by rw [hMB]; decide
      obtain ⟨i3, hi3a, hi3⟩ := (mem_sizeSet_iff S).mp h3mem
      obtain ⟨i4, hi4a, hi4⟩ := (mem_sizeSet_iff S).mp h4mem
      obtain ⟨i5, hi5a, hi5⟩ := (mem_sizeSet_iff S).mp h5mem
      have hd3' : S.dval i3 = 0 := by rw [dval_eq_toFun S hi3a hi3, hd3]
      have hd4' : S.dval i4 = 0 := by rw [dval_eq_toFun S hi4a hi4, hd4]
      have ht3 : (S.trace i3).card = 3 := by
        have h := trace_card_le S i3
        rw [hi3, traceCap_three] at h
        rw [dval, hi3, traceCap_three] at hd3'
        omega
      have ht4 : (S.trace i4).card = 4 := by
        have h := trace_card_le S i4
        rw [hi4, traceCap_four] at h
        rw [dval, hi4, traceCap_four] at hd4'
        omega
      have ht5 : (S.trace i5).card = 1 := by
        have h := trace_card_le S i5
        rw [hi5, traceCap_five] at h
        have h0 : S.dval i5 = 0 := by
          have hd := dval_mem S i5
          rw [hi5] at hd
          simpa only [deficiencies, Finset.mem_singleton] using hd
        rw [dval, hi5, traceCap_five] at h0
        omega
      have ht10 : (S.trace i10).card = 2 := trace_card_eq_of_sz S hi10 attainableTraces_ten
      have h510 : i5 ≠ i10 := fun hh => by rw [hh] at hi5; omega
      by_cases hdisj : Disjoint (S.trace i5) (S.trace i10)
      · have hfive : (S.out i10 i5).card ≤ 1 := by
          have h := S.lemma42 i5 i10 hi5 hi10 (by rwa [trace, trace] at hdisj)
          rw [out_def, Finset.inter_comm]
          exact h
        have hex : excess S.dOf ≠ 0 := by
          have h16 : sizeSum S.sizeSet = 16 := by rw [hMB]; decide
          rw [excess, slack, h16, hdelta]
          norm_num
        have hle3 := sum_out_le_outsideBound_sub_three S hi10 hi5 h510 hfive hex
        omega
      · have hne2 : (S.trace i5 ∩ S.trace i10).Nonempty :=
          Finset.not_disjoint_iff_nonempty_inter.mp hdisj
        have hne1 : (S.trace i3 ∩ S.trace i4).Nonempty := by
          have h' : (S.trace i3 ∩ S.trace i4).card = 1 := S.lemma41 i3 i4 hi3 hi4 ht3 ht4
          exact Finset.card_pos.mp (by omega)
        have hsum : ∑ k ∈ S.rest, (S.trace k).card = 13 := by
          have h := trace_sum_add_delta S
          have h16 : sizeSum S.sizeSet = 16 := by rw [hMB]; decide
          rw [h16, hdelta] at h
          exact Nat.add_right_cancel (by rw [h])
        exact Util.no_two_collisions' S.rest S.trace S.H S.card_H
          (fun p hp => trace_cover S hp) hsum
          (Finset.mem_erase.mpr ⟨hi3a, Finset.mem_univ i3⟩)
          (Finset.mem_erase.mpr ⟨hi4a, Finset.mem_univ i4⟩)
          (Finset.mem_erase.mpr ⟨hi5a, Finset.mem_univ i5⟩)
          (Finset.mem_erase.mpr ⟨hi10a, Finset.mem_univ i10⟩)
          (fun hh => by rw [hh] at hi3; omega) (fun hh => by rw [hh] at hi3; omega)
          (fun hh => by rw [hh] at hi3; omega) (fun hh => by rw [hh] at hi4; omega)
          (fun hh => by rw [hh] at hi4; omega) h510 ht3 ht4 ht5 ht10 hne1 hne2

end Anchored
end CertPP12
end HSC
