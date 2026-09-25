import StepsUnboundedResults.HSC.CertPPSixOutside

open scoped BigOperators
open Finset

namespace HSC.CertPP

variable {G : Type*} [Group G] [Fintype G]

theorem certPP_anchor_six (H : Subgroup G) (hH : Nat.card H = 6)
    {ι : Type*} [Fintype ι] (K : ι → Subgroup G) (x : ι → G) (i₀ : ι)
    (hanchor : lcoset (K i₀) (x i₀) = (H : Set G))
    (hsize : ∀ i, Nat.card (K i) ≤ 6)
    (hdist : ∀ i j, i ≠ j → Nat.card (K i) ≠ Nat.card (K j))
    (hcover : ∀ g : G, Nat.card {i : ι // g ∈ lcoset (K i) (x i)} ≠ 1) :
    False := by
  classical
  set s : Finset ι := Finset.univ.erase i₀ with hs
  have hmem_s : ∀ i, i ∈ s ↔ i ≠ i₀ := by intro i; rw [hs]; simp
  have hn0 : Nat.card (K i₀) = 6 := by
    have h1 : ((H : Set G)).ncard = 6 := ((Nat.card_coe_set_eq (H : Set G)).symm).trans hH
    have h2 : ((H : Set G)).ncard = Nat.card (K i₀) := by
      rw [← ncard_lcoset (K i₀) (x i₀), hanchor]
    omega
  have hn1 : ∀ i ∈ s, 1 ≤ Nat.card (K i) := by
    intro i _
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨1, (K i).one_mem⟩⟩
  have hn5 : ∀ i ∈ s, Nat.card (K i) ≤ 5 := by
    intro i hi
    have hne : i ≠ i₀ := (hmem_s i).mp hi
    have h4 : Nat.card (K i) ≠ 6 := fun h => hdist i i₀ hne (h.trans hn0.symm)
    have := hsize i
    omega
  have hinj : Set.InjOn (fun i => Nat.card (K i)) (↑s : Set ι) := by
    intro i _ j _ hij
    by_contra hne
    exact hdist i j hne hij
  have hcoverH : ∀ h : G, h ∈ (H : Set G) → ∃ i, i ≠ i₀ ∧ h ∈ lcoset (K i) (x i) := by
    intro h hh
    have hpos : 0 < Nat.card {i : ι // h ∈ lcoset (K i) (x i)} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨i₀, by rw [hanchor]; exact hh⟩⟩
    have hne1 : Nat.card {i : ι // h ∈ lcoset (K i) (x i)} ≠ 1 := hcover h
    have htwo : 2 ≤ Nat.card {i : ι // h ∈ lcoset (K i) (x i)} := by omega
    rw [Nat.card_eq_fintype_card] at htwo
    have hex : ∃ i j : {i : ι // h ∈ lcoset (K i) (x i)}, i ≠ j := by
      by_contra hc
      push Not at hc
      have : Subsingleton {i : ι // h ∈ lcoset (K i) (x i)} := ⟨fun a b => hc a b⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr this
      omega
    obtain ⟨i, j, hij⟩ := hex
    by_cases hi : (i : ι) = i₀
    · refine ⟨j, ?_, j.2⟩
      rintro rfl
      exact hij (Subtype.ext hi)
    · exact ⟨i, hi, i.2⟩
  have hHsub : (H : Set G) ⊆ ⋃ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)) := by
    intro h hh
    obtain ⟨i, hi, hhi⟩ := hcoverH h hh
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨(hmem_s i).mpr hi, hhi, hh⟩⟩
  have hsum6 : 6 ≤ ∑ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard := by
    have hHn : ((H : Set G)).ncard = 6 :=
      ((Nat.card_coe_set_eq (H : Set G)).symm).trans hH
    have h1 : ((H : Set G)).ncard
        ≤ (⋃ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G))).ncard := Set.ncard_le_ncard hHsub
    have h2 := ncard_iUnion_finset_le s (fun i => lcoset (K i) (x i) ∩ (H : Set G))
    omega
  have hdvd : ∀ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard = 0
      ∨ ((lcoset (K i) (x i) ∩ (H : Set G)).ncard ∣ Nat.card (K i)
          ∧ (lcoset (K i) (x i) ∩ (H : Set G)).ncard ∣ 6) := by
    intro i _
    by_cases hne : (lcoset (K i) (x i) ∩ (H : Set G)).Nonempty
    · obtain ⟨h1, h2⟩ := ncard_trace_dvd hne
      exact Or.inr ⟨h1, by rw [hH] at h2; exact h2⟩
    · refine Or.inl ?_
      rw [Set.ncard_eq_zero]
      exact Set.not_nonempty_iff_eq_empty.mp hne
  have hale : ∀ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard ≤ Nat.card (K i) := by
    intro i hi
    rcases hdvd i hi with h | h
    · omega
    · exact Nat.le_of_dvd (by have := hn1 i hi; omega) h.1
  have hsieve : ∀ i ∈ s, Nat.card (K i) - (lcoset (K i) (x i) ∩ (H : Set G)).ncard = 0
      ∨ Nat.card (K i) - (lcoset (K i) (x i) ∩ (H : Set G)).ncard
        ≤ ∑ j ∈ s.erase i, min (Nat.card (K j) - (lcoset (K j) (x j) ∩ (H : Set G)).ncard)
            (Nat.gcd (Nat.card (K i)) (Nat.card (K j))) := by
    intro i hi
    have hbd' : ∀ j, (lcoset (K j) (x j) \ (H : Set G)).ncard
        = Nat.card (K j) - (lcoset (K j) (x j) ∩ (H : Set G)).ncard := by
      intro j
      have hsplit : (lcoset (K j) (x j)).ncard
          = (lcoset (K j) (x j) ∩ (H : Set G)).ncard
            + (lcoset (K j) (x j) \ (H : Set G)).ncard := by
        rw [← Set.ncard_union_eq (s := lcoset (K j) (x j) ∩ (H : Set G))
          (t := lcoset (K j) (x j) \ (H : Set G)) ?_ (Set.toFinite _) (Set.toFinite _),
          Set.inter_union_sdiff]
        rw [Set.disjoint_left]
        intro y hy hy'
        exact hy'.2 hy.2
      have h1 := ncard_lcoset (K j) (x j)
      omega
    rcases Nat.eq_zero_or_pos ((lcoset (K i) (x i) \ (H : Set G)).ncard) with h0 | hpos
    · exact Or.inl (by rw [← hbd' i]; omega)
    · refine Or.inr ?_
      have hs := outside_sieve' s (fun j => lcoset (K j) (x j)) (H : Set G) i hi
        (fun g _ => hcover g) (fun j hj => by
          by_contra hc
          obtain ⟨y, hy, hyH⟩ := Set.not_subset.mp hc
          have hji : j = i₀ := by
            by_contra hne
            exact hj ((hmem_s j).mpr hne)
          rw [hji, hanchor] at hy
          exact hyH hy)
      have hmain : (lcoset (K i) (x i) \ (H : Set G)).ncard
          ≤ ∑ j ∈ s.erase i, min (Nat.card (K j) - (lcoset (K j) (x j) ∩ (H : Set G)).ncard)
              (Nat.gcd (Nat.card (K i)) (Nat.card (K j))) := by
        refine le_trans hs (Finset.sum_le_sum (fun j hj => ?_))
        refine le_min ?_ ?_
        · rw [← hbd' j]
          exact Set.ncard_le_ncard Set.inter_subset_right
        · have h1 : ((lcoset (K i) (x i) \ (H : Set G)) ∩
              (lcoset (K j) (x j) \ (H : Set G))).ncard
              ≤ (lcoset (K i) (x i) ∩ lcoset (K j) (x j)).ncard :=
            Set.ncard_le_ncard (fun y hy => ⟨hy.1.1, hy.2.1⟩)
          have h2 := ncard_lcoset_inter_le' (K := K i) (L := K j) (x i) (x j)
          have h3 : Nat.card (K i ⊓ K j : Subgroup G) ∣ Nat.card (K i) :=
            Subgroup.card_dvd_of_le inf_le_left
          have h4 : Nat.card (K i ⊓ K j : Subgroup G) ∣ Nat.card (K j) :=
            Subgroup.card_dvd_of_le inf_le_right
          have h5 : Nat.card (K i ⊓ K j : Subgroup G)
              ≤ Nat.gcd (Nat.card (K i)) (Nat.card (K j)) := by
            refine Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by have := hn1 i hi; omega)) ?_
            exact Nat.dvd_gcd h3 h4
          omega
      rwa [← hbd' i]
  obtain ⟨hsum_eq, ⟨i3, hi3s, hi3a⟩, ⟨i2, hi2s, hi2a⟩⟩ :=
    anchor_six_arith s (fun i => Nat.card (K i))
      (fun i => (lcoset (K i) (x i) ∩ (H : Set G)).ncard) hn1 hn5 hinj hdvd hsum6 hsieve
  have hi23 : i2 ≠ i3 := by rintro rfl; omega
  have hi3n : Nat.card (K i3) = 3 := by
    have hd : 3 ∣ Nat.card (K i3) := by
      rcases hdvd i3 hi3s with h | h
      · omega
      · rw [hi3a] at h
        exact h.1
    have h1 := hn1 i3 hi3s
    have h2 := hn5 i3 hi3s
    obtain ⟨c, hc⟩ := hd
    omega
  obtain ⟨z3, hz3⟩ : (lcoset (K i3) (x i3) ∩ (H : Set G)).Nonempty := by
    rw [← Set.ncard_pos]; omega
  have htrace3 : lcoset (K i3) (x i3) ∩ (H : Set G)
      = (fun k : G => z3 * k) '' ((K i3 ⊓ H : Subgroup G) : Set G) := trace_eq_image' hz3
  have hPcard : Nat.card (K i3 ⊓ H : Subgroup G) = 3 := by
    have h1 : ((K i3 ⊓ H : Subgroup G) : Set G).ncard
        = (lcoset (K i3) (x i3) ∩ (H : Set G)).ncard := by
      rw [htrace3, Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
    have h2 : Nat.card (K i3 ⊓ H : Subgroup G)
        = ((K i3 ⊓ H : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
    rw [h2, h1, hi3a]
  have hP3 : (lcoset (K i3) (x i3) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard = 0
      ∨ (lcoset (K i3) (x i3) ∩ (H : Set G)
          ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard = 3 := by
    have hset : lcoset (K i3) (x i3) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)
        = (fun k : G => z3 * k) '' ((K i3 ⊓ H : Subgroup G) : Set G)
          ∩ ((K i3 ⊓ H : Subgroup G) : Set G) := by rw [htrace3]
    by_cases hzP : z3 ∈ (K i3 ⊓ H : Subgroup G)
    · right
      have himg : (fun k : G => z3 * k) '' ((K i3 ⊓ H : Subgroup G) : Set G)
          = ((K i3 ⊓ H : Subgroup G) : Set G) := by
        ext y; constructor
        · rintro ⟨k, hk, rfl⟩; exact (K i3 ⊓ H).mul_mem hzP hk
        · intro hy
          exact ⟨z3⁻¹ * y, (K i3 ⊓ H).mul_mem ((K i3 ⊓ H).inv_mem hzP) hy, by group⟩
      rw [hset, himg, Set.inter_self, ← Nat.card_coe_set_eq]
      exact hPcard
    · left
      have hdisj : (fun k : G => z3 * k) '' ((K i3 ⊓ H : Subgroup G) : Set G)
          ∩ ((K i3 ⊓ H : Subgroup G) : Set G) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨⟨k, hk, rfl⟩, hy⟩
        exact hzP (by
          have : z3 = (z3 * k) * k⁻¹ := by group
          rw [this]; exact (K i3 ⊓ H).mul_mem hy ((K i3 ⊓ H).inv_mem hk))
      rw [hset, hdisj, Set.ncard_empty]
  have hPtrace2 : ∀ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard = 2 →
      (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard = 1 := by
    intro i hi hai
    obtain ⟨z, hz⟩ : (lcoset (K i) (x i) ∩ (H : Set G)).Nonempty := by
      rw [← Set.ncard_pos]; omega
    have htz : lcoset (K i) (x i) ∩ (H : Set G)
        = (fun k : G => z * k) '' ((K i ⊓ H : Subgroup G) : Set G) := trace_eq_image' hz
    have hJcard : Nat.card (K i ⊓ H : Subgroup G) = 2 := by
      have h1 : ((K i ⊓ H : Subgroup G) : Set G).ncard
          = (lcoset (K i) (x i) ∩ (H : Set G)).ncard := by
        rw [htz, Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
      have h2 : Nat.card (K i ⊓ H : Subgroup G)
          = ((K i ⊓ H : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
      rw [h2, h1, hai]
    have hplemma := order_six_lcoset_inter_eq_one H (K i3 ⊓ H) (K i ⊓ H) hH
      inf_le_right hPcard inf_le_right hJcard hz.2
    have heq : lcoset (K i ⊓ H) z = lcoset (K i) (x i) ∩ (H : Set G) := by
      rw [lcoset_eq_image', htz]
    rw [← heq]
    exact hplemma
  set Tf : ι → Finset G := fun i => (lcoset (K i) (x i) ∩ (H : Set G)).toFinset with hTf
  set Pf : Finset G := ((K i3 ⊓ H : Subgroup G) : Set G).toFinset with hPf
  set c : G → ℕ := fun y => (s.filter (fun i => y ∈ Tf i)).card with hc
  have hTfcard : ∀ i, (Tf i).card = (lcoset (K i) (x i) ∩ (H : Set G)).ncard := by
    intro i; rw [hTf, Set.ncard_eq_toFinset_card']
  have hcy : ∀ y ∈ (H : Set G), 1 ≤ c y := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := hcoverH y hy
    rw [hc]
    refine Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨(hmem_s i).mpr hi, ?_⟩⟩
    rw [hTf, Set.mem_toFinset]
    exact ⟨hyi, hy⟩
  have hcardH : (((H : Set G)).toFinset).card = 6 := by
    rw [← Set.ncard_eq_toFinset_card', ← Nat.card_coe_set_eq]
    exact hH
  have hsumH : ∑ y ∈ ((H : Set G)).toFinset, c y = 6 := by
    have h1 : ∑ y ∈ ((H : Set G)).toFinset, c y
        = ∑ i ∈ s, (Tf i ∩ ((H : Set G)).toFinset).card := by
      rw [hc]; exact sum_card_filter_mem s Tf _
    have h2 : ∀ i ∈ s, (Tf i ∩ ((H : Set G)).toFinset).card
        = (lcoset (K i) (x i) ∩ (H : Set G)).ncard := by
      intro i _
      have hsub : Tf i ⊆ ((H : Set G)).toFinset := by
        rw [hTf, Set.toFinset_subset_toFinset]
        exact Set.inter_subset_right
      rw [(Finset.inter_eq_left).mpr hsub, hTfcard]
    rw [h1, Finset.sum_congr rfl h2, hsum_eq]
  have hcone : ∀ y ∈ ((H : Set G)).toFinset, c y = 1 := by
    have h1 : ∀ y ∈ ((H : Set G)).toFinset, 1 ≤ c y := fun y hy =>
      hcy y (Set.mem_toFinset.mp hy)
    have h2 : ∑ y ∈ ((H : Set G)).toFinset, c y
        = ∑ y ∈ ((H : Set G)).toFinset, (1 : ℕ) := by
      rw [hsumH]; simp [hcardH]
    exact fun y hy => ((Finset.sum_eq_sum_iff_of_le h1).mp h2.symm y hy).symm
  have hcountP : ∑ i ∈ s, (Tf i ∩ Pf).card = 3 := by
    have h1 : ∑ y ∈ Pf, c y = ∑ i ∈ s, (Tf i ∩ Pf).card := by
      rw [hc]; exact sum_card_filter_mem s Tf Pf
    have h2 : ∑ y ∈ Pf, c y = ∑ y ∈ Pf, (1 : ℕ) := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hyP : y ∈ ((K i3 ⊓ H : Subgroup G) : Set G) := by
        rw [← Set.mem_toFinset, ← hPf]; exact hy
      exact hcone y (Set.mem_toFinset.mpr
        ((inf_le_right : (K i3 ⊓ H : Subgroup G) ≤ H) hyP))
    have h3 : Pf.card = 3 := by
      have h4 : ((K i3 ⊓ H : Subgroup G) : Set G).ncard = 3 := by
        rw [← Nat.card_coe_set_eq]
        exact hPcard
      rw [hPf, ← Set.ncard_eq_toFinset_card']
      exact h4
    have h5 : ∑ y ∈ Pf, (1 : ℕ) = 3 := by simp [Finset.sum_const, h3]
    omega
  have hTP : ∀ i, (Tf i ∩ Pf).card
      = (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard := by
    intro i
    rw [hTf, hPf, ← Set.toFinset_inter, Set.ncard_eq_toFinset_card']
  have hsumP : ∑ i ∈ s,
      (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard = 3 := by
    rw [← hcountP]
    exact Finset.sum_congr rfl (fun i _ => (hTP i).symm)
  have hle1 : ∀ i ∈ s.erase i3,
      (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard
        ≤ if 1 ≤ (lcoset (K i) (x i) ∩ (H : Set G)).ncard then 1 else 0 := by
    intro i hi
    have his : i ∈ s := Finset.mem_of_mem_erase hi
    have hne : i ≠ i3 := (Finset.mem_erase.mp hi).1
    have hai : (lcoset (K i) (x i) ∩ (H : Set G)).ncard ≠ 3 := by
      intro h3
      rcases hdvd i his with h | h
      · omega
      · rw [h3] at h
        have hd : 3 ∣ Nat.card (K i) := h.1
        have h1 := hn1 i his
        have h2 := hn5 i his
        obtain ⟨c, hc⟩ := hd
        have hni : Nat.card (K i) = 3 := by omega
        exact hne (hinj his hi3s (by
          show Nat.card (K i) = Nat.card (K i3)
          rw [hni, hi3n]))
    have hle3 : (lcoset (K i) (x i) ∩ (H : Set G)).ncard ≤ 3 := by
      rcases hdvd i his with h | h
      · omega
      · refine le_three_of_dvd_six h.2 ?_
        have h1 := hale i his
        have h2 := hn5 i his
        omega
    rcases Nat.lt_or_ge ((lcoset (K i) (x i) ∩ (H : Set G)).ncard) 3 with hlt | hge
    · by_cases h2 : (lcoset (K i) (x i) ∩ (H : Set G)).ncard = 2
      · have := hPtrace2 i his h2
        rw [if_pos (by omega), this]
      · have h1 : (lcoset (K i) (x i) ∩ (H : Set G)).ncard ≤ 1 := by omega
        by_cases hz : (lcoset (K i) (x i) ∩ (H : Set G)).ncard = 0
        · have hempty : lcoset (K i) (x i) ∩ (H : Set G) = ∅ := by
            rw [← Set.ncard_eq_zero]; exact hz
          rw [if_neg (by omega),
            show lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G) = ∅ from by
              rw [hempty, Set.empty_inter]]
          simp
        · have hle : (lcoset (K i) (x i) ∩ (H : Set G)
              ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard
              ≤ (lcoset (K i) (x i) ∩ (H : Set G)).ncard :=
            Set.ncard_le_ncard Set.inter_subset_left
          rw [if_pos (by omega)]
          omega
    · omega
  have hone : ∀ i ∈ s.erase i3,
      (if 1 ≤ (lcoset (K i) (x i) ∩ (H : Set G)).ncard then 1 else 0)
        ≤ (lcoset (K i) (x i) ∩ (H : Set G)).ncard := by
    intro i _
    split_ifs with h
    · omega
    · omega
  rcases hP3 with hP3z | hP3t
  · have hsumEraseP : ∑ i ∈ s.erase i3,
        (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard = 3 := by
      have := Finset.sum_erase_add s (fun i =>
        (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard) hi3s
      omega
    have hsumEraseA : ∑ i ∈ s.erase i3,
        (lcoset (K i) (x i) ∩ (H : Set G)).ncard = 3 := by
      have := Finset.sum_erase_add s
        (fun i => (lcoset (K i) (x i) ∩ (H : Set G)).ncard) hi3s
      omega
    have hifsum : ∑ i ∈ s.erase i3,
        (if 1 ≤ (lcoset (K i) (x i) ∩ (H : Set G)).ncard then 1 else 0) = 3 := by
      have h1 := Finset.sum_le_sum hle1
      have h2 := Finset.sum_le_sum hone
      omega
    have hcontra : (if 1 ≤ (lcoset (K i2) (x i2) ∩ (H : Set G)).ncard then 1 else 0)
        = (lcoset (K i2) (x i2) ∩ (H : Set G)).ncard :=
      (Finset.sum_eq_sum_iff_of_le hone).mp (by rw [hifsum, hsumEraseA])
        i2 (Finset.mem_erase.mpr ⟨hi23, hi2s⟩)
    rw [hi2a] at hcontra
    norm_num at hcontra
  · have hpos : 0 < ∑ i ∈ s.erase i3,
        (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard := by
      refine Finset.sum_pos' (fun i _ => by positivity)
        ⟨i2, Finset.mem_erase.mpr ⟨hi23, hi2s⟩, ?_⟩
      rw [hPtrace2 i2 hi2s hi2a]; norm_num
    have hsumEraseP : ∑ i ∈ s.erase i3,
        (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard
        = 3 - 3 := by
      have := Finset.sum_erase_add s (fun i =>
        (lcoset (K i) (x i) ∩ (H : Set G) ∩ ((K i3 ⊓ H : Subgroup G) : Set G)).ncard) hi3s
      omega
    omega

end HSC.CertPP
