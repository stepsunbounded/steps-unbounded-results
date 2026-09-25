import Mathlib

open scoped BigOperators

namespace HSC.CertPP

variable {G : Type*} [Group G] [Fintype G]

/-- The left coset `xK` of the subgroup `K` through `x`, as a set of group elements. -/
def lcoset (K : Subgroup G) (x : G) : Set G := {g | x⁻¹ * g ∈ K}

theorem mem_lcoset {K : Subgroup G} {x g : G} :
    g ∈ lcoset K x ↔ x⁻¹ * g ∈ K := Iff.rfl

theorem lcoset_eq_of_mem {K : Subgroup G} {x g : G} (h : g ∈ lcoset K x) :
    lcoset K x = lcoset K g := by
  have h' : x⁻¹ * g ∈ K := h
  ext y
  simp only [mem_lcoset]
  constructor
  · intro hy
    have hy' : g⁻¹ * y = (x⁻¹ * g)⁻¹ * (x⁻¹ * y) := by group
    rw [hy']; exact K.mul_mem (K.inv_mem h') hy
  · intro hy
    have hy' : x⁻¹ * y = (x⁻¹ * g) * (g⁻¹ * y) := by group
    rw [hy']; exact K.mul_mem h' hy

theorem ncard_lcoset (K : Subgroup G) (x : G) : (lcoset K x).ncard = Nat.card K := by
  have hset : lcoset K x = (fun k : G => x * k) '' (K : Set G) := by
    ext g
    constructor
    · intro hg
      exact ⟨x⁻¹ * g, hg, by group⟩
    · rintro ⟨k, hk, rfl⟩
      simpa [mem_lcoset] using hk
  rw [hset, Set.ncard_image_of_injective _ (fun a b hab => by simpa using hab)]
  exact (Nat.card_coe_set_eq (K : Set G)).symm

theorem ncard_lcoset_inter_le (K H : Subgroup G) (x : G) :
    (lcoset K x ∩ (H : Set G)).ncard ≤ Nat.card (K ⊓ H : Subgroup G) := by
  classical
  rcases Set.eq_empty_or_nonempty (lcoset K x ∩ (H : Set G)) with h | ⟨z, hz⟩
  · rw [h]
    simp
  · refine le_trans (Set.ncard_le_ncard_of_injOn (s := lcoset K x ∩ (H : Set G))
      (t := ((K ⊓ H : Subgroup G) : Set G)) (fun w : G => z⁻¹ * w) ?_ ?_) ?_
    · rintro w ⟨hw1, hw2⟩
      have hw1' : x⁻¹ * w ∈ K := hw1
      have hz1 : x⁻¹ * z ∈ K := hz.1
      have hz2 : z ∈ H := hz.2
      have hK : z⁻¹ * w ∈ K := by
        have hzw : z⁻¹ * w = (x⁻¹ * z)⁻¹ * (x⁻¹ * w) := by group
        rw [hzw]
        exact K.mul_mem (K.inv_mem hz1) hw1'
      have hH' : z⁻¹ * w ∈ H := H.mul_mem (H.inv_mem hz2) hw2
      exact ⟨hK, hH'⟩
    · intro a _ b _ hab
      exact mul_left_cancel hab
    · exact (Nat.card_coe_set_eq ((K ⊓ H : Subgroup G) : Set G)).symm.le

theorem gcd_four_le (m : ℕ) (h1 : 1 ≤ m) (h3 : m ≤ 3) :
    Nat.gcd m 4 ≤ if m = 2 then 2 else 1 := by
  have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm with h | h | h <;> subst h <;> decide

theorem exists_size_three {ι : Type*} [Fintype ι] (s : Finset ι) (n a : ι → ℕ)
    (hn1 : ∀ i ∈ s, 1 ≤ n i) (hn3 : ∀ i ∈ s, n i ≤ 3)
    (hinj : Set.InjOn n (↑s : Set ι))
    (ha : ∀ i ∈ s, a i ≤ if n i = 2 then 2 else 1)
    (hsum : 4 ≤ ∑ i ∈ s, a i) : ∃ i ∈ s, n i = 3 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hn12 : ∀ i ∈ s, n i = 1 ∨ n i = 2 := by
    intro i hi
    have h1 := hn1 i hi
    have h3 := hn3 i hi
    have hne := hcon i hi
    omega
  have ht : ∀ i ∈ s, (if n i = 2 then 2 else 1) = n i := by
    intro i hi
    rcases hn12 i hi with h | h
    · rw [if_neg (by omega), h]
    · rw [if_pos h, h]
  have himg : s.image n ⊆ ({1, 2} : Finset ℕ) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨i, hi, rfl⟩
    rcases hn12 i hi with h | h <;> simp [h]
  have hsum3 : ∑ i ∈ s, n i ≤ 3 := by
    rw [(Finset.sum_image (f := fun m : ℕ => m) hinj).symm]
    calc ∑ x ∈ s.image n, id x ≤ ∑ x ∈ ({1, 2} : Finset ℕ), id x :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (by intro i _ _; simp)
      _ = 3 := by decide
  have hle : ∑ i ∈ s, a i ≤ ∑ i ∈ s, (if n i = 2 then 2 else 1) := Finset.sum_le_sum ha
  have heq : ∑ i ∈ s, (if n i = 2 then 2 else 1) = ∑ i ∈ s, n i := Finset.sum_congr rfl ht
  omega

theorem ncard_iUnion_finset_le {α β : Type*} (s : Finset β) (f : β → Set α) :
    (⋃ i ∈ s, f i).ncard ≤ ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hset : (⋃ i ∈ insert a s, f i) = f a ∪ ⋃ i ∈ s, f i := by
        ext y
        constructor
        · intro hy
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
          obtain ⟨hmem, hyi⟩ := Set.mem_iUnion.mp hi
          rcases Finset.mem_insert.mp hmem with rfl | hmem'
          · exact Or.inl hyi
          · exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hmem', hyi⟩⟩)
        · intro hy
          rcases hy with hy | hy
          · exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨Finset.mem_insert_self a s, hy⟩⟩
          · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
            obtain ⟨hmem, hyi⟩ := Set.mem_iUnion.mp hi
            exact Set.mem_iUnion.mpr
              ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hmem, hyi⟩⟩
      rw [hset, Finset.sum_insert ha]
      exact le_trans (Set.ncard_union_le _ _) (add_le_add le_rfl ih)

theorem certPP_anchor_four (H : Subgroup G) (hH : Nat.card H = 4)
    {ι : Type*} [Fintype ι] (K : ι → Subgroup G) (x : ι → G) (i₀ : ι)
    (hanchor : lcoset (K i₀) (x i₀) = (H : Set G))
    (hsize : ∀ i, Nat.card (K i) ≤ 4)
    (hdist : ∀ i j, i ≠ j → Nat.card (K i) ≠ Nat.card (K j))
    (hcover : ∀ g : G, Nat.card {i : ι // g ∈ lcoset (K i) (x i)} ≠ 1) :
    False := by
  classical
  set s : Finset ι := Finset.univ.erase i₀ with hs
  have hmem_s : ∀ i, i ∈ s ↔ i ≠ i₀ := by
    intro i; rw [hs]; simp
  have hsize_eq : ∀ i, Nat.card (K i) = (lcoset (K i) (x i)).ncard :=
    fun i => (ncard_lcoset (K i) (x i)).symm
  have hn0 : Nat.card (K i₀) = 4 := by
    have h1 : ((H : Set G)).ncard = 4 :=
      ((Nat.card_coe_set_eq (H : Set G)).symm).trans hH
    have h2 : ((H : Set G)).ncard = Nat.card (K i₀) := by
      rw [← ncard_lcoset (K i₀) (x i₀), hanchor]
    omega
  have hle3 : ∀ i ∈ s, Nat.card (K i) ≤ 3 := by
    intro i hi
    have hne : i ≠ i₀ := (hmem_s i).mp hi
    have h4 : Nat.card (K i) ≠ 4 := fun h => hdist i i₀ hne (h.trans hn0.symm)
    have := hsize i
    omega
  have hge1 : ∀ i ∈ s, 1 ≤ Nat.card (K i) := by
    intro i _
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨1, (K i).one_mem⟩⟩
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
      push_neg at hc
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
  have h4_le : 4 ≤ ∑ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard := by
    have hHn : ((H : Set G)).ncard = 4 :=
      ((Nat.card_coe_set_eq (H : Set G)).symm).trans hH
    have h1 : ((H : Set G)).ncard
        ≤ (⋃ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G))).ncard := Set.ncard_le_ncard hHsub
    have h2 := ncard_iUnion_finset_le s (fun i => lcoset (K i) (x i) ∩ (H : Set G))
    omega
  have ha_le : ∀ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard
      ≤ if Nat.card (K i) = 2 then 2 else 1 := by
    intro i hi
    have h1 := ncard_lcoset_inter_le (K i) H (x i)
    have h2 : Nat.card (K i ⊓ H : Subgroup G) ∣ Nat.card (K i) :=
      Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card (K i ⊓ H : Subgroup G) ∣ 4 := by
      rw [← hH]; exact Subgroup.card_dvd_of_le inf_le_right
    have h4 : Nat.card (K i ⊓ H : Subgroup G) ≤ Nat.gcd (Nat.card (K i)) 4 :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_left 4 (by have := hge1 i hi; omega))
        (Nat.dvd_gcd h2 h3)
    have h5 := gcd_four_le (Nat.card (K i)) (hge1 i hi) (hle3 i hi)
    omega
  have hs_card_le : s.card ≤ 3 := by
    have himg : s.image (fun i => Nat.card (K i)) ⊆ ({1, 2, 3} : Finset ℕ) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨i, hi, rfl⟩
      have h1 := hge1 i hi
      have h2 := hle3 i hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc s.card = (s.image fun i => Nat.card (K i)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ 3 := by simpa using Finset.card_le_card himg
  have hs_two_le : (s.filter (fun i => Nat.card (K i) = 2)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [Finset.mem_filter] at hi hj
    exact hinj hi.1 hj.1 (by simp only [hi.2, hj.2])
  have hsumT : ∑ i ∈ s, (if Nat.card (K i) = 2 then 2 else 1)
      = s.card + (s.filter (fun i => Nat.card (K i) = 2)).card := by
    have hsplit : ∀ i, (if Nat.card (K i) = 2 then (2 : ℕ) else 1)
        = 1 + (if Nat.card (K i) = 2 then 1 else 0) := by
      intro i; split_ifs <;> omega
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_const,
      ← Finset.card_filter (fun i => Nat.card (K i) = 2) s]
    simp
  have hsumT_le : ∑ i ∈ s, (if Nat.card (K i) = 2 then 2 else 1) ≤ 4 := by omega
  have hsumA_le : ∑ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard
      ≤ ∑ i ∈ s, (if Nat.card (K i) = 2 then 2 else 1) := Finset.sum_le_sum ha_le
  have hsumA : ∑ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard = 4 := by omega
  have hterm : ∀ i ∈ s, (lcoset (K i) (x i) ∩ (H : Set G)).ncard
      = (if Nat.card (K i) = 2 then 2 else 1) := by
    by_contra hc
    push_neg at hc
    obtain ⟨i, hi, hne⟩ := hc
    have hlt : (lcoset (K i) (x i) ∩ (H : Set G)).ncard
        < (if Nat.card (K i) = 2 then 2 else 1) := lt_of_le_of_ne (ha_le i hi) hne
    have := Finset.sum_lt_sum ha_le ⟨i, hi, hlt⟩
    omega
  obtain ⟨i₃, hi₃s, hi₃n⟩ := exists_size_three s (fun i => Nat.card (K i))
    (fun i => (lcoset (K i) (x i) ∩ (H : Set G)).ncard) hge1 hle3 hinj ha_le h4_le
  have htrace3 : (lcoset (K i₃) (x i₃) ∩ (H : Set G)).ncard = 1 := by
    have := hterm i₃ hi₃s
    rw [hi₃n] at this
    simpa using this
  have hcard3 : (lcoset (K i₃) (x i₃)).ncard = 3 := (ncard_lcoset (K i₃) (x i₃)).trans hi₃n
  obtain ⟨z, hz3, hzH⟩ : ∃ z ∈ lcoset (K i₃) (x i₃), z ∉ (H : Set G) := by
    by_contra hc
    push_neg at hc
    have hinter : lcoset (K i₃) (x i₃) ∩ (H : Set G) = lcoset (K i₃) (x i₃) :=
      Set.inter_eq_left.mpr hc
    rw [hinter, hcard3] at htrace3
    omega
  have huniq : ∀ i : ι, z ∈ lcoset (K i) (x i) → i = i₃ := by
    intro i hzi
    by_cases hi : i = i₀
    · subst hi
      rw [hanchor] at hzi
      exact absurd hzi hzH
    · have his : i ∈ s := (hmem_s i).mpr hi
      rcases eq_or_ne (Nat.card (K i)) 3 with h3 | h3
      · exact hinj his hi₃s (h3.trans hi₃n.symm)
      · have hni : Nat.card (K i) = 1 ∨ Nat.card (K i) = 2 := by
          have := hle3 i his; have := hge1 i his; omega
        have hai : (lcoset (K i) (x i) ∩ (H : Set G)).ncard = Nat.card (K i) := by
          have ht := hterm i his
          rcases hni with h | h
          · rw [ht, if_neg (by omega), h]
          · rw [ht, if_pos h, h]
        have hsub : lcoset (K i) (x i) ⊆ (H : Set G) := by
          have h1 : lcoset (K i) (x i) ∩ (H : Set G) ⊆ lcoset (K i) (x i) :=
            Set.inter_subset_left
          have h2 : (lcoset (K i) (x i)).ncard
              ≤ (lcoset (K i) (x i) ∩ (H : Set G)).ncard := by
            rw [ncard_lcoset, hai]
          exact Set.inter_eq_left.mp (Set.eq_of_subset_of_ncard_le h1 h2)
        exact absurd (hsub hzi) hzH
  have hsingle : Nat.card {i : ι // z ∈ lcoset (K i) (x i)} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (by rw [huniq a a.2, huniq b b.2])⟩, ⟨⟨i₃, hz3⟩⟩⟩
  exact hcover z hsingle

end HSC.CertPP
