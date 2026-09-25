import StepsUnboundedResults.HSC.CertPP12Core

open scoped Classical
open Finset

namespace HSC
namespace CertPP12
namespace Util

private lemma biUnion_subset_union_erase_erase {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {s : Finset ι} {T : ι → Finset α} {i j : ι} :
    s.biUnion T ⊆ (T i ∪ T j) ∪ ((s.erase i).erase j).biUnion T := by
  intro q hq
  obtain ⟨k, hk, hkq⟩ := Finset.mem_biUnion.mp hq
  by_cases hki : k = i
  · rw [hki] at hkq
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hkq)))
  · by_cases hkj : k = j
    · rw [hkj] at hkq
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hkq)))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩, hkq⟩))

private lemma biUnion_subset_union_erase_four {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {s : Finset ι} {T : ι → Finset α} {a b c d : ι} :
    s.biUnion T ⊆ (T a ∪ T b ∪ T c ∪ T d) ∪
      ((((s.erase a).erase b).erase c).erase d).biUnion T := by
  intro q hq
  obtain ⟨k, hk, hkq⟩ := Finset.mem_biUnion.mp hq
  by_cases hka : k = a
  · rw [hka] at hkq
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hkq)))))))
  · by_cases hkb : k = b
    · rw [hkb] at hkq
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hkq)))))))
    · by_cases hkc : k = c
      · rw [hkc] at hkq
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr hkq)))))
      · by_cases hkd : k = d
        · rw [hkd] at hkq
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hkq)))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
            ⟨k, Finset.mem_erase.mpr ⟨hkd, Finset.mem_erase.mpr ⟨hkc, Finset.mem_erase.mpr
              ⟨hkb, Finset.mem_erase.mpr ⟨hka, hk⟩⟩⟩⟩, hkq⟩))

private lemma sum_erase_erase_add_of_mem {ι : Type*} [DecidableEq ι] {s : Finset ι} (f : ι → ℕ)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    f i + f j + ∑ k ∈ (s.erase i).erase j, f k = ∑ k ∈ s, f k := by
  have h1 := Finset.add_sum_erase s f hi
  have h2 := Finset.add_sum_erase (s.erase i) f (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)
  omega

private lemma sum_erase_four_add_of_mem {ι : Type*} [DecidableEq ι] {s : Finset ι} (f : ι → ℕ)
    {a b c d : ι} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    f a + f b + f c + f d + ∑ k ∈ ((((s.erase a).erase b).erase c).erase d), f k =
      ∑ k ∈ s, f k := by
  have h1 := Finset.add_sum_erase s f ha
  have h2 := Finset.add_sum_erase (s.erase a) f (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
  have h3 := Finset.add_sum_erase ((s.erase a).erase b) f
    (Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, hc⟩⟩)
  have h4 := Finset.add_sum_erase (((s.erase a).erase b).erase c) f
    (Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_erase.mpr ⟨hbd.symm,
      Finset.mem_erase.mpr ⟨had.symm, hd⟩⟩⟩)
  omega

private lemma card_union_four_le_pair {α : Type*} [DecidableEq α] (A B C D : Finset α) :
    (A ∪ B ∪ C ∪ D).card ≤ (A ∪ B).card + (C ∪ D).card := by
  have h := Finset.card_union_le (A ∪ B) (C ∪ D)
  simpa only [Finset.union_assoc] using h

theorem card_le_sum_card_of_subset_biUnion {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : ι → Finset α) (H : Finset α)
    (h : ∀ p ∈ H, ∃ i ∈ s, p ∈ T i) : H.card ≤ ∑ i ∈ s, (T i).card := by
  have hsub : H ⊆ s.biUnion T := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := h p hp
    exact Finset.mem_biUnion.mpr ⟨i, hi, hip⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le

theorem exists_ne_of_two_le_card_filter {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    {T : ι → Finset α} {i : ι} {p : α} (hp : p ∈ T i)
    (h2 : 2 ≤ (Finset.univ.filter (fun j => p ∈ T j)).card) : ∃ j, j ≠ i ∧ p ∈ T j := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hsub : Finset.univ.filter (fun j => p ∈ T j) ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_singleton]
    by_contra hji
    exact hcon j hji hj
  have hle : (Finset.univ.filter (fun j => p ∈ T j)).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hmem : i ∈ Finset.univ.filter (fun j => p ∈ T j) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  have hge : 1 ≤ (Finset.univ.filter (fun j => p ∈ T j)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

theorem disjoint_of_sum_card_eq' {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : ι → Finset α) (H : Finset α)
    (hsub : ∀ i ∈ s, T i ⊆ H) (hcover : ∀ p ∈ H, ∃ i ∈ s, p ∈ T i)
    (hsum : ∑ i ∈ s, (T i).card = H.card) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) : Disjoint (T i) (T j) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hpi, hpj⟩ := Finset.mem_inter.mp hp
  have hHsub : H ⊆ s.biUnion T := by
    intro q hq
    obtain ⟨k, hk, hkq⟩ := hcover q hq
    exact Finset.mem_biUnion.mpr ⟨k, hk, hkq⟩
  have hTsub : s.biUnion T ⊆ H := Finset.biUnion_subset.mpr hsub
  have hcard_eq : (s.biUnion T).card = H.card :=
    le_antisymm (Finset.card_le_card hTsub) (Finset.card_le_card hHsub)
  have hb2 : (s.biUnion T).card ≤
      ((T i ∪ T j) ∪ ((s.erase i).erase j).biUnion T).card :=
    Finset.card_le_card biUnion_subset_union_erase_erase
  have hb3 : ((T i ∪ T j) ∪ ((s.erase i).erase j).biUnion T).card ≤
      (T i ∪ T j).card + ∑ k ∈ (s.erase i).erase j, (T k).card :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left Finset.card_biUnion_le _)
  have hAi : 1 ≤ (T i).card := Finset.card_pos.mpr ⟨p, hpi⟩
  have hBj : 1 ≤ (T j).card := Finset.card_pos.mpr ⟨p, hpj⟩
  have hI : 1 ≤ (T i ∩ T j).card := Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpi, hpj⟩⟩
  have hunion : (T i ∪ T j).card = (T i).card + (T j).card - (T i ∩ T j).card :=
    Finset.card_union _ _
  have hsum' : (T i).card + (T j).card + ∑ k ∈ (s.erase i).erase j, (T k).card = H.card := by
    rw [← hsum]
    exact sum_erase_erase_add_of_mem (fun k => (T k).card) hi hj hij
  omega

theorem no_two_collisions' {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : ι → Finset α) (H : Finset α) (hH : H.card = 12)
    (hcover : ∀ p ∈ H, ∃ i ∈ s, p ∈ T i)
    (hsum : ∑ i ∈ s, (T i).card = 13)
    {a b c d : ι} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h3 : (T a).card = 3) (h4 : (T b).card = 4) (h1 : (T c).card = 1) (h2 : (T d).card = 2)
    (hne1 : (T a ∩ T b).Nonempty) (hne2 : (T c ∩ T d).Nonempty) : False := by
  have hcover' : H ⊆ s.biUnion T := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := hcover p hp
    exact Finset.mem_biUnion.mpr ⟨i, hi, hip⟩
  have hb1 : H.card ≤ (s.biUnion T).card := Finset.card_le_card hcover'
  have hb2 : (s.biUnion T).card ≤
      (T a ∪ T b ∪ T c ∪ T d).card +
        ∑ i ∈ (((s.erase a).erase b).erase c).erase d, (T i).card := by
    have hcard : (s.biUnion T).card ≤
        ((T a ∪ T b ∪ T c ∪ T d) ∪
          ((((s.erase a).erase b).erase c).erase d).biUnion T).card :=
      Finset.card_le_card biUnion_subset_union_erase_four
    exact le_trans hcard
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left Finset.card_biUnion_le _))
  have huab : (T a ∪ T b).card ≤ 6 := by
    have h := Finset.card_union (T a) (T b)
    have hp : 1 ≤ (T a ∩ T b).card := Finset.card_pos.mpr hne1
    omega
  have hucd : (T c ∪ T d).card ≤ 2 := by
    have h := Finset.card_union (T c) (T d)
    have hp : 1 ≤ (T c ∩ T d).card := Finset.card_pos.mpr hne2
    omega
  have hu : (T a ∪ T b ∪ T c ∪ T d).card ≤ 8 := by
    have h := card_union_four_le_pair (T a) (T b) (T c) (T d)
    omega
  have hsum4 : (T a).card + (T b).card + (T c).card + (T d).card +
      ∑ i ∈ (((s.erase a).erase b).erase c).erase d, (T i).card = ∑ i ∈ s, (T i).card :=
    sum_erase_four_add_of_mem (fun k => (T k).card) ha hb hc hd hab hac had hbc hbd hcd
  omega

end Util
end CertPP12
end HSC
