import StepsUnboundedResults.HSC.CertPPFour

open scoped BigOperators
open Finset

namespace HSC.CertPP

variable {G : Type*} [Group G] [Fintype G]

theorem trace_subset_image {K H : Subgroup G} {x z : G}
    (hz : z ∈ lcoset K x ∩ (H : Set G)) :
    lcoset K x ∩ (H : Set G) ⊆ (fun k : G => z * k) '' ((K ⊓ H : Subgroup G) : Set G) := by
  rintro g ⟨hg1, hg2⟩
  have hz1 : x⁻¹ * z ∈ K := hz.1
  have hg1' : x⁻¹ * g ∈ K := hg1
  have hz2 : z ∈ H := hz.2
  have hg2' : g ∈ H := hg2
  refine ⟨z⁻¹ * g, ⟨?_, ?_⟩, by group⟩
  · show z⁻¹ * g ∈ K
    have h : z⁻¹ * g = (x⁻¹ * z)⁻¹ * (x⁻¹ * g) := by group
    rw [h]; exact K.mul_mem (K.inv_mem hz1) hg1'
  · show z⁻¹ * g ∈ H
    exact H.mul_mem (H.inv_mem hz2) hg2'

theorem ncard_trace_dvd {K H : Subgroup G} {x : G} (hne : (lcoset K x ∩ (H : Set G)).Nonempty) :
    (lcoset K x ∩ (H : Set G)).ncard ∣ Nat.card K
    ∧ (lcoset K x ∩ (H : Set G)).ncard ∣ Nat.card H := by
  obtain ⟨z, hz⟩ := hne
  have himg : ((K ⊓ H : Subgroup G) : Set G) ⊆
      (fun k : G => z⁻¹ * k) '' (lcoset K x ∩ (H : Set G)) := by
    intro k hk
    refine ⟨z * k, ⟨?_, ?_⟩, by group⟩
    · show x⁻¹ * (z * k) ∈ K
      have h : x⁻¹ * (z * k) = (x⁻¹ * z) * k := by group
      rw [h]; exact K.mul_mem hz.1 hk.1
    · show z * k ∈ H
      exact H.mul_mem hz.2 hk.2
  have hcard : (lcoset K x ∩ (H : Set G)).ncard = Nat.card (K ⊓ H : Subgroup G) := by
    refine le_antisymm ?_ ?_
    · calc (lcoset K x ∩ (H : Set G)).ncard
          ≤ ((fun k : G => z * k) '' ((K ⊓ H : Subgroup G) : Set G)).ncard :=
            Set.ncard_le_ncard (trace_subset_image hz) (Set.toFinite _)
        _ = Nat.card (K ⊓ H : Subgroup G) := by
            rw [← Nat.card_coe_set_eq]
            exact Set.ncard_image_of_injective _
              (fun a b hab => mul_left_cancel hab)
    · calc Nat.card (K ⊓ H : Subgroup G)
          = ((K ⊓ H : Subgroup G) : Set G).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ((fun k : G => z⁻¹ * k) '' (lcoset K x ∩ (H : Set G))).ncard :=
            Set.ncard_le_ncard himg (Set.toFinite _)
        _ ≤ (lcoset K x ∩ (H : Set G)).ncard := by
            rw [Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
  constructor
  · rw [hcard]; exact Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ H : Subgroup G) ≤ K)
  · rw [hcard]; exact Subgroup.card_dvd_of_le (inf_le_right : (K ⊓ H : Subgroup G) ≤ H)

theorem ncard_lcoset_inter_le' {K L : Subgroup G} (x y : G) :
    (lcoset K x ∩ lcoset L y).ncard ≤ Nat.card (K ⊓ L : Subgroup G) := by
  classical
  rcases Set.eq_empty_or_nonempty (lcoset K x ∩ lcoset L y) with h | ⟨z, hz⟩
  · rw [h]; simp
  · have hz1 : x⁻¹ * z ∈ K := hz.1
    have hz2 : y⁻¹ * z ∈ L := hz.2
    have hsub : (lcoset K x ∩ lcoset L y) ⊆
        (fun w : G => z * w) '' ((K ⊓ L : Subgroup G) : Set G) := by
      rintro w ⟨hw1, hw2⟩
      have hw1' : x⁻¹ * w ∈ K := hw1
      have hw2' : y⁻¹ * w ∈ L := hw2
      refine ⟨z⁻¹ * w, ⟨?_, ?_⟩, by group⟩
      · show z⁻¹ * w ∈ K
        have h : z⁻¹ * w = (x⁻¹ * z)⁻¹ * (x⁻¹ * w) := by group
        rw [h]; exact K.mul_mem (K.inv_mem hz1) hw1'
      · show z⁻¹ * w ∈ L
        have h : z⁻¹ * w = (y⁻¹ * z)⁻¹ * (y⁻¹ * w) := by group
        rw [h]; exact L.mul_mem (L.inv_mem hz2) hw2'
    calc (lcoset K x ∩ lcoset L y).ncard
        ≤ ((fun w : G => z * w) '' ((K ⊓ L : Subgroup G) : Set G)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Nat.card (K ⊓ L : Subgroup G) := by
          rw [← Nat.card_coe_set_eq]; exact Set.ncard_image_le

theorem outside_sieve {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (D : ι → Set G) (H : Set G) (m : ι)
    (hcover : ∀ g : G, 2 ≤ Nat.card {i : ι // g ∈ D i})
    (hset : ∀ i ∉ s, D i = ∅) :
    (D m \ H).ncard
      ≤ ∑ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H)).ncard := by
  classical
  have hsub : (D m \ H) ⊆ ⋃ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H)) := by
    intro g hg
    have hg2 : 2 ≤ Nat.card {i : ι // g ∈ D i} := hcover g
    rw [Nat.card_eq_fintype_card] at hg2
    have hmem : ∃ a ∈ s, g ∈ D a ∧ a ≠ m := by
      by_contra hc
      push Not at hc
      have hkey : ∀ x : {i : ι // g ∈ D i}, x.1 = m := by
        rintro ⟨i, hi⟩
        by_contra him
        have his : i ∈ s := by
          by_contra hs
          rw [hset i hs] at hi
          exact hi
        exact absurd (hc i his hi) him
      have hcard : Nat.card {i : ι // g ∈ D i} ≤ 1 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b =>
          Subtype.ext ((hkey a).trans (hkey b).symm)⟩
      rw [Nat.card_eq_fintype_card] at hcard
      exact absurd hcard (by omega)
    obtain ⟨a, has, hga, ham⟩ := hmem
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
      ⟨Finset.mem_erase.mpr ⟨ham, has⟩, hg, ⟨hga, hg.2⟩⟩⟩
  calc (D m \ H).ncard
      ≤ (⋃ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H))).ncard := Set.ncard_le_ncard hsub
    _ ≤ ∑ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H)).ncard := ncard_iUnion_finset_le _ _

end HSC.CertPP
