/-
HSC/A5Sieve.lean

The **capacity sieve** for the Herzog–Schönheim conjecture on `A₅`.

The main reduction (`max_size_mem`) says: in a family of pairwise distinct left cosets of
subgroups of `A₅` whose subgroup orders are pairwise distinct and maximal at `i₀`, if no element
of the group is covered by exactly one member of the family, then the maximal order
`Nat.card (K i₀)` must lie in `{4, 6, 10, 12}`.

The proof is finite and elementary:

* `card_mem_orderSet`: every subgroup order of `A₅` is one of `60 / n` for a subgroup index
  `n ∈ {1, 5, 6, 10, 12, 15, 20, 30, 60}` (`HSC.a5_indexSet_subset`), and the nine quotients are
  `{60, 12, 10, 6, 5, 4, 3, 2, 1} ⊆ orderSet`.
* `ncard_leftCoset_inter_le_gcd`: `xK ∩ yL` is contained in a coset of `K ⊓ L`, hence its
  cardinality divides both `Nat.card K` and `Nat.card L`, so it is at most their `gcd`.
* `max_size_mem`: every point of the largest coset `D i₀` is covered by a second coset, so
  `|D i₀| ≤ ∑_{j ≠ i₀} |D j ∩ D i₀| ≤ ∑_{j ≠ i₀} gcd (|K i₀|) (|K j|)`. The orders `|K j|`
  (`j ≠ i₀`) are pairwise distinct, all in `orderSet` and all `< |K i₀|`, so this last sum is at
  most `sieveSum (|K i₀|)`; and `sieveSum S < S` for every `S ∈ orderSet` outside `{4, 6, 10, 12}`.
-/

import StepsUnboundedResults.HSC.A5Index
import Mathlib

open scoped Classical
open Finset

namespace HSC
namespace A5Sieve

def orderSet : Finset ℕ := {1, 2, 3, 4, 5, 6, 10, 12, 60}

def sieveSum (S : ℕ) : ℕ := (orderSet.filter (fun m => m < S)).sum (fun m => Nat.gcd S m)

theorem ncard_leftCoset {G : Type*} [Group G] (x : G) (H : Subgroup G) :
    (leftCoset x H).ncard = Nat.card H := by
  have hinj : Function.Injective (fun h : H => x * (h : G)) :=
    fun a b hab => Subtype.ext (mul_left_cancel hab)
  calc (leftCoset x H).ncard = ((fun h : H => x * (h : G)) '' Set.univ).ncard := by
        rw [leftCoset_eq_image]
    _ = (Set.univ : Set H).ncard := Set.ncard_image_of_injective _ hinj
    _ = Nat.card H := Set.ncard_univ H

theorem card_mem_orderSet (K : Subgroup Alt5) : Nat.card K ∈ orderSet := by
  have hidx : K.index ∈ a5IndexSet := a5_indexSet_subset K.index (index_mem_indexSet Alt5 K)
  have hmul : Nat.card K * K.index = 60 := by rw [Subgroup.card_mul_index, nat_card_alt5]
  have hkey : ∀ m ∈ a5IndexSet,
      0 < m ∧ (∀ c ∈ Finset.range 61, c * m = 60 → c ∈ orderSet) := by
    decide
  obtain ⟨hpos, hc⟩ := hkey K.index hidx
  have hle : Nat.card K ≤ 60 := by
    calc Nat.card K ≤ Nat.card K * K.index := Nat.le_mul_of_pos_right (Nat.card K) hpos
      _ = 60 := hmul
  exact hc (Nat.card K) (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)) hmul

theorem ncard_leftCoset_inter_le_gcd (K L : Subgroup Alt5) (x y : Alt5) :
    (leftCoset x K ∩ leftCoset y L).ncard ≤ Nat.gcd (Nat.card K) (Nat.card L) := by
  classical
  by_cases hne : (leftCoset x K ∩ leftCoset y L).Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    obtain ⟨hg₀x, hg₀y⟩ := hg₀
    have hsub : leftCoset x K ∩ leftCoset y L ⊆ leftCoset g₀ (K ⊓ L) := by
      rintro g hg
      obtain ⟨hgx, hgy⟩ := hg
      rw [mem_leftCoset] at hgx hgy hg₀x hg₀y ⊢
      exact ⟨by
          have h : (x⁻¹ * g₀)⁻¹ * (x⁻¹ * g) ∈ K := K.mul_mem (K.inv_mem hg₀x) hgx
          have heq : (x⁻¹ * g₀)⁻¹ * (x⁻¹ * g) = g₀⁻¹ * g := by group
          rwa [heq] at h,
        by
          have h : (y⁻¹ * g₀)⁻¹ * (y⁻¹ * g) ∈ L := L.mul_mem (L.inv_mem hg₀y) hgy
          have heq : (y⁻¹ * g₀)⁻¹ * (y⁻¹ * g) = g₀⁻¹ * g := by group
          rwa [heq] at h⟩
    have hpos : 0 < Nat.gcd (Nat.card K) (Nat.card L) :=
      Nat.gcd_pos_of_pos_left _ (by
        haveI : Nonempty K := ⟨⟨1, K.one_mem⟩⟩
        exact Nat.card_pos)
    have hcard : (leftCoset g₀ (K ⊓ L)).ncard = Nat.card ↥(K ⊓ L) := ncard_leftCoset g₀ (K ⊓ L)
    have hgcd : Nat.card ↥(K ⊓ L) ≤ Nat.gcd (Nat.card K) (Nat.card L) :=
      Nat.le_of_dvd hpos
        (Nat.dvd_gcd (Subgroup.card_dvd_of_le inf_le_left)
          (Subgroup.card_dvd_of_le inf_le_right))
    exact le_trans (Set.ncard_le_ncard hsub) (le_trans hcard.le hgcd)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
    exact Nat.zero_le _

set_option linter.unusedVariables false in
theorem max_size_mem {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → Alt5) (K : ι → Subgroup Alt5) (i₀ : ι)
    (hcoset : ∀ i j, i ≠ j → leftCoset (c i) (K i) ≠ leftCoset (c j) (K j))
    (hsize : Function.Injective fun i => Nat.card (K i))
    (hmax : ∀ i, Nat.card (K i) ≤ Nat.card (K i₀))
    (hnopriv : ∀ g : Alt5, Nat.card {i : ι // g ∈ leftCoset (c i) (K i)} ≠ 1) :
    Nat.card (K i₀) ∈ ({4, 6, 10, 12} : Finset ℕ) := by
  classical
  set S : ℕ := Nat.card (K i₀) with hS
  let D : ι → Set Alt5 := fun i => leftCoset (c i) (K i)
  have hncard : ∀ i, (D i).ncard = Nat.card (K i) := fun i => ncard_leftCoset (c i) (K i)
  have hDi₀ : (D i₀).ncard = S := by rw [hncard i₀, hS]
  have hcover : ∀ g ∈ D i₀, ∃ j : ι, j ≠ i₀ ∧ g ∈ D j := by
    intro g hg
    have hne : Fintype.card {i : ι // g ∈ D i} ≠ 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact hnopriv g
    have htwo : 1 < Fintype.card {i : ι // g ∈ D i} := by
      have hone : 0 < Fintype.card {i : ι // g ∈ D i} :=
        Fintype.card_pos_iff.mpr ⟨⟨i₀, hg⟩⟩
      omega
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card htwo (⟨i₀, hg⟩ : {i : ι // g ∈ D i})
    exact ⟨b.1, fun hbi => hb (Subtype.ext hbi), b.2⟩
  have hsubset : D i₀ ⊆ ⋃ j ∈ (Finset.univ.erase i₀ : Finset ι), (D j ∩ D i₀) := by
    intro g hg
    obtain ⟨j, hj, hgj⟩ := hcover g hg
    exact Set.mem_biUnion (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) ⟨hgj, hg⟩
  have h1 : S ≤ (⋃ j ∈ (Finset.univ.erase i₀ : Finset ι), (D j ∩ D i₀)).ncard := by
    rw [← hDi₀]
    exact Set.ncard_le_ncard hsubset
  have h2 : (⋃ j ∈ (Finset.univ.erase i₀ : Finset ι), (D j ∩ D i₀)).ncard
      ≤ ∑ j ∈ (Finset.univ.erase i₀ : Finset ι), (D j ∩ D i₀).ncard :=
    Finset.set_ncard_biUnion_le _ _
  have h3 : ∑ j ∈ (Finset.univ.erase i₀ : Finset ι), (D j ∩ D i₀).ncard
      ≤ ∑ j ∈ (Finset.univ.erase i₀ : Finset ι), Nat.gcd S (Nat.card (K j)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    calc (D j ∩ D i₀).ncard
        ≤ Nat.gcd (Nat.card (K j)) (Nat.card (K i₀)) :=
          ncard_leftCoset_inter_le_gcd (K j) (K i₀) (c j) (c i₀)
      _ = Nat.gcd S (Nat.card (K j)) := by rw [Nat.gcd_comm, hS]
  have h4 : ∑ j ∈ (Finset.univ.erase i₀ : Finset ι), Nat.gcd S (Nat.card (K j))
      = ∑ m ∈ (Finset.univ.erase i₀ : Finset ι).image (fun i => Nat.card (K i)),
          Nat.gcd S m :=
    (Finset.sum_image (fun a _ b _ hab => hsize hab)).symm
  have h5 : ∑ m ∈ (Finset.univ.erase i₀ : Finset ι).image (fun i => Nat.card (K i)),
        Nat.gcd S m ≤ sieveSum S := by
    rw [sieveSum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => Nat.zero_le _)
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    rw [Finset.mem_erase] at hj
    obtain ⟨hji, -⟩ := hj
    refine Finset.mem_filter.mpr ⟨card_mem_orderSet (K j), ?_⟩
    have hle : Nat.card (K j) ≤ S := by rw [hS]; exact hmax j
    have hne : Nat.card (K j) ≠ S := fun heq => hji (hsize (by rw [hS] at heq; exact heq))
    omega
  have hsix : S ≤ sieveSum S := h1.trans (h2.trans (h3.trans (h4.le.trans h5)))
  have horder : S ∈ orderSet := by rw [hS]; exact card_mem_orderSet (K i₀)
  exact (by decide : ∀ S ∈ orderSet, S ≤ sieveSum S → S ∈ ({4, 6, 10, 12} : Finset ℕ))
    S horder hsix

end A5Sieve
end HSC
