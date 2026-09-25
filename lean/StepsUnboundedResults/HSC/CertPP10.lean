import StepsUnboundedResults.HSC.CertPP12Util
import Mathlib.Tactic

open scoped Classical
open Finset

namespace HSC
namespace CertPP10

/-! Kernel reduction for the order-10 anchor of the R004 private-point certificate.
The A₅-specific finite input fields are instantiated separately. -/

def lowerSizes : Finset ℕ := {1, 2, 3, 4, 5, 6}
def allSizes : Finset ℕ := insert 10 lowerSizes

def traceCap : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 5
  | 6 => 2
  | 10 => 10
  | _ => 0

@[simp] theorem traceCap_one : traceCap 1 = 1 := by decide
@[simp] theorem traceCap_two : traceCap 2 = 2 := by decide
@[simp] theorem traceCap_three : traceCap 3 = 1 := by decide
@[simp] theorem traceCap_four : traceCap 4 = 2 := by decide
@[simp] theorem traceCap_five : traceCap 5 = 5 := by decide
@[simp] theorem traceCap_six : traceCap 6 = 2 := by decide
@[simp] theorem traceCap_ten : traceCap 10 = 10 := by decide

theorem traceCap_le_two : ∀ m ∈ ({1, 2, 3, 4, 6} : Finset ℕ), traceCap m ≤ 2 := by decide

theorem five_mem : ∀ M ∈ lowerSizes.powerset, 10 ≤ ∑ m ∈ M, traceCap m → (5 : ℕ) ∈ M := by
  decide

theorem erase_five_le : ∀ M ∈ lowerSizes.powerset, (∑ m ∈ M.erase 5, traceCap m) ≤ 8 := by decide

theorem lowerSizes_card : lowerSizes.card = 6 := by decide

theorem sum_erase_six_le_three :
    (∑ m ∈ lowerSizes.erase 6, (if m = 2 ∨ m = 3 ∨ m = 4 then 1 else 0)) ≤ 3 := by decide

structure Anchored (ι : Type*) [Fintype ι] [DecidableEq ι] where
  anchor : ι
  sz : ι → ℕ
  point : ι → Finset (Fin 60)
  H : Finset (Fin 60)
  P : Finset (Fin 60)
  sz_anchor : sz anchor = 10
  sz_mem : ∀ i, sz i ∈ allSizes
  sz_injective : Function.Injective sz
  card_point : ∀ i, (point i).card = sz i
  point_anchor : point anchor = H
  card_H : H.card = 10
  P_sub : P ⊆ H
  card_P : P.card = 5
  cover : ∀ p : Fin 60, 2 ≤ (univ.filter fun i => p ∈ point i).card ∨ ∀ i, p ∉ point i
  trace_cap : ∀ i, (point i ∩ H).card ≤ traceCap (sz i)
  trace_two_P : ∀ i, (point i ∩ H).card = 2 → ((point i ∩ H) ∩ P).card = 1
  trace_five : ∀ i, sz i = 5 → 2 ≤ (point i ∩ H).card →
    point i ∩ H = P ∨ point i ∩ H = H \ P
  out_six_three : ∀ i j, sz i = 6 → 1 ≤ (point i ∩ H).card → sz j = 3 →
    (point j ∩ H).card = 1 → 2 ≤ ((point i \ H) ∩ (point j \ H)).card →
    point j ∩ H ⊆ point i ∩ H
  out_six_four : ∀ i j, sz i = 6 → 1 ≤ (point i ∩ H).card → sz j = 4 →
    1 ≤ (point j ∩ H).card → ((point i \ H) ∩ (point j \ H)).card ≤ 1

namespace Anchored

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def trace (S : Anchored ι) (i : ι) : Finset (Fin 60) := S.point i ∩ S.H
def out (S : Anchored ι) (i j : ι) : Finset (Fin 60) := (S.point i \ S.H) ∩ (S.point j \ S.H)
def b (S : Anchored ι) (i : ι) : ℕ := (S.point i \ S.H).card
def rest (S : Anchored ι) : Finset ι := univ.erase S.anchor
def sizeSet (S : Anchored ι) : Finset ℕ := (univ.erase S.anchor).image S.sz
noncomputable def memOfSize (S : Anchored ι) (m : ℕ) : ι :=
  @Function.invFun ι ℕ ⟨S.anchor⟩ S.sz m
noncomputable def one (S : Anchored ι) : ι := S.memOfSize 1
noncomputable def two (S : Anchored ι) : ι := S.memOfSize 2
noncomputable def three (S : Anchored ι) : ι := S.memOfSize 3
noncomputable def four (S : Anchored ι) : ι := S.memOfSize 4
noncomputable def five (S : Anchored ι) : ι := S.memOfSize 5
noncomputable def six (S : Anchored ι) : ι := S.memOfSize 6
noncomputable def comp (S : Anchored ι) : Finset (Fin 60) := S.H \ S.trace S.five

@[simp] theorem trace_def (S : Anchored ι) (i : ι) : S.trace i = S.point i ∩ S.H := rfl
@[simp] theorem out_def (S : Anchored ι) (i j : ι) :
    S.out i j = (S.point i \ S.H) ∩ (S.point j \ S.H) := rfl

theorem trace_subset (S : Anchored ι) (i : ι) : S.trace i ⊆ S.H := Finset.inter_subset_right
theorem comp_sub (S : Anchored ι) : S.comp ⊆ S.H := Finset.sdiff_subset

theorem sz_mem_lower (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) : S.sz i ∈ lowerSizes := by
  have h := S.sz_mem i
  rw [allSizes, Finset.mem_insert] at h
  rcases h with h | h
  · exact absurd (S.sz_injective (by rw [h, S.sz_anchor])) hi
  · exact h

theorem mem_sizeSet_iff (S : Anchored ι) {m : ℕ} :
    m ∈ S.sizeSet ↔ ∃ i, i ≠ S.anchor ∧ S.sz i = m := by
  rw [sizeSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hsz⟩
    exact ⟨i, (Finset.mem_erase.mp hi).1, hsz⟩
  · rintro ⟨i, hi, hsz⟩
    exact ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hsz⟩

theorem sizeSet_subset (S : Anchored ι) : S.sizeSet ⊆ lowerSizes := by
  intro m hm
  obtain ⟨i, hi, hsz⟩ := (mem_sizeSet_iff S).mp hm
  rw [← hsz]
  exact sz_mem_lower S hi

theorem rest_card_eq_sizeSet_card (S : Anchored ι) : S.rest.card = S.sizeSet.card := by
  rw [rest, sizeSet]
  exact (Finset.card_image_of_injOn (fun a _ b _ h => S.sz_injective h)).symm

theorem sz_memOfSize (S : Anchored ι) {m : ℕ} (hm : m ∈ S.sizeSet) : S.sz (S.memOfSize m) = m := by
  obtain ⟨i, _, hsz⟩ := (mem_sizeSet_iff S).mp hm
  exact @Function.invFun_eq ι ℕ ⟨S.anchor⟩ S.sz m ⟨i, hsz⟩

theorem memOfSize_ne_anchor (S : Anchored ι) {m : ℕ} (hm : m ∈ S.sizeSet) (hm10 : m ≠ 10) :
    S.memOfSize m ≠ S.anchor := by
  intro h
  have h1 : S.sz (S.memOfSize m) = 10 := by rw [h, S.sz_anchor]
  rw [sz_memOfSize S hm] at h1
  exact hm10 h1

theorem sum_rest_eq_sizeSet (S : Anchored ι) (F : ℕ → ℕ) :
    ∑ i ∈ S.rest, F (S.sz i) = ∑ m ∈ S.sizeSet, F m := by
  rw [rest, sizeSet]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

theorem sum_rest_erase_eq (S : Anchored ι) (i : ι) (F : ℕ → ℕ) :
    ∑ j ∈ S.rest.erase i, F (S.sz j) = ∑ n ∈ S.sizeSet.erase (S.sz i), F n := by
  rw [rest, sizeSet, ← Finset.image_erase S.sz_injective]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

theorem trace_cover (S : Anchored ι) {p : Fin 60} (hp : p ∈ S.H) :
    ∃ i ∈ S.rest, p ∈ S.trace i := by
  have hpa : p ∈ S.point S.anchor := by rw [S.point_anchor]; exact hp
  rcases S.cover p with h2 | hnone
  · obtain ⟨j, hj, hpj⟩ := CertPP12.Util.exists_ne_of_two_le_card_filter hpa h2
    exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, Finset.mem_inter.mpr ⟨hpj, hp⟩⟩
  · exact absurd hpa (hnone S.anchor)

theorem trace_sum_ge (S : Anchored ι) : 10 ≤ ∑ i ∈ S.rest, (S.trace i).card := by
  have h1 := CertPP12.Util.card_le_sum_card_of_subset_biUnion S.rest S.trace S.H
    (fun p hp => trace_cover S hp)
  have h2 : S.H.card = 10 := S.card_H
  omega

theorem trace_sum_le_caps (S : Anchored ι) :
    ∑ i ∈ S.rest, (S.trace i).card ≤ ∑ m ∈ S.sizeSet, traceCap m := by
  calc ∑ i ∈ S.rest, (S.trace i).card ≤ ∑ i ∈ S.rest, traceCap (S.sz i) :=
        Finset.sum_le_sum fun i _ => S.trace_cap i
    _ = ∑ m ∈ S.sizeSet, traceCap m := sum_rest_eq_sizeSet S traceCap

theorem sizeSum_ge (S : Anchored ι) : 10 ≤ ∑ m ∈ S.sizeSet, traceCap m :=
  le_trans (trace_sum_ge S) (trace_sum_le_caps S)

theorem five_mem_sizeSet (S : Anchored ι) : (5 : ℕ) ∈ S.sizeSet :=
  five_mem S.sizeSet (by rw [Finset.mem_powerset]; exact sizeSet_subset S) (sizeSum_ge S)

theorem sz_five (S : Anchored ι) : S.sz S.five = 5 := sz_memOfSize S (five_mem_sizeSet S)

theorem five_mem_rest (S : Anchored ι) : S.five ∈ S.rest :=
  Finset.mem_erase.mpr ⟨memOfSize_ne_anchor S (five_mem_sizeSet S) (by norm_num), Finset.mem_univ _⟩

theorem trace_five_card_ge_two (S : Anchored ι) : 2 ≤ (S.trace S.five).card := by
  by_contra hcon
  push Not at hcon
  have hsplit := Finset.add_sum_erase S.rest (fun i => (S.trace i).card) (five_mem_rest S)
  have h1 : ∑ i ∈ S.rest.erase S.five, (S.trace i).card ≤ ∑ m ∈ S.sizeSet.erase 5, traceCap m := by
    calc ∑ i ∈ S.rest.erase S.five, (S.trace i).card
        ≤ ∑ i ∈ S.rest.erase S.five, traceCap (S.sz i) := Finset.sum_le_sum fun i _ => S.trace_cap i
      _ = ∑ m ∈ S.sizeSet.erase 5, traceCap m := by
          rw [sum_rest_erase_eq S S.five traceCap, sz_five S]
  have h2 : (∑ m ∈ S.sizeSet.erase 5, traceCap m) ≤ 8 :=
    erase_five_le S.sizeSet (by rw [Finset.mem_powerset]; exact sizeSet_subset S)
  have h3 := trace_sum_ge S
  omega

theorem trace_five_eq (S : Anchored ι) : S.trace S.five = S.P ∨ S.trace S.five = S.H \ S.P :=
  S.trace_five S.five (sz_five S) (trace_five_card_ge_two S)

theorem card_trace_five (S : Anchored ι) : (S.trace S.five).card = 5 := by
  rcases trace_five_eq S with h | h
  · rw [h]; exact S.card_P
  · rw [h, Finset.card_sdiff, Finset.inter_eq_left.mpr S.P_sub, S.card_H, S.card_P]

theorem card_comp (S : Anchored ι) : (S.comp).card = 5 := by
  rw [comp, Finset.card_sdiff, Finset.inter_eq_left.mpr (trace_subset S S.five), S.card_H,
    card_trace_five S]

theorem comp_cover (S : Anchored ι) {p : Fin 60} (hp : p ∈ S.comp) :
    ∃ i ∈ S.rest.erase S.five, p ∈ S.trace i := by
  have hpH : p ∈ S.H := comp_sub S hp
  obtain ⟨i, hi, hpi⟩ := trace_cover S hpH
  have hine : i ≠ S.five := by
    rintro rfl
    exact (Finset.mem_sdiff.mp hp).2 hpi
  exact ⟨i, Finset.mem_erase.mpr ⟨hine, hi⟩, hpi⟩

theorem trace_inter_comp_le_one (S : Anchored ι) {i : ι} (hi : i ∈ S.rest.erase S.five) :
    (S.trace i ∩ S.comp).card ≤ 1 := by
  have hia : i ≠ S.anchor := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hmem : S.sz i ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
    have h := sz_mem_lower S hia
    simp only [lowerSizes, Finset.mem_insert, Finset.mem_singleton] at h
    have hne5 : S.sz i ≠ 5 := by
      intro h5
      exact (Finset.mem_erase.mp hi).1 (S.sz_injective (by rw [h5, sz_five S]))
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcap : (S.trace i).card ≤ 2 := le_trans (S.trace_cap i) (traceCap_le_two (S.sz i) hmem)
  have hsub : S.trace i ⊆ S.H := trace_subset S i
  have hcut : ∀ T : Finset (Fin 60), S.trace i ∩ (S.H \ T) = S.trace i \ T := by
    intro T
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxA, _, hxT⟩; exact ⟨hxA, hxT⟩
    · rintro ⟨hxA, hxT⟩; exact ⟨hxA, hsub hxA, hxT⟩
  rcases lt_or_eq_of_le hcap with hlt | heq
  · calc (S.trace i ∩ S.comp).card ≤ (S.trace i).card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ 1 := by omega
  · have hP : (S.trace i ∩ S.P).card = 1 := S.trace_two_P i heq
    have hHP : (S.trace i ∩ (S.H \ S.P)).card = (S.trace i).card - (S.trace i ∩ S.P).card := by
      rw [hcut S.P, Finset.card_sdiff, Finset.inter_comm S.P (S.trace i)]
    rcases trace_five_eq S with hfive | hfive
    · rw [comp, hfive, hcut S.P, Finset.card_sdiff, Finset.inter_comm S.P (S.trace i), heq, hP]
    · rw [comp, hfive, hcut (S.H \ S.P), Finset.card_sdiff,
        Finset.inter_comm (S.H \ S.P) (S.trace i), hHP, heq, hP]

theorem forced_profile (S : Anchored ι) :
    S.sizeSet = lowerSizes ∧ (S.trace S.five).card = 5 ∧
      (∀ i ∈ S.rest.erase S.five, (S.trace i ∩ S.comp).card = 1) ∧
      (∀ i ∈ S.rest.erase S.five, ∀ j ∈ S.rest.erase S.five, i ≠ j →
        S.trace i ∩ S.comp ≠ S.trace j ∩ S.comp) := by
  have hle1 : ∀ i ∈ S.rest.erase S.five, (S.trace i ∩ S.comp).card ≤ 1 :=
    fun i hi => trace_inter_comp_le_one S hi
  have hge5 : 5 ≤ ∑ i ∈ S.rest.erase S.five, (S.trace i ∩ S.comp).card := by
    have h := CertPP12.Util.card_le_sum_card_of_subset_biUnion (S.rest.erase S.five)
      (fun i => S.trace i ∩ S.comp) S.comp
      (fun p hp => let ⟨i, hi, hpi⟩ := comp_cover S hp
                   ⟨i, hi, Finset.mem_inter.mpr ⟨hpi, hp⟩⟩)
    rwa [card_comp S] at h
  have hsum_le : ∑ i ∈ S.rest.erase S.five, (S.trace i ∩ S.comp).card
      ≤ (S.rest.erase S.five).card := by
    calc ∑ i ∈ S.rest.erase S.five, (S.trace i ∩ S.comp).card
        ≤ ∑ _i ∈ S.rest.erase S.five, 1 := Finset.sum_le_sum hle1
      _ = (S.rest.erase S.five).card := by simp
  have hrest_le : S.rest.card ≤ 6 := by
    rw [rest_card_eq_sizeSet_card S]
    calc S.sizeSet.card ≤ lowerSizes.card := Finset.card_le_card (sizeSet_subset S)
      _ = 6 := lowerSizes_card
  have hs5 : (S.rest.erase S.five).card = 5 := by
    have h1 : (S.rest.erase S.five).card + 1 = S.rest.card := Finset.card_erase_add_one (five_mem_rest S)
    omega
  have hsum_eq : ∑ i ∈ S.rest.erase S.five, (S.trace i ∩ S.comp).card = 5 := by omega
  have hterm : ∀ i ∈ S.rest.erase S.five, (S.trace i ∩ S.comp).card = 1 := by
    intro i hi
    by_contra hne
    have hlt : (S.trace i ∩ S.comp).card < 1 := lt_of_le_of_ne (hle1 i hi) hne
    have hlt' := Finset.sum_lt_sum hle1 ⟨i, hi, hlt⟩
    have hones : ∑ _x ∈ S.rest.erase S.five, (1 : ℕ) = 5 := by
      rw [Finset.sum_const, hs5]; simp
    omega
  have hdisj : ∀ i ∈ S.rest.erase S.five, ∀ j ∈ S.rest.erase S.five, i ≠ j →
      S.trace i ∩ S.comp ≠ S.trace j ∩ S.comp := by
    intro i hi j hj hij heq
    have hcover' : ∀ p ∈ S.comp, ∃ k ∈ (S.rest.erase S.five).erase i, p ∈ S.trace k ∩ S.comp := by
      intro p hp
      obtain ⟨k, hk, hkp⟩ := comp_cover S hp
      by_cases hki : k = i
      · subst hki
        have hpj : p ∈ S.trace j ∩ S.comp := by rw [← heq]; exact Finset.mem_inter.mpr ⟨hkp, hp⟩
        exact ⟨j, Finset.mem_erase.mpr ⟨hij.symm, hj⟩, hpj⟩
      · exact ⟨k, Finset.mem_erase.mpr ⟨hki, hk⟩, Finset.mem_inter.mpr ⟨hkp, hp⟩⟩
    have h1 := CertPP12.Util.card_le_sum_card_of_subset_biUnion ((S.rest.erase S.five).erase i)
      (fun k => S.trace k ∩ S.comp) S.comp hcover'
    have h2 : ∑ k ∈ (S.rest.erase S.five).erase i, (S.trace k ∩ S.comp).card = 4 := by
      have hcongr : ∀ k ∈ (S.rest.erase S.five).erase i, (S.trace k ∩ S.comp).card = 1 :=
        fun k hk => hterm k (Finset.mem_erase.mp hk).2
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_erase_of_mem hi, hs5]
      norm_num
    rw [card_comp S, h2] at h1
    omega
  have hsizeSet_eq : S.sizeSet = lowerSizes := by
    apply Finset.eq_of_subset_of_card_le (sizeSet_subset S)
    rw [lowerSizes_card]
    have h1 : (S.rest.erase S.five).card + 1 = S.rest.card := Finset.card_erase_add_one (five_mem_rest S)
    have h2 : S.rest.card = S.sizeSet.card := rest_card_eq_sizeSet_card S
    omega
  exact ⟨hsizeSet_eq, card_trace_five S, hterm, hdisj⟩

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
      · obtain ⟨j, hji, hpj⟩ := CertPP12.Util.exists_ne_of_two_le_card_filter hpi h2
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

theorem no_anchored_system (S : Anchored ι) : False := by
  obtain ⟨hsizeSet_eq, hcard5, hterm, hdisj⟩ := forced_profile S
  have hsix_mem : (6 : ℕ) ∈ S.sizeSet := by rw [hsizeSet_eq]; decide
  have hsz_six : S.sz S.six = 6 := sz_memOfSize S hsix_mem
  have hsix_ne : S.six ≠ S.anchor := memOfSize_ne_anchor S hsix_mem (by norm_num)
  have hsix_rest : S.six ∈ S.rest := Finset.mem_erase.mpr ⟨hsix_ne, Finset.mem_univ _⟩
  have hsix5 : S.six ≠ S.five := by
    intro h
    have h' : S.sz S.six = 5 := by rw [h]; exact sz_five S
    omega
  have hsix_s : S.six ∈ S.rest.erase S.five := Finset.mem_erase.mpr ⟨hsix5, hsix_rest⟩
  have ht6 : 1 ≤ (S.trace S.six).card := by
    have h := hterm S.six hsix_s
    have : (S.trace S.six ∩ S.comp).card ≤ (S.trace S.six).card := Finset.card_le_card Finset.inter_subset_left
    omega
  have hb6 : 4 ≤ S.b S.six := by
    have hcap : (S.trace S.six).card ≤ 2 := by
      have h := S.trace_cap S.six
      rw [hsz_six, traceCap_six] at h
      exact h
    have hb : S.b S.six = 6 - (S.trace S.six).card := by
      rw [b, trace, Finset.card_sdiff, Finset.inter_comm S.H (S.point S.six), S.card_point S.six, hsz_six]
    omega
  have hthree : ∑ j ∈ S.rest.erase S.six, (S.out S.six j).card ≤ 3 := by
    have h1 : ∀ j ∈ S.rest.erase S.six, (S.out S.six j).card
        ≤ (if S.sz j = 2 ∨ S.sz j = 3 ∨ S.sz j = 4 then 1 else 0) := by
      intro j hj
      have hjrest : j ∈ S.rest := (Finset.mem_erase.mp hj).2
      have hja : j ≠ S.anchor := (Finset.mem_erase.mp hjrest).1
      have hj6 : S.sz j ≠ 6 := by
        intro h
        exact (Finset.mem_erase.mp hj).1 (S.sz_injective (by rw [h, hsz_six]))
      have hjmem : S.sz j ∈ lowerSizes := sz_mem_lower S hja
      have hbj : S.b j = S.sz j - (S.trace j).card := by
        rw [b, trace, Finset.card_sdiff, Finset.inter_comm S.H (S.point j), S.card_point j]
      simp only [lowerSizes, Finset.mem_insert, Finset.mem_singleton] at hjmem
      rcases hjmem with h | h | h | h | h | h
      · have hj5' : j ≠ S.five := by intro hf; rw [hf, sz_five S] at h; omega
        have hmem' : j ∈ S.rest.erase S.five := Finset.mem_erase.mpr ⟨hj5', hjrest⟩
        have hc := hterm j hmem'
        have hb0 : S.b j = 0 := by
          have hle : (S.trace j).card ≤ 1 := by have := S.trace_cap j; rw [h, traceCap_one] at this; exact this
          have hge : 1 ≤ (S.trace j).card := by
            have : (S.trace j ∩ S.comp).card ≤ (S.trace j).card := Finset.card_le_card Finset.inter_subset_left
            omega
          rw [hbj, h]; omega
        have hout0 : S.out S.six j = ∅ := by
          apply Finset.card_eq_zero.mp
          have hsub : (S.out S.six j).card ≤ S.b j := Finset.card_le_card Finset.inter_subset_right
          omega
        rw [if_neg (by rintro (h' | h' | h') <;> omega), hout0]
        simp
      · have hj5' : j ≠ S.five := by intro hf; rw [hf, sz_five S] at h; omega
        have hmem' : j ∈ S.rest.erase S.five := Finset.mem_erase.mpr ⟨hj5', hjrest⟩
        have hc := hterm j hmem'
        have hge : 1 ≤ (S.trace j).card := by
          have : (S.trace j ∩ S.comp).card ≤ (S.trace j).card := Finset.card_le_card Finset.inter_subset_left
          omega
        have hout : (S.out S.six j).card ≤ S.b j := Finset.card_le_card Finset.inter_subset_right
        rw [hbj, h] at hout
        rw [if_pos (Or.inl h)]
        omega
      · have hj5' : j ≠ S.five := by intro hf; rw [hf, sz_five S] at h; omega
        have hmem' : j ∈ S.rest.erase S.five := Finset.mem_erase.mpr ⟨hj5', hjrest⟩
        have hc := hterm j hmem'
        have h3card : (S.trace j).card = 1 := by
          have hle : (S.trace j).card ≤ 1 := by have := S.trace_cap j; rw [h, traceCap_three] at this; exact this
          have : (S.trace j ∩ S.comp).card ≤ (S.trace j).card := Finset.card_le_card Finset.inter_subset_left
          omega
        have hlt : (S.out S.six j).card ≤ 1 := by
          by_contra hcon
          push Not at hcon
          have hcon' : 2 ≤ ((S.point S.six \ S.H) ∩ (S.point j \ S.H)).card := by rw [← out_def]; omega
          have hsub := S.out_six_three S.six j hsz_six ht6 h h3card hcon'
          have heq : S.trace j ∩ S.comp = S.trace S.six ∩ S.comp := by
            apply Finset.eq_of_subset_of_card_le
            · intro x hx
              exact Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
            · rw [hterm j hmem', hterm S.six hsix_s]
          exact hdisj S.six hsix_s j hmem' (by
            intro hsj
            have hh : S.sz S.six = S.sz j := by rw [hsj]
            rw [hsz_six, h] at hh
            omega) heq.symm
        rw [if_pos (Or.inr (Or.inl h))]
        exact hlt
      · have hj5' : j ≠ S.five := by intro hf; rw [hf, sz_five S] at h; omega
        have hmem' : j ∈ S.rest.erase S.five := Finset.mem_erase.mpr ⟨hj5', hjrest⟩
        have hge : 1 ≤ (S.trace j).card := by
          have := hterm j hmem'
          have : (S.trace j ∩ S.comp).card ≤ (S.trace j).card := Finset.card_le_card Finset.inter_subset_left
          omega
        have hlt : (S.out S.six j).card ≤ 1 := S.out_six_four S.six j hsz_six ht6 h hge
        rw [if_pos (Or.inr (Or.inr h))]
        exact hlt
      · have hjf : j = S.five := S.sz_injective (by rw [h, sz_five S])
        have hb0 : S.b j = 0 := by
          have hfive0 : S.b S.five = 0 := by
            have h : S.b S.five = S.sz S.five - (S.trace S.five).card := by
              rw [b, trace, Finset.card_sdiff, Finset.inter_comm S.H (S.point S.five), S.card_point S.five]
            rw [h, sz_five S, card_trace_five S]
          rwa [hjf]
        have hout0 : S.out S.six j = ∅ := by
          apply Finset.card_eq_zero.mp
          have hsub : (S.out S.six j).card ≤ S.b j := Finset.card_le_card Finset.inter_subset_right
          omega
        rw [if_neg (by rintro (h' | h' | h') <;> omega), hout0]
        simp
      · exact absurd h hj6
    calc ∑ j ∈ S.rest.erase S.six, (S.out S.six j).card
        ≤ ∑ j ∈ S.rest.erase S.six, (if S.sz j = 2 ∨ S.sz j = 3 ∨ S.sz j = 4 then 1 else 0) := Finset.sum_le_sum h1
      _ = ∑ m ∈ S.sizeSet.erase 6, (if m = 2 ∨ m = 3 ∨ m = 4 then 1 else 0) := by
          rw [sum_rest_erase_eq S S.six (fun m => if m = 2 ∨ m = 3 ∨ m = 4 then (1 : ℕ) else 0), hsz_six]
      _ = ∑ m ∈ lowerSizes.erase 6, (if m = 2 ∨ m = 3 ∨ m = 4 then 1 else 0) := by rw [hsizeSet_eq]
      _ ≤ 3 := sum_erase_six_le_three
  have h4 := b_le_sum_out S S.six
  omega

end Anchored
end CertPP10
end HSC
