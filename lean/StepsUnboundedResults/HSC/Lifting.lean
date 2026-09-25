/-
HSC/Lifting.lean

Machine-checked pieces of the R004/R006 lifting circle, complementing the counting layer
(`HSC/Criterion`) and the monoid layer (`HSC/A5Monoid`, `HSC/Assembly`).

* `geom_sum_pow_mul_pred_add_one`, `geom_range_lt` : the subtraction-free geometric bound
  `∑_{k<n} p^k < p^n` underlying the `p`-adic counting argument.

* `isHS_of_card_eq_prime_pow` / `isHS_of_isPGroup` : **every finite `p`-group satisfies the
  Herzog–Schönheim conjecture.**  This is the degenerate (`Q = 1`) case of R004's lifting
  theorem, proved here by the classical `p`-adic counting argument alone: a coset partition
  with pairwise distinct indices would write `p^n` as a sum of pairwise distinct powers `p^k`,
  `k < n`, and `∑_{k<n} p^k < p^n`.  Neither the index-set enumeration nor the monoid mass is
  used.  (The paper's mass criterion also happens to apply to `p`-groups: the distinct indices
  of a group of order `p^n` are `1, p, …, pⁿ`, so `𝒥 = ∑_{k≤n} p^{-k} < 2`.  The point of
  this file is that the `p`-adic route closes the case with no mass computation at all.)

Everything is kernel-checked; no `sorry`, no `axiom`, no `native_decide`.
-/
import StepsUnboundedResults.HSC.Criterion
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

open scoped Classical
open Finset

namespace HSC

variable {G : Type*} [Group G] [Finite G]

/-! ## 1. The geometric bound `∑_{k<n} p^k < p^n` -/

theorem geom_sum_pow_mul_pred_add_one {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    (∑ k ∈ range n, p ^ k) * (p - 1) + 1 = p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : p ^ n * (p - 1) + p ^ n = p ^ n * p := by
        have h2 : p ^ n * (p - 1) + p ^ n * 1 = p ^ n * p := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hp]
        simpa using h2
      have h3 : (∑ k ∈ range n, p ^ k) * (p - 1) + p ^ n * (p - 1) + 1
          = ((∑ k ∈ range n, p ^ k) * (p - 1) + 1) + p ^ n * (p - 1) := by ring
      rw [Finset.sum_range_succ, add_mul, pow_succ, h3, ih]
      exact (add_comm (p ^ n) (p ^ n * (p - 1))).trans h1

theorem geom_range_lt {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (∑ k ∈ range n, p ^ k) < p ^ n := by
  have hp2 : 2 ≤ p := hp.two_le
  have h := geom_sum_pow_mul_pred_add_one (p := p) (by omega) n
  have hle : (∑ k ∈ range n, p ^ k) ≤ (∑ k ∈ range n, p ^ k) * (p - 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hlt : (∑ k ∈ range n, p ^ k) * (p - 1) < p ^ n := by omega
  exact lt_of_le_of_lt hle hlt

theorem isHS_of_card_eq_prime_pow {p n : ℕ} (hp : p.Prime) (hcard : Nat.card G = p ^ n) :
    IsHS G := by
  classical
  intro P
  by_contra hcon
  push_neg at hcon
  have hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index :=
    fun i j hij h => hcon i j hij h
  have hex : ∀ i : P.ι, ∃ e : ℕ, e ≤ n ∧ (P.H i).index = p ^ e := by
    intro i
    have hdvd : (P.H i).index ∣ p ^ n := by
      rw [← hcard]; exact Subgroup.index_dvd_card (P.H i)
    exact (Nat.dvd_prime_pow hp).mp hdvd
  choose e he hpow using hex
  have hepos : ∀ i, 1 ≤ e i := by
    intro i
    by_contra h
    have h0 : e i = 0 := by omega
    exact P.proper i (Subgroup.index_eq_one.mp (by rw [hpow i, h0, pow_zero]))
  haveI : Nonempty P.ι := by
    have h2 : 0 < Nat.card P.ι := by have := P.two_le; omega
    rw [Nat.card_eq_fintype_card] at h2
    exact Fintype.card_pos_iff.mp h2
  have hnpos : 0 < n := by
    obtain ⟨i⟩ := ‹Nonempty P.ι›
    have h1 := he i
    have h2 := hepos i
    omega
  have hcardH : ∀ i, Nat.card (P.H i) = p ^ (n - e i) := by
    intro i
    have hmul := Subgroup.index_mul_card (P.H i)
    rw [hpow i, hcard] at hmul
    have h2 : p ^ e i * p ^ (n - e i) = p ^ n := by
      rw [← pow_add, add_comm (e i) (n - e i), Nat.sub_add_cancel (he i)]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) (by rw [hmul, h2])
  have hsum : p ^ n = ∑ i : P.ι, p ^ (n - e i) := by
    rw [← hcard, card_eq_sum_card P]
    exact Finset.sum_congr rfl fun i _ => hcardH i
  have hinj : ∀ i j : P.ι, i ≠ j → n - e i ≠ n - e j := by
    intro i j hij h
    apply hdist i j hij
    have hee : e i = e j := by
      rw [← Nat.sub_sub_self (he i), ← Nat.sub_sub_self (he j), h]
    rw [hpow i, hpow j, hee]
  have hbound : ∑ i : P.ι, p ^ (n - e i) < p ^ n := by
    have himg : ∑ i : P.ι, p ^ (n - e i)
        = ∑ k ∈ (univ : Finset P.ι).image (fun i => n - e i), p ^ k :=
      (Finset.sum_image (f := fun k => p ^ k) (g := fun i => n - e i) (s := univ)
        (fun i _ j _ hij => by by_contra hne; exact hinj i j hne hij)).symm
    have h2 : ∑ k ∈ (univ : Finset P.ι).image (fun i => n - e i), p ^ k < p ^ n := by
      calc ∑ k ∈ (univ : Finset P.ι).image (fun i => n - e i), p ^ k
          ≤ ∑ k ∈ range n, p ^ k := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_
              (fun k _ _ => pow_nonneg (Nat.zero_le p) k)
            intro k hk
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
            simp only [Finset.mem_range]
            exact Nat.sub_lt hnpos (hepos i)
        _ < p ^ n := geom_range_lt hp n
    exact himg.symm ▸ h2
  exact absurd (hsum ▸ hbound) (lt_irrefl _)

theorem isHS_of_isPGroup {p : ℕ} [Fact p.Prime] (h : IsPGroup p G) : IsHS G := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  exact isHS_of_card_eq_prime_pow Fact.out hn

omit [Finite G] in
theorem leftCoset_one_top : leftCoset (1 : G) (⊤ : Subgroup G) = Set.univ := by
  ext g
  simp [mem_leftCoset]

omit [Finite G] in
theorem leftCoset_eq_univ_iff {x : G} {H : Subgroup G} :
    leftCoset x H = Set.univ ↔ H = ⊤ := by
  constructor
  · intro h
    ext g
    refine ⟨fun _ => Subgroup.mem_top g, fun _ => ?_⟩
    have h1 : x * g ∈ leftCoset x H := by rw [h]; trivial
    have h2 : x⁻¹ * (x * g) ∈ H := h1
    simpa using h2
  · intro h
    rw [h]
    exact leftCoset_one_top

def LICosets (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → G) (H : ι → Subgroup G),
    (∀ i j, i ≠ j → leftCoset (c i) (H i) ≠ leftCoset (c j) (H j)) →
    (∀ i j, i ≠ j → (H i).index ≠ (H j).index) →
    LinearIndependent (ZMod p) fun i =>
      (leftCoset (c i) (H i)).indicator fun _ => (1 : ZMod p)

omit [Finite G] in
theorem isHS_of_licosets {p : ℕ} (hp : p.Prime) (h : LICosets p G) : IsHS G := by
  classical
  intro P
  by_contra hcon
  push_neg at hcon
  have hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index :=
    fun i j hij hh => hcon i j hij hh
  let c : Option P.ι → G := fun o => o.elim 1 P.x
  let H : Option P.ι → Subgroup G := fun o => o.elim ⊤ P.H
  have hcnone : c none = 1 := rfl
  have hcsome : ∀ i, c (some i) = P.x i := fun i => rfl
  have hHnone : H none = ⊤ := rfl
  have hHsome : ∀ i, H (some i) = P.H i := fun i => rfl
  have hnone_univ : leftCoset (c none) (H none) = Set.univ := by
    rw [hcnone, hHnone]; exact leftCoset_one_top
  have hsome_eq : ∀ i, leftCoset (c (some i)) (H (some i)) = leftCoset (P.x i) (P.H i) :=
    fun i => by rw [hcsome i, hHsome i]
  have hcoset : ∀ o o' : Option P.ι, o ≠ o' →
      leftCoset (c o) (H o) ≠ leftCoset (c o') (H o') := by
    intro o o' hne hEq
    rcases o with _ | i
    · rcases o' with _ | j
      · exact absurd rfl hne
      · have h1 : leftCoset (P.x j) (P.H j) = Set.univ := by
          rw [← hsome_eq j, ← hEq, hnone_univ]
        exact P.proper j (leftCoset_eq_univ_iff.mp h1)
    · rcases o' with _ | j
      · have h1 : leftCoset (P.x i) (P.H i) = Set.univ := by
          rw [← hsome_eq i, hEq, hnone_univ]
        exact P.proper i (leftCoset_eq_univ_iff.mp h1)
      · have hij : i ≠ j := by rintro rfl; exact hne rfl
        have hd := P.disjoint i j hij
        have hmem : P.x i ∈ leftCoset (P.x i) (P.H i) := by simp [mem_leftCoset]
        have hEq' : leftCoset (P.x i) (P.H i) = leftCoset (P.x j) (P.H j) := by
          rw [← hsome_eq i, hEq, hsome_eq j]
        have h2 : P.x i ∈ (⊥ : Set G) := hd.le_bot ⟨hmem, by rw [← hEq']; exact hmem⟩
        simpa using h2
  have hidx : ∀ o o' : Option P.ι, o ≠ o' → (H o).index ≠ (H o').index := by
    intro o o' hne
    rcases o with _ | i
    · rcases o' with _ | j
      · exact absurd rfl hne
      · intro hh
        rw [hHnone, hHsome j, Subgroup.index_eq_one.mpr rfl] at hh
        exact P.proper j (Subgroup.index_eq_one.mp hh.symm)
    · rcases o' with _ | j
      · intro hh
        rw [hHnone, hHsome i, Subgroup.index_eq_one.mpr rfl] at hh
        exact P.proper i (Subgroup.index_eq_one.mp hh)
      · intro hh
        exact hdist i j (by rintro rfl; exact hne rfl)
          (by simpa only [hHsome i, hHsome j] using hh)
  have hLI := h (Option P.ι) c H hcoset hidx
  let g : Option P.ι → ZMod p := fun o => match o with | none => -1 | some _ => 1
  have hrel : (∑ o : Option P.ι, g o • fun y : G =>
      (leftCoset (c o) (H o)).indicator (fun _ => (1 : ZMod p)) y) = 0 := by
    funext x
    rw [Finset.sum_apply, Fintype.sum_option]
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨i₀, hx₀⟩ : ∃ i, x ∈ leftCoset (P.x i) (P.H i) := P.cover x
    have hnone : g none * (leftCoset (c none) (H none)).indicator (fun _ => (1 : ZMod p)) x
        = -1 := by
      rw [hcnone, hHnone, leftCoset_one_top, Set.indicator_of_mem (Set.mem_univ x)]
      simp [g]
    have hsome : (∑ i : P.ι, g (some i) *
        (leftCoset (c (some i)) (H (some i))).indicator (fun _ => (1 : ZMod p)) x) = 1 := by
      rw [Finset.sum_eq_single i₀]
      · rw [hcsome, hHsome, Set.indicator_of_mem hx₀]
        simp [g]
      · intro i _ hi
        have hxnot : x ∉ leftCoset (P.x i) (P.H i) := by
          intro hx
          have hd := P.disjoint i₀ i (by rintro rfl; exact hi rfl)
          have h2 : x ∈ (⊥ : Set G) := hd.le_bot ⟨hx₀, hx⟩
          simpa using h2
        rw [hcsome, hHsome, Set.indicator_of_notMem hxnot, mul_zero]
      · exact fun hmem => absurd (Finset.mem_univ i₀) hmem
    rw [hnone, hsome]
    ring
  have hg : ∀ o, g o = 0 := (Fintype.linearIndependent_iff.mp hLI) g hrel
  have h1 : ((-1 : ZMod p) = 0) := by simpa [g] using hg none
  have h2 : (1 : ZMod p) = 0 := by simpa using neg_eq_zero.mp h1
  exact hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h2))

end HSC
