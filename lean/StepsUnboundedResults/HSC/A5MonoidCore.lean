/-
HSC/A5MonoidCore.lean

Exponent description and geometric-series infrastructure for the exact `A₅` index-monoid mass bound.
-/
import StepsUnboundedResults.HSC.Defs
import Mathlib.Tactic

open scoped Classical
open Finset

namespace HSC

def kappa (i j : ℕ) : ℕ := if i < j then j - i else max 0 ((i + 1) / 2 - j)

theorem kappa_le_iff {i j k : ℕ} : kappa i j ≤ k ↔ j ≤ i + k ∧ (i + 1) / 2 ≤ j + k := by
  unfold kappa
  split_ifs with hij
  · constructor
    · intro h; exact ⟨by omega, by omega⟩
    · intro h; omega
  · rw [max_le_iff]
    constructor
    · rintro ⟨-, h⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨Nat.zero_le _, by omega⟩

theorem kappa_add_le {i j k i' j' k' : ℕ} (h : kappa i j ≤ k) (h' : kappa i' j' ≤ k') :
    kappa (i + i') (j + j') ≤ k + k' := by
  rw [kappa_le_iff] at h h' ⊢
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨by omega, ?_⟩
  have h3 : (i + i' + 1) / 2 ≤ (i + 1) / 2 + (i' + 1) / 2 := by omega
  omega

def Good (n : ℕ) : Prop :=
  ∃ t : ℕ × ℕ × ℕ, n = 2^t.1 * 3^t.2.1 * 5^t.2.2 ∧ kappa t.1 t.2.1 ≤ t.2.2

theorem good_mul {m n : ℕ} (hm : Good m) (hn : Good n) : Good (m * n) := by
  obtain ⟨t, ht, htk⟩ := hm
  obtain ⟨u, hu, huk⟩ := hn
  refine ⟨(t.1 + u.1, t.2.1 + u.2.1, t.2.2 + u.2.2), ?_, kappa_add_le htk huk⟩
  rw [ht, hu, pow_add, pow_add, pow_add]; ring

theorem good_of_mem_a5IndexSet : ∀ a ∈ a5IndexSet, Good a := by
  intro a ha
  simp only [a5IndexSet, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 0, 0), by decide, by decide⟩
  · exact ⟨(0, 0, 1), by decide, by decide⟩
  · exact ⟨(1, 1, 0), by decide, by decide⟩
  · exact ⟨(1, 0, 1), by decide, by decide⟩
  · exact ⟨(2, 1, 0), by decide, by decide⟩
  · exact ⟨(0, 1, 1), by decide, by decide⟩
  · exact ⟨(2, 0, 1), by decide, by decide⟩
  · exact ⟨(1, 1, 1), by decide, by decide⟩
  · exact ⟨(2, 1, 1), by decide, by decide⟩

theorem good_of_mem_MonoidGen : ∀ {n : ℕ}, n ∈ MonoidGen a5IndexSet → Good n := by
  rintro n ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil => intro _; exact ⟨(0, 0, 0), by decide, by decide⟩
  | cons a L ih =>
      intro hL
      have ha : a ∈ a5IndexSet := hL a (by simp)
      have ih' : Good L.prod := ih (fun b hb => hL b (by simp [hb]))
      simpa [List.prod_cons] using good_mul (good_of_mem_a5IndexSet a ha) ih'

noncomputable def Phi (n : ℕ) : ℕ × ℕ × ℕ :=
  if h : Good n then Classical.choose h else (0, 0, 0)

theorem Phi_spec {n : ℕ} (h : Good n) :
    n = 2^(Phi n).1 * 3^(Phi n).2.1 * 5^(Phi n).2.2 ∧
      kappa (Phi n).1 (Phi n).2.1 ≤ (Phi n).2.2 := by
  have hc : Phi n = Classical.choose h := by unfold Phi; rw [dif_pos h]
  rw [hc]
  exact Classical.choose_spec h

theorem Phi_inj {m n : ℕ} (hm : Good m) (hn : Good n) (h : Phi m = Phi n) : m = n := by
  obtain ⟨hm1, -⟩ := Phi_spec hm
  obtain ⟨hn1, -⟩ := Phi_spec hn
  rw [hm1, h, ← hn1]

theorem Phi_ne_zero {n : ℕ} (h : Good n) (hn : 1 < n) : Phi n ≠ (0, 0, 0) := by
  intro h0
  obtain ⟨h1, -⟩ := Phi_spec h
  rw [h0] at h1
  simp only [pow_zero, mul_one] at h1
  omega

theorem Phi_le {n N : ℕ} (h : Good n) (hN : n ≤ N) :
    (Phi n).1 ≤ N ∧ (Phi n).2.1 ≤ N ∧ (Phi n).2.2 ≤ N := by
  obtain ⟨h1, -⟩ := Phi_spec h
  have hp1 : 2^(Phi n).1 ≤ n := by
    conv_rhs => rw [h1]
    calc 2^(Phi n).1 ≤ 2^(Phi n).1 * (3^(Phi n).2.1 * 5^(Phi n).2.2) :=
          Nat.le_mul_of_pos_right _
            (Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _))
      _ = 2^(Phi n).1 * 3^(Phi n).2.1 * 5^(Phi n).2.2 := by ring
  have hp2 : 3^(Phi n).2.1 ≤ n := by
    conv_rhs => rw [h1]
    calc 3^(Phi n).2.1 ≤ 2^(Phi n).1 * 3^(Phi n).2.1 :=
          Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
      _ ≤ (2^(Phi n).1 * 3^(Phi n).2.1) * 5^(Phi n).2.2 :=
          Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
  have hp3 : 5^(Phi n).2.2 ≤ n := by
    conv_rhs => rw [h1]
    exact Nat.le_mul_of_pos_left _
      (Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _))
  have h2 : (Phi n).1 ≤ 2^(Phi n).1 := le_of_lt Nat.lt_two_pow_self
  have h3 : (Phi n).2.1 ≤ 3^(Phi n).2.1 :=
    le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by norm_num) _)
  have h4 : (Phi n).2.2 ≤ 5^(Phi n).2.2 :=
    le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by norm_num) _)
  exact ⟨by omega, by omega, by omega⟩

theorem geom_range_eq (x : ℚ) (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, x^k = (1 - x^n) / (1 - x) := by
  have h1 : x^n - 1 = -(1 - x^n) := by ring
  have h2 : x - 1 = -(1 - x) := by ring
  rw [geom_sum_eq hx n, h1, h2, neg_div_neg_eq]

theorem geom_range_le (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    ∑ k ∈ range n, x^k ≤ 1 / (1 - x) := by
  rw [geom_range_eq x (ne_of_lt h1) n]
  have hpos : (0 : ℚ) < 1 - x := by linarith
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg h0 n]) (le_of_lt hpos)

theorem geom_Ico_eq (x : ℚ) (hx : x ≠ 1) (m n : ℕ) :
    ∑ k ∈ Ico m n, x^k = x^m * ((1 - x^(n - m)) / (1 - x)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∀ t, x^(m + t) = x^m * x^t := fun t => by rw [pow_add]
  simp only [h]
  rw [← Finset.mul_sum]
  congr 1
  exact geom_range_eq x hx (n - m)

theorem geom_Ico_le (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (m n : ℕ) :
    ∑ k ∈ Ico m n, x^k ≤ x^m * (1 / (1 - x)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h : ∀ t, x^(m + t) = x^m * x^t := fun t => by rw [pow_add]
  simp only [h]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (geom_range_le x h0 h1 _) (pow_nonneg h0 m)

end HSC
