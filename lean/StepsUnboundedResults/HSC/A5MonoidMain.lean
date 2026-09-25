import StepsUnboundedResults.HSC.A5MonoidBoundsC

open scoped Classical
open Finset

namespace HSC

theorem massBound_a5IndexSet : MassBound a5IndexSet (5611 / 5852) := by
  intro N
  have hSgood : ∀ n ∈ (monoidUpTo a5IndexSet N).filter (fun n => 1 < n), Good n := by
    intro n hn
    exact good_of_mem_MonoidGen (mem_monoidUpTo.mp (Finset.mem_filter.mp hn).1).2
  have hSlt : ∀ n ∈ (monoidUpTo a5IndexSet N).filter (fun n => 1 < n), 1 < n :=
    fun n hn => (Finset.mem_filter.mp hn).2
  have hSle : ∀ n ∈ (monoidUpTo a5IndexSet N).filter (fun n => 1 < n), n ≤ N :=
    fun n hn => (mem_monoidUpTo.mp (Finset.mem_filter.mp hn).1).1
  have hterm : ∀ n ∈ (monoidUpTo a5IndexSet N).filter (fun n => 1 < n),
      (1 : ℚ) / n = term (Phi n) := by
    intro n hn
    obtain ⟨h1, -⟩ := Phi_spec (hSgood n hn)
    conv_lhs => rw [h1]
    exact one_div_pow_mul (Phi n).1 (Phi n).2.1 (Phi n).2.2
  have himage : ((monoidUpTo a5IndexSet N).filter (fun n => 1 < n)).image Phi
      ⊆ (tripleGood N).erase (0, 0, 0) := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    have hg := hSgood n hn
    obtain ⟨-, hkap⟩ := Phi_spec hg
    have hb := Phi_le hg (hSle n hn)
    rw [Finset.mem_erase]
    refine ⟨Phi_ne_zero hg (hSlt n hn), ?_⟩
    simp only [tripleGood, tripleRange, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Nat.lt_succ_iff]
    exact ⟨⟨hb.1, hb.2.1, hb.2.2⟩, hkap⟩
  calc ∑ n ∈ (monoidUpTo a5IndexSet N).filter (fun n => 1 < n), (1 : ℚ) / n
      = ∑ n ∈ (monoidUpTo a5IndexSet N).filter (fun n => 1 < n), term (Phi n) :=
        Finset.sum_congr rfl hterm
    _ = ∑ t ∈ ((monoidUpTo a5IndexSet N).filter (fun n => 1 < n)).image Phi, term t := by
        rw [← Finset.sum_image (f := term)
          (s := (monoidUpTo a5IndexSet N).filter (fun n => 1 < n)) (g := Phi)
          (fun x hx y hy hxy => Phi_inj (hSgood x hx) (hSgood y hy) hxy)]
    _ ≤ ∑ t ∈ (tripleGood N).erase (0, 0, 0), term t :=
        Finset.sum_le_sum_of_subset_of_nonneg himage (fun t _ _ => term_nonneg t)
    _ = ∑ t ∈ tripleGood N, term t - 1 := by
        have hmem : (0, 0, 0) ∈ tripleGood N := by
          simp only [tripleGood, tripleRange, Finset.mem_filter, Finset.mem_product,
            Finset.mem_range]
          exact ⟨⟨Nat.succ_pos N, ⟨Nat.succ_pos N, Nat.succ_pos N⟩⟩, by decide⟩
        have h := Finset.sum_erase_add (tripleGood N) term hmem
        have h0 : term (0, 0, 0) = 1 := by unfold term; norm_num
        rw [h0] at h
        linarith
    _ ≤ 11463 / 5852 - 1 := by
        have := triple_good_bound N
        linarith
    _ = 5611 / 5852 := by norm_num

end HSC
