import StepsUnboundedResults.HSC.CertPPSixTraceB

open scoped BigOperators
open Finset

namespace HSC.CertPP

variable {G : Type*} [Group G] [Fintype G]

theorem le_three_of_dvd_six {x : ℕ} (h : x ∣ 6) (h5 : x ≤ 5) : x ≤ 3 := by
  rcases Nat.lt_or_ge x 4 with h4 | h4
  · omega
  · have hx : x = 4 ∨ x = 5 := by omega
    rcases hx with hx | hx
    · rw [hx] at h; norm_num at h
    · rw [hx] at h; norm_num at h

theorem anchor_six_arith {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (n a : ι → ℕ)
    (hn1 : ∀ i ∈ s, 1 ≤ n i) (hn5 : ∀ i ∈ s, n i ≤ 5)
    (hinj : Set.InjOn n (↑s : Set ι))
    (hdvd : ∀ i ∈ s, a i = 0 ∨ (a i ∣ n i ∧ a i ∣ 6))
    (hsum : 6 ≤ ∑ i ∈ s, a i)
    (hsieve : ∀ i ∈ s, n i - a i = 0 ∨
      n i - a i ≤ ∑ j ∈ s.erase i, min (n j - a j) (Nat.gcd (n i) (n j))) :
    (∑ i ∈ s, a i = 6) ∧ (∃ i ∈ s, a i = 3) ∧ (∃ i ∈ s, a i = 2) := by
  classical
  have hale : ∀ i ∈ s, a i ≤ n i := by
    intro i hi
    rcases hdvd i hi with h | h
    · omega
    · exact Nat.le_of_dvd (by have := hn1 i hi; omega) h.1
  set A : ℕ → ℕ := fun m => ∑ i ∈ s.filter (fun i => n i = m), a i with hAdef
  have himage_sub : s.image n ⊆ ({1, 2, 3, 4, 5} : Finset ℕ) := by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    have h1 := hn1 i hi
    have h2 := hn5 i hi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hA_self : ∀ i ∈ s, A (n i) = a i := by
    intro i hi
    have hf : s.filter (fun j => n j = n i) = {i} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hi, rfl⟩, ?_⟩
      intro j hj
      rw [Finset.mem_filter] at hj
      exact hinj hj.1 hi hj.2
    simp [hAdef, hf]
  have hA_zero : ∀ m, m ∉ s.image n → A m = 0 := by
    intro m hm
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    exact absurd (Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩) hm
  have hA_le : ∀ m, m ≤ 5 → A m ≤ m := by
    intro m _
    by_cases hemp : s.filter (fun i => n i = m) = ∅
    · simp [hAdef, hemp]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      rw [Finset.mem_filter] at hi
      have hf : s.filter (fun j => n j = m) = {i} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr hi, ?_⟩
        intro j hj
        rw [Finset.mem_filter] at hj
        exact hinj hj.1 hi.1 (hj.2.trans hi.2.symm)
      have h1 : A m = a i := by simp only [hAdef, hf, Finset.sum_singleton]
      rw [h1]
      have hle : a i ≤ n i := hale i hi.1
      omega
  have hA_dvd : ∀ m, m ∈ s.image n → A m = 0 ∨ (A m ∣ m ∧ A m ∣ 6) := by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    rw [hA_self i hi]
    exact hdvd i hi
  have hA3le : A 3 ≠ 3 → A 3 ≤ 1 := by
    intro hne
    by_cases h : (3 : ℕ) ∈ s.image n
    · rcases hA_dvd 3 h with h0 | hd
      · omega
      · have hle := hA_le 3 (by norm_num)
        rcases Nat.lt_or_ge (A 3) 2 with h2 | h2
        · omega
        · have hA3e : A 3 = 2 ∨ A 3 = 3 := by omega
          rcases hA3e with h3 | h3
          · rw [h3] at hd
            obtain ⟨c, hc⟩ := hd
            omega
          · exact absurd h3 hne
    · have hz := hA_zero 3 h
      omega
  have hsum_fib : ∑ i ∈ s, a i = ∑ m ∈ ({1, 2, 3, 4, 5} : Finset ℕ), A m := by
    have hbU : (s.image n).biUnion (fun m => s.filter (fun i => n i = m)) = s := by
      ext i; constructor
      · intro hi
        rw [Finset.mem_biUnion] at hi
        obtain ⟨m, _, hmi⟩ := hi
        rw [Finset.mem_filter] at hmi
        exact hmi.1
      · intro hi
        rw [Finset.mem_biUnion]
        exact ⟨n i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
    have hpd : (↑(s.image n) : Set ℕ).PairwiseDisjoint (fun m => s.filter (fun i => n i = m)) := by
      intro m _ m' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i hi hi'
      rw [Finset.mem_filter] at hi hi'
      exact hne (hi.2.symm.trans hi'.2)
    calc ∑ i ∈ s, a i
        = ∑ x ∈ (s.image n).biUnion (fun m => s.filter (fun i => n i = m)), a x := by rw [hbU]
      _ = ∑ m ∈ s.image n, ∑ i ∈ s.filter (fun i => n i = m), a i := Finset.sum_biUnion hpd
      _ = ∑ m ∈ s.image n, A m := rfl
      _ = ∑ m ∈ ({1, 2, 3, 4, 5} : Finset ℕ), A m :=
          Finset.sum_subset himage_sub (fun m _ hm => hA_zero m hm)
  have hsum_expl : ∑ m ∈ ({1, 2, 3, 4, 5} : Finset ℕ), A m
      = A 1 + A 2 + A 3 + A 4 + A 5 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ac_rfl
  have hsum_eq : ∑ i ∈ s, a i = A 1 + A 2 + A 3 + A 4 + A 5 := hsum_fib.trans hsum_expl
  have hsieve' : ∀ i ∈ s, n i - a i = 0 ∨
      n i - a i ≤ ∑ m ∈ (s.erase i).image n, min (m - A m) (Nat.gcd (n i) m) := by
    intro i hi
    have hinj' : Set.InjOn n (↑(s.erase i) : Set ι) := fun x hx y hy hxy =>
      hinj (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
    have hcongr : ∑ j ∈ s.erase i, min (n j - a j) (Nat.gcd (n i) (n j))
        = ∑ m ∈ (s.erase i).image n, min (m - A m) (Nat.gcd (n i) m) := by
      rw [Finset.sum_image (f := fun m => min (m - A m) (Nat.gcd (n i) m)) hinj']
      exact Finset.sum_congr rfl (fun j hj => by
        rw [hA_self j (Finset.mem_of_mem_erase hj)])
    rcases hsieve i hi with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans_eq hcongr)
  by_cases h5 : ∃ i ∈ s, n i = 5
  · exfalso
    obtain ⟨i5, hi5, hi5n⟩ := h5
    have hA5 : A 5 = a i5 := by rw [← hi5n]; exact hA_self i5 hi5
    have hA5le1 : A 5 ≤ 1 := by
      rw [hA5]
      rcases hdvd i5 hi5 with h | h
      · omega
      · rw [hi5n] at h
        have h3 : a i5 ∣ Nat.gcd 5 6 := Nat.dvd_gcd h.1 h.2
        have h4' : Nat.gcd 5 6 = 1 := by norm_num
        rw [h4'] at h3
        exact Nat.le_of_dvd (by norm_num) h3
    have hFsub : (s.erase i5).image n ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro m hm
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
      have hj' := Finset.mem_of_mem_erase hj
      have h1 := hn1 j hj'
      have h2 := hn5 j hj'
      have hne : n j ≠ 5 := by
        rintro h
        exact (Finset.mem_erase.mp hj).1 (hinj hj' hi5 (h.trans hi5n.symm))
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hFcard : ((s.erase i5).image n).card ≤ 4 := by
      calc ((s.erase i5).image n).card ≤ (({1, 2, 3, 4} : Finset ℕ)).card :=
            Finset.card_le_card hFsub
        _ = 4 := by decide
    have hterm : ∀ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd 5 m) ≤ 1 := by
      intro m hm
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
      have hj' := Finset.mem_of_mem_erase hj
      have h1 : n j ≤ 4 := by
        have := hFsub (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        omega
      have h0 : 1 ≤ n j := hn1 j hj'
      have h2 : Nat.gcd 5 (n j) = 1 := by interval_cases n j <;> norm_num
      rw [h2]
      exact min_le_right _ _
    have hs5 : 5 - A 5 ≤ ∑ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd 5 m) := by
      have hb5 : n i5 - a i5 = 5 - A 5 := by rw [hi5n, ← hA5]
      have h' : 5 - A 5 ≤ ∑ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd (n i5) m) := by
        rcases hsieve' i5 hi5 with h | h
        · rw [hb5] at h; omega
        · rwa [hb5] at h
      simpa only [hi5n] using h'
    have hbound : ∑ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd 5 m) ≤ 4 := by
      calc _ ≤ ∑ _m ∈ (s.erase i5).image n, (1 : ℕ) := Finset.sum_le_sum hterm
        _ = ((s.erase i5).image n).card := by simp
        _ ≤ 4 := hFcard
    have hA5eq : A 5 = 1 := by omega
    have hsum4 : ∑ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd 5 m) = 4 := by omega
    have hcard4 : ((s.erase i5).image n).card = 4 := by
      have : ∑ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd 5 m)
          ≤ ((s.erase i5).image n).card := by
        calc _ ≤ ∑ _m ∈ (s.erase i5).image n, (1 : ℕ) := Finset.sum_le_sum hterm
          _ = ((s.erase i5).image n).card := by simp
      omega
    have hall : ∀ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd 5 m) = 1 := by
      have h2 : ∑ m ∈ (s.erase i5).image n, min (m - A m) (Nat.gcd 5 m)
          = ∑ _m ∈ (s.erase i5).image n, (1 : ℕ) := by rw [hsum4]; simp [hcard4]
      exact (Finset.sum_eq_sum_iff_of_le hterm).mp h2
    have hkey : ∀ m, m ≤ 4 → A m ≤ m - 1 := by
      intro m hm4
      by_cases hmem : m ∈ (s.erase i5).image n
      · have := hall m hmem; omega
      · by_cases hsm : m ∈ s.image n
        · exfalso
          obtain ⟨i, hi, hin⟩ := Finset.mem_image.mp hsm
          have hii : i = i5 := by
            by_contra hne
            exact hmem (Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hne, hi⟩, hin⟩)
          rw [hii] at hin
          omega
        · rw [hA_zero m hsm]; omega
    have hA1 : A 1 = 0 := by have := hkey 1 (by norm_num); omega
    have hA2 : A 2 ≤ 1 := by have := hkey 2 (by norm_num); omega
    have hA3 : A 3 ≤ 1 := by
      by_cases h3 : A 3 = 3
      · have := hkey 3 (by norm_num); omega
      · exact hA3le h3
    have hA4 : A 4 ≤ 2 := by
      have h3 := hkey 4 (by norm_num)
      by_cases hsm : (4 : ℕ) ∈ s.image n
      · rcases hA_dvd 4 hsm with h0 | hd
        · omega
        · have hg : A 4 ∣ Nat.gcd 4 6 := Nat.dvd_gcd hd.1 hd.2
          have hg' : Nat.gcd 4 6 = 2 := by norm_num
          rw [hg'] at hg
          exact Nat.le_of_dvd (by norm_num) hg
      · have hz := hA_zero 4 hsm; omega
    omega
  · push Not at h5
    have hA5zero : A 5 = 0 := hA_zero 5 (by
      intro hmem
      obtain ⟨i, hi, hin⟩ := Finset.mem_image.mp hmem
      exact h5 i hi hin)
    have hsum_eq' : ∑ i ∈ s, a i = A 1 + A 2 + A 3 + A 4 := by omega
    by_cases h4 : ∃ i ∈ s, n i = 4
    · obtain ⟨i4, hi4, hi4n⟩ := h4
      have hA4 : A 4 = a i4 := by rw [← hi4n]; exact hA_self i4 hi4
      have hA4le2 : A 4 ≤ 2 := by
        rw [hA4]
        rcases hdvd i4 hi4 with h | h
        · omega
        · rw [hi4n] at h
          have h3 : a i4 ∣ Nat.gcd 4 6 := Nat.dvd_gcd h.1 h.2
          have h4' : Nat.gcd 4 6 = 2 := by norm_num
          rw [h4'] at h3
          exact Nat.le_of_dvd (by norm_num) h3
      have hFsub : (s.erase i4).image n ⊆ ({1, 2, 3} : Finset ℕ) := by
        intro m hm
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
        have hj' := Finset.mem_of_mem_erase hj
        have h1 := hn1 j hj'
        have h2 := hn5 j hj'
        have hne5 : n j ≠ 5 := h5 j hj'
        have hne4 : n j ≠ 4 := by
          rintro h
          exact (Finset.mem_erase.mp hj).1 (hinj hj' hi4 (h.trans hi4n.symm))
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hs4 : 4 - A 4 ≤ ∑ m ∈ (s.erase i4).image n, min (m - A m) (Nat.gcd 4 m) := by
        have hb4 : n i4 - a i4 = 4 - A 4 := by rw [hi4n, ← hA4]
        have h' : 4 - A 4 ≤ ∑ m ∈ (s.erase i4).image n, min (m - A m) (Nat.gcd (n i4) m) := by
          rcases hsieve' i4 hi4 with h | h
          · rw [hb4] at h; omega
          · rwa [hb4] at h
        simpa only [hi4n] using h'
      have hTle : ∑ m ∈ (s.erase i4).image n, min (m - A m) (Nat.gcd 4 m)
          ≤ min (1 - A 1) 1 + min (2 - A 2) 2 + min (3 - A 3) 1 := by
        calc _ ≤ ∑ m ∈ ({1, 2, 3} : Finset ℕ), min (m - A m) (Nat.gcd 4 m) :=
              Finset.sum_le_sum_of_subset_of_nonneg hFsub (by intro i _ _; omega)
          _ = min (1 - A 1) (Nat.gcd 4 1) + min (2 - A 2) (Nat.gcd 4 2)
                + min (3 - A 3) (Nat.gcd 4 3) := by
              rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
                Finset.sum_singleton]
              ac_rfl
          _ = min (1 - A 1) 1 + min (2 - A 2) 2 + min (3 - A 3) 1 := by norm_num
      have hA1le : A 1 ≤ 1 := hA_le 1 (by norm_num)
      have hA2le : A 2 ≤ 2 := hA_le 2 (by norm_num)
      have hsum4 : 6 ≤ A 1 + A 2 + A 3 + A 4 := by omega
      rcases Nat.lt_or_ge (A 4) 1 with h4a | h4a
      · have hA4e : A 4 = 0 := by omega
        have hb : min (1 - A 1) 1 + min (2 - A 2) 2 + min (3 - A 3) 1 ≤ 4 - A 1 - A 2 := by
          have h1 := min_le_left (1 - A 1) 1
          have h2 := min_le_left (2 - A 2) 2
          have h3 := min_le_right (3 - A 3) (1 : ℕ)
          omega
        omega
      · rcases Nat.lt_or_ge (A 4) 2 with h4b | h4b
        · have hA4e : A 4 = 1 := by omega
          have hT3 : 3 ≤ min (1 - A 1) 1 + min (2 - A 2) 2 + min (3 - A 3) 1 := by
            have h := hs4; rw [hA4e] at h; omega
          by_cases h3 : A 3 = 3
          · have hb : 3 ≤ 3 - A 1 - A 2 := by
              have h1 := min_le_left (1 - A 1) 1
              have h2 := min_le_left (2 - A 2) 2
              have h3' : min (3 - A 3) 1 = 0 := by rw [h3]; norm_num
              omega
            omega
          · have h3le : A 3 ≤ 1 := hA3le h3
            have hb : min (1 - A 1) 1 + min (2 - A 2) 2 + min (3 - A 3) 1
                ≤ 4 - A 1 - A 2 := by
              have h1 := min_le_left (1 - A 1) 1
              have h2 := min_le_left (2 - A 2) 2
              have h3' := min_le_right (3 - A 3) (1 : ℕ)
              omega
            omega
        · have hA4e : A 4 = 2 := by omega
          have hT2 : 2 ≤ min (1 - A 1) 1 + min (2 - A 2) 2 + min (3 - A 3) 1 := by
            have h := hs4; rw [hA4e] at h; omega
          have hS : 4 ≤ A 1 + A 2 + A 3 := by omega
          by_cases h3 : A 3 = 3
          · have hcases : (A 1 = 1 ∧ A 2 = 0) ∨ (A 1 = 0 ∧ A 2 = 1) := by
              have h1 := min_le_left (1 - A 1) 1
              have h2 := min_le_left (2 - A 2) 2
              have h3' : min (3 - A 3) 1 = 0 := by rw [h3]; norm_num
              rw [h3'] at hT2
              omega
            have hfin : A 1 + A 2 + A 3 + A 4 = 6 := by omega
            have hmem3 : (3 : ℕ) ∈ s.image n := by
              by_contra hc
              exact absurd (hA_zero 3 hc) (by omega)
            refine ⟨by omega, ?_, ?_⟩
            · obtain ⟨j, hj, hjn⟩ := Finset.mem_image.mp hmem3
              exact ⟨j, hj, by rw [← hA_self j hj, hjn]; exact h3⟩
            · exact ⟨i4, hi4, by rw [← hA4]; exact hA4e⟩
          · have h3le : A 3 ≤ 1 := hA3le h3
            have hb : min (1 - A 1) 1 + min (2 - A 2) 2 + min (3 - A 3) 1 ≤ 1 := by
              have h1 := min_le_left (1 - A 1) 1
              have h2 := min_le_left (2 - A 2) 2
              have h3' := min_le_right (3 - A 3) (1 : ℕ)
              have hS' : 3 ≤ A 1 + A 2 := by omega
              omega
            omega
    · push Not at h4
      have hA4zero : A 4 = 0 := hA_zero 4 (by
        intro hmem
        obtain ⟨i, hi, hin⟩ := Finset.mem_image.mp hmem
        exact h4 i hi hin)
      have hA1 : A 1 ≤ 1 := hA_le 1 (by norm_num)
      have hA2 : A 2 ≤ 2 := hA_le 2 (by norm_num)
      have hA3 : A 3 ≤ 3 := hA_le 3 (by norm_num)
      have hall : A 1 + A 2 + A 3 = 6 := by omega
      have hA3e : A 3 = 3 := by omega
      have hA2e : A 2 = 2 := by omega
      have hmem3 : (3 : ℕ) ∈ s.image n := by
        by_contra hc
        exact absurd (hA_zero 3 hc) (by omega)
      have hmem2 : (2 : ℕ) ∈ s.image n := by
        by_contra hc
        exact absurd (hA_zero 2 hc) (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · obtain ⟨j, hj, hjn⟩ := Finset.mem_image.mp hmem3
        exact ⟨j, hj, by rw [← hA_self j hj, hjn]; exact hA3e⟩
      · obtain ⟨j, hj, hjn⟩ := Finset.mem_image.mp hmem2
        exact ⟨j, hj, by rw [← hA_self j hj, hjn]; exact hA2e⟩

end HSC.CertPP
