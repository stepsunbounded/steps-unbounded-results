import StepsUnboundedResults.HSC.CertPPSixTraceA

open scoped BigOperators
open Finset

namespace HSC.CertPP

variable {G : Type*} [Group G] [Fintype G]

theorem sum_card_filter_mem {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : ι → Finset α) (A : Finset α) :
    ∑ x ∈ A, (s.filter (fun i => x ∈ T i)).card = ∑ i ∈ s, (T i ∩ A).card := by
  classical
  have h1 : ∀ x ∈ A, (s.filter (fun i => x ∈ T i)).card
      = ∑ i ∈ s, if x ∈ T i then 1 else 0 := by
    intro x _; rw [Finset.card_filter]
  have h2 : ∀ i ∈ s, (T i ∩ A).card = ∑ x ∈ A, if x ∈ T i then 1 else 0 := by
    intro i _
    rw [← Finset.inter_comm A (T i), ← Finset.filter_mem_eq_inter (s := A), Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2]

theorem trace_packing {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (D : ι → Finset α) (A : Finset α)
    (hcover : ∀ x ∈ A, ∃ i ∈ s, x ∈ D i) :
    2 * ((∑ i ∈ s, (D i ∩ A).card) - A.card)
      ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, (D i ∩ D j).card := by
  classical
  set c : α → ℕ := fun x => (s.filter (fun i => x ∈ D i)).card with hc
  have hcx : ∀ x ∈ A, 1 ≤ c x := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcover x hx
    rw [hc]
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩
  have hcard_sum : ∑ x ∈ A, c x = ∑ i ∈ s, (D i ∩ A).card := by
    rw [hc]; exact sum_card_filter_mem s D A
  have hcard_sub : ∑ x ∈ A, (c x - 1) = (∑ x ∈ A, c x) - A.card := by
    have h : ∑ x ∈ A, (c x - 1) + A.card = ∑ x ∈ A, c x := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x hx => by have := hcx x hx; omega)
    omega
  have hstep : 2 * (∑ x ∈ A, (c x - 1)) ≤ ∑ x ∈ A, c x * (c x - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x hx => ?_)
    rcases Nat.lt_or_ge (c x) 2 with h | h
    · have hc1 : c x = 1 := by have := hcx x hx; omega
      rw [hc1]; norm_num
    · exact Nat.mul_le_mul_right _ h
  have hpair : ∑ x ∈ A, c x * (c x - 1)
      = ∑ i ∈ s, ∑ j ∈ s.erase i, (D i ∩ D j ∩ A).card := by
    have hstep1 : ∀ x ∈ A, c x * (c x - 1)
        = ∑ i ∈ s.filter (fun i => x ∈ D i), (c x - 1) := by
      intro x _
      simp only [hc, Finset.sum_const, smul_eq_mul]
    rw [Finset.sum_congr rfl hstep1]
    have hstep2 : ∀ x ∈ A, (∑ i ∈ s.filter (fun i => x ∈ D i), (c x - 1))
        = ∑ i ∈ s, if x ∈ D i then (c x - 1) else 0 := by
      intro x _
      rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl hstep2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hinner : ∀ x ∈ A, (if x ∈ D i then (c x - 1) else 0)
        = ∑ j ∈ s.erase i, if x ∈ D i ∧ x ∈ D j then 1 else 0 := by
      intro x _
      by_cases hxi : x ∈ D i
      · have herase : (s.filter (fun j => x ∈ D j)).erase i
            = (s.erase i).filter (fun j => x ∈ D j) := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_filter]
          tauto
        have hcf : c x - 1 = ((s.erase i).filter (fun j => x ∈ D j)).card := by
          simp only [hc]
          rw [← herase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hi, hxi⟩)]
        rw [if_pos hxi, hcf, Finset.card_filter]
        exact Finset.sum_congr rfl (fun j _ => by simp [hxi])
      · rw [if_neg hxi]
        exact (Finset.sum_eq_zero (fun j _ => by simp [hxi])).symm
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have : (D i ∩ D j ∩ A).card = ∑ x ∈ A, if x ∈ D i ∧ x ∈ D j then 1 else 0 := by
      have h1 : D i ∩ D j ∩ A = A.filter (fun x => x ∈ D i ∧ x ∈ D j) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_filter]
        tauto
      rw [h1, Finset.card_filter]
    rw [this]
  calc 2 * ((∑ i ∈ s, (D i ∩ A).card) - A.card)
      = 2 * (∑ x ∈ A, (c x - 1)) := by rw [hcard_sub, hcard_sum]
    _ ≤ ∑ x ∈ A, c x * (c x - 1) := hstep
    _ = ∑ i ∈ s, ∑ j ∈ s.erase i, (D i ∩ D j ∩ A).card := hpair
    _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase i, (D i ∩ D j).card :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          Finset.card_le_card (fun x hx => (Finset.mem_inter.mp hx).1)))

theorem sum_erase_eq_two_nsmul_sum_filter_lt {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [AddCommMonoid M] (s : Finset ι) (f : ι → ι → M)
    (hsymm : ∀ i j, f i j = f j i) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, f i j = 2 • ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), f i j := by
  classical
  have hsplit : ∀ i, s.erase i = (s.filter (fun j => j < i)) ∪ (s.filter (fun j => i < j)) := by
    intro i
    ext j
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hj⟩
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inl ⟨hj, h⟩
      · exact absurd h hne
      · exact Or.inr ⟨hj, h⟩
    · rintro (⟨hj, h⟩ | ⟨hj, h⟩)
      · exact ⟨ne_of_lt h, hj⟩
      · exact ⟨ne_of_gt h, hj⟩
  have hdisj : ∀ i, Disjoint (s.filter (fun j => j < i)) (s.filter (fun j => i < j)) := by
    intro i
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_filter] at hj hj'
    exact absurd hj'.2 (not_lt.mpr hj.2.le)
  have hx : ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f i j
      = ∑ p ∈ (s.product s).filter (fun p => p.2 < p.1), f p.1 p.2 := by
    rw [show (∑ p ∈ (s.product s).filter (fun p => p.2 < p.1), f p.1 p.2)
        = ∑ p ∈ (s ×ˢ s).filter (fun p => p.2 < p.1), f p.1 p.2 from rfl]
    rw [show (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f i j)
        = ∑ p ∈ (s ×ˢ s).filter (fun p => p.2 < p.1), f p.1 p.2 from by
      rw [Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_filter _ _)]
  have hy : ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), f i j
      = ∑ p ∈ (s.product s).filter (fun p => p.1 < p.2), f p.1 p.2 := by
    rw [show (∑ p ∈ (s.product s).filter (fun p => p.1 < p.2), f p.1 p.2)
        = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), f p.1 p.2 from rfl]
    rw [show (∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), f i j)
        = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), f p.1 p.2 from by
      rw [Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_filter _ _)]
  have hswap : ∑ p ∈ (s.product s).filter (fun p => p.1 < p.2), f p.1 p.2
      = ∑ p ∈ (s.product s).filter (fun p => p.2 < p.1), f p.1 p.2 := by
    refine Finset.sum_nbij (fun p : ι × ι => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp2, hp1⟩, hp.2⟩
    · intro p _ q _ hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_filter] at hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq.1
      exact ⟨(q.2, q.1), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hq2, hq1⟩, hq.2⟩, rfl⟩
    · intro p _
      exact (hsymm p.2 p.1).symm
  have hxy : (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f i j)
      = ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), f i j := hx.trans (hswap.symm.trans hy.symm)
  calc ∑ i ∈ s, ∑ j ∈ s.erase i, f i j
      = ∑ i ∈ s, ((∑ j ∈ s.filter (fun j => j < i), f i j)
          + (∑ j ∈ s.filter (fun j => i < j), f i j)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hsplit i, Finset.sum_union (hdisj i)]
    _ = (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f i j)
          + ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), f i j := Finset.sum_add_distrib
    _ = 2 • ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), f i j := by rw [two_nsmul, hxy]

theorem trace_packing_pairwise {ι α : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [DecidableEq α] (s : Finset ι) (D : ι → Finset α) (A : Finset α)
    (hcover : ∀ x ∈ A, ∃ i ∈ s, x ∈ D i) :
    (∑ i ∈ s, (D i ∩ A).card) - A.card
      ≤ ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), (D i ∩ D j).card := by
  classical
  have h1 := trace_packing s D A hcover
  have h2 : ∑ i ∈ s, ∑ j ∈ s.erase i, (D i ∩ D j).card
      = 2 * ∑ i ∈ s, ∑ j ∈ s.filter (fun j => i < j), (D i ∩ D j).card := by
    rw [sum_erase_eq_two_nsmul_sum_filter_lt s (fun i j => (D i ∩ D j).card)
      (fun i j => by rw [Finset.inter_comm]), two_nsmul, two_mul]
  rw [h2] at h1
  omega

theorem lcoset_eq_image' (L : Subgroup G) (z : G) :
    lcoset L z = (fun k : G => z * k) '' (L : Set G) := by
  ext g
  constructor
  · intro hg
    exact ⟨z⁻¹ * g, hg, by group⟩
  · rintro ⟨k, hk, rfl⟩
    simpa [mem_lcoset] using hk

theorem trace_eq_image' {K H : Subgroup G} {x z : G} (hz : z ∈ lcoset K x ∩ (H : Set G)) :
    lcoset K x ∩ (H : Set G) = (fun k : G => z * k) '' ((K ⊓ H : Subgroup G) : Set G) := by
  refine Set.Subset.antisymm (trace_subset_image hz) ?_
  rintro g ⟨k, hk, rfl⟩
  refine ⟨?_, H.mul_mem hz.2 hk.2⟩
  rw [mem_lcoset]
  have h1 : x⁻¹ * (z * k) = (x⁻¹ * z) * k := by group
  rw [h1]
  exact K.mul_mem hz.1 hk.1

theorem order_six_lcoset_inter_eq_one (H P J : Subgroup G) (hH : Nat.card H = 6)
    (hPH : P ≤ H) (hP : Nat.card P = 3) (hJH : J ≤ H) (hJ : Nat.card J = 2)
    {z : G} (hz : z ∈ H) :
    (lcoset J z ∩ (P : Set G)).ncard = 1 := by
  classical
  have hbot : P ⊓ J = ⊥ := by
    have hpos : 0 < Nat.card (P ⊓ J : Subgroup G) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨1, (P ⊓ J).one_mem⟩⟩
    have h1 : Nat.card (P ⊓ J : Subgroup G) ∣ 3 := by
      rw [← hP]; exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (P ⊓ J : Subgroup G) ∣ 2 := by
      rw [← hJ]; exact Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card (P ⊓ J : Subgroup G) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 3 2 = 1 := by norm_num
    rw [h4] at h3
    exact Subgroup.card_eq_one.mp (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h3) hpos)
  have hP' : Nat.card (P.subgroupOf H) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hP]
  have hJ' : Nat.card (J.subgroupOf H) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv, hJ]
  have hcomp : (P.subgroupOf H).IsComplement' (J.subgroupOf H) := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hP', hJ', hH]
    · rw [hP', hJ']; norm_num
  obtain ⟨⟨p, l⟩, hpl, -⟩ := hcomp.existsUnique ⟨z, hz⟩
  have hpP : ((p : H) : G) ∈ P := Subgroup.mem_subgroupOf.mp p.2
  have hlJ : ((l : H) : G) ∈ J := Subgroup.mem_subgroupOf.mp l.2
  have hz_eq : ((p : H) : G) * ((l : H) : G) = z := by
    have := congrArg (fun t : H => (t : G)) hpl
    simpa using this
  have hz_mem : z ∈ lcoset J ((p : H) : G) := by
    rw [mem_lcoset]
    have : ((p : H) : G)⁻¹ * z = ((l : H) : G) := by rw [← hz_eq]; group
    rw [this]
    exact hlJ
  have hset : lcoset J ((p : H) : G) ∩ (P : Set G) = {((p : H) : G)} := by
    ext w
    constructor
    · rintro ⟨hw, hwP⟩
      rw [mem_lcoset] at hw
      have hmem : ((p : H) : G)⁻¹ * w ∈ P ⊓ J :=
        ⟨P.mul_mem (P.inv_mem hpP) hwP, hw⟩
      rw [hbot] at hmem
      have h1 : ((p : H) : G)⁻¹ * w = 1 := Subgroup.mem_bot.mp hmem
      rw [Set.mem_singleton_iff]
      calc w = ((p : H) : G) * (((p : H) : G)⁻¹ * w) := by group
        _ = ((p : H) : G) := by rw [h1, mul_one]
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      refine ⟨?_, ?_⟩
      · rw [mem_lcoset, hw]; simp
      · rw [hw]; exact hpP
  have hfinal : lcoset J ((p : H) : G) = lcoset J z := lcoset_eq_of_mem hz_mem
  rw [← hfinal, hset, Set.ncard_singleton]

end HSC.CertPP
