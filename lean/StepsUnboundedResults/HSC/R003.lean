/-
HSC/R003.lean

Result R003 (Steps Unbounded), "Every Direct Power of A₅ Satisfies the Herzog–Schönheim
Conjecture".
-/
import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Extension
import StepsUnboundedResults.HSC.Assembly
import StepsUnboundedResults.HSC.Products
import StepsUnboundedResults.HSC.CompFactors
import StepsUnboundedResults.HSC.A5Index
import StepsUnboundedResults.HSC.A5Monoid
import Mathlib.Tactic

open scoped Classical

namespace HSC

inductive CompFactorsIn (P : (G : Type) → [Group G] → [Finite G] → Prop) :
    (G : Type) → [Group G] → [Finite G] → Prop
  | trivial (G : Type) [Group G] [Finite G] [Subsingleton G] : CompFactorsIn P G
  | base (G : Type) [Group G] [Finite G] (h : P G) : CompFactorsIn P G
  | ext (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal] (h : P (G ⧸ N)) :
      CompFactorsIn P ↥N → CompFactorsIn P G

theorem P_of_compFactorsIn {P : (G : Type) → [Group G] → [Finite G] → Prop}
    (hP1 : ∀ (G : Type) [Group G] [Finite G] [Subsingleton G], P G)
    (hPext : ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal],
      P ↥N → P (G ⧸ N) → P G) :
    ∀ {G : Type} [Group G] [Finite G], CompFactorsIn P G → P G := by
  intro G _ _ h
  induction h with
  | trivial G => exact hP1 G
  | base G h => exact h
  | ext G N hQ hrec ih => exact hPext G N ih hQ

theorem indexSet_subset_monoidGen_of_compFactorsIn {A : Finset ℕ}
    {G : Type} [Group G] [Finite G]
    (h : CompFactorsIn (fun G _ _ => ∀ n ∈ indexSet G, n ∈ MonoidGen A) G) :
    ∀ n ∈ indexSet G, n ∈ MonoidGen A := by
  refine P_of_compFactorsIn (P := fun G _ _ => ∀ n ∈ indexSet G, n ∈ MonoidGen A) ?_ ?_ h
  · intro G _ _ _ n hn
    obtain ⟨-, H, rfl⟩ := mem_indexSet.mp hn
    have htop : H = ⊤ := by
      refine top_le_iff.mp ?_
      intro x _
      rw [Subsingleton.elim x 1]
      exact H.one_mem
    rw [htop, Subgroup.index_top]
    exact one_mem_MonoidGen A
  · intro G _ _ N _ hN hQ n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := index_mem_mul_indexSet N n hn
    exact MonoidGen.mul_mem (hQ a ha) (hN b hb)

theorem isHS_of_compFactorsIn {A : Finset ℕ} {c : ℚ} (hMass : MassBound A c) (hc : c < 1)
    {G : Type} [Group G] [Finite G]
    (h : CompFactorsIn (fun G _ _ => ∀ n ∈ indexSet G, n ∈ MonoidGen A) G) : IsHS G :=
  isHS_of_indexSet_subset (indexSet_subset_monoidGen_of_compFactorsIn h) hMass hc

theorem eq_one_or_eq_of_mem_indexSet_of_card_prime {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card Q = p) {n : ℕ} (hn : n ∈ indexSet Q) : n = 1 ∨ n = p := by
  obtain ⟨hdvd, -⟩ := mem_indexSet.mp hn
  rw [hcard] at hdvd
  exact (Nat.dvd_prime hp).mp hdvd

abbrev C5 : Type := Multiplicative (ZMod 5)

theorem nat_card_C5 : Nat.card C5 = 5 := by
  show Nat.card (ZMod 5) = 5
  simp

theorem indexSet_C5_subset : ∀ n ∈ indexSet C5, n ∈ MonoidGen a5IndexSet := by
  intro n hn
  rcases eq_one_or_eq_of_mem_indexSet_of_card_prime (by norm_num) nat_card_C5 hn with h | h
  · rw [h]
    exact one_mem_MonoidGen a5IndexSet
  · rw [h]
    exact subset_MonoidGen (by simp [a5IndexSet])

theorem indexSet_pow_Alt5_subset :
    ∀ r, ∀ n ∈ indexSet (pow Alt5 r), n ∈ MonoidGen a5IndexSet := fun r =>
  indexSet_pow_subset Alt5 (fun n hn => subset_MonoidGen (a5_indexSet_subset n hn)) r

theorem indexSet_pow_C5_subset :
    ∀ r, ∀ n ∈ indexSet (pow C5 r), n ∈ MonoidGen a5IndexSet :=
  indexSet_pow_subset C5 indexSet_C5_subset

theorem indexSet_pow_Alt5_prod_pow_C5_subset (r s : ℕ) :
    ∀ n ∈ indexSet (pow Alt5 r × pow C5 s), n ∈ MonoidGen a5IndexSet := by
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := indexSet_prod_subset n hn
  exact MonoidGen.mul_mem (indexSet_pow_Alt5_subset r a ha) (indexSet_pow_C5_subset s b hb)

theorem isHS_pow_Alt5_prod_pow_C5 (r s : ℕ) : IsHS (pow Alt5 r × pow C5 s) :=
  isHS_of_indexSet_subset (indexSet_pow_Alt5_prod_pow_C5_subset r s) massBound_a5IndexSet
    (by norm_num)

theorem isHS_of_compFactors_C5 {G : Type} [Group G] [Finite G] (h : CompFactorsIso C5 G) :
    IsHS G :=
  isHS_of_compFactors (A := a5IndexSet) indexSet_C5_subset massBound_a5IndexSet (by norm_num) h

theorem isHS_quotient {G : Type} [Group G] (N : Subgroup G) [N.Normal] (h : IsHS G) :
    IsHS (G ⧸ N) := by
  classical
  intro P
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  let H' : P.ι → Subgroup G := fun i => (P.H i).comap π
  let x' : P.ι → G := fun i => Classical.choose (hπ (P.x i))
  have hx' : ∀ i, π (x' i) = P.x i := fun i => Classical.choose_spec (hπ (P.x i))
  have hpre : ∀ i, leftCoset (x' i) (H' i) = π ⁻¹' (leftCoset (P.x i) (P.H i)) := by
    intro i
    ext g
    show (x' i)⁻¹ * g ∈ (P.H i).comap π ↔ (P.x i)⁻¹ * π g ∈ P.H i
    rw [Subgroup.mem_comap, map_mul, map_inv, hx' i]
  have hindex' : ∀ i, (H' i).index = (P.H i).index := fun i =>
    Subgroup.index_comap_of_surjective (P.H i) hπ
  let P' : CosetPartition G :=
    { ι := P.ι
      fintype := inferInstance
      H := H'
      x := x'
      proper := fun i htop => by
        have h1 : (P.H i).index = 1 := by rw [← hindex' i, htop, Subgroup.index_top]
        exact P.proper i (Subgroup.index_eq_one.mp h1)
      two_le := P.two_le
      cover := fun g => by
        obtain ⟨i, hi⟩ := P.cover (π g)
        exact ⟨i, by rw [hpre i]; exact hi⟩
      disjoint := fun i j hij => by
        rw [hpre i, hpre j]
        exact (P.disjoint i j hij).preimage π }
  obtain ⟨i, j, hij, heq⟩ := h P'
  exact ⟨i, j, hij, by rw [← hindex' i, heq, hindex' j]⟩

theorem isHS_quotient_pow_Alt5_prod_pow_C5 (r s : ℕ)
    (N : Subgroup (pow Alt5 r × pow C5 s)) [N.Normal] :
    IsHS ((pow Alt5 r × pow C5 s) ⧸ N) :=
  isHS_quotient N (isHS_pow_Alt5_prod_pow_C5 r s)

end HSC
