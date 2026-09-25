import StepsUnboundedResults.HSC.CertPP12Util

open scoped Classical
open Finset

namespace HSC
namespace CertPP12

structure Anchored (ι : Type*) [Fintype ι] [DecidableEq ι] where
  anchor : ι
  sz : ι → ℕ
  point : ι → Finset (Fin 60)
  H : Finset (Fin 60)
  sz_anchor : sz anchor = 12
  sz_mem : ∀ i, sz i ∈ allSizes
  sz_injective : Function.Injective sz
  card_point : ∀ i, (point i).card = sz i
  point_anchor : point anchor = H
  card_H : H.card = 12
  cover : ∀ p : Fin 60, 2 ≤ (univ.filter fun i => p ∈ point i).card ∨ ∀ i, p ∉ point i
  trace_table : ∀ i, (point i ∩ H).card ∈ attainableTraces (sz i)
  pair_cap : ∀ i j, i ≠ j → ((point i \ H) ∩ (point j \ H)).card ≤
    min (sz i - (point i ∩ H).card) (min (sz j - (point j ∩ H).card) (pairCap (sz i) (sz j)))
  lemma41 : ∀ i j, sz i = 3 → sz j = 4 → (point i ∩ H).card = 3 → (point j ∩ H).card = 4 →
    ((point i ∩ H) ∩ (point j ∩ H)).card = 1
  lemma42 : ∀ i j, sz i = 5 → sz j = 10 → Disjoint (point i ∩ H) (point j ∩ H) →
    ((point i \ H) ∩ (point j \ H)).card ≤ 1
  lemma43 : ∀ i j, sz i = 6 → (point i ∩ H).card = 3 → sz j = 10 →
    ((point i \ H) ∩ (point j \ H)).card ≤ 1

namespace Anchored

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def trace (S : Anchored ι) (i : ι) : Finset (Fin 60) := S.point i ∩ S.H
def out (S : Anchored ι) (i j : ι) : Finset (Fin 60) := (S.point i \ S.H) ∩ (S.point j \ S.H)

@[simp] theorem trace_def (S : Anchored ι) (i : ι) : S.trace i = S.point i ∩ S.H := rfl
@[simp] theorem out_def (S : Anchored ι) (i j : ι) :
    S.out i j = (S.point i \ S.H) ∩ (S.point j \ S.H) := rfl

def b (S : Anchored ι) (i : ι) : ℕ := (S.point i \ S.H).card
def dval (S : Anchored ι) (i : ι) : ℕ := traceCap (S.sz i) - (S.trace i).card
def sizeSet (S : Anchored ι) : Finset ℕ := (univ.erase S.anchor).image S.sz
noncomputable def invOf (S : Anchored ι) (m : ℕ) : ι :=
  @Function.invFun ι ℕ ⟨S.anchor⟩ S.sz m
noncomputable def dOf (S : Anchored ι) : DefTuple S.sizeSet :=
  fun n => traceCap n.val - (S.trace (S.invOf n.val)).card

theorem sz_mem_lower (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) : S.sz i ∈ lowerSizes := by
  have h := S.sz_mem i
  rw [allSizes, Finset.mem_insert] at h
  rcases h with h | h
  · exact absurd (S.sz_injective (by rw [h, S.sz_anchor])) hi
  · exact h

theorem sz_ne_twelve (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) : S.sz i ≠ 12 :=
  fun h => hi (S.sz_injective (by rw [h, S.sz_anchor]))

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

theorem trace_subset (S : Anchored ι) (i : ι) : S.trace i ⊆ S.H := Finset.inter_subset_right

theorem trace_card_le (S : Anchored ι) (i : ι) : (S.trace i).card ≤ traceCap (S.sz i) := by
  have h := S.trace_table i
  rw [attainableTraces, Finset.mem_image] at h
  obtain ⟨d, hd, hdval⟩ := h
  have := deficiencies_le_traceCap (S.sz i) (S.sz_mem i) d hd
  simp only [trace]
  omega

theorem b_eq (S : Anchored ι) (i : ι) : S.b i = S.sz i - (S.trace i).card := by
  rw [b, Finset.card_sdiff, S.card_point, Finset.inter_comm]
  rfl

theorem sz_invOf (S : Anchored ι) {m : ℕ} (hm : m ∈ S.sizeSet) : S.sz (S.invOf m) = m := by
  obtain ⟨i, _, hsz⟩ := (mem_sizeSet_iff S).mp hm
  exact @Function.invFun_eq ι ℕ ⟨S.anchor⟩ S.sz m ⟨i, hsz⟩

theorem dOf_apply (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) :
    S.dOf ⟨S.sz i, (mem_sizeSet_iff S).mpr ⟨i, hi, rfl⟩⟩ = S.dval i := by
  have h : S.invOf (S.sz i) = i :=
    S.sz_injective (sz_invOf S ((mem_sizeSet_iff S).mpr ⟨i, hi, rfl⟩))
  simp only [dOf, dval, trace, h]

theorem dval_mem (S : Anchored ι) (i : ι) : S.dval i ∈ deficiencies (S.sz i) := by
  have hm : S.sz i ∈ allSizes := S.sz_mem i
  have h := S.trace_table i
  rw [attainableTraces, Finset.mem_image] at h
  obtain ⟨d, hd, hdval⟩ := h
  rw [dval, trace, ← hdval, traceCap_sub_traceCap_sub (S.sz i) hm d hd]
  exact hd

theorem b_eq_bval (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) :
    S.b i = bval S.dOf (S.sz i) := by
  have hmem : S.sz i ∈ S.sizeSet := (mem_sizeSet_iff S).mpr ⟨i, hi, rfl⟩
  have hd : toFun S.dOf (S.sz i) = S.dval i := by
    rw [toFun, dif_pos hmem]
    exact dOf_apply S hi
  have hle : (S.trace i).card ≤ traceCap (S.sz i) := trace_card_le S i
  have hle' : traceCap (S.sz i) ≤ S.sz i := traceCap_le_self (S.sz i) (S.sz_mem i)
  simp only [b_eq, bval, hd, dval]
  omega

theorem trace_card_eq_of_sz (S : Anchored ι) {i : ι} {m k : ℕ} (hm : S.sz i = m)
    (hk : attainableTraces m = {k}) : (S.trace i).card = k := by
  have h := S.trace_table i
  rw [hm, hk] at h
  simpa only [trace, Finset.mem_singleton] using h

theorem b_of_sz_five (S : Anchored ι) {i : ι} (h : S.sz i = 5) : S.b i = 4 := by
  have hc := trace_card_eq_of_sz S h attainableTraces_five
  rw [b_eq, h, hc]

theorem b_of_sz_ten (S : Anchored ι) {i : ι} (h : S.sz i = 10) : S.b i = 8 := by
  have hc := trace_card_eq_of_sz S h attainableTraces_ten
  rw [b_eq, h, hc]

end Anchored
end CertPP12
end HSC
