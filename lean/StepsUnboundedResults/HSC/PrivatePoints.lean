import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Criterion
import StepsUnboundedResults.HSC.Lifting

open scoped Classical
open Finset

namespace HSC

def HasPrivatePoint {ι : Type*} {G : Type*} (D : ι → Set G) (i : ι) : Prop :=
  ∃ x : G, x ∈ D i ∧ ∀ j : ι, j ≠ i → x ∉ D j

theorem hasPrivatePoint_leftCoset {ι : Type*} {G : Type*} [Group G] (c : ι → G)
    (H : ι → Subgroup G) (i : ι) :
    HasPrivatePoint (fun i => leftCoset (c i) (H i)) i ↔
      ∃ x : G, x ∈ leftCoset (c i) (H i) ∧ ∀ j : ι, j ≠ i → x ∉ leftCoset (c j) (H j) :=
  Iff.rfl

def PP (G : Type*) [Group G] : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → G) (H : ι → Subgroup G),
    Nonempty ι →
    (∀ i j, i ≠ j → leftCoset (c i) (H i) ≠ leftCoset (c j) (H j)) →
    (∀ i j, i ≠ j → (H i).index ≠ (H j).index) →
    ∃ i, HasPrivatePoint (fun i => leftCoset (c i) (H i)) i

theorem option_extension_distinct {G : Type*} [Group G] (P : CosetPartition G)
    (hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index) :
    (∀ o o' : Option P.ι, o ≠ o' →
      leftCoset (o.elim 1 P.x) (o.elim ⊤ P.H) ≠
        leftCoset (o'.elim 1 P.x) (o'.elim ⊤ P.H)) ∧
    (∀ o o' : Option P.ι, o ≠ o' →
      (o.elim ⊤ P.H).index ≠ (o'.elim ⊤ P.H).index) := by
  classical
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
  constructor
  · intro o o' hne hEq
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
        simp at h2
  · intro o o' hne
    change (H o).index ≠ (H o').index
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

theorem isHS_of_PP {G : Type*} [Group G] (h : PP G) : IsHS G := by
  classical
  intro P
  by_contra hcon
  push_neg at hcon
  have hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index :=
    fun i j hij hh => hcon i j hij hh
  obtain ⟨hcoset, hidx⟩ := option_extension_distinct P hdist
  have hnon : Nonempty (Option P.ι) := ⟨none⟩
  obtain ⟨o, x, hxmem, hxnot⟩ :=
    h (Option P.ι) (fun o => o.elim 1 P.x) (fun o => o.elim ⊤ P.H) hnon hcoset hidx
  rcases o with _ | i
  · obtain ⟨j, hxj⟩ := P.cover x
    exact hxnot (some j) (by simp) hxj
  · refine hxnot none (by simp) ?_
    show x ∈ leftCoset (1 : G) (⊤ : Subgroup G)
    rw [leftCoset_one_top]
    trivial

def HpUnguarded (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → G) (H : ι → Subgroup G),
    Nonempty ι →
    (∀ i j, i ≠ j → leftCoset (c i) (H i) ≠ leftCoset (c j) (H j)) →
    (∀ i j, i ≠ j → (H i).index ≠ (H j).index) →
    (∑ i : ι, (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) ≠ 0

def Hp (p : ℕ) (G : Type*) [Group G] : Prop :=
  (1 : ZMod p) ≠ 0 → HpUnguarded p G

theorem HpUnguarded_of_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (h : Hp p G) :
    HpUnguarded p G :=
  h (fun h1 => hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h1)))

theorem not_HpUnguarded_one : ¬ HpUnguarded 1 (Multiplicative (ZMod 2)) := by
  intro h
  refine h Unit (fun _ => 1) (fun _ => ⊤) ⟨()⟩ ?_ ?_ (Subsingleton.elim _ _)
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij

theorem HpUnguarded_of_PP {G : Type*} [Group G] {p : ℕ} (h : PP G)
    (hp1 : (1 : ZMod p) ≠ 0) : HpUnguarded p G := by
  classical
  intro ι _ c H hne hcoset hidx hsum
  obtain ⟨i₀, x, hxmem, hxnot⟩ := h ι c H hne hcoset hidx
  have hx := congrFun hsum x
  rw [Finset.sum_apply] at hx
  have hsingle : (∑ i : ι, (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p)) x) = 1 := by
    rw [Finset.sum_eq_single i₀]
    · rw [Set.indicator_of_mem hxmem]
    · intro i _ hi
      rw [Set.indicator_of_notMem (hxnot i hi)]
    · intro hmem
      exact absurd (Finset.mem_univ i₀) hmem
  rw [hsingle] at hx
  exact hp1 hx

theorem Hp_of_PP {G : Type*} [Group G] (h : PP G) : Hp p G :=
  HpUnguarded_of_PP h

theorem HpUnguarded_of_licosets {G : Type*} [Group G] {p : ℕ} (h : LICosets p G)
    (hp1 : (1 : ZMod p) ≠ 0) : HpUnguarded p G := by
  classical
  intro ι _ c H hne hcoset hidx hsum
  have hLI := h ι c H hcoset hidx
  have hrel : (∑ i : ι, (1 : ZMod p) •
      (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) = 0 := by
    exact (Finset.sum_congr rfl fun i _ => one_smul (ZMod p) _).trans hsum
  have hg := (Fintype.linearIndependent_iff.mp hLI) (fun _ : ι => (1 : ZMod p)) hrel
  obtain ⟨i⟩ := hne
  exact hp1 (hg i)

theorem Hp_of_licosets {G : Type*} [Group G] (h : LICosets p G) : Hp p G :=
  HpUnguarded_of_licosets h

end HSC
