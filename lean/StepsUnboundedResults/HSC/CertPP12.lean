/-
HSC/CertPP12.lean

The `S = 12` anchor of `Cert-PP(A₅)` — the last finite input of **R004** — formalized after the
written argument recorded in `results/R004-cert-pp.md`, whose finite inputs are machine-checked by
`verify/R004-cert-pp.py`.

## What is encoded

`H ≤ A₅` is a fixed subgroup of order `12` (`H ≅ A₄`), the *anchor*.  A **family** for the anchor is
a finite set of left cosets of `A₅` of size `≤ 12` containing `H`; it is *admissible* when

* no two members have the same size (`sz_injective`, the "at most one per size" constraint,
  `∑_{|D| = m} x_D ≤ 1`), and
* no point of `A₅` is covered exactly once (`cover`: every point is covered `0` or `≥ 2` times,
  `2u_g ≤ ∑_{D ∋ g} x_D`).

`HSC.CertPP12.Anchored` is that system, encoded over an abstract finite index type `ι` of members:
each member `i` carries its size `sz i` and its point set `point i : Finset (Fin 60)` (the `60`
elements of `A₅`), with `point anchor = H`, `(point anchor).card = 12`, `(point i).card = sz i`.  The
hypotheses `trace_table`, `pair_cap`, `lemma41`, `lemma42`, `lemma43` are *not* consequences of the
two constraints: they are the finite inputs of the argument, i.e. the facts about `A₅` that
`verify/R004-cert-pp.py` establishes by brute force over the `60` elements and the `1018` cosets of
size `≤ 12`.  Every one of them is stated at the level of the point sets, so it is exactly a
statement about cosets of `A₅`:
* `trace_table`: the attainable trace sizes `|D ∩ H|` are those of the paper's §2 table;
* `pair_cap`: the capacity matrix `c_{mn}` of §3 bounds every outside intersection;
* `lemma41`/`lemma42`/`lemma43`: the three structure lemmas of §4.

## What is kernel-checked here

* the whole finite arithmetic core (§2–§3, §5 of the paper), by `decide`: the twenty size sets
  forced by the cover of `H` (`sizeSets_eq`, `sizeSets_card`), the coarse outside sieve with its
  eighteen universally refuted rows (`sieve_exhaustive`, `sieve_table`, `refuted_card`), the case
  analysis bounding the outside support of the size-`10` member below the eight points it must cover
  (`bound_M_A`, `bound_M_B`, `bound_M_B_eq`), and their combined form `finite_core`;
* the combinatorial reduction from the anchored system to that core: the anchor's `12` points force
  the lower traces to cover `H` (`sizeSum_ge`), the cover constraint forces every outside point of a
  member to be shared with a second member (`b_le_sum_out`), the capacity matrix bounds the outside
  intersections size by size (`sum_out_le_outsideBound`), and the two collision arguments of §5 are
  proved outright: `disjoint_of_sum_card_eq'` (excess `0` partitions `H`, so Lemma 4.2 applies) and
  `no_two_collisions'` (the equality case of `M_B` is impossible: `12 ≤ (3+4-1) + (1+2-1) + 3 = 11`);
* the refutation `no_anchored_system : Anchored ι → False` — for one fixed `H`, no family satisfies
  the anchored system, so `Cert-PP(A₅)` holds at `S = 12`.

## What remains Python-side

The five input fields above (trace table, capacity matrix, Lemmas 4.1–4.3) and the enumerative facts
behind them — `59` subgroups, `1018` cosets, the five conjugate order-`12` subgroups — are checked by
`verify/R004-cert-pp.py`, not here.  The conjugacy reduction of §6 (infeasibility for one `H` gives
it for all five) is not formalized either: `Anchored` is stated for an arbitrary fixed `H` of order
`12`, and the five order-`12` subgroups are conjugate by the Python check.  The capacity matrix is
Python-checked at the level of *subgroup* intersections; its transfer to cosets is the paper's §1
identity `xK ∩ yL = z(K ∩ L)`, also not formalized here.  Nothing else is assumed: in particular the
`decide` proofs assume no solver verdict and no DRAT certificate.
-/
import StepsUnboundedResults.HSC.Defs
import Mathlib.Tactic

open scoped Classical
open Finset

set_option maxRecDepth 100000

namespace HSC
namespace CertPP12

def lowerSizes : Finset ℕ := {1, 2, 3, 4, 5, 6, 10}
def allSizes : Finset ℕ := insert 12 lowerSizes

def traceCap : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 1
  | 6 => 3
  | 10 => 2
  | 12 => 12
  | _ => 0

def deficiencies : ℕ → Finset ℕ
  | 1 => {0, 1}
  | 2 => {0, 1, 2}
  | 3 => {0, 2, 3}
  | 4 => {0, 3, 4}
  | 5 => {0}
  | 6 => {0, 1, 3}
  | 10 => {0}
  | 12 => {0}
  | _ => ∅

def attainableTraces (m : ℕ) : Finset ℕ := (deficiencies m).image (fun d => traceCap m - d)

def pairCap : ℕ → ℕ → ℕ
  | 1, _ => 1
  | _, 1 => 1
  | 2, 2 => 2
  | 2, 3 => 1
  | 2, 4 => 2
  | 2, 5 => 1
  | 2, 6 => 2
  | 2, 10 => 2
  | 3, 2 => 1
  | 3, 3 => 3
  | 3, 4 => 1
  | 3, 5 => 1
  | 3, 6 => 3
  | 3, 10 => 1
  | 4, 2 => 2
  | 4, 3 => 1
  | 4, 4 => 4
  | 4, 5 => 1
  | 4, 6 => 2
  | 4, 10 => 2
  | 5, 2 => 1
  | 5, 3 => 1
  | 5, 4 => 1
  | 5, 5 => 5
  | 5, 6 => 1
  | 5, 10 => 5
  | 6, 2 => 2
  | 6, 3 => 3
  | 6, 4 => 2
  | 6, 5 => 1
  | 6, 6 => 6
  | 6, 10 => 2
  | 10, 2 => 2
  | 10, 3 => 1
  | 10, 4 => 2
  | 10, 5 => 5
  | 10, 6 => 2
  | 10, 10 => 10
  | _, _ => 0

def M_A : Finset ℕ := {2, 3, 4, 5, 6, 10}
def M_B : Finset ℕ := {1, 2, 3, 4, 5, 6, 10}
def sizeSum (M : Finset ℕ) : ℕ := ∑ m ∈ M, traceCap m
def slack (M : Finset ℕ) : ℕ := sizeSum M - 12
def sizeSets : Finset (Finset ℕ) := lowerSizes.powerset.filter (fun M => 12 ≤ sizeSum M)
abbrev DefTuple (M : Finset ℕ) := {m // m ∈ M} → ℕ
def tuples (M : Finset ℕ) : Finset (DefTuple M) :=
  Fintype.piFinset (fun m : {m // m ∈ M} => deficiencies m.val)
def toFun {M : Finset ℕ} (d : DefTuple M) : ℕ → ℕ :=
  fun m => if h : m ∈ M then d ⟨m, h⟩ else 0
def delta {M : Finset ℕ} (d : DefTuple M) : ℕ := ∑ m ∈ M, toFun d m
def admissible {M : Finset ℕ} (d : DefTuple M) : Prop := delta d ≤ slack M
instance {M : Finset ℕ} (d : DefTuple M) : Decidable (admissible d) := by
  unfold admissible delta; infer_instance
def excess {M : Finset ℕ} (d : DefTuple M) : ℕ := slack M - delta d
def bval {M : Finset ℕ} (d : DefTuple M) (m : ℕ) : ℕ := m - traceCap m + toFun d m
def rhs {M : Finset ℕ} (d : DefTuple M) (m : ℕ) : ℕ :=
  ∑ n ∈ M.erase m, min (bval d m) (min (bval d n) (pairCap m n))
def sizeContrib {M : Finset ℕ} (d : DefTuple M) (n : ℕ) : ℕ :=
  if n = 1 then toFun d 1
  else if n = 2 then toFun d 2
  else if n = 3 then min (toFun d 3) 1
  else if n = 4 then min (toFun d 4) 2
  else if n = 5 then (if slack M - delta d = 0 then 1 else 4)
  else if n = 6 then 1 + toFun d 6
  else 0
def outsideBound {M : Finset ℕ} (d : DefTuple M) : ℕ := ∑ n ∈ M.erase 10, sizeContrib d n

theorem trace_table :
    attainableTraces 1 = {0, 1} ∧ attainableTraces 2 = {0, 1, 2} ∧ attainableTraces 3 = {0, 1, 3} ∧
      attainableTraces 4 = {0, 1, 4} ∧ attainableTraces 5 = {1} ∧ attainableTraces 6 = {0, 2, 3} ∧
      attainableTraces 10 = {2} ∧ attainableTraces 12 = {12} := by decide
@[simp] theorem traceCap_one : traceCap 1 = 1 := by decide
@[simp] theorem traceCap_two : traceCap 2 = 2 := by decide
@[simp] theorem traceCap_three : traceCap 3 = 3 := by decide
@[simp] theorem traceCap_four : traceCap 4 = 4 := by decide
@[simp] theorem traceCap_five : traceCap 5 = 1 := by decide
@[simp] theorem traceCap_six : traceCap 6 = 3 := by decide
@[simp] theorem traceCap_ten : traceCap 10 = 2 := by decide
@[simp] theorem attainableTraces_one : attainableTraces 1 = {0, 1} := by decide
@[simp] theorem attainableTraces_two : attainableTraces 2 = {0, 1, 2} := by decide
@[simp] theorem attainableTraces_three : attainableTraces 3 = {0, 1, 3} := by decide
@[simp] theorem attainableTraces_four : attainableTraces 4 = {0, 1, 4} := by decide
@[simp] theorem attainableTraces_five : attainableTraces 5 = {1} := by decide
@[simp] theorem attainableTraces_six : attainableTraces 6 = {0, 2, 3} := by decide
@[simp] theorem attainableTraces_ten : attainableTraces 10 = {2} := by decide
@[simp] theorem attainableTraces_twelve : attainableTraces 12 = {12} := by decide
theorem traceCap_le_self : ∀ m ∈ allSizes, traceCap m ≤ m := by decide
theorem deficiencies_le_traceCap : ∀ m ∈ allSizes, ∀ d ∈ deficiencies m, d ≤ traceCap m := by decide
theorem traceCap_sub_traceCap_sub :
    ∀ m ∈ allSizes, ∀ d ∈ deficiencies m, traceCap m - (traceCap m - d) = d := by decide
theorem trace_five_ten : traceCap 5 = 1 ∧ traceCap 10 = 2 ∧ traceCap 12 = 12 := by decide
theorem pairCap_ten :
    pairCap 10 1 = 1 ∧ pairCap 10 2 = 2 ∧ pairCap 10 3 = 1 ∧ pairCap 10 4 = 2 ∧
      pairCap 10 5 = 5 ∧ pairCap 10 6 = 2 ∧ pairCap 10 10 = 10 := by decide
@[simp] theorem pairCap_ten_one : pairCap 10 1 = 1 := by decide
@[simp] theorem pairCap_ten_two : pairCap 10 2 = 2 := by decide
@[simp] theorem pairCap_ten_three : pairCap 10 3 = 1 := by decide
@[simp] theorem pairCap_ten_four : pairCap 10 4 = 2 := by decide
@[simp] theorem pairCap_ten_five : pairCap 10 5 = 5 := by decide
@[simp] theorem pairCap_ten_six : pairCap 10 6 = 2 := by decide
theorem pairCap_comm : ∀ m ∈ allSizes, ∀ n ∈ allSizes, pairCap m n = pairCap n m := by decide

theorem sizeSets_eq : sizeSets =
    ({{2, 3, 4, 6}, {1, 2, 3, 4, 6}, {1, 3, 4, 5, 6}, {2, 3, 4, 5, 6}, {1, 2, 3, 4, 5, 6},
      {1, 2, 3, 4, 10}, {2, 3, 4, 5, 10}, {1, 2, 3, 4, 5, 10}, {1, 2, 4, 6, 10}, {3, 4, 6, 10},
      {1, 3, 4, 6, 10}, {2, 3, 4, 6, 10}, {1, 2, 3, 4, 6, 10}, {1, 2, 3, 5, 6, 10},
      {2, 4, 5, 6, 10}, {1, 2, 4, 5, 6, 10}, {3, 4, 5, 6, 10}, {1, 3, 4, 5, 6, 10},
      M_A, M_B} : Finset (Finset ℕ)) := by decide
theorem sizeSets_card : sizeSets.card = 20 := by decide
theorem sieve_exhaustive : ∀ M ∈ sizeSets,
    (∃ m ∈ M, ∀ d ∈ tuples M, admissible d → rhs d m < bval d m) ∨ M = M_A ∨ M = M_B := by decide
theorem sieve_table :
    (∀ d ∈ tuples {2, 3, 4, 6}, admissible d → rhs d 6 < bval d 6) ∧
      (∀ d ∈ tuples {1, 2, 3, 4, 6}, admissible d → rhs d 6 < bval d 6) ∧
      (∀ d ∈ tuples {1, 3, 4, 5, 6}, admissible d → rhs d 5 < bval d 5) ∧
      (∀ d ∈ tuples {2, 3, 4, 5, 6}, admissible d → rhs d 5 < bval d 5) ∧
      (∀ d ∈ tuples {1, 2, 3, 4, 5, 6}, admissible d → rhs d 5 < bval d 5) ∧
      (∀ d ∈ tuples {1, 2, 3, 4, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {2, 3, 4, 5, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {1, 2, 3, 4, 5, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {1, 2, 4, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {3, 4, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {1, 3, 4, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {2, 3, 4, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {1, 2, 3, 4, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {1, 2, 3, 5, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {2, 4, 5, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {1, 2, 4, 5, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {3, 4, 5, 6, 10}, admissible d → rhs d 10 < bval d 10) ∧
      (∀ d ∈ tuples {1, 3, 4, 5, 6, 10}, admissible d → rhs d 10 < bval d 10) := by decide
theorem refuted_card :
    (sizeSets.filter fun M => ∃ m ∈ M, ∀ d ∈ tuples M, admissible d → rhs d m < bval d m).card = 18 := by decide
theorem slack_M_A : slack M_A = 3 := by decide
theorem slack_M_B : slack M_B = 4 := by decide
theorem bound_M_A : ∀ d ∈ tuples M_A, admissible d → outsideBound d < 8 := by decide
theorem bound_M_B : ∀ d ∈ tuples M_B, admissible d → outsideBound d ≤ 8 := by decide
theorem bound_M_B_eq : ∀ d ∈ tuples M_B, admissible d → outsideBound d = 8 →
    toFun d 3 = 0 ∧ toFun d 4 = 0 ∧ delta d = 3 := by decide
theorem finite_core : ∀ M ∈ sizeSets,
    (∃ m ∈ M, ∀ d ∈ tuples M, admissible d → rhs d m < bval d m)
    ∨ (10 ∈ M ∧ ∀ d ∈ tuples M, admissible d → outsideBound d < 8)
    ∨ (M = M_B ∧ 10 ∈ M ∧ ∀ d ∈ tuples M, admissible d →
        outsideBound d ≤ 8 ∧ (outsideBound d = 8 →
          toFun d 3 = 0 ∧ toFun d 4 = 0 ∧ delta d = 3)) := by decide

namespace Util

private lemma biUnion_subset_union_erase_erase {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {s : Finset ι} {T : ι → Finset α} {i j : ι} :
    s.biUnion T ⊆ (T i ∪ T j) ∪ ((s.erase i).erase j).biUnion T := by
  intro q hq
  obtain ⟨k, hk, hkq⟩ := Finset.mem_biUnion.mp hq
  by_cases hki : k = i
  · rw [hki] at hkq
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hkq)))
  · by_cases hkj : k = j
    · rw [hkj] at hkq
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hkq)))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩, hkq⟩))

private lemma biUnion_subset_union_erase_four {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {s : Finset ι} {T : ι → Finset α} {a b c d : ι} :
    s.biUnion T ⊆ (T a ∪ T b ∪ T c ∪ T d) ∪
      ((((s.erase a).erase b).erase c).erase d).biUnion T := by
  intro q hq
  obtain ⟨k, hk, hkq⟩ := Finset.mem_biUnion.mp hq
  by_cases hka : k = a
  · rw [hka] at hkq
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hkq)))))))
  · by_cases hkb : k = b
    · rw [hkb] at hkq
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hkq)))))))
    · by_cases hkc : k = c
      · rw [hkc] at hkq
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr hkq)))))
      · by_cases hkd : k = d
        · rw [hkd] at hkq
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hkq)))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
            ⟨k, Finset.mem_erase.mpr ⟨hkd, Finset.mem_erase.mpr ⟨hkc, Finset.mem_erase.mpr
              ⟨hkb, Finset.mem_erase.mpr ⟨hka, hk⟩⟩⟩⟩, hkq⟩))

private lemma sum_erase_erase_add_of_mem {ι : Type*} [DecidableEq ι] {s : Finset ι} (f : ι → ℕ)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    f i + f j + ∑ k ∈ (s.erase i).erase j, f k = ∑ k ∈ s, f k := by
  have h1 := Finset.add_sum_erase s f hi
  have h2 := Finset.add_sum_erase (s.erase i) f (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)
  omega

private lemma sum_erase_four_add_of_mem {ι : Type*} [DecidableEq ι] {s : Finset ι} (f : ι → ℕ)
    {a b c d : ι} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    f a + f b + f c + f d + ∑ k ∈ ((((s.erase a).erase b).erase c).erase d), f k =
      ∑ k ∈ s, f k := by
  have h1 := Finset.add_sum_erase s f ha
  have h2 := Finset.add_sum_erase (s.erase a) f (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
  have h3 := Finset.add_sum_erase ((s.erase a).erase b) f
    (Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, hc⟩⟩)
  have h4 := Finset.add_sum_erase (((s.erase a).erase b).erase c) f
    (Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_erase.mpr ⟨hbd.symm,
      Finset.mem_erase.mpr ⟨had.symm, hd⟩⟩⟩)
  omega

private lemma card_union_four_le_pair {α : Type*} [DecidableEq α] (A B C D : Finset α) :
    (A ∪ B ∪ C ∪ D).card ≤ (A ∪ B).card + (C ∪ D).card := by
  have h := Finset.card_union_le (A ∪ B) (C ∪ D)
  simpa only [Finset.union_assoc] using h

theorem card_le_sum_card_of_subset_biUnion {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : ι → Finset α) (H : Finset α)
    (h : ∀ p ∈ H, ∃ i ∈ s, p ∈ T i) : H.card ≤ ∑ i ∈ s, (T i).card := by
  have hsub : H ⊆ s.biUnion T := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := h p hp
    exact Finset.mem_biUnion.mpr ⟨i, hi, hip⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le

theorem exists_ne_of_two_le_card_filter {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    {T : ι → Finset α} {i : ι} {p : α} (hp : p ∈ T i)
    (h2 : 2 ≤ (Finset.univ.filter (fun j => p ∈ T j)).card) : ∃ j, j ≠ i ∧ p ∈ T j := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hsub : Finset.univ.filter (fun j => p ∈ T j) ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_singleton]
    by_contra hji
    exact hcon j hji hj
  have hle : (Finset.univ.filter (fun j => p ∈ T j)).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hmem : i ∈ Finset.univ.filter (fun j => p ∈ T j) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  have hge : 1 ≤ (Finset.univ.filter (fun j => p ∈ T j)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

theorem disjoint_of_sum_card_eq' {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : ι → Finset α) (H : Finset α)
    (hsub : ∀ i ∈ s, T i ⊆ H) (hcover : ∀ p ∈ H, ∃ i ∈ s, p ∈ T i)
    (hsum : ∑ i ∈ s, (T i).card = H.card) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) : Disjoint (T i) (T j) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hpi, hpj⟩ := Finset.mem_inter.mp hp
  have hHsub : H ⊆ s.biUnion T := by
    intro q hq
    obtain ⟨k, hk, hkq⟩ := hcover q hq
    exact Finset.mem_biUnion.mpr ⟨k, hk, hkq⟩
  have hTsub : s.biUnion T ⊆ H := Finset.biUnion_subset.mpr hsub
  have hcard_eq : (s.biUnion T).card = H.card :=
    le_antisymm (Finset.card_le_card hTsub) (Finset.card_le_card hHsub)
  have hb2 : (s.biUnion T).card ≤
      ((T i ∪ T j) ∪ ((s.erase i).erase j).biUnion T).card :=
    Finset.card_le_card biUnion_subset_union_erase_erase
  have hb3 : ((T i ∪ T j) ∪ ((s.erase i).erase j).biUnion T).card ≤
      (T i ∪ T j).card + ∑ k ∈ (s.erase i).erase j, (T k).card :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left Finset.card_biUnion_le _)
  have hAi : 1 ≤ (T i).card := Finset.card_pos.mpr ⟨p, hpi⟩
  have hBj : 1 ≤ (T j).card := Finset.card_pos.mpr ⟨p, hpj⟩
  have hI : 1 ≤ (T i ∩ T j).card := Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpi, hpj⟩⟩
  have hunion : (T i ∪ T j).card = (T i).card + (T j).card - (T i ∩ T j).card :=
    Finset.card_union _ _
  have hsum' : (T i).card + (T j).card + ∑ k ∈ (s.erase i).erase j, (T k).card = H.card := by
    rw [← hsum]
    exact sum_erase_erase_add_of_mem (fun k => (T k).card) hi hj hij
  omega

theorem no_two_collisions' {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (T : ι → Finset α) (H : Finset α) (hH : H.card = 12)
    (hcover : ∀ p ∈ H, ∃ i ∈ s, p ∈ T i)
    (hsum : ∑ i ∈ s, (T i).card = 13)
    {a b c d : ι} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h3 : (T a).card = 3) (h4 : (T b).card = 4) (h1 : (T c).card = 1) (h2 : (T d).card = 2)
    (hne1 : (T a ∩ T b).Nonempty) (hne2 : (T c ∩ T d).Nonempty) : False := by
  have hcover' : H ⊆ s.biUnion T := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := hcover p hp
    exact Finset.mem_biUnion.mpr ⟨i, hi, hip⟩
  have hb1 : H.card ≤ (s.biUnion T).card := Finset.card_le_card hcover'
  have hb2 : (s.biUnion T).card ≤
      (T a ∪ T b ∪ T c ∪ T d).card +
        ∑ i ∈ (((s.erase a).erase b).erase c).erase d, (T i).card := by
    have hcard : (s.biUnion T).card ≤
        ((T a ∪ T b ∪ T c ∪ T d) ∪
          ((((s.erase a).erase b).erase c).erase d).biUnion T).card :=
      Finset.card_le_card biUnion_subset_union_erase_four
    exact le_trans hcard
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left Finset.card_biUnion_le _))
  have huab : (T a ∪ T b).card ≤ 6 := by
    have h := Finset.card_union (T a) (T b)
    have hp : 1 ≤ (T a ∩ T b).card := Finset.card_pos.mpr hne1
    omega
  have hucd : (T c ∪ T d).card ≤ 2 := by
    have h := Finset.card_union (T c) (T d)
    have hp : 1 ≤ (T c ∩ T d).card := Finset.card_pos.mpr hne2
    omega
  have hu : (T a ∪ T b ∪ T c ∪ T d).card ≤ 8 := by
    have h := card_union_four_le_pair (T a) (T b) (T c) (T d)
    omega
  have hsum4 : (T a).card + (T b).card + (T c).card + (T d).card +
      ∑ i ∈ (((s.erase a).erase b).erase c).erase d, (T i).card = ∑ i ∈ s, (T i).card :=
    sum_erase_four_add_of_mem (fun k => (T k).card) ha hb hc hd hab hac had hbc hbd hcd
  omega

end Util

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
@[simp] theorem out_def (S : Anchored ι) (i j : ι) : S.out i j = (S.point i \ S.H) ∩ (S.point j \ S.H) := rfl
def b (S : Anchored ι) (i : ι) : ℕ := (S.point i \ S.H).card
def dval (S : Anchored ι) (i : ι) : ℕ := traceCap (S.sz i) - (S.trace i).card
def sizeSet (S : Anchored ι) : Finset ℕ := (univ.erase S.anchor).image S.sz
noncomputable def invOf (S : Anchored ι) (m : ℕ) : ι := @Function.invFun ι ℕ ⟨S.anchor⟩ S.sz m
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

def rest (S : Anchored ι) : Finset ι := univ.erase S.anchor

theorem trace_cover (S : Anchored ι) {p : Fin 60} (hp : p ∈ S.H) :
    ∃ i ∈ S.rest, p ∈ S.trace i := by
  have hpa : p ∈ S.point S.anchor := by rw [S.point_anchor]; exact hp
  rcases S.cover p with h2 | hnone
  · obtain ⟨j, hj, hpj⟩ := Util.exists_ne_of_two_le_card_filter hpa h2
    exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, Finset.mem_inter.mpr ⟨hpj, hp⟩⟩
  · exact absurd hpa (hnone S.anchor)

theorem sum_rest_eq_sizeSet (S : Anchored ι) (F : ℕ → ℕ) :
    ∑ i ∈ S.rest, F (S.sz i) = ∑ m ∈ S.sizeSet, F m := by
  rw [rest, sizeSet]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

theorem sum_rest_erase_eq (S : Anchored ι) (i : ι) (F : ℕ → ℕ) :
    ∑ j ∈ S.rest.erase i, F (S.sz j) = ∑ n ∈ S.sizeSet.erase (S.sz i), F n := by
  rw [rest, sizeSet, ← Finset.image_erase S.sz_injective]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

theorem sum_rest_erase_erase_eq (S : Anchored ι) (i j : ι) (F : ℕ → ℕ) :
    ∑ k ∈ (S.rest.erase i).erase j, F (S.sz k)
      = ∑ n ∈ (S.sizeSet.erase (S.sz i)).erase (S.sz j), F n := by
  rw [rest, sizeSet, ← Finset.image_erase S.sz_injective, ← Finset.image_erase S.sz_injective]
  exact (Finset.sum_image (f := F) (g := S.sz) (fun x _ y _ hxy => S.sz_injective hxy)).symm

theorem sum_dval_eq_delta (S : Anchored ι) : ∑ i ∈ S.rest, S.dval i = delta S.dOf := by
  have h1 : ∀ i ∈ S.rest, S.dval i = toFun S.dOf (S.sz i) := by
    intro i hi
    have hia : i ≠ S.anchor := (Finset.mem_erase.mp hi).1
    rw [toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨i, hia, rfl⟩)]
    exact (dOf_apply S hia).symm
  rw [Finset.sum_congr rfl h1, sum_rest_eq_sizeSet S (toFun S.dOf)]
  rfl

theorem trace_sum_add_delta (S : Anchored ι) :
    (∑ i ∈ S.rest, (S.trace i).card) + delta S.dOf = sizeSum S.sizeSet := by
  have h1 : ∀ i ∈ S.rest, (S.trace i).card = traceCap (S.sz i) - S.dval i := by
    intro i _
    have := trace_card_le S i
    rw [dval]
    omega
  have h2 : ∀ i ∈ S.rest, traceCap (S.sz i) - S.dval i + S.dval i = traceCap (S.sz i) :=
    fun i _ => Nat.sub_add_cancel (Nat.sub_le _ _)
  have h3 : ∑ i ∈ S.rest, S.dval i = delta S.dOf := sum_dval_eq_delta S
  have h4 : ∑ i ∈ S.rest, traceCap (S.sz i) = sizeSum S.sizeSet := sum_rest_eq_sizeSet S traceCap
  rw [Finset.sum_congr rfl h1, ← h3, ← Finset.sum_add_distrib, Finset.sum_congr rfl h2, h4]

theorem sizeSum_ge (S : Anchored ι) : 12 ≤ sizeSum S.sizeSet := by
  have h1 := Util.card_le_sum_card_of_subset_biUnion S.rest S.trace S.H (fun p hp => trace_cover S hp)
  have h2 := trace_sum_add_delta S
  have h3 : S.H.card = 12 := S.card_H
  omega

theorem dOf_mem_tuples (S : Anchored ι) : S.dOf ∈ tuples S.sizeSet := by
  rw [tuples, Fintype.mem_piFinset]
  intro n
  have hsz : S.sz (S.invOf n.val) = n.val := sz_invOf S n.property
  have hdof : S.dOf n = S.dval (S.invOf n.val) := by simp only [dOf, dval, hsz]
  rw [hdof]
  have h := dval_mem S (S.invOf n.val)
  rwa [hsz] at h

theorem dOf_admissible (S : Anchored ι) : admissible S.dOf := by
  rw [admissible, slack]
  have h1 := Util.card_le_sum_card_of_subset_biUnion S.rest S.trace S.H (fun p hp => trace_cover S hp)
  have h2 := trace_sum_add_delta S
  have h3 : S.H.card = 12 := S.card_H
  omega

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
      · obtain ⟨j, hji, hpj⟩ := Util.exists_ne_of_two_le_card_filter hpi h2
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

theorem out_card_le_cap (S : Anchored ι) {i j : ι} (hij : i ≠ j) :
    (S.out i j).card ≤ min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j))) := by
  have h := S.pair_cap i j hij
  have h1 : S.b i = S.sz i - (S.point i ∩ S.H).card := b_eq S i
  have h2 : S.b j = S.sz j - (S.point j ∩ S.H).card := b_eq S j
  rw [h1, h2]
  exact h

theorem sum_min_eq_rhs (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) :
    ∑ j ∈ S.rest.erase i, min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j)))
      = rhs S.dOf (S.sz i) := by
  have h1 : ∀ j ∈ S.rest.erase i,
      min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j)))
        = min (bval S.dOf (S.sz i)) (min (bval S.dOf (S.sz j)) (pairCap (S.sz i) (S.sz j))) := by
    intro j hj
    have hja : j ≠ S.anchor := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    rw [b_eq_bval S hi, b_eq_bval S hja]
  rw [Finset.sum_congr rfl h1, sum_rest_erase_eq S i
    (fun n => min (bval S.dOf (S.sz i)) (min (bval S.dOf n) (pairCap (S.sz i) n)))]
  rfl

theorem false_of_witness (S : Anchored ι) (m : ℕ) (hm : m ∈ S.sizeSet)
    (hviol : ∀ d ∈ tuples S.sizeSet, admissible d → rhs d m < bval d m) : False := by
  obtain ⟨i, hi, hsz⟩ := (mem_sizeSet_iff S).mp hm
  have h1 := b_le_sum_out S i
  have h2 : ∑ j ∈ S.rest.erase i, min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j)))
      = rhs S.dOf m := by rw [← hsz]; exact sum_min_eq_rhs S hi
  have h3 : rhs S.dOf m < bval S.dOf m := hviol S.dOf (dOf_mem_tuples S) (dOf_admissible S)
  have h4 : bval S.dOf m = S.b i := by rw [← hsz]; exact (b_eq_bval S hi).symm
  have h5 : S.b i ≤ ∑ j ∈ S.rest.erase i, min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j))) :=
    le_trans h1 (Finset.sum_le_sum fun j hj => out_card_le_cap S (Finset.mem_erase.mp hj).1.symm)
  omega

theorem out_card_le_sizeContrib (S : Anchored ι) {i j : ι} (h10 : S.sz i = 10) (hj : j ≠ i)
    (hja : j ≠ S.anchor) : (S.out i j).card ≤ sizeContrib S.dOf (S.sz j) := by
  have hcap : (S.out i j).card ≤ min (S.b i) (min (S.b j) (pairCap (S.sz i) (S.sz j))) :=
    out_card_le_cap S hj.symm
  have hbi : S.b i = 8 := b_of_sz_ten S h10
  have hbj : S.b j = S.sz j - traceCap (S.sz j) + S.dval j := by
    rw [b_eq_bval S hja, bval]
    congr 1
    rw [toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨j, hja, rfl⟩)]
    exact dOf_apply S hja
  have htof : ∀ m : ℕ, S.sz j = m → toFun S.dOf m = S.dval j := by
    intro m hm
    rw [← hm, toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨j, hja, rfl⟩)]
    exact dOf_apply S hja
  have hdj := dval_mem S j
  have hmem := sz_mem_lower S hja
  have hne : S.sz j ≠ 10 := fun h => hj (S.sz_injective (by rw [h, h10]))
  simp only [lowerSizes, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h
  · have hsc : sizeContrib S.dOf (S.sz j) = S.dval j := by
      rw [h, sizeContrib, if_pos rfl]
      exact htof 1 h
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_one] at h2
    rw [hsc]
    omega
  · have hsc : sizeContrib S.dOf (S.sz j) = S.dval j := by
      rw [h, sizeContrib, if_neg (by norm_num : (2:ℕ) ≠ 1), if_pos rfl]
      exact htof 2 h
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_two] at h2
    rw [hsc]
    omega
  · have hsc : sizeContrib S.dOf (S.sz j) = min (S.dval j) 1 := by
      rw [h, sizeContrib, if_neg (by norm_num : (3:ℕ) ≠ 1), if_neg (by norm_num : (3:ℕ) ≠ 2),
        if_pos rfl, htof 3 h]
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_three] at h2
    rw [hsc]
    omega
  · have hsc : sizeContrib S.dOf (S.sz j) = min (S.dval j) 2 := by
      rw [h, sizeContrib, if_neg (by norm_num : (4:ℕ) ≠ 1), if_neg (by norm_num : (4:ℕ) ≠ 2),
        if_neg (by norm_num : (4:ℕ) ≠ 3), if_pos rfl, htof 4 h]
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_four] at h2
    rw [hsc]
    omega
  · have hd5 : S.dval j = 0 := by
      rw [h] at hdj
      simpa only [deficiencies, Finset.mem_singleton] using hdj
    have hsc : sizeContrib S.dOf (S.sz j) = (if excess S.dOf = 0 then 1 else 4) := by
      rw [h, sizeContrib, if_neg (by norm_num : (5:ℕ) ≠ 1), if_neg (by norm_num : (5:ℕ) ≠ 2),
        if_neg (by norm_num : (5:ℕ) ≠ 3), if_neg (by norm_num : (5:ℕ) ≠ 4), if_pos rfl]
      rfl
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_five] at h2
    by_cases hex : excess S.dOf = 0
    · have hsum : ∑ k ∈ S.rest, (S.trace k).card = S.H.card := by
        have h1 := trace_sum_add_delta S
        have h2 := sizeSum_ge S
        have hadm : delta S.dOf ≤ slack S.sizeSet := dOf_admissible S
        have hge : slack S.sizeSet ≤ delta S.dOf := by
          have hh : slack S.sizeSet - delta S.dOf = 0 := by rw [← excess]; exact hex
          omega
        have h4 : delta S.dOf = slack S.sizeSet := le_antisymm hadm hge
        have hsl : slack S.sizeSet = sizeSum S.sizeSet - 12 := rfl
        have h1' : sizeSum S.sizeSet = (∑ k ∈ S.rest, (S.trace k).card) + slack S.sizeSet := by
          rw [← h4]
          exact h1.symm
        have h7 : sizeSum S.sizeSet - slack S.sizeSet = ∑ k ∈ S.rest, (S.trace k).card :=
          Nat.sub_eq_of_eq_add h1'
        rw [S.card_H, ← h7, hsl, Nat.sub_sub_self h2]
      have hia : i ≠ S.anchor := by
        rintro rfl
        rw [S.sz_anchor] at h10
        exact absurd h10 (by norm_num)
      have hdisj : Disjoint (S.trace j) (S.trace i) :=
        Util.disjoint_of_sum_card_eq' S.rest S.trace S.H (fun k _ => trace_subset S k)
          (fun p hp => trace_cover S hp) hsum
          (Finset.mem_erase.mpr ⟨hja, Finset.mem_univ j⟩)
          (Finset.mem_erase.mpr ⟨hia, Finset.mem_univ i⟩) hj
      have h42 : ((S.point j \ S.H) ∩ (S.point i \ S.H)).card ≤ 1 := S.lemma42 j i h h10 hdisj
      rw [hsc, if_pos hex, out_def, Finset.inter_comm]
      exact h42
    · rw [hsc, if_neg hex]
      omega
  · have hd6 : S.dval j = 0 ∨ 1 ≤ S.dval j := by
      rw [h] at hdj
      simp only [deficiencies, Finset.mem_insert, Finset.mem_singleton] at hdj
      omega
    have hsc : sizeContrib S.dOf (S.sz j) = 1 + S.dval j := by
      rw [h, sizeContrib, if_neg (by norm_num : (6:ℕ) ≠ 1), if_neg (by norm_num : (6:ℕ) ≠ 2),
        if_neg (by norm_num : (6:ℕ) ≠ 3), if_neg (by norm_num : (6:ℕ) ≠ 4),
        if_neg (by norm_num : (6:ℕ) ≠ 5), if_pos rfl, htof 6 h]
    have h2 := hcap
    rw [hbi, h10, h, pairCap_ten_six] at h2
    rcases hd6 with hd6 | hd6
    · have hcard3 : (S.trace j).card = 3 := by
        have hle := trace_card_le S j
        rw [h, traceCap_six] at hle
        rw [dval, h, traceCap_six] at hd6
        omega
      have h43 : ((S.point j \ S.H) ∩ (S.point i \ S.H)).card ≤ 1 := S.lemma43 j i h hcard3 h10
      rw [hsc, hd6, out_def, Finset.inter_comm]
      exact h43
    · rw [hsc]
      omega
  · exact absurd h hne

theorem sum_out_le_outsideBound (S : Anchored ι) {i : ι} (h10 : S.sz i = 10) :
    ∑ j ∈ S.rest.erase i, (S.out i j).card ≤ outsideBound S.dOf := by
  calc ∑ j ∈ S.rest.erase i, (S.out i j).card
      ≤ ∑ j ∈ S.rest.erase i, sizeContrib S.dOf (S.sz j) :=
        Finset.sum_le_sum fun j hj => out_card_le_sizeContrib S h10 (Finset.mem_erase.mp hj).1
          ((Finset.mem_erase.mp (Finset.mem_erase.mp hj).2)).1
    _ = ∑ n ∈ S.sizeSet.erase (S.sz i), sizeContrib S.dOf n := sum_rest_erase_eq S i _
    _ = outsideBound S.dOf := by rw [h10]; rfl

theorem dval_eq_toFun (S : Anchored ι) {i : ι} (hi : i ≠ S.anchor) {m : ℕ} (hm : S.sz i = m) :
    S.dval i = toFun S.dOf m := by
  rw [← hm, toFun, dif_pos ((mem_sizeSet_iff S).mpr ⟨i, hi, rfl⟩)]
  exact (dOf_apply S hi).symm

theorem sum_out_le_outsideBound_sub_three (S : Anchored ι) {i i5 : ι} (h10 : S.sz i = 10)
    (h5 : S.sz i5 = 5) (hi5 : i5 ≠ i) (hfive : (S.out i i5).card ≤ 1)
    (hex : excess S.dOf ≠ 0) :
    ∑ j ∈ S.rest.erase i, (S.out i j).card ≤ outsideBound S.dOf - 3 := by
  have h5a : i5 ≠ S.anchor := by
    rintro rfl
    rw [S.sz_anchor] at h5
    exact absurd h5 (by norm_num)
  have h5mem : S.sz i5 ∈ S.sizeSet.erase 10 :=
    Finset.mem_erase.mpr ⟨by rw [h5]; norm_num, (mem_sizeSet_iff S).mpr ⟨i5, h5a, rfl⟩⟩
  have hi5mem : i5 ∈ S.rest.erase i :=
    Finset.mem_erase.mpr ⟨hi5, Finset.mem_erase.mpr ⟨h5a, Finset.mem_univ i5⟩⟩
  have hsc5 : sizeContrib S.dOf (S.sz i5) = 4 := by
    rw [h5, sizeContrib, if_neg (by norm_num : (5:ℕ) ≠ 1), if_neg (by norm_num : (5:ℕ) ≠ 2),
      if_neg (by norm_num : (5:ℕ) ≠ 3), if_neg (by norm_num : (5:ℕ) ≠ 4), if_pos rfl]
    rw [excess] at hex
    exact if_neg hex
  have hsplit : ∑ j ∈ S.rest.erase i, (S.out i j).card
      = (S.out i i5).card + ∑ k ∈ (S.rest.erase i).erase i5, (S.out i k).card :=
    (Finset.add_sum_erase (S.rest.erase i) (fun j => (S.out i j).card) hi5mem).symm
  have hrest : ∑ k ∈ (S.rest.erase i).erase i5, (S.out i k).card
      ≤ ∑ n ∈ (S.sizeSet.erase (S.sz i)).erase (S.sz i5), sizeContrib S.dOf n := by
    refine le_trans (Finset.sum_le_sum fun k hk => ?_)
      (le_of_eq (sum_rest_erase_erase_eq S i i5 _))
    exact out_card_le_sizeContrib S h10 (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      (Finset.mem_erase.mp ((Finset.mem_erase.mp (Finset.mem_erase.mp hk).2)).2).1
  have hbound : outsideBound S.dOf
      = sizeContrib S.dOf (S.sz i5)
        + ∑ n ∈ (S.sizeSet.erase (S.sz i)).erase (S.sz i5), sizeContrib S.dOf n := by
    rw [outsideBound, h10]
    exact (Finset.add_sum_erase (S.sizeSet.erase 10) (sizeContrib S.dOf) h5mem).symm
  rw [hsplit, hbound, hsc5]
  omega

theorem no_anchored_system (S : Anchored ι) : False := by
  have hM : S.sizeSet ∈ sizeSets := by
    rw [sizeSets, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨sizeSet_subset S, sizeSum_ge S⟩
  have key : ∀ i : ι, S.sz i = 10 →
      8 ≤ ∑ j ∈ S.rest.erase i, (S.out i j).card ∧
        ∑ j ∈ S.rest.erase i, (S.out i j).card ≤ outsideBound S.dOf := by
    intro i hi
    have h8 : 8 ≤ ∑ j ∈ S.rest.erase i, (S.out i j).card := by
      have h := b_le_sum_out S i
      rwa [b_of_sz_ten S hi] at h
    exact ⟨h8, sum_out_le_outsideBound S hi⟩
  rcases finite_core S.sizeSet hM with ⟨m, hm, hviol⟩ | ⟨h10mem, hbound⟩ | ⟨hMB, h10mem, hbound⟩
  · exact false_of_witness S m hm hviol
  · obtain ⟨i10, -, hi10⟩ := (mem_sizeSet_iff S).mp h10mem
    obtain ⟨h8, hle⟩ := key i10 hi10
    have hb := hbound S.dOf (dOf_mem_tuples S) (dOf_admissible S)
    omega
  · obtain ⟨i10, hi10a, hi10⟩ := (mem_sizeSet_iff S).mp h10mem
    obtain ⟨h8, hle⟩ := key i10 hi10
    obtain ⟨hb8, hbeq⟩ := hbound S.dOf (dOf_mem_tuples S) (dOf_admissible S)
    by_cases hlt : outsideBound S.dOf < 8
    · omega
    · have heq : outsideBound S.dOf = 8 := by omega
      obtain ⟨hd3, hd4, hdelta⟩ := hbeq heq
      have h3mem : (3:ℕ) ∈ S.sizeSet := by rw [hMB]; decide
      have h4mem : (4:ℕ) ∈ S.sizeSet := by rw [hMB]; decide
      have h5mem : (5:ℕ) ∈ S.sizeSet := by rw [hMB]; decide
      obtain ⟨i3, hi3a, hi3⟩ := (mem_sizeSet_iff S).mp h3mem
      obtain ⟨i4, hi4a, hi4⟩ := (mem_sizeSet_iff S).mp h4mem
      obtain ⟨i5, hi5a, hi5⟩ := (mem_sizeSet_iff S).mp h5mem
      have hd3' : S.dval i3 = 0 := by rw [dval_eq_toFun S hi3a hi3, hd3]
      have hd4' : S.dval i4 = 0 := by rw [dval_eq_toFun S hi4a hi4, hd4]
      have ht3 : (S.trace i3).card = 3 := by
        have h := trace_card_le S i3
        rw [hi3, traceCap_three] at h
        rw [dval, hi3, traceCap_three] at hd3'
        omega
      have ht4 : (S.trace i4).card = 4 := by
        have h := trace_card_le S i4
        rw [hi4, traceCap_four] at h
        rw [dval, hi4, traceCap_four] at hd4'
        omega
      have ht5 : (S.trace i5).card = 1 := by
        have h := trace_card_le S i5
        rw [hi5, traceCap_five] at h
        have h0 : S.dval i5 = 0 := by
          have hd := dval_mem S i5
          rw [hi5] at hd
          simpa only [deficiencies, Finset.mem_singleton] using hd
        rw [dval, hi5, traceCap_five] at h0
        omega
      have ht10 : (S.trace i10).card = 2 := trace_card_eq_of_sz S hi10 attainableTraces_ten
      have h510 : i5 ≠ i10 := fun hh => by rw [hh] at hi5; omega
      by_cases hdisj : Disjoint (S.trace i5) (S.trace i10)
      · have hfive : (S.out i10 i5).card ≤ 1 := by
          have h := S.lemma42 i5 i10 hi5 hi10 (by rwa [trace, trace] at hdisj)
          rw [out_def, Finset.inter_comm]
          exact h
        have hex : excess S.dOf ≠ 0 := by
          have h16 : sizeSum S.sizeSet = 16 := by rw [hMB]; decide
          rw [excess, slack, h16, hdelta]
          norm_num
        have hle3 := sum_out_le_outsideBound_sub_three S hi10 hi5 h510 hfive hex
        omega
      · have hne2 : (S.trace i5 ∩ S.trace i10).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hdisj
        have hne1 : (S.trace i3 ∩ S.trace i4).Nonempty := by
          have h' : (S.trace i3 ∩ S.trace i4).card = 1 := S.lemma41 i3 i4 hi3 hi4 ht3 ht4
          exact Finset.card_pos.mp (by omega)
        have hsum : ∑ k ∈ S.rest, (S.trace k).card = 13 := by
          have h := trace_sum_add_delta S
          have h16 : sizeSum S.sizeSet = 16 := by rw [hMB]; decide
          rw [h16, hdelta] at h
          exact Nat.add_right_cancel (by rw [h])
        exact Util.no_two_collisions' S.rest S.trace S.H S.card_H
          (fun p hp => trace_cover S hp) hsum
          (Finset.mem_erase.mpr ⟨hi3a, Finset.mem_univ i3⟩)
          (Finset.mem_erase.mpr ⟨hi4a, Finset.mem_univ i4⟩)
          (Finset.mem_erase.mpr ⟨hi5a, Finset.mem_univ i5⟩)
          (Finset.mem_erase.mpr ⟨hi10a, Finset.mem_univ i10⟩)
          (fun hh => by rw [hh] at hi3; omega) (fun hh => by rw [hh] at hi3; omega)
          (fun hh => by rw [hh] at hi3; omega) (fun hh => by rw [hh] at hi4; omega)
          (fun hh => by rw [hh] at hi4; omega) h510 ht3 ht4 ht5 ht10 hne1 hne2

end Anchored
end CertPP12
end HSC
