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

def attainableTraces (m : ℕ) : Finset ℕ :=
  (deficiencies m).image (fun d => traceCap m - d)

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
def sizeSets : Finset (Finset ℕ) :=
  lowerSizes.powerset.filter (fun M => 12 ≤ sizeSum M)
abbrev DefTuple (M : Finset ℕ) := {m // m ∈ M} → ℕ
def tuples (M : Finset ℕ) : Finset (DefTuple M) :=
  Fintype.piFinset (fun m : {m // m ∈ M} => deficiencies m.val)
def toFun {M : Finset ℕ} (d : DefTuple M) : ℕ → ℕ :=
  fun m => if h : m ∈ M then d ⟨m, h⟩ else 0
def delta {M : Finset ℕ} (d : DefTuple M) : ℕ := ∑ m ∈ M, toFun d m
def admissible {M : Finset ℕ} (d : DefTuple M) : Prop := delta d ≤ slack M
instance {M : Finset ℕ} (d : DefTuple M) : Decidable (admissible d) := by
  unfold admissible delta
  infer_instance
def excess {M : Finset ℕ} (d : DefTuple M) : ℕ := slack M - delta d
def bval {M : Finset ℕ} (d : DefTuple M) (m : ℕ) : ℕ :=
  m - traceCap m + toFun d m
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
def outsideBound {M : Finset ℕ} (d : DefTuple M) : ℕ :=
  ∑ n ∈ M.erase 10, sizeContrib d n

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
theorem deficiencies_le_traceCap :
    ∀ m ∈ allSizes, ∀ d ∈ deficiencies m, d ≤ traceCap m := by decide
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
    (∃ m ∈ M, ∀ d ∈ tuples M, admissible d → rhs d m < bval d m) ∨ M = M_A ∨ M = M_B := by
  decide

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
      (∀ d ∈ tuples {1, 3, 4, 5, 6, 10}, admissible d → rhs d 10 < bval d 10) := by
  decide

theorem refuted_card :
    (sizeSets.filter fun M =>
      ∃ m ∈ M, ∀ d ∈ tuples M, admissible d → rhs d m < bval d m).card = 18 := by
  decide

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
          toFun d 3 = 0 ∧ toFun d 4 = 0 ∧ delta d = 3)) := by
  decide

end CertPP12
end HSC
