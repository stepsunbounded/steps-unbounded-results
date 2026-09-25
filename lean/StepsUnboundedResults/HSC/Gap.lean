/-
HSC/Gap.lean

The statements the R006 programme still rests on, named and left **open**.  The file exists so that
the gap is a visible object in the formal development rather than a remark in a note, and nothing
below is assumed anywhere in this development.

Position on 2026-09-13 (record: `results/R006.md`; ledger:
`hsc-audit/theory/verification_ledger.md`):

* `LemmaA` — the abelian case of `H_p`.  Proved for every cyclic group (all `n`, all primes) and,
  since 2026-09-13, for every finite abelian `q`-group: `StepsUnboundedResults/HSC/LemmaGQGroup.lean`,
  `HSC.LemmaGQGroup.no_family_distinct_orders_qgroup`.  What remains is `CStar` below, the
  unrestricted form of the lattice statement; by the descent lemma of
  `hsc-audit/theory/lemma_R_attack_verification.md` §4.2 combined with the prime-power case, `CStar`
  is *equivalent* to the recorded residual `C*` (at least two prime divisors, every Sylow of rank
  ≥ 2), so proving it completes the abelian case.
* `Ascension_ne` — the ascension through a normal `q`-subgroup with `q ≠ p`.  This is the case
  `LemmaB` does not cover: the trace coefficients are units mod `p` and no layer vanishes.  The
  record reduces it to one statement about two equal-size nonvanishing descended collision classes
  (`hsc-audit/theory/qp_ascension_case_b.md`).

`LemmaB` is **not** a gap: it is proved and consumed in `StepsUnboundedResults/HSC/LemmaB.lean`
(`HSC.lemmaB_holds (G) : LemmaB G`, and the unconditional
`HSC.HpUnguarded_of_isPGroup_normal`).  It is kept here for the record of what the programme needed.

With `LemmaA` and `Ascension_ne` proved, `H_p` would hold for every finite solvable group, and — with
the machine-checked reduction and lifting step of this development — the corollary "every finite
solvable group is HS" follows.  The numeric range the GAP search covers (`LI_p` for solvable groups
of order at most 47, plus orders 49–59 and 61–63) is deliberately **not** formalized: it is an
experiment, not a theorem.
-/
import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.PrivatePoints

open scoped Classical

namespace HSC

/-- **Lemma A (abelian case of `H_p`), stated in full.** `H_p(A)` for every finite abelian group
`A` and every prime `p` — equivalent to `LI_p(A)`.

Proved for cyclic `A` (every `n`, every prime) and for every finite abelian `q`-group
(`StepsUnboundedResults/HSC/LemmaGQGroup.lean`).  Open in general, and the residual is `CStar` below: the
lattice statement in its unrestricted form. -/
def LemmaA (A : Type*) [CommGroup A] [Finite A] : Prop :=
  ∀ (p : ℕ), p.Prime → HpUnguarded p A

/-- **`(D′)` — the dual form of the corpus condition `(D)`.**  Every element of the ambient group
lies in exactly zero or at least two members of the family.  For a family of pairwise distinct
orders, `(D′)` is the dual of "no quotient by a co-cyclic subgroup contains exactly one member";
the equivalence is §2 of `hsc-audit/theory/lemma_G_qgroup.md`. -/
def DPrime {B : Type*} [Group B] {ι : Type*} [Fintype ι] (L : ι → Subgroup B) : Prop :=
  ∀ x : B, Nat.card {i : ι // x ∈ L i} ≠ 1

/-- **The residual of the abelian case.**  No finite abelian group carries a *nonempty* family of
subgroups with pairwise distinct orders satisfying `(D′)`.

This is the unrestricted form of the lattice statement.  By the descent lemma of
`hsc-audit/theory/lemma_R_attack_verification.md` §4.2 together with the prime-power theorem
(`HSC.LemmaGQGroup`), it is equivalent to the recorded residual `C*`: the case in which the group
has at least two prime divisors and every Sylow subgroup has rank at least two.  A counterexample
to either form would refute Lemma R and break the Lemma A interface. -/
def CStar : Prop :=
  ∀ (B : Type*) [CommGroup B] [Finite B] (ι : Type) [Fintype ι] [Nonempty ι]
    (L : ι → Subgroup B),
    Function.Injective (fun i => Nat.card (L i)) → DPrime L → False

/-- **Lemma B (ascension through a normal `p`-subgroup), stated in full.**  If `V ⊴ G` is a normal
`p`-subgroup and `H_p(G ⧸ V)` holds, then `H_p(G)` holds.

**Proved** (2026-09-13, `hsc-audit/theory/lemma_B_attack3.md`, independently checked in
`theory/lemma_B_attack3_verification.md`; formalized here).  The case in which some member meets
`V` trivially is the trace/descent argument; the case in which every member contains `V` is a
pullback; and the remaining case — every member meets `V` in a subgroup of order divisible by `p`,
with at least one not containing `V` — is closed by tracing along a *non-normal* subgroup
`W ≤ V` of order `p^{d-k_min}` complementary to the minimal block's `V`-part: the survivors
(`H_i ∩ W = 1`) all have `k_i = k_min`, so `H_iW = H_iV` and their cosets pull back to an all-ones
relation on `G ⧸ V`, contradicting `H_p(G ⧸ V)`.  This definition is consumed and proved in
`StepsUnboundedResults/HSC/LemmaB.lean`: `HSC.lemmaB_holds (G) : LemmaB G` and the unconditional
`HSC.HpUnguarded_of_isPGroup_normal`, so the statement below is a theorem of this development. -/
def LemmaB (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (V : Subgroup G) [V.Normal] (p : ℕ), p.Prime → IsPGroup p V →
    HpUnguarded p (G ⧸ V) → HpUnguarded p G

/-- **The residual ascension.**  The ascension through a normal `q`-subgroup with `q ≠ p`: the case
`LemmaB` does not cover, where the trace coefficients are units mod `p` and no layer vanishes.

The record reduces this to one statement — no null distinct-size family has two distinct descended
collision classes of equal size with nonzero coefficients — in
`hsc-audit/theory/qp_ascension_case_b.md`; the reduction is independently verified in
`hsc-audit/theory/qp_ascension_spectral_verification.md`. -/
def Ascension_ne (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (V : Subgroup G) [V.Normal] (p q : ℕ), p.Prime → q.Prime → q ≠ p → IsPGroup q V →
    HpUnguarded p (G ⧸ V) → HpUnguarded p G

end HSC
