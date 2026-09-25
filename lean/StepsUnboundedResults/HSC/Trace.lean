/-
HSC/Trace.lean

R006, **Lemma B (the ascension lemma)** — the fragments that are proved, formalized.

The informal proof is `hsc-audit/theory/proof_lemma_B.md`, closed in
`hsc-audit/theory/lemma_B_attack3.md` and independently checked in
`hsc-audit/theory/lemma_B_attack3_verification.md`; the record entry is `results/R006.md` §3–§4.
Lemma B is a **theorem** of this development: `StepsUnboundedResults/HSC/LemmaB.lean` proves
`HSC.lemmaB_holds (G) : LemmaB G`. What remains for `H_p` of solvable groups is a different
statement — the ascension through a normal `q`-subgroup with `q ≠ p`, named `HSC.Ascension_ne` in
`HSC/Gap.lean`.  Nothing here closes that case, and nothing here assumes it.

What is formalized:

* **(B1) the trace identity.**  For `V ⊴ G`, `x : G`, `H ≤ G` and a `V`-coset `C = cV`, the
  intersection `xH ∩ C` is empty or a left coset of `H ⊓ V`
  (`leftCoset_inter_leftCoset_eq_empty_or_leftCoset_inf`); consequently `|xH ∩ C| = |H ⊓ V|` when
  `C ⊆ xHV` and `0` otherwise (`natCard_inter_leftCoset_eq_of_subset`), in the quotient-image form
  used downstream `natCard_inter_leftCoset_eq`.  The trace form `θ(𝟙_{xH}) = |H ⊓ V| • 𝟙_{ξK}`,
  `ξ = π x`, `K = HV/V`, is `trace_indicator_leftCoset` for the trace map `trace`.
* **(B2) the unrestricted descent.**  A relation `∑ᵢ 𝟙_{Dᵢ} = 0` in `𝔽_p[G]` descends to
  `∑ᵢ |Hᵢ ⊓ V| • 𝟙_{ξᵢKᵢ} = 0` in `𝔽_p[G ⧸ V]` (`descent`), by additivity of the trace and (B1).
* **(B3) the closure.**  If, in addition, some member meets `V` trivially, the descended relation
  has a nonempty all-ones layer: the coefficients `|Hᵢ ⊓ V|` are powers of `p`, so every coefficient
  with `|Hᵢ ⊓ V| ≠ 1` vanishes in `𝔽_p`, and the survivors are pairwise distinct cosets of pairwise
  distinct indices on `G ⧸ V`.  This contradicts `H_p(G ⧸ V)`:
  `not_sum_indicator_eq_zero_of_exists_inf_eq_bot`, with the contradiction form
  `not_relation_of_exists_inf_eq_bot`.  The arithmetic is `zmod_natCast_pow`; that the survivors also
  have pairwise distinct *sizes* on `G ⧸ V` — the admissibility remark after Lemma B.3 — is
  `natCard_map_ne_of_natCard_inf_eq_one`.
* **(B3(2)) blindness.**  If instead every member meets `V` in a subgroup of order divisible by `p`,
  then *every* descended coefficient is `0` in `𝔽_p[G ⧸ V]`: the descent of any relation — indeed of
  any family — is the tautology `0 = 0` and carries no information about the quotient
  (`descended_coefficient_eq_zero_of_dvd`, `descent_eq_zero_of_forall_dvd`).

The residual case of Lemma B — every member meets `V` in a subgroup of order divisible by `p` — is
**not** proved here and is not assumed: it is the open `HSC.LemmaB` of `HSC/Gap.lean`, and (B3(2)) is
the precise sense in which the descent is blind to it.  The index type of the two (B3) theorems is
`Type` rather than `Type*`, matching the frozen `HSC.HpUnguarded`, which quantifies over `ι : Type`;
every other statement below is universe-polymorphic.

Everything is kernel-checked; no `sorry`, no `axiom`, no `native_decide`.
-/
import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Lifting
import StepsUnboundedResults.HSC.PrivatePoints
import StepsUnboundedResults.HSC.LiftingTheorem
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped Classical Pointwise
open Finset

namespace HSC

variable {G : Type*} [Group G]

section Basic

/-! ## 1. The trace identity (Lemma B.1)

`V` is a *normal* subgroup throughout this section: normality is exactly what makes `HV` a subgroup
and the intersection `xH ∩ cV` a coset of `H ⊓ V`.  Without it the identity fails (the record's
`theory/verify_lemma_B_identity.g` finds failures already in `A₄`).
-/

/-- **Lemma B.1, geometric form.**  A left coset of `H` meets a left coset of the normal subgroup
`V` in either nothing or a left coset of `H ⊓ V`. -/
theorem leftCoset_inter_leftCoset_eq_empty_or_leftCoset_inf (V : Subgroup G) [V.Normal] (x : G)
    (H : Subgroup G) (c : G) :
    leftCoset x H ∩ leftCoset c V = ∅ ∨
      ∃ g₀ : G, leftCoset x H ∩ leftCoset c V = leftCoset g₀ (H ⊓ V) := by
  by_cases h : (leftCoset x H ∩ leftCoset c V).Nonempty
  · right
    obtain ⟨g₀, hgH, hgV⟩ := h
    exact ⟨g₀, by
      rw [Set.inter_comm, leftCoset_inter_leftCoset_eq_inf c x g₀ V H hgV hgH, inf_comm]⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp h)

/-- **Lemma B.1, counting form (the `0`-or-`|H ⊓ V|` dichotomy).**  This is the form in which the
identity is used downstream: for every `V`-coset `C = cV`, the cardinality of `xH ∩ C` is either `0`
or `|H ⊓ V|` — in particular it does not depend on which `V`-coset inside `xHV` was taken. -/
theorem natCard_inter_leftCoset_eq_zero_or (V : Subgroup G) [V.Normal] (x : G) (H : Subgroup G)
    (c : G) :
    Nat.card ↥(leftCoset x H ∩ leftCoset c V) = 0 ∨
      Nat.card ↥(leftCoset x H ∩ leftCoset c V) = Nat.card ↥(H ⊓ V) := by
  rcases leftCoset_inter_leftCoset_eq_empty_or_leftCoset_inf V x H c with h | ⟨g₀, hg₀⟩
  · exact Or.inl (by rw [h]; exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => x.2⟩))
  · exact Or.inr (by rw [hg₀, natCard_leftCoset])

/-- **Lemma B.1.**  For `V ⊴ G`, `x : G`, `H ≤ G` and every `V`-coset `C = cV`:
`|xH ∩ C| = |H ⊓ V|` if `C ⊆ xHV`, and `0` otherwise.  The condition `C ⊆ xHV` is stated in the
equivalent quotient form `π(c) ∈ π '' xH`, which is what the descent consumes (see
`natCard_inter_leftCoset_eq_of_subset` for the literal `C ⊆ xHV` form). -/
theorem natCard_inter_leftCoset_eq (V : Subgroup G) [V.Normal] (x : G) (H : Subgroup G) (c : G) :
    Nat.card ↥(leftCoset x H ∩ leftCoset c V)
      = if QuotientGroup.mk' V c ∈ QuotientGroup.mk' V '' leftCoset x H
        then Nat.card ↥(H ⊓ V) else 0 := by
  classical
  by_cases h : QuotientGroup.mk' V c ∈ QuotientGroup.mk' V '' leftCoset x H
  · rw [if_pos h]
    obtain ⟨g, hgH, hgq⟩ := h
    have hgV : g ∈ leftCoset c V := (mem_leftCoset_iff_mk'_eq V).mpr hgq
    rw [Set.inter_comm, leftCoset_inter_leftCoset_eq_inf c x g V H hgV hgH, natCard_leftCoset,
      inf_comm]
  · rw [if_neg h]
    have hempty : leftCoset x H ∩ leftCoset c V = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro g ⟨hgH, hgV⟩
      exact h ⟨g, hgH, (mem_leftCoset_iff_mk'_eq V).mp hgV⟩
    rw [hempty]
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => x.2⟩)

/-- The set `xHV` of the informal statement is the left coset of `H ⊔ V`: since `V ⊴ G`,
`HV = H ⊔ V` as sets.  A `V`-coset `cV` is contained in `xHV` exactly when its image in `G ⧸ V`
lies in the image of `xH`. -/
theorem leftCoset_subset_leftCoset_sup_iff (V : Subgroup G) [V.Normal] (x : G) (H : Subgroup G)
    (c : G) :
    leftCoset c V ⊆ leftCoset x (H ⊔ V) ↔
      QuotientGroup.mk' V c ∈ QuotientGroup.mk' V '' leftCoset x H := by
  constructor
  · intro hsub
    have hc : c ∈ leftCoset x (H ⊔ V) :=
      hsub (by rw [mem_leftCoset, inv_mul_cancel]; exact V.one_mem)
    have hc' : x⁻¹ * c ∈ ((H : Set G) * (V : Set G)) := by
      rw [← Subgroup.mul_normal H V]
      exact hc
    obtain ⟨h, hh, v, hv, hhv⟩ := Set.mem_mul.mp hc'
    refine ⟨x * h, ?_, ?_⟩
    · rw [mem_leftCoset, show x⁻¹ * (x * h) = h from by group]
      exact hh
    · refine (QuotientGroup.eq (s := V) (a := x * h) (b := c)).mpr ?_
      have hc_eq : c = x * (h * v) := by rw [hhv]; group
      rw [hc_eq]
      rw [show (x * h)⁻¹ * (x * (h * v)) = v from by group]
      exact hv
  · rintro ⟨g, hgH, hgq⟩ y hy
    rw [mem_leftCoset] at hy ⊢
    have hmk : QuotientGroup.mk' V g = QuotientGroup.mk' V y := by
      rw [hgq, (mem_leftCoset_iff_mk'_eq V).mp hy]
    have hyV : g⁻¹ * y ∈ V := (QuotientGroup.eq (s := V) (a := g) (b := y)).mp hmk
    rw [show x⁻¹ * y = (x⁻¹ * g) * (g⁻¹ * y) from by group]
    exact mul_mem (Subgroup.mem_sup_left hgH) (Subgroup.mem_sup_right hyV)

/-- **Lemma B.1 in the literal `C ⊆ xHV` form.**  For every `V`-coset `C = cV`,
`|xH ∩ C| = |H ⊓ V|` if `C ⊆ xHV`, and `0` otherwise. -/
theorem natCard_inter_leftCoset_eq_of_subset (V : Subgroup G) [V.Normal] (x : G) (H : Subgroup G)
    (c : G) :
    Nat.card ↥(leftCoset x H ∩ leftCoset c V)
      = if leftCoset c V ⊆ leftCoset x (H ⊔ V) then Nat.card ↥(H ⊓ V) else 0 := by
  rw [natCard_inter_leftCoset_eq, leftCoset_subset_leftCoset_sup_iff]

end Basic

section Descent

/-! ## 2. The trace map `θ` and the unrestricted descent (Lemma B.2)

`θ` sums the coefficients of an `𝔽_p`-valued function over each `V`-coset; it is the linear map
that carries a relation on `G` to the quotient `G ⧸ V`, with each member weighted by `|Hᵢ ⊓ V|`. -/

/-- **The trace map `θ`.**  For `f : G → 𝔽_p`, `trace V f q` is the sum of the coefficients of `f`
over the `V`-coset `π⁻¹(q)`, i.e. `∑_{x ∈ π⁻¹(q)} f x`. -/
noncomputable def trace {p : ℕ} (V : Subgroup G) [V.Normal] [Finite G] (f : G → ZMod p) :
    G ⧸ V → ZMod p :=
  letI := Fintype.ofFinite G
  fun q => ∑ g ∈ Finset.univ.filter (fun g => QuotientGroup.mk' V g = q), f g

/-- `θ` is additive: it is the `𝔽_p`-linear transfer of the relation to the quotient. -/
theorem trace_sum {p : ℕ} (V : Subgroup G) [V.Normal] [Finite G] {ι : Type*} [Fintype ι]
    (f : ι → G → ZMod p) : trace V (∑ i, f i) = ∑ i, trace V (f i) := by
  classical
  letI := Fintype.ofFinite G
  funext q
  simp only [trace, Finset.sum_apply]
  exact Finset.sum_comm

/-- **Lemma B.1 in trace form**: `θ(𝟙_{xH}) = |H ⊓ V| • 𝟙_{ξK}`, where `ξ = π x` and
`K = HV/V` is the image of `H` in `G ⧸ V`.  This is the identity that makes the descent work: the
trace of a member depends on it only through `|H ⊓ V|` and its `V`-coset. -/
theorem trace_indicator_leftCoset {p : ℕ} (V : Subgroup G) [V.Normal] [Finite G] (x : G)
    (H : Subgroup G) :
    trace V ((leftCoset x H).indicator (fun _ => (1 : ZMod p)))
      = (Nat.card ↥(H ⊓ V) : ZMod p) •
          ((leftCoset (QuotientGroup.mk' V x) (H.map (QuotientGroup.mk' V))).indicator
            (fun _ => (1 : ZMod p))) := by
  classical
  letI := Fintype.ofFinite G
  funext q
  rw [Pi.smul_apply, smul_eq_mul]
  obtain ⟨c₀, hc₀⟩ := QuotientGroup.mk'_surjective V q
  -- the fibre sum is the cardinality of the piece of the `V`-coset cut out by `xH`
  have h1 : trace V ((leftCoset x H).indicator (fun _ => (1 : ZMod p))) q
      = (((Finset.univ.filter (fun g : G => QuotientGroup.mk' V g = q)).filter
            (fun g => g ∈ leftCoset x H)).card : ZMod p) := by
    rw [trace]
    rw [← Finset.sum_boole (fun g => g ∈ leftCoset x H)
      (Finset.univ.filter (fun g : G => QuotientGroup.mk' V g = q))]
    exact Finset.sum_congr rfl fun g _ => by rw [Set.indicator_apply]
  have h2 : Nat.card ↥(leftCoset x H ∩ leftCoset c₀ V)
      = ((Finset.univ.filter (fun g : G => QuotientGroup.mk' V g = q)).filter
            (fun g => g ∈ leftCoset x H)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr ?_
    intro g _
    rw [Set.mem_inter_iff, mem_leftCoset_iff_mk'_eq V, hc₀]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [h1, ← h2, natCard_inter_leftCoset_eq V x H c₀, mk'_image_leftCoset V x H, hc₀,
    Set.indicator_apply]
  simp

/-- **Lemma B.2 (unrestricted descent).**  If `∑ᵢ 𝟙_{Dᵢ} = 0` in `𝔽_p[G]`, where `Dᵢ = cᵢHᵢ`, then
`∑ᵢ |Hᵢ ⊓ V| • 𝟙_{ξᵢKᵢ} = 0` in `𝔽_p[G ⧸ V]`, where `ξᵢ = π cᵢ` and `Kᵢ = HᵢV/V`. -/
theorem descent {p : ℕ} (V : Subgroup G) [V.Normal] [Finite G] {ι : Type*} [Fintype ι]
    (c : ι → G) (H : ι → Subgroup G)
    (hrel : (∑ i : ι, (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) = 0) :
    (∑ i : ι, (Nat.card ↥(H i ⊓ V) : ZMod p) •
        ((leftCoset (QuotientGroup.mk' V (c i)) ((H i).map (QuotientGroup.mk' V))).indicator
          (fun _ => (1 : ZMod p)))) = 0 := by
  classical
  calc (∑ i : ι, (Nat.card ↥(H i ⊓ V) : ZMod p) •
        ((leftCoset (QuotientGroup.mk' V (c i)) ((H i).map (QuotientGroup.mk' V))).indicator
          (fun _ => (1 : ZMod p))))
      = ∑ i : ι, trace V ((leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) :=
        Finset.sum_congr rfl fun i _ => (trace_indicator_leftCoset V (c i) (H i)).symm
    _ = trace V (∑ i : ι, (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) :=
        (trace_sum V _).symm
    _ = 0 := by rw [hrel]; funext q; simp [trace]

end Descent

section TrivialIntersection

/-! ## 3. The closure when some member meets `V` trivially (Lemma B.3)

`V` is now a normal `p`-subgroup.  The coefficients `|Hᵢ ⊓ V|` of the descended relation are powers
of `p`, so each is either `1` or `0` in `𝔽_p`: the members meeting `V` trivially survive the descent,
all others vanish.  If at least one member meets `V` trivially, the survivors are a nonempty
all-ones relation on `G ⧸ V` among cosets of pairwise distinct indices, which `H_p(G ⧸ V)` forbids.

The complementary statement — when *every* member meets `V` in a subgroup of order divisible by `p`,
the descent is the tautology `0 = 0` — is `descent_eq_zero_of_forall_dvd` below. -/

/-- `p ^ k` read in `𝔽_p` is `1` for `k = 0` and `0` for `k ≥ 1`: the arithmetic that decides which
members survive the descent. -/
theorem zmod_natCast_pow (p k : ℕ) : ((p ^ k : ℕ) : ZMod p) = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with h | h
  · rw [h, pow_zero, Nat.cast_one, if_pos rfl]
  · rw [if_neg h]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    rw [pow_succ, Nat.cast_mul, ZMod.natCast_self, mul_zero]

/-- **Lemma B.3(2), coefficient form (blindness).**  A descended coefficient `|H ⊓ V|` vanishes in
`𝔽_p[G ⧸ V]` as soon as `p` divides it. -/
theorem descended_coefficient_eq_zero_of_dvd {p : ℕ} (V : Subgroup G) (H : Subgroup G)
    (h : p ∣ Nat.card ↥(H ⊓ V)) : ((Nat.card ↥(H ⊓ V) : ℕ) : ZMod p) = 0 :=
  (ZMod.natCast_eq_zero_iff (Nat.card ↥(H ⊓ V)) p).mpr h

/-- **Lemma B.3(2) (blindness).**  If every member of the family meets `V` in a subgroup of order
divisible by `p`, then every coefficient of the descended relation is `0` in `𝔽_p[G ⧸ V]`. -/
theorem descended_coefficient_eq_zero_of_forall_dvd {p : ℕ} (V : Subgroup G) {ι : Type*}
    (H : ι → Subgroup G) (hdvd : ∀ i, p ∣ Nat.card ↥(H i ⊓ V)) (i : ι) :
    ((Nat.card ↥(H i ⊓ V) : ℕ) : ZMod p) = 0 :=
  descended_coefficient_eq_zero_of_dvd V (H i) (hdvd i)

/-- **Lemma B.3(2), descended form.**  If every coefficient is divisible by `p`, the descent of *any*
family — relation or not — is the tautology `0 = 0` in `𝔽_p[G ⧸ V]`.  This is the precise sense in
which the `V`-coset trace method is blind in the residual case of Lemma B: it imposes no constraint
on the quotient. -/
theorem descent_eq_zero_of_forall_dvd {p : ℕ} (V : Subgroup G) [V.Normal] [Finite G]
    {ι : Type*} [Fintype ι] (c : ι → G) (H : ι → Subgroup G)
    (hdvd : ∀ i, p ∣ Nat.card ↥(H i ⊓ V)) :
    (∑ i : ι, (Nat.card ↥(H i ⊓ V) : ZMod p) •
        ((leftCoset (QuotientGroup.mk' V (c i)) ((H i).map (QuotientGroup.mk' V))).indicator
          (fun _ => (1 : ZMod p)))) = 0 := by
  classical
  exact Finset.sum_eq_zero fun i _ => by
    rw [descended_coefficient_eq_zero_of_dvd V (H i) (hdvd i), zero_smul]

/-- In a finite group, distinct indices give distinct subgroup orders. -/
theorem natCard_ne_of_index_ne [Finite G] {H K : Subgroup G} (h : H.index ≠ K.index) :
    Nat.card ↥H ≠ Nat.card ↥K := by
  intro hcard
  refine h ?_
  have h1 := Subgroup.index_mul_card H
  have h2 := Subgroup.index_mul_card K
  rw [hcard] at h1
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥K)) (h1.trans h2.symm)

/-- In a finite group, equal indices give equal subgroup orders. -/
theorem natCard_eq_of_index_eq [Finite G] {H K : Subgroup G} (h : H.index = K.index) :
    Nat.card ↥H = Nat.card ↥K := by
  have h1 := Subgroup.index_mul_card H
  have h2 := Subgroup.index_mul_card K
  rw [h] at h1
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
    (h1.trans h2.symm)

/-- **Admissibility of the surviving family** (the remark after Lemma B.3 in `proof_lemma_B.md`
§2): on the layer where `|Hᵢ ⊓ V| = 1`, one has `|Hᵢ| = |Kᵢ|` for `Kᵢ = HᵢV/V`, so distinct `|Hᵢ|`
force the descended cosets to have pairwise distinct **sizes** on `G ⧸ V` — not only distinct
indices. -/
theorem natCard_map_ne_of_natCard_inf_eq_one [Finite G] (V : Subgroup G) [V.Normal] {ι : Type*}
    (H : ι → Subgroup G) (hidx : ∀ i j, i ≠ j → (H i).index ≠ (H j).index)
    {i j : ι} (hi : Nat.card ↥(H i ⊓ V) = 1) (hj : Nat.card ↥(H j ⊓ V) = 1) (hij : i ≠ j) :
    Nat.card ↥((H i).map (QuotientGroup.mk' V)) ≠ Nat.card ↥((H j).map (QuotientGroup.mk' V)) := by
  intro hK
  refine natCard_ne_of_index_ne (hidx i j hij) ?_
  have hi' : Nat.card ↥(H i) = Nat.card ↥((H i).map (QuotientGroup.mk' V)) := by
    rw [card_eq_card_inf_mul_card_map V (H i), inf_comm, hi, one_mul]
  have hj' : Nat.card ↥(H j) = Nat.card ↥((H j).map (QuotientGroup.mk' V)) := by
    rw [card_eq_card_inf_mul_card_map V (H j), inf_comm, hj, one_mul]
  rw [hi', hj', hK]

/-- **Lemma B.3 (the trivial-intersection case).**  Let `V ⊴ G` be a normal `p`-subgroup with
`H_p(G ⧸ V)`.  Then no nonempty family of pairwise distinct cosets of `G` with pairwise distinct
indices, *some member of which meets `V` trivially*, satisfies `∑ᵢ 𝟙_{Dᵢ} = 0` in `𝔽_p[G]`.

Descent (Lemma B.2) turns the relation into `∑ᵢ |Hᵢ ⊓ V| • 𝟙_{ξᵢKᵢ} = 0` on `G ⧸ V`; each
`|Hᵢ ⊓ V|` is a power of `p`, so it is `1` exactly for the members meeting `V` trivially and `0`
otherwise, and the surviving layer is a nonempty all-ones relation among cosets of pairwise distinct
indices on `G ⧸ V` — contradicting `H_p(G ⧸ V)`. -/
theorem not_sum_indicator_eq_zero_of_exists_inf_eq_bot {p : ℕ} (hp : p.Prime) (V : Subgroup G)
    [V.Normal] [Finite G] (hV : IsPGroup p V) (hQ : HpUnguarded p (G ⧸ V))
    {ι : Type} [Fintype ι] (c : ι → G) (H : ι → Subgroup G)
    (hcoset : ∀ i j, i ≠ j → leftCoset (c i) (H i) ≠ leftCoset (c j) (H j))
    (hidx : ∀ i j, i ≠ j → (H i).index ≠ (H j).index)
    (hsome : ∃ i, H i ⊓ V = ⊥) :
    (∑ i : ι, (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) ≠ 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have _ := hcoset
  intro hrel
  have hpow : ∀ i : ι, ∃ k : ℕ, Nat.card ↥(H i ⊓ V) = p ^ k := by
    intro i
    exact IsPGroup.iff_card.mp (hV.of_injective
      (Subgroup.inclusion (inf_le_right : H i ⊓ V ≤ V))
      (Subgroup.inclusion_injective (inf_le_right : H i ⊓ V ≤ V)))
  have hcoef : ∀ i : ι, ((Nat.card ↥(H i ⊓ V) : ℕ) : ZMod p)
      = if Nat.card ↥(H i ⊓ V) = 1 then 1 else 0 := by
    intro i
    obtain ⟨k, hk⟩ := hpow i
    rw [hk, zmod_natCast_pow p k]
    rcases eq_or_ne k 0 with hk0 | hk0
    · rw [if_pos hk0, if_pos (by rw [hk0, pow_zero])]
    · rw [if_neg hk0, if_neg]
      intro h1
      have h2 : 1 < p ^ k := Nat.one_lt_pow hk0 hp.one_lt
      omega
  obtain ⟨i₀, hi₀⟩ := hsome
  have hLne : Nonempty {i : ι // Nat.card ↥(H i ⊓ V) = 1} :=
    ⟨⟨i₀, by rw [hi₀]; exact Subgroup.card_bot⟩⟩
  have hLrel : (∑ i : {i : ι // Nat.card ↥(H i ⊓ V) = 1},
        (leftCoset (QuotientGroup.mk' V (c (i : ι)))
          ((H (i : ι)).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p))) = 0 := by
    calc (∑ i : {i : ι // Nat.card ↥(H i ⊓ V) = 1},
          (leftCoset (QuotientGroup.mk' V (c (i : ι)))
            ((H (i : ι)).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p)))
        = ∑ i ∈ Finset.univ.filter (fun i : ι => Nat.card ↥(H i ⊓ V) = 1),
            (leftCoset (QuotientGroup.mk' V (c i))
              ((H i).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p)) :=
          (Finset.sum_subtype (Finset.univ.filter (fun i : ι => Nat.card ↥(H i ⊓ V) = 1))
            (fun x => by simp)
            (fun i => (leftCoset (QuotientGroup.mk' V (c i))
              ((H i).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p)))).symm
      _ = ∑ i : ι, if Nat.card ↥(H i ⊓ V) = 1 then
            (leftCoset (QuotientGroup.mk' V (c i))
              ((H i).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p)) else 0 :=
          Finset.sum_filter (s := Finset.univ)
            (fun i : ι => Nat.card ↥(H i ⊓ V) = 1)
            (fun i => (leftCoset (QuotientGroup.mk' V (c i))
              ((H i).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p)))
      _ = ∑ i : ι, (Nat.card ↥(H i ⊓ V) : ZMod p) •
            (leftCoset (QuotientGroup.mk' V (c i))
              ((H i).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoef i]
          simp
      _ = 0 := descent V c H hrel
  have hcosetL : ∀ i j : {i : ι // Nat.card ↥(H i ⊓ V) = 1}, i ≠ j →
      leftCoset (QuotientGroup.mk' V (c (i : ι))) ((H (i : ι)).map (QuotientGroup.mk' V))
        ≠ leftCoset (QuotientGroup.mk' V (c (j : ι))) ((H (j : ι)).map (QuotientGroup.mk' V)) := by
    intro i j hij hEq
    refine natCard_map_ne_of_natCard_inf_eq_one V H hidx i.2 j.2 (fun h => hij (Subtype.ext h)) ?_
    have h1 := natCard_leftCoset (QuotientGroup.mk' V (c (i : ι)))
      ((H (i : ι)).map (QuotientGroup.mk' V))
    have h2 := natCard_leftCoset (QuotientGroup.mk' V (c (j : ι)))
      ((H (j : ι)).map (QuotientGroup.mk' V))
    rw [hEq] at h1
    exact h1.symm.trans h2
  have hidxL : ∀ i j : {i : ι // Nat.card ↥(H i ⊓ V) = 1}, i ≠ j →
      ((H (i : ι)).map (QuotientGroup.mk' V)).index
        ≠ ((H (j : ι)).map (QuotientGroup.mk' V)).index := by
    intro i j hij h
    exact natCard_map_ne_of_natCard_inf_eq_one V H hidx i.2 j.2
      (fun hh => hij (Subtype.ext hh)) (natCard_eq_of_index_eq h)
  exact hQ {i : ι // Nat.card ↥(H i ⊓ V) = 1}
    (fun i => QuotientGroup.mk' V (c (i : ι)))
    (fun i => (H (i : ι)).map (QuotientGroup.mk' V)) hLne hcosetL hidxL hLrel

/-- **Lemma B.3, contradiction form.**  Under the hypotheses of
`not_sum_indicator_eq_zero_of_exists_inf_eq_bot`, a relation `∑ᵢ 𝟙_{Dᵢ} = 0` in `𝔽_p[G]` is
impossible. -/
theorem not_relation_of_exists_inf_eq_bot {p : ℕ} (hp : p.Prime) (V : Subgroup G) [V.Normal]
    [Finite G] (hV : IsPGroup p V) (hQ : HpUnguarded p (G ⧸ V))
    {ι : Type} [Fintype ι] (c : ι → G) (H : ι → Subgroup G)
    (hcoset : ∀ i j, i ≠ j → leftCoset (c i) (H i) ≠ leftCoset (c j) (H j))
    (hidx : ∀ i j, i ≠ j → (H i).index ≠ (H j).index)
    (hsome : ∃ i, H i ⊓ V = ⊥)
    (hrel : (∑ i : ι, (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) = 0) : False :=
  not_sum_indicator_eq_zero_of_exists_inf_eq_bot hp V hV hQ c H hcoset hidx hsome hrel

end TrivialIntersection
