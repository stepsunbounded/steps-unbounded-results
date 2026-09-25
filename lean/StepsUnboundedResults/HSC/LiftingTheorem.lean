/-
HSC/LiftingTheorem.lean

**R004, "Lifting a normal `p`-subgroup."**  If `V ⊴ G` is a normal `p`-subgroup of the finite
group `G` and the quotient `G ⧸ V` has property `H_p` (the all-ones hypothesis of R006 — weaker
than `LI_p`, which appears here as the corollary `isHS_of_licosets_quotient`), then `G` satisfies
the Herzog–Schönheim conjecture.

The mathematical content is the classical `p`-adic lifting step (R004 page): given a coset
partition of `G` with pairwise distinct indices, one looks at the `V`-cosets (`= ` the fibres of
`π : G → G ⧸ V`).  Inside a fixed `V`-coset `F`, the pieces `F ∩ Dᵢ` are cosets of `V ⊓ Hᵢ`, of
size `p^(d - eᵢ)` where `p^d = |V|` and `p^{eᵢ} = [V : V ⊓ Hᵢ]`; they partition `F`.  Dividing the
resulting counting identity by `p^d` and reading it modulo `p` produces a nontrivial `𝔽_p`-linear
relation among the *largest* pieces, whose cosets in the quotient are pairwise distinct with
pairwise distinct indices.  That contradicts `LI_p(G ⧸ V)`.

Everything is kernel-checked; no `sorry`, no `axiom`, no `native_decide`.
-/
import StepsUnboundedResults.HSC.Lifting
import StepsUnboundedResults.HSC.PrivatePoints
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped Classical
open Finset

namespace HSC

variable {G : Type*} [Group G]

theorem leftCoset_inter_leftCoset_eq_inf (c x g₀ : G) (V H : Subgroup G)
    (hV : g₀ ∈ leftCoset c V) (hH : g₀ ∈ leftCoset x H) :
    leftCoset c V ∩ leftCoset x H = leftCoset g₀ (V ⊓ H) := by
  ext g
  simp only [Set.mem_inter_iff, mem_leftCoset, Subgroup.mem_inf]
  constructor
  · rintro ⟨hgV, hgH⟩
    refine ⟨?_, ?_⟩
    · have h : g₀⁻¹ * g = (c⁻¹ * g₀)⁻¹ * (c⁻¹ * g) := by group
      rw [h]; exact mul_mem (inv_mem hV) hgV
    · have h : g₀⁻¹ * g = (x⁻¹ * g₀)⁻¹ * (x⁻¹ * g) := by group
      rw [h]; exact mul_mem (inv_mem hH) hgH
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h : c⁻¹ * g = (c⁻¹ * g₀) * (g₀⁻¹ * g) := by group
      rw [h]; exact mul_mem hV h1
    · have h : x⁻¹ * g = (x⁻¹ * g₀) * (g₀⁻¹ * g) := by group
      rw [h]; exact mul_mem hH h2

theorem natCard_inter_leftCoset_of_nonempty {c x g₀ : G} {V H : Subgroup G}
    (hV : g₀ ∈ leftCoset c V) (hH : g₀ ∈ leftCoset x H) :
    Nat.card ↥(leftCoset c V ∩ leftCoset x H) = Nat.card ↥(V ⊓ H) := by
  rw [leftCoset_inter_leftCoset_eq_inf c x g₀ V H hV hH, natCard_leftCoset]

theorem card_eq_sum_card_inter [Finite G] (P : CosetPartition G) (F : Set G) :
    Nat.card ↥F = ∑ i : P.ι, Nat.card ↥(F ∩ leftCoset (P.x i) (P.H i)) := by
  classical
  let f : ↥F → Σ i : P.ι, ↥(F ∩ leftCoset (P.x i) (P.H i)) :=
    fun g => ⟨Classical.choose (P.cover (g : G)),
      ⟨(g : G), g.2, Classical.choose_spec (P.cover (g : G))⟩⟩
  have hf_apply : ∀ g : ↥F,
      f g = ⟨Classical.choose (P.cover (g : G)),
        ⟨(g : G), g.2, Classical.choose_spec (P.cover (g : G))⟩⟩ := fun g => rfl
  have hf_inj : Function.Injective f := by
    intro g g' h
    refine Subtype.ext ?_
    exact congrArg
      (fun t : Σ i : P.ι, ↥(F ∩ leftCoset (P.x i) (P.H i)) => (t.2 : G)) h
  have hf_surj : Function.Surjective f := by
    rintro ⟨i, g, hgF, hgD⟩
    have hchoose : Classical.choose (P.cover (g : G)) = i := by
      by_contra hne
      have h1 : (g : G) ∈ leftCoset (P.x (Classical.choose (P.cover (g : G))))
          (P.H (Classical.choose (P.cover (g : G)))) := Classical.choose_spec (P.cover (g : G))
      have hd := P.disjoint (Classical.choose (P.cover (g : G))) i hne
      have hbot : (g : G) ∈ (⊥ : Set G) := hd.le_bot ⟨h1, hgD⟩
      simp at hbot
    refine ⟨⟨(g : G), hgF⟩, ?_⟩
    rw [hf_apply]
    cases hchoose
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext rfl))
  have hcard : Nat.card ↥F = Nat.card (Σ i : P.ι, ↥(F ∩ leftCoset (P.x i) (P.H i))) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [hcard, Nat.card_sigma]

theorem mem_leftCoset_iff_mk'_eq (V : Subgroup G) [V.Normal] {c g : G} :
    g ∈ leftCoset c V ↔ QuotientGroup.mk' V g = QuotientGroup.mk' V c := by
  show c⁻¹ * g ∈ V ↔ _
  exact (QuotientGroup.eq (s := V) (a := c) (b := g)).symm.trans eq_comm

theorem mk'_image_leftCoset (V : Subgroup G) [V.Normal] (x : G) (H : Subgroup G) :
    QuotientGroup.mk' V '' leftCoset x H
      = leftCoset (QuotientGroup.mk' V x) (H.map (QuotientGroup.mk' V)) := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_leftCoset] at hg ⊢
    have h : (QuotientGroup.mk' V x)⁻¹ * QuotientGroup.mk' V g
        = QuotientGroup.mk' V (x⁻¹ * g) := by rw [map_mul, map_inv]
    rw [h]
    exact Subgroup.mem_map_of_mem _ hg
  · intro hq
    rw [mem_leftCoset] at hq
    obtain ⟨h, hh, hhq⟩ := Subgroup.mem_map.mp hq
    exact ⟨x * h, by rw [mem_leftCoset]; simpa using hh, by rw [map_mul, hhq]; group⟩

theorem sum_ite_card_eq_card_mk' [Finite G] (P : CosetPartition G) (V : Subgroup G) [V.Normal]
    (c : G) :
    ∑ i : P.ι,
        (if QuotientGroup.mk' V c
              ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i)
          then Nat.card ↥(V ⊓ P.H i) else 0)
      = Nat.card ↥V := by
  classical
  have hterm : ∀ i : P.ι,
      Nat.card ↥(leftCoset c V ∩ leftCoset (P.x i) (P.H i))
        = (if QuotientGroup.mk' V c
                ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i)
            then Nat.card ↥(V ⊓ P.H i) else 0) := by
    intro i
    by_cases h : QuotientGroup.mk' V c ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i)
    · rw [if_pos h]
      obtain ⟨g, hgD, hgq⟩ := h
      have hgF : g ∈ leftCoset c V := mem_leftCoset_iff_mk'_eq V |>.mpr hgq
      rw [leftCoset_inter_leftCoset_eq_inf c (P.x i) g V (P.H i) hgF hgD, natCard_leftCoset]
    · rw [if_neg h]
      have hempty : leftCoset c V ∩ leftCoset (P.x i) (P.H i) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro g ⟨hgF, hgD⟩
        exact h ⟨g, hgD, mem_leftCoset_iff_mk'_eq V |>.mp hgF⟩
      rw [hempty]
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => x.2⟩)
  calc ∑ i : P.ι,
        (if QuotientGroup.mk' V c ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i)
          then Nat.card ↥(V ⊓ P.H i) else 0)
      = ∑ i : P.ι, Nat.card ↥(leftCoset c V ∩ leftCoset (P.x i) (P.H i)) :=
        Finset.sum_congr rfl fun i _ => (hterm i).symm
    _ = Nat.card ↥(leftCoset c V) := (card_eq_sum_card_inter P (leftCoset c V)).symm
    _ = Nat.card ↥V := natCard_leftCoset c V

theorem sum_ite_card_eq_card [Finite G] (P : CosetPartition G) (V : Subgroup G) [V.Normal]
    (q : G ⧸ V) :
    ∑ i : P.ι,
        (if q ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i)
          then Nat.card ↥(V ⊓ P.H i) else 0)
      = Nat.card ↥V := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective V q
  rw [← hc]
  exact sum_ite_card_eq_card_mk' P V c

theorem zmod_natCast_pow_sub (p : ℕ) {f E : ℕ} (h : E ≤ f) :
    ((p ^ (f - E) : ℕ) : ZMod p) = if f = E then 1 else 0 := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h', Nat.sub_self, pow_zero, Nat.cast_one, if_pos rfl]
  · have hne : f ≠ E := h'.ne'
    rw [if_neg hne]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f - E ≠ 0)
    rw [hk, pow_succ, Nat.cast_mul, ZMod.natCast_self, mul_zero]

theorem zmod_sum_ite_eq_zero {p : ℕ} (hp : p.Prime) {κ : Type*} [Fintype κ]
    (f : κ → ℕ) {d E : ℕ} (hE : ∀ i, E ≤ f i) (hEd : E < d) (A : κ → Prop)
    [DecidablePred A]
    (h : ∑ i : κ, (if A i then p ^ (f i) else 0) = p ^ d) :
    ∑ i : κ, (if A i ∧ f i = E then (1 : ZMod p) else 0) = 0 := by
  classical
  have hdiv : ∑ i : κ, (if A i then p ^ (f i - E) else 0) = p ^ (d - E) := by
    refine Nat.mul_left_cancel (pow_pos hp.pos E) ?_
    rw [Finset.mul_sum, ← pow_add, Nat.add_sub_of_le hEd.le, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : A i
    · rw [if_pos hi, if_pos hi, ← pow_add, Nat.add_sub_of_le (hE i)]
    · rw [if_neg hi, if_neg hi, mul_zero]
  have hcast : ∑ i : κ, ((if A i then p ^ (f i - E) else 0 : ℕ) : ZMod p) = 0 := by
    rw [← Nat.cast_sum, hdiv, zmod_natCast_pow_sub p hEd.le, if_neg hEd.ne']
  have hgoal : ∑ i : κ, (if A i ∧ f i = E then (1 : ZMod p) else 0)
      = ∑ i : κ, ((if A i then p ^ (f i - E) else 0 : ℕ) : ZMod p) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : A i
    · rw [if_pos hi, zmod_natCast_pow_sub p (hE i)]
      by_cases hif : f i = E
      · rw [if_pos hif, if_pos ⟨hi, hif⟩]
      · rw [if_neg hif, if_neg (fun hc => hif hc.2)]
    · rw [if_neg hi, if_neg (fun hc => hi hc.1), Nat.cast_zero]
  rw [hgoal, hcast]

theorem card_eq_card_inf_mul_card_map (V : Subgroup G) [V.Normal] [Finite G]
    (H : Subgroup G) :
    Nat.card ↥H
      = Nat.card ↥(V ⊓ H) * Nat.card ↥(H.map (QuotientGroup.mk' V)) := by
  have hrel : V.relIndex H = Nat.card ↥(H.map (QuotientGroup.mk' V)) :=
    (congrArg (fun K : Subgroup G => K.relIndex H) (QuotientGroup.ker_mk' V)).symm.trans
      (Subgroup.relIndex_ker H (QuotientGroup.mk' V))
  have hidx : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : H.index * Nat.card ↥H
      = H.index * ((V ⊓ H).relIndex H * Nat.card ↥(V ⊓ H)) := by
    rw [Subgroup.index_mul_card H, ← mul_assoc,
      mul_comm H.index ((V ⊓ H).relIndex H),
      Subgroup.relIndex_mul_index (inf_le_right : V ⊓ H ≤ H),
      Subgroup.index_mul_card (V ⊓ H)]
  rw [Nat.mul_left_cancel (Nat.pos_of_ne_zero hidx) h1, Subgroup.inf_relIndex_right V H, hrel,
    mul_comm]

theorem sum_ite_and_eq_sum_subtype {κ M : Type*} [Fintype κ] [AddCommMonoid M]
    (f : κ → ℕ) (E : ℕ) (B : κ → Prop) [DecidablePred B] (v : M) :
    (∑ i : κ, (if B i ∧ f i = E then v else 0))
      = ∑ i : {i : κ // f i = E}, (if B (i : κ) then v else 0) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => f i = E)
    (fun x => by simp) (fun i => if B i then v else 0)]
  rw [← Finset.sum_subset (Finset.filter_subset (fun i => f i = E) Finset.univ)
    (fun x _ hx => by
      rw [Finset.mem_filter] at hx
      exact if_neg (fun hc => hx ⟨Finset.mem_univ x, hc.2⟩))]
  exact Finset.sum_congr rfl fun i hi => by
    rw [Finset.mem_filter] at hi
    rw [hi.2]; simp

theorem not_isHS_quotient_of_forall_le [Finite G] (V : Subgroup G) [V.Normal]
    (P : CosetPartition G) (hVH : ∀ i, V ≤ P.H i)
    (hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index) :
    ¬ IsHS (G ⧸ V) := by
  classical
  have hpre : ∀ i : P.ι,
      QuotientGroup.mk' V ⁻¹' (QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i))
        = leftCoset (P.x i) (P.H i) := by
    intro i
    ext g
    constructor
    · rintro ⟨h, hh, hgh⟩
      have hgV : h⁻¹ * g ∈ V := by
        refine (QuotientGroup.eq_one_iff (N := V) (h⁻¹ * g)).mp ?_
        show QuotientGroup.mk' V (h⁻¹ * g) = 1
        rw [map_mul, map_inv, hgh, inv_mul_cancel]
      rw [mem_leftCoset]
      have h4 : (P.x i)⁻¹ * g = ((P.x i)⁻¹ * h) * (h⁻¹ * g) := by group
      rw [h4]
      exact mul_mem hh (hVH i hgV)
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hdisj : ∀ i j : P.ι, i ≠ j →
      Disjoint (QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i))
        (QuotientGroup.mk' V '' leftCoset (P.x j) (P.H j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro q hqi hqj
    obtain ⟨a, ha, rfl⟩ := hqi
    obtain ⟨b, hb, hba⟩ := hqj
    have hmem : a ∈ QuotientGroup.mk' V ⁻¹'
        (QuotientGroup.mk' V '' leftCoset (P.x j) (P.H j)) := ⟨b, hb, hba⟩
    rw [hpre j] at hmem
    have hbot : a ∈ (⊥ : Set G) := (P.disjoint i j hij).le_bot ⟨ha, hmem⟩
    simp at hbot
  have hproper : ∀ i : P.ι, (P.H i).map (QuotientGroup.mk' V) ≠ ⊤ := by
    intro i htop
    have huniv : leftCoset (QuotientGroup.mk' V (P.x i)) ((P.H i).map (QuotientGroup.mk' V))
        = Set.univ := leftCoset_eq_univ_iff.mpr htop
    obtain ⟨j, hj⟩ : ∃ j : P.ι, j ≠ i := by
      by_contra h
      push_neg at h
      haveI : Subsingleton P.ι := ⟨fun a b => by rw [h a, h b]⟩
      have h1 : Nat.card P.ι ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr ‹Subsingleton P.ι›
      have h2 := P.two_le
      omega
    have hmem : QuotientGroup.mk' V (P.x j)
        ∈ leftCoset (QuotientGroup.mk' V (P.x i)) ((P.H i).map (QuotientGroup.mk' V)) := by
      rw [huniv]; trivial
    rw [← mk'_image_leftCoset] at hmem
    obtain ⟨a, ha, haq⟩ := hmem
    have hxji : P.x j ∈ leftCoset (P.x i) (P.H i) := by
      rw [← hpre i]; exact ⟨a, ha, haq⟩
    have hbot : P.x j ∈ (⊥ : Set G) :=
      (P.disjoint j i hj).le_bot ⟨by rw [mem_leftCoset]; simp, hxji⟩
    simp at hbot
  let P' : CosetPartition (G ⧸ V) :=
    { ι := P.ι
      fintype := P.fintype
      H := fun i => (P.H i).map (QuotientGroup.mk' V)
      x := fun i => QuotientGroup.mk' V (P.x i)
      proper := hproper
      two_le := P.two_le
      cover := by
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V q
        obtain ⟨i, hi⟩ := P.cover g
        exact ⟨i, by rw [← mk'_image_leftCoset V (P.x i) (P.H i)]; exact ⟨g, hi, rfl⟩⟩
      disjoint := by
        intro i j hij
        rw [← mk'_image_leftCoset V (P.x i) (P.H i),
          ← mk'_image_leftCoset V (P.x j) (P.H j)]
        exact hdisj i j hij }
  intro hHS
  obtain ⟨i, j, hij, hidx⟩ := hHS P'
  refine hdist i j hij ?_
  have hi : (P'.H i).index = (P.H i).index :=
    Subgroup.index_map_eq (P.H i) (QuotientGroup.mk'_surjective V)
      (by rw [QuotientGroup.ker_mk' V]; exact hVH i)
  have hj : (P'.H j).index = (P.H j).index :=
    Subgroup.index_map_eq (P.H j) (QuotientGroup.mk'_surjective V)
      (by rw [QuotientGroup.ker_mk' V]; exact hVH j)
  rw [hi, hj] at hidx
  exact hidx

theorem isHS_of_Hp_of_isHS_quotient {G : Type} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] {p : ℕ} (hp : p.Prime)
    (hV : IsPGroup p V) (hHS : IsHS (G ⧸ V)) (hHp : HpUnguarded p (G ⧸ V)) : IsHS G := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro P
  by_contra hcon
  push_neg at hcon
  have hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index :=
    fun i j hij h => hcon i j hij h
  have hcarddist : ∀ i j : P.ι, i ≠ j → Nat.card ↥(P.H i) ≠ Nat.card ↥(P.H j) := by
    intro i j hij h
    refine hdist i j hij ?_
    have h1 := Subgroup.index_mul_card (P.H i)
    have h2 := Subgroup.index_mul_card (P.H j)
    rw [h] at h1
    haveI : Nonempty ↥(P.H j) := ⟨⟨1, (P.H j).one_mem⟩⟩
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥(P.H j))) (h1.trans h2.symm)
  by_cases hcase : ∀ i, V ≤ P.H i
  · exact not_isHS_quotient_of_forall_le V P hcase hdist hHS
  · push_neg at hcase
    obtain ⟨i₀, hi₀⟩ := hcase
    haveI : Nonempty P.ι := by
      have h2 : 0 < Nat.card P.ι := by have := P.two_le; omega
      rw [Nat.card_eq_fintype_card] at h2
      exact Fintype.card_pos_iff.mp h2
    obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hV
    choose e he using fun i : P.ι =>
      IsPGroup.iff_card.mp (hV.of_injective (Subgroup.inclusion (inf_le_left : V ⊓ P.H i ≤ V))
        (Subgroup.inclusion_injective (inf_le_left : V ⊓ P.H i ≤ V)))
    obtain ⟨E, hEle, i₁, hi₁⟩ : ∃ E : ℕ, (∀ i : P.ι, E ≤ e i) ∧ ∃ i : P.ι, e i = E := by
      refine ⟨(Finset.univ : Finset P.ι).inf' Finset.univ_nonempty e,
        fun i => Finset.inf'_le e (Finset.mem_univ i), ?_⟩
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty e
      exact ⟨i, hi.symm⟩
    have hEd : E < d := by
      have h1 : e i₀ < d := by
        have hssub : ((V ⊓ P.H i₀ : Subgroup G) : Set G) ⊂ (V : Set G) := by
          rw [Set.ssubset_iff_subset_ne]
          refine ⟨fun x hx => hx.1, fun hEq => hi₀ fun v hv => ?_⟩
          have hv' : v ∈ ((V ⊓ P.H i₀ : Subgroup G) : Set G) := by rw [hEq]; exact hv
          exact ((Subgroup.mem_inf).mp hv').2
        have hlt : Nat.card ↥(V ⊓ P.H i₀) < Nat.card ↥V :=
          Set.Finite.card_lt_card (Set.toFinite (V : Set G)) hssub
        rw [he i₀, hd] at hlt
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
      have h2 : E ≤ e i₀ := hEle i₀
      omega
    have hcount : ∀ q : G ⧸ V,
        ∑ i : P.ι,
          (if q ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i) then p ^ (e i) else 0)
          = p ^ d := by
      intro q
      rw [← hd, ← sum_ite_card_eq_card P V q]
      exact Finset.sum_congr rfl fun i _ => by rw [he i]
    have hperq : ∀ q : G ⧸ V,
        ∑ i : {i : P.ι // e i = E},
          (if q ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i) then (1 : ZMod p) else 0)
          = 0 := by
      intro q
      rw [← sum_ite_and_eq_sum_subtype e E
        (fun i => q ∈ QuotientGroup.mk' V '' leftCoset (P.x i) (P.H i)) (1 : ZMod p)]
      exact zmod_sum_ite_eq_zero hp e hEle hEd _ (hcount q)
    have hcardtop : ∀ i : {i : P.ι // e i = E},
        Nat.card ↥(P.H (i : P.ι))
          = p ^ E * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) := by
      intro i
      rw [card_eq_card_inf_mul_card_map V (P.H (i : P.ι)), he (i : P.ι), i.2]
    have hidxoftop : ∀ i : {i : P.ι // e i = E},
        (P.H (i : P.ι)).index
          = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index * p ^ (d - E) := by
      intro i
      haveI : Nonempty ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) :=
        ⟨⟨1, ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).one_mem⟩⟩
      have hQ : Nat.card (G ⧸ V)
          = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index
            * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) :=
        (Subgroup.index_mul_card _).symm
      have hG : Nat.card G = (P.H (i : P.ι)).index * (p ^ E
          * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V))) := by
        rw [← hcardtop i]
        exact (Subgroup.index_mul_card (P.H (i : P.ι))).symm
      have hG2 : Nat.card G = Nat.card (G ⧸ V) * p ^ d := by
        rw [← hd, ← Subgroup.index_eq_card V]
        exact (Subgroup.index_mul_card V).symm
      have hmain : (P.H (i : P.ι)).index * (p ^ E
            * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)))
          = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index
            * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) * p ^ d :=
        hG.symm.trans (hG2.trans (by rw [hQ]))
      have hmain' : (P.H (i : P.ι)).index * p ^ E
            * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V))
          = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index * p ^ d
            * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) := by
        calc (P.H (i : P.ι)).index * p ^ E
              * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V))
            = (P.H (i : P.ι)).index * (p ^ E
              * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V))) := by ring
          _ = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index
              * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) * p ^ d := hmain
          _ = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index * p ^ d
              * Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) := by ring
      have hcancel : (P.H (i : P.ι)).index * p ^ E
          = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index * p ^ d :=
        Nat.mul_right_cancel (Nat.card_pos (α := ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V))))
          hmain'
      have hcancel' : (P.H (i : P.ι)).index * p ^ E
          = ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index * p ^ (d - E) * p ^ E := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hEd.le]
        exact hcancel
      exact Nat.mul_right_cancel (pow_pos hp.pos E) hcancel'
    have hcoset : ∀ i j : {i : P.ι // e i = E}, i ≠ j →
        leftCoset (QuotientGroup.mk' V (P.x (i : P.ι)))
            ((P.H (i : P.ι)).map (QuotientGroup.mk' V))
          ≠ leftCoset (QuotientGroup.mk' V (P.x (j : P.ι)))
            ((P.H (j : P.ι)).map (QuotientGroup.mk' V)) := by
      intro i j hij hEq
      have hne : (i : P.ι) ≠ (j : P.ι) := fun h => hij (Subtype.ext h)
      refine hcarddist (i : P.ι) (j : P.ι) hne ?_
      have hcard_eq : Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V))
          = Nat.card ↥((P.H (j : P.ι)).map (QuotientGroup.mk' V)) := by
        have h1 : Nat.card ↥(leftCoset (QuotientGroup.mk' V (P.x (i : P.ι)))
            ((P.H (i : P.ι)).map (QuotientGroup.mk' V)))
            = Nat.card ↥((P.H (i : P.ι)).map (QuotientGroup.mk' V)) := natCard_leftCoset _ _
        have h2 : Nat.card ↥(leftCoset (QuotientGroup.mk' V (P.x (j : P.ι)))
            ((P.H (j : P.ι)).map (QuotientGroup.mk' V)))
            = Nat.card ↥((P.H (j : P.ι)).map (QuotientGroup.mk' V)) := natCard_leftCoset _ _
        rw [hEq] at h1
        exact h1.symm.trans h2
      rw [hcardtop i, hcardtop j, hcard_eq]
    have hidx : ∀ i j : {i : P.ι // e i = E}, i ≠ j →
        ((P.H (i : P.ι)).map (QuotientGroup.mk' V)).index
          ≠ ((P.H (j : P.ι)).map (QuotientGroup.mk' V)).index := by
      intro i j hij h
      have hne : (i : P.ι) ≠ (j : P.ι) := fun hh => hij (Subtype.ext hh)
      refine hdist (i : P.ι) (j : P.ι) hne ?_
      rw [hidxoftop i, hidxoftop j, h]
    have hrel : (∑ i : {i : P.ι // e i = E}, (1 : ZMod p) •
        (fun q : G ⧸ V =>
          (leftCoset (QuotientGroup.mk' V (P.x (i : P.ι)))
            ((P.H (i : P.ι)).map (QuotientGroup.mk' V))).indicator (fun _ => (1 : ZMod p)) q))
        = 0 := by
      funext q
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, one_mul, Set.indicator_apply]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans (hperq q)
      rw [mk'_image_leftCoset]
    refine hHp {i : P.ι // e i = E}
      (fun i => QuotientGroup.mk' V (P.x (i : P.ι)))
      (fun i => (P.H (i : P.ι)).map (QuotientGroup.mk' V))
      ⟨⟨i₁, hi₁⟩⟩ hcoset hidx ?_
    simpa using hrel

theorem isHS_of_licosets_quotient {G : Type} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] {p : ℕ} (hp : p.Prime)
    (hV : IsPGroup p V) (hLI : LICosets p (G ⧸ V)) : IsHS G := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isHS_of_Hp_of_isHS_quotient V hp hV (isHS_of_licosets hp hLI)
    (HpUnguarded_of_licosets hLI (by
      haveI : NeZero p := ⟨hp.pos.ne'⟩
      exact one_ne_zero))

end HSC
