/-
HSC/CertPPAlt5.lean

Assembling `Cert-PP(A₅)` from its four anchors, then reducing it to `PP(A₅)` and `LI_p(A₅)`.
-/
import StepsUnboundedResults.HSC.A5Index
import StepsUnboundedResults.HSC.CertPP
import StepsUnboundedResults.HSC.CertPP10All
import StepsUnboundedResults.HSC.CertPP12All
import StepsUnboundedResults.HSC.PrivatePoints

open scoped Classical
open Finset

set_option maxHeartbeats 1000000

namespace HSC
namespace CertPPAlt5

abbrev P : Type := Equiv.Perm (Fin 5)
abbrev A5 : Subgroup P := alternatingGroup (Fin 5)

theorem mem_allSizes_ten {m : ℕ} (hdvd : m ∣ 60) (hm : m ≤ 10) : m ∈ CertPP10.allSizes := by
  have key : ∀ m ∈ Finset.range 11, m ∣ 60 → m ∈ CertPP10.allSizes := by decide
  exact key m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)) hdvd

theorem mem_allSizes_twelve {m : ℕ} (hdvd : m ∣ 60) (hm : m ≤ 12) : m ∈ CertPP12.allSizes := by
  have key : ∀ m ∈ Finset.range 13, m ∣ 60 → m ∈ CertPP12.allSizes := by decide
  exact key m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)) hdvd

theorem card_dvd_sixty (L : Subgroup Alt5) : Nat.card L ∣ 60 := by
  have h : Nat.card L ∣ Nat.card Alt5 := by simpa using Subgroup.card_dvd_of_le (le_top : L ≤ ⊤)
  rwa [nat_card_alt5] at h

theorem lcoset_eq_leftCoset {G : Type*} [Group G] (K : Subgroup G) (x : G) :
    CertPP.lcoset K x = leftCoset x K := rfl

theorem mem_map_subtype_leftCoset {L : Subgroup Alt5} {y z : Alt5} :
    A5.subtype z ∈ leftCoset (A5.subtype y) (L.map A5.subtype) ↔ z ∈ leftCoset y L := by
  rw [mem_leftCoset, mem_leftCoset, ← map_inv, ← map_mul,
    Subgroup.mem_map_iff_mem A5.subtype_injective]

theorem mem_cos_iff_leftCoset {K : Subgroup P} {x p : P} :
    p ∈ CertPP10Inputs.cos K x ↔ p ∈ leftCoset x K := by
  rw [CertPP10Inputs.mem_cos, mem_leftCoset]

theorem mem_cos12_iff_leftCoset {K : Subgroup P} {x p : P} :
    p ∈ CertPP12Inputs.cos K x ↔ p ∈ leftCoset x K := by
  rw [CertPP12Inputs.mem_cos, mem_leftCoset]

theorem card_filter_ne_one_of_two {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : ι → Prop)
    [DecidablePred Q] {i j : ι} (hij : i ≠ j) (hi : Q i) (hj : Q j) :
    (Finset.univ.filter Q).card ≠ 1 := by
  intro h1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hia : i = a := by
    have : i ∈ ({a} : Finset ι) := by rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    simpa using this
  have hja : j = a := by
    have : j ∈ ({a} : Finset ι) := by rw [← ha]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    simpa using this
  exact hij (hia.trans hja.symm)

theorem natCard_subtype_eq_one_iff {ι : Type*} [Fintype ι] (Q : ι → Prop) [DecidablePred Q] :
    Nat.card {a : ι // Q a} = 1 ↔ (Finset.univ.filter Q).card = 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_subtype_ne_one_of_two {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : ι → Prop)
    [DecidablePred Q] {i j : ι} (hij : i ≠ j) (hi : Q i) (hj : Q j) :
    Nat.card {a : ι // Q a} ≠ 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_filter_ne_one_of_two Q hij hi hj

theorem certPP_raw (S : ℕ) (hS : S ∈ ({4, 6, 10, 12} : Finset ℕ))
    (H : Subgroup Alt5) (hH : Nat.card H = S)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Subgroup Alt5) (x : ι → Alt5) (i₀ : ι)
    (hanchor : K i₀ = H) (hx₀ : x i₀ = 1)
    (hsize : ∀ i, Nat.card (K i) ≤ S)
    (hdist : ∀ i j, i ≠ j → Nat.card (K i) ≠ Nat.card (K j))
    (hcover : ∀ p : Alt5, (∃ i, p ∈ leftCoset (x i) (K i)) →
      ∃ i j, i ≠ j ∧ p ∈ leftCoset (x i) (K i) ∧ p ∈ leftCoset (x j) (K j)) : False := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · refine CertPP.certPP_anchor_four (G := Alt5) H (by simpa using hH) K x i₀ ?_
      (fun i => by simpa using hsize i) hdist ?_
    · show CertPP.lcoset (K i₀) (x i₀) = (H : Set Alt5)
      rw [lcoset_eq_leftCoset, hx₀, hanchor]
      ext g; simp [leftCoset]
    · intro g hcount
      have hcount'' : Nat.card {i : ι // g ∈ leftCoset (x i) (K i)} = 1 := by
        simpa only [lcoset_eq_leftCoset] using hcount
      have hcount' : (Finset.univ.filter (fun i => g ∈ leftCoset (x i) (K i))).card = 1 := by
        rw [← Fintype.card_subtype (fun i => g ∈ leftCoset (x i) (K i)), ← Nat.card_eq_fintype_card]
        exact hcount''
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcount'
      have ha_mem : a ∈ Finset.univ.filter (fun i => g ∈ leftCoset (x i) (K i)) := by
        rw [ha]; exact Finset.mem_singleton_self a
      have haP : g ∈ leftCoset (x a) (K a) := (Finset.mem_filter.mp ha_mem).2
      obtain ⟨i, j, hij, hi, hj⟩ := hcover g ⟨a, haP⟩
      exact card_subtype_ne_one_of_two (fun i => g ∈ leftCoset (x i) (K i)) hij hi hj hcount''
  · refine CertPP.certPP_anchor_six (G := Alt5) H (by simpa using hH) K x i₀ ?_
      (fun i => by simpa using hsize i) hdist ?_
    · show CertPP.lcoset (K i₀) (x i₀) = (H : Set Alt5)
      rw [lcoset_eq_leftCoset, hx₀, hanchor]
      ext g; simp [leftCoset]
    · intro g hcount
      have hcount'' : Nat.card {i : ι // g ∈ leftCoset (x i) (K i)} = 1 := by
        simpa only [lcoset_eq_leftCoset] using hcount
      have hcount' : (Finset.univ.filter (fun i => g ∈ leftCoset (x i) (K i))).card = 1 := by
        rw [← Fintype.card_subtype (fun i => g ∈ leftCoset (x i) (K i)), ← Nat.card_eq_fintype_card]
        exact hcount''
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcount'
      have ha_mem : a ∈ Finset.univ.filter (fun i => g ∈ leftCoset (x i) (K i)) := by
        rw [ha]; exact Finset.mem_singleton_self a
      have haP : g ∈ leftCoset (x a) (K a) := (Finset.mem_filter.mp ha_mem).2
      obtain ⟨i, j, hij, hi, hj⟩ := hcover g ⟨a, haP⟩
      exact card_subtype_ne_one_of_two (fun i => g ∈ leftCoset (x i) (K i)) hij hi hj hcount''
  · let Km : ι → Subgroup P := fun i => (K i).map A5.subtype
    let xm : ι → P := fun i => A5.subtype (x i)
    let szm : ι → ℕ := fun i => Nat.card (K i)
    have hcard : Nat.card (H.map A5.subtype) = 10 := by
      rw [Subgroup.card_map_of_injective A5.subtype_injective, hH]
    refine CertPP10All.anchor_ten_closed_all (H' := H.map A5.subtype) hcard
      ({ anchor := i₀
         K := Km
         x := xm
         sz := szm
         sz_eq := fun i => (Subgroup.card_map_of_injective A5.subtype_injective).symm
         sz_mem := fun i => mem_allSizes_ten (card_dvd_sixty (K i)) (by simpa [szm] using hsize i)
         sz_injective := fun i j hij => by by_contra hne; exact hdist i j hne hij
         K_le := fun i => by rintro p ⟨z, -, rfl⟩; exact z.2
         x_mem := fun i => by show A5.subtype (x i) ∈ A5; exact Subtype.property _
         anchor_K := by show (K i₀).map A5.subtype = H.map A5.subtype; rw [hanchor]
         anchor_x := by show A5.subtype (x i₀) = 1; rw [hx₀]; rfl
         cover := fun p hp hmem => ?_ } : CertPP10All.CosetSystemFor (H.map A5.subtype) ι)
    · obtain ⟨i, hi⟩ := hmem
      rw [mem_cos_iff_leftCoset] at hi
      have hi' : (⟨p, hp⟩ : Alt5) ∈ leftCoset (x i) (K i) :=
        (mem_map_subtype_leftCoset (L := K i) (y := x i)).mp hi
      obtain ⟨a, b, hab, ha, hb⟩ := hcover ⟨p, hp⟩ ⟨i, hi'⟩
      refine ⟨a, b, hab, ?_, ?_⟩
      · show p ∈ CertPP10Inputs.cos (Km a) (xm a)
        rw [mem_cos_iff_leftCoset]
        exact (mem_map_subtype_leftCoset (L := K a) (y := x a)).mpr ha
      · show p ∈ CertPP10Inputs.cos (Km b) (xm b)
        rw [mem_cos_iff_leftCoset]
        exact (mem_map_subtype_leftCoset (L := K b) (y := x b)).mpr hb
  · let Km : ι → Subgroup P := fun i => (K i).map A5.subtype
    let xm : ι → P := fun i => A5.subtype (x i)
    let szm : ι → ℕ := fun i => Nat.card (K i)
    have hcard : Nat.card (H.map A5.subtype) = 12 := by
      rw [Subgroup.card_map_of_injective A5.subtype_injective, hH]
    refine CertPP12All.anchor_twelve_closed_all (H' := H.map A5.subtype) hcard
      ({ anchor := i₀
         K := Km
         x := xm
         sz := szm
         sz_eq := fun i => (Subgroup.card_map_of_injective A5.subtype_injective).symm
         sz_mem := fun i => mem_allSizes_twelve (card_dvd_sixty (K i)) (by simpa [szm] using hsize i)
         sz_injective := fun i j hij => by by_contra hne; exact hdist i j hne hij
         K_le := fun i => by rintro p ⟨z, -, rfl⟩; exact z.2
         x_mem := fun i => by show A5.subtype (x i) ∈ A5; exact Subtype.property _
         anchor_K := by show (K i₀).map A5.subtype = H.map A5.subtype; rw [hanchor]
         anchor_x := by show A5.subtype (x i₀) = 1; rw [hx₀]; rfl
         cover := fun p hp hmem => ?_ } : CertPP12All.CosetSystemFor (H.map A5.subtype) ι)
    · obtain ⟨i, hi⟩ := hmem
      rw [mem_cos12_iff_leftCoset] at hi
      have hi' : (⟨p, hp⟩ : Alt5) ∈ leftCoset (x i) (K i) :=
        (mem_map_subtype_leftCoset (L := K i) (y := x i)).mp hi
      obtain ⟨a, b, hab, ha, hb⟩ := hcover ⟨p, hp⟩ ⟨i, hi'⟩
      refine ⟨a, b, hab, ?_, ?_⟩
      · show p ∈ CertPP12Inputs.cos (Km a) (xm a)
        rw [mem_cos12_iff_leftCoset]
        exact (mem_map_subtype_leftCoset (L := K a) (y := x a)).mpr ha
      · show p ∈ CertPP12Inputs.cos (Km b) (xm b)
        rw [mem_cos12_iff_leftCoset]
        exact (mem_map_subtype_leftCoset (L := K b) (y := x b)).mpr hb

theorem pp_alt5_of_max_size
    (hsieve : ∀ {ι : Type} [Fintype ι] [Nonempty ι] (c : ι → Alt5) (K : ι → Subgroup Alt5)
      (i₀ : ι),
      (∀ i j, i ≠ j → leftCoset (c i) (K i) ≠ leftCoset (c j) (K j)) →
      Function.Injective (fun i => Nat.card (K i)) →
      (∀ i, Nat.card (K i) ≤ Nat.card (K i₀)) →
      (∀ g : Alt5, Nat.card {i : ι // g ∈ leftCoset (c i) (K i)} ≠ 1) →
      Nat.card (K i₀) ∈ ({4, 6, 10, 12} : Finset ℕ)) : PP Alt5 := by
  classical
  intro ι _ c H hne hcoset hidx
  by_contra hno
  haveI : Nonempty ι := hne
  have hcover : ∀ (i : ι) (g : Alt5), g ∈ leftCoset (c i) (H i) →
      ∃ j, j ≠ i ∧ g ∈ leftCoset (c j) (H j) := by
    intro i g hg
    by_contra hcon
    push_neg at hcon
    exact hno ⟨i, g, hg, fun j hj => hcon j hj⟩
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun i => Nat.card (H i)) Finset.univ_nonempty
  have hmax' : ∀ i, Nat.card (H i) ≤ Nat.card (H i₀) := fun i => hmax i (Finset.mem_univ i)
  have hpos : ∀ i, 0 < Nat.card (H i) := fun i => Nat.card_pos_iff.mpr ⟨⟨1, (H i).one_mem⟩, inferInstance⟩
  have hinj : Function.Injective (fun i => Nat.card (H i)) := by
    intro i j hij
    have hij' : Nat.card (H i) = Nat.card (H j) := hij
    by_contra hne'
    refine hidx i j hne' ?_
    have hi : Nat.card (H j) * (H i).index = Nat.card Alt5 := by rw [← hij']; exact Subgroup.card_mul_index (H i)
    have hj : Nat.card (H j) * (H j).index = Nat.card Alt5 := Subgroup.card_mul_index (H j)
    exact Nat.mul_left_cancel (hpos j) (hi.trans hj.symm)
  have hnopriv : ∀ g : Alt5, Nat.card {i : ι // g ∈ leftCoset (c i) (H i)} ≠ 1 := by
    intro g h1
    have h1' : (Finset.univ.filter (fun i => g ∈ leftCoset (c i) (H i))).card = 1 :=
      (natCard_subtype_eq_one_iff (fun i => g ∈ leftCoset (c i) (H i))).mp h1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1'
    have ha_mem : a ∈ Finset.univ.filter (fun i => g ∈ leftCoset (c i) (H i)) := by rw [ha]; exact Finset.mem_singleton_self a
    have haP : g ∈ leftCoset (c a) (H a) := (Finset.mem_filter.mp ha_mem).2
    obtain ⟨j, hj, hjg⟩ := hcover a g haP
    exact card_subtype_ne_one_of_two (i := j) (j := a)
      (fun i => g ∈ leftCoset (c i) (H i)) hj hjg haP h1
  have hS : Nat.card (H i₀) ∈ ({4, 6, 10, 12} : Finset ℕ) :=
    hsieve (ι := ι) c H i₀ hcoset hinj hmax' hnopriv
  have htranslate : ∀ (i : ι) (g : Alt5),
      g ∈ leftCoset ((c i₀)⁻¹ * c i) (H i) ↔ (c i₀) * g ∈ leftCoset (c i) (H i) := by
    intro i g
    rw [mem_leftCoset, mem_leftCoset]
    have h : (c i)⁻¹ * ((c i₀) * g) = ((c i₀)⁻¹ * c i)⁻¹ * g := by group
    rw [h]
  refine certPP_raw (Nat.card (H i₀)) hS (H i₀) rfl H (fun i => (c i₀)⁻¹ * c i) i₀ rfl
    (by simp) hmax' (fun i j hij h => hij (hinj h)) ?_
  intro p hp
  obtain ⟨i, hi⟩ := hp
  have htrans : (c i₀) * p ∈ leftCoset (c i) (H i) := (htranslate i p).mp hi
  obtain ⟨j, hj, hjmem⟩ := hcover i ((c i₀) * p) htrans
  exact ⟨i, j, Ne.symm hj, hi, (htranslate j p).mpr hjmem⟩

theorem licosets_of_pp {G : Type*} [Group G] (h : PP G) (p : ℕ) : LICosets p G := by
  classical
  intro ι _ c H hcoset hidx
  rw [Fintype.linearIndependent_iff]
  intro g hg j₀
  by_contra hj₀
  let s : Finset ι := Finset.univ.filter (fun i => g i ≠ 0)
  have hs : j₀ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀⟩
  have hzero_of_not_mem : ∀ i, i ∉ s → g i = 0 := by
    intro i hi
    by_contra h0
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h0⟩)
  let ι' := {i : ι // i ∈ s}
  haveI : Nonempty ι' := ⟨⟨j₀, hs⟩⟩
  obtain ⟨i', x, hxmem, hxnot⟩ :=
    h ι' (fun i => c i.1) (fun i => H i.1) inferInstance
      (fun a b hab => hcoset a.1 b.1 (fun hh => hab (Subtype.ext hh)))
      (fun a b hab => hidx a.1 b.1 (fun hh => hab (Subtype.ext hh)))
  have hsingle : (∑ i : ι,
      (g i • (leftCoset (c i) (H i)).indicator (fun _ => (1 : ZMod p))) x) = g i'.1 := by
    rw [Finset.sum_eq_single i'.1]
    · simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hxmem, mul_one]
    · intro b _ hb
      by_cases hbs : b ∈ s
      · have hb' : (⟨b, hbs⟩ : ι') ≠ i' := fun hh => hb (congrArg Subtype.val hh)
        have hxb : x ∉ leftCoset (c b) (H b) := fun hmem => hxnot ⟨b, hbs⟩ hb' hmem
        simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hxb, mul_zero]
      · simp only [Pi.smul_apply, smul_eq_mul, hzero_of_not_mem b hbs, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_univ i'.1) hnot
  have hx := congrFun hg x
  rw [Finset.sum_apply, hsingle] at hx
  exact (Finset.mem_filter.mp i'.2).2 hx

end CertPPAlt5
end HSC
