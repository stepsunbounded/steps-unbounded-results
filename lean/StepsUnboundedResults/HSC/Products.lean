/-
HSC/Products.lean

The direct-product index factorisation and the direct-power corollary.
-/
import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Extension
import StepsUnboundedResults.HSC.Assembly
import Mathlib.Tactic

open scoped Classical

universe u

namespace HSC

noncomputable def kerFstEquiv (G₁ G₂ : Type*) [Group G₁] [Group G₂] :
    ↥(MonoidHom.fst G₁ G₂).ker ≃* G₂ where
  toFun := fun x => (x : G₁ × G₂).2
  invFun := fun g => ⟨(1, g), by
    rw [show (MonoidHom.fst G₁ G₂).ker = (⊥ : Subgroup G₁).prod (⊤ : Subgroup G₂) from by
      ext x
      simp [Subgroup.mem_prod]]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (MonoidHom.mem_ker.mp x.2).symm
    · rfl
  right_inv := by
    intro g
    rfl
  map_mul' := by
    intro x y
    rfl

theorem indexSet_prod_subset {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] :
    ∀ n ∈ indexSet (G₁ × G₂), ∃ a ∈ indexSet G₁, ∃ b ∈ indexSet G₂, n = a * b := by
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := index_mem_mul_indexSet (MonoidHom.fst G₁ G₂).ker n hn
  have ha' : a ∈ indexSet G₁ :=
    indexSet_subset_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst G₁ G₂) fun x => ⟨(x, 1), rfl⟩) ha
  have hb' : b ∈ indexSet G₂ := indexSet_subset_of_mulEquiv (kerFstEquiv G₁ G₂) hb
  exact ⟨a, ha', b, hb', rfl⟩

def pow (G : Type u) : ℕ → Type u
  | 0 => PUnit
  | (r + 1) => pow G r × G

instance instGroupPow (G : Type u) [Group G] : ∀ r, Group (pow G r)
  | 0 => inferInstanceAs (Group PUnit)
  | (r + 1) => by
      letI := instGroupPow G r
      exact inferInstanceAs (Group (pow G r × G))

instance instFinitePow (G : Type u) [Finite G] : ∀ r, Finite (pow G r)
  | 0 => inferInstanceAs (Finite (PUnit : Type u))
  | (r + 1) => by
      letI := instFinitePow G r
      exact inferInstanceAs (Finite (pow G r × G))

theorem indexSet_pow_subset (G : Type u) [Group G] [Finite G] {A : Finset ℕ}
    (hG : ∀ n ∈ indexSet G, n ∈ MonoidGen A) :
    ∀ r, ∀ n ∈ indexSet (pow G r), n ∈ MonoidGen A
  | 0, n, hn => by
      obtain ⟨hdvd, -⟩ := mem_indexSet.mp hn
      have hcard : Nat.card (pow G 0) = 1 := by simp [pow]
      rw [hcard] at hdvd
      rw [Nat.dvd_one.mp hdvd]
      exact one_mem_MonoidGen A
  | (r + 1), n, hn => by
      obtain ⟨a, ha, b, hb, rfl⟩ := indexSet_prod_subset n hn
      exact MonoidGen.mul_mem (indexSet_pow_subset G hG r a ha) (hG b hb)

end HSC
