module

public import BlockBand.Window.Count.SchurInertia
public import BlockBand.DeterminantScore.Sector.Coordinates

/-!
# A whole-row variation moves the inertia by at most one

A whole Hermitian row variation has at most one positive and one negative eigenvalue, so on an
attainable minor sector the restored row belongs to at most the three neighbouring full sectors.

* `negativeCount_le_add_one_of_quadForm_eq`: two Hermitian forms agreeing on a subspace of
  codimension at most one have negative counts differing by at most one (a negative-definite
  subspace of the first meets the hyperplane in a negative-definite subspace of the second);
* `negativeCount_row_le`: matrices agreeing off the row and column `a₀`;
* `sector_neighbour`: if `N_-(A) + n = α` then `N_-(B) + n ∈ {α - 1, α, α + 1}`;
* `hermOfCoord_row_agree`: `K + G(y)` and `K + G(y')` agree off row/column `a₀` when the
  coordinates `y`, `y'` agree on every coordinate not touching `a₀`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.PhysicalColumn

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Window.Count
open BlockBand.DeterminantScore.Sector

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Forms agreeing on a subspace of codimension `≤ 1` have negative counts within one. -/
theorem negativeCount_le_add_one_of_quadForm_eq {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (S : Submodule ℂ (ι → ℂ))
    (hS : Fintype.card ι ≤ Module.finrank ℂ S + 1)
    (heq : ∀ x ∈ S, quadForm A x = quadForm B x) :
    negativeCount A ≤ negativeCount B + 1 := by
  obtain ⟨VA, UA, hVA, _, hVAr, _⟩ := exists_negDef_nonneg_subspaces hA
  obtain ⟨VB, UB, _, hUB, _, hUBr⟩ := exists_negDef_nonneg_subspaces hB
  have hneg : NegDefOn B (VA ⊓ S) := fun x hx h0 => by
    rw [← heq x (Submodule.mem_inf.mp hx).2]
    exact hVA x (Submodule.mem_inf.mp hx).1 h0
  have h1 := finrank_add_le_of_negDef_nonneg hneg hUB
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq VA S
  have h3 : Module.finrank ℂ ↥(VA ⊔ S) ≤ Fintype.card ι := by
    rw [← Module.finrank_fintype_fun_eq_card (R := ℂ)]
    exact Submodule.finrank_le _
  omega

/-- The hyperplane `{x | x a₀ = 0}` has codimension at most one. -/
theorem card_le_finrank_ker_proj_add_one (a₀ : ι) :
    Fintype.card ι ≤
      Module.finrank ℂ (LinearMap.ker (LinearMap.proj a₀ : (ι → ℂ) →ₗ[ℂ] ℂ)) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj a₀ : (ι → ℂ) →ₗ[ℂ] ℂ)
  have h' : Module.finrank ℂ (LinearMap.range (LinearMap.proj a₀ : (ι → ℂ) →ₗ[ℂ] ℂ)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (LinearMap.proj a₀ : (ι → ℂ) →ₗ[ℂ] ℂ))
    rwa [Module.finrank_self] at this
  rw [Module.finrank_fintype_fun_eq_card] at h
  omega

/-- Matrices agreeing off row and column `a₀` have the same form on `{x | x a₀ = 0}`. -/
theorem quadForm_eq_of_row {A B : Matrix ι ι ℂ} (a₀ : ι)
    (hAB : ∀ a b, a ≠ a₀ → b ≠ a₀ → A a b = B a b) {x : ι → ℂ} (hx : x a₀ = 0) :
    quadForm A x = quadForm B x := by
  unfold quadForm
  congr 1
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a = a₀
  · subst ha; simp [hx]
  · congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b = a₀
    · subst hb; simp [hx]
    · rw [hAB a b ha hb]

/-- **Row variation.** Hermitian matrices agreeing off row/column `a₀` have negative counts
within one. -/
theorem negativeCount_row_le {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (a₀ : ι) (hAB : ∀ a b, a ≠ a₀ → b ≠ a₀ → A a b = B a b) :
    negativeCount A ≤ negativeCount B + 1 :=
  negativeCount_le_add_one_of_quadForm_eq hA hB _ (card_le_finrank_ker_proj_add_one a₀)
    fun x hx => quadForm_eq_of_row a₀ hAB (by simpa using hx)

/-- **Three neighbouring sectors.** -/
theorem sector_neighbour {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (a₀ : ι) (hAB : ∀ a b, a ≠ a₀ → b ≠ a₀ → A a b = B a b) {n α : ℕ}
    (h : negativeCount A + n = α) :
    negativeCount B + n = α - 1 ∨ negativeCount B + n = α ∨ negativeCount B + n = α + 1 := by
  have h1 := negativeCount_row_le hA hB a₀ hAB
  have h2 := negativeCount_row_le hB hA a₀ fun a b ha hb => (hAB a b ha hb).symm
  omega

variable {m : ℕ}

/-- `K + G(y)` and `K + G(y')` agree off row/column `a₀` when `y`, `y'` agree on the coordinates
not touching `a₀`. -/
theorem hermOfCoord_row_agree (K : Matrix (Fin m) (Fin m) ℂ) (a₀ : Fin m)
    {y y' : HermCoord m → ℝ} (hy : ∀ c : HermCoord m, c.1 ≠ a₀ → c.2 ≠ a₀ → y c = y' c) :
    ∀ a b, a ≠ a₀ → b ≠ a₀ → (K + hermOfCoord y) a b = (K + hermOfCoord y') a b := by
  intro a b ha hb
  simp only [Matrix.add_apply, hermOfCoord_apply, hy (a, a) ha ha, hy (a, b) ha hb,
    hy (b, a) hb ha]

end BlockBand.DeterminantScore.PhysicalColumn
