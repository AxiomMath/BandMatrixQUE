module

public import BlockBand.DeterminantScore.WeylIntegrationCorner

/-!
# Weyl integration: reduction of the bordered-matrix law to a diagonal corner

* `ComplexUnitaryInvarianceStatement`: Lebesgue measure on `ℂ^n` is invariant under unitary
  matrices (`v ↦ W v`);
* `DiagonalBorderLawStatement`: the bordered-matrix law for a diagonal corner `diag(μ)`, `μ`
  strictly increasing (the arrowhead computation).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector Polynomial
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

variable {n : ℕ}

/-- **Unitary invariance of Lebesgue measure on `ℂ^n`** (standard volume, `ℂ ≅ ℝ²`). -/
def ComplexUnitaryInvarianceStatement : Prop :=
  ∀ n : ℕ, ∀ W : Matrix.unitaryGroup (Fin n) ℂ, ∀ F : (Fin n → ℂ) → ℝ≥0∞, Measurable F →
    ∫⁻ v, F ((W : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) = ∫⁻ v, F v

/-- **The bordered-matrix law for a diagonal corner** (the arrowhead computation:
`det(z - [[diag μ, w],[w*, a]]) = (z - a)∏(z - μ_k) - Σ_i |w_i|² ∏_{k≠i}(z - μ_k)`, polar
coordinates `dw_i = π d|w_i|²` and the change of variables `(a, |w|²) ↦ λ` onto the strictly
interlacing `λ`, Jacobian `Δ(λ)/Δ(μ)`). For strictly increasing `μ` and measurable `g ≥ 0`:
`∫_{ℂ^n} ∫_ℝ g(λ([[diag μ, v],[v*, a]])) da dv = π^n ∫_{λ ≻ μ} (Δ(λ)/Δ(μ)) g(λ) dλ`. -/
def DiagonalBorderLawStatement : Prop :=
  ∀ n : ℕ, ∀ g : (Fin (n + 1) → ℝ) → ℝ≥0∞, Measurable g → ∀ μ : Fin n → ℝ, StrictMono μ →
    ∫⁻ v : Fin n → ℂ, ∫⁻ a : ℝ,
        g (fun k => freshEigenvalue (borderHerm (diagonal fun i => (μ i : ℂ)) v a) k) =
      ENNReal.ofReal (Real.pi ^ n) * interlaceAverage g μ

theorem continuous_borderHerm (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun p : (Fin n → ℂ) × ℝ => borderHerm M p.1 p.2 := by
  refine continuous_matrix fun r s => ?_
  induction r using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last => simp only [borderHerm, Matrix.of_apply, Fin.lastCases_last]; fun_prop
    | cast j =>
      simp only [borderHerm, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact continuous_star.comp ((continuous_apply j).comp continuous_fst)
  | cast i =>
    induction s using Fin.lastCases with
    | last =>
      simp only [borderHerm, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact (continuous_apply i).comp continuous_fst
    | cast j =>
      simp only [borderHerm, Matrix.of_apply, Fin.lastCases_castSucc]
      exact continuous_const

/-- Increasing eigenvalues depend only on the characteristic polynomial. -/
theorem freshEigenvalue_eq_of_charpoly_eq {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    (fun k => freshEigenvalue A k) = fun k => freshEigenvalue B k := by
  refine EigenDensity.freshEigenvalue_eq_of_charpoly hA (EigenDensity.monotone_freshEigenvalue hB)
    ?_
  rw [h, hB.charpoly_eq]
  obtain ⟨e, he⟩ := SpectralConvexity.exists_equiv_freshEigenvalue hB
  rw [← Equiv.prod_comp e]
  simp_rw [he]
  rfl

theorem isHermitian_borderHerm {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian)
    (v : Fin n → ℂ) (a : ℝ) : (borderHerm M v a).IsHermitian := by
  ext r s
  induction r using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last => simp [borderHerm]
    | cast j => simp [borderHerm]
  | cast i =>
    induction s using Fin.lastCases with
    | last => simp [borderHerm]
    | cast j => simpa [borderHerm] using congrFun (congrFun hM i) j

/-- `D = diag(W, 1)` is unitary when `W` is. -/
theorem borderHerm_unit_conjTranspose_mul {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ * W = 1) :
    (borderHerm W 0 1)ᴴ * borderHerm W 0 1 = 1 := by
  ext r s
  have hWe : ∀ i j, ∑ k, star (W k i) * W k j = (1 : Matrix (Fin n) (Fin n) ℂ) i j := fun i j => by
    rw [← hW]; simp [Matrix.mul_apply]
  induction r using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last => simp [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc]
    | cast j =>
      simp [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc, (Fin.castSucc_ne_last j).symm]
  | cast i =>
    induction s using Fin.lastCases with
    | last =>
      simp [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last i]
    | cast j =>
      simp only [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.conjTranspose_apply,
        Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, Pi.zero_apply, star_zero,
        mul_zero, add_zero]
      rw [hWe, Matrix.one_apply, Matrix.one_apply]
      simp

/-- `D [[M', v'],[v'*, a]] D* = [[W M' W*, W v'],[(W v')*, a]]`, `D = diag(W, 1)`. -/
theorem borderHerm_conj (W M' : Matrix (Fin n) (Fin n) ℂ) (v' : Fin n → ℂ) (a : ℝ) :
    borderHerm W 0 1 * borderHerm M' v' a * (borderHerm W 0 1)ᴴ =
      borderHerm (W * M' * Wᴴ) (W *ᵥ v') a := by
  ext r s
  induction r using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last => simp [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc]
    | cast j =>
      simp [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct,
        star_sum, mul_comm]
  | cast i =>
    induction s using Fin.lastCases with
    | last => simp [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]
    | cast j =>
      simp [borderHerm, Matrix.mul_apply, Fin.sum_univ_castSucc, Finset.sum_mul]

/-- **Reduction of the bordered-matrix law to a diagonal corner.** -/
theorem borderEigenLaw_of_diagonal (hU : ComplexUnitaryInvarianceStatement)
    (hD : DiagonalBorderLawStatement) : BorderEigenLawStatement := by
  intro n g hg M hM hμ
  obtain ⟨W, hW⟩ := exists_conjDiag_freshEigenvalue hM
  set μ := fun k => freshEigenvalue M k
  set Wm : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ)
  have hWW : Wmᴴ * Wm = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.UnitaryGroup.star_mul_self W
  have hWW' : Wm * Wmᴴ = 1 := mul_eq_one_comm.1 hWW
  set Λ : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => (μ i : ℂ)
  have hΛ : Λ.IsHermitian := by simp [Λ, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  have hpt : ∀ v a, (fun k => freshEigenvalue (borderHerm M v a) k) =
      fun k => freshEigenvalue (borderHerm Λ (Wmᴴ *ᵥ v) a) k := by
    intro v a
    have hconj : borderHerm M v a =
        borderHerm Wm 0 1 * borderHerm Λ (Wmᴴ *ᵥ v) a * (borderHerm Wm 0 1)ᴴ := by
      rw [borderHerm_conj, Matrix.mulVec_mulVec, hWW', Matrix.one_mulVec]
      exact congrArg (fun A => borderHerm A v a) hW
    refine freshEigenvalue_eq_of_charpoly_eq (isHermitian_borderHerm hM v a)
      (isHermitian_borderHerm hΛ _ a) ?_
    rw [hconj, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      borderHerm_unit_conjTranspose_mul hWW, Matrix.one_mul]
  simp_rw [hpt]
  have hjoint : Measurable fun p : (Fin n → ℂ) × ℝ =>
      g (fun k => freshEigenvalue (borderHerm Λ p.1 p.2) k) :=
    hg.comp (EigenDensity.measurable_freshEigs.comp (continuous_borderHerm Λ).measurable)
  have hF : Measurable fun v : Fin n → ℂ =>
      ∫⁻ a : ℝ, g (fun k => freshEigenvalue (borderHerm Λ v a) k) :=
    hjoint.lintegral_prod_right' (ν := volume)
  have hWs : (Wmᴴ : Matrix (Fin n) (Fin n) ℂ) = ((star W : Matrix.unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) := by
    simp [Wm, Matrix.star_eq_conjTranspose]
  rw [hWs, hU n (star W) _ hF]
  exact hD n g hg μ hμ

/-- **The Weyl integration formula from unitary invariance on `ℂ^n` and the diagonal-corner
bordered law** (corner Fubini, the interlacing integral, the induction and the angular reduction
are proved). -/
theorem weylIntegration_of_diagonal (hU : ComplexUnitaryInvarianceStatement)
    (hD : DiagonalBorderLawStatement) : EigenDensity.WeylIntegrationStatement :=
  weylIntegration_of_border cornerFubini (borderEigenLaw_of_diagonal hU hD)

end BlockBand.DeterminantScore.WeylIntegration
