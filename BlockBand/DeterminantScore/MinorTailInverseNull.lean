module

public import BlockBand.DeterminantScore.MinorTailRow

/-!
# The deleted-row minor is almost surely invertible

The minor `B = V*MV` of `M = K + G` on `w^⊥` has `V_B = Tr B⁻² < ∞` almost surely, so the
totalized inverse at a singular minor does not affect the integrals of the inverse spread bound.

`ae_minor_det_ne_zero_gue`: for any `K` on `Fin m`, `m = k + 1`, a unit `w`, an orthonormal
frame `V` of `w^⊥` (`V*V = 1`, `V*w = 0`) and `t > 0`, `det(V*(K + G)V) ≠ 0` for
`GUE_m(t)`-almost every `G`.

Proof: rotate by the unitary `F = [w | V]` (`frameCompletion`, unitary invariance of `G_m(t)` in
`hermOfCoord` coordinates), so `V*(K + FYF*)V = (F*KF + Y)` restricted to the minor indices
(`frameCompletion_succ`); split the coordinates into the deleted row and the minor
(`lintegral_hermGaussian_row`); the minor coordinates have the law `G_k(t)`, under which
`K'_B + G_B` is almost surely invertible (`ae_minor_det_ne_zero`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTailInverse

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.GaussianGradient BlockBand.DeterminantScore.PhysicalColumn
open BlockBand.DeterminantScore.MinorTail
open scoped NNReal ENNReal

/-- The minor block of a row-split coordinate point is the coordinate matrix of the minor
coordinates. -/
theorem hermOfCoord_rowPoint_submatrix {k : ℕ} (t : ℝ≥0) (u : RowIdx (k + 1) → ℝ)
    (w : RestIdx (k + 1) → ℝ) :
    (hermOfCoord (rowPoint (hermSd (k + 1) t) u w)).submatrix Fin.succ Fin.succ =
      hermOfCoord (restVal t w) := by
  ext a b
  simp [hermOfCoord, rowPoint, IsRow, restVal, restEquiv, restOf, hermSd_succ, Fin.succ_ne_zero]

/-- **The deleted-row minor is almost surely invertible**: for any `K` on `Fin m`, `m = k + 1`,
unit `w`, orthonormal frame `V` of `w^⊥` and `t > 0`, `det(V*(K + G)V) ≠ 0` for `GUE_m(t)`-a.e.
`G`. -/
theorem ae_minor_det_ne_zero_gue {m k : ℕ} (hmk : m = k + 1) {t : ℝ≥0} (ht : 0 < t)
    (K : Matrix (Fin m) (Fin m) ℂ) {w : Fin m → ℂ} (hw : l2Norm w = 1)
    {V : Matrix (Fin m) (Fin k) ℂ} (hV : Vᴴ * V = 1) (hVw : Vᴴ *ᵥ w = 0) :
    ∀ᵐ G ∂gueMeasure (Fin m) t, (Vᴴ * (K + G) * V).det ≠ 0 := by
  subst hmk
  set F := frameCompletion w V
  have hF : Fᴴ * F = 1 := frameCompletion_unitary hw hV hVw
  have hFF : F * Fᴴ = 1 := mul_eq_one_comm.mp hF
  have hF' : (Fᴴ)ᴴ * Fᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hFF
  set K' := Fᴴ * K * F
  set S : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := {G | (Vᴴ * (K + G) * V).det = 0}
  have hdetc : Continuous fun G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ =>
      (Vᴴ * (K + G) * V).det :=
    Continuous.matrix_det ((continuous_const.matrix_mul (continuous_const.add continuous_id)).matrix_mul
      continuous_const)
  have hS : MeasurableSet S := (isClosed_eq hdetc continuous_const).measurableSet
  have hf : Measurable (S.indicator (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → ℝ≥0∞)) :=
    measurable_one.indicator hS
  -- the rotated minor
  have hrot : ∀ Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
      Vᴴ * (K + (Fᴴ)ᴴ * Y * Fᴴ) * V = (K' + Y).submatrix Fin.succ Fin.succ := by
    intro Y
    rw [← frameCompletion_succ w V, conjTranspose_conjTranspose]
    congr 1
    simp only [K', Matrix.mul_add, Matrix.add_mul]
    congr 1
    rw [show Fᴴ * (F * Y * Fᴴ) * F = (Fᴴ * F) * Y * (Fᴴ * F) by simp only [Matrix.mul_assoc],
      hF, Matrix.one_mul, Matrix.mul_one]
  set g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → ℝ≥0∞ :=
    fun X => if (X.submatrix Fin.succ Fin.succ).det = 0 then 1 else 0
  have hg : Measurable g := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (isClosed_eq (Continuous.matrix_det (continuous_id.matrix_submatrix _ _))
      continuous_const).measurableSet
  have hgc : Measurable fun y : HermCoord (k + 1) → ℝ => g (K' + hermOfCoord y) :=
    hg.comp (continuous_const.add continuous_hermOfCoord).measurable
  rw [ae_iff]
  simp only [ne_eq, not_not]
  change gueMeasure (Fin (k + 1)) t S = 0
  rw [← lintegral_indicator_one hS, ← map_hermOfCoord_hermGaussian,
    lintegral_map hf continuous_hermOfCoord.measurable,
    ← lintegral_hermGaussian_unitary t hF' _ hf]
  have e1 : ∀ y : HermCoord (k + 1) → ℝ,
      S.indicator 1 ((Fᴴ)ᴴ * hermOfCoord y * Fᴴ) = g (K' + hermOfCoord y) := by
    intro y
    simp only [S, g, Set.indicator_apply, Set.mem_ofPred_eq, hrot, Pi.one_apply]
  simp_rw [e1]
  rw [lintegral_hermGaussian_row t _ hgc]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [ae_minor_det_ne_zero ht (K'.submatrix Fin.succ Fin.succ)] with x hx
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun u => ?_)
  have e2 : (K' + hermOfCoord (rowPoint (hermSd (k + 1) t) u x)).submatrix Fin.succ Fin.succ =
      K'.submatrix Fin.succ Fin.succ + hermOfCoord (restVal t x) := by
    rw [← hermOfCoord_rowPoint_submatrix t u x]; rfl
  simp only [g, e2, hx, ↓reduceIte, Pi.zero_apply]

end BlockBand.DeterminantScore.MinorTailInverse
