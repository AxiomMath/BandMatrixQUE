module

public import BlockBand.Transmission.Bridge.Complete

/-!
# The absorbed path pencil `H_j - E + i diag ε` is almost surely invertible

The absorbed analogue of `Bridge.ae_isUnit_pathPencil_growth` (which is the case `κ ≡ 0`), for an
**arbitrary** absorption profile `κ` (no sign condition): newest block first,
`F_{j+1} = [[A_j - E + iε₀, C_nᴴ], [C_n, F_j]]` (`absorbedPencil_succ_submatrix`), so
`det F_{j+1} = det F_j · det(A_j + C_j)` with `C_j = -E + iε₀ - C_nᴴF_j⁻¹C_n` a function of the
past, and the GUE block `A_j` is independent of the past. Needed because the bridge recursion
`pathNearSchur_succ_eq_freshSchur` assumes invertible pencils, and absorptions `ε_i = 0` are
allowed by the `absorbedMoment` clause (so `Bridge.isUnit_pathPencil_of_pos` does not apply).

Main result: `ae_isUnit_absorbedPencil_growth` (`b < 1/2`, `W ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge
open scoped ENNReal NNReal Matrix

variable {W : ℕ}

theorem layerAbsorption_succ (κ : ℝ → ℝ) (j : ℕ) (i : Fin j) :
    layerAbsorption W κ (j + 1) i.succ = layerAbsorption W κ j i := by
  simp only [layerAbsorption, Fin.val_succ]
  rw [show j + 1 - (i.val + 1) = j - i.val by omega]

theorem absorptionDiag_succ_submatrix (κ : ℝ → ℝ) (j : ℕ) :
    (absorptionDiag W (layerAbsorption W κ (j + 1))).submatrix (headEquiv j W) (headEquiv j W) =
      Matrix.fromBlocks ((((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1) 0 0
        (absorptionDiag W (layerAbsorption W κ j)) := by
  ext (x | ⟨i, x⟩) (y | ⟨k, y⟩)
  · simp [absorptionDiag, headEquiv_inl, Matrix.diagonal_apply, Matrix.one_apply]
  · simp [absorptionDiag, headEquiv_inl, headEquiv_inr, (Fin.succ_ne_zero k).symm]
  · simp [absorptionDiag, headEquiv_inl, headEquiv_inr]
  · simp only [absorptionDiag, Matrix.submatrix_apply, headEquiv_inr, Matrix.diagonal_apply,
      Matrix.fromBlocks_apply₂₂, Prod.mk.injEq, Fin.succ_inj, layerAbsorption_succ]

/-- **Block form of the absorbed pencil**, newest block first. -/
theorem absorbedPencil_succ_submatrix (E : ℝ) (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    (pathPencil E (layerAbsorption W κ (j + 1)) (pathAt W (j + 1) ω)).submatrix (headEquiv j W)
        (headEquiv j W) =
      Matrix.fromBlocks
        (ω.1 j - (E : ℂ) • 1 + (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1)
        (nearCol W j ω)ᴴ (nearCol W j ω) (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)) := by
  have hadd : ∀ A B : Matrix (Fin (j + 1) × Fin W) (Fin (j + 1) × Fin W) ℂ,
      (A + B).submatrix (headEquiv j W) (headEquiv j W) =
        A.submatrix (headEquiv j W) (headEquiv j W) + B.submatrix (headEquiv j W) (headEquiv j W) :=
    fun _ _ => rfl
  rw [pathPencil, hadd, pathMatrix_succ_submatrix, absorptionDiag_succ_submatrix,
    Matrix.fromBlocks_add, pathPencil]
  simp only [add_zero]

/-- The absorbed pencil as a function of the past coordinates. -/
def pastPencilAbs (E : ℝ) (κ : ℝ → ℝ) (W j : ℕ)
    (p : (Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)) :
    Matrix (Fin j × Fin W) (Fin j × Fin W) ℂ :=
  pastPencil E W j p + absorptionDiag W (layerAbsorption W κ j)

/-- The absorbed Schur shift `C_j = -E + iε₀ - C_nᴴF_j⁻¹C_n` as a function of the past. -/
def pastShiftAbs (E : ℝ) (κ : ℝ → ℝ) (W j : ℕ)
    (p : (Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)) :
    Matrix (Fin W) (Fin W) ℂ :=
  let Cn : Matrix (Fin j × Fin W) (Fin W) ℂ := fun a y => pathPortCoupling (pathOfPast W j p) a (0, y)
  (-((E : ℂ) • 1) + (((layerAbsorption W κ (j + 1) 0 : ℝ) : ℂ) * Complex.I) • 1 -
    Cnᴴ * (pastPencilAbs E κ W j p)⁻¹ * Cn)

theorem measurable_pastPencilAbs (E : ℝ) (κ : ℝ → ℝ) (j : ℕ) :
    Measurable (pastPencilAbs E κ W j) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pastPencilAbs, Matrix.add_apply]
  exact (measurable_pastPencil E j).eval_matrix.add measurable_const

theorem measurable_pastShiftAbs (E : ℝ) (κ : ℝ → ℝ) (j : ℕ) :
    Measurable (pastShiftAbs E κ W j) := by
  have hCn : Measurable fun p : (Fin j → Matrix (Fin W) (Fin W) ℂ) ×
      (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ) =>
      (fun a y => pathPortCoupling (pathOfPast W j p) a (0, y) :
        Matrix (Fin j × Fin W) (Fin W) ℂ) :=
    Measurable.of_eval_matrix _ fun x y =>
      ((measurable_pathPortCoupling j).comp (measurable_pathOfPast j)).eval_matrix
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [pastShiftAbs, Matrix.sub_apply]
  exact measurable_const.sub (measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_conjTranspose' hCn) (measurable_matrix_inv.comp
      (measurable_pastPencilAbs E κ j))) hCn).eval_matrix

theorem absorbedPencil_eq_past (E : ℝ) (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    pathPencil E (layerAbsorption W κ j) (pathAt W j ω) = pastPencilAbs E κ W j (pastCoords W j ω) := by
  rw [pastPencilAbs, ← pathPencil_eq_past]; rfl

/-- **Schur step**: `det F_{j+1} = det F_j · det(A_j + C_j)` when `F_j` is invertible. -/
theorem det_absorbedPencil_succ (E : ℝ) (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W)
    (hD : IsUnit (pathPencil E (layerAbsorption W κ j) (pathAt W j ω))) :
    (pathPencil E (layerAbsorption W κ (j + 1)) (pathAt W (j + 1) ω)).det =
      (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)).det *
        ((freshSample W j ω).1 0 + pastShiftAbs E κ W j (pastCoords W j ω)).det := by
  let : Invertible (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)) := hD.invertible
  rw [← Matrix.det_submatrix_equiv_self (headEquiv j W), absorbedPencil_succ_submatrix,
    Matrix.det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  congr 2
  rw [pastShiftAbs, ← absorbedPencil_eq_past]
  simp only [freshSample, pathAt_eq_pathOfPast, Function.comp]
  have : nearCol W j ω = fun a y => pathPortCoupling (pathOfPast W j (pastCoords W j ω)) a (0, y) := by
    funext a y; simp only [nearCol, pathAt_eq_pathOfPast, Function.comp]
  rw [this]
  abel

/-- The absorbed pencil is singular only on a null set, at every length. -/
theorem growth_det_absorbedPencil_null {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ)
    (κ : ℝ → ℝ) : ∀ j : ℕ, growthPathLaw W b
      {ω | (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)).det = 0} = 0
  | 0 => by simp [Matrix.det_isEmpty]
  | j + 1 => by
    set T : Set (((Fin j → Matrix (Fin W) (Fin W) ℂ) × (Fin (j + 1) → Matrix (Fin W) (Fin W) ℂ)) ×
        LayerSample W .oneBlockOnePort) :=
      {q | (pastPencilAbs E κ W j q.1).det ≠ 0 ∧ (q.2.1 0 + pastShiftAbs E κ W j q.1).det = 0}
    have hT : MeasurableSet T := by
      refine ((measurableSet_singleton 0).compl.preimage
        (measurable_det.comp ((measurable_pastPencilAbs E κ j).comp measurable_fst))).inter
        ((measurableSet_singleton 0).preimage (measurable_det.comp ?_))
      refine Measurable.of_eval_matrix _ fun x y => ?_
      simp only [Matrix.add_apply]
      exact (Matrix.measurable_apply.comp ((measurable_pi_apply 0).comp
        (measurable_fst.comp measurable_snd))).add
        ((measurable_pastShiftAbs E κ j).comp measurable_fst).eval_matrix
    have hsub : {ω | (pathPencil E (layerAbsorption W κ (j + 1)) (pathAt W (j + 1) ω)).det = 0} ⊆
        {ω | (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)).det = 0} ∪
          (fun ω => (pastCoords W j ω, freshSample W j ω)) ⁻¹' T := by
      intro ω hω
      by_cases h : (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)).det = 0
      · exact Or.inl h
      · right
        have hD : IsUnit (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)) :=
          (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
        simp only [Set.mem_ofPred_eq, det_absorbedPencil_succ E κ j ω hD, mul_eq_zero] at hω
        refine ⟨by rwa [← absorbedPencil_eq_past], hω.resolve_left h⟩
    refine measure_mono_null hsub (measure_union_null
      (growth_det_absorbedPencil_null hb hW E κ j) ?_)
    rw [← Measure.map_apply ((measurable_pastCoords W j).prodMk (measurable_freshSample W j)) hT,
      growthPathLaw_map_past_fresh, Measure.measure_prod_null hT]
    refine Filter.Eventually.of_forall fun p => ?_
    have hA := ae_det_gue_add_ne_zero W (gueVariance_ne_zero hb hW) (pastShiftAbs E κ W j p)
    rw [ae_iff, ← freshLaw_map_block W b, Measure.map_apply (by
      exact (measurable_pi_apply 0).comp measurable_fst)] at hA
    · simp only [Pi.zero_apply]
      refine measure_mono_null (fun f hf => ?_) hA
      simpa [T] using hf.2
    · exact (measurableSet_singleton 0).compl.compl.preimage (measurable_det.comp
        (Measurable.of_eval_matrix _ fun x y => Matrix.measurable_apply.add measurable_const))

/-- **The absorbed pencils are almost surely invertible at every length** (`b < 1/2`, `W ≥ 1`,
any absorption profile `κ`). -/
theorem ae_isUnit_absorbedPencil_growth {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ)
    (κ : ℝ → ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, IsUnit (pathPencil E (layerAbsorption W κ j) (pathAt W j ω)) := by
  rw [ae_all_iff]
  intro j
  rw [ae_iff]
  simpa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] using
    growth_det_absorbedPencil_null hb hW E κ j

end BlockBand.Transmission.PathScalar
