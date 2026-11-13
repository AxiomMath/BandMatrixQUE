module

public import BlockBand.DeterminantScore.SignedRowSpreadMoments
public import BlockBand.DeterminantScore.RowInverseTrace

/-!
# The signed row spread

The signed row integral identity and bound `SignedRowSpreadStatement`, at a fixed minor `B`.

Proof:
* `rowSchur_sq_mul_trace_eq` (block inversion, `Row.rowMatrix_inverse_square_polynomial`): off the
  Schur pole `a = 0`, `a²U = a²V_B + 2a·y*C_B³y + (1 + y*C_B²y)²`;
* `ae_rowSchur_ne_zero`: the pole `a = 0` is null under the row law (for fixed `y` it is one value
  of the nondegenerate Gaussian `x`); there the Lean inverse is `0`, so only an a.e. identity is
  used;
* `hasInt_rowSchur_sq`, `hasInt_rowPoly`: the complex Gaussian contractions
  (`wick_one`, `wick_two`, moments of `x`) integrate the polynomial term by
  term on `N(0,t) ⊗ CN(0,I)` after the scaling `y = √t g` (`rowLaw_eq_map`);
* the identity `first = second` and the bound are `Row.signed_row_matrix_square_identity` and
  `Row.signed_row_matrix_square_le` (completed matrix square, `1 + tV_B ≤ q_B²/t`).

The cubic and quartic terms are combined at fixed `B`; nothing is integrated over `B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SignedRowSpread

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

variable {k : ℕ}

theorem continuous_quad_re (A : Matrix (Fin k) (Fin k) ℂ) :
    Continuous fun y : Fin k → ℂ => (star y ⬝ᵥ (A *ᵥ y)).re := by
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def]
  fun_prop

theorem continuous_rowSchur (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) :
    Continuous (rowSchur μ B) := by
  unfold rowSchur
  exact (continuous_const.add continuous_fst).sub ((continuous_quad_re B⁻¹).comp continuous_snd)

/-- The Schur pole `a = 0` is null under the row law. -/
theorem ae_rowSchur_ne_zero (t : ℝ≥0) (ht : 0 < t) (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) :
    ∀ᵐ z ∂rowLaw k t, rowSchur μ B z ≠ 0 := by
  have hmeas : MeasurableSet {z | rowSchur μ B z = 0} :=
    (isClosed_eq (continuous_rowSchur μ B) continuous_const).measurableSet
  rw [ae_iff]
  simp only [ne_eq, not_not]
  unfold rowLaw
  have hprob : IsProbabilityMeasure
      (BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin k)) := by
    rw [coarea_circularVectorLaw_eq]
    infer_instance
  have hprob' : IsProbabilityMeasure ((BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw
      (Fin k)).map fun g => (Real.sqrt (t : ℝ) : ℂ) • g) :=
    inferInstance
  rw [Measure.prod_apply_symm hmeas]
  have := nullSingletonClass_gaussianReal (μ := 0) ht.ne'
  have hsl : ∀ y : Fin k → ℂ, (fun x : ℝ => (x, y)) ⁻¹' {z | rowSchur μ B z = 0} =
      {(star y ⬝ᵥ (B⁻¹ *ᵥ y)).re - μ} := by
    intro y
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, rowSchur]
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  simp [hsl]

/-- Block inversion off the Schur pole: `a²U = a²V_B + 2a y*C_B³y + (1 + y*C_B²y)²`. -/
theorem rowSchur_sq_mul_trace_eq (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) (z : ℝ × (Fin k → ℂ)) (ha : rowSchur μ B z ≠ 0) :
    rowSchur μ B z ^ 2 * ((rowMatrix μ z.1 z.2 B)⁻¹ * (rowMatrix μ z.1 z.2 B)⁻¹).trace.re =
      rowSchur μ B z ^ 2 * (B⁻¹ * B⁻¹).trace.re +
        2 * rowSchur μ B z * (star z.2 ⬝ᵥ ((B⁻¹ ^ 3) *ᵥ z.2)).re +
        (1 + (star z.2 ⬝ᵥ ((B⁻¹ ^ 2) *ᵥ z.2)).re) ^ 2 := by
  have hrow : rowMatrix μ z.1 z.2 B = Row.rowMatrix B (((μ + z.1 : ℝ)) : ℂ) z.2 := rfl
  have hs : Row.schurScalar B⁻¹ (((μ + z.1 : ℝ)) : ℂ) z.2 = ((rowSchur μ B z : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Row.schurScalar, rowSchur]
    · simp [Row.schurScalar, rowSchur, quad_im_eq_zero B⁻¹ hB.inv z.2]
  have hne : Row.schurScalar B⁻¹ (((μ + z.1 : ℝ)) : ℂ) z.2 ≠ 0 := by
    rw [hs]
    exact_mod_cast ha
  have key := Row.rowMatrix_inverse_square_polynomial B hB (isUnit_iff_ne_zero.2 hdet) _ z.2 hne
  rw [← hrow, hs, Row.hermitian_quadratic_eq_ofReal _ (hB.inv.pow 3) z.2,
    Row.hermitian_quadratic_eq_ofReal _ (hB.inv.pow 2) z.2,
    Row.hermitian_trace_eq_ofReal _ (hB.inv.pow 2)] at key
  have e := congrArg Complex.re key
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul] at e
  rw [← pow_two (rowMatrix μ z.1 z.2 B)⁻¹, ← pow_two B⁻¹, e]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im, pow_two, mul_zero,
    sub_zero, add_zero, Complex.add_im]

/-- Pulling a continuous integrand back from `rowLaw k t` to `N(0,t) ⊗ CN(0,I)`. -/
theorem hasInt_rowLaw_of_pullback (t : ℝ≥0) {G : ℝ × (Fin k → ℂ) → ℝ} (hG : Continuous G)
    {c : ℝ}
    (h : HasInt ((gaussianReal 0 t).prod (BlockBand.Counting.circularVectorLaw (Fin k)))
      (fun w => G (w.1, (Real.sqrt (t : ℝ) : ℂ) • BlockBand.Counting.circularVector w.2)) c) :
    HasInt (rowLaw k t) G c := by
  have hφ : Measurable (Prod.map (id : ℝ → ℝ) fun z : Fin k → ℝ × ℝ =>
      (Real.sqrt (t : ℝ) : ℂ) • BlockBand.Counting.circularVector z) :=
    measurable_id.prodMap
      ((continuous_const_smul _).comp (continuous_circularVector (Fin k))).measurable
  rw [rowLaw_eq_map]
  exact ⟨(integrable_map_measure hG.aestronglyMeasurable hφ.aemeasurable).2 h.1, by
    rw [integral_map hφ.aemeasurable hG.aestronglyMeasurable]; exact h.2⟩

/-- `E a² = q_B²`. -/
theorem hasInt_rowSchur_sq (t : ℝ≥0) (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) (hB : B.IsHermitian) :
    HasInt (rowLaw k t) (fun z => rowSchur μ B z ^ 2)
      ((μ - t * (B⁻¹).trace.re) ^ 2 + t + t ^ 2 * (B⁻¹ * B⁻¹).trace.re) := by
  have hC := hB.inv
  apply hasInt_rowLaw_of_pullback (G := fun z => rowSchur μ B z ^ 2) t
    ((continuous_rowSchur μ B).pow 2)
  have h1 := (hasInt_gauss_shift_sq t μ).prod
    (hasInt_const (P := BlockBand.Counting.circularVectorLaw (Fin k)) 1)
  have h2 := (hasInt_gauss_shift t μ).prod ⟨(wick_one B⁻¹).1, (wick_one B⁻¹).2⟩
  have h3 := (hasInt_const (P := gaussianReal 0 t) 1).prod
    ⟨(wick_two B⁻¹ B⁻¹ hC hC).1, (wick_two B⁻¹ B⁻¹ hC hC).2⟩
  refine ((h1.sub (h2.const_mul (2 * t))).add (h3.const_mul ((t : ℝ) ^ 2))).congr ?_ ?_
  · intro w
    simp only [rowSchur, quad_re_sqrt_smul _ (t : ℝ) t.coe_nonneg]
    ring
  · ring

/-- The row polynomial `a²V_B + 2a y*C_B³y + (1 + y*C_B²y)²`. -/
def rowPoly (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) (z : ℝ × (Fin k → ℂ)) : ℝ :=
  rowSchur μ B z ^ 2 * (B⁻¹ * B⁻¹).trace.re +
    2 * rowSchur μ B z * (star z.2 ⬝ᵥ ((B⁻¹ ^ 3) *ᵥ z.2)).re +
    (1 + (star z.2 ⬝ᵥ ((B⁻¹ ^ 2) *ᵥ z.2)).re) ^ 2

theorem continuous_rowPoly (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) : Continuous (rowPoly μ B) := by
  unfold rowPoly
  have h0 := continuous_rowSchur μ B
  have h3 : Continuous fun z : ℝ × (Fin k → ℂ) => (star z.2 ⬝ᵥ ((B⁻¹ ^ 3) *ᵥ z.2)).re :=
    (continuous_quad_re (B⁻¹ ^ 3)).comp continuous_snd
  have h2 : Continuous fun z : ℝ × (Fin k → ℂ) => (star z.2 ⬝ᵥ ((B⁻¹ ^ 2) *ᵥ z.2)).re :=
    (continuous_quad_re (B⁻¹ ^ 2)).comp continuous_snd
  fun_prop

/-- `E[a²V_B + 2a y*C_B³y + (1 + y*C_B²y)²] = V_Bq_B² + (1+tV_B)² + 2tδ_B Tr C_B³ - t² Tr C_B⁴`. -/
theorem hasInt_rowPoly (t : ℝ≥0) (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) (hB : B.IsHermitian) :
    HasInt (rowLaw k t) (rowPoly μ B)
      ((B⁻¹ * B⁻¹).trace.re * ((μ - t * (B⁻¹).trace.re) ^ 2 + t +
          t ^ 2 * (B⁻¹ * B⁻¹).trace.re) +
        (1 + t * (B⁻¹ * B⁻¹).trace.re) ^ 2 +
        2 * t * (μ - t * (B⁻¹).trace.re) * (B⁻¹ ^ 3).trace.re -
        t ^ 2 * (B⁻¹ ^ 4).trace.re) := by
  have hC := hB.inv
  have hC2 := hC.pow 2
  have hC3 := hC.pow 3
  set V := (B⁻¹ * B⁻¹).trace.re with hV
  have hV2 : (B⁻¹ ^ 2).trace.re = V := by rw [hV, pow_two]
  have h13 : (B⁻¹ * B⁻¹ ^ 3).trace = (B⁻¹ ^ 4).trace := by rw [← pow_succ']
  have h22 : (B⁻¹ ^ 2 * B⁻¹ ^ 2).trace = (B⁻¹ ^ 4).trace := by rw [← pow_add]
  apply hasInt_rowLaw_of_pullback t (continuous_rowPoly μ B)
  let ν := BlockBand.Counting.circularVectorLaw (Fin k)
  let γ := gaussianReal 0 t
  have c1 : HasInt ν (fun _ => (1 : ℝ)) 1 := hasInt_const 1
  have g1 : HasInt γ (fun _ => (1 : ℝ)) 1 := hasInt_const 1
  have w1 := fun A : Matrix (Fin k) (Fin k) ℂ =>
    (⟨(wick_one A).1, (wick_one A).2⟩ : HasInt ν _ _)
  have w2 := fun (A A' : Matrix (Fin k) (Fin k) ℂ) (hA : A.IsHermitian) (hA' : A'.IsHermitian) =>
    (⟨(wick_two A A' hA hA').1, (wick_two A A' hA hA').2⟩ : HasInt ν _ _)
  have t1 := ((hasInt_gauss_shift_sq t μ).prod c1).const_mul V
  have t2 := ((hasInt_gauss_shift t μ).prod (w1 B⁻¹)).const_mul (2 * t * V)
  have t3 := (g1.prod (w2 B⁻¹ B⁻¹ hC hC)).const_mul ((t : ℝ) ^ 2 * V)
  have t4 := ((hasInt_gauss_shift t μ).prod (w1 (B⁻¹ ^ 3))).const_mul (2 * t)
  have t5 := (g1.prod (w2 B⁻¹ (B⁻¹ ^ 3) hC hC3)).const_mul (2 * (t : ℝ) ^ 2)
  have t6 := (g1.prod (w1 (B⁻¹ ^ 2))).const_mul (2 * t)
  have t7 := (g1.prod (w2 (B⁻¹ ^ 2) (B⁻¹ ^ 2) hC2 hC2)).const_mul ((t : ℝ) ^ 2)
  refine ((((((t1.sub t2).add t3).add t4).sub t5).add (hasInt_const (P := γ.prod ν) 1)).add t6
    |>.add t7).congr ?_ ?_
  · intro w
    simp only [rowPoly, rowSchur, quad_re_sqrt_smul _ (t : ℝ) t.coe_nonneg]
    ring
  · rw [h13, h22, hV2]
    ring

/-- **The signed row spread** `SignedRowSpreadStatement`: the second moment of the Schur
complement and the signed row identity and bound, at a fixed Hermitian invertible minor. -/
theorem signedRowSpread : SignedRowSpreadStatement := by
  intro k t μ B ht hB hdet t' CB V δ q2 F X first second
  have hC : CB.IsHermitian := hB.inv
  have hsq := hasInt_rowSchur_sq t μ B hB
  have hpoly := hasInt_rowPoly t μ B hB
  have hae : F =ᵐ[rowLaw k t] rowPoly μ B := by
    filter_upwards [ae_rowSchur_ne_zero t ht μ B] with z hz
    exact rowSchur_sq_mul_trace_eq μ B hB hdet z hz
  have hV2 : (CB ^ 2).trace.re = V := by simp only [V, pow_two]
  have hid := Row.signed_row_matrix_square_identity CB δ t'
  have hle := Row.signed_row_matrix_square_le CB hC δ t' (by exact_mod_cast ht)
  rw [hV2] at hid hle
  have hfs : first = second := by
    simp only [first, second, X]
    exact hid
  refine ⟨hsq.2, hpoly.1.congr hae.symm, ?_, hfs, ?_⟩
  · rw [integral_congr_ae hae, hpoly.2]
  · rw [← hfs]
    exact hle

end BlockBand.DeterminantScore.SignedRowSpread
