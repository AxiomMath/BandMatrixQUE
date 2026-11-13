module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Phase
public import BlockBand.Critical.RelativeVectors.AbstractFlow.Backward

/-!
# Assembly helpers: phase algebra, factor covariance, test classes

* `rowPhase β S = P_β S` (`(P_β S)_{ij} = e^{iβ_i} S_{ij}`), with `arrayMul (P_β S) G = P_β (S G)`
  (`arrayMul_rowPhase`) and `(P_β S)(P_β S)ᴴ = P_β (S Sᴴ) P_β⁻¹` (`rowPhase_mul_conjTranspose`).
* `labelPhaseMatrix α` (`M ↦ P_α⁻¹ M P_α`) fixes `1`, commutes with `1 - ·` and with
  `M ↦ M Mᴴ`; it preserves the modulus of entries and the `ℓ²` contraction rate.
* `sqrtOneSub_mul_conjTranspose_of_contracts`: if `‖K v‖₂ ≤ q ‖v‖₂` with `0 ≤ q < 1`, then
  `√(1 - KKᴴ) √(1 - KKᴴ)ᴴ = 1 - KKᴴ`; `sqrtOneSub_one_mul`: the same for `K = 1`.
* `isC2BoundedBy_of_isArrayC2Bounded`: the Euclidean test class `IsArrayC2Bounded C` gives the
  sup-norm class `IsC2BoundedBy (C (1 + N r + (N r)²))`.
* `backwardPropagator_congr_Icc`: `BackwardPropagator` only sees the values on `[a, c]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.ReferenceFlow

variable {N r : ℕ}

/-!
## Row phases
-/

/-- The row phase `P_β S`: `(P_β S)_{ij} = e^{iβ_i} S_{ij}`. -/
def rowPhase (β : Fin N → ℝ) (S : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => Complex.exp ((β i : ℂ) * Complex.I) * S i j

/-- `(P_β S) G = P_β (S G)` on arrays. -/
theorem arrayMul_rowPhase (β : Fin N → ℝ) (S : Matrix (Fin N) (Fin N) ℂ)
    (G : Fin N → Fin r → ℂ) : arrayMul (rowPhase β S) G = labelPhase β (arrayMul S G) := by
  funext i q
  simp only [arrayMul, rowPhase, labelPhase, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- `conj (e^{it}) = e^{-it}`. -/
theorem star_exp_ofReal_mul_I (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I)) = Complex.exp (-((t : ℂ) * Complex.I)) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

/-- `conj (e^{-it}) = e^{it}`. -/
theorem star_exp_neg_ofReal_mul_I (t : ℝ) :
    star (Complex.exp (-((t : ℂ) * Complex.I))) = Complex.exp ((t : ℂ) * Complex.I) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, neg_neg]

/-- `e^{-it} e^{it} = 1`. -/
theorem exp_neg_mul_exp (t : ℝ) :
    Complex.exp (-((t : ℂ) * Complex.I)) * Complex.exp ((t : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- `(P_β S)(P_β S)ᴴ = P_β (S Sᴴ) P_β⁻¹ = labelPhaseMatrix (-β) (S Sᴴ)`. -/
theorem rowPhase_mul_conjTranspose (β : Fin N → ℝ) (S : Matrix (Fin N) (Fin N) ℂ) :
    rowPhase β S * (rowPhase β S)ᴴ = labelPhaseMatrix (-β) (S * Sᴴ) := by
  ext i j
  simp only [rowPhase, labelPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, star_mul', star_exp_ofReal_mul_I, Pi.neg_apply, Complex.ofReal_neg, neg_mul,
    neg_neg, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-!
## Phase conjugation
-/

/-- `P_α⁻¹ 1 P_α = 1`. -/
theorem labelPhaseMatrix_one (α : Fin N → ℝ) :
    labelPhaseMatrix α (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [labelPhaseMatrix, Matrix.of_apply, Matrix.one_apply_eq, mul_one]
    exact exp_neg_mul_exp (α i)
  · simp only [labelPhaseMatrix, Matrix.of_apply, Matrix.one_apply_ne h, mul_zero, zero_mul]

/-- `P_α⁻¹ (A - B) P_α = P_α⁻¹ A P_α - P_α⁻¹ B P_α`. -/
theorem labelPhaseMatrix_sub (α : Fin N → ℝ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    labelPhaseMatrix α (A - B) = labelPhaseMatrix α A - labelPhaseMatrix α B := by
  ext i j
  simp only [labelPhaseMatrix, Matrix.of_apply, Matrix.sub_apply]
  ring

/-- `P_α⁻¹ (M Mᴴ) P_α = (P_α⁻¹ M P_α)(P_α⁻¹ M P_α)ᴴ`. -/
theorem labelPhaseMatrix_mul_conjTranspose (α : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    labelPhaseMatrix α (M * Mᴴ) = labelPhaseMatrix α M * (labelPhaseMatrix α M)ᴴ := by
  ext i j
  simp only [labelPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_mul', star_exp_ofReal_mul_I, star_exp_neg_ofReal_mul_I, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := exp_neg_mul_exp (α k)
  linear_combination (-(Complex.exp (-((α i : ℂ) * Complex.I)) * M i k * star (M j k) *
    Complex.exp ((α j : ℂ) * Complex.I))) * h1

/-- Phase conjugation preserves the modulus of the entries. -/
theorem norm_labelPhaseMatrix_apply (α : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ‖labelPhaseMatrix α M i j‖ = ‖M i j‖ := by
  simp only [labelPhaseMatrix, Matrix.of_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Multiplying the coordinates by phases preserves the `ℓ²` norm. -/
theorem l2Norm_phase (α : Fin N → ℝ) (v : Fin N → ℂ) :
    l2Norm (fun j => Complex.exp ((α j : ℂ) * Complex.I) * v j) = l2Norm v := by
  simp only [l2Norm, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `(P_α⁻¹ M P_α) v = P_α⁻¹ (M (P_α v))`, so the `ℓ²` norms agree. -/
theorem l2Norm_labelPhaseMatrix_mulVec (α : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) :
    l2Norm (labelPhaseMatrix α M *ᵥ v) =
      l2Norm (M *ᵥ fun j => Complex.exp ((α j : ℂ) * Complex.I) * v j) := by
  have h : labelPhaseMatrix α M *ᵥ v = fun i => Complex.exp ((-α i : ℝ) * Complex.I) *
      (M *ᵥ fun j => Complex.exp ((α j : ℂ) * Complex.I) * v j) i := by
    funext i
    simp only [Matrix.mulVec, dotProduct, labelPhaseMatrix, Matrix.of_apply, Finset.mul_sum,
      Complex.ofReal_neg, neg_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h, l2Norm_phase]

/-- Phase conjugation preserves the `ℓ²` contraction rate. -/
theorem l2Norm_labelPhaseMatrix_mulVec_le {α : Fin N → ℝ} {M : Matrix (Fin N) (Fin N) ℂ} {q : ℝ}
    (hM : ∀ w : Fin N → ℂ, l2Norm (M *ᵥ w) ≤ q * l2Norm w) (v : Fin N → ℂ) :
    l2Norm (labelPhaseMatrix α M *ᵥ v) ≤ q * l2Norm v := by
  rw [l2Norm_labelPhaseMatrix_mulVec, ← l2Norm_phase α v]
  exact hM _

/-!
## The factor `√(1 - KKᴴ)`
-/

/-- `l2Norm v ^ 2 = Σ_k |v_k|²`. -/
theorem l2Norm_sq (v : Fin N → ℂ) : l2Norm v ^ 2 = ∑ k, ‖v k‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- If `‖K v‖₂ ≤ q ‖v‖₂` with `0 ≤ q < 1`, then `opNorm (K Kᴴ) < 1`. -/
theorem opNorm_mul_conjTranspose_lt_one {K : Matrix (Fin N) (Fin N) ℂ} {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hK : ∀ v : Fin N → ℂ, l2Norm (K *ᵥ v) ≤ q * l2Norm v) :
    opNorm (K * Kᴴ) < 1 := by
  have h : ∀ v : Fin N → ℂ, ∑ k, ‖(K *ᵥ v) k‖ ^ 2 ≤ q ^ 2 * ∑ k, ‖v k‖ ^ 2 := by
    intro v
    rw [← l2Norm_sq, ← l2Norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hK v) 2
  refine (opNorm_mul_conjTranspose_le K (sq_nonneg q) h).trans_lt ?_
  nlinarith

/-- **Covariance of the factor.** If `‖K v‖₂ ≤ q ‖v‖₂` with `0 ≤ q < 1`, then
`√(1 - KKᴴ) √(1 - KKᴴ)ᴴ = 1 - KKᴴ`. -/
theorem sqrtOneSub_mul_conjTranspose_of_contracts {K : Matrix (Fin N) (Fin N) ℂ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hK : ∀ v : Fin N → ℂ, l2Norm (K *ᵥ v) ≤ q * l2Norm v) :
    sqrtOneSub (K * Kᴴ) * (sqrtOneSub (K * Kᴴ))ᴴ = 1 - K * Kᴴ := by
  have hA := opNorm_mul_conjTranspose_lt_one hq0 hq1 hK
  rw [(sqrtOneSub_isHermitian hA (isHermitian_mul_conjTranspose_self' K)).eq]
  exact sqrtOneSub_mul_self hA

/-- **Covariance of the factor at `K = 1`**: `√(1 - 1) √(1 - 1)ᴴ = 1 - 1 1ᴴ` (both are `0`). -/
theorem sqrtOneSub_one_mul :
    sqrtOneSub ((1 : Matrix (Fin N) (Fin N) ℂ) * 1ᴴ) * (sqrtOneSub ((1 : Matrix (Fin N) (Fin N) ℂ) * 1ᴴ))ᴴ =
      1 - (1 : Matrix (Fin N) (Fin N) ℂ) * 1ᴴ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact matrix_subsingleton_zero hN _ _
  · have h0 : sqrtOneSub ((1 : Matrix (Fin N) (Fin N) ℂ) * 1ᴴ) = 0 := by
      rw [Matrix.conjTranspose_one, mul_one]
      exact sqrtOneSub_of_not_lt (by rw [opNorm_one_of_pos hN]; exact lt_irrefl 1)
    rw [h0, zero_mul, Matrix.conjTranspose_one, mul_one, sub_self]

/-- `√(1 - 1 1ᴴ) = 0` applied to an array, for every `N`. -/
theorem arrayMul_sqrtOneSub_one (G : Fin N → Fin r → ℂ) :
    arrayMul (sqrtOneSub ((1 : Matrix (Fin N) (Fin N) ℂ) * 1ᴴ)) G = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · funext i
    exact absurd i.2 (by omega)
  · rw [Matrix.conjTranspose_one, mul_one,
      sqrtOneSub_of_not_lt (by rw [opNorm_one_of_pos hN]; exact lt_irrefl 1)]
    funext i q
    simp only [arrayMul, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, Pi.zero_apply]

/-!
## Test classes
-/

/-- **From the Euclidean test class to the sup-norm class.** `IsArrayC2Bounded C f` gives
`IsC2BoundedBy (C (1 + N r + (N r)²)) f` (sup norm on `ℂ^{N×r}`). -/
theorem isC2BoundedBy_of_isArrayC2Bounded {C : ℝ} {f : (Fin N → Fin r → ℂ) → ℝ}
    (hf : IsArrayC2Bounded C f) :
    IsC2BoundedBy (C * (1 + N * r + (N * r) * (N * r))) f := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf.bound 0)
  have hNr : (0 : ℝ) ≤ N * r := by positivity
  refine ⟨hf.contDiff, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · refine (hf.bound z).trans ?_
    nlinarith [mul_nonneg hC hNr, mul_nonneg (mul_nonneg hC hNr) hNr]
  · refine (AbstractFlow.norm_fderiv_le_of_array hf z).trans ?_
    nlinarith [mul_nonneg hC hNr, mul_nonneg (mul_nonneg hC hNr) hNr]
  · have e : ‖iteratedFDeriv ℝ 2 f z‖ = ‖fderiv ℝ (fderiv ℝ f) z‖ := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
    rw [e]
    refine (AbstractFlow.norm_fderiv_fderiv_le_of_array hf z).trans ?_
    nlinarith [mul_nonneg hC hNr, mul_nonneg (mul_nonneg hC hNr) hNr]

/-!
## Backward propagators
-/

/-- `BackwardPropagator L a c` depends only on the values of the solution on `[a, c]`. -/
theorem backwardPropagator_congr_Icc {L : ℝ → Fin N → Fin N → ℝ} {a c : ℝ} (hac : a ≤ c)
    {P Q : ℝ → Fin N → Fin N → ℝ} (hP : BackwardPropagator L a c P)
    (hPQ : ∀ s ∈ Icc a c, P s = Q s) : BackwardPropagator L a c Q := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨(hPQ c ⟨hac, le_rfl⟩).symm.trans h1, h2.congr fun s hs => (hPQ s hs).symm,
    fun x hx => ?_⟩
  have hev : P =ᶠ[𝓝 x] Q := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with s hs
    exact hPQ s (Ioo_subset_Icc_self hs)
  rw [← hPQ x (Ioo_subset_Icc_self hx)]
  exact (h3 x hx).congr_of_eventuallyEq hev.symm

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
