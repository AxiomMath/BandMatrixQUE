module

public import BlockBand.SourceProcess.ComplexSourceLaw.ExtTag

/-!
# The trace and Hilbert–Schmidt norm of `A_Q` as conditional Gaussian moments

The identity `E(ξξ*|G) = Q/W²` holds exactly:
for `A_Q = W⁻²Q^{1/2}GQ^{1/2}` (`extendedSourceMatrix`) and unit-mass tags,
* `trace_extended`: `Tr A_Q = Σ_k (q_k/W) E_g[ξ_k*Gξ_k]`;
* `hs_extended`: `‖A_Q‖²_HS = Σ_{k,l} (q_k/W)(q_l/W) · W⁻² Σ_{a,b}|G_{(k,a),(l,b)}|²`, the inner
  factor being `E_{g,h}|ξ_k*Gξ'_l|²` (`lintegral_tagY_sq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws

variable {W n : ℕ}

theorem extended_apply (b E : ℝ) (q : Fin n → ℝ) (ω : GrowthPath W) (x y : Fin n × Fin W) :
    extendedSourceMatrix b E W n q ω x y = ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (q x.1) : ℝ) : ℂ) * (fullInverse b E W n ω).toBlocks₁₁ x y *
        ((Real.sqrt (q y.1) : ℝ) : ℂ)) := by
  simp [extendedSourceMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem trace_extended (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) (ω : GrowthPath W) :
    (extendedSourceMatrix b E W n q ω).trace = ∑ k, ((q k / W : ℝ) : ℂ) *
      ∫ g, tagForm (fullInverse b E W n ω).toBlocks₁₁ (tagVector W n k 1 g)
        (tagVector W n k 1 g) ∂circularVectorLaw (Fin W) := by
  simp_rw [integral_tagZ]
  rw [Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, extended_apply]
  have hs : ((Real.sqrt (q k) : ℝ) : ℂ) * ((Real.sqrt (q k) : ℝ) : ℂ) = (q k : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hq k)]
  push_cast
  linear_combination (((W : ℂ) ^ 2)⁻¹ * (fullInverse b E W n ω).toBlocks₁₁ (k, a) (k, a)) * hs

theorem norm_sq_extended (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) (ω : GrowthPath W)
    (x y : Fin n × Fin W) :
    ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2 = (((W : ℝ) ^ 2)⁻¹) ^ 2 *
      (q x.1 * q y.1 * ‖(fullInverse b E W n ω).toBlocks₁₁ x y‖ ^ 2) := by
  rw [extended_apply, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((W : ℝ) ^ 2)⁻¹)]
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hq _), Real.sq_sqrt (hq _)]
  ring

theorem hs_extended (b E : ℝ) (q : Fin n → ℝ) (hq : ∀ k, 0 ≤ q k) (ω : GrowthPath W) :
    ∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2 = ∑ k, ∑ l, q k / W * (q l / W) *
      (((W : ℝ)⁻¹) ^ 2 * ∑ a, ∑ b', ‖(fullInverse b E W n ω).toBlocks₁₁ (k, a) (l, b')‖ ^ 2) := by
  simp_rw [norm_sq_extended b E q hq ω, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

end BlockBand.SourceProcess.ComplexSourceLaw
