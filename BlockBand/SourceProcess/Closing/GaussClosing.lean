module

public import BlockBand.SourceProcess.Closing.HardyMain
public import BlockBand.SourceProcess.ComplexSourceLaw.GaussianForms

/-!
# The Gaussian closing error

For an orthogonal projection `A`, a pairing with `ΠΠᴴ = A`, `𝕊𝕊ᴴ = 1` and `N^n → 0`, a source
map `F` and a standard complex Gaussian `h`, the closing map satisfies
`E_z E_h ‖F C(z) h - F h‖² = 2 Re Tr(F A Fᴴ)` (`gaussian_closing_error`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm
open scoped Matrix ComplexConjugate

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-- `E_h Σ_r |(Mh)_r|² = Re Tr(MMᴴ)`. -/
theorem integral_normSq_mulVec (M : Matrix ρ ι ℂ) :
    ∫ g, ∑ r, ‖(M *ᵥ g) r‖ ^ 2 ∂circularVectorLaw ι = (M * Mᴴ).trace.re := by
  simp_rw [mulVec, dotProduct]
  rw [integral_finsetSum _ fun r _ => ComplexSourceLaw.integrable_normSq_lin (M r)]
  simp_rw [ComplexSourceLaw.integral_normSq_lin]
  simp only [Matrix.trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show M r a * star (M r a) = M r a * (starRingEnd ℂ) (M r a) from rfl, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.ofReal_re]

omit [DecidableEq ι] in
/-- `∫ Tr(F X(θ) Fᴴ) = Tr(F (E_z X) Fᴴ)` for continuous `X`. -/
theorem integral_trace_conj (F : Matrix ρ ι ℂ) {X : ℝ → Matrix ι ι ℂ} (hX : Continuous X) :
    ∫ θ, (F * X θ * Fᴴ).trace ∂phaseLaw = (F * phaseAvg X * Fᴴ).trace := by
  simp only [Matrix.trace, diag_apply, mul_apply, phaseAvg, of_apply]
  rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun b _ =>
    (integrable_finsetSum _ fun a _ => ((integrable_entry hX a b).const_mul _)).mul_const _]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_finsetSum _ fun b _ =>
    (integrable_finsetSum _ fun a _ => ((integrable_entry hX a b).const_mul _)).mul_const _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_finsetSum _ fun a _ => (integrable_entry hX a b).const_mul _]
  simp_rw [integral_const_mul]

/-- **The Gaussian closing error**: `E_z E_h ‖F C(z) h - F h‖² = 2 Re Tr(F A Fᴴ)`. -/
theorem gaussian_closing_error {S A Pi : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : S * Sᴴ = 1)
    (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) (F : Matrix ρ ι ℂ) :
    ∫ θ, (∫ g, ∑ r, ‖((F * closingMap S A Pi (phase θ)) *ᵥ g - F *ᵥ g) r‖ ^ 2
        ∂circularVectorLaw ι) ∂phaseLaw = 2 * (F * A * Fᴴ).trace.re := by
  have hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det :=
    fun θ => isUnit_det_of_tendsto hN (norm_phase θ)
  have hX := continuous_closingX hU
  have hD : Continuous fun θ => (closingMap S A Pi (phase θ) - 1) *
      (closingMap S A Pi (phase θ) - 1)ᴴ := by
    have hC : Continuous fun θ => closingMap S A Pi (phase θ) - 1 := by
      simp_rw [closingMap_sub_one]
      exact hX.sub continuous_const
    exact hC.matrix_mul hC.matrix_conjTranspose
  have e : ∀ θ, ∫ g, ∑ r, ‖((F * closingMap S A Pi (phase θ)) *ᵥ g - F *ᵥ g) r‖ ^ 2
      ∂circularVectorLaw ι = (F * ((closingMap S A Pi (phase θ) - 1) *
        (closingMap S A Pi (phase θ) - 1)ᴴ) * Fᴴ).trace.re := by
    intro θ
    have hv : ∀ g : ι → ℂ, (F * closingMap S A Pi (phase θ)) *ᵥ g - F *ᵥ g =
        (F * (closingMap S A Pi (phase θ) - 1)) *ᵥ g := by
      intro g
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec]
    simp_rw [hv]
    rw [integral_normSq_mulVec, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp_rw [e]
  have hint : Integrable (fun θ => (F * ((closingMap S A Pi (phase θ) - 1) *
      (closingMap S A Pi (phase θ) - 1)ᴴ) * Fᴴ).trace) phaseLaw := by
    simp only [Matrix.trace, diag_apply, mul_apply]
    refine integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun b _ =>
      (integrable_finsetSum _ fun a _ => ((integrable_entry hD a b).const_mul _)).mul_const _
  have h2 : ∫ θ, (F * ((closingMap S A Pi (phase θ) - 1) *
      (closingMap S A Pi (phase θ) - 1)ᴴ) * Fᴴ).trace.re ∂phaseLaw =
      (∫ θ, (F * ((closingMap S A Pi (phase θ) - 1) *
      (closingMap S A Pi (phase θ) - 1)ᴴ) * Fᴴ).trace ∂phaseLaw).re := integral_re hint
  rw [h2, integral_trace_conj F hD,
    phaseAvg_closingDefect hA2 hAH hPi hS hN, Matrix.mul_smul, Matrix.smul_mul, trace_smul,
    smul_eq_mul]
  simp

end BlockBand.SourceProcess.Closing
