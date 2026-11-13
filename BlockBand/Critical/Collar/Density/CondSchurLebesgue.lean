module

public import BlockBand.Critical.Collar.Density.CondSchurMeasurable

/-!
# Conditional Schur identity: the Lebesgue form

Continuity of the boundary value of the top quadratic form of the Schur pencil, its almost-everywhere
identification, and `lintegral_cauchyKernel_csTop`, the extended-real Lebesgue-integral form of the
Cauchy-height identity under genericity of `(D, B)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_eq_im_inv cauchyKernel_nonneg
  continuous_cauchyKernel measurable_cauchyKernel)
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {D : Matrix m m ℂ} {B : Matrix m n ℂ} {G : Matrix n n ℂ}

theorem continuous_csF_zero (hD : D.IsHermitian) (hG : G.IsHermitian) (hgen : CsGeneric D B)
    (u : m → ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η) : Continuous (csF D B G u t η 0) := by
  have hM : Continuous fun x : ℝ => csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) -
      ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) :=
    continuous_const.sub (((Complex.continuous_ofReal).add continuous_const).smul continuous_const)
  have hU : ∀ x : ℝ, IsUnit (csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) -
      ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ)).det := fun x =>
    isUnit_det_csPencil_sub hD hG hgen hη t (by simp)
  have hinv := continuous_inv_of_isUnit_det hM hU
  have h2 : Continuous fun x : ℝ => Real.pi⁻¹ * (star (Sum.elim u (0 : n → ℂ)) ⬝ᵥ
      ((csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) -
        ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ))⁻¹ *ᵥ
          Sum.elim u 0)).im :=
    continuous_const.mul (Complex.continuous_im.comp (continuous_const.dotProduct
      (hinv.matrix_mulVec continuous_const)))
  exact h2

theorem ae_csF_zero_eq (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (t : ℝ) {η : ℝ}
    (hη : 0 < η) : ∀ᵐ x ∂(volume : Measure ℝ), csF D B G u t η 0 x =
      quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x)) (csY D B u x) := by
  have hfin := finite_setOf_det_sub_eq_zero D
  have hnull : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ {x : ℝ | (D - (x : ℂ) • (1 : Matrix m m ℂ)).det = 0} := by
    rw [ae_iff]; simpa using hfin.measure_zero volume
  filter_upwards [hnull] with x hx
  exact csF_zero_eq hD hG u t hη (isUnit_iff_ne_zero.2 hx)

theorem integrableOn_quadForm_cfc_csS (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (u : m → ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η) (a₁ a₂ : ℝ) :
    IntegrableOn (fun x => quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x))
      (csY D B u x)) (Set.Icc a₁ a₂) :=
  ((continuous_csF_zero hD hG hgen u t hη).integrableOn_Icc).congr_fun_ae
    (ae_restrict_of_ae (ae_csF_zero_eq hD hG u t hη))

theorem cauchyKernel_shift_nonneg {η : ℝ} (hη : 0 < η) (t l : ℝ) :
    0 ≤ (fun l => cauchyKernel η (l + t)) l := cauchyKernel_nonneg hη.le _

/-- **Cauchy-height identity, extended-real Lebesgue form.** -/
theorem lintegral_cauchyKernel_csTop (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (u : m → ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η) {a₁ a₂ : ℝ}
    (ha : a₁ ≤ a₂) :
    ∫⁻ θ, ENNReal.ofReal (cauchyKernel η (θ - t)) * ENNReal.ofReal (csTop D B G a₁ a₂ u θ) =
      ∫⁻ x in Set.Icc a₁ a₂, ENNReal.ofReal (quadForm (cfc (fun l => cauchyKernel η (l + t))
        (csS D B G x)) (csY D B u x)) := by
  have hm : Measurable fun θ => ENNReal.ofReal (csTop D B G a₁ a₂ u θ) :=
    ENNReal.measurable_ofReal.comp (measurable_csTop hD hG a₁ a₂ u)
  rw [← lintegral_stdCauchy_eq hm t hη]
  have hint : Integrable (fun s => csTop D B G a₁ a₂ u (t + η * s)) stdCauchy := by
    refine Integrable.of_bound ((measurable_csTop hD hG a₁ a₂ u).comp (measurable_const.add
      (measurable_const.mul measurable_id))).aestronglyMeasurable (∑ a, ‖u a‖ ^ 2)
      (Eventually.of_forall fun s => ?_)
    obtain ⟨h0, h1⟩ := csTop_nonneg_le (B := B) hD hG a₁ a₂ u (t + η * s)
    rw [Real.norm_of_nonneg h0]; exact h1
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun s =>
    (csTop_nonneg_le (B := B) hD hG a₁ a₂ u _).1), integral_csTop_stdCauchy hD hG hgen u t hη ha,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_quadForm_cfc_csS hD hG hgen u t hη a₁ a₂)
      (Eventually.of_forall fun x => quadForm_cfc_nonneg (csS_isHermitian hD hG x)
        (cauchyKernel_shift_nonneg hη t) _)]

end BlockBand.Critical.Collar.Density
