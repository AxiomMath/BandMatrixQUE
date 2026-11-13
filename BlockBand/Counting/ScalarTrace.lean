module

public import BlockBand.Model.Construction.GaussianCharacteristic

/-!
# The Gaussian law of the scalar trace

Under the Gaussian ring law, the normalized trace `N⁻¹ Tr H` is a centered real Gaussian
with variance `c / (N W)`.  After the microscopic scaling by `N ρ` its variance is
`c ρ² n`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Real scalar trace mean of a raw matrix `H`; agrees with `N⁻¹ Tr H` for Hermitian `H`. -/
def scalarTrace (p : BlockBand.Parameters) (H : p.SiteMatrix) : ℝ :=
  (∑ x, (H x x).re) / (p.N : ℝ)

/-- The scalar trace variance `c / (N W)`. -/
def scalarTraceVariance (p : BlockBand.Parameters) : ℝ≥0 :=
  ⟨p.c / ((p.N : ℝ) * (p.W : ℝ)), by positivity [p.c_pos]⟩

theorem measurable_scalarTrace (p : BlockBand.Parameters) : Measurable p.scalarTrace := by
  unfold scalarTrace
  fun_prop

/-- There are exactly `N` physical sites. -/
theorem card_site (p : BlockBand.Parameters) : Fintype.card p.Site = p.N := by
  simp [Site, N]

/-- A constant diagonal test is precisely the scalar trace characteristic pairing. -/
theorem scalarTrace_pairing (p : BlockBand.Parameters) (r : ℝ) (H : p.SiteMatrix) :
    p.coordinatePairing (fun _ => r / (p.N : ℝ)) (fun _ _ => 0) (fun _ _ => 0) H =
      r * p.scalarTrace H := by
  simp only [coordinatePairing, zero_mul, Finset.sum_const_zero, add_zero,
    scalarTrace, div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  ring

/-- Exact covariance computation without a dimension-normalization assumption. -/
theorem scalarTrace_pairingVariance (p : BlockBand.Parameters) (r : ℝ) :
    p.coordinateVariance (fun _ => r / (p.N : ℝ)) (fun _ _ => 0) (fun _ _ => 0) =
      (p.scalarTraceVariance : ℝ) * r ^ 2 := by
  simp only [coordinateVariance, entryVariance, ite_true, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.card_univ, p.card_site, nsmul_eq_mul]
  change (p.N : ℝ) * (p.c / p.W * (r / p.N) ^ 2) =
    (p.c / ((p.N : ℝ) * (p.W : ℝ))) * r ^ 2
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  have hW : (p.W : ℝ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  field_simp

/-- The scalar trace is a centered Gaussian of variance `c / (N W)` under the
Gaussian ring law. -/
theorem GaussianRingModel.scalarTrace_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw p.scalarTrace (gaussianReal 0 p.scalarTraceVariance)
      (model.law : Measure p.SiteMatrix) := by
  refine ⟨p.measurable_scalarTrace.aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  funext r
  rw [charFun_apply_real]
  simp only [← Complex.ofReal_mul, mul_comm _ Complex.I]
  rw [integral_map p.measurable_scalarTrace.aemeasurable
    (show AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (Complex.I * ((r * x : ℝ) : ℂ)))
      (Measure.map p.scalarTrace (model.law : Measure p.SiteMatrix)) from
      (show Continuous (fun x : ℝ =>
        Complex.exp (Complex.I * ((r * x : ℝ) : ℂ))) by fun_prop).aestronglyMeasurable)]
  simp_rw [← p.scalarTrace_pairing r]
  rw [model.isPhysical.2, p.scalarTrace_pairingVariance]
  have h := charFun_gaussianReal (μ := 0) (v := p.scalarTraceVariance) r
  simpa [Complex.ofReal_mul, Complex.ofReal_pow, neg_div] using h.symm

/-- Microscopic trace-shift variance `c ρ² n` at a real density parameter `ρ`.
For `ρ = ρ(E)` this is the variance in the stationarity proposition. -/
def spectralScalarVariance (p : BlockBand.Parameters) (ρ : ℝ) : ℝ≥0 :=
  ⟨p.c * ρ ^ 2 * (p.n : ℝ), mul_nonneg (mul_nonneg p.c_pos.le (sq_nonneg _))
    (Nat.cast_nonneg _)⟩

theorem scalarTraceVariance_scaling (p : BlockBand.Parameters) (ρ : ℝ) :
    NNReal.mk (((p.N : ℝ) * ρ) ^ 2) (sq_nonneg _) * p.scalarTraceVariance =
      p.spectralScalarVariance ρ := by
  apply NNReal.coe_injective
  change ((p.N : ℝ) * ρ) ^ 2 * (p.c / ((p.N : ℝ) * (p.W : ℝ))) =
    p.c * ρ ^ 2 * (p.n : ℝ)
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  have hW : (p.W : ℝ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hn : (p.N : ℝ) = (p.n : ℝ) * (p.W : ℝ) := by simp [N]
  field_simp
  rw [hn]
  ring

/-- The microscopic shift `N ρ` times the scalar trace is a centered Gaussian of
variance `c ρ² n`. -/
theorem GaussianRingModel.spectralScalarTrace_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (ρ : ℝ) :
    HasLaw (fun H => ((p.N : ℝ) * ρ) * p.scalarTrace H)
      (gaussianReal 0 (p.spectralScalarVariance ρ)) (model.law : Measure p.SiteMatrix) := by
  simpa only [mul_zero, p.scalarTraceVariance_scaling] using
    gaussianReal_const_mul model.scalarTrace_hasLaw ((p.N : ℝ) * ρ)

/-- The scalar trace is integrable under the model law. -/
theorem GaussianRingModel.integrable_scalarTrace {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) : Integrable p.scalarTrace (model.law : Measure p.SiteMatrix) :=
  model.scalarTrace_hasLaw.integrable
    (memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := _) 1))

/-- Exact centered scalar trace expectation. -/
theorem GaussianRingModel.integral_scalarTrace {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) : (∫ H, p.scalarTrace H ∂(model.law : Measure p.SiteMatrix)) = 0 := by
  rw [model.scalarTrace_hasLaw.integral_eq, integral_id_gaussianReal]

/-- Scalar trace variance under the model law. -/
theorem GaussianRingModel.variance_scalarTrace {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    Var[p.scalarTrace; (model.law : Measure p.SiteMatrix)] = p.c / ((p.N : ℝ) * (p.W : ℝ)) := by
  rw [model.scalarTrace_hasLaw.variance_eq, variance_id_gaussianReal]
  rfl

end BlockBand.Parameters
