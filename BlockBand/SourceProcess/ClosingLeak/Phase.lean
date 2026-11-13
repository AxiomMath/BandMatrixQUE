module

public import BlockBand.SourceProcess.ClosingLeak.Pointwise
public import BlockBand.SourceProcess.ClosingAux.Reflection

/-!
# The phase average of the leaked mass for one injection

For a path `ω` with `N^n → 0` (`closedReflection_holds`) and the closing covariance
identity `E_z DD* = 2 farEmbed(A_-)` (`ae_phaseAvg_physClosingDefect`), every fixed matrix
`ξ ⪰ 0` satisfies

`∫⁻ θ, Re Tr(D(θ)D(θ)* ξ) ∂phaseLaw = Re Tr(2 farEmbed(A_-) ξ)` (`lintegral_phase_leak`).

The integrand is continuous in `θ` (`continuous_closingX`) and nonnegative
(`re_trace_mul_nonneg`: `Re Tr(KX) ≥ 0` for `K, X ⪰ 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.Closing
open scoped ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `Re Tr(KX) ≥ 0` for `K, X ⪰ 0`. -/
theorem re_trace_mul_nonneg {K X : Matrix ι ι ℂ} (hK : K.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (K * X).trace.re := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hK.nonneg
  rw [star_eq_conjTranspose] at hB
  rw [hB, Matrix.mul_assoc, trace_mul_comm]
  exact (Complex.nonneg_iff.1 (hX.mul_mul_conjTranspose_same B).trace_nonneg).1

omit [DecidableEq ι] in
/-- The trace against a fixed matrix commutes with the phase average. -/
theorem integral_trace_re_mul {f : ℝ → Matrix ι ι ℂ} (hf : Continuous f) (X : Matrix ι ι ℂ) :
    ∫ θ, (f θ * X).trace.re ∂phaseLaw = (phaseAvg f * X).trace.re := by
  classical
  have hfX : Continuous fun θ => f θ * X := hf.matrix_mul continuous_const
  have htr : Continuous fun θ => (f θ * X).trace := (continuous_id.matrix_trace).comp hfX
  rw [← phaseAvg_mul_right X hf]
  have hi := integrable_of_continuous htr
  have e : ∫ θ, (f θ * X).trace ∂phaseLaw = (phaseAvg fun θ => f θ * X).trace := by
    simp only [trace, diag, phaseAvg, of_apply]
    exact integral_finsetSum _ fun a _ => integrable_entry hfX a a
  rw [← e]
  exact integral_re hi

/-- **The phase average of one leaked mass.** On a path with `N^n → 0` and the closing covariance
identity, `∫⁻_θ Re Tr(DD* ξ) = Re Tr(2 farEmbed(A_-) ξ)` for `ξ ⪰ 0`. -/
theorem lintegral_phase_leak {W : ℕ} {b E s T h : ℝ} {ω : GrowthPath W}
    (hN : Tendsto (fun n => closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
        (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
        (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) ^ n) atTop (𝓝 0))
    (hD : phaseAvg (fun θ => (physClosingMap b E s T h W ω (phase θ) - 1) *
          (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.PosSemidef) :
    ∫⁻ θ, ENNReal.ofReal (((physClosingMap b E s T h W ω (phase θ) - 1) *
        (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ * X).trace.re) ∂phaseLaw =
      ENNReal.ofReal (((2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) * X).trace.re) := by
  set S := scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω
  set A := farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω)
  set P := farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)
  have hU : ∀ θ, IsUnit (1 - phase θ • closingN S A P).det :=
    fun θ => isUnit_det_of_tendsto hN (norm_phase θ)
  have hc : Continuous fun θ => physClosingMap b E s T h W ω (phase θ) - 1 := by
    have e : (fun θ => physClosingMap b E s T h W ω (phase θ) - 1) =
        fun θ => closingX S A P θ - A := funext fun θ => closingMap_sub_one S A P θ
    rw [e]
    exact (continuous_closingX hU).sub continuous_const
  have hcc : Continuous fun θ => (physClosingMap b E s T h W ω (phase θ) - 1) *
      (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ :=
    hc.matrix_mul hc.matrix_conjTranspose
  have hint : Integrable (fun θ => ((physClosingMap b E s T h W ω (phase θ) - 1) *
      (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ * X).trace.re) phaseLaw :=
    (integrable_of_continuous ((continuous_id.matrix_trace).comp
      (hcc.matrix_mul (continuous_const (y := X))))).re
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun θ => re_trace_mul_nonneg (posSemidef_self_mul_conjTranspose _) hX),
    integral_trace_re_mul hcc, hD]

end BlockBand.SourceProcess.ClosingLeak
