module

public import BlockBand.Transmission.LawClauses.HessianBounds
public import BlockBand.Transmission.SchurDerivative
public import BlockBand.Transmission.PassiveCovariance.Fluctuation
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# First derivative of `τ ↦ Tr (A + τH)^p`

A step towards `fractionalHessian`. With `R_τ(s) = (A + τH + s)⁻¹`,
`hasDerivAt_fracTrace_line`: on the coercive window `|τ| < δ` (`A + τH - m ⪰ 0`),

`d/dτ Tr (A+τH)^p = (sin πp/π) ∫_0^∞ s^{p-1} · s Re Tr[R_τ H R_τ] ds`,

by differentiating `fracTrace_eq_integral` under the integral sign (dominated by
`n‖H‖ s^p/(m+s)²`). Also: the `ℝ`-linear functional `trRe = Re Tr`, the real-line inverse
derivative and the resolvent bounds `|Re Tr(RH)| ≤ n‖H‖/(m+s)`, etc.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Set Real Matrix Filter Topology
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `M ↦ Re Tr M` as a continuous `ℝ`-linear map. -/
def trRe : Matrix ι ι ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((LinearMap.toContinuousLinearMap (Matrix.traceLinearMap ι ℂ ℂ)).restrictScalars ℝ)

omit [DecidableEq ι] in
theorem trRe_apply (M : Matrix ι ι ℂ) : trRe M = M.trace.re := rfl

/-- `d/dτ (B + τH)⁻¹ = -(B+τH)⁻¹H(B+τH)⁻¹` along the real line. -/
theorem hasDerivAt_inv_real_line (B H : Matrix ι ι ℂ) (τ₀ : ℝ) (hu : IsUnit (B + (τ₀ : ℂ) • H)) :
    HasDerivAt (fun τ : ℝ => (B + (τ : ℂ) • H)⁻¹)
      (-((B + (τ₀ : ℂ) • H)⁻¹ * H * (B + (τ₀ : ℂ) • H)⁻¹)) τ₀ := by
  have h := affineInverse_hasDerivAt B H (τ₀ : ℂ) hu
  have h' : HasDerivAt (fun t : ℂ => (B + t • H)⁻¹)
      (-((B + (τ₀ : ℂ) • H)⁻¹ * H * (B + (τ₀ : ℂ) • H)⁻¹)) (Complex.ofRealCLM τ₀) := by
    simpa using h
  have := h'.scomp τ₀ Complex.ofRealCLM.hasDerivAt
  simpa [Function.comp_def] using this

theorem measurable_resolvent (X : Matrix ι ι ℂ) :
    Measurable (fun s : ℝ => (X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹) :=
  measurable_matrix_inv.comp
    ((continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).measurable)

/-- Resolvent bounds: `‖R‖ ≤ (m+s)⁻¹` gives the four trace bounds. -/
theorem resolvent_norm_bounds {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {m s : ℝ} (hm : 0 < m)
    (hs : 0 ≤ s) (hXm : (X - (m : ℂ) • 1).PosSemidef) (H : Matrix ι ι ℂ) :
    ‖(X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ * H‖ ≤ ‖H‖ / (m + s) ∧
    ‖(X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ * H * (X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤
      ‖H‖ / (m + s) ^ 2 ∧
    ‖(X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ * H * (X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ * H‖ ≤
      ‖H‖ ^ 2 / (m + s) ^ 2 ∧
    ‖(X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ * (X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ * H‖ ≤
      ‖H‖ / (m + s) ^ 2 := by
  set R := (X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹
  have hR : ‖R‖ ≤ (m + s)⁻¹ := norm_inv_add_smul_le hX hm hs hXm
  have hR0 := norm_nonneg R
  have hH0 := norm_nonneg H
  have hms : 0 < m + s := by linarith
  have hRH : ‖R * H‖ ≤ ‖H‖ / (m + s) := by
    refine (norm_mul_le _ _).trans ?_
    rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_right hR hH0
  have hRHR : ‖R * H * R‖ ≤ ‖H‖ / (m + s) ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖R * H‖ * ‖R‖ ≤ ‖H‖ / (m + s) * (m + s)⁻¹ :=
          mul_le_mul hRH hR hR0 (by positivity)
      _ = _ := by field_simp
  refine ⟨hRH, hRHR, ?_, ?_⟩
  · refine (norm_mul_le _ _).trans ?_
    calc ‖R * H * R‖ * ‖H‖ ≤ ‖H‖ / (m + s) ^ 2 * ‖H‖ := mul_le_mul_of_nonneg_right hRHR hH0
      _ = _ := by ring
  · rw [Matrix.mul_assoc]
    refine (norm_mul_le _ _).trans ?_
    calc ‖R‖ * ‖R * H‖ ≤ (m + s)⁻¹ * (‖H‖ / (m + s)) := mul_le_mul hR hRH (norm_nonneg _)
          (by positivity)
      _ = _ := by field_simp

/-- **First derivative under the integral sign.** -/
theorem hasDerivAt_fracTrace_line {A H : Matrix ι ι ℂ} (hA : A.IsHermitian) (hH : H.IsHermitian)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {m δ : ℝ} (hm : 0 < m)
    (hcoer : ∀ τ : ℝ, |τ| < δ → (A + (τ : ℂ) • H - (m : ℂ) • 1).PosSemidef) {τ₀ : ℝ}
    (hτ₀ : |τ₀| < δ) :
    HasDerivAt (fun τ : ℝ => fracTrace p (A + (τ : ℂ) • H))
      (Real.sin (π * p) / π * ∫ s in Ioi (0 : ℝ), s ^ (p - 1) *
        (s * ((A + (τ₀ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H *
          (A + (τ₀ : ℂ) • H + (s : ℂ) • 1)⁻¹).trace.re)) τ₀ := by
  set n := (Fintype.card ι : ℝ)
  set ε := (δ - |τ₀|) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hball : ∀ τ ∈ Metric.ball τ₀ ε, |τ| < δ := by
    intro τ hτ
    rw [Metric.mem_ball, Real.dist_eq] at hτ
    have := abs_sub_abs_le_abs_sub τ τ₀
    rw [hε] at hτ; linarith
  have hpd : ∀ τ : ℝ, |τ| < δ → (A + (τ : ℂ) • H).PosDef := fun τ hτ => by
    simpa using posDef_add_smul (s := 0) hm le_rfl (hcoer τ hτ)
  set F : ℝ → ℝ → ℝ := fun τ s => s ^ (p - 1) *
    (n - s * ((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹).trace.re) with hF
  set F' : ℝ → ℝ → ℝ := fun τ s => s ^ (p - 1) *
    (s * ((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H * (A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹).trace.re)
    with hF'
  have hmeasF : ∀ τ : ℝ, Measurable (F τ) := fun τ =>
    (measurable_id.pow_const _).mul (measurable_const.sub (measurable_id.mul
      (trRe.continuous.measurable.comp (measurable_resolvent _))))
  have hmeasF' : Measurable (F' τ₀) := by
    have hR := measurable_resolvent (A + (τ₀ : ℂ) • H)
    exact (measurable_id.pow_const _).mul (measurable_id.mul (trRe.continuous.measurable.comp
      ((hR.mul_const H).mul hR)))
  have hInt := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := τ₀)
    (bound := fun s => n * ‖H‖ * (s ^ p / (m + s) ^ 2)) (Metric.ball_mem_nhds τ₀ hεpos)
    (Eventually.of_forall fun τ => (hmeasF τ).aestronglyMeasurable)
    (integrableOn_fracTrace_integrand (hpd τ₀ hτ₀) hp0 hp1) hmeasF'.aestronglyMeasurable
    ?bound ((integrableOn_rpow_div_pow (q := p) (k := 2) (by linarith) (by push_cast; linarith)
      hm).const_mul _) ?diff
  case bound =>
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs τ hτ => ?_)
    have hs0 : 0 < s := hs
    have hX := isHermitian_add_real_smul hA τ hH
    have hb := (resolvent_norm_bounds hX hm hs0.le (hcoer τ (hball τ hτ)) H).2.1
    have htr := abs_trace_re_le ((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H *
      (A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹)
    simp only [hF', Real.norm_eq_abs]
    have hsp : s ^ (p - 1) * s = s ^ p := by rw [← rpow_add_one hs0.ne']; ring_nf
    rw [← mul_assoc, hsp, abs_mul, abs_of_pos (rpow_pos_of_pos hs0 p)]
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    calc s ^ p * |((A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹ * H *
          (A + (τ : ℂ) • H + (s : ℂ) • 1)⁻¹).trace.re| ≤ s ^ p * (n * (‖H‖ / (m + s) ^ 2)) :=
          mul_le_mul_of_nonneg_left (htr.trans (mul_le_mul_of_nonneg_left hb hn0))
            (rpow_pos_of_pos hs0 p).le
      _ = _ := by ring
  case diff =>
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs τ hτ => ?_)
    have hs0 : 0 < s := hs
    have hu : IsUnit (A + (s : ℂ) • 1 + (τ : ℂ) • H) := by
      have := (posDef_add_smul hm hs0.le (hcoer τ (hball τ hτ))).isUnit
      rwa [add_right_comm] at this
    have hinv := hasDerivAt_inv_real_line (A + (s : ℂ) • 1) H τ hu
    have hd := (((trRe.hasFDerivAt.comp_hasDerivAt τ hinv).const_mul s).const_sub n).const_mul
      (s ^ (p - 1))
    have hfun : (fun τ' : ℝ => F τ' s) = fun τ' : ℝ => s ^ (p - 1) *
        (n - s * (trRe ∘ fun τ : ℝ => (A + (s : ℂ) • 1 + (τ : ℂ) • H)⁻¹) τ') := by
      funext τ'; simp only [hF, Function.comp_apply, trRe_apply, add_right_comm]
    rw [hfun]
    convert hd using 1
    simp only [hF', trRe_apply, map_neg, add_right_comm]
    ring
  have hev : (fun τ : ℝ => fracTrace p (A + (τ : ℂ) • H)) =ᶠ[𝓝 τ₀]
      fun τ => Real.sin (π * p) / π * ∫ s in Ioi (0 : ℝ), F τ s := by
    filter_upwards [Metric.ball_mem_nhds τ₀ hεpos] with τ hτ
    exact fracTrace_eq_integral (hpd τ (hball τ hτ)) hp0 hp1
  exact (hInt.2.const_mul _).congr_of_eventuallyEq hev

end BlockBand.Transmission.LawClauses
