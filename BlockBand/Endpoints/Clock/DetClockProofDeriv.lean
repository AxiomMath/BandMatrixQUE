module

public import BlockBand.Endpoints.Clock.DetClockProofLayer

/-!
# The deterministic-clock lemma: the derivatives of the expected determinant

For a probability measure `μ`, a measurable family `Q` of PSD matrices and `a > 0`:
`a² ∂_a² E F_a(Q) = E F_a(Q)[(Tr A_a)² + Tr A_a²]` (`integral_deriv_deriv`). The proof
differentiates twice under the integral sign, with the deterministic dominations
`|∂_a F_a| ≤ n/a`, `|∂_a² F_a| ≤ 2n²/a²` (`Tr A_a ≤ n`) on `a > a₀/2`; no moment is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

namespace DetClockProof

open ClockMixingAlg ClockMixingProb

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

theorem measurable_detLaplace {Q : Ω → Matrix (Fin n) (Fin n) ℂ} (hQ : Measurable Q) (x : ℝ) :
    Measurable (fun ω => detLaplace (Q ω) x) := by
  unfold detLaplace
  refine Measurable.inv (Complex.measurable_re.comp ?_)
  exact (Continuous.measurable (continuous_id.matrix_det)).comp
    (measurable_const.add (meas_smul _ hQ))

theorem measurable_resolventWeight {Q : Ω → Matrix (Fin n) (Fin n) ℂ} (hQ : Measurable Q)
    (x : ℝ) : Measurable (fun ω => resolventWeight (Q ω) x) := by
  unfold resolventWeight
  exact meas_mul (meas_smul _ hQ) (BlockBand.Layers.measurable_matrix_inv.comp
    (measurable_const.add (meas_smul _ hQ)))

theorem deriv_detLaplace_eq {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {x : ℝ}
    (hx : 0 < x) :
    deriv (detLaplace Q) x = -(detLaplace Q x * (resolventWeight Q x).trace.re) / x := by
  have h := mul_deriv_detLaplace hQ hx.le
  field_simp
  linarith

theorem deriv_deriv_detLaplace_eq {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {x : ℝ}
    (hx : 0 < x) :
    deriv (deriv (detLaplace Q)) x = detLaplace Q x * ((resolventWeight Q x).trace.re ^ 2 +
      ((resolventWeight Q x) ^ 2).trace.re) / x ^ 2 := by
  have h := sq_mul_deriv_deriv_detLaplace hQ hx.le
  field_simp
  linarith

theorem abs_deriv_detLaplace_le {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef) {x : ℝ}
    (hx : 0 < x) : |deriv (detLaplace Q) x| ≤ n / x := by
  rw [deriv_detLaplace_eq hQ hx, abs_div, abs_neg, abs_of_pos hx, abs_mul,
    abs_of_pos (detLaplace_pos hQ hx.le), abs_of_nonneg (re_trace_resolventWeight_nonneg hQ hx.le)]
  refine div_le_div_of_nonneg_right ?_ hx.le
  calc detLaplace Q x * (resolventWeight Q x).trace.re ≤ 1 * n :=
        mul_le_mul (detLaplace_le_one hQ hx.le) (trace_weight_le_card hQ hx.le)
          (re_trace_resolventWeight_nonneg hQ hx.le) zero_le_one
    _ = n := one_mul _

theorem abs_deriv_deriv_detLaplace_le {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.PosSemidef)
    {x : ℝ} (hx : 0 < x) : |deriv (deriv (detLaplace Q)) x| ≤ 2 * (n : ℝ) ^ 2 / x ^ 2 := by
  rw [deriv_deriv_detLaplace_eq hQ hx, abs_div, abs_of_pos (by positivity : 0 < x ^ 2)]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg x)
  have hT0 := re_trace_resolventWeight_nonneg hQ hx.le
  have hT := trace_weight_le_card hQ hx.le
  have hT2 := trace_weight_sq_le hQ hx.le
  have hT20 : 0 ≤ ((resolventWeight Q x) ^ 2).trace.re := by
    rw [trace_resolventWeight_sq_eq_sum hQ hx.le, Complex.ofReal_re]; positivity
  have hsq : (resolventWeight Q x).trace.re ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hT0 hT 2
  rw [abs_mul, abs_of_pos (detLaplace_pos hQ hx.le), abs_of_nonneg (by positivity)]
  calc detLaplace Q x * ((resolventWeight Q x).trace.re ^ 2 + ((resolventWeight Q x) ^ 2).trace.re)
      ≤ 1 * (2 * (n : ℝ) ^ 2) := mul_le_mul (detLaplace_le_one hQ hx.le) (by linarith)
        (by positivity) zero_le_one
    _ = 2 * (n : ℝ) ^ 2 := one_mul _

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The first derivative under the integral, at every `x₀ > 0`. -/
theorem hasDerivAt_integral_detLaplace {Q : Ω → Matrix (Fin n) (Fin n) ℂ} (hQm : Measurable Q)
    (hQ : ∀ ω, (Q ω).PosSemidef) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    HasDerivAt (fun x => ∫ ω, detLaplace (Q ω) x ∂μ)
      (∫ ω, deriv (detLaplace (Q ω)) x₀ ∂μ) x₀ := by
  have hs : Ioi (x₀ / 2) ∈ 𝓝 x₀ := Ioi_mem_nhds (by linarith)
  have hF'm : AEStronglyMeasurable (fun ω => deriv (detLaplace (Q ω)) x₀) μ := by
    have h : (fun ω => deriv (detLaplace (Q ω)) x₀) = fun ω =>
        -(detLaplace (Q ω) x₀ * (resolventWeight (Q ω) x₀).trace.re) / x₀ := by
      funext ω; exact deriv_detLaplace_eq (hQ ω) hx₀
    rw [h]
    refine Measurable.aestronglyMeasurable ?_
    exact (((measurable_detLaplace hQm x₀).mul (Complex.measurable_re.comp
      (meas_trace (measurable_resolventWeight hQm x₀)))).neg).div_const _
  have hint : Integrable (fun ω => detLaplace (Q ω) x₀) μ := by
    refine Integrable.of_bound (measurable_detLaplace hQm x₀).aestronglyMeasurable 1
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (detLaplace_pos (hQ ω) hx₀.le)]
    exact detLaplace_le_one (hQ ω) hx₀.le
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun x ω => detLaplace (Q ω) x) (F' := fun x ω => deriv (detLaplace (Q ω)) x)
    (bound := fun _ => 2 * n / x₀) hs
    (Eventually.of_forall fun x => (measurable_detLaplace hQm x).aestronglyMeasurable) hint hF'm
    (ae_of_all _ fun ω x hx => ?_) (integrable_const _) (ae_of_all _ fun ω x hx => ?_)
  · exact h.2
  · have hx0 : 0 < x := lt_trans (by linarith) (mem_Ioi.mp hx)
    rw [Real.norm_eq_abs]
    refine (abs_deriv_detLaplace_le (hQ ω) hx0).trans ?_
    rw [div_le_div_iff₀ hx0 hx₀]
    have := mem_Ioi.mp hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · have hx0 : 0 ≤ x := le_trans (by linarith) (le_of_lt (mem_Ioi.mp hx))
    exact (hasDerivAt_detLaplace (hQ ω) hx0).differentiableAt.hasDerivAt

/-- **Two derivatives under the integral**: for `a > 0`,
`a² ∂_a² E F_a(Q) = E F_a(Q)[(Tr A_a)² + Tr A_a²]`. -/
theorem integral_deriv_deriv {Q : Ω → Matrix (Fin n) (Fin n) ℂ} (hQm : Measurable Q)
    (hQ : ∀ ω, (Q ω).PosSemidef) {a : ℝ} (ha : 0 < a) :
    a ^ 2 * deriv (deriv (fun x => ∫ ω, detLaplace (Q ω) x ∂μ)) a =
      ∫ ω, detLaplace (Q ω) a * ((resolventWeight (Q ω) a).trace.re ^ 2 +
        ((resolventWeight (Q ω) a) ^ 2).trace.re) ∂μ := by
  have hev : deriv (fun x => ∫ ω, detLaplace (Q ω) x ∂μ) =ᶠ[𝓝 a]
      fun x => ∫ ω, deriv (detLaplace (Q ω)) x ∂μ := by
    filter_upwards [Ioi_mem_nhds ha] with x hx
    exact (hasDerivAt_integral_detLaplace μ hQm hQ hx).deriv
  rw [hev.deriv_eq]
  have hs : Ioi (a / 2) ∈ 𝓝 a := Ioi_mem_nhds (by linarith)
  have hmeas1 : ∀ x, 0 < x → AEStronglyMeasurable (fun ω => deriv (detLaplace (Q ω)) x) μ := by
    intro x hx
    have h : (fun ω => deriv (detLaplace (Q ω)) x) = fun ω =>
        -(detLaplace (Q ω) x * (resolventWeight (Q ω) x).trace.re) / x := by
      funext ω; exact deriv_detLaplace_eq (hQ ω) hx
    rw [h]
    exact ((((measurable_detLaplace hQm x).mul (Complex.measurable_re.comp
      (meas_trace (measurable_resolventWeight hQm x)))).neg).div_const _).aestronglyMeasurable
  have hF''m : AEStronglyMeasurable (fun ω => deriv (deriv (detLaplace (Q ω))) a) μ := by
    have h : (fun ω => deriv (deriv (detLaplace (Q ω))) a) = fun ω =>
        detLaplace (Q ω) a * ((resolventWeight (Q ω) a).trace.re ^ 2 +
          ((resolventWeight (Q ω) a) ^ 2).trace.re) / a ^ 2 := by
      funext ω; exact deriv_deriv_detLaplace_eq (hQ ω) ha
    rw [h]
    refine Measurable.aestronglyMeasurable ?_
    refine ((measurable_detLaplace hQm a).mul ?_).div_const _
    refine ((Complex.measurable_re.comp (meas_trace (measurable_resolventWeight hQm a))).pow_const
      2).add (Complex.measurable_re.comp (meas_trace ?_))
    simp only [pow_two]
    exact meas_mul (measurable_resolventWeight hQm a) (measurable_resolventWeight hQm a)
  have hint1 : Integrable (fun ω => deriv (detLaplace (Q ω)) a) μ := by
    refine Integrable.of_bound (hmeas1 a ha) (n / a) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_deriv_detLaplace_le (hQ ω) ha
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun x ω => deriv (detLaplace (Q ω)) x)
    (F' := fun x ω => deriv (deriv (detLaplace (Q ω))) x)
    (bound := fun _ => 8 * (n : ℝ) ^ 2 / a ^ 2) hs
    (by filter_upwards [Ioi_mem_nhds ha] with x hx using hmeas1 x hx) hint1 hF''m
    (ae_of_all _ fun ω x hx => ?_) (integrable_const _) (ae_of_all _ fun ω x hx => ?_)
  · rw [h.2.deriv, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact sq_mul_deriv_deriv_detLaplace (hQ ω) ha.le
  · have hx0 : 0 < x := lt_trans (by linarith) (mem_Ioi.mp hx)
    rw [Real.norm_eq_abs]
    refine (abs_deriv_deriv_detLaplace_le (hQ ω) hx0).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hx2 : a / 2 < x := mem_Ioi.mp hx
    have hxa : a ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  · have hx0 : 0 ≤ x := le_trans (by linarith) (le_of_lt (mem_Ioi.mp hx))
    exact (hasDerivAt_deriv_detLaplace (hQ ω) hx0).differentiableAt.hasDerivAt

end DetClockProof

end BlockBand.Endpoints.Clock
