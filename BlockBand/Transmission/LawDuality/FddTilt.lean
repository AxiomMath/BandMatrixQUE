module

public import BlockBand.Transmission.LawDuality.FddLimit

/-!
# Tilting by a past test

For a nonnegative bounded continuous past test `Φ = ψ(μ_{u_1}, …, μ_{u_m})` with `E Φ = c > 0`,
the tilted measure `(Φ/c)·P` is a probability measure, keeps the local mass bound, and keeps the
forward ratio increments after any `a₀ ≥ max u_l` (`ratioIncFrom_tilt`).

* `integral_tiltMeasure`, `tiltMeasure_le`: for a measurable `Φ ≥ 0` and `c > 0`,
  `∫ g d((Φ/c)·P) = c⁻¹ ∫ Φ g dP`, and `(Φ/c)·P ≤ (C/c)·P` when `Φ ≤ C`.
* `hasLocalMassBound_of_le_smul`: the local mass bound passes to any `Q ≤ B·P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal BoundedContinuousFunction

/-- The past test `Φ(ω) = ψ(μ_{u_1}(ω), …, μ_{u_m}(ω))`. -/
def pastTest {Ω : Type*} {m : ℕ} (ψ : (Fin m → FiniteMeasure unitInterval) →ᵇ ℝ)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) (u : Fin m → ℝ) (ω : Ω) : ℝ :=
  ψ fun l => μ (u l) ω

/-- The tilted measure `(Φ/c)·P`. -/
def tiltMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Φ : Ω → ℝ) (c : ℝ) :
    Measure Ω :=
  P.withDensity fun ω => ((Φ ω / c).toNNReal : ℝ≥0∞)

theorem measurable_pastTest {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (ψ : (Fin m → FiniteMeasure unitInterval) →ᵇ ℝ) {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hmeas : ∀ t, 0 < t → Measurable (μ t)) {u : Fin m → ℝ} (hu : ∀ l, 0 < u l) :
    Measurable (pastTest ψ μ u) :=
  ψ.continuous.measurable.comp (measurable_pi_iff.2 fun l => hmeas _ (hu l))

theorem pastTest_le {Ω : Type*} {m : ℕ} (ψ : (Fin m → FiniteMeasure unitInterval) →ᵇ ℝ)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) (u : Fin m → ℝ) (ω : Ω) :
    pastTest ψ μ u ω ≤ ‖ψ‖ :=
  (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm _)

section Tilt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Φ : Ω → ℝ} {c : ℝ}

theorem integral_tiltMeasure (hΦm : Measurable Φ) (hΦ0 : ∀ ω, 0 ≤ Φ ω) (hc : 0 < c)
    (g : Ω → ℝ) : ∫ ω, g ω ∂tiltMeasure P Φ c = c⁻¹ * ∫ ω, Φ ω * g ω ∂P := by
  unfold tiltMeasure
  rw [integral_withDensity_eq_integral_smul ((hΦm.div_const c).real_toNNReal), ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  show (Φ ω / c).toNNReal • g ω = c⁻¹ * (Φ ω * g ω)
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (div_nonneg (hΦ0 ω) hc.le)]
  ring

theorem tiltMeasure_le (hc : 0 < c) {C : ℝ} (hΦC : ∀ ω, Φ ω ≤ C) :
    tiltMeasure P Φ c ≤ ENNReal.ofReal (C / c) • P := by
  unfold tiltMeasure
  rw [← withDensity_const]
  exact withDensity_mono (ae_of_all _ fun ω =>
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hΦC ω) hc.le))

theorem isProbabilityMeasure_tilt [IsFiniteMeasure P] (hΦm : Measurable Φ) (hΦ0 : ∀ ω, 0 ≤ Φ ω)
    {C : ℝ} (hΦC : ∀ ω, Φ ω ≤ C) (hc : 0 < c) (hcdef : ∫ ω, Φ ω ∂P = c) :
    IsProbabilityMeasure (tiltMeasure P Φ c) := by
  have hi : Integrable (fun ω => (((Φ ω / c).toNNReal : ℝ≥0) : ℝ)) P := by
    refine Integrable.of_bound ((hΦm.div_const c).real_toNNReal.coe_nnreal_real).aestronglyMeasurable
      (C / c) (ae_of_all _ fun ω => ?_)
    rw [Real.coe_toNNReal _ (div_nonneg (hΦ0 ω) hc.le), Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hΦ0 ω) hc.le)]
    exact div_le_div_of_nonneg_right (hΦC ω) hc.le
  have hΦi : Integrable Φ P := by
    refine (hi.const_mul c).congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [Real.coe_toNNReal _ (div_nonneg (hΦ0 ω) hc.le)]
    field_simp
  constructor
  unfold tiltMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral _ hi]
  have : ∫ ω, (((Φ ω / c).toNNReal : ℝ≥0) : ℝ) ∂P = ∫ ω, Φ ω / c ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => Real.coe_toNNReal _ (div_nonneg (hΦ0 ω) hc.le))
  rw [this, integral_div, hcdef, div_self hc.ne', ENNReal.ofReal_one]

end Tilt

/-- The local mass bound passes to every `Q ≤ B·P`. -/
theorem hasLocalMassBound_of_le_smul {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (hmass : HasLocalMassBound P μ) {B : ℝ}
    (hB : 0 ≤ B) (hQ : Q ≤ ENNReal.ofReal B • P) : HasLocalMassBound Q μ := by
  intro ε T hε
  obtain ⟨Cm, hCm⟩ := hmass ε T hε
  refine ⟨B * max Cm 0, fun t ht => ?_⟩
  calc ∫⁻ ω, (μ t ω : Measure unitInterval) univ ∂Q
      ≤ ∫⁻ ω, (μ t ω : Measure unitInterval) univ ∂(ENNReal.ofReal B • P) :=
        lintegral_mono' hQ le_rfl
    _ = ENNReal.ofReal B * ∫⁻ ω, (μ t ω : Measure unitInterval) univ ∂P :=
        lintegral_smul_measure _ _
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (max Cm 0) :=
        mul_le_mul_right ((hCm t ht).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) _
    _ = ENNReal.ofReal (B * max Cm 0) := (ENNReal.ofReal_mul hB).symm

/-- **The forward increments after `a₀` under the tilt by a past test.** -/
theorem ratioIncFrom_tilt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : ℝ → Ω → FiniteMeasure unitInterval} {D0 E : ℝ} {κ : ℝ → ℝ}
    (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hM : IsRatioMartingale D0 E κ P μ) {m : ℕ}
    (ψ : (Fin m → FiniteMeasure unitInterval) →ᵇ ℝ) (hψ : ∀ v, 0 ≤ ψ v) {u : Fin m → ℝ}
    {a0 : ℝ} (ha0 : 0 < a0) (hu : ∀ l, 0 < u l ∧ u l ≤ a0) {c : ℝ} (hc : 0 < c)
    (hcdef : ∫ ω, pastTest ψ μ u ω ∂P = c) :
    RatioIncFrom D0 E κ (tiltMeasure P (pastTest ψ μ u) c) μ a0 := by
  have hΦm := measurable_pastTest ψ hmeas fun l => (hu l).1
  have hΦ0 : ∀ ω, 0 ≤ pastTest ψ μ u ω := fun ω => hψ _
  have := isProbabilityMeasure_tilt hΦm hΦ0 (pastTest_le ψ μ u) hc hcdef
  intro p z hz s t hs hst
  have hs0 : 0 < s := lt_of_lt_of_le ha0 hs
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  obtain ⟨hI, horth⟩ := hM p z hz s t (mem_Ioi.2 hs0) (mem_Ioi.2 ht0) hst
  have h0 := horth m (fun _ => ()) u (fun l => ⟨mem_Ioi.2 (hu l).1, (hu l).2.trans hs⟩) ψ
  simp only [smul_eq_mul] at h0
  have hQ := tiltMeasure_le (P := P) hc (pastTest_le ψ μ u)
  have hIQ := hI.of_measure_le_smul ENNReal.ofReal_ne_top hQ
  have hinc : ∫ ω, (transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω) -
      ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) ∂tiltMeasure P (pastTest ψ μ u) c = 0 := by
    rw [integral_tiltMeasure hΦm hΦ0 hc]
    unfold pastTest
    rw [h0, mul_zero]
  have hr := IsRatioParameter.isRatioRange (show IsRatioParameter z.1 z.2 from hz)
  have hFt := integrable_ratio_comp (P := tiltMeasure P (pastTest ψ μ u) c) hr (hmeas t ht0)
  have hFs := integrable_ratio_comp (P := tiltMeasure P (pastTest ψ μ u) c) hr (hmeas s hs0)
  have e : (fun ω => ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) = fun ω =>
      (transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω)) -
        (transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω) -
          ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) := by
    funext ω; ring
  have hsub : Integrable (fun ω => transmissionRatio z.1 z.2 (μ t ω) -
      transmissionRatio z.1 z.2 (μ s ω)) (tiltMeasure P (pastTest ψ μ u) c) := hFt.sub hFs
  beta_reduce at hIQ
  rw [e, integral_sub hsub hIQ, integral_sub hFt hFs, hinc, sub_zero]

end BlockBand.Transmission.LawDuality
