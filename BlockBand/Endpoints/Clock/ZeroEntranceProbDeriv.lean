module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbMean

/-!
# The zero-entrance lemma: the first `z`-derivative

The normalized trace and its first `z`-derivative have centered `L^p` norm at most `C_J √p / W`;
the bound for the derivative follows from Cauchy's formula.

Generic Cauchy transfer (`deriv_mean_le`, `deriv_fluct_le`): for a random function `H(ζ, ω)`,
almost surely holomorphic on the upper half-plane and bounded by `(Im ζ)⁻¹`, and a disc
`closedBall z₀ r` in the upper half-plane,
* `|E ∂H(z₀) - g'(z₀)| ≤ B / r` if `|E H - g| ≤ B` on the circle (`g` holomorphic);
* `‖∂H(z₀) - E ∂H(z₀)‖_p ≤ B / r` if `‖H(ζ) - E H(ζ)‖_p ≤ B` on the circle.
This is the `k = 1` case of the argument of `cavityMean_deriv` (its Fubini, Minkowski and
Cauchy-formula lemmas are reused).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Metric
open scoped ENNReal NNReal Real

namespace ZeroEntranceProb

open CavityMeanProb

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℂ → Ω → ℂ}

theorem norm_cauchyConst_one : ‖cauchyConst 1‖ = 1 / (2 * π) := by
  rw [norm_cauchyConst]; simp

/-- Cauchy representation of the mean derivative. -/
theorem integral_deriv_eq (hHm : Measurable (fun q : ℂ × Ω => H q.1 q.2))
    (hHd : ∀ᵐ ω ∂μ, DifferentiableOn ℂ (fun ζ => H ζ ω) {ζ : ℂ | 0 < ζ.im})
    {z₀ : ℂ} {r η₁ : ℝ} (hr : 0 < r) (hη₁ : 0 < η₁)
    (hball : closedBall z₀ r ⊆ {ζ : ℂ | η₁ ≤ ζ.im})
    (hHb : ∀ᵐ ω ∂μ, ∀ ζ ∈ sphere z₀ r, ‖H ζ ω‖ ≤ 1 / η₁) :
    ∫ ω, iteratedDeriv 1 (fun ζ => H ζ ω) z₀ ∂μ =
      cauchyConst 1 • ∮ ζ in C(z₀, r), (1 / (ζ - z₀) ^ (1 + 1)) • ∫ ω, H ζ ω ∂μ := by
  have hball' : closedBall z₀ r ⊆ {ζ : ℂ | 0 < ζ.im} := fun ζ hζ => hη₁.trans_le (hball hζ)
  have hrep : ∀ᵐ ω ∂μ, iteratedDeriv 1 (fun ζ => H ζ ω) z₀ =
      cauchyConst 1 • ∮ ζ in C(z₀, r), (1 / (ζ - z₀) ^ (1 + 1)) • H ζ ω := by
    filter_upwards [hHd] with ω hω
    exact iteratedDeriv_eq_cauchy hω 1 hr hball'
  have hbd : ∀ᵐ ω ∂μ, ∀ ζ ∈ sphere z₀ r,
      ‖(1 / (ζ - z₀) ^ (1 + 1)) • H ζ ω‖ ≤ (1 / r) ^ (1 + 1) * (1 / η₁) := by
    filter_upwards [hHb] with ω hω
    intro ζ hζ
    rw [norm_smul, norm_cauchyWeight hζ 1]
    exact mul_le_mul_of_nonneg_left (hω ζ hζ) (by positivity)
  have hFm : Measurable (fun q : ℂ × Ω => (1 / (q.1 - z₀) ^ (1 + 1)) • H q.1 q.2) :=
    ((measurable_cauchyWeight z₀ 1).comp measurable_fst).smul hHm
  rw [integral_congr_ae hrep, integral_smul,
    integral_circleIntegral_comm (F := fun ζ ω => (1 / (ζ - z₀) ^ (1 + 1)) • H ζ ω) hFm z₀ hr.le hbd]
  congr 1
  congr 1
  funext ζ
  exact integral_smul _ _

theorem continuousOn_weight {z₀ : ℂ} {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun ζ : ℂ => 1 / (ζ - z₀) ^ (1 + 1)) (sphere z₀ r) := by
  refine ContinuousOn.div continuousOn_const ((continuousOn_id.sub continuousOn_const).pow _) ?_
  intro ζ hζ
  refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
  rintro rfl
  rw [mem_sphere, dist_self] at hζ
  exact hr.ne' hζ.symm

/-- **Mean of the derivative.** -/
theorem deriv_mean_le (hHm : Measurable (fun q : ℂ × Ω => H q.1 q.2))
    (hHd : ∀ᵐ ω ∂μ, DifferentiableOn ℂ (fun ζ => H ζ ω) {ζ : ℂ | 0 < ζ.im})
    {z₀ : ℂ} {r η₁ : ℝ} (hr : 0 < r) (hη₁ : 0 < η₁)
    (hball : closedBall z₀ r ⊆ {ζ : ℂ | η₁ ≤ ζ.im})
    (hHb : ∀ᵐ ω ∂μ, ∀ ζ ∈ sphere z₀ r, ‖H ζ ω‖ ≤ 1 / η₁)
    (hHmc : ContinuousOn (fun ζ => ∫ ω, H ζ ω ∂μ) (sphere z₀ r))
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {ζ : ℂ | 0 < ζ.im}) {B : ℝ}
    (hB : ∀ ζ ∈ sphere z₀ r, ‖(∫ ω, H ζ ω ∂μ) - g ζ‖ ≤ B) :
    ‖(∫ ω, deriv (fun ζ => H ζ ω) z₀ ∂μ) - deriv g z₀‖ ≤ B / r := by
  have hball' : closedBall z₀ r ⊆ {ζ : ℂ | 0 < ζ.im} := fun ζ hζ => hη₁.trans_le (hball hζ)
  have hsph : ∀ ζ ∈ sphere z₀ r, 0 < ζ.im := fun ζ hζ => hball' (sphere_subset_closedBall hζ)
  have h1 := integral_deriv_eq hHm hHd hr hη₁ hball hHb
  simp only [iteratedDeriv_one] at h1
  have h2 := iteratedDeriv_eq_cauchy hg 1 hr hball'
  rw [iteratedDeriv_one] at h2
  have hci1 : CircleIntegrable (fun ζ => (1 / (ζ - z₀) ^ (1 + 1)) • ∫ ω, H ζ ω ∂μ) z₀ r :=
    ((continuousOn_weight hr).smul hHmc).circleIntegrable hr.le
  have hci2 : CircleIntegrable (fun ζ => (1 / (ζ - z₀) ^ (1 + 1)) • g ζ) z₀ r :=
    ((continuousOn_weight hr).smul ((hg.mono fun ζ hζ => hsph ζ hζ).continuousOn)).circleIntegrable
      hr.le
  rw [h1, h2, ← smul_sub, ← circleIntegral.integral_sub hci1 hci2, cauchyConst_eq, mul_smul,
    norm_smul, Complex.norm_natCast]
  have hb : ∀ ζ ∈ sphere z₀ r, ‖(1 / (ζ - z₀) ^ (1 + 1)) • (∫ ω, H ζ ω ∂μ) -
      (1 / (ζ - z₀) ^ (1 + 1)) • g ζ‖ ≤ (1 / r) ^ (1 + 1) * B := by
    intro ζ hζ
    rw [← smul_sub, norm_smul, norm_cauchyWeight hζ 1]
    exact mul_le_mul_of_nonneg_left (hB ζ hζ) (by positivity)
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hb
  calc ((Nat.factorial 1 : ℕ) : ℝ) * ‖(2 * (π : ℂ) * Complex.I)⁻¹ •
        ∮ ζ in C(z₀, r), ((1 / (ζ - z₀) ^ (1 + 1)) • (∫ ω, H ζ ω ∂μ) -
          (1 / (ζ - z₀) ^ (1 + 1)) • g ζ)‖
      ≤ 1 * (r * ((1 / r) ^ (1 + 1) * B)) := by
        rw [Nat.factorial_one, Nat.cast_one]; exact mul_le_mul_of_nonneg_left h zero_le_one
    _ = B / r := by rw [show (1 + 1 : ℕ) = 2 from rfl]; field_simp

/-- **Fluctuation of the derivative.** -/
theorem deriv_fluct_le (hHm : Measurable (fun q : ℂ × Ω => H q.1 q.2))
    (hHd : ∀ᵐ ω ∂μ, DifferentiableOn ℂ (fun ζ => H ζ ω) {ζ : ℂ | 0 < ζ.im})
    {z₀ : ℂ} {r η₁ : ℝ} (hr : 0 < r) (hη₁ : 0 < η₁)
    (hball : closedBall z₀ r ⊆ {ζ : ℂ | η₁ ≤ ζ.im})
    (hHb : ∀ᵐ ω ∂μ, ∀ ζ ∈ sphere z₀ r, ‖H ζ ω‖ ≤ 1 / η₁)
    (hHmc : ContinuousOn (fun ζ => ∫ ω, H ζ ω ∂μ) (sphere z₀ r))
    {p : ℝ} (hp : 1 ≤ p) {B : ℝ}
    (hB : ∀ ζ ∈ sphere z₀ r, eLpNorm (fun ω => H ζ ω - ∫ ω', H ζ ω' ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal B) :
    eLpNorm (fun ω => deriv (fun ζ => H ζ ω) z₀ - ∫ ω', deriv (fun ζ => H ζ ω') z₀ ∂μ)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (B / r) := by
  have hball' : closedBall z₀ r ⊆ {ζ : ℂ | 0 < ζ.im} := fun ζ hζ => hη₁.trans_le (hball hζ)
  have hsph : ∀ ζ ∈ sphere z₀ r, 0 < ζ.im := fun ζ hζ => hball' (sphere_subset_closedBall hζ)
  set Λ := cauchyConst 1 with hΛ
  set w : ℂ → ℂ := fun ζ => 1 / (ζ - z₀) ^ (1 + 1) with hwdef
  set Hm : ℂ → ℂ := fun ζ => ∫ ω, H ζ ω ∂μ with hHmdef
  have hED := integral_deriv_eq hHm hHd hr hη₁ hball hHb
  simp only [iteratedDeriv_one] at hED
  have hrepH : ∀ᵐ ω ∂μ, deriv (fun ζ => H ζ ω) z₀ = Λ • ∮ ζ in C(z₀, r), w ζ • H ζ ω := by
    filter_upwards [hHd] with ω hω
    have := iteratedDeriv_eq_cauchy hω 1 hr hball'
    rwa [iteratedDeriv_one] at this
  have hci_Hm : CircleIntegrable (fun ζ => w ζ • Hm ζ) z₀ r :=
    ((continuousOn_weight hr).smul hHmc).circleIntegrable hr.le
  have hci_H : ∀ᵐ ω ∂μ, CircleIntegrable (fun ζ => w ζ • H ζ ω) z₀ r := by
    filter_upwards [hHd] with ω hω
    exact ((continuousOn_weight hr).smul ((hω.mono fun ζ hζ => hsph ζ hζ).continuousOn)).circleIntegrable
      hr.le
  set ν := volume.restrict (Set.Ioc (0 : ℝ) (2 * π)) with hν
  set G : ℝ → Ω → ℂ := fun θ ω =>
    deriv (circleMap z₀ r) θ • (w (circleMap z₀ r θ) •
      (H (circleMap z₀ r θ) ω - Hm (circleMap z₀ r θ))) with hGdef
  have hae : (fun ω => deriv (fun ζ => H ζ ω) z₀ - ∫ ω', deriv (fun ζ => H ζ ω') z₀ ∂μ) =ᵐ[μ]
      fun ω => Λ • ∫ θ, G θ ω ∂ν := by
    filter_upwards [hrepH, hci_H] with ω h1 h2
    rw [h1, hED, ← smul_sub, ← circleIntegral.integral_sub h2 hci_Hm]
    congr 1
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    congr 1
    funext θ
    simp only [hGdef, smul_sub]
  rw [eLpNorm_congr_ae hae]
  have hsmul : (fun ω => Λ • ∫ θ, G θ ω ∂ν) = Λ • fun ω => ∫ θ, G θ ω ∂ν := rfl
  rw [hsmul]
  refine eLpNorm_const_smul_le.trans ?_
  have hcm : ∀ θ, circleMap z₀ r θ ∈ sphere z₀ r := circleMap_mem_sphere z₀ hr.le
  have hHmθ : Continuous (fun θ => Hm (circleMap z₀ r θ)) :=
    hHmc.comp_continuous (continuous_circleMap z₀ r) hcm
  have hGmeas : Measurable (fun q : Ω × ℝ => G q.2 q.1) := by
    have hc2 : Measurable (fun q : Ω × ℝ => circleMap z₀ r q.2) :=
      (continuous_circleMap z₀ r).measurable.comp measurable_snd
    have h1 : Measurable (fun q : Ω × ℝ => H (circleMap z₀ r q.2) q.1) :=
      hHm.comp (f := fun q : Ω × ℝ => (circleMap z₀ r q.2, q.1)) (hc2.prodMk measurable_fst)
    have h2 : Measurable (fun q : Ω × ℝ => Hm (circleMap z₀ r q.2)) :=
      hHmθ.measurable.comp measurable_snd
    have h3 : Measurable (fun q : Ω × ℝ => w (circleMap z₀ r q.2)) :=
      (measurable_cauchyWeight z₀ 1).comp hc2
    have h4 : Measurable (fun q : Ω × ℝ => deriv (circleMap z₀ r) q.2) :=
      (continuous_deriv_circleMap z₀ r).measurable.comp measurable_snd
    exact h4.smul (h3.smul (h1.sub h2))
  set B' : ℝ≥0∞ := ENNReal.ofReal (r * (1 / r) ^ (1 + 1) * B) with hB'def
  have hBθ : ∀ θ, eLpNorm (G θ) (ENNReal.ofReal p) μ ≤ B' := by
    intro θ
    have hG : G θ = (deriv (circleMap z₀ r) θ * w (circleMap z₀ r θ)) •
        fun ω => H (circleMap z₀ r θ) ω - Hm (circleMap z₀ r θ) := by
      funext ω; simp only [hGdef, Pi.smul_apply, smul_eq_mul]; ring
    rw [hG]
    refine eLpNorm_const_smul_le.trans ?_
    have hn : ‖deriv (circleMap z₀ r) θ * w (circleMap z₀ r θ)‖ₑ =
        ENNReal.ofReal (r * (1 / r) ^ (1 + 1)) := by
      rw [← ofReal_norm, norm_mul, norm_deriv_circleMap hr.le, hwdef, norm_cauchyWeight (hcm θ) 1]
    rw [hn, hB'def, ENNReal.ofReal_mul (p := r * (1 / r) ^ (1 + 1)) (q := B) (by positivity)]
    gcongr
    exact hB _ (hcm θ)
  have hmink := eLpNorm_integral_le_measure_mul (ν := ν) hGmeas hp hBθ
  have hνu : ν Set.univ = ENNReal.ofReal (2 * π) := by
    rw [hν, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [hνu] at hmink
  calc ‖Λ‖ₑ * eLpNorm (fun ω => ∫ θ, G θ ω ∂ν) (ENNReal.ofReal p) μ
      ≤ ‖Λ‖ₑ * (ENNReal.ofReal (2 * π) * B') := by gcongr
    _ = ENNReal.ofReal (1 / (2 * π) * (2 * π * (r * (1 / r) ^ (1 + 1) * B))) := by
        rw [← ofReal_norm, hΛ, norm_cauchyConst_one, hB'def, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (B / r) := by
        congr 1; rw [show (1 + 1 : ℕ) = 2 from rfl]; field_simp

end Generic

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
