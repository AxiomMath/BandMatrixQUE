module

public import BlockBand.SourceProcess.ClosingAux.Spectral
public import BlockBand.SourceProcess.Closing.PhaseAvg
public import BlockBand.SourceProcess.ComplexSourceLaw.Interface
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Analytic inputs of the fractional closing error

Spectral radius `ρ(N) < 1`, analyticity, Kolmogorov's conjugate inequality under `phaseLaw`, and
Jensen's inequality, used for `TargetT2`.

* `norm_lt_one_of_tendsto_pow`: `N^n → 0` puts every eigenvalue in the open unit disc.
* `exists_radius_scalar`: if `N^n → 0` there is `R > 1` with `1 - zN` invertible on `‖z‖ < R`
  and `z ↦ w₁* (1 - zN)⁻¹ w₂` complex differentiable on the ball (Gelfand: `ρ(N) < 1`;
  `spectrum.differentiableOn_inverse_one_sub_smul`, `L²` operator norm used inside the proof).
* `lintegral_phaseLaw_eq`: the uniform phase against Lebesgue measure on `(0, 2π]`.
* `lintegral_phase_kolmogorov`: Kolmogorov's conjugate inequality (a hypothesis) in the form
  `E_z|f|^p ≤ C (E_z|Im f|)^p` under `phaseLaw`, `C ≥ 0`.
* `lintegral_rpow_le_rpow_lintegral`: Jensen for `t ↦ t^p`, `0 < p < 1`, probability measures.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Matrix Filter Topology
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingAux
open BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `N^n → 0` puts every eigenvalue in the open unit disc. -/
theorem norm_lt_one_of_tendsto_pow {N : Matrix ι ι ℂ}
    (hN : Tendsto (fun n => N ^ n) atTop (𝓝 0)) {k : ℂ} {v : ι → ℂ} (hv : v ≠ 0)
    (hkv : N *ᵥ v = k • v) : ‖k‖ < 1 := by
  by_contra hk'
  have hk : 1 ≤ ‖k‖ := not_lt.1 hk'
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun i => not_not.1 fun hne => h ⟨i, hne⟩)
  have hpow : ∀ n : ℕ, N ^ n *ᵥ v = k ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mulVec_mulVec, hkv, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have hc : Continuous fun P : Matrix ι ι ℂ => (P *ᵥ v) i :=
    (continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)
  have ht := ((hc.tendsto 0).comp hN).norm
  simp only [Function.comp_def, zero_mulVec, Pi.zero_apply, hpow, Pi.smul_apply, smul_eq_mul,
    norm_zero] at ht
  have hle : ∀ n : ℕ, ‖v i‖ ≤ ‖k ^ n * v i‖ := fun n => by
    rw [norm_mul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hk)
  have h0 := ge_of_tendsto ht (Eventually.of_forall hle)
  exact hi (norm_le_zero_iff.1 h0)

open scoped Matrix.Norms.L2Operator in
/-- **Analyticity beyond the unit circle**: `N^n → 0` gives `R > 1` with `1 - zN` invertible and
`z ↦ w₁* (1 - zN)⁻¹ w₂` differentiable on `‖z‖ < R`. -/
theorem exists_radius_scalar {N : Matrix ι ι ℂ} (hN : Tendsto (fun n => N ^ n) atTop (𝓝 0))
    (w₁ w₂ : ι → ℂ) :
    ∃ R : ℝ, 1 < R ∧ (∀ z : ℂ, ‖z‖ < R → IsUnit (1 - z • N).det) ∧
      DifferentiableOn ℂ (fun z : ℂ => star w₁ ⬝ᵥ ((1 - z • N)⁻¹ *ᵥ w₂)) (Metric.ball 0 R) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨2, by norm_num, fun z _ => ?_, ?_⟩
    · rw [Matrix.det_isEmpty]
      exact isUnit_one
    · refine (differentiableOn_const (0 : ℂ)).congr fun z _ => ?_
      simp [dotProduct]
  have hlt : ∀ k ∈ spectrum ℂ N, ‖k‖₊ < (1 : ℝ≥0) := by
    intro k hk
    obtain ⟨v, hv, hkv⟩ := exists_eigen_of_mem_spectrum hk
    have h := norm_lt_one_of_tendsto_pow hN hv hkv
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
    exact h
  have hρ : spectralRadius ℂ N < (1 : ℝ≥0) :=
    spectrum.spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty N) hlt
  have h1 : (1 : ℝ≥0∞) < (spectralRadius ℂ N)⁻¹ := by
    have h := ENNReal.inv_lt_inv.2 (show spectralRadius ℂ N < 1 by exact_mod_cast hρ)
    simpa using h
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h1
  have hr1' : (1 : ℝ) < r := by exact_mod_cast hr1
  refine ⟨r, hr1', fun z hz => ?_, ?_⟩
  · refine (Matrix.isUnit_iff_isUnit_det _).1
      (spectrum.isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt ?_ hr2))
    have : ‖z‖₊ ≤ r := by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hz.le
    exact_mod_cast this
  · have hd := spectrum.differentiableOn_inverse_one_sub_smul (𝕜 := ℂ) (a := N) hr2
    let L : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => star w₁ ⬝ᵥ (M *ᵥ w₂)
        map_add' := fun M M' => by rw [add_mulVec, dotProduct_add]
        map_smul' := fun c M => by
          rw [smul_mulVec, dotProduct_smul]
          rfl }
    have hL := (LinearMap.toContinuousLinearMap L).differentiable.comp_differentiableOn hd
    refine (hL.mono Metric.ball_subset_closedBall).congr fun z _ => ?_
    rw [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', ←
      Matrix.nonsing_inv_eq_ringInverse]
    rfl

/-- The uniform phase against Lebesgue measure on `(0, 2π]`, for continuous `g ≥ 0`. -/
theorem lintegral_phaseLaw_eq {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ θ, 0 ≤ g θ) :
    ∫⁻ θ, ENNReal.ofReal (g θ) ∂phaseLaw =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * ∫ θ in Set.Ioc 0 (2 * Real.pi), g θ) := by
  rw [phaseLaw, lintegral_smul_measure, setLIntegral_congr Ico_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal
      ((hg.integrableOn_Icc (a := 0) (b := 2 * Real.pi)).mono_set Set.Ioc_subset_Icc_self)
      (ae_of_all _ hg0),
    smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]

/-- **Kolmogorov under `phaseLaw`**: `E_z|f|^p ≤ C (E_z|Im f|)^p`, `C ≥ 0`. -/
theorem lintegral_phase_kolmogorov (hK : KolmogorovConjugate) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℂ) (R : ℝ), 1 < R → DifferentiableOn ℂ f (Metric.ball 0 R) →
      f 0 = 0 →
      ∫⁻ θ, ENNReal.ofReal (‖f (phase θ)‖ ^ p) ∂phaseLaw ≤
        ENNReal.ofReal C * (∫⁻ θ, ENNReal.ofReal |(f (phase θ)).im| ∂phaseLaw) ^ p := by
  obtain ⟨C, hC⟩ := hK p hp0 hp1
  refine ⟨max C 0, le_max_right _ _, fun f R hR hd h0 => ?_⟩
  have hcont : Continuous fun θ => f (phase θ) :=
    hd.continuousOn.comp_continuous continuous_phase fun θ => by
      rw [Metric.mem_ball, dist_zero_right, norm_phase]
      exact hR
  have hg1 : Continuous fun θ => ‖f (phase θ)‖ ^ p :=
    hcont.norm.rpow_const fun _ => Or.inr hp0.le
  have hg2 : Continuous fun θ => |(f (phase θ)).im| :=
    (Complex.continuous_im.comp hcont).abs
  rw [lintegral_phaseLaw_eq hg1 fun _ => by positivity,
    lintegral_phaseLaw_eq hg2 fun _ => abs_nonneg _]
  have hK' : ∫ θ in Set.Ioc 0 (2 * Real.pi), ‖f (phase θ)‖ ^ p ≤
      C * (2 * Real.pi) ^ (1 - p) * (∫ θ in Set.Ioc 0 (2 * Real.pi), |(f (phase θ)).im|) ^ p :=
    hC f R hR hd h0
  set I1 := ∫ θ in Set.Ioc 0 (2 * Real.pi), ‖f (phase θ)‖ ^ p
  set I2 := ∫ θ in Set.Ioc 0 (2 * Real.pi), |(f (phase θ)).im|
  have hI2 : 0 ≤ I2 := setIntegral_nonneg measurableSet_Ioc fun _ _ => abs_nonneg _
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.ofReal_mul (le_max_right _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (2 * Real.pi)⁻¹ * (C * (2 * Real.pi) ^ (1 - p) * I2 ^ p) =
      C * ((2 * Real.pi)⁻¹ * I2) ^ p := by
    rw [Real.mul_rpow (by positivity) hI2, Real.inv_rpow h2π.le, Real.rpow_sub h2π,
      Real.rpow_one]
    field_simp
  calc (2 * Real.pi)⁻¹ * I1 ≤ (2 * Real.pi)⁻¹ * (C * (2 * Real.pi) ^ (1 - p) * I2 ^ p) :=
        mul_le_mul_of_nonneg_left hK' (by positivity)
    _ = C * ((2 * Real.pi)⁻¹ * I2) ^ p := e
    _ ≤ max C 0 * ((2 * Real.pi)⁻¹ * I2) ^ p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Jensen** for `t ↦ t^p`, `0 < p < 1`: `∫⁻ f^p ≤ (∫⁻ f)^p` under a probability measure. -/
theorem lintegral_rpow_le_rpow_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : ∫⁻ a, f a ^ p ∂μ ≤ (∫⁻ a, f a ∂μ) ^ p := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.inv_one_sub_inv hp0 hp1)
    (hf.pow_const p) (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have e : ∀ a, (f a ^ p) ^ p⁻¹ = f a := fun a => by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ, e,
    one_div, inv_inv] at h
  simpa using h

end BlockBand.SourceProcess.PhysApprox
