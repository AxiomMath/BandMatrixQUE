module

public import Mathlib

/-!
# From interval counts to the Poisson-kernel density

* `neg_im_trace_inv_eq_sum_poissonKernel`: for Hermitian `B` and `η > 0`,
  `-Im Tr (B + iη)⁻¹ = Σ_λ η/(λ² + η²)` over the eigenvalues of `B` with multiplicity.
* `lintegral_sum_poissonKernel_le`: on any s-finite measure space, for finitely many
  measurable real "eigenvalue" functions `λ_i` whose mean count on every closed interval
  `[a,b]` is at most `K(b-a)`, the mean of `Σ_i η/(λ_i² + η²)` is at most `K π`, for every
  `η > 0` (layer-cake/Tonelli, the superlevel sets of the Poisson kernel are intervals,
  `∫ η/(x²+η²) dx = π`). Uniform in the measure, the functions and `η`.

No contract and no cited input.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory Set Complex Matrix
open scoped ENNReal

/-- The (unnormalized) Poisson kernel `η/(x² + η²)`. -/
def poissonKernel (η x : ℝ) : ℝ := η / (x ^ 2 + η ^ 2)

theorem poissonKernel_nonneg {η : ℝ} (hη : 0 < η) (x : ℝ) : 0 ≤ poissonKernel η x := by
  unfold poissonKernel
  positivity

theorem continuous_poissonKernel {η : ℝ} (hη : 0 < η) : Continuous (poissonKernel η) := by
  unfold poissonKernel
  exact continuous_const.div ((continuous_id.pow 2).add continuous_const)
    fun x => by positivity

theorem measurable_poissonKernel {η : ℝ} (hη : 0 < η) : Measurable (poissonKernel η) :=
  (continuous_poissonKernel hη).measurable

/-!
## Spectral formula
-/

section Spectral

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `-Im Tr (B + iη)⁻¹ = Σ_i η/(λ_i² + η²)` for Hermitian `B` (Mathlib eigenvalues). -/
theorem neg_im_trace_inv_eq_sum_poissonKernel {B : Matrix n n ℂ} (hB : B.IsHermitian)
    {η : ℝ} (hη : 0 < η) :
    -((B + ((η : ℂ) * I) • (1 : Matrix n n ℂ))⁻¹.trace).im =
      ∑ i, poissonKernel η (hB.eigenvalues i) := by
  set U : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ)
  set c : ℂ := (η : ℂ) * I
  have hU1 : U * star U = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.2
  set lam : n → ℂ := fun i => ((hB.eigenvalues i : ℝ) : ℂ)
  have hspec : B = U * Matrix.diagonal lam * star U := by
    have h := hB.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hne : ∀ i, lam i + c ≠ 0 := by
    intro i h
    have := congrArg Complex.im h
    simp [lam, c] at this
    exact hη.ne' this
  have hshift : B + c • (1 : Matrix n n ℂ) =
      U * Matrix.diagonal (fun i => lam i + c) * star U := by
    have : Matrix.diagonal (fun i => lam i + c) = Matrix.diagonal lam + c • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.mul_add, Matrix.add_mul, ← hspec, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hU1]
  have hinv : (B + c • (1 : Matrix n n ℂ))⁻¹ =
      U * Matrix.diagonal (fun i => (lam i + c)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hshift]
    calc U * Matrix.diagonal (fun i => lam i + c) * star U *
          (U * Matrix.diagonal (fun i => (lam i + c)⁻¹) * star U)
        = U * (Matrix.diagonal (fun i => lam i + c) * (star U * U) *
            Matrix.diagonal (fun i => (lam i + c)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU2, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          have : (fun i => (lam i + c) * (lam i + c)⁻¹) = fun _ => (1 : ℂ) := by
            funext i
            exact mul_inv_cancel₀ (hne i)
          rw [this, Matrix.diagonal_one, Matrix.mul_one, hU1]
  rw [hinv, Matrix.trace_mul_cycle, hU2, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [lam, c, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, zero_add, add_zero, poissonKernel]
  rw [neg_div, neg_neg]
  congr 1
  ring

end Spectral

/-!
## Superlevel sets and the integral of the kernel
-/

/-- Radius of the superlevel set `{s < η/(x²+η²)}`. -/
def poissonRadius (η s : ℝ) : ℝ := Real.sqrt (max 0 (η / s - η ^ 2))

theorem poissonRadius_nonneg (η s : ℝ) : 0 ≤ poissonRadius η s := Real.sqrt_nonneg _

theorem setOf_lt_poissonKernel {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    {x : ℝ | s < poissonKernel η x} = Ioo (-poissonRadius η s) (poissonRadius η s) := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_Ioo, poissonKernel, poissonRadius]
  have hd : 0 < x ^ 2 + η ^ 2 := by positivity
  have key : s < η / (x ^ 2 + η ^ 2) ↔ x ^ 2 < max 0 (η / s - η ^ 2) := by
    rw [lt_div_iff₀ hd]
    constructor
    · intro h
      rw [lt_max_iff]
      right
      rw [lt_sub_iff_add_lt, lt_div_iff₀ hs]
      linarith
    · intro h
      rcases lt_max_iff.mp h with h | h
      · exact absurd h (not_lt.mpr (sq_nonneg x))
      · rw [lt_sub_iff_add_lt, lt_div_iff₀ hs] at h
        linarith
  rw [key, ← sq_abs, ← Real.lt_sqrt (abs_nonneg x), abs_lt]

theorem integral_poissonKernel {η : ℝ} (hη : 0 < η) :
    Integrable (poissonKernel η) ∧ ∫ x, poissonKernel η x = Real.pi := by
  have hfun : poissonKernel η = fun x => η⁻¹ * (1 + (η⁻¹ * x) ^ 2)⁻¹ := by
    funext x
    unfold poissonKernel
    field_simp
    ring
  have hint : Integrable (fun x : ℝ => (1 + (η⁻¹ * x) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hη.ne')
  rw [hfun]
  refine ⟨hint.const_mul _, ?_⟩
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) η⁻¹,
    integral_univ_inv_one_add_sq, inv_inv, abs_of_pos hη, smul_eq_mul]
  field_simp

theorem lintegral_poissonKernel {η : ℝ} (hη : 0 < η) :
    ∫⁻ x, ENNReal.ofReal (poissonKernel η x) = ENNReal.ofReal Real.pi := by
  obtain ⟨hint, heq⟩ := integral_poissonKernel hη
  rw [← heq, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (poissonKernel_nonneg hη))]

/-!
## Mean density bound
-/

/-- `∫_{s>0} 1[s < c] ds = c⁺`. -/
theorem setLIntegral_Ioi_indicator_lt (c : ℝ) :
    ∫⁻ s in Ioi (0 : ℝ), (if s < c then (1 : ℝ≥0∞) else 0) = ENNReal.ofReal c := by
  have h : (fun s : ℝ => if s < c then (1 : ℝ≥0∞) else 0) = (Iio c).indicator 1 := by
    funext s
    simp [Set.indicator, mem_Iio]
  rw [h, lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
    Iio_inter_Ioi, Real.volume_Ioo, sub_zero]

/-- **Mean Poisson-kernel density from interval counts.** For measurable `λ_i : Ω → ℝ`
(`i : ι` finite) on an s-finite measure space with
`∫⁻ #{i : λ_i ∈ [a,b]} ≤ K (b - a)` for every `a ≤ b`, and every `η > 0`:
`∫⁻ Σ_i η/(λ_i² + η²) ≤ K π`. -/
theorem lintegral_sum_poissonKernel_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [SFinite P] {ι : Type*} [Fintype ι] (lam : ι → Ω → ℝ) (hlam : ∀ i, Measurable (lam i))
    {K : ℝ} (hK : 0 ≤ K)
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫⁻ ω, ∑ i, (Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) (lam i ω) ∂P ≤
        ENNReal.ofReal (K * (b - a)))
    {η : ℝ} (hη : 0 < η) :
    ∫⁻ ω, ENNReal.ofReal (∑ i, poissonKernel η (lam i ω)) ∂P ≤ ENNReal.ofReal (K * Real.pi) := by
  set N : Ω → ℝ → ℝ≥0∞ := fun ω s => ∑ i, if s < poissonKernel η (lam i ω) then 1 else 0
  have hN : Measurable (Function.uncurry N) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_snd
      ((measurable_poissonKernel hη).comp ((hlam i).comp measurable_fst))
  have hpt : ∀ ω, ENNReal.ofReal (∑ i, poissonKernel η (lam i ω)) =
      ∫⁻ s in Ioi (0 : ℝ), N ω s := by
    intro ω
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => poissonKernel_nonneg hη _),
      lintegral_finsetSum _ fun i _ => ?_]
    · exact Finset.sum_congr rfl fun i _ => (setLIntegral_Ioi_indicator_lt _).symm
    · exact Measurable.ite measurableSet_Iio measurable_const measurable_const
  simp_rw [hpt]
  rw [lintegral_lintegral_swap hN.aemeasurable]
  have hinner : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ ω, N ω s ∂P ≤
      ENNReal.ofReal K * volume {x : ℝ | s < poissonKernel η x} := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    set r := poissonRadius η s
    have hr : 0 ≤ r := poissonRadius_nonneg η s
    have hle : ∀ ω, N ω s ≤ ∑ i, (Icc (-r) r).indicator (fun _ => (1 : ℝ≥0∞)) (lam i ω) := by
      intro ω
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases h : s < poissonKernel η (lam i ω)
      · have hm : lam i ω ∈ {x : ℝ | s < poissonKernel η x} := h
        rw [setOf_lt_poissonKernel hη hs'] at hm
        rw [Set.indicator_of_mem (Ioo_subset_Icc_self hm)]
        simp [h]
      · simp [h]
    calc ∫⁻ ω, N ω s ∂P
        ≤ ∫⁻ ω, ∑ i, (Icc (-r) r).indicator (fun _ => (1 : ℝ≥0∞)) (lam i ω) ∂P :=
          lintegral_mono hle
      _ ≤ ENNReal.ofReal (K * (r - -r)) := hcount (-r) r (by linarith)
      _ = ENNReal.ofReal K * volume {x : ℝ | s < poissonKernel η x} := by
          rw [setOf_lt_poissonKernel hη hs', Real.volume_Ioo, ENNReal.ofReal_mul hK]
  calc ∫⁻ s in Ioi (0 : ℝ), ∫⁻ ω, N ω s ∂P
      ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal K * volume {x : ℝ | s < poissonKernel η x} :=
        setLIntegral_mono' measurableSet_Ioi hinner
    _ = ENNReal.ofReal K * ∫⁻ s in Ioi (0 : ℝ), volume {x : ℝ | s < poissonKernel η x} := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (poissonKernel η x) := by
        rw [lintegral_eq_lintegral_meas_lt volume
          (Filter.Eventually.of_forall (poissonKernel_nonneg hη))
          (measurable_poissonKernel hη).aemeasurable]
    _ = ENNReal.ofReal (K * Real.pi) := by
        rw [lintegral_poissonKernel hη, ENNReal.ofReal_mul hK]

end BlockBand.Wegner
