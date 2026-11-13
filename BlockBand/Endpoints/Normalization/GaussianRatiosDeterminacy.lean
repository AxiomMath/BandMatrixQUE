module

public import BlockBand.Endpoints.Normalization.GaussianRatiosPolarization

/-!
# Moment determinacy with exponential moments (one and several variables)

In the proof of the Gaussian ratios theorem and in Step 1 of the two-positive-clocks lemma, the
factorial bounds imply a finite exponential moment near zero for both limits; with
`|X_j| ≤ X₀`, this determines their joint laws. Exact measure theory.

* `eq_of_moments_of_integrable_exp`: two probability measures on `ℝ` with
  `∫ e^{s|x|} < ∞` (some `s > 0`) and equal moments are equal (complex mgf analytic on the strip
  `|Re z| < s`, equal Taylor coefficients at `0`, identity theorem, characteristic functions).
* `ext_of_map_dual`: (Cramér–Wold) finite measures on `ι → ℝ` with equal one-dimensional
  images under every continuous linear functional are equal.
* `eq_of_mixed_moments`: probability measures on `ι → ℝ` with
  `∫ e^{s Σ_i |x_i|} < ∞` and equal mixed moments `∫ Π_m x_{f m}` are equal.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

/-!
## One variable
-/

theorem Ioo_subset_interior_integrableExpSet {μ : Measure ℝ} {s : ℝ}
    (h : Integrable (fun x => Real.exp (s * |x|)) μ) :
    Set.Ioo (-s) s ⊆ interior (integrableExpSet id μ) := by
  refine interior_maximal (fun t ht => ?_) isOpen_Ioo
  refine h.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  simp only [id_eq]
  have h1 : t * x ≤ |t| * |x| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |t| ≤ s := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  nlinarith [abs_nonneg x]

theorem iteratedDeriv_complexMGF_zero {μ : Measure ℝ} {s : ℝ} (hs : 0 < s)
    (h : Integrable (fun x => Real.exp (s * |x|)) μ) (n : ℕ) :
    iteratedDeriv n (complexMGF id μ) 0 = ((∫ x, x ^ n ∂μ : ℝ) : ℂ) := by
  have h0 : (0 : ℂ).re ∈ interior (integrableExpSet id μ) :=
    Ioo_subset_interior_integrableExpSet h (by simp [hs])
  rw [iteratedDeriv_complexMGF h0 n]
  simp only [id_eq, zero_mul, Complex.exp_zero, mul_one]
  rw [← integral_complex_ofReal]
  simp

/-- **One-dimensional moment determinacy** under a finite exponential moment. -/
theorem eq_of_moments_of_integrable_exp {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s)
    (hμ : Integrable (fun x => Real.exp (s * |x|)) μ)
    (hν : Integrable (fun x => Real.exp (s * |x|)) ν)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) : μ = ν := by
  set U : Set ℂ := Complex.reLm ⁻¹' Set.Ioo (-s) s with hU
  have hUμ : U ⊆ {z | z.re ∈ interior (integrableExpSet id μ)} := fun z hz =>
    Ioo_subset_interior_integrableExpSet hμ hz
  have hUν : U ⊆ {z | z.re ∈ interior (integrableExpSet id ν)} := fun z hz =>
    Ioo_subset_interior_integrableExpSet hν hz
  have hf : AnalyticOnNhd ℂ (complexMGF id μ) U := analyticOnNhd_complexMGF.mono hUμ
  have hg : AnalyticOnNhd ℂ (complexMGF id ν) U := analyticOnNhd_complexMGF.mono hUν
  have hpre : IsPreconnected U := ((convex_Ioo (-s) s).linear_preimage Complex.reLm).isPreconnected
  have h0U : (0 : ℂ) ∈ U := by simp [hU, hs]
  have hball : Metric.ball (0 : ℂ) s ⊆ U := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz
    simp only [hU, Set.mem_preimage, Complex.reLm_coe, Set.mem_Ioo]
    have := Complex.abs_re_le_norm z
    constructor <;> [linarith [neg_abs_le z.re]; linarith [le_abs_self z.re]]
  have hev : complexMGF id μ =ᶠ[𝓝 0] complexMGF id ν := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hs] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz ((hf.mono hball).differentiableOn),
      ← Complex.taylorSeries_eq_on_ball' hz ((hg.mono hball).differentiableOn)]
    congr 1
    funext n
    rw [iteratedDeriv_complexMGF_zero hs hμ, iteratedDeriv_complexMGF_zero hs hν, hmom n]
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hpre h0U hev
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  refine heq ?_
  simp [hU, hs]

/-!
## Several variables
-/

variable {ι : Type*} [Fintype ι]

/-- **Cramér–Wold**: equal images under every continuous linear functional. -/
theorem ext_of_map_dual {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ L : StrongDual ℝ (ι → ℝ), μ.map L = ν.map L) : μ = ν := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, h L]

/-- `Σ_i |x_i|`. -/
def absSum (x : ι → ℝ) : ℝ := ∑ i, |x i|

theorem absSum_nonneg (x : ι → ℝ) : 0 ≤ absSum x := Finset.sum_nonneg fun i _ => abs_nonneg (x i)

theorem continuous_absSum : Continuous (absSum (ι := ι)) := by
  unfold absSum; fun_prop

theorem abs_monomial_le {r : ℕ} (f : Fin r → ι) (x : ι → ℝ) :
    |monomial f x| ≤ absSum x ^ r := by
  unfold monomial
  rw [Finset.abs_prod]
  calc ∏ m, |x (f m)| ≤ ∏ _m : Fin r, absSum x :=
        Finset.prod_le_prod₀ (fun m _ => abs_nonneg _) fun m _ =>
          Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _)
            (Finset.mem_univ (f m))
    _ = absSum x ^ r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [Fintype ι] in
theorem continuous_monomial {r : ℕ} (f : Fin r → ι) : Continuous (monomial f) := by
  unfold monomial; fun_prop

/-- `y^n ≤ n! s^{-n} e^{sy}` for `y ≥ 0`, `s > 0`. -/
theorem pow_le_factorial_mul_exp {y s : ℝ} (hy : 0 ≤ y) (hs : 0 < s) (n : ℕ) :
    y ^ n ≤ n.factorial / s ^ n * Real.exp (s * y) := by
  have h := Real.pow_div_factorial_le_exp (s * y) (mul_nonneg hs.le hy) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hs n)]
  linarith [mul_comm (s ^ n) (y ^ n)]

theorem integrable_absSum_pow {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ] {s : ℝ} (hs : 0 < s)
    (h : Integrable (fun x => Real.exp (s * absSum x)) μ) (n : ℕ) :
    Integrable (fun x => absSum x ^ n) μ := by
  refine (h.const_mul (n.factorial / s ^ n)).mono' (continuous_absSum.pow n).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (absSum_nonneg x) n)]
  exact pow_le_factorial_mul_exp (absSum_nonneg x) hs n

theorem integrable_monomial_of_exp {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ] {s : ℝ}
    (hs : 0 < s) (h : Integrable (fun x => Real.exp (s * absSum x)) μ) {r : ℕ}
    (f : Fin r → ι) : Integrable (monomial f) μ :=
  (integrable_absSum_pow hs h r).mono' (continuous_monomial f).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_monomial_le f x)

/-- A continuous linear functional on `ι → ℝ` is `x ↦ Σ_i c_i x_i`. -/
theorem dual_apply_eq_sum [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  have h := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
  rw [ContinuousLinearMap.coe_coe] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- **Moment determinacy on `ι → ℝ`** under a finite exponential moment of `Σ|x_i|`. -/
theorem eq_of_mixed_moments {μ ν : Measure (ι → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s)
    (hμ : Integrable (fun x => Real.exp (s * absSum x)) μ)
    (hν : Integrable (fun x => Real.exp (s * absSum x)) ν)
    (hmom : ∀ (r : ℕ) (f : Fin r → ι), ∫ x, monomial f x ∂μ = ∫ x, monomial f x ∂ν) :
    μ = ν := by
  classical
  refine ext_of_map_dual fun L => ?_
  set c : ι → ℝ := fun i => L (Pi.single i 1) with hc
  set C : ℝ := ∑ i, |c i| + 1 with hC
  have hC0 : 0 < C := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (c i); linarith
  have hLx : ∀ x, L x = ∑ i, c i * x i := dual_apply_eq_sum L
  have hLbound : ∀ x, |L x| ≤ C * absSum x := by
    intro x
    rw [hLx]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold absSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have := Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith
  have hLm : Measurable L := L.continuous.measurable
  have hexp : ∀ (ρ : Measure (ι → ℝ)), Integrable (fun x => Real.exp (s * absSum x)) ρ →
      Integrable (fun y => Real.exp (s / C * |y|)) (ρ.map L) := by
    intro ρ hρ
    rw [integrable_map_measure (by fun_prop) hLm.aemeasurable]
    refine hρ.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hC0]
    nlinarith [hLbound x]
  have hpow : ∀ (n : ℕ) (x : ι → ℝ), L x ^ n =
      ∑ p : Fin n → ι, (∏ k, c (p k)) * monomial p x := by
    intro n x
    rw [hLx, Fintype.sum_pow]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold monomial
    rw [← Finset.prod_mul_distrib]
  have hmomL : ∀ (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ],
      Integrable (fun x => Real.exp (s * absSum x)) ρ → ∀ n : ℕ,
      ∫ y, y ^ n ∂(ρ.map L) = ∑ p : Fin n → ι, (∏ k, c (p k)) * ∫ x, monomial p x ∂ρ := by
    intro ρ _ hρ n
    rw [integral_map hLm.aemeasurable (by fun_prop)]
    simp_rw [hpow n]
    rw [integral_finsetSum _ fun p _ => (integrable_monomial_of_exp hs hρ p).const_mul _]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  refine eq_of_moments_of_integrable_exp (div_pos hs hC0) (hexp μ hμ) (hexp ν hν) fun n => ?_
  rw [hmomL μ hμ n, hmomL ν hν n]
  exact Finset.sum_congr rfl fun p _ => by rw [hmom n p]

end BlockBand.Endpoints.Normalization
