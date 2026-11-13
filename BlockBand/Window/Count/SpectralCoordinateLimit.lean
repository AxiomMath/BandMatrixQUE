module

public import BlockBand.Window.Count.SpectralCoordinateDeriv

/-!
# `C¹` trace functions along affine Hermitian families

*Setting.* `E` finite-dimensional real normed space, `L : E →ₗ[ℝ] Matrix n n ℂ`, `F` a
matrix with `L x + F` Hermitian for all `x`, and `f : ℝ → ℝ` of class `C¹` (no growth or
boundedness condition is needed here).

*Result* (`hasFDerivAt_spectralSum`, `continuous_traceDeriv`): `x ↦ Tr f(L x + F)` has
Fréchet derivative `v ↦ Re Tr(f'(L x + F) · L v)` at every `x`, and this derivative is
continuous in `x` for the operator norm.

*Route.* Polynomial approximation on the spectral interval `[-R, R]` of a unit ball
(Weierstrass for `f'`, antiderivatives normalized at `0`, mean value theorem), and Mathlib's
`hasFDerivAt_of_tendstoUniformlyOn` / `TendstoUniformlyOn.continuousOn`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count.SpectralCalculus

open Matrix Filter Topology Polynomial Set

/-!
## Polynomial approximation of a `C¹` function together with its derivative
-/

/-- The antiderivative `Σ_k q_k X^{k+1}/(k+1)` of a real polynomial. -/
def antideriv (q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k / (k + 1)) * X ^ (k + 1)

theorem derivative_antideriv (q : ℝ[X]) : derivative (antideriv q) = q := by
  rw [antideriv, derivative_sum]
  conv_rhs => rw [q.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]
  congr 2
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem eval_zero_antideriv (q : ℝ[X]) : (antideriv q).eval 0 = 0 := by
  simp [antideriv, eval_finsetSum]

/-- For `f ∈ C¹` and `R ≥ 0`, polynomials `p` with `|p - f| ≤ R ε` and `|p' - f'| ≤ ε` on
`[-R, R]`. -/
theorem exists_poly_approx {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 ≤ R) {ε : ℝ}
    (hε : 0 < ε) : ∃ p : ℝ[X], (∀ y ∈ Icc (-R) R, |p.eval y - f y| ≤ R * ε) ∧
      ∀ y ∈ Icc (-R) R, |(derivative p).eval y - deriv f y| ≤ ε := by
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-R) R (deriv f)
    (hf.continuous_deriv le_rfl).continuousOn ε hε
  refine ⟨C (f 0) + antideriv q, ?_, ?_⟩
  · intro y hy
    have hd : derivative (C (f 0) + antideriv q) = q := by
      rw [derivative_add, derivative_C, zero_add, derivative_antideriv]
    have hdiff : ∀ z ∈ Icc (-R) R,
        DifferentiableAt ℝ (fun z => (C (f 0) + antideriv q).eval z - f z) z := fun z _ =>
      (Polynomial.differentiableAt _).sub ((hf.differentiable one_ne_zero) z)
    have hbound : ∀ z ∈ Icc (-R) R,
        ‖deriv (fun z => (C (f 0) + antideriv q).eval z - f z) z‖ ≤ ε := by
      intro z hz
      rw [deriv_fun_sub (Polynomial.differentiableAt _) ((hf.differentiable one_ne_zero) z),
        Polynomial.deriv, hd, Real.norm_eq_abs]
      exact (hq z hz).le
    have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc (-R) R) h0 hy
    simp only [eval_add, eval_C, eval_zero_antideriv, add_zero, sub_self, sub_zero,
      Real.norm_eq_abs] at hmvt
    have hy' : |y| ≤ R := abs_le.mpr ⟨hy.1, hy.2⟩
    calc |(C (f 0) + antideriv q).eval y - f y| ≤ ε * |y| := by
          simpa [eval_add, eval_C] using hmvt
      _ ≤ ε * R := by gcongr
      _ = R * ε := by ring
  · intro y hy
    rw [derivative_add, derivative_C, zero_add, derivative_antideriv]
    exact (hq y hy).le

/-!
## The main differentiability theorem
-/

variable {n : Type*} [Fintype n]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuous_entry_sum (L : E →ₗ[ℝ] Matrix n n ℂ) (F : Matrix n n ℂ) :
    Continuous fun x => ∑ a, ∑ b, ‖(L x + F) a b‖ := by
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  have : (fun x => ‖(L x + F) a b‖) = fun x => ‖entryCLM L a b x + F a b‖ := rfl
  rw [this]
  exact ((entryCLM L a b).continuous.add continuous_const).norm

variable [DecidableEq n]

/-- The candidate derivative `v ↦ Re Tr(g(H) · L v)`. -/
def traceDeriv (L : E →ₗ[ℝ] Matrix n n ℂ) (g : ℝ → ℝ) (M : Matrix n n ℂ) : E →L[ℝ] ℝ :=
  trCLM L (fcalc g M)

/-- **Local statement.** At every `x₀`, `x ↦ Tr f(L x + F)` has derivative
`traceDeriv L f' (L x₀ + F)`, and `x ↦ traceDeriv L f' (L x + F)` is continuous at `x₀`. -/
theorem hasFDerivAt_spectralSum_and_continuousAt (L : E →ₗ[ℝ] Matrix n n ℂ) (F : Matrix n n ℂ)
    (hH : ∀ x, (L x + F).IsHermitian) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x₀ : E) :
    HasFDerivAt (fun x => spectralSum f (L x + F)) (traceDeriv L (deriv f) (L x₀ + F)) x₀ ∧
      ContinuousAt (fun x => traceDeriv L (deriv f) (L x + F)) x₀ := by
  set s : Set E := Metric.ball x₀ 1 with hs
  -- spectral radius bound on the closed unit ball
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall x₀ 1).exists_bound_of_continuousOn
    (continuous_entry_sum L F).continuousOn
  set R : ℝ := max C₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hspec : ∀ x ∈ s, ∀ j, (hH x).eigenvalues j ∈ Icc (-R) R := by
    intro x hx j
    have h1 := abs_eigenvalues_le (hH x) j
    have h2 := hC₀ x (Metric.ball_subset_closedBall hx)
    have h3 : |(hH x).eigenvalues j| ≤ R :=
      h1.trans ((Real.le_norm_self _).trans (h2.trans (le_max_left _ _)))
    exact ⟨by linarith [neg_abs_le ((hH x).eigenvalues j)],
      (le_abs_self _).trans h3⟩
  -- approximating polynomials
  have hεm : ∀ m : ℕ, (0 : ℝ) < 1 / ((m : ℝ) + 1) := fun m => by positivity
  choose p hp0 hp1 using fun m : ℕ => exists_poly_approx hf hR (hεm m)
  set N : ℝ := (Fintype.card n : ℝ) with hN
  set B : ℝ := entryBound L with hB
  have hBnn : 0 ≤ B := entryBound_nonneg L
  set fn : ℕ → E → ℝ := fun m x => (trace (aeval (L x + F) (p m))).re with hfn
  set fn' : ℕ → E → (E →L[ℝ] ℝ) :=
    fun m x => trCLM L (aeval (L x + F) (derivative (p m))) with hfn'
  set g' : E → (E →L[ℝ] ℝ) := fun x => traceDeriv L (deriv f) (L x + F) with hg'
  have hlim0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- uniform convergence of the derivatives
  have hunif : TendstoUniformlyOn fn' g' atTop s := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hl : Tendsto (fun m : ℕ => N * B * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hlim0.const_mul (N * B)
    filter_upwards [(tendsto_order.1 hl).2 ε hε] with m hm
    intro x hx
    rw [dist_eq_norm, hg', hfn']
    simp only [traceDeriv]
    rw [fcalc_eq (hH x), ← cfc_eval_eq_aeval (hH x), ← trCLM_sub, ← cfc_sub' (hH x)]
    refine (norm_trCLM_cfc_le L (hH x) _).trans_lt (lt_of_le_of_lt ?_ hm)
    rw [show N * B * (1 / ((m : ℝ) + 1)) = N * (1 / ((m : ℝ) + 1)) * entryBound L by
      rw [hB]; ring]
    refine mul_le_mul_of_nonneg_right ?_ (entryBound_nonneg L)
    calc ∑ j, |deriv f ((hH x).eigenvalues j) - (derivative (p m)).eval ((hH x).eigenvalues j)|
        ≤ ∑ _j : n, 1 / ((m : ℝ) + 1) := Finset.sum_le_sum fun j _ => by
          rw [abs_sub_comm]; exact hp1 m _ (hspec x hx j)
      _ = N * (1 / ((m : ℝ) + 1)) := by simp [hN]
  -- derivatives of the approximants
  have hder : ∀ m, ∀ x ∈ s, HasFDerivAt (fn m) (fn' m x) x := fun m x _ =>
    hasFDerivAt_re_trace_aeval L F (p m) x
  -- pointwise convergence of the approximants
  have hpt : ∀ x ∈ s, Tendsto (fun m => fn m x) atTop (𝓝 (spectralSum f (L x + F))) := by
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    have hl2 : Tendsto (fun m : ℕ => N * R * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hlim0.const_mul (N * R)
    refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) hl2
    rw [Real.dist_eq, hfn]
    simp only
    rw [← cfc_eval_eq_aeval (hH x), re_trace_cfc (hH x), spectralSum_eq (hH x),
      ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(p m).eval ((hH x).eigenvalues j) - f ((hH x).eigenvalues j)|
        ≤ ∑ _j : n, R * (1 / ((m : ℝ) + 1)) := Finset.sum_le_sum fun j _ =>
          hp0 m _ (hspec x hx j)
      _ = N * R * (1 / ((m : ℝ) + 1)) := by simp [hN, mul_assoc]
  have hx₀ : x₀ ∈ s := Metric.mem_ball_self one_pos
  refine ⟨hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hunif hder hpt hx₀, ?_⟩
  have hcont : ContinuousOn g' s := hunif.continuousOn
    (Filter.Frequently.of_forall fun m => (continuous_trCLM_aeval L F _).continuousOn)
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds hx₀)

/-- **Trace derivative.** `x ↦ Tr f(L x + F)` has derivative `v ↦ Re Tr(f'(L x + F) L v)`. -/
theorem hasFDerivAt_spectralSum (L : E →ₗ[ℝ] Matrix n n ℂ) (F : Matrix n n ℂ)
    (hH : ∀ x, (L x + F).IsHermitian) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : E) :
    HasFDerivAt (fun x => spectralSum f (L x + F)) (traceDeriv L (deriv f) (L x + F)) x :=
  (hasFDerivAt_spectralSum_and_continuousAt L F hH hf x).1

/-- **Continuity of the trace derivative** in operator norm. -/
theorem continuous_traceDeriv (L : E →ₗ[ℝ] Matrix n n ℂ) (F : Matrix n n ℂ)
    (hH : ∀ x, (L x + F).IsHermitian) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous fun x => traceDeriv L (deriv f) (L x + F) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_spectralSum_and_continuousAt L F hH hf x).2

/-- **`C¹` regularity** of `x ↦ Tr f(L x + F)`. -/
theorem contDiff_spectralSum (L : E →ₗ[ℝ] Matrix n n ℂ) (F : Matrix n n ℂ)
    (hH : ∀ x, (L x + F).IsHermitian) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 fun x => spectralSum f (L x + F) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_spectralSum L F hH hf x).differentiableAt, ?_⟩
  have : fderiv ℝ (fun x => spectralSum f (L x + F)) =
      fun x => traceDeriv L (deriv f) (L x + F) :=
    funext fun x => (hasFDerivAt_spectralSum L F hH hf x).fderiv
  rw [this]
  exact continuous_traceDeriv L F hH hf

end BlockBand.Window.Count.SpectralCalculus
