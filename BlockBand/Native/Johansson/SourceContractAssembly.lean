module

public import BlockBand.Native.Johansson.CornerInduction

/-!
# Johansson's formula (2.18): the source statement from the intermediate statements

The fields of `SourceContract` are derived from the intermediate statements of the proof.

* `Φ_N = κ det K_N` pointwise, `κ = (2πS)^{N/2} e^{Σd²/(2S)}` (`KernelFactorStatement`,
  `GaussDetScalingStatement`);
* `det K_N ≥ 0` everywhere: invariance under simultaneous permutation, sorting (`Tuple.sort`),
  zero at ties, `ProfileNonnegStatement` on the open chamber;
* the normalization `C κ = 1`, from `FactorialFromOrderedStatement` at `k = 0`,
  `factorialCorrelationMeasure_univ` and `KernelMarginalStatement` at `k = 0`;
* the field `correlations` from `FactorialFromOrderedStatement` and `KernelMarginalStatement` at
  every `k ≤ N`;
* the field `determinant_real_nonnegative` from `ContourKernelStatement` (the contour-integral
  kernel is real) and the Gaudin marginal;
* the fields `vertical_integrable`, `circle_integrable` as stated.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory ProbabilityTheory Polynomial
open BlockBand.External.Johansson
open BlockBand.DeterminantScore.SpectralConvexity (vandermonde weylChamber)
open scoped ENNReal NNReal BigOperators

/-- `κ = (2πS)^{N/2} e^{Σd²/(2S)}`. -/
theorem profile_eq_kappa_mul_kernelMatDet (hK : KernelFactorStatement)
    (hG : GaussDetScalingStatement) {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (hd : StrictMono d) (x : Fin N → ℝ) :
    orderedProfile S d x = Real.sqrt (2 * Real.pi * S) ^ N *
      Real.exp ((∑ j, d j ^ 2) / (2 * (S : ℝ))) * kernelMatDet S d x := by
  rw [hK S hS d hd x, hG S hS d x]
  have hs : 0 < Real.sqrt (2 * Real.pi * S) := Real.sqrt_pos.2 (by positivity)
  have he : Real.exp (-(∑ i, x i ^ 2 + ∑ j, d j ^ 2) / (2 * (S : ℝ))) =
      Real.exp (-(∑ i, x i ^ 2) / (2 * (S : ℝ))) * Real.exp (-(∑ j, d j ^ 2) / (2 * (S : ℝ))) := by
    rw [← Real.exp_add]; congr 1; ring
  have he' : Real.exp ((∑ j, d j ^ 2) / (2 * (S : ℝ))) *
      Real.exp (-(∑ j, d j ^ 2) / (2 * (S : ℝ))) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]; congr 1; ring
  have hp : Real.sqrt (2 * Real.pi * S) ^ N * (Real.sqrt (2 * Real.pi * S))⁻¹ ^ N = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow]
  rw [he, orderedProfile]
  calc vandermonde x / vandermonde d * expDet S d x * Real.exp (-(∑ i, x i ^ 2) / (2 * (S : ℝ)))
      = (Real.sqrt (2 * Real.pi * S) ^ N * (Real.sqrt (2 * Real.pi * S))⁻¹ ^ N) *
          (Real.exp ((∑ j, d j ^ 2) / (2 * (S : ℝ))) *
            Real.exp (-(∑ j, d j ^ 2) / (2 * (S : ℝ)))) *
          (vandermonde x / vandermonde d * expDet S d x *
            Real.exp (-(∑ i, x i ^ 2) / (2 * (S : ℝ)))) := by rw [hp, he']; ring
    _ = _ := by ring

/-- `κ > 0`. -/
theorem kappa_pos {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ) :
    0 < Real.sqrt (2 * Real.pi * S) ^ N * Real.exp ((∑ j, d j ^ 2) / (2 * (S : ℝ))) := by
  have hs : 0 < Real.sqrt (2 * Real.pi * S) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- `det K` is invariant under simultaneous permutation of the points. -/
theorem kernelMatDet_comp_perm {n k : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (x : Fin k → ℝ)
    (σ : Equiv.Perm (Fin k)) : kernelMatDet S d (x ∘ σ) = kernelMatDet S d x := by
  unfold kernelMatDet
  exact Matrix.det_submatrix_equiv_self σ (Matrix.of fun i l => sourceKernel S d (x i) (x l))

/-- `det K` vanishes at a tie. -/
theorem kernelMatDet_eq_zero_of_eq {n k : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (x : Fin k → ℝ)
    {i j : Fin k} (hij : i ≠ j) (hx : x i = x j) : kernelMatDet S d x = 0 := by
  unfold kernelMatDet
  refine Matrix.det_zero_of_row_eq hij ?_
  funext l
  simp [hx]

/-- **`det K_N ≥ 0` at every point.** -/
theorem kernelMatDet_nonneg (hK : KernelFactorStatement) (hG : GaussDetScalingStatement)
    (hP : ProfileNonnegStatement) {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (hd : StrictMono d) (x : Fin N → ℝ) : 0 ≤ kernelMatDet S d x := by
  rw [← kernelMatDet_comp_perm S d x (Tuple.sort x)]
  set y := x ∘ Tuple.sort x with hy
  have hmono : Monotone y := Tuple.monotone_sort x
  by_cases hs : StrictMono y
  · have h1 := hP S hS d hd y hs
    rw [profile_eq_kappa_mul_kernelMatDet hK hG S hS d hd y] at h1
    exact (mul_nonneg_iff_of_pos_left (kappa_pos S hS d)).1 h1
  · have hinj : ¬ Function.Injective y := fun h => hs (hmono.strictMono_of_injective h)
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hinj
    rw [kernelMatDet_eq_zero_of_eq S d y hne hij]

/-- `det K_k ≥ 0` at every point, `k ≤ N` (Gaudin marginal of `det K_N ≥ 0`). -/
theorem kernelMatDet_nonneg_of_le (hK : KernelFactorStatement) (hG : GaussDetScalingStatement)
    (hP : ProfileNonnegStatement) (hM : KernelMarginalStatement) {N : ℕ} (S : ℝ≥0) (hS : 0 < S)
    (d : Fin N → ℝ) (hd : StrictMono d) {k : ℕ} (hk : k ≤ N) (x : Fin k → ℝ) :
    0 ≤ kernelMatDet S d x := by
  have h := (hM S hS d hd hk x).2
  have hI : 0 ≤ ∫ y : Fin (N - k) → ℝ, kernelMatDet S d (appendCast hk x y) :=
    integral_nonneg fun y => kernelMatDet_nonneg hK hG hP S hS d hd _
  rw [h] at hI
  have hf : (0 : ℝ) < ((N - k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact (mul_nonneg_iff_of_pos_left hf).1 hI

/-- The marginal identity in `ℝ≥0∞` form. -/
theorem lintegral_marginal (hK : KernelFactorStatement) (hG : GaussDetScalingStatement)
    (hP : ProfileNonnegStatement) (hM : KernelMarginalStatement) {N : ℕ} (S : ℝ≥0) (hS : 0 < S)
    (d : Fin N → ℝ) (hd : StrictMono d) {k : ℕ} (hk : k ≤ N) (x : Fin k → ℝ) {c : ℝ}
    (hc : 0 ≤ c) :
    ∫⁻ y : Fin (N - k) → ℝ, ENNReal.ofReal (c * kernelMatDet S d (appendCast hk x y)) =
      ENNReal.ofReal (c * (((N - k).factorial : ℝ) * kernelMatDet S d x)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((hM S hS d hd hk x).1.const_mul c)
    (Filter.Eventually.of_forall fun y => mul_nonneg hc (kernelMatDet_nonneg hK hG hP S hS d hd _)),
    integral_const_mul, (hM S hS d hd hk x).2]

/-- The determinant of the contour-integral kernel is the real `det K`. -/
theorem kernelDeterminant_eq (hC : ContourKernelStatement) {N : ℕ} (hN : 0 < N) (S : ℝ≥0)
    (hS : 0 < S) (d : Fin N → ℝ) (hd : StrictMono d) {R L : ℝ} (hRL : AdmissibleContours d R L)
    {k : ℕ} (x : Fin k → ℝ) :
    kernelDeterminant S d R L x = (kernelMatDet S d x : ℂ) := by
  unfold kernelDeterminant kernelMatDet
  rw [← Complex.ofRealHom_eq_coe, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, hC hN S hS d hd R L hRL]

/-- **The source statement from the intermediate statements.** -/
theorem sourceContract_of_statements (hO : OrderedLawStatement) (hP : ProfileNonnegStatement)
    (hK : KernelFactorStatement) (hG : GaussDetScalingStatement) (hM : KernelMarginalStatement)
    (hF : FactorialFromOrderedStatement) (hC : ContourKernelStatement)
    (hV : VerticalIntegrableStatement) (hCi : CircleIntegrableStatement) : SourceContract where
  vertical_integrable := hV
  circle_integrable := hCi
  determinant_real_nonnegative := by
    intro N hN S hS d hd R L hRL k hk x
    rw [kernelDeterminant_eq hC hN S hS d hd hRL x, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, kernelMatDet_nonneg_of_le hK hG hP hM S hS d hd hk x⟩
  correlations := by
    intro N hN S hS d hd R L hRL k hk
    obtain ⟨C, hC0, hlaw⟩ := hO S hS d hd
    set κ := Real.sqrt (2 * Real.pi * S) ^ N * Real.exp ((∑ j, d j ^ 2) / (2 * (S : ℝ))) with hκ
    have hκ0 : 0 < κ := kappa_pos S hS d
    have hprof : ∀ z, orderedProfile S d z = κ * kernelMatDet S d z :=
      profile_eq_kappa_mul_kernelMatDet hK hG S hS d hd
    set f : (Fin N → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (C * orderedProfile S d z) with hfdef
    have hfC : ∀ z, f z = ENNReal.ofReal ((C * κ) * kernelMatDet S d z) := by
      intro z; simp only [hfdef, hprof, mul_assoc]
    have hfm : Measurable f :=
      ENNReal.measurable_ofReal.comp ((continuous_orderedProfile S d).measurable.const_mul C)
    have hfsym : ∀ (σ : Equiv.Perm (Fin N)) (z : Fin N → ℝ), f (z ∘ σ) = f z := by
      intro σ z; rw [hfC, hfC, kernelMatDet_comp_perm]
    have hord : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
        ∫⁻ A, g (spectralTuple (Equiv.refl (Fin N)).toEmbedding A) ∂matrixMeasure S d =
          ∫⁻ lam in weylChamber N, g lam * f lam := by
      intro g hg
      rw [hlaw g hg, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun lam => ?_
      simp only [hfdef]
      rw [ENNReal.ofReal_mul hC0.le]
      ring
    -- normalization `C κ = 1`
    have hCκ0 : 0 ≤ C * κ := (mul_pos hC0 hκ0).le
    have hnorm : C * κ = 1 := by
      have h0 := congrArg (fun μ : Measure (Fin 0 → ℝ) => μ Set.univ)
        (hF S d f hfm hfsym hord (Nat.zero_le N))
      rw [factorialCorrelationMeasure_univ, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, lintegral_unique] at h0
      simp_rw [hfC] at h0
      rw [lintegral_marginal hK hG hP hM S hS d hd (Nat.zero_le N) _ hCκ0, kernelMatDet_zero,
        mul_one] at h0
      have hvol : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [volume_pi, Measure.pi_univ]; simp
      rw [hvol, mul_one, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
        ENNReal.ofReal_mul hCκ0, ENNReal.ofReal_natCast, mul_comm (ENNReal.ofReal _),
        ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.factorial_pos N).ne')
          (ENNReal.natCast_ne_top _), one_mul] at h0
      exact (ENNReal.ofReal_eq_one.1 h0.symm)
    rw [hF S d f hfm hfsym hord hk]
    congr 1
    funext x
    simp_rw [hfC, hnorm]
    rw [lintegral_marginal hK hG hP hM S hS d hd hk x zero_le_one, one_mul,
      kernelDeterminant_eq hC hN S hS d hd hRL x, Complex.ofReal_re,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← mul_assoc,
      ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.factorial_pos _).ne')
        (ENNReal.natCast_ne_top _), one_mul]

end BlockBand.Native.Johansson
