module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorRadiusReduction

/-!
# Exact standard-Gaussian radius moments

This module supplies the dimension-exact squared-radius expectation and its Markov tail,
the radius component of the complex spherical small-ball argument of APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory

/-- A scalar coordinate of a standard Gaussian has squared expectation one. -/
theorem integral_sq_inner_stdGaussian {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E) (he : ‖e‖ = 1) :
    ∫ x, (inner ℝ e x) ^ 2 ∂stdGaussian E = 1 := by
  let L : StrongDual ℝ E := innerSL ℝ e
  have hv := variance_dual_stdGaussian L
  rw [variance_eq_integral (L.continuous.measurable.aemeasurable),
    integral_strongDual_stdGaussian] at hv
  simpa [L, he] using hv

/-- The exact squared-radius expectation of a standard Gaussian equals real dimension. -/
theorem integral_sq_norm_stdGaussian (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∫ x, ‖x‖ ^ 2 ∂stdGaussian E = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hpoint : (fun x : E => ‖x‖ ^ 2) =
      fun x => ∑ i, (inner ℝ (b i) x) ^ 2 := by
    funext x
    exact (b.sum_sq_inner_right x).symm
  rw [hpoint]
  rw [integral_finsetSum Finset.univ]
  · simp [integral_sq_inner_stdGaussian, b]
  · intro i _
    simpa using ((IsGaussian.memLp_two_id (μ := stdGaussian E)).continuousLinearMap_comp
      (innerSL ℝ (b i))).integrable_sq

/-- The squared radius of a finite-dimensional standard Gaussian is integrable. -/
theorem integrable_sq_norm_stdGaussian (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    Integrable (fun x : E => ‖x‖ ^ 2) (stdGaussian E) := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : (fun x : E => ‖x‖ ^ 2) =
      fun x => ∑ i, (inner ℝ (b i) x) ^ 2 := by
    funext x
    exact (b.sum_sq_inner_right x).symm
  rw [hsum]
  apply integrable_finsetSum
  intro i _
  simpa using ((IsGaussian.memLp_two_id (μ := stdGaussian E)).continuousLinearMap_comp
    (innerSL ℝ (b i))).integrable_sq

/-- Markov's inequality at twice the exact squared-radius mean. -/
theorem stdGaussian_sq_norm_tail_le_half (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (hd : 0 < Module.finrank ℝ E) :
    stdGaussian E {x | (2 * Module.finrank ℝ E : ℝ) < ‖x‖ ^ 2} ≤
      ENNReal.ofReal (1 / 2 : ℝ) := by
  let d : ℝ := Module.finrank ℝ E
  let f : E → ℝ := fun x => ‖x‖ ^ 2 / (2 * d)
  have hdR : 0 < d := by
    dsimp [d]
    exact_mod_cast hd
  have hf : Integrable f (stdGaussian E) :=
    (integrable_sq_norm_stdGaussian E).div_const _
  have hmarkov := hf.measure_le_integral (ae_of_all _ fun x => by
      dsimp [f]
      positivity) (s := {x : E | (2 * d) < ‖x‖ ^ 2}) (fun x hx => by
        dsimp [f] at ⊢
        change 2 * d < ‖x‖ ^ 2 at hx
        apply (le_div_iff₀ (by positivity)).2
        nlinarith)
  rw [integral_div, integral_sq_norm_stdGaussian] at hmarkov
  have heq : (Module.finrank ℝ E : ℝ) / (2 * d) = 1 / 2 := by
    dsimp [d]
    field_simp
  rw [heq] at hmarkov
  exact hmarkov

/-- For a standard complex Gaussian in `ℂ^N`, the squared radius exceeds
`4N` with probability at most one half.  The factor `4N` is twice its real dimension
`2N`. -/
theorem stdGaussian_complex_sq_norm_tail_le_half {N : ℕ} (hN : 0 < N) :
    stdGaussian (EuclideanSpace ℂ (Fin N))
      {x | (4 * N : ℝ) < ‖x‖ ^ 2} ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin N)),
      Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  have htail := stdGaussian_sq_norm_tail_le_half
    (EuclideanSpace ℂ (Fin N)) (by rw [hdim]; omega)
  rw [hdim] at htail
  have hset : {x : EuclideanSpace ℂ (Fin N) | 4 * (N : ℝ) < ‖x‖ ^ 2} =
      {x | 2 * ((2 * N : ℕ) : ℝ) < ‖x‖ ^ 2} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    push_cast
    ring_nf
  rw [hset]
  exact htail

/-- Radius form used directly by the spherical truncation reduction: a standard complex
Gaussian lies outside radius `2√N` with probability at most one half. -/
theorem stdGaussian_complex_norm_tail_le_half {N : ℕ} (hN : 0 < N) :
    stdGaussian (EuclideanSpace ℂ (Fin N))
      {x | 2 * Real.sqrt N < ‖x‖} ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  refine (measure_mono ?_).trans (stdGaussian_complex_sq_norm_tail_le_half hN)
  intro x hx
  change 2 * Real.sqrt (N : ℝ) < ‖x‖ at hx
  change (4 * N : ℝ) < ‖x‖ ^ 2
  have hsqrt : (Real.sqrt (N : ℝ)) ^ 2 = N := by
    rw [Real.sq_sqrt]
    positivity
  have hn : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hxnorm : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

end PSSSNative.BlockBand.PSSS
