module

public import BlockBand.GaussianBulk.ExternalSineHomologyLine
public import BlockBand.GaussianBulk.ExternalSineHomologyPath

/-!
# Deforming the `z`-circle onto the grafted level loop

The `z`-contour of Johansson's double contour kernel is moved from a circle onto the grafted
level loop used for the steepest-descent analysis.

* `verticalIntegral_eq_numerator`: `V_L(z) = kernelNumerator(z) · (∏_j (z - d_j))⁻¹` with
  `kernelNumerator = exp((2uz-z²)/(2S)) · cauchyLine(lineAmplitude)(L, ·)` holomorphic on
  `Re z < L` (`differentiableOn_kernelNumerator`), so the only `z`-poles are the `d_j`.
* `circleIntegral_verticalIntegral_eq_loop`: for every `L' ≥ L` and every loop calculus on
  `ball 0 L'` with poles the `d_j`, `∮_{C(0,R)} V_L = I(V_{L'})`.
* `kernel_eq_graftedLoop`: **the kernel as a curve integral over the grafted level loop**
  `γ = nativeGraftedLevelLoop`: `kernel S d R L u v = pref · ∫_γ V_{L'}(z) dz` whenever
  `L' ≥ L` and `γ ⊆ ball 0 L'` (such `L'` always exist, `exists_range_subset_ball`).
* `kernel_contour_independent`: the kernel does not depend on the admissible pair `(R, L)`
  (proved by Cauchy directly, not from equality of determinant densities).

`Johansson.SourceContract` is not needed. All statements are exact identities.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology
open BlockBand.External
open scoped NNReal

/-- The holomorphic numerator of `V_L`: `exp((2uz - z²)/(2S)) · cauchyLine(lineAmplitude)(L, z)`. -/
def kernelNumerator {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u v L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((-z ^ 2 + 2 * (u : ℂ) * z) / (2 * (S : ℂ))) * cauchyLine (lineAmplitude S d v) L z

/-- The source points as a list of complex poles. -/
def sourcePoleList {N : ℕ} (d : Fin N → ℝ) : List ℂ := List.ofFn (fun j => (d j : ℂ))

theorem poleProd_sourcePoleList {N : ℕ} (d : Fin N → ℝ) (z : ℂ) :
    poleProd (sourcePoleList d) z = ∏ j, (z - (d j : ℂ)) := by
  unfold poleProd sourcePoleList
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

theorem mem_sourcePoles_of_mem_list {N : ℕ} (d : Fin N → ℝ) :
    ∀ p ∈ sourcePoleList d, p ∈ sourcePoles d := by
  intro p hp
  unfold sourcePoleList at hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨j, rfl⟩

theorem verticalIntegral_eq_numerator {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u v L : ℝ) (z : ℂ) :
    Johansson.verticalIntegral S d u v L z =
      kernelNumerator S d u v L z * (poleProd (sourcePoleList d) z)⁻¹ := by
  rw [verticalIntegral_eq_factor, poleProd_sourcePoleList]
  unfold kernelNumerator sourceFactor
  rw [div_eq_mul_inv]
  ring

theorem differentiableOn_kernelNumerator {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (u v L : ℝ) : DifferentiableOn ℂ (kernelNumerator S d u v L) {z : ℂ | z.re < L} := by
  have hSr : (0 : ℝ) < S := hS
  unfold kernelNumerator
  apply DifferentiableOn.mul
  · exact (Differentiable.differentiableOn (by fun_prop))
  · exact differentiableOn_cauchyLine (c := 1 / (4 * S)) (by positivity)
      (differentiable_lineAmplitude S d v) (lineAmplitude_verticalGaussian S hS d v) L

theorem ball_subset_re_lt (L : ℝ) : Metric.ball (0 : ℂ) L ⊆ {z : ℂ | z.re < L} := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact lt_of_le_of_lt ((le_abs_self _).trans (Complex.abs_re_le_norm z)) hz

/-- **Circle → loop.** For `L' ≥ L` and every loop calculus `I` on `ball 0 L'` whose poles are
the source points, the circle integral of `V_L` equals `I (V_{L'})`. -/
theorem circleIntegral_verticalIntegral_eq_loop {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (R L : ℝ) (hC : Johansson.AdmissibleContours d R L) (u v L' : ℝ) (hLL' : L ≤ L')
    {I : (ℂ → ℂ) → ℂ} {K : Set ℂ} (hI : LoopCalculus I K (Metric.ball 0 L') (sourcePoles d)) :
    (∮ z in C(0, R), Johansson.verticalIntegral S d u v L z) =
      I (Johansson.verticalIntegral S d u v L') := by
  obtain ⟨hR, hdR, hRL⟩ := hC
  have h1 : (∮ z in C(0, R), Johansson.verticalIntegral S d u v L z) =
      ∮ z in C(0, R), Johansson.verticalIntegral S d u v L' z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    apply verticalIntegral_shift S hS d u v L L' z
    rw [Metric.mem_sphere, dist_zero_right] at hz
    have := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
    rw [min_eq_left hLL']
    linarith
  have hfun : Johansson.verticalIntegral S d u v L' =
      fun z => kernelNumerator S d u v L' z * (poleProd (sourcePoleList d) z)⁻¹ :=
    funext (verticalIntegral_eq_numerator S d u v L')
  have hcirc : LoopCalculus (fun f => ∮ z in C(0, R), f z) (Metric.sphere 0 R)
      (Metric.ball 0 L') (sourcePoles d) := by
    apply circleLoopCalculus hR Metric.isOpen_ball
    · intro z hz
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    · rintro p ⟨j, rfl⟩
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact hdR j
  have hH : DifferentiableOn ℂ (kernelNumerator S d u v L') (Metric.ball 0 L') :=
    (differentiableOn_kernelNumerator S hS d u v L').mono (ball_subset_re_lt L')
  rw [h1, hfun]
  exact hcirc.eq_of_same hI (sourcePoleList d) _ (mem_sourcePoles_of_mem_list d) hH

/-- **The kernel as a contour integral over the grafted level loop**, which encircles all
the `d_j`. For `S > 0`, any real source `d` with `N > 0`, admissible `(R, L)`, the loop
`γ = nativeGraftedLevelLoop hN d t tmax eta x₀ ht` (any `0 < t ≤ tmax`,
`0 < eta ≤ levelHeight d t x₀`), and any `L' ≥ L` with `γ ⊆ ball 0 L'`:
`kernel S d R L u v = exp((v²-u²)/(2S)) / ((2πi)² S) · ∫_γ V_{L'}(z) dz`. -/
theorem kernel_eq_graftedLoop {N : ℕ} (hN : 0 < N) (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (R L : ℝ) (hC : Johansson.AdmissibleContours d R L) (u v : ℝ)
    (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀) (L' : ℝ) (hLL' : L ≤ L')
    (hball : range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) ⊆ Metric.ball 0 L') :
    Johansson.kernel S d R L u v =
      Complex.exp (((v : ℂ) ^ 2 - (u : ℂ) ^ 2) / (2 * (S : ℂ))) /
        (((2 * (Real.pi : ℂ) * Complex.I) ^ 2) * (S : ℂ)) *
        curveIntegral (scalarForm (Johansson.verticalIntegral S d u v L'))
          (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) := by
  have hγ := graftedLoopCalculus hN d t tmax eta x₀ ht htmax heta hheight hball
    (fun j => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith [hC.2.1 j, hC.2.2])
  unfold Johansson.kernel
  rw [circleIntegral_verticalIntegral_eq_loop S hS d R L hC u v L' hLL' hγ]

/-- **Contour independence of the kernel**: for two admissible pairs `(R, L)` and
`(R', L')`, `kernel S d R L = kernel S d R' L'` (Cauchy, directly on the kernel). -/
theorem kernel_contour_independent {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (R L R' L' : ℝ) (hC : Johansson.AdmissibleContours d R L)
    (hC' : Johansson.AdmissibleContours d R' L') (u v : ℝ) :
    Johansson.kernel S d R L u v = Johansson.kernel S d R' L' u v := by
  set L'' : ℝ := max L L' with hL''
  have hcirc : LoopCalculus (fun f => ∮ z in C(0, R'), f z) (Metric.sphere 0 R')
      (Metric.ball 0 L'') (sourcePoles d) := by
    apply circleLoopCalculus hC'.1 Metric.isOpen_ball
    · intro z hz
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      have := hC'.2.2
      have := le_max_right L L'
      linarith
    · rintro p ⟨j, rfl⟩
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact hC'.2.1 j
  have h1 := circleIntegral_verticalIntegral_eq_loop S hS d R L hC u v L'' (le_max_left _ _) hcirc
  have h2 := circleIntegral_verticalIntegral_eq_loop S hS d R' L' hC' u v L''
    (le_max_right _ _) hcirc
  unfold Johansson.kernel
  rw [h1, h2]

end BlockBand.GaussianBulk
