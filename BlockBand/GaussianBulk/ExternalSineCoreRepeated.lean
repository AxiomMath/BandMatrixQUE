module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineCoreKernel
public import BlockBand.GaussianBulk.ExternalSineCoreUnitary

/-!
# The determinantal formula for repeated sources, by continuity

The determinantal formula with Johansson's double contour kernel extends from strictly
increasing to repeated sources `d_j` by continuity of the Gaussian law and of the kernel.
Law: the Johansson
factorial correlation measure `Johansson.factorialCorrelationMeasure S d k` of
`diag(d) + G` (Johansson coordinate law, total entry variance `S`). Domain: `N > 0`, `S > 0`,
`k ≤ N`, monotone (not necessarily strictly) real `d`, admissible contours
`0 < R`, `|d_j| < R`, `R < L`.

Input: `Johansson.SourceContract` (only at strictly increasing perturbations
`d_j + j/(n+1)`), plus the joint continuity of the kernel (`continuous_kernel`).
Argument:
* `tendsto_integral_factorialCorrelation`: weak continuity of `d ↦ factorialCorrelationMeasure`
  against bounded continuous test functions (dominated convergence on the coordinate law;
  eigenvalues are continuous in the matrix);
* the densities `Re det K_{d_n}` converge to `Re det K_d` locally uniformly in the sense
  needed for dominated convergence on compact supports (joint continuity of the kernel in
  `(d, u, v)`, compactness of `{d_n} ∪ {d}`);
* uniqueness of regular measures from `C_c` integrals (Riesz–Markov–Kakutani uniqueness).

Results: `factorialCorrelationMeasure_eq_kernel_of_monotone`, its form
`deformedFactorialCorrelation_eq_kernel` for every Hermitian `F`, and the packaged statement
`externalSine_step1` (continuous kernel and determinantal identity for every `k ≤ N`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Filter Topology Set
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal CompactlySupported

/-- Sources strictly inside the circle `|z| = R`. -/
def sourceDomain (N : ℕ) (R : ℝ) : Set (Fin N → ℝ) := {d | ∀ j, |d j| < R}

/-- The admissible source domain `{∀ j, |d_j| < R}` is open. -/
theorem isOpen_sourceDomain (N : ℕ) (R : ℝ) : IsOpen (sourceDomain N R) := by
  have : sourceDomain N R = ⋂ j, {d : Fin N → ℝ | |d j| < R} := by
    ext d; simp [sourceDomain]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_abs.comp (continuous_apply j)) continuous_const

/-- The real part of the (2.18) determinant as a function of `(d, x)`. -/
def kernelDetRe {N : ℕ} (S : ℝ≥0) (R L : ℝ) (k : ℕ) (q : (Fin N → ℝ) × (Fin k → ℝ)) : ℝ :=
  (Johansson.kernelDeterminant S q.1 R L q.2).re

/-- Joint continuity of `(d, x) ↦ Re det[K_d(x_i,x_j)]` on admissible sources (`S > 0`, `0 < R < L`). -/
theorem continuousOn_kernelDetRe {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (R L : ℝ) (hR : 0 < R)
    (hRL : R < L) (k : ℕ) :
    ContinuousOn (kernelDetRe (N := N) S R L k) (sourceDomain N R ×ˢ univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hK := continuousOn_kernel (N := N) S hS R L hR hRL
  have hentry : ∀ i j : Fin k, Continuous (fun y : (sourceDomain N R ×ˢ (univ : Set (Fin k → ℝ))) =>
      Johansson.kernel S y.1.1 R L (y.1.2 i) (y.1.2 j)) := by
    intro i j
    have hmap : Continuous (fun y : (sourceDomain N R ×ˢ (univ : Set (Fin k → ℝ))) =>
        ((y.1.1, y.1.2 i, y.1.2 j) : (Fin N → ℝ) × ℝ × ℝ)) := by fun_prop
    have h2 := hK.comp_continuous hmap (fun y => y.2.1)
    simp only [Function.comp_def] at h2
    exact h2
  have hdet : Continuous (fun y : (sourceDomain N R ×ˢ (univ : Set (Fin k → ℝ))) =>
      Matrix.det (Matrix.of fun i j => Johansson.kernel S y.1.1 R L (y.1.2 i) (y.1.2 j))) :=
    (continuous_matrix fun i j => hentry i j).matrix_det
  exact (Complex.continuous_re.comp hdet).congr (fun y => rfl)

/-- Ordered spectral tuples are continuous on Hermitian matrices. -/
theorem continuous_spectralTuple {N k : ℕ} (e : Fin k ↪ Fin N) :
    Continuous (Johansson.spectralTuple e) :=
  continuous_pi fun _ => Model.Construction.continuous_orderedEigenvalue _

/-- For a fixed Gaussian sample, `diag(d) + G` is continuous in the source `d`. -/
theorem continuous_deformedMatrix_source {N : ℕ} (z : Johansson.UpperPair N → ℝ × ℝ) :
    Continuous (fun d : Fin N → ℝ => Johansson.deformedMatrix d z) := by
  unfold Johansson.deformedMatrix
  exact Continuous.subtype_mk ((Continuous.matrix_diagonal (continuous_pi fun i =>
    Complex.continuous_ofReal.comp (continuous_apply i))).add continuous_const) _

/-- Weak continuity of the Johansson factorial correlation measure in the source, against
bounded continuous test functions. -/
theorem tendsto_integral_factorialCorrelation {N : ℕ} (S : ℝ≥0) (k : ℕ)
    {e : ℕ → Fin N → ℝ} {d : Fin N → ℝ} (he : Tendsto e atTop (𝓝 d))
    (f : (Fin k → ℝ) → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂Johansson.factorialCorrelationMeasure S (e n) k) atTop
      (𝓝 (∫ x, f x ∂Johansson.factorialCorrelationMeasure S d k)) := by
  have hcoord := Johansson.coordinateMeasure_probability N S
  have key : ∀ d' : Fin N → ℝ, ∫ x, f x ∂Johansson.factorialCorrelationMeasure S d' k =
      ∑ σ : Fin k ↪ Fin N, ∫ z, f (Johansson.spectralTuple σ (Johansson.deformedMatrix d' z))
        ∂Johansson.coordinateMeasure N S := by
    intro d'
    have := Johansson.matrixMeasure_probability S d'
    unfold Johansson.factorialCorrelationMeasure
    rw [integral_finsetSum_measure (fun σ _ => Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC))]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [integral_map (Johansson.measurable_spectralTuple σ).aemeasurable hf.aestronglyMeasurable,
      Johansson.matrixMeasure, integral_map (Johansson.measurable_deformedMatrix d').aemeasurable
        (show Continuous (fun x => f (Johansson.spectralTuple σ x)) from
          hf.comp (continuous_spectralTuple σ)).aestronglyMeasurable]
  simp_rw [key]
  apply tendsto_finsetSum
  intro σ _
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro n
    exact ((hf.comp (continuous_spectralTuple σ)).measurable.comp
      (Johansson.measurable_deformedMatrix (e n))).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    exact Filter.Eventually.of_forall fun z => hC _
  · refine Filter.Eventually.of_forall fun z => ?_
    exact ((hf.comp (continuous_spectralTuple σ)).comp
      (continuous_deformedMatrix_source z)).continuousAt.tendsto.comp he

/-- For a monotone (possibly repeated) source `d`, admissible contours and `k ≤ N`,
the Johansson factorial correlation measure has density `Re det[K_N(x_i,x_j)]` with the
kernel `K_N = Johansson.kernel S d R L`. Uses
`Johansson.SourceContract` only at strictly increasing perturbations of `d`. -/
theorem factorialCorrelationMeasure_eq_kernel_of_monotone (hJ : Johansson.SourceContract)
    {N : ℕ} (hN : 0 < N) (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ) (hd : Monotone d)
    (R L : ℝ) (hC : Johansson.AdmissibleContours d R L) (k : ℕ) (hk : k ≤ N) :
    Johansson.factorialCorrelationMeasure S d k =
      (volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Johansson.kernelDeterminant S d R L x).re) := by
  obtain ⟨hR, hdR, hRL⟩ := hC
  -- strictly increasing perturbations
  let dn : ℕ → Fin N → ℝ := fun n j => d j + (j : ℝ) * (1 / ((n : ℝ) + 1))
  have hdn_tend : Tendsto dn atTop (𝓝 d) := by
    rw [tendsto_pi_nhds]
    intro j
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (j : ℝ)
    simpa [dn] using (tendsto_const_nhds (x := d j)).add h
  have hdn_mono : ∀ n, StrictMono (dn n) := by
    intro n i j hij
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    have := hd hij.le
    simp only [dn]
    nlinarith
  have hdom : d ∈ sourceDomain N R := hdR
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (hdn_tend.eventually ((isOpen_sourceDomain N R).mem_nhds hdom))
  let e : ℕ → Fin N → ℝ := fun n => dn (n + n0)
  have he_tend : Tendsto e atTop (𝓝 d) := hdn_tend.comp (tendsto_add_atTop_nat n0)
  have he_dom : ∀ n, e n ∈ sourceDomain N R := fun n => hn0 _ (Nat.le_add_left _ _)
  have hcorr : ∀ n, Johansson.factorialCorrelationMeasure S (e n) k =
      (volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal (kernelDetRe S R L k (e n, x))) := fun n =>
    hJ.correlations hN S hS (e n) (hdn_mono _) R L ⟨hR, he_dom n, hRL⟩ k hk
  -- continuity of the densities
  have hΦ := continuousOn_kernelDetRe (N := N) S hS R L hR hRL k
  have hΦx : ∀ d' ∈ sourceDomain N R, Continuous (fun x : Fin k → ℝ => kernelDetRe S R L k (d', x)) :=
    fun d' hd' => hΦ.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hd', trivial⟩)
  -- regularity of both sides
  have hfin : IsFiniteMeasure (Johansson.factorialCorrelationMeasure S d k) :=
    ⟨by rw [Johansson.factorialCorrelationMeasure_univ]; exact ENNReal.natCast_lt_top _⟩
  have hloc : IsLocallyFiniteMeasure ((volume : Measure (Fin k → ℝ)).withDensity
      (fun x => ENNReal.ofReal (kernelDetRe S R L k (d, x)))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (hΦx d hdom)
  change Johansson.factorialCorrelationMeasure S d k =
    (volume : Measure (Fin k → ℝ)).withDensity
      (fun x => ENNReal.ofReal (kernelDetRe S R L k (d, x)))
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have h1 := tendsto_integral_factorialCorrelation S k he_tend f f.continuous Cf hCf
  -- integrals against the densities
  have hrw : ∀ d' ∈ sourceDomain N R,
      ∫ x, f x ∂((volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal (kernelDetRe S R L k (d', x)))) =
      ∫ x, ((kernelDetRe S R L k (d', x)).toNNReal : ℝ) * f x := by
    intro d' hd'
    have hmeas : Measurable (fun x => (kernelDetRe S R L k (d', x)).toNNReal) :=
      (continuous_real_toNNReal.comp (hΦx d' hd')).measurable
    have := integral_withDensity_eq_integral_smul (μ := volume) hmeas (fun x => f x)
    simp only [NNReal.smul_def, smul_eq_mul] at this
    exact this
  -- dominated convergence for the density side
  have hK : IsCompact (insert d (range e) ×ˢ tsupport f) :=
    he_tend.isCompact_insert_range.prod f.hasCompactSupport.isCompact
  have hKsub : insert d (range e) ×ˢ tsupport f ⊆ sourceDomain N R ×ˢ univ := by
    rintro ⟨d', x⟩ ⟨hd', -⟩
    refine ⟨?_, trivial⟩
    rcases hd' with rfl | ⟨n, rfl⟩
    · exact hdom
    · exact he_dom n
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hΦ.mono hKsub)
  have h2 : Tendsto (fun n => ∫ x, ((kernelDetRe S R L k (e n, x)).toNNReal : ℝ) * f x)
      atTop (𝓝 (∫ x, ((kernelDetRe S R L k (d, x)).toNNReal : ℝ) * f x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => M * ‖f x‖)
    · intro n
      exact ((NNReal.continuous_coe.comp (continuous_real_toNNReal.comp
        (hΦx _ (he_dom n)))).mul f.continuous).aestronglyMeasurable
    · exact (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm.const_mul M
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul]
      by_cases hx : x ∈ tsupport f
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hb := hM (e n, x) ⟨Set.mem_insert_of_mem _ ⟨n, rfl⟩, hx⟩
        refine le_trans ?_ hb
        rw [Real.norm_eq_abs, Real.norm_eq_abs, NNReal.abs_eq, Real.coe_toNNReal']
        exact max_le (le_abs_self _) (abs_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, mul_zero]
    · refine Filter.Eventually.of_forall fun x => ?_
      have hcw : ContinuousWithinAt (kernelDetRe (N := N) S R L k) (sourceDomain N R ×ˢ univ)
          (d, x) := hΦ (d, x) ⟨hdom, trivial⟩
      have ht : Tendsto (fun n => (e n, x)) atTop (𝓝[sourceDomain N R ×ˢ univ] (d, x)) :=
        tendsto_nhdsWithin_iff.mpr ⟨he_tend.prodMk_nhds tendsto_const_nhds,
          Filter.Eventually.of_forall fun n => ⟨he_dom n, trivial⟩⟩
      have := (hcw.tendsto.comp ht)
      exact ((NNReal.continuous_coe.comp continuous_real_toNNReal).continuousAt.tendsto.comp
        this).mul tendsto_const_nhds
  have heq : ∀ n, ∫ x, f x ∂Johansson.factorialCorrelationMeasure S (e n) k =
      ∫ x, ((kernelDetRe S R L k (e n, x)).toNNReal : ℝ) * f x := by
    intro n
    rw [hcorr n, hrw _ (he_dom n)]
  rw [hrw d hdom]
  exact tendsto_nhds_unique (h1.congr heq) h2

/-- The determinantal formula for every Hermitian source (repeated eigenvalues allowed): for `N > 0`, `t > 0`,
admissible contours `R, L` for `d = spectralSource F` and `k ≤ N`, the factorial correlation
measure of `F + √t G_N` has density `Re det[K_N(x_i,x_j)]`, `K_N = Johansson.kernel (t/N) d R L`.
Input: `Johansson.SourceContract`. -/
theorem deformedFactorialCorrelation_eq_kernel (hJ : Johansson.SourceContract)
    {N : ℕ} (hN : 0 < N) (t : ℝ≥0) (ht : 0 < t) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) (R L : ℝ)
    (hC : Johansson.AdmissibleContours (spectralSource F hF) R L) (k : ℕ) (hk : k ≤ N) :
    deformedFactorialCorrelation N t F hF k =
      (volume : Measure (Fin k → ℝ)).withDensity (fun x => ENNReal.ofReal
        (Matrix.det (fun i j => Johansson.kernel (Johansson.sourceTime N t)
          (spectralSource F hF) R L (x i) (x j))).re) := by
  have hS : 0 < Johansson.sourceTime N t := by
    rw [Johansson.sourceTime]
    exact div_pos ht (by exact_mod_cast hN)
  rw [deformedFactorialCorrelation_eq_johansson]
  exact factorialCorrelationMeasure_eq_kernel_of_monotone hJ hN _ hS _
    (spectralSource_monotone F hF) R L hC k hk

/-- The determinantal formula packaged for `ExternalSineKernelCore`: for `N > 0`, `t > 0` and every Hermitian
`F`, with `d = spectralSource F`, `R = ∑_j |d_j| + 1`, `L = R + 1` and `S = t/N`, the contours are
admissible, `Kern = Johansson.kernel S d R L` is jointly continuous, and every factorial
correlation of order `k ≤ N` of `F + √t G_N` has density `Re det[Kern(x_i,x_j)]`.
Input: `Johansson.SourceContract`. -/
theorem externalSine_step1 (hJ : Johansson.SourceContract) {N : ℕ} (hN : 0 < N) (t : ℝ≥0)
    (ht : 0 < t) (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) :
    Johansson.AdmissibleContours (spectralSource F hF)
        (∑ j, |spectralSource F hF j| + 1) (∑ j, |spectralSource F hF j| + 1 + 1) ∧
      Continuous (Function.uncurry (Johansson.kernel (Johansson.sourceTime N t)
        (spectralSource F hF) (∑ j, |spectralSource F hF j| + 1)
        (∑ j, |spectralSource F hF j| + 1 + 1))) ∧
      ∀ k : ℕ, k ≤ N → deformedFactorialCorrelation N t F hF k =
        (volume : Measure (Fin k → ℝ)).withDensity (fun x => ENNReal.ofReal
          (Matrix.det (fun i j => Johansson.kernel (Johansson.sourceTime N t)
            (spectralSource F hF) (∑ j, |spectralSource F hF j| + 1)
            (∑ j, |spectralSource F hF j| + 1 + 1) (x i) (x j))).re) := by
  have hS : 0 < Johansson.sourceTime N t := by
    rw [Johansson.sourceTime]
    exact div_pos ht (by exact_mod_cast hN)
  have hsum0 : 0 ≤ ∑ j, |spectralSource F hF j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hC : Johansson.AdmissibleContours (spectralSource F hF)
      (∑ j, |spectralSource F hF j| + 1) (∑ j, |spectralSource F hF j| + 1 + 1) := by
    refine ⟨by linarith, fun j => ?_, by linarith⟩
    have := Finset.single_le_sum (f := fun j => |spectralSource F hF j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  exact ⟨hC, continuous_kernel _ hS _ _ _ hC,
    fun k hk => deformedFactorialCorrelation_eq_kernel hJ hN t ht F hF _ _ hC k hk⟩

end BlockBand.GaussianBulk
