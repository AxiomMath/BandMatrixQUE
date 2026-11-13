module

public import Mathlib
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import BlockBand.Model.Construction.OrderedSpectrum

/-!
# Johansson's correlation kernel for GUE with an external source

This file states, as the hypothesis `SourceContract`, Johansson's double contour formula (2.18)
(arXiv math-ph/0006020) for the correlation kernel of `D + H`, where `D = diag(d)` has distinct
increasing real entries and `H` is a complex Gaussian Hermitian matrix with diagonal variance `S`
and real and imaginary parts of the off-diagonal entries of variance `S/2`. The time `S = t/N`
is the normalized GUE time. No restriction is placed on the real variables `u, v`.

The kernel uses a counterclockwise circle about `0` enclosing all `d_j` and the upward vertical
line `L + iℝ` to its right. `SourceContract` asserts that the contour integrals are well defined
and that the factorial correlation measures of the law of `D + H` (sums over ordered `k`-tuples
of distinct eigenvalue ranks, of total mass `N!/(N-k)!`) have density `det(K(x_i, x_j))`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.External.Johansson

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

abbrev HermitianMatrix (N : ℕ) :=
  BlockBand.Model.Construction.HermitianMatrix (Fin N)

/-- The index pairs `i ≤ j` of the upper triangle, including the diagonal. -/
abbrev UpperPair (N : ℕ) := {q : Fin N × Fin N // q.1 ≤ q.2}

/-- The law of one upper entry, as a pair of reals: `N(0, S)` on the diagonal (imaginary part
`0`), and `N(0, S/2) ⊗ N(0, S/2)` off the diagonal. -/
def upperEntryMeasure {N : ℕ} (S : ℝ≥0) (q : UpperPair N) : Measure (ℝ × ℝ) :=
  if q.1.1 = q.1.2 then
    Measure.map (fun x : ℝ => (x,0)) (gaussianReal 0 S)
  else (gaussianReal 0 (S/2)).prod (gaussianReal 0 (S/2))

/-- The product law of the independent upper entries. -/
def coordinateMeasure (N : ℕ) (S : ℝ≥0) : Measure (UpperPair N → ℝ × ℝ) :=
  Measure.pi (upperEntryMeasure S)

/-- The complex number `x + iy` from the pair `(x, y)`. -/
def complexPair (z : ℝ × ℝ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- The Hermitian matrix with the given upper entries; the imaginary parts of the diagonal
coordinates are ignored. -/
def gaussianMatrixRaw {N : ℕ} (z : UpperPair N → ℝ × ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    if hij : i = j then (z ⟨(i,j), by simp [hij]⟩).1
    else if hle : i ≤ j then complexPair (z ⟨(i,j),hle⟩)
    else star (complexPair (z ⟨(j,i), le_of_not_ge hle⟩))

/-- `gaussianMatrixRaw z` is Hermitian. -/
theorem gaussianMatrixRaw_isHermitian {N : ℕ} (z : UpperPair N → ℝ × ℝ) :
    (gaussianMatrixRaw z).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.conjTranspose_apply, gaussianMatrixRaw]
  · by_cases hle : i ≤ j
    · have hnot : ¬ j ≤ i := fun hji => hij (le_antisymm hle hji)
      simp [Matrix.conjTranspose_apply, gaussianMatrixRaw, hij, Ne.symm hij, hle, hnot]
    · have hji : j ≤ i := le_of_not_ge hle
      simp [Matrix.conjTranspose_apply, gaussianMatrixRaw, hij, Ne.symm hij, hle, hji]

/-- `gaussianMatrixRaw z` as a Hermitian matrix. -/
def gaussianMatrix {N : ℕ} (z : UpperPair N → ℝ × ℝ) : HermitianMatrix N :=
  ⟨gaussianMatrixRaw z, gaussianMatrixRaw_isHermitian z⟩

/-- `gaussianMatrix` is measurable. -/
theorem measurable_gaussianMatrix {N : ℕ} : Measurable (@gaussianMatrix N) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro i j
  unfold gaussianMatrixRaw
  split_ifs
  · fun_prop
  · unfold complexPair
    fun_prop
  · unfold complexPair
    fun_prop

/-- The matrix `diag(d) + H` with the external source `d`. -/
def deformedMatrix {N : ℕ} (d : Fin N → ℝ)
    (z : UpperPair N → ℝ × ℝ) : HermitianMatrix N :=
  ⟨Matrix.diagonal (fun i => (d i : ℂ)) + (gaussianMatrix z).1,
    (Matrix.isHermitian_diagonal_iff.mpr (by intro i; simp [IsSelfAdjoint])).add
      (gaussianMatrix z).2⟩

/-- `deformedMatrix d` is measurable. -/
theorem measurable_deformedMatrix {N : ℕ} (d : Fin N → ℝ) :
    Measurable (deformedMatrix d) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro i j
  have h := measurable_subtype_coe.comp (measurable_gaussianMatrix (N := N))
  exact measurable_const.add ((Matrix.measurable_iff.mp h) i j)

/-- The law of `diag(d) + H`. -/
def matrixMeasure {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) : Measure (HermitianMatrix N) :=
  Measure.map (deformedMatrix d) (coordinateMeasure N S)

/-- Each upper-entry law is a probability measure. -/
theorem upperEntryMeasure_probability {N : ℕ} (S : ℝ≥0) (q : UpperPair N) :
    IsProbabilityMeasure (upperEntryMeasure S q) := by
  unfold upperEntryMeasure
  split_ifs
  · constructor
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]
    exact (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 S).measure_univ
  · infer_instance

/-- The product law of the upper entries is a probability measure (also for `N = 0`). -/
theorem coordinateMeasure_probability (N : ℕ) (S : ℝ≥0) :
    IsProbabilityMeasure (coordinateMeasure N S) := by
  have : ∀ q : UpperPair N, IsProbabilityMeasure (upperEntryMeasure S q) :=
    upperEntryMeasure_probability S
  unfold coordinateMeasure
  infer_instance

/-- The law of `diag(d) + H` is a probability measure. -/
theorem matrixMeasure_probability {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) :
    IsProbabilityMeasure (matrixMeasure S d) := by
  have := coordinateMeasure_probability N S
  constructor
  rw [matrixMeasure, Measure.map_apply (measurable_deformedMatrix d) MeasurableSet.univ]
  simp

/-- The normalized time `S = t/N`. -/
def sourceTime (N : ℕ) (t : ℝ≥0) : ℝ≥0 := t / N

/-- `sourceTime N t = t/N` as a real number. -/
theorem sourceTime_coe (N : ℕ) (t : ℝ≥0) :
    (sourceTime N t : ℝ) = (t : ℝ) / (N : ℝ) := by
  simp [sourceTime]

/-- The eigenvalues of `A` (in increasing order) at the ranks `e(0), …, e(k-1)`. -/
def spectralTuple {N k : ℕ} (e : Fin k ↪ Fin N) (A : HermitianMatrix N) : Fin k → ℝ :=
  fun i => BlockBand.Model.Construction.orderedEigenvalue A
    (Fin.cast (Fintype.card_fin N).symm (e i))

/-- `spectralTuple e` is measurable. -/
theorem measurable_spectralTuple {N k : ℕ} (e : Fin k ↪ Fin N) :
    Measurable (spectralTuple e) := by
  exact measurable_pi_iff.mpr fun i =>
    BlockBand.Model.Construction.measurable_orderedEigenvalue _

/-- The `k`-th factorial correlation measure of the law of `diag(d) + H`: the sum over injective
`k`-tuples of ranks of the law of the corresponding eigenvalues, without division by `k!`. -/
def factorialCorrelationMeasure {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (k : ℕ) :
    Measure (Fin k → ℝ) :=
  ∑ e : Fin k ↪ Fin N, Measure.map (spectralTuple e) (matrixMeasure S d)

/-- The `k`-th factorial correlation measure has total mass `N(N-1)⋯(N-k+1)`; for `k = N` this is
`N!`, so the symmetric joint density is `det(K)/N!`. -/
theorem factorialCorrelationMeasure_univ {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (k : ℕ) :
    factorialCorrelationMeasure S d k Set.univ = (N.descFactorial k : ℝ≥0∞) := by
  have := matrixMeasure_probability S d
  have he : ∀ e : Fin k ↪ Fin N,
      Measure.map (spectralTuple e) (matrixMeasure S d) Set.univ = 1 := by
    intro e
    rw [Measure.map_apply (measurable_spectralTuple e) MeasurableSet.univ]
    simp
  unfold factorialCorrelationMeasure
  rw [Measure.finsetSum_apply]
  simp [he, Fintype.card_embedding_eq]

/-- Admissible contours: a circle of radius `R` about `0` enclosing all `d_j`, traversed
counterclockwise, and the vertical line `Re w = L > R`, traversed upward. -/
def AdmissibleContours {N : ℕ} (d : Fin N → ℝ) (R L : ℝ) : Prop :=
  0 < R ∧ (∀ j, |d j| < R) ∧ R < L

/-- The integrand of the double contour integral (2.18):
`exp((w² - 2vw - z² + 2uz)/(2S)) / (w - z) · ∏_j (w - d_j)/(z - d_j)`. -/
def kernelIntegrand {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u v : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp ((w^2 - 2*(v : ℂ)*w - z^2 + 2*(u : ℂ)*z) / (2*(S : ℂ))) /
    (w-z) * ∏ j, (w-(d j : ℂ)) / (z-(d j : ℂ))

/-- The integral over the upward vertical line `w = L + iy`, with `dw = i dy`. -/
def verticalIntegral {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ)
    (u v L : ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, Complex.I * kernelIntegrand S d u v z ((L : ℂ) + (y : ℂ)*Complex.I)

/-- The kernel (2.18): `exp((v² - u²)/(2S)) / ((2πi)² S)` times the double contour integral over
the circle and the vertical line. Integrability on admissible contours is part of
`SourceContract`. -/
def kernel {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (R L u v : ℝ) : ℂ :=
  Complex.exp (((v : ℂ)^2 - (u : ℂ)^2) / (2*(S : ℂ))) /
    (((2*(Real.pi : ℂ)*Complex.I)^2) * (S : ℂ)) *
      circleIntegral (verticalIntegral S d u v L) 0 R

/-- The determinant `det(K(x_i, x_j))_{i,j<k}`. -/
def kernelDeterminant {N k : ℕ} (S : ℝ≥0) (d : Fin N → ℝ)
    (R L : ℝ) (x : Fin k → ℝ) : ℂ :=
  Matrix.det (fun i j => kernel S d R L (x i) (x j))

/-- Johansson's formula, as a hypothesis: for `N > 0`, `S > 0`, strictly increasing `d` and
admissible contours, the contour integrals exist, the determinants are real and nonnegative, and
for `k ≤ N` the `k`-th factorial correlation measure has density `det(K(x_i, x_j))`. -/
structure SourceContract : Prop where
  vertical_integrable : ∀ {N : ℕ}, 0 < N → ∀ (S : ℝ≥0), 0 < S →
    ∀ (d : Fin N → ℝ), StrictMono d → ∀ (R L : ℝ), AdmissibleContours d R L →
      ∀ (u v : ℝ) (z : ℂ), ‖z‖ = R →
        Integrable (fun y : ℝ => Complex.I *
          kernelIntegrand S d u v z ((L : ℂ)+(y : ℂ)*Complex.I))
  circle_integrable : ∀ {N : ℕ}, 0 < N → ∀ (S : ℝ≥0), 0 < S →
    ∀ (d : Fin N → ℝ), StrictMono d → ∀ (R L : ℝ), AdmissibleContours d R L →
      ∀ (u v : ℝ), CircleIntegrable (verticalIntegral S d u v L) 0 R
  determinant_real_nonnegative : ∀ {N : ℕ}, 0 < N → ∀ (S : ℝ≥0), 0 < S →
    ∀ (d : Fin N → ℝ), StrictMono d → ∀ (R L : ℝ), AdmissibleContours d R L →
      ∀ {k : ℕ}, k ≤ N → ∀ (x : Fin k → ℝ),
        (kernelDeterminant S d R L x).im = 0 ∧
          0 ≤ (kernelDeterminant S d R L x).re
  correlations : ∀ {N : ℕ}, 0 < N → ∀ (S : ℝ≥0), 0 < S →
    ∀ (d : Fin N → ℝ), StrictMono d → ∀ (R L : ℝ), AdmissibleContours d R L →
      ∀ (k : ℕ), k ≤ N →
        factorialCorrelationMeasure S d k =
          (volume : Measure (Fin k → ℝ)).withDensity
            (fun x => ENNReal.ofReal (kernelDeterminant S d R L x).re)

/-- The factorial correlation measures have density `det(K(x_i, x_j))`, given `SourceContract`. -/
theorem factorialCorrelations_of_source (source : SourceContract)
    {N : ℕ} (hN : 0 < N) (S : ℝ≥0) (hS : 0 < S)
    (d : Fin N → ℝ) (hd : StrictMono d) (R L : ℝ)
    (hC : AdmissibleContours d R L) (k : ℕ) (hk : k ≤ N) :
    factorialCorrelationMeasure S d k =
      (volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal (kernelDeterminant S d R L x).re) :=
  source.correlations hN S hS d hd R L hC k hk

end BlockBand.External.Johansson
