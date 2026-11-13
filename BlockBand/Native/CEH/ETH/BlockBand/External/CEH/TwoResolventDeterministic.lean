module

public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.ResolventIdentities
public import BlockBand.Native.CEH.BlockBand.Conventions
public import Mathlib.Analysis.Real.Sqrt

/-!
# Generic denominator algebra for the CEH two-resolvent approximation

This file records scalar denominator rearrangements and generic positivity and
Cauchy–Schwarz helpers for the deterministic bounds of Cipolloni–Erdős–Henheik (CEH),
Lemma 5.6. It does **not** prove that lemma: the MDE numerator estimates, matrix
tensorization, source cutoff, and regularized observables are not treated here.

The scalar variables below are the values of the normalized trace functional
on the indicated matrix words. This isolates precisely the deterministic
rank-one stability direction in (5.12), while matrix Ward identities are
provided by `Analysis.ResolventIdentities`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open scoped BigOperators ComplexConjugate

/-- CEH (5.12): scalar stability denominator
`β₁₂ = 1 - λ² ⟨M₁M₂⟩`. -/
def stabilityDenominator (lambda pairTrace : ℂ) : ℂ :=
  1 - lambda ^ 2 * pairTrace

/-- The trace of the CEH deterministic two-resolvent approximation.  Here
`wordTrace = ⟨M₁ A M₂⟩` and `pairTrace = ⟨M₁ M₂⟩`. -/
def twoResolventTraceApprox
    (lambda pairTrace wordTrace : ℂ) : ℂ :=
  wordTrace + lambda ^ 2 * (wordTrace / stabilityDenominator lambda pairTrace) * pairTrace

/-- The apparent two-term approximation is exactly application of the scalar
stability inverse.  This is the algebra behind the trace formula following
CEH (5.12). -/
theorem twoResolventTraceApprox_eq_div
    (lambda pairTrace wordTrace : ℂ)
    (hstable : stabilityDenominator lambda pairTrace ≠ 0) :
    twoResolventTraceApprox lambda pairTrace wordTrace =
      wordTrace / stabilityDenominator lambda pairTrace := by
  apply (eq_div_iff hstable).2
  unfold twoResolventTraceApprox stabilityDenominator at *
  field_simp [hstable]
  ring

/-- Applying `1 + λ²⟨M₁M₂⟩/β₁₂` is the inverse stability factor `1/β₁₂`.
This is the identity used in the characteristic-flow trace equation. -/
theorem one_add_feedback_eq_stabilityInverse
    (lambda pairTrace : ℂ)
    (hstable : stabilityDenominator lambda pairTrace ≠ 0) :
    1 + lambda ^ 2 * pairTrace / stabilityDenominator lambda pairTrace =
      1 / stabilityDenominator lambda pairTrace := by
  calc
    1 + lambda ^ 2 * pairTrace / stabilityDenominator lambda pairTrace =
        twoResolventTraceApprox lambda pairTrace 1 := by
          simp [twoResolventTraceApprox]
          ring
    _ = 1 / stabilityDenominator lambda pairTrace :=
      twoResolventTraceApprox_eq_div lambda pairTrace 1 hstable

/-- Matrix-valued CEH deterministic approximation (5.12), before taking its
normalized trace. -/
def twoResolventApprox {d : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  let word := M₁ * A * M₂
  let pair := M₁ * M₂
  word +
    (lambda ^ 2 *
      (CEHNative.BlockBand.Conventions.normalizedTrace word /
        stabilityDenominator lambda
          (CEHNative.BlockBand.Conventions.normalizedTrace pair))) • pair

/-- Taking normalized trace of the matrix-valued approximation gives the
scalar stability inverse formula, with no probabilistic input. -/
theorem normalizedTrace_twoResolventApprox {d : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin d) (Fin d) ℂ)
    (hstable : stabilityDenominator lambda
      (CEHNative.BlockBand.Conventions.normalizedTrace (M₁ * M₂)) ≠ 0) :
    CEHNative.BlockBand.Conventions.normalizedTrace
        (twoResolventApprox lambda M₁ A M₂) =
      CEHNative.BlockBand.Conventions.normalizedTrace (M₁ * A * M₂) /
        stabilityDenominator lambda
          (CEHNative.BlockBand.Conventions.normalizedTrace (M₁ * M₂)) := by
  rw [twoResolventApprox,
    CEHNative.BlockBand.Conventions.normalizedTrace_add,
    CEHNative.BlockBand.Conventions.normalizedTrace_smul]
  exact twoResolventTraceApprox_eq_div _ _ _ hstable

/-- Regular-observable subtraction in the active (`θ = 1`) regime. -/
def regularizeObservableTrace (observableTrace pairTrace : ℂ) : ℂ :=
  observableTrace - observableTrace / pairTrace * pairTrace

/-- The CEH regular-observable cutoff kills the unstable trace direction
exactly, rather than merely bounding it. -/
theorem regularizeObservableTrace_eq_zero
    (observableTrace pairTrace : ℂ) (hpair : pairTrace ≠ 0) :
    regularizeObservableTrace observableTrace pairTrace = 0 := by
  simp [regularizeObservableTrace, hpair]

/-- Boolean version of the cutoff: outside the active regime the observable is
unchanged, while inside it the unstable component is subtracted. -/
def cutoffRegularizeObservableTrace
    (active : Bool) (observableTrace pairTrace : ℂ) : ℂ :=
  if active then regularizeObservableTrace observableTrace pairTrace else observableTrace

@[simp] theorem cutoffRegularizeObservableTrace_false
    (observableTrace pairTrace : ℂ) :
    cutoffRegularizeObservableTrace false observableTrace pairTrace = observableTrace := by
  simp [cutoffRegularizeObservableTrace]

@[simp] theorem cutoffRegularizeObservableTrace_true
    (observableTrace pairTrace : ℂ) (hpair : pairTrace ≠ 0) :
    cutoffRegularizeObservableTrace true observableTrace pairTrace = 0 := by
  simp [cutoffRegularizeObservableTrace, regularizeObservableTrace_eq_zero _ _ hpair]

/-- Replication used in the CEH tensorization meta-argument: replicate each
scalar spectral contribution `d` times. -/
def replicatedAverage (d : ℕ) {ι : Type*} [Fintype ι]
    (f : ι → ℂ) : ℂ :=
  ((d * Fintype.card ι : ℕ) : ℂ)⁻¹ *
    ∑ p : Fin d × ι, f p.2

/-- Direct finite-dimensional tensorization: normalized traces are invariant
under replication by `I_d`.  This replaces the paper's meta-limit for the
purely deterministic trace identity. -/
theorem replicatedAverage_eq
    (d : ℕ) (hd : 0 < d) {ι : Type*} [Fintype ι]
    (hι : 0 < Fintype.card ι) (f : ι → ℂ) :
    replicatedAverage d f =
      ((Fintype.card ι : ℕ) : ℂ)⁻¹ * ∑ i, f i := by
  classical
  rw [replicatedAverage, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp [ne_of_gt hd, ne_of_gt hι]

/-- Spectral-decomposition positivity: a nonnegative spectral weight times a
squared coefficient contributes a nonnegative quantity. -/
theorem spectralDecomposition_nonneg
    {ι : Type*} [Fintype ι] (weight coefficient : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ ∑ i, weight i * coefficient i ^ 2 := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hweight i) (sq_nonneg _)

/-- Every spectral component is controlled by the full positive trace. -/
theorem spectralTerm_le_trace
    {ι : Type*} [Fintype ι] (weight coefficient : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (i : ι) :
    weight i * coefficient i ^ 2 ≤ ∑ j, weight j * coefficient j ^ 2 := by
  classical
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (hweight j) (sq_nonneg _)) (Finset.mem_univ i)

/-- Finite spectral Cauchy–Schwarz, the deterministic core of the Schwarz
chains in the proof of CEH Lemma 5.6. -/
theorem spectralSchwarzChain
    {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    ∑ i, u i * v i ≤
      Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v

/-- Absolute-value form of the finite spectral Schwarz chain. -/
theorem spectralSchwarzChain_abs
    {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    |∑ i, u i * v i| ≤
      Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  rw [abs_le]
  constructor
  · have h := spectralSchwarzChain (fun i => -u i) v
    have h' := neg_le_neg h
    simpa only [neg_mul, Finset.sum_neg_distrib, neg_sq, neg_neg] using h'
  · exact spectralSchwarzChain u v

/-- Ward reduction after spectral decomposition: if the second squared chain
is bounded by `η⁻²` times the first, its Schwarz product is bounded by the
corresponding Ward scale.  The hypotheses are the pointwise resolvent
inequality; the summed consequence is proved here. -/
theorem wardSchwarzChain
    {ι : Type*} [Fintype ι] (u v : ι → ℝ) (eta : ℝ)
    (_heta : 0 < eta)
    (hv : ∀ i, v i ^ 2 ≤ eta⁻¹ ^ 2 * u i ^ 2) :
    |∑ i, u i * v i| ≤
      Real.sqrt (∑ i, u i ^ 2) *
        Real.sqrt (eta⁻¹ ^ 2 * ∑ i, u i ^ 2) := by
  refine (spectralSchwarzChain_abs u v).trans ?_
  gcongr
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hv i

/-- A stability numerator bound gives the corresponding inverse-stability
bound.  This elementary division lemma is used separately for every displayed
CEH estimate below. -/
theorem norm_div_le_of_norm_le_mul
    {numerator beta : ℂ} {bound : ℝ} (hbeta : beta ≠ 0)
    (hnumerator : ‖numerator‖ ≤ bound * ‖beta‖) :
    ‖numerator / beta‖ ≤ bound := by
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hbeta)).2 hnumerator

/-- CEH Lemma 5.6, first deterministic trace bound (`++` constellation),
proved separately from its numerator and stability estimates. -/
theorem deterministicTraceBound_pp
    {numerator beta : ℂ} {rho₁ rho₂ eta₁ s₂ : ℝ}
    (hbeta : beta ≠ 0)
    (hnumerator : ‖numerator‖ ≤
      (Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖) :
    ‖numerator / beta‖ ≤
      Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_div_le_of_norm_le_mul hbeta hnumerator

/-- CEH Lemma 5.6, second deterministic trace bound (`--` constellation). -/
theorem deterministicTraceBound_mm
    {numerator beta : ℂ} {rho₁ rho₂ eta₂ s₂ : ℝ}
    (hbeta : beta ≠ 0)
    (hnumerator : ‖numerator‖ ≤
      (Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖) :
    ‖numerator / beta‖ ≤
      Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_div_le_of_norm_le_mul hbeta hnumerator

/-- CEH Lemma 5.6, third deterministic trace bound (mixed constellation). -/
theorem deterministicTraceBound_mp
    {numerator beta : ℂ} {rho₁ rho₂ eta₁ eta₂ s₂ : ℝ}
    (hbeta : beta ≠ 0)
    (hnumerator : ‖numerator‖ ≤
      (Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖) :
    ‖numerator / beta‖ ≤
      Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_div_le_of_norm_le_mul hbeta hnumerator

/-- CEH Lemma 5.6, fourth (hatted one-observable) bound. -/
theorem deterministicHatTraceBound
    {numerator beta : ℂ} {rho₁ rho₂ eta₁ eta₂ s₂ : ℝ}
    (hbeta : beta ≠ 0)
    (hnumerator : ‖numerator‖ ≤
      (Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖) :
    ‖numerator / beta‖ ≤
      Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂ :=
  norm_div_le_of_norm_le_mul hbeta hnumerator

/-- CEH Lemma 5.6, fifth positive two-observable trace bound. -/
theorem deterministicPositiveTraceBound
    {numerator beta : ℂ} {rho₁ rho₂ s₂ : ℝ}
    (hbeta : beta ≠ 0)
    (hnumerator : ‖numerator‖ ≤ (rho₁ * rho₂ * s₂ ^ 2) * ‖beta‖) :
    ‖numerator / beta‖ ≤ rho₁ * rho₂ * s₂ ^ 2 :=
  norm_div_le_of_norm_le_mul hbeta hnumerator

/-- A generic simultaneous division lemma.  Each substantive numerator bound and
denominator nonvanishing is an explicit hypothesis; consequently this theorem
is not CEH Lemma 5.6.  `npp`, `nmm`, `nmp`, `nhat`, and `npos` denote the five numerators in
CEH (5.13). -/
theorem divideFiveNumeratorBoundsByDenominator
    {beta npp nmm nmp nhat npos : ℂ}
    {rho₁ rho₂ eta₁ eta₂ s₂ : ℝ}
    (hbeta : beta ≠ 0)
    (hpp : ‖npp‖ ≤
      (Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖)
    (hmm : ‖nmm‖ ≤
      (Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖)
    (hmp : ‖nmp‖ ≤
      (Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖)
    (hhat : ‖nhat‖ ≤
      (Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) *
        Real.sqrt (rho₁ * rho₂) * s₂) * ‖beta‖)
    (hpos : ‖npos‖ ≤ (rho₁ * rho₂ * s₂ ^ 2) * ‖beta‖) :
    (‖npp / beta‖ ≤ Real.sqrt (rho₂ / eta₁) * Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖nmm / beta‖ ≤ Real.sqrt (rho₁ / eta₂) * Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖nmp / beta‖ ≤ Real.sqrt (max (rho₁ / eta₂) (rho₂ / eta₁)) *
      Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖nhat / beta‖ ≤ Real.sqrt (min (rho₁ / eta₂) (rho₂ / eta₁)) *
      Real.sqrt (rho₁ * rho₂) * s₂) ∧
    (‖npos / beta‖ ≤ rho₁ * rho₂ * s₂ ^ 2) := by
  exact ⟨deterministicTraceBound_pp hbeta hpp,
    deterministicTraceBound_mm hbeta hmm,
    deterministicTraceBound_mp hbeta hmp,
    deterministicHatTraceBound hbeta hhat,
    deterministicPositiveTraceBound hbeta hpos⟩

end CEHNative.BlockBand.External.CEH
