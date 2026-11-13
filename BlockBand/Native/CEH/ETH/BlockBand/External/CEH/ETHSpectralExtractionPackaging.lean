module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHResolventSpectralTrace

/-!
# Packaging lemmas for the CEH spectral-point ETH extraction

This module supplies the last purely deterministic and finite-probability
steps of the extraction of the CEH local ETH estimate from the two-resolvent law.
It specializes the positive
spectral expansion at an ordered eigenvalue pair and packages a fixed-grid
two-resolvent estimate with the concrete grid inclusion and the exact square
cardinality loss.

The probability theorem below deliberately takes the pointwise fixed-grid
estimates as hypotheses.  Those hypotheses are the direct output expected from
the eventual CEH two-resolvent law; they are not stored in a structure or
promoted to a new input/certificate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory
open scoped ENNReal

/-- At its own eigenvalue, the positive resolvent weight is exactly the
inverse height. -/
theorem cehSpectralWeight_self {lambda eta : ℝ} (heta : 0 < eta) :
    cehSpectralWeight lambda lambda eta = eta⁻¹ := by
  unfold cehSpectralWeight
  rw [sub_self, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_add]
  field_simp [heta.ne']

/-- The ordered `(i,j)` spectral summand is controlled by the full positive
two-resolvent trace at the two matching eigenvalues.  This is the
finite-dimensional extraction used after the CEH two-resolvent law. -/
theorem spectralMatrixElement_sq_le_positiveKernel_at_eigenvalues
    {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ)
    (u : Fin N → Fin N → ℂ) {eta₁ eta₂ : ℝ}
    (heta₁ : 0 < eta₁) (heta₂ : 0 < eta₂)
    (A : LocalETHMatrix N) (i j : Fin N) :
    ‖spectralMatrixElement u A i j‖ ^ 2 ≤
      (N : ℝ) * eta₁ * eta₂ *
        (NTrace
          (spectralImaginaryKernel lam u (lam i) eta₁ * A *
            spectralImaginaryKernel lam u (lam j) eta₂ * Aᴴ)).re := by
  have hpair := spectralPair_le_re_normalizedTrace_kernel
    hN lam u (lam i) (lam j) heta₁.le heta₂.le A i j
  rw [cehSpectralWeight_self heta₁, cehSpectralWeight_self heta₂] at hpair
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 < (N : ℝ) * eta₁ * eta₂ :=
    mul_pos (mul_pos hNreal heta₁) heta₂
  calc
    ‖spectralMatrixElement u A i j‖ ^ 2 =
        ((N : ℝ) * eta₁ * eta₂) *
          ((N : ℝ)⁻¹ * eta₁⁻¹ * eta₂⁻¹ *
            ‖spectralMatrixElement u A i j‖ ^ 2) := by
              field_simp [hNreal.ne', heta₁.ne', heta₂.ne']
    _ ≤ ((N : ℝ) * eta₁ * eta₂) *
        (NTrace
          (spectralImaginaryKernel lam u (lam i) eta₁ * A *
            spectralImaginaryKernel lam u (lam j) eta₂ * Aᴴ)).re :=
      mul_le_mul_of_nonneg_left hpair hscale.le

/-- Actual-resolvent form of the positive spectral-pair extraction. -/
theorem spectralMatrixElement_sq_le_positiveResolvent_at_eigenvalues
    {N : ℕ} (hN : 0 < N) {H : LocalETHMatrix N}
    {lam : Fin N → ℝ} {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily H lam u)
    {eta₁ eta₂ : ℝ} (heta₁ : 0 < eta₁) (heta₂ : 0 < eta₂)
    (A : LocalETHMatrix N) (i j : Fin N) :
    ‖spectralMatrixElement u A i j‖ ^ 2 ≤
      (N : ℝ) * eta₁ * eta₂ *
        (NTrace
          (matrixImaginaryPart
              ((H - (((lam i : ℝ) : ℂ) +
                (eta₁ : ℂ) * Complex.I) • 1)⁻¹) * A *
            matrixImaginaryPart
              ((H - (((lam j : ℝ) : ℂ) +
                (eta₂ : ℂ) * Complex.I) • 1)⁻¹) * Aᴴ)).re := by
  rw [← spectralImaginaryKernel_eq_matrixImaginaryPart_resolvent
      hfamily (lam i) heta₁,
    ← spectralImaginaryKernel_eq_matrixImaginaryPart_resolvent
      hfamily (lam j) heta₂]
  exact spectralMatrixElement_sq_le_positiveKernel_at_eigenvalues
    hN lam u heta₁ heta₂ A i j

/-- Failure at one ordered pair of points of a deterministic grid. -/
def fixedTwoResolventGridPairBadEvent {Ω X ι : Type*}
    (f : Ω → X → X → ℂ) (grid : ι → X) (threshold : ℝ)
    (a b : ι) : Set Ω :=
  {ω | threshold ≤ ‖f ω (grid a) (grid b)‖}

/-- The fixed-grid bad event is exactly the finite union of its ordered
grid-pair bad events. -/
theorem fixedTwoResolventGridBadEvent_eq_iUnion
    {Ω X ι : Type*} [Fintype ι]
    (f : Ω → X → X → ℂ) (grid : ι → X) (threshold : ℝ) :
    fixedTwoResolventGridBadEvent f grid threshold =
      ⋃ a : ι, ⋃ b : ι,
        fixedTwoResolventGridPairBadEvent f grid threshold a b := by
  ext ω
  simp [fixedTwoResolventGridBadEvent, fixedTwoResolventGridPairBadEvent]

/-- A direct fixed-grid two-resolvent tail estimate loses exactly the square
of the grid cardinality.  The hypothesis is pointwise in the two deterministic
grid points, matching the eventual two-resolvent law rather than introducing
another packaged probabilistic assumption. -/
theorem measure_fixedTwoResolventGridBadEvent_le_card_sq_mul
    {Ω X ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : Ω → X → X → ℂ) (grid : ι → X)
    (threshold : ℝ) (p : ENNReal)
    (hpair : ∀ a b : ι,
      μ (fixedTwoResolventGridPairBadEvent f grid threshold a b) ≤ p) :
    μ (fixedTwoResolventGridBadEvent f grid threshold) ≤
      (Fintype.card ι : ENNReal) ^ 2 * p := by
  rw [fixedTwoResolventGridBadEvent_eq_iUnion]
  calc
    μ (⋃ a : ι, ⋃ b : ι,
        fixedTwoResolventGridPairBadEvent f grid threshold a b) ≤
        ∑ a : ι, ∑ b : ι,
          μ (fixedTwoResolventGridPairBadEvent f grid threshold a b) := by
      exact
        (measure_iUnion_fintype_le (μ := μ)
          (fun a : ι => ⋃ b : ι,
            fixedTwoResolventGridPairBadEvent f grid threshold a b)).trans
          (Finset.sum_le_sum fun a _ =>
            measure_iUnion_fintype_le (μ := μ)
              (fun b : ι =>
                fixedTwoResolventGridPairBadEvent f grid threshold a b))
    _ ≤ ∑ _a : ι, ∑ _b : ι, p := by
      gcongr with a b
      exact hpair a b
    _ = (Fintype.card ι : ENNReal) ^ 2 * p := by
      simp [pow_two, mul_assoc]

/-- Combine a deterministic random-point-to-grid inclusion with fixed-grid
pointwise tails.  This is the exact probability packaging required after
applying the eventual CEH two-resolvent law on the finite grid. -/
theorem measure_localETHTwoResolventRandomBadEvent_le_card_sq_mul_of_subset
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {N : ℕ}
    (μ : Measure Ω) (f : Ω → ℂ → ℂ → ℂ)
    (etaF : ℝ → ℝ) (ξ : ℝ) (lam : Ω → Fin N → ℝ)
    (threshold : Fin N → Fin N → ℝ)
    (grid : ι → ℂ) (gridThreshold : ℝ) (p : ENNReal)
    (hsubset :
      localETHTwoResolventRandomBadEvent f etaF ξ lam threshold ⊆
        fixedTwoResolventGridBadEvent f grid gridThreshold)
    (hpair : ∀ a b : ι,
      μ (fixedTwoResolventGridPairBadEvent
        f grid gridThreshold a b) ≤ p) :
    μ (localETHTwoResolventRandomBadEvent
        f etaF ξ lam threshold) ≤
      (Fintype.card ι : ENNReal) ^ 2 * p := by
  exact (measure_mono hsubset).trans
    (measure_fixedTwoResolventGridBadEvent_le_card_sq_mul
      μ f grid gridThreshold p hpair)

/-- Specialization of the preceding probability packaging to the concrete
`meshCount+1` CEH grid. -/
theorem measure_localETHTwoResolventRandomBadEvent_le_concreteGrid_sq_mul
    {Ω : Type*} [MeasurableSpace Ω] {N meshCount : ℕ}
    (μ : Measure Ω) (f : Ω → ℂ → ℂ → ℂ)
    (etaF : ℝ → ℝ) (ξ E₀ R : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ)
    (gridThreshold : ℝ) (p : ENNReal)
    (hsubset :
      localETHTwoResolventRandomBadEvent f etaF ξ lam threshold ⊆
        fixedTwoResolventGridBadEvent f
          (localETHSpectralGridPoint N etaF ξ E₀ R meshCount)
          gridThreshold)
    (hpair : ∀ a b : Fin (meshCount + 1),
      μ (fixedTwoResolventGridPairBadEvent f
        (localETHSpectralGridPoint N etaF ξ E₀ R meshCount)
        gridThreshold a b) ≤ p) :
    μ (localETHTwoResolventRandomBadEvent
        f etaF ξ lam threshold) ≤
      ((meshCount + 1 : ℕ) : ENNReal) ^ 2 * p := by
  simpa using
    measure_localETHTwoResolventRandomBadEvent_le_card_sq_mul_of_subset
      μ f etaF ξ lam threshold
      (localETHSpectralGridPoint N etaF ξ E₀ R meshCount)
      gridThreshold p hsubset hpair

end CEHNative.BlockBand.External.CEH
