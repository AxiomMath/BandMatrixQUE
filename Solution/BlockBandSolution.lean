module

public import BlockBand
public import BlockBand.Internal.Composition.QUEUnconditional
public import BlockBand.Internal.Composition.CriticalUnconditional
public import BlockBand.Internal.Composition.EndpointsUnconditional
public import BlockBand.Internal.Composition.CriticalConstruction
public import BlockBand.Internal.Composition.CriticalSourceConstruction

/-!
# Satisfying the formal challenge

Proofs of the three statements of `BlockBandChallenge` (Theorems 1.1, 1.3 and 1.4 of the paper),
from the main theorems of the `BlockBand` library, together with a companion theorem for the last sentence of
Theorem 1.3: the critical law is determined by the construction of the random entire function.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand

open MeasureTheory

-- The linter option only silences the unused binders `hnW` and `hθ'`, which the statements keep.
set_option linter.unusedVariables false in
/-- **Theorem 1.1** (quantum unique ergodicity at every bulk rank).

There is one constant depending only on `(b, θ, T)`. Dimensions, the exact
physical Gaussian model, deterministic rank, and deterministic real site test
are quantified after that constant and outside the expectation. The estimate
uses the physical row-variance-one matrix and admits every parity. -/
theorem que
    (b θ T : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hθ' : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n W : ℕ)
        (hn : 4 ≤ n) (hW : 0 < W)
        (hnW : (n : ℝ) ≤ T * (W : ℝ)),
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      Nonempty (FiniteRealization p) ∧
        ∀ (R : FiniteRealization p) (α : Fin p.N),
          IsBulkRank p θ α →
        ∀ v : p.Site → ℝ, (∀ x, |v x| ≤ 1) →
          R.spectral.queStatistic α v ≤
            C * (p.ratio + Real.rpow p.ratio (3 / 2 : ℝ)) +
              1 / ((W : ℝ) + 1) := by
  exact BlockBand.Internal.Composition.que_unconditional b θ T hb hb' hθ hθ'

/-- **Theorem 1.3** (the critical joint law of eigenvalues and eigenvector profiles).

For every fixed admissible `(b,E)` there is a unique all-ratio family. Its
characterization includes convergence along every critical sequence, the full
marked vague topology, simple locations, both mean-intensity identities, and
both stationarities. There is no rate or subsequence parameter. -/
theorem critical
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family := by
  exact BlockBand.Internal.Composition.critical_unconditional b E hb hb' hE

/-- **Theorem 1.4** (positive profile variance and the sine and Poisson endpoints).

The assertion applies to the already-characterized critical family. It gives a
single smoothing-independent variance, positivity for every positive ratio,
the right limit at zero, and the sine/Poisson spectral limits in that order of
limits. No diagonal `n/W → ∞` assertion is made. -/
theorem endpoints
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
        HasCriticalEndpoints b E hb hb' family := by
  exact BlockBand.Internal.Composition.endpoints_unconditional b E hb hb' hE

/-- **Theorem 1.3, last sentence** (companion to `critical`): the critical law is determined by the
construction of the random entire function.

(A) every critical family satisfies, at every ratio and for every finite nonnegative continuous profile family,
the root/derivative rule of the construction; (B) at most one law satisfies that rule for every profile family;
(C) the complex source limit used by the rule is unique; (D) its integrals are the iterated limits of the finite
complex source model; (E) the law of the transmission process that gives the entrance law of that model. -/
theorem critical_construction
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    (∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
        ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)),
          Internal.Contracts.CriticalEntire.IsProfileFamily q →
            Internal.Contracts.CriticalEntire.RootDerivativeRule b E τ q (family τ)) ∧
    (∀ (τ : PositiveRatio) (law law' : ProbabilityMeasure MarkedPointMeasure),
      (∀ (k : ℕ) (q : Fin k → C(Torus, ℝ)), Internal.Contracts.CriticalEntire.IsProfileFamily q →
        Internal.Contracts.CriticalEntire.RootDerivativeRule b E τ q law) →
      (∀ (k : ℕ) (q : Fin k → C(Torus, ℝ)), Internal.Contracts.CriticalEntire.IsProfileFamily q →
        Internal.Contracts.CriticalEntire.RootDerivativeRule b E τ q law') →
        law = law') ∧
    (∀ (T : ℝ) {np : ℕ} (τ m : Fin np → ℝ)
      (ν ν' : Measure (Internal.Contracts.TransmissionLaws.SourceData np)),
      Internal.Contracts.TransmissionLaws.IsComplexSourceLimit b E T τ m ν →
      Internal.Contracts.TransmissionLaws.IsComplexSourceLimit b E T τ m ν' → ν = ν') ∧
    Internal.Contracts.TransmissionLaws.ComplexSourceLawContract ∧
    Internal.Contracts.TransmissionLaws.TransmissionLawContract := by
  exact BlockBand.Internal.Composition.critical_determined_unconditional b E hb hb' hE

end BlockBand
