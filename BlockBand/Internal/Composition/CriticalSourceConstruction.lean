module

public import BlockBand.Internal.Composition.CriticalConstruction
public import BlockBand.Critical.JointRecovery.ReadoutDetermination
public import BlockBand.Transmission.LawForced.LawHolds

/-!
# The critical law is determined by the construction

The last sentence of Theorem 1.3 says that the critical law is determined by the construction of the random
entire function. It is stated here as the conjunction of five facts, all proved with no hypotheses:

* (A) `critical_construction_unconditional`: every critical family satisfies, at every ratio and for every finite
  nonnegative continuous profile family, the root/derivative rule of the construction (`RootDerivativeRule`);
* (B) `rootDerivativeRule_determines`: at each ratio, at most one law satisfies the rule for every profile
  family (the readout Laplace functionals determine the marked law, `markedLaw_eq_of_readoutLaplace`);
* (C) `complexSourceLimit_unique`: the complex source limit used by the rule is unique;
* (D) `complexSourceLaw_unconditional`: `ComplexSourceLawContract`, identifying integrals against that source
  limit with the iterated limits (K → ∞, then h → 0) of the finite complex source model;
* (E) `transmissionLaw_unconditional`: `TransmissionLawContract`, the law of the transmission process that gives
  the entrance law of the finite source model.

(D) and (E) are the instances used in the proof of `entireLaw_unconditional`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Composition

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CriticalEntire BlockBand.Internal.Contracts.TransmissionLaws

/-- (B) The construction clause determines the law: two laws satisfying the root/derivative rule for every
profile family at the same ratio are equal. -/
theorem rootDerivativeRule_determines (b E : ℝ) (τ : PositiveRatio)
    (law law' : ProbabilityMeasure MarkedPointMeasure)
    (h : ∀ (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q → RootDerivativeRule b E τ q law)
    (h' : ∀ (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q → RootDerivativeRule b E τ q law') :
    law = law' := by
  apply BlockBand.Critical.JointRecovery.markedLaw_eq_of_readoutLaplace
  intro k q hq f hf
  obtain ⟨⟨μ, hμ⟩, hl⟩ := h k q hq
  rw [hl μ hμ f hf, (h' k q hq).2 μ hμ f hf]

/-- (C) The complex source limit is unique. -/
theorem complexSourceLimit_unique (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (ν ν' : Measure (SourceData np))
    (h : IsComplexSourceLimit b E T τ m ν) (h' : IsComplexSourceLimit b E T τ m ν') : ν = ν' := by
  have := h.1; have := h'.1
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact tendsto_nhds_unique (h.2 f) (h'.2 f)

/-- (D) `ComplexSourceLawContract` with no hypotheses. -/
theorem complexSourceLaw_unconditional : ComplexSourceLawContract := by
  have source := BlockBand.Native.PSSS.sourceContract_holds_zero
  have hLp := BlockBand.GaussianCalculus.gaussianLpGradient_holds
  have hP := BlockBand.GaussianCalculus.gaussianPoincare_holds
  have hGA := BlockBand.Internal.Composition.gaussianAbsorption_native source
  have hMT := BlockBand.Internal.Composition.matchedTraces_native source
  have hSR := BlockBand.Internal.Composition.scalarRecursion_native source
  exact BlockBand.SourceProcess.ComplexFreq.complexSourceLawContract_of_physFreq
    hMT hGA hLp hP hSR
    (BlockBand.SourceProcess.PhysApprox.complexPhysicalApproximationFreq_holds hMT hGA hSR hLp hP
      BlockBand.SourceProcess.Kolmogorov.kolmogorovConjugate_holds)

/-- (E) `TransmissionLawContract` with no hypotheses. -/
theorem transmissionLaw_unconditional : TransmissionLawContract := by
  have source := BlockBand.Native.PSSS.sourceContract_holds_zero
  exact BlockBand.Transmission.LawForced.transmissionLawContract_holds
    (BlockBand.Internal.Composition.matchedTraces_native source)
    (BlockBand.Internal.Composition.gaussianAbsorption_native source)
    BlockBand.GaussianCalculus.gaussianLpGradient_holds BlockBand.GaussianCalculus.gaussianPoincare_holds

/-- Theorem 1.3, last sentence: the critical law is determined by the construction of the random entire
function. Conjunction (A) ∧ (B) ∧ (C) ∧ (D) ∧ (E); see the module docstring. -/
theorem critical_determined_unconditional
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    (∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
        ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
          RootDerivativeRule b E τ q (family τ)) ∧
    (∀ (τ : PositiveRatio) (law law' : ProbabilityMeasure MarkedPointMeasure),
      (∀ (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q → RootDerivativeRule b E τ q law) →
      (∀ (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q → RootDerivativeRule b E τ q law') →
        law = law') ∧
    (∀ (T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (ν ν' : Measure (SourceData np)),
      IsComplexSourceLimit b E T τ m ν → IsComplexSourceLimit b E T τ m ν' → ν = ν') ∧
    ComplexSourceLawContract ∧
    TransmissionLawContract :=
  ⟨critical_construction_unconditional b E hb hb' hE,
   fun τ law law' h h' => rootDerivativeRule_determines b E τ law law' h h',
   fun T _ τ m ν ν' h h' => complexSourceLimit_unique b E T τ m ν ν' h h',
   complexSourceLaw_unconditional,
   transmissionLaw_unconditional⟩

end BlockBand.Internal.Composition
