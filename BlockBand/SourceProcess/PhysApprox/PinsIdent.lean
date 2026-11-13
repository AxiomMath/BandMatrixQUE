module

public import BlockBand.SourceProcess.PhysApprox.Defs
public import BlockBand.SourceProcess.ClosedLimit.Tested

/-!
# The tested complex model and the limit law

* `complexObs`: the observables of a complex model and their natural filtration.
* `IsTestedComplexModel`: a complex model whose martingale clauses are stated as tested
  increments against the natural filtration of `complexObs`.
* `ComplexClosedLimitLaw` (b3): the limit points of the capped closed expectation are restricted
  values of tested complex models.
* `IsStoppedTestedComplexModel`, `ComplexClosedLimitLawStopped`: the same with every clause
  tested after the Gram trace stop.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ComplexConjugate

/-- Observables of a complex model: the Gram entries, the entrance coordinates (constant in
time) and the `𝒦` entries. Their natural filtration is `ClosedLimit.pastFiltration`. -/
def complexObs {Ω : Type*} {K np : ℕ} (tseq : Ω → ℕ → ℝ)
    (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) :
    (Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) ⊕ ℕ ⊕ (Fin np × Fin np) → ℝ≥0 → Ω → ℂ
  | Sum.inl e => fun u ω => gramEntry e (G u ω)
  | Sum.inr (Sum.inl k) => fun _ ω => (tseq ω k : ℂ)
  | Sum.inr (Sum.inr ij) => fun u ω => Kc u ω ij.1 ij.2

/-- The deterministic Gram birth jumps of `IsFiniteComplexSourceModel.solution`
(`birthJump (τ - s) (d_* m)`). -/
def gramJ (b s : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (t : ℝ≥0) : GramState (SrcCol K (Fin np)) :=
  birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)

/-- The deterministic `𝒦` birth jumps of `IsFiniteComplexSourceModel.complex`
(`kBirthJump E (τ - s) m`, entry `a m_j`). -/
def kJ (E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (t : ℝ≥0) : Matrix (Fin np) (Fin np) ℂ :=
  kBirthJump E (fun j => τ j - s) m (t : ℝ)

/-- **A tested complex finite model** (for (b3)): the data of `IsFiniteComplexSourceModel`
without a filtration; strong measurability of `G u` and `Kc u`; `G - gramJ` and `Kc - kJ`
continuous for **every** `ω`; `GramFeasible` a.s.; and tested **unstopped** increments (against
`complexObs`) of every martingale clause, with the same integrands: the Gram `drift` and `bracket`
of `IsBornGramSolution`, and the five `𝒦` clauses of `IsComplexSourceExtension`.
-/
structure IsTestedComplexModel (b E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (h : ℝ) (K : ℕ)
    (entrance : Measure (Measure unitInterval)) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) : Prop where
  prob : IsProbabilityMeasure Q
  entrance_measurable : Measurable tseq
  gram_measurable : ∀ u, StronglyMeasurable (G u)
  k_measurable : ∀ u, StronglyMeasurable (Kc u)
  entrance_sequence : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω)
  entrance_law : Q.map (fun ω => seqTraceMeasure (tseq ω)) = entrance
  initial : ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin np) (tseq ω) h ∧ Kc 0 ω = 0
  continuous : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u
  k_continuous : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u
  feasible : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin np)) (G t ω)
  drift : ∀ e, IsTestedMart Q (complexObs tseq G Kc)
    (bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
      (fun t _ => gramJ b s τ m t) e)
  bracket : ∀ e e', IsTestedMart Q (complexObs tseq G Kc) (fun t ω =>
    bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
        (fun t _ => gramJ b s τ m t) e t ω *
      bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
        (fun t _ => gramJ b s τ m t) e' t ω -
      ∫ u in Set.Ioc (0 : ℝ) t, gramCovEntry (transportD0 b E) (srcSignature K (Fin np)) e e'
        (G u.toNNReal ω))
  martingale : ∀ i j : Fin np, IsTestedMart Q (complexObs tseq G Kc)
    (kCompensated Kc (fun t _ => kJ E s τ m t) i j)
  holomorphic : ∀ i j k l : Fin np, IsTestedMart Q (complexObs tseq G Kc) (fun t ω =>
    kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
      kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω)
  antiholomorphic : ∀ i j k l : Fin np, IsTestedMart Q (complexObs tseq G Kc) (fun t ω =>
    kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
      conj (kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω) -
      ∫ u in Set.Ioc (0 : ℝ) t, ((2 * etaZ b E ^ 2 * transportD0 b E : ℝ) : ℂ) *
        (G u.toNNReal ω).2 (Sum.inr i) (Sum.inr k) *
        gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np))
          (Sum.inr l) (Sum.inr j))
  crossM : ∀ (i j : Fin np) (k l : SrcCol K (Fin np)), IsTestedMart Q (complexObs tseq G Kc)
    (fun t ω => kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
      bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G (fun t _ => gramJ b s τ m t)
        (0, k, l) t ω -
      ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
        (G u.toNNReal ω).2 (Sum.inr i) l *
        gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)) k (Sum.inr j))
  crossB : ∀ (i j : Fin np) (k l : SrcCol K (Fin np)), IsTestedMart Q (complexObs tseq G Kc)
    (fun t ω => kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
      bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G (fun t _ => gramJ b s τ m t)
        (1, k, l) t ω -
      ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
        (G u.toNNReal ω).2 (Sum.inr i) l *
        (gramC1 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)))ᴴ k (Sum.inr j))

/-- **(b3) Limit law**: `ComplexClosedLimitIdentification` with the tested form
`IsTestedComplexModel` in place of `IsFiniteComplexSourceModel`. -/
def ComplexClosedLimitLaw : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ L : ℝ,
      Tendsto (fun n => cappedClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 L) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
        (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
        (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
        IsTestedComplexModel b E s τ m h K (entranceLaw P μ s) Q tseq G Kc ∧
        restrictedModelExpectation K h s T Q tseq G Kc Φ = L

/-!
## The stopped tested form
-/

/-- **A stopped-tested complex finite model** (the stopped form of (b3)): the data fields of
`IsTestedComplexModel`, with each of the seven martingale clauses replaced by tested increments
of the clause **stopped at every Gram trace level** `L` (`stoppedProcess … (gramTraceStop G L)`),
exactly the stopped processes of the `IsBornGramSolution` and `IsComplexSourceExtension`.
No moment of an unstopped process is required.
-/
structure IsStoppedTestedComplexModel (b E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (h : ℝ) (K : ℕ)
    (entrance : Measure (Measure unitInterval)) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) : Prop where
  prob : IsProbabilityMeasure Q
  entrance_measurable : Measurable tseq
  gram_measurable : ∀ u, StronglyMeasurable (G u)
  k_measurable : ∀ u, StronglyMeasurable (Kc u)
  entrance_sequence : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω)
  entrance_law : Q.map (fun ω => seqTraceMeasure (tseq ω)) = entrance
  initial : ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin np) (tseq ω) h ∧ Kc 0 ω = 0
  continuous : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u
  k_continuous : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u
  feasible : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin np)) (G t ω)
  drift : ∀ (L : ℝ) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess
      (bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
        (fun t _ => gramJ b s τ m t) e) (gramTraceStop G L))
  bracket : ∀ (L : ℝ) (e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess (fun t ω =>
      bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e' t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, gramCovEntry (transportD0 b E) (srcSignature K (Fin np)) e e'
          (G u.toNNReal ω)) (gramTraceStop G L))
  martingale : ∀ (L : ℝ) (i j : Fin np), IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (kCompensated Kc (fun t _ => kJ E s τ m t) i j) (gramTraceStop G L))
  holomorphic : ∀ (L : ℝ) (i j k l : Fin np), IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω) (gramTraceStop G L))
  antiholomorphic : ∀ (L : ℝ) (i j k l : Fin np), IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        conj (kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω) -
        ∫ u in Set.Ioc (0 : ℝ) t, ((2 * etaZ b E ^ 2 * transportD0 b E : ℝ) : ℂ) *
          (G u.toNNReal ω).2 (Sum.inr i) (Sum.inr k) *
          gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np))
            (Sum.inr l) (Sum.inr j)) (gramTraceStop G L))
  crossM : ∀ (L : ℝ) (i j : Fin np) (k l : SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) (0, k, l) t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G u.toNNReal ω).2 (Sum.inr i) l *
          gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)) k (Sum.inr j))
      (gramTraceStop G L))
  crossB : ∀ (L : ℝ) (i j : Fin np) (k l : SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) (1, k, l) t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G u.toNNReal ω).2 (Sum.inr i) l *
          (gramC1 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)))ᴴ k
            (Sum.inr j))
      (gramTraceStop G L))

/-- **(b3, stopped form) Limit law with stopped tested identities**: `ComplexClosedLimitLaw`
with `IsStoppedTestedComplexModel` in place of `IsTestedComplexModel`.
-/
def ComplexClosedLimitLawStopped : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ L : ℝ,
      Tendsto (fun n => cappedClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 L) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
        (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
        (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
        IsStoppedTestedComplexModel b E s τ m h K (entranceLaw P μ s) Q tseq G Kc ∧
        restrictedModelExpectation K h s T Q tseq G Kc Φ = L

end BlockBand.SourceProcess.PhysApprox
