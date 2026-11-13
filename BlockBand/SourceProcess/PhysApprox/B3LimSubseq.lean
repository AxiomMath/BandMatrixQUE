module

public import BlockBand.SourceProcess.PhysApprox.B3LimReduce

/-!
# The subsequence form of the conditioned cap limit

A limit passage by compactness produces, along a **further** subsequence of any `W_n → ∞`, a model
whose value is the limit of the conditioned expectations. `ComplexCapSubseq` is that form,
for every cap `K` with positive entrance mass and every non-atomic cutoff `h`. It gives the
conditioned law in the stopped form, because a convergent sequence has only one limit:

* **`complexCapCondLawStopped_of_subseq`**: `ComplexCapSubseq → ComplexCapCondLawStopped`;
* **`complexCapCondLimit_of_subseq`**: with `TransmissionLawContract`, `ComplexCapCondLimit`;
* **`targetCapCond'_of_subseq`**: if the estimates of `TargetCapCond'` and `ComplexClosedFeasible`
  give `ComplexCapSubseq`, then `ComplexClosedFeasible` gives `TargetCapCond'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal

/-- **The subsequence form of the conditioned cap limit**: for non-atomic
`0 < h < 1`, every cap `K` with `P(μ(s) ∈ capSet K h) ≠ 0` and every `W_n → ∞`, some further
subsequence and some stopped tested complex model with entrance `μ(s)[|capSet K h]` are such that
the conditioned closed expectations converge along it to the model value at `T − s`. -/
def ComplexCapSubseq : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ h : ℝ, 0 < h → h < 1 → CapCond.NoAtom (entranceLaw P μ s) h →
  ∀ K : ℕ, entranceLaw P μ s (capSet K h) ≠ 0 →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
        (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
        (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
        IsStoppedTestedComplexModel b E s τ m h K ((entranceLaw P μ s)[|capSet K h]) Q
          tseq G Kc ∧
        Tendsto (fun n => condClosedPhysExpectation b E s T h τ m Φ K (φ (ψ n))) atTop
          (𝓝 (modelExpectation K s T Q G Kc Φ))

/-- **The subsequence form gives the conditioned law** (uniqueness of limits). -/
theorem complexCapCondLawStopped_of_subseq (hS : ComplexCapSubseq) : ComplexCapCondLawStopped := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ h hh0 hh1 hA
  refine Frequently.of_forall fun K hne φ hφ ℓ hℓ => ?_
  obtain ⟨ψ, hψ, Ω', mΩ', Q, tseq, G, Kc, hM, hT⟩ :=
    hS b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ h hh0 hh1 hA K hne φ hφ
  exact ⟨Ω', mΩ', Q, tseq, G, Kc, hM,
    tendsto_nhds_unique hT (hℓ.comp hψ.tendsto_atTop)⟩

/-- **`ComplexCapCondLimit` from the subsequence form.** -/
theorem complexCapCondLimit_of_subseq (hTL : TransmissionLawContract) (hS : ComplexCapSubseq) :
    ComplexCapCondLimit :=
  complexCapCondLimit_of_law hTL (complexCapCondLaw_of_stopped
    (complexCapCondLawStopped_of_subseq hS))

/-- **`TargetCapCond'` from a passage to the subsequence form**, given `ComplexClosedFeasible`. -/
theorem targetCapCond'_of_subseq
    (hP : TransmissionLawContract → ExistsTimeSFrame → ComplexClosedSummed → ComplexClosedTight →
      ComplexKStoppedMomentMax → ComplexClosedCurrent → ComplexClosedLindeberg →
      ComplexClosedFeasible → ComplexCapSubseq)
    (hF : ComplexClosedFeasible) : TargetCapCond' :=
  fun hTL hEx hS hT hK hC hL => complexCapCondLimit_of_subseq hTL (hP hTL hEx hS hT hK hC hL hF)

end BlockBand.SourceProcess.PhysApprox.B3
