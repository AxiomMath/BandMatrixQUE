module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Init
public import BlockBand.SourceProcess.PhysApprox.B3Ident2KStop
public import BlockBand.SourceProcess.PhysApprox.B3FddMain

/-!
# `TargetCapIdentAll` reduced to four estimates

Every estimate has the premises of `ComplexCapIdentAll` (packaged as `CapIdentPremise`:
admissible frame, transmission limit, non-atomic `h`, positive cap mass, `W_n → ∞`, a continuous
candidate `(Q, tseq, G, 𝒦)` that is an uncapped conditioned fdd limit) and, where needed, the
hypotheses of `TargetCapFdd`.

* `CapIdentEntrance` (the scalar entrance): `tseq` is a transmission sequence a.s. and
  `seqTraceMeasure ∘ tseq` has law `μ(s)[|capSet K h]`. Uses only `TransmissionLawContract`
  (`tendsto_capWeighted`, `countExt_smCount`).
* `CapIdentGram` (the Gram coordinates): the Gram coordinate identities of the limit at the trace
  stops.
* `CapIdentKDouble` (the `𝒦` coordinates): the `𝒦` coordinate identities stopped at
  `σ_L ∧ ρ_M`, `ρ_M` the `𝒦` level stop (`kLevelStop`), for every `M`. Before `ρ_M` every
  coordinate is bounded, so this is the bounded limit passage, as for the Gram coordinates.
* `CapIdentKStop` (the `𝒦` stop in the limit; limit form of `ComplexKStoppedMomentMax`):
  `IsKStopDominated`.

Proved here: **`complexCapIdentAll_of_pins`**, **`targetCapIdentAll_of_pins`** and
**`targetCapCond'_of_identPins`** (the four estimates give `TargetCapCond'`, with
`Fdd.targetCapFddAll_holds`). The initial state is proved from the entrance (`ae_tseq_ne`,
`ae_initial_of_fddAll`). The other fields of the model need no further hypothesis: probability,
measurability and every-`ω` continuity (`IsCapLimitData`), feasibility at every time
(`ae_feasible_all`), `𝒦(0) = 0` (`ae_kc_zero`); the removal of `ρ_M` is
`isKCoordTested_of_double`; the seven clauses come from the coordinate identities by
`isStoppedTestedComplexModel_of_coord`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- **The premises of `ComplexCapIdentAll`**, for one frame and one candidate. -/
def CapIdentPremise (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) {Ω' : Type} [MeasurableSpace Ω'] (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) : Prop :=
  FrameDomain b E τ m T s h K Vs ∧ IsTransmissionLimit b E (fun _ => 0) P μ ∧
    CapCond.NoAtom (entranceLaw P μ s) h ∧ entranceLaw P μ s (capSet K h) ≠ 0 ∧
    Tendsto φ atTop atTop ∧ IsCapLimitData b E s τ m K Q tseq G Kc ∧
    IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc

/-- **`CapIdentEntrance`**: the limit entrance coordinates form a transmission sequence whose
trace measure has law `μ(s)[|capSet K h]`. -/
def CapIdentEntrance : Prop :=
  TransmissionLawContract →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    (∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω)) ∧
      Q.map (fun ω => seqTraceMeasure (tseq ω)) = (entranceLaw P μ s)[|capSet K h]

/-- **`CapIdentGram`**: the Gram coordinate identities of the limit at the trace stops. -/
def CapIdentGram : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    IsGramCoordTested b E s τ m Q tseq G Kc (gramTraceStop G)

/-- **`CapIdentKDouble`**: the `𝒦` coordinate identities of the limit stopped at `σ_L ∧ ρ_M`,
for every `𝒦` level `M`, given the Gram identities. -/
def CapIdentKDouble : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    IsGramCoordTested b E s τ m Q tseq G Kc (gramTraceStop G) →
    ∀ M : ℕ, IsKCoordTested b E s τ m Q tseq G Kc
      (fun L ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω))

/-- **`CapIdentKStop`: the `𝒦` stop in the limit** (the limit form of
`ComplexKStoppedMomentMax`): the births-removed `|𝒦|²` is dominated before every trace stop. -/
def CapIdentKStop : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc → IsKStopDominated E s τ m Q G Kc

/-- **`ComplexCapIdentAll` from the hypotheses of `TargetCapFdd` and the four estimates.** -/
theorem complexCapIdentAll_of_pins (hTL : TransmissionLawContract) (hS : ComplexClosedSummed)
    (hT : ComplexClosedTight) (hK : ComplexKStoppedMomentMax) (hL : ComplexClosedLindeberg)
    (hEnt : CapIdentEntrance) (hGr : CapIdentGram) (hKD : CapIdentKDouble)
    (hKS : CapIdentKStop) : ComplexCapIdentAll := by
  intro b E np τ m T s h K Vs hD Ω mΩ P μ hlim hA hne φ hφ Ω' mΩ' Q tseq G Kc hdat hfdd
  have hP : CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc :=
    ⟨hD, hlim, hA, hne, hφ, hdat, hfdd⟩
  obtain ⟨hQ, htm, hGm, hKm, hc, hkc⟩ := hdat
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, hs, hτ, hh0, -, -⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  have hcap := hφ.eventually (eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh0 hA hne)
  have hfe := ae_feasible_all hD hφ hfdd hobs hcap hc
  have hK0 := ae_kc_zero hb1 hE1 hE2 hτ hfdd hobs hcap
  obtain ⟨hseq, hlaw⟩ := hEnt hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  have hG0 := ae_initial_of_fddAll hD hφ hfdd hobs hcap (ae_tseq_ne htm hseq hlaw hA)
  have hGc := hGr hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  have hKc := isKCoordTested_of_double hobs hc hkc hfe
    (hKD hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGc)
    (hKS hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP)
  exact isStoppedTestedComplexModel_of_coord hQ htm hGm hKm hseq hlaw (hG0.and hK0) hc hkc hfe
    hGc hKc

/-- **`TargetCapIdentAll` from the four estimates.** -/
theorem targetCapIdentAll_of_pins (hEnt : CapIdentEntrance) (hGr : CapIdentGram)
    (hKD : CapIdentKDouble) (hKS : CapIdentKStop) : TargetCapIdentAll :=
  fun hTL hS hT hK hL => complexCapIdentAll_of_pins hTL hS hT hK hL hEnt hGr hKD hKS

/-- **`TargetCapCond'` from the four estimates** (with `Fdd.targetCapFddAll_holds`). -/
theorem targetCapCond'_of_identPins (hEnt : CapIdentEntrance) (hGr : CapIdentGram)
    (hKD : CapIdentKDouble) (hKS : CapIdentKStop) : TargetCapCond' :=
  targetCapCond'_of_all Fdd.targetCapFddAll_holds (targetCapIdentAll_of_pins hEnt hGr hKD hKS)

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
