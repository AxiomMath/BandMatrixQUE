module

public import BlockBand.SourceProcess.ComplexFreq.Interface
public import BlockBand.SourceProcess.ComplexConstruct.Holds
public import BlockBand.SourceProcess.ComplexSplit.Holds2
public import BlockBand.SourceProcess.SourcePins.Freq

/-!
# `ComplexSourceConstruction` and `ComplexSourceLawContract` with the frequent approximation

The physical approximation step only needs to hold frequently in `h`
(`ComplexPhysicalApproximationFreq`).
* `iterated_values_freq`: the iterated model values, from the frequent form.
* `complexSourceConstruction_of_pins_freq`: `ComplexSourceConstruction` from the named steps with
  the frequent physical approximation.
* `complexSourceLawContract_of_freq`: `ComplexSourceLawContract` from the matched-traces, Gaussian
  and scalar-recursion inputs, `BornKExtension`, `ComplexCutoffRemoval` and
  `ComplexPhysicalApproximationFreq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexFreq

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ComplexConstruct
open scoped NNReal

/-- **Iterated model values** (as `ComplexConstruct.iterated_values`), from the frequent
physical approximation. -/
theorem iterated_values_freq (hA1 : EntranceAtomic) (hA2 : SeqExtraction)
    (hU : ComplexFiniteUniqueness) (hEx : ComplexModelExists) (hCap : ComplexCapRemoval)
    (hCut : ComplexCutoffRemoval) (hPA : ComplexPhysicalApproximationFreq)
    {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T : ℝ} (hD : ComplexSourceLawDomain b E τ m T)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) {s : ℝ} (hs : 0 < s) (hsτ : ∀ j, s < τ j)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) :
    ∃ Ψ : ℕ → ℝ → ℝ, RealizedValues b E s T τ m (entranceLaw P μ s) Φ Ψ ∧
      ∃ Λ : ℝ → ℝ, (∀ h, 0 < h → Tendsto (fun K => Ψ K h) atTop (𝓝 (Λ h))) ∧
        ∃ L : ℝ, Tendsto Λ (𝓝[>] 0) (𝓝 L) ∧
          Tendsto (physExpectation b E T τ m Φ) atTop (𝓝 L) := by
  obtain ⟨hb0, hb1, hE1, hE2, -⟩ := id hD
  obtain ⟨ρ, hρ, hρseq, hent⟩ := entrance_sequence hA1 hA2 hb0 hb1 hE1 hE2 hlim hs
  have hv := fun (K : ℕ) {h : ℝ} (hh : 0 < h) =>
    exists_complexModelValue hU hEx hD hs hsτ hρ hρseq hent Φ K hh
  let Ψ : ℕ → ℝ → ℝ := fun K h => if hh : 0 < h then Classical.choose (hv K hh) else 0
  have hΨ : ∀ K h, 0 < h → ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ (Ψ K h) := by
    intro K h hh
    simp only [Ψ, dite_eq_left hh]
    exact Classical.choose_spec (hv K hh)
  have hR : RealizedValues b E s T τ m (entranceLaw P μ s) Φ Ψ := by
    intro K h hh
    obtain ⟨⟨Ω', mΩ', 𝓖, Q, tseq, G, Kc, hM⟩, hall⟩ := hΨ K h hh
    exact ⟨Ω', mΩ', 𝓖, Q, tseq, G, Kc, hM, hall Ω' mΩ' 𝓖 Q tseq G Kc hM⟩
  have hcap := fun {h : ℝ} (hh : 0 < h) =>
    hCap b E np τ m T hD Ω mΩ P μ hlim s hs hsτ Φ h hh (fun K => Ψ K h) fun K => hΨ K h hh
  let Λ : ℝ → ℝ := fun h => if hh : 0 < h then Classical.choose (hcap hh) else 0
  have hΛ : ∀ h, 0 < h → Tendsto (fun K => Ψ K h) atTop (𝓝 (Λ h)) := by
    intro h hh
    simp only [Λ, dite_eq_left hh]
    exact Classical.choose_spec (hcap hh)
  obtain ⟨L, hL⟩ := hCut b E np τ m T hD Ω mΩ P μ hlim s hs hsτ Φ Ψ Λ hΨ hΛ
  refine ⟨Ψ, hR, Λ, hΛ, L, hL, SourcePins.tendsto_of_iterated_freq hΛ hL fun ε hε => ?_⟩
  refine ((hPA b E np τ m T hD Ω mΩ P μ hlim s hs hsτ Φ ε hε).and_eventually
    self_mem_nhdsWithin).mono fun h ⟨hK, hh⟩ => hK.mono fun K hKv => hKv _ (hΨ K h hh)

/-- **`ComplexSourceConstruction`** from the named steps, with the frequent physical
approximation. -/
theorem complexSourceConstruction_of_pins_freq (hTL : TransmissionLawContract)
    (hA1 : EntranceAtomic) (hA2 : SeqExtraction) (hU : ComplexFiniteUniqueness)
    (hEx : ComplexModelExists) (hCap : ComplexCapRemoval) (hCut : ComplexCutoffRemoval)
    (hPA : ComplexPhysicalApproximationFreq) (hTi : ComplexSourceTight) :
    ComplexSourceConstruction := by
  intro b E np τ m T hD
  obtain ⟨hb0, hb1, hE1, hE2, -, hτ, -⟩ := id hD
  obtain ⟨Ω, mΩ, P, μ, hlim, -⟩ := hTL.law b hb0 hb1 E hE1 hE2 _ isAbsorptionProfile_zero'
  have hval := fun {s : ℝ} (hs : 0 < s) (hsτ : ∀ j, s < τ j) Φ =>
    iterated_values_freq hA1 hA2 hU hEx hCap hCut hPA hD hlim hs hsτ Φ
  obtain ⟨s₀, hs₀, hs₀τ⟩ := exists_start hτ
  let μW : ℕ → ProbabilityMeasure (SourceData np) := fun W => ⟨physLaw b E T τ m W, inferInstance⟩
  obtain ⟨ν, hν⟩ := exists_weak_limit_of_tight μW (hTi b E np τ m T hD) fun Φ => by
    obtain ⟨-, -, -, -, L, -, hL⟩ := hval hs₀ hs₀τ Φ
    refine ⟨L, ?_⟩
    simpa only [μW, ProbabilityMeasure.coe_mk, integral_physLaw] using hL
  have hν' : ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
      Tendsto (physExpectation b E T τ m Φ) atTop (𝓝 (∫ y, Φ y ∂(ν : Measure (SourceData np)))) :=
    fun Φ => by simpa only [μW, ProbabilityMeasure.coe_mk, integral_physLaw] using hν Φ
  refine ⟨ν, ⟨inferInstance, hν'⟩, Ω, mΩ, P, μ, hlim, fun s hs hsτ Φ => ?_⟩
  obtain ⟨Ψ, hR, Λ, hΛ, L, hL, hphys⟩ := hval hs hsτ Φ
  have hLeq : L = ∫ y, Φ y ∂(ν : Measure (SourceData np)) := tendsto_nhds_unique hphys (hν' Φ)
  exact ⟨Ψ, hR, Λ, hΛ, hLeq ▸ hL⟩

/-- `ComplexSourceLawContract` from `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient`, `GaussianPoincare`, `ScalarRecursionContract`, `BornKExtension`,
`ComplexCutoffRemoval` and `ComplexPhysicalApproximationFreq`.
-/
theorem complexSourceLawContract_of_freq (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hP : GaussianPoincare)
    (hSR : ScalarRecursionContract) (hK : BornKExtension) (hCut : ComplexCutoffRemoval)
    (hPA : ComplexPhysicalApproximationFreq) : ComplexSourceLawContract :=
  ComplexSplit.complexSourceLawContract_of_construction hGA hLp hSR hMT
    (complexSourceConstruction_of_pins_freq
      (BlockBand.Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP)
      (BlockBand.SourceProcess.SourcePins.entranceAtomic_holds hMT hGA hLp hP)
      seqExtraction_holds ComplexSplit.complexFiniteUniqueness_holds
      (complexModelExists_of_kExtension hK) ComplexSplit.complexCapRemoval_holds hCut hPA
      (complexSourceTight_of_raw (RawTag.rawTagMoments_holds hGA hLp hSR hMT)))

end BlockBand.SourceProcess.ComplexFreq
