module

public import BlockBand.SourceProcess.ComplexConstruct.Interface
public import BlockBand.SourceProcess.SourceProcessLaw.Assembly

/-!
# The iterated model values at a fixed start and test

`iterated_values`: for a homogeneous transmission limit `(P, μ)`, a source-free start `s` and a
test `Φ`, the hypotheses give model values `Ψ K h` realized by complex finite models with entrance
`μ(s)` (`RealizedValues`), their limits `Λ h` as `K → ∞`, and a number `L` with `Λ → L` along
`𝓝[>] 0` and `E_W Φ → L` for the finite-width expectations. The entrance is the law of a random
transmission sequence (`entrance_sequence` from `EntranceAtomic` + `SeqExtraction`);
`ComplexModelExists` + `ComplexFiniteUniqueness` give `ComplexModelValue` at every `(K, h)`;
`ComplexCapRemoval`, `ComplexCutoffRemoval` give `Λ`, `L`; `tendsto_of_iterated` with
`ComplexPhysicalApproximation` gives `E_W Φ → L`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal

/-- Existence and uniqueness give a complex model value at every `(K, h)`. -/
theorem exists_complexModelValue (hU : ComplexFiniteUniqueness) (hEx : ComplexModelExists)
    {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T : ℝ} (hD : ComplexSourceLawDomain b E τ m T)
    {s : ℝ} (hs : 0 < s) (hsτ : ∀ j, s < τ j) {ρ : Measure (ℕ → ℝ)} (hρ : IsProbabilityMeasure ρ)
    (hρseq : ∀ᵐ t ∂ρ, IsTransmissionSequence t) {entrance : Measure (Measure unitInterval)}
    (hent : ρ.map seqTraceMeasure = entrance) (Φ : BoundedContinuousFunction (SourceData np) ℝ)
    (K : ℕ) {h : ℝ} (hh : 0 < h) : ∃ v : ℝ, ComplexModelValue b E s T τ m h K entrance Φ v := by
  obtain ⟨Ω, mΩ, 𝓖, Q, tseq, G, Kc, hM⟩ := hEx b E np τ m T hD s hs hsτ ρ hρ hρseq h K hh
  rw [hent] at hM
  refine ⟨modelExpectation K s T Q G Kc Φ, ⟨Ω, mΩ, 𝓖, Q, tseq, G, Kc, hM⟩, ?_⟩
  intro Ω' mΩ' 𝓖' Q' tseq' G' Kc' hM'
  exact (hU b E np τ m T hD s hs hsτ h hh K entrance Φ Ω' mΩ' 𝓖' Q' tseq' G' Kc' hM' Ω mΩ 𝓖 Q
    tseq G Kc hM)

/-- **Iterated model values at a fixed start and test.** -/
theorem iterated_values (hA1 : EntranceAtomic) (hA2 : SeqExtraction)
    (hU : ComplexFiniteUniqueness) (hEx : ComplexModelExists) (hCap : ComplexCapRemoval)
    (hCut : ComplexCutoffRemoval) (hPA : ComplexPhysicalApproximation)
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
  refine ⟨Ψ, hR, Λ, hΛ, L, hL, tendsto_of_iterated hΛ hL fun ε hε => ?_⟩
  obtain ⟨h₀, hh₀, hK⟩ := hPA b E np τ m T hD Ω mΩ P μ hlim s hs hsτ Φ ε hε
  refine ⟨h₀, hh₀, fun h hh hlt => ?_⟩
  obtain ⟨K₀, hK₀⟩ := hK h hh hlt
  exact ⟨K₀, fun K hKle => hK₀ K hKle _ (hΨ K h hh)⟩

end BlockBand.SourceProcess.ComplexConstruct
