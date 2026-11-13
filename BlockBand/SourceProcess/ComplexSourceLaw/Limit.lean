module

public import BlockBand.SourceProcess.ComplexSourceLaw.Interface

/-!
# The `limit` field of the complex source law from uniqueness and construction

Under `ComplexFiniteUniqueness`, values realized by some complex finite model are model values
(`complexModelValue_of_realized`); with `ComplexSourceConstruction` this gives the `limit` field
of `ComplexSourceLawContract` (`limit_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

/-- Realized values are model values once finite uniqueness holds. -/
theorem complexModelValue_of_realized (hU : ComplexFiniteUniqueness) {b E : ℝ} {np : ℕ}
    {τ m : Fin np → ℝ} {T : ℝ} (hD : ComplexSourceLawDomain b E τ m T) {s : ℝ} (hs : 0 < s)
    (hsτ : ∀ j, s < τ j) {entrance : Measure (Measure unitInterval)}
    {Φ : BoundedContinuousFunction (SourceData np) ℝ} {Ψ : ℕ → ℝ → ℝ}
    (hΨ : RealizedValues b E s T τ m entrance Φ Ψ) (K : ℕ) {h : ℝ} (hh : 0 < h) :
    ComplexModelValue b E s T τ m h K entrance Φ (Ψ K h) := by
  obtain ⟨Ω, mΩ, 𝓖, Q, tseq, G, Kc, hM, hv⟩ := hΨ K h hh
  refine ⟨⟨Ω, mΩ, 𝓖, Q, tseq, G, Kc, hM⟩, ?_⟩
  intro Ω' mΩ' 𝓖' Q' tseq' G' Kc' hM'
  have := hU b E np τ m T hD s hs hsτ h hh K entrance Φ Ω' mΩ' 𝓖' Q' tseq' G' Kc' hM'
    Ω mΩ 𝓖 Q tseq G Kc hM
  rw [← hv, ← this]
  rfl

/-- **The `ComplexSourceLawContract.limit`** from finite uniqueness and the construction. -/
theorem limit_of (hU : ComplexFiniteUniqueness) (hC : ComplexSourceConstruction) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (np : ℕ) (τ m : Fin np → ℝ), Function.Injective τ → (∀ j, 0 < τ j) → (∀ j, 0 ≤ m j) →
    ∀ T : ℝ, (∀ j, τ j < T) →
      ∃ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ ∧
          ∀ s : ℝ, 0 < s → (∀ j, s < τ j) →
          ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
            ∃ Ψ : ℕ → ℝ → ℝ,
              (∀ K h, 0 < h → ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ (Ψ K h)) ∧
              ∃ Λ : ℝ → ℝ, (∀ h, 0 < h → Tendsto (fun K => Ψ K h) atTop (𝓝 (Λ h))) ∧
                Tendsto Λ (𝓝[>] 0) (𝓝 (∫ y, Φ y ∂ν)) := by
  intro b hb0 hb1 E hE0 hE1 np τ m hinj hτ hm T hT
  have hD : ComplexSourceLawDomain b E τ m T := ⟨hb0, hb1, hE0, hE1, hinj, hτ, hm, hT⟩
  obtain ⟨ν, hν, Ω, mΩ, P, μ, hP, hcons⟩ := hC b E np τ m T hD
  refine ⟨ν, hν, Ω, mΩ, P, μ, hP, fun s hs hsτ Φ => ?_⟩
  obtain ⟨Ψ, hΨ, Λ, hΛ⟩ := hcons s hs hsτ Φ
  exact ⟨Ψ, fun K h hh => complexModelValue_of_realized hU hD hs hsτ hΨ K hh, Λ, hΛ⟩

end BlockBand.SourceProcess.ComplexSourceLaw
