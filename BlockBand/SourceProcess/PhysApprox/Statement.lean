module

public import BlockBand.SourceProcess.ComplexConstruct.Interface

/-!
# The physical approximation in the "frequently in `h`" form

`ComplexPhysicalApproximationFreq`: frequently as `h ↓ 0` and frequently in `K`, every complex
model value at `(h, K)` is eventually within `ε` of the physical expectation.
`complexPhysicalApproximationFreq_of`: it follows from `ComplexPhysicalApproximation`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct

/-- **The physical approximation, frequently in `h` and `K`.** -/
def ComplexPhysicalApproximationFreq : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop, ∀ v : ℝ,
    ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ v →
    ∀ᶠ W in atTop, |physExpectation b E T τ m Φ W - v| ≤ ε

/-- The every-`h` form `ComplexPhysicalApproximation` implies the frequent form. -/
theorem complexPhysicalApproximationFreq_of (h : ComplexPhysicalApproximation) :
    ComplexPhysicalApproximationFreq := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ ε hε
  obtain ⟨h₀, hh₀, hK⟩ := h b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ ε hε
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x < h₀ :=
    Eventually.and self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hh₀))
  refine (hev.mono fun x hx => ?_).frequently
  obtain ⟨K₀, hK₀⟩ := hK x hx.1 hx.2
  exact (eventually_atTop.2 ⟨K₀, hK₀⟩).frequently

end BlockBand.SourceProcess.PhysApprox
