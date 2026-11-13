module

public import BlockBand.SourceProcess.ComplexConstruct.Interface

/-!
# `ComplexPhysicalApproximation`, restated frequently in `h`

`ComplexPhysicalApproximationFreq` asks the physical approximation only for `h` frequently near `0`
and caps `K` frequently large; it follows from the every-`h` form
(`complexPhysicalApproximationFreq_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexFreq

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct

/-- **The physical approximation, frequently in `h`**: for every `ε > 0`,
frequently as `h ↓ 0` and then frequently in the cap `K`, every complex model value `v` at
`(h, K)` with entrance `μ(s)` is eventually in `W` within `ε` of the width-`W` expectation. It is
proved from the input hypotheses and `KolmogorovConjugate` as
`PhysApprox.complexPhysicalApproximationFreq_holds`. -/
def ComplexPhysicalApproximationFreq : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∀ ε : ℝ, 0 < ε → ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop, ∀ v : ℝ,
    ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ v →
    ∀ᶠ W in atTop, |physExpectation b E T τ m Φ W - v| ≤ ε

/-- The every-`h` form implies the frequent form. -/
theorem complexPhysicalApproximationFreq_of (h : ComplexPhysicalApproximation) :
    ComplexPhysicalApproximationFreq := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hsτ Φ ε hε
  obtain ⟨h₀, hh₀, hK⟩ := h b E np τ m T hD Ω mΩ P μ hlim s hs hsτ Φ ε hε
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x < h₀ :=
    Eventually.and self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds hh₀))
  refine hev.frequently.mono fun x ⟨hx0, hxh⟩ => ?_
  obtain ⟨K₀, hK₀⟩ := hK x hx0 hxh
  exact (eventually_ge_atTop K₀).frequently.mono fun K hKle => hK₀ K hKle

end BlockBand.SourceProcess.ComplexFreq
