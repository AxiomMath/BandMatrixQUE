module

public import BlockBand.SourceProcess.BornStopped.Pin
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.Main

/-!
# Gram-law uniqueness up to a horizon from an extension property

`GramHorizonExtension` states that for every solution `G` of the Gram martingale problem up to the
deterministic horizon `r`, some global solution `Ĝ` (`IsGramMartingaleSolution`, possibly on
another filtered probability space) has the same laws as `G` at times `0` and `r`. A natural
construction keeps `G` on `[0, r]` and continues it after `r` by an ambient strong solution
(`SourceSDE.finiteSourceWellPosed_holds`, `GramUniqueness.ambient_isGramMartingaleSolution`)
started from a measurable factor realization of `G_r`.

`gramHorizonLaw_of_extension` derives `GramHorizonLaw` from this property and global Gram-law
uniqueness (`GramUniqueness.gramLaw_eq_of_initial`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal

/-- **Extension of a horizon solution to a global solution, in law at times `0` and `r`.**
This is stated as a hypothesis. -/
def GramHorizonExtension : Prop :=
  ∀ (c : Type) [Fintype c] [DecidableEq c] (D0 : ℝ) (D : Matrix c c ℂ), 0 < D0 → IsSignature D →
  ∀ r : ℝ≥0,
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ),
    IsProbabilityMeasure Q → IsGramHorizonSolution Q 𝓖 D0 D r G →
  ∃ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓗 : Filtration ℝ≥0 m₁) (Q₁ : Measure Ω₁)
    (H : ℝ≥0 → Ω₁ → Matrix c c ℂ × Matrix c c ℂ),
    IsProbabilityMeasure Q₁ ∧ IsGramMartingaleSolution Q₁ 𝓗 D0 D H ∧
    Q₁.map (H 0) = Q.map (G 0) ∧ Q₁.map (H r) = Q.map (G r)

/-- **`GramHorizonLaw` from `GramHorizonExtension`**, using global Gram-law uniqueness
`gramLaw_eq_of_initial`. -/
theorem gramHorizonLaw_of_extension (hE : GramHorizonExtension) : GramHorizonLaw := by
  intro c _ _ D0 D hD0 hD r Ω m 𝓖 Q G hQ hG Ω' m' 𝓖' Q' G' hQ' hG' h0
  obtain ⟨Ω₁, m₁, 𝓗₁, Q₁, H₁, hQ₁, hH₁, h₁0, h₁r⟩ := hE c D0 D hD0 hD r Ω m 𝓖 Q G hQ hG
  obtain ⟨Ω₂, m₂, 𝓗₂, Q₂, H₂, hQ₂, hH₂, h₂0, h₂r⟩ := hE c D0 D hD0 hD r Ω' m' 𝓖' Q' G' hQ' hG'
  have hp := gramLaw_eq_of_initial hD0 hD hH₁ hH₂ (by rw [h₁0, h₂0, h0])
  rw [← h₁r, ← h₂r]
  have e : ∀ {Ω₃ : Type} (H : ℝ≥0 → Ω₃ → Matrix c c ℂ × Matrix c c ℂ),
      H r = (fun f : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ => f r) ∘ (fun ω t => H t ω) :=
    fun _ => rfl
  rw [e H₁, e H₂, ← Measure.map_map (measurable_pi_apply r) (measurable_path hH₁),
    ← Measure.map_map (measurable_pi_apply r) (measurable_path hH₂), hp]

end BlockBand.SourceProcess.BornStopped
