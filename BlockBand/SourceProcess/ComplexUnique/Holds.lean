module

public import BlockBand.SourceProcess.ComplexUnique.SegLaw
public import BlockBand.SourceProcess.ComplexSplit.Interface

/-!
# `ComplexSplit.JointSegmentLaw` holds

Finite uniqueness follows by adding the linear martingale equation of `𝒦` to the smooth Gram
charts; the restart is at a deterministic time.

**`jointSegmentLaw_holds : JointSegmentLaw`**, with no hypotheses: with `h = t - a`, each model's
restarted real joint process solves the joint real martingale problem in `{t < h}`
(`segModel`), and `segment_law` gives the equality of the laws at `a + h = t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open MeasureTheory
open BlockBand.SourceProcess BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.ComplexSplit
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal

/-- **`JointSegmentLaw` holds.** -/
theorem jointSegmentLaw_holds : JointSegmentLaw := by
  intro b E np τ m T hdom s _ _ K Ω₁ m₁ 𝓖₁ Q₁ G₁ K₁ hQ₁ hG₁ hK₁ Ω₂ m₂ 𝓖₂ Q₂ G₂ K₂ hQ₂ hG₂ hK₂
    a t hat hnb h0
  obtain ⟨hb, -, hE1, hE2, -⟩ := hdom
  have hth : t = a + (t - a) := (add_tsub_cancel_of_le hat).symm
  have hnb' : ∀ j, τ j - s ≤ a ∨ ((a + (t - a) : ℝ≥0) : ℝ) < τ j - s := by
    intro j
    by_cases h1 : τ j - s ≤ a
    · exact Or.inl h1
    · right; rw [← hth]
      exact not_le.1 fun h2 => hnb j ⟨not_le.1 h1, h2⟩
  obtain ⟨hY₁, ht₁, hz₁, hf₁, hr₁⟩ := segModel (Ω := Ω₁) (v := fun j => dStar b * m j)
    hb hE1 hE2 hG₁ hK₁ hnb'
  obtain ⟨hY₂, ht₂, hz₂, hf₂, hr₂⟩ := segModel (Ω := Ω₂) (v := fun j => dStar b * m j)
    hb hE1 hE2 hG₂ hK₂ hnb'
  have h := segment_law (transportD0_pos' hb hE1 hE2).le (isSignature_srcSignature K (Fin np))
    hY₁ ht₁ hz₁ hf₁ hr₁
    (measurable_GK ((hG₁.adapted a).mono (𝓖₁.le a)) ((hK₁.adapted a).mono (𝓖₁.le a)))
    hY₂ ht₂ hz₂ hf₂ hr₂
    (measurable_GK ((hG₂.adapted a).mono (𝓖₂.le a)) ((hK₂.adapted a).mono (𝓖₂.le a))) h0
  rwa [← hth] at h

end BlockBand.SourceProcess.ComplexUnique
