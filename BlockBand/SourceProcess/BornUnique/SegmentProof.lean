module

public import BlockBand.SourceProcess.BornUnique.Stopped

/-!
# `BornSegmentStep` from `BornStoppedLaw` and `BornRestart`

Restarting a born solution at the `𝓖₀`-measurable time `α` (`BornRestart`) gives a born solution
with births shifted by `α`, and the stopped law from time `0` (`BornStoppedLaw`) then determines
the law at the next time `α'`. Together they give `BornSegmentStep` (`bornSegmentStep_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

theorem birthSum_shift {c F : Type*} [Fintype F] (j : F → GramState c) (x : F → ℝ)
    (a : ℝ≥0) (u : ℝ≥0) :
    birthSum j (fun f => x f - a) (u : ℝ) = birthSum j x ((a + u : ℝ≥0) : ℝ) := by
  unfold birthSum
  refine Finset.sum_congr rfl fun f _ => ?_
  exact if_congr (by rw [NNReal.coe_add, sub_le_iff_le_add']) rfl rfl

theorem bornCont_restart {Ω c F : Type*} [Fintype F]
    (j : F → GramState c) (β : Ω → F → ℝ) (α : (F → ℝ) → ℝ≥0) {G H : ℝ≥0 → Ω → GramState c} {ω : Ω}
    (hω : ∀ u, H u ω = G (α (β ω) + u) ω) (u : ℝ≥0) :
    H u ω - birthSum j (fun f => β ω f - α (β ω)) (u : ℝ) =
      G (α (β ω) + u) ω - birthSum j (β ω) ((α (β ω) + u : ℝ≥0) : ℝ) := by
  rw [hω u, birthSum_shift]

/-- **`BornSegmentStep` from the stopped law and the restart.** -/
theorem bornSegmentStep_of (hSt : BornStoppedLaw) (hR : BornRestart) : BornSegmentStep := by
  intro c F _ _ _ D0 D hD0 hD j α α' hα hα' hle hnb Ω m 𝓖 Q β G hQ hβ hG
    Ω' m' 𝓖' Q' β' G' hQ' hβ' hG' h0
  obtain ⟨𝓗, H, hβH, hH, hHG⟩ := hR c F D0 D j α hα Ω m 𝓖 Q β G hQ hβ hG
  obtain ⟨𝓗', H', hβH', hH', hHG'⟩ := hR c F D0 D j α hα Ω' m' 𝓖' Q' β' G' hQ' hβ' hG'
  have hb : Measurable fun (x : F → ℝ) (f : F) => x f - α x :=
    measurable_pi_iff.2 fun f => (measurable_pi_apply f).sub (measurable_coe_nnreal_real.comp hα)
  have hnb' : ∀ (x : F → ℝ) (f : F), x f - α x ≤ 0 ∨ ((α' x - α x : ℝ≥0) : ℝ) ≤ x f - α x := by
    intro x f
    rcases hnb x f with h | h
    · exact Or.inl (sub_nonpos.2 h)
    · refine Or.inr ?_
      rw [NNReal.coe_sub (hle x)]
      linarith
  have e0 : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} {β₁ : Ω₁ → F → ℝ}
      {G₁ H₁ : ℝ≥0 → Ω₁ → GramState c}, (∀ᵐ ω ∂Q₁, ∀ u, H₁ u ω = G₁ (α (β₁ ω) + u) ω) →
      (fun ω => (β₁ ω, bornCont j (fun ω => (fun x f => x f - α x) (β₁ ω)) H₁ 0 ω)) =ᵐ[Q₁]
        fun ω => (β₁ ω, bornCont j β₁ G₁ (α (β₁ ω)) ω) := by
    intro _ _ _ β₁ G₁ H₁ hHG₁
    filter_upwards [hHG₁] with ω hω
    simp only [bornCont]
    rw [bornCont_restart j β₁ α hω, add_zero]
  have e1 : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} {β₁ : Ω₁ → F → ℝ}
      {G₁ H₁ : ℝ≥0 → Ω₁ → GramState c}, (∀ᵐ ω ∂Q₁, ∀ u, H₁ u ω = G₁ (α (β₁ ω) + u) ω) →
      (fun ω => (β₁ ω, bornCont j (fun ω => (fun x f => x f - α x) (β₁ ω)) H₁
        ((fun x => α' x - α x) (β₁ ω)) ω)) =ᵐ[Q₁]
        fun ω => (β₁ ω, bornCont j β₁ G₁ (α' (β₁ ω)) ω) := by
    intro _ _ _ β₁ G₁ H₁ hHG₁
    filter_upwards [hHG₁] with ω hω
    simp only [bornCont]
    rw [bornCont_restart j β₁ α hω, add_tsub_cancel_of_le (hle _)]
  have h1 := h0
  rw [← Measure.map_congr (e0 hHG), ← Measure.map_congr (e0 hHG')] at h1
  have key := hSt c F (F → ℝ) D0 D hD0 hD j (fun x f => x f - α x) (fun x => α' x - α x) hb
    (hα'.sub hα) hnb' Ω m 𝓗 Q β H hQ hβH hH Ω' m' 𝓗' Q' β' H' hQ' hβH' hH' h1
  rw [Measure.map_congr (e1 hHG), Measure.map_congr (e1 hHG')] at key
  exact key

end BlockBand.SourceProcess.BornUnique
