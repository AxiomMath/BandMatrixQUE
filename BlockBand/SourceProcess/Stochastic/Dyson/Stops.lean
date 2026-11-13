module

public import BlockBand.SourceProcess.Stochastic.Dyson.GapStop

/-!
# Hitting stops of continuous real processes

Localization for the semimartingale clause of `DysonBrownianMotion`: the norm and gap stops used
to bound the stopped Dyson state, as in the relative localization lemma.

For `f : ℝ≥0 → Ω → ℝ` with continuous paths, `hitStop f c ω = inf {v | f v ω ≤ c}` (`⊤` if empty):
* `isStoppingTime_hitStop`: a stopping time when each `f v` is `𝓕_v`-measurable;
* `lt_of_lt_hitStop`: before the stop `f > c`; `le_of_le_hitStop`: up to and including the stop
  (at positive times, or if `f 0 > c`) `c ≤ f`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

/-- First time `f · ω ≤ c`. -/
def hitStop {Ω : Type*} (f : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ v ∈ {v : ℝ≥0 | f v ω ≤ c}, (v : WithTop ℝ≥0)

theorem hitStop_le_iff {Ω : Type*} {f : ℝ≥0 → Ω → ℝ} {ω : Ω} (hf : Continuous fun v => f v ω)
    (c : ℝ) (u : ℝ≥0) : hitStop f c ω ≤ u ↔ ∃ v, v ≤ u ∧ f v ω ≤ c := by
  rw [hitStop, iInf_coe_le_iff_of_isClosed (isClosed_le hf continuous_const)]
  exact ⟨fun ⟨v, hv, hvu⟩ => ⟨v, hvu, hv⟩, fun ⟨v, hvu, hv⟩ => ⟨v, hv, hvu⟩⟩

theorem isStoppingTime_hitStop {Ω : Type*} [MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {f : ℝ≥0 → Ω → ℝ}
    (hf : ∀ ω, Continuous fun v => f v ω) (hm : ∀ v, Measurable[𝓕 v] (f v)) (c : ℝ) :
    IsStoppingTime 𝓕 (hitStop f c) := by
  intro u
  simp_rw [hitStop_le_iff (hf _)]
  exact measurableSet_exists_le_of_continuous (m := 𝓕 u) f hf u
    (fun v hv => (hm v).mono (𝓕.mono hv) le_rfl) c

theorem lt_of_lt_hitStop {Ω : Type*} {f : ℝ≥0 → Ω → ℝ} {c : ℝ} {ω : Ω} {v : ℝ≥0}
    (hv : (v : WithTop ℝ≥0) < hitStop f c ω) : c < f v ω := by
  by_contra h
  exact absurd (iInf₂_le (f := fun (v : ℝ≥0) (_ : v ∈ {v : ℝ≥0 | f v ω ≤ c}) =>
    (v : WithTop ℝ≥0)) v (not_lt.mp h)) (not_le.mpr hv)

theorem le_of_le_hitStop {Ω : Type*} {f : ℝ≥0 → Ω → ℝ} {c : ℝ} {ω : Ω}
    (hf : Continuous fun v => f v ω) {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ hitStop f c ω)
    (h0 : 0 < v ∨ c < f 0 ω) : c ≤ f v ω := by
  rcases hv.lt_or_eq with hlt | heq
  · exact (lt_of_lt_hitStop hlt).le
  rcases (zero_le : (0 : ℝ≥0) ≤ v).lt_or_eq with hpos | hzero
  · -- left limit at `v > 0`
    have hev : ∀ᶠ w in 𝓝[<] v, c ≤ f w ω := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (lt_of_lt_hitStop (heq ▸ WithTop.coe_lt_coe.mpr hw)).le
    have : (𝓝[<] v).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
    exact ge_of_tendsto ((hf.tendsto v).mono_left nhdsWithin_le_nhds) hev
  · subst hzero
    rcases h0 with h | h
    · exact absurd h (lt_irrefl 0)
    · exact h.le

end BlockBand.SourceProcess.Stochastic.Dyson
