module

public import BlockBand.SourceProcess.RankFree.LocMartShift
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.Pathwise

/-!
# Increments after a stopping time with an `𝓕_θ`-measurable weight: measurability

* `shiftProc Y θ ξ t = ξ (Y_t − Y_{t∧θ})`; `onAfter θ ξ f t = 1{θ < t} ξ f_t`.
* `stronglyMeasurable_shiftProc`, `isStronglyProgressive_shiftProc`,
  `isStronglyProgressive_onAfter`: adaptedness and progressive measurability, by the device of
  `LocMart.shift`: on `[0, i]`, `ξ` may be replaced by the `𝓖_i`-measurable
  `1{θ ≤ i} ξ` (`stronglyMeasurable_ite_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `ξ (Y_t − Y_{t∧θ})`. -/
def shiftProc (Y : ℝ≥0 → Ω → E) (θ : Ω → WithTop ℝ≥0) (ξ : Ω → ℝ) (t : ℝ≥0) (x : Ω) : E :=
  ξ x • (Y t x - stoppedProcess Y θ t x)

/-- `1{θ < t} ξ f_t`. -/
def onAfter (θ : Ω → WithTop ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → E) (t : ℝ≥0) (x : Ω) : E :=
  if θ x < (t : WithTop ℝ≥0) then ξ x • f t x else 0

variable [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [MeasurableSpace Ω] in
theorem shiftProc_eq_gate (Y : ℝ≥0 → Ω → E) (θ : Ω → WithTop ℝ≥0) (ξ : Ω → ℝ) {i t : ℝ≥0}
    (hti : t ≤ i) (x : Ω) :
    shiftProc Y θ ξ t x =
      (if θ x ≤ (i : WithTop ℝ≥0) then ξ x else 0) • (Y t x - stoppedProcess Y θ t x) := by
  unfold shiftProc
  split_ifs with h
  · rfl
  · have hle : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ θ x :=
      (WithTop.coe_le_coe.2 hti).trans (not_le.1 h).le
    rw [stoppedProcess_eq_of_le hle, sub_self, smul_zero, smul_zero]

theorem stronglyMeasurable_shiftProc {Y : ℝ≥0 → Ω → E} (hY : IsStronglyProgressive 𝓖 Y)
    {θ : Ω → WithTop ℝ≥0} (hθ : IsStoppingTime 𝓖 θ) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[hθ.measurableSpace] ξ) (t : ℝ≥0) :
    StronglyMeasurable[𝓖 t] (shiftProc Y θ ξ t) := by
  have e : shiftProc Y θ ξ t = fun x =>
      (if θ x ≤ (t : WithTop ℝ≥0) then ξ x else 0) • (Y t x - stoppedProcess Y θ t x) :=
    funext fun x => shiftProc_eq_gate Y θ ξ le_rfl x
  rw [e]
  exact (stronglyMeasurable_ite_le hθ hξ t).smul
    ((hY.stronglyAdapted t).sub ((hY.stoppedProcess hθ).stronglyAdapted t))

theorem isStronglyProgressive_shiftProc {Y : ℝ≥0 → Ω → E} (hY : IsStronglyProgressive 𝓖 Y)
    {θ : Ω → WithTop ℝ≥0} (hθ : IsStoppingTime 𝓖 θ) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[hθ.measurableSpace] ξ) :
    IsStronglyProgressive 𝓖 (shiftProc Y θ ξ) := by
  intro i
  convert ((stronglyMeasurable_ite_le hθ hξ i).comp_measurable measurable_snd).smul
    ((hY i).sub ((hY.stoppedProcess hθ) i)) using 1
  funext p
  exact shiftProc_eq_gate Y θ ξ (mem_Iic.1 p.1.2) p.2

omit [MeasurableSpace Ω] in
theorem onAfter_eq_gate (θ : Ω → WithTop ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → E) {i t : ℝ≥0}
    (hti : t ≤ i) (x : Ω) :
    onAfter θ ξ f t x =
      (if θ x ≤ (i : WithTop ℝ≥0) then ξ x else 0) • (f t x - switchAfter θ f t x) := by
  unfold onAfter switchAfter
  by_cases h : θ x < (t : WithTop ℝ≥0)
  · have h1 : θ x ≤ (i : WithTop ℝ≥0) := h.le.trans (WithTop.coe_le_coe.2 hti)
    simp only [h, ↓reduceIte, h1, not_le.2 h, sub_zero]
  · simp only [h, ↓reduceIte, not_lt.1 h, sub_self, smul_zero]

theorem isStronglyProgressive_onAfter {f : ℝ≥0 → Ω → E} (hf : IsStronglyProgressive 𝓖 f)
    {θ : Ω → WithTop ℝ≥0} (hθ : IsStoppingTime 𝓖 θ) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[hθ.measurableSpace] ξ) :
    IsStronglyProgressive 𝓖 (onAfter θ ξ f) := by
  intro i
  convert ((stronglyMeasurable_ite_le hθ hξ i).comp_measurable measurable_snd).smul
    ((hf i).sub ((isStronglyProgressive_switchAfter hf hθ) i)) using 1
  funext p
  exact onAfter_eq_gate θ ξ f (mem_Iic.1 p.1.2) p.2

end BlockBand.SourceProcess.CoupledFrames
