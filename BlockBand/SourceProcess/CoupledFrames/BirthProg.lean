module

public import BlockBand.SourceProcess.RankFree.BirthProcess
public import BlockBand.SourceProcess.RankFree.LocMartShift

/-!
# Progressive measurability of births at `𝓖₀`-measurable times

`isStronglyProgressive_ite_le`: for a `𝓖₀`-measurable time `τ` and an `𝓕_τ`-measurable `f`, the
process `t ↦ 1{τ ≤ t} f` is progressively measurable: on `[0, i] × Ω` it is
`1{τ(x) ≤ s} · 1{τ ≤ i} f(x)`, a product of a `Borel ⊗ 𝓖_i`-measurable indicator (`τ` is
`𝓖_i`-measurable) and a `𝓖_i`-measurable function (`stronglyMeasurable_ite_le`).
`isStronglyProgressive_frameBirthJump`: the shared-birth jump process `J_b` is progressive.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.RankFree BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {E : Type*} [TopologicalSpace E] [Zero E]

theorem isStronglyProgressive_ite_le {τ : Ω → ℝ≥0} (hτ0 : Measurable[𝓖 0] τ)
    (hτ : IsStoppingTime 𝓖 (fun x => ((τ x : ℝ≥0) : WithTop ℝ≥0))) {f : Ω → E}
    (hf : StronglyMeasurable[hτ.measurableSpace] f) :
    IsStronglyProgressive 𝓖 (fun t x => if τ x ≤ t then f x else 0) := by
  classical
  intro i
  have hg := stronglyMeasurable_ite_le hτ hf i
  have hS : MeasurableSet[Subtype.instMeasurableSpace.prod (𝓖 i)]
      {p : Set.Iic i × Ω | τ p.2 ≤ (p.1 : ℝ≥0)} :=
    measurableSet_le ((hτ0.mono (𝓖.mono zero_le) le_rfl).comp measurable_snd)
      (measurable_subtype_coe.comp measurable_fst)
  convert StronglyMeasurable.ite hS (hg.comp_measurable measurable_snd)
    (stronglyMeasurable_const (b := (0 : E))) using 1
  · funext p
    simp only [Function.comp_apply]
    by_cases h : τ p.2 ≤ (p.1 : ℝ≥0)
    · have h' : ((τ p.2 : ℝ≥0) : WithTop ℝ≥0) ≤ ((i : ℝ≥0) : WithTop ℝ≥0) :=
        WithTop.coe_le_coe.2 (h.trans (mem_Iic.1 p.1.2))
      simp only [h, ↓reduceIte, h']
    · simp only [h, ↓reduceIte]
  · exact Classical.decPred _

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c] {nb : ℕ}

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

omit [DecidableEq ι] [Fintype c] in
theorem isStronglyProgressive_frameBirthJump {τ : Fin nb → Ω → ℝ≥0}
    (hτ0 : ∀ k, Measurable[𝓖 0] (τ k))
    (hτ : ∀ k, IsStoppingTime 𝓖 (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))) (col : Fin nb → c)
    {w : Fin nb → Ω → ι → ℂ} (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k)) :
    IsStronglyProgressive 𝓖 (frameBirthJump τ col w) := by
  have e : frameBirthJump τ col w = fun t x => ∑ k, (fun t x =>
      if τ k x ≤ t then birthCLM (col k) (w k x) else 0) t x := by
    funext t x
    rw [frameBirthJump_eq]
    rfl
  rw [e]
  intro i
  exact Finset.stronglyMeasurable_fun_sum _ fun k _ => isStronglyProgressive_ite_le (hτ0 k) (hτ k)
    ((birthCLM (col k)).continuous.comp_stronglyMeasurable (hw k)) i

end BlockBand.SourceProcess.CoupledFrames
