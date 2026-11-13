module

public import BlockBand.SourceProcess.BornRestart.Hit

/-!
# The restarted process and its elementary properties

Data of `BornUnique.BornRestart`: a born Gram
solution `G` on `(Ω, 𝓖, Q)` with `𝓖₀`-measurable births `β`, and a measurable time `α` of the
births. Put `a = α ∘ β`.

* `rsH`: `H_u = lim_k G(a_k + u)` with `a_k = dyU k a ↓ a`, taken in real coordinates
  (`limUnder`). It is `𝓗_u`-measurable (`stronglyMeasurable_rsH`), and on every path with
  continuous `G - J` it equals `G(a + u)` for every `u` (`rsH_eq`), by right-continuity.
* `rsBirth`: the shifted births `β - a`, which are `𝓗₀`-measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] {Ω : Type} {m : MeasurableSpace Ω}

/-- The restarted process `H_u = lim_k G(a_k + u)` (real coordinates). -/
def rsH (α : (F → ℝ) → ℝ≥0) (β : Ω → F → ℝ) (G : ℝ≥0 → Ω → GramState c) (u : ℝ≥0) (ω : Ω) :
    GramState c :=
  fromGramReal (limUnder atTop fun k => toGramReal (G (dyU k (α (β ω)) + u) ω))

/-- The shifted births `β - α(β)`. -/
def rsBirth (α : (F → ℝ) → ℝ≥0) (β : Ω → F → ℝ) (ω : Ω) : F → ℝ := fun f => β ω f - α (β ω)

variable {j : F → GramState c} {α : (F → ℝ) → ℝ≥0} {β : Ω → F → ℝ} {G : ℝ≥0 → Ω → GramState c}

omit [Fintype c] [DecidableEq c] in
/-- A born path is right-continuous. -/
theorem continuousWithinAt_path {ω : Ω}
    (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ)) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => G u ω) (Ici t) t := by
  have hJ : ∀ᶠ u : ℝ≥0 in 𝓝[≥] t, birthSum j (β ω) (u : ℝ) = birthSum j (β ω) (t : ℝ) :=
    ((NNReal.continuous_coe.continuousWithinAt (s := Ici t) (x := t)).tendsto_nhdsWithin
      (t := Ici (t : ℝ)) (fun x hx => NNReal.coe_le_coe.2 hx)).eventually
      (birthSum_eventually_eq j (β ω) t)
  have hJc : ContinuousWithinAt (fun u : ℝ≥0 => birthSum j (β ω) (u : ℝ)) (Ici t) t :=
    continuousWithinAt_const.congr_of_eventuallyEq hJ rfl
  exact (hc.continuousWithinAt.add hJc).congr (fun u _ => (sub_add_cancel _ _).symm)
    (sub_add_cancel _ _).symm

/-- **On every born path the restarted process is `G(a + ·)`.** -/
theorem rsH_eq {ω : Ω} (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ)) (u : ℝ≥0) :
    rsH α β G u ω = G (α (β ω) + u) ω := by
  have ht : Tendsto (fun k => dyU k (α (β ω)) + u) atTop (𝓝[≥] (α (β ω) + u)) :=
    tendsto_nhdsWithin_iff.2 ⟨(tendsto_dyU _).add_const u,
      Eventually.of_forall fun k => add_le_add (lt_dyU k _).le le_rfl⟩
  have hlim : Tendsto (fun k => toGramReal (G (dyU k (α (β ω)) + u) ω)) atTop
      (𝓝 (toGramReal (G (α (β ω) + u) ω))) := (continuous_toGramReal.continuousAt.tendsto.comp
    ((continuousWithinAt_path hc (α (β ω) + u)).tendsto.comp ht))
  rw [rsH, hlim.limUnder_eq, fromGramReal_toGramReal]

theorem rsH_shift {ω : Ω} (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ)) :
    (fun u => rsH α β G u ω) = fun u => G (α (β ω) + u) ω := funext (rsH_eq hc)

omit [Fintype c] [DecidableEq c] in
theorem birthSum_rsBirth (ω : Ω) (u : ℝ≥0) :
    birthSum j (rsBirth α β ω) (u : ℝ) = birthSum j (β ω) ((α (β ω) + u : ℝ≥0) : ℝ) :=
  birthSum_shift j (β ω) (α (β ω)) u

theorem continuous_rsH {ω : Ω} (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ)) :
    Continuous fun u => rsH α β G u ω - birthSum j (rsBirth α β ω) (u : ℝ) := by
  simp only [rsH_eq hc]
  exact continuous_shift hc (α (β ω))

variable {𝓖 : Filtration ℝ≥0 m}

omit [Fintype c] [DecidableEq c] [Fintype F] in
theorem measurable_rsTime (hα : Measurable α) (hβ : Measurable[𝓖 0] β) :
    Measurable[𝓖 0] fun ω => α (β ω) := hα.comp hβ

/-- The restarted filtration of `BornUnique.BornRestart`. -/
abbrev rsFil (hα : Measurable α) (hβ : Measurable[𝓖 0] β) : Filtration ℝ≥0 m :=
  shiftFiltration 𝓖 (fun ω => α (β ω)) (measurable_rsTime hα hβ)

omit [Fintype c] [DecidableEq c] [Fintype F] in
theorem measurable_beta_rsFil (hα : Measurable α) (hβ : Measurable[𝓖 0] β) :
    Measurable[rsFil hα hβ 0] β :=
  hβ.mono (zero_le_shift 0) le_rfl

omit [Fintype c] [DecidableEq c] [Fintype F] in
theorem measurable_rsBirth (hα : Measurable α) (hβ : Measurable[𝓖 0] β) :
    Measurable[rsFil hα hβ 0] (rsBirth α β) := by
  have h : Measurable fun x : F → ℝ => fun f => x f - (α x : ℝ) :=
    measurable_pi_iff.2 fun f => (measurable_pi_apply f).sub (measurable_coe_nnreal_real.comp hα)
  exact h.comp (measurable_beta_rsFil hα hβ)

omit [Fintype F] in
theorem stronglyMeasurable_rsH (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : ∀ t, StronglyMeasurable[𝓖 t] (G t)) (u : ℝ≥0) :
    StronglyMeasurable[rsFil hα hβ u] (rsH α β G u) :=
  continuous_fromGramReal'.comp_stronglyMeasurable
    (stronglyMeasurable_limUnder_shift (ha := measurable_rsTime hα hβ)
      (Y := fun _ t ω => toGramReal (G t ω))
      (fun _ t => continuous_toGramReal.comp_stronglyMeasurable (hG t)) u)

omit [DecidableEq c] in
theorem stronglyMeasurable_rsJump (hα : Measurable α) (hβ : Measurable[𝓖 0] β) (u : ℝ≥0) :
    StronglyMeasurable[rsFil hα hβ 0] fun ω => birthSum j (rsBirth α β ω) (u : ℝ) :=
  stronglyMeasurable_of_measurable_gram ((measurable_birthSum j _).comp (measurable_rsBirth hα hβ))

/-- `𝓖₀`-measurable times are stopping times. -/
theorem isStoppingTime_of_zero {a : Ω → ℝ≥0} (ha : Measurable[𝓖 0] a) :
    IsStoppingTime 𝓖 fun ω => (a ω : WithTop ℝ≥0) := fun t => by
  have e : {ω | (a ω : WithTop ℝ≥0) ≤ t} = {ω | a ω ≤ t} := by
    ext ω; simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  rw [e]
  exact 𝓖.mono zero_le _ (measurableSet_le ha measurable_const)

end BlockBand.SourceProcess.BornRestart
