module

public import BlockBand.Transmission.Dual.UniqueLevel

/-!
# Uniqueness in law of the top level up to the first deletion

`map_stopped_padPath_eq`: for two realizations of `IsDualFrom` at level `p ≥ 1` (any filtered
probability spaces) with the same law of the padded start `V₀`, the laws of `V` stopped at its
exit from `flatChamber p` (that is, at the first deletion time `σ_{p−1}`,
`IsDualFrom.exitTime_eq`) coincide, on `ℝ≥0 → ℝ^{p+p}` with the product σ-algebra.

Proof: `stoppedMartingaleProblemUniquenessPosDef_holds` on each `exhaust (flatChamber p) m` (a
relatively compact subdomain), with the regularity of the flat coefficients and the solution
property `IsDualFrom.isMPSolutionOn`; then `tendsto_stopped_exhaust` and `map_eq_of_tendsto_ae`
for the finite-dimensional laws, and `map_eq_of_fdd_eq₂'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Uniqueness BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {p : ℕ} {D0 : ℝ}

/-- **The stopped top-level law is determined by the law of the start.** -/
theorem map_stopped_padPath_eq (hD0 : 0 < D0) (hp : 1 ≤ p)
    {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)} {N₁ : ℝ≥0 → Ω₁ → ℕ}
    {X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ}
    {Ω₂ : Type} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂}
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {N₂ : ℝ≥0 → Ω₂ → ℕ}
    {X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ}
    (h₁ : IsDualFrom P₁ 𝓖₁ D0 p N₁ X₁ Y₁) (h₂ : IsDualFrom P₂ 𝓖₂ D0 p N₂ X₂ Y₂)
    (h0 : P₁.map (padPath p N₁ X₁ Y₁ 0) = P₂.map (padPath p N₂ X₂ Y₂ 0)) :
    P₁.map (fun ω t => stoppedProcess (padPath p N₁ X₁ Y₁)
        (exitTimeFrom (flatChamber p) (padPath p N₁ X₁ Y₁)) t ω) =
      P₂.map (fun ω t => stoppedProcess (padPath p N₂ X₂ Y₂)
        (exitTimeFrom (flatChamber p) (padPath p N₂ X₂ Y₂)) t ω) := by
  have := h₁.prob
  have := h₂.prob
  set V₁ := padPath p N₁ X₁ Y₁
  set V₂ := padPath p N₂ X₂ Y₂
  set U := flatChamber p
  have hU : IsOpen U := isOpen_flatChamber p
  have hYa₁ : ∀ t, Measurable[𝓖₁ t] (V₁ t) := h₁.measurable_padPath
  have hYa₂ : ∀ t, Measurable[𝓖₂ t] (V₂ t) := h₂.measurable_padPath
  have hc₁ : ∀ᵐ ω ∂P₁, Continuous fun t => V₁ t ω := Eventually.of_forall h₁.continuous_padPath
  have hc₂ : ∀ᵐ ω ∂P₂, Continuous fun t => V₂ t ω := Eventually.of_forall h₂.continuous_padPath
  have hS₁ := h₁.isMPSolutionOn hp
  have hS₂ := h₂.isMPSolutionOn hp
  have hm : ∀ (m : ℕ) (I : Finset ℝ≥0),
      P₁.map (fun ω => I.restrict fun t => stoppedProcess V₁ (exitTimeFrom (exhaust U m) V₁) t ω) =
        P₂.map (fun ω => I.restrict fun t =>
          stoppedProcess V₂ (exitTimeFrom (exhaust U m) V₂) t ω) := by
    intro m I
    have hW : IsInteriorDomain (exhaust U m) U :=
      ⟨isOpen_exhaust m, isCompact_closure_exhaust m, closure_exhaust_subset_U m⟩
    have hWU : exhaust U m ⊆ U := subset_closure.trans hW.2.2
    have hfull := stoppedMartingaleProblemUniquenessPosDef_holds (p + p) (flatDrift D0 p)
      (flatDiff D0 p) U (exhaust U m) hU (locallyLipschitzOn_flatDrift D0)
      (contDiffOn_flatDiff D0) (fun w hw => flatDiff_posDef hD0 hw) hW Ω₁ P₁ 𝓖₁ V₁ Ω₂ P₂ 𝓖₂ V₂
      (isMPSolutionOn_mono hS₁ hWU) (isMPSolutionOn_mono hS₂ hWU) h0
    have e₁ := AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable
      (aemeasurable_stopped hYa₁ hc₁ (isOpen_exhaust (U := U) m))
    have e₂ := AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable
      (aemeasurable_stopped hYa₂ hc₂ (isOpen_exhaust (U := U) m))
    rw [← Function.comp_def (Finset.restrict I), ← e₁, hfull, e₂]
    rfl
  have hfdd : ∀ I : Finset ℝ≥0,
      P₁.map (fun ω => I.restrict fun t => stoppedProcess V₁ (exitTimeFrom U V₁) t ω) =
        P₂.map (fun ω => I.restrict fun t => stoppedProcess V₂ (exitTimeFrom U V₂) t ω) := by
    intro I
    refine map_eq_of_tendsto_ae
      (f₁ := fun m ω => I.restrict fun t => stoppedProcess V₁ (exitTimeFrom (exhaust U m) V₁) t ω)
      (f₂ := fun m ω => I.restrict fun t => stoppedProcess V₂ (exitTimeFrom (exhaust U m) V₂) t ω)
      (fun m => (Finset.measurable_restrict I).comp_aemeasurable
        (aemeasurable_stopped hYa₁ hc₁ (isOpen_exhaust m)))
      (fun m => (Finset.measurable_restrict I).comp_aemeasurable
        (aemeasurable_stopped hYa₂ hc₂ (isOpen_exhaust m))) ?_ ?_ (hm · I)
    · filter_upwards [hc₁] with ω hω
      exact tendsto_pi_nhds.2 fun t => tendsto_stopped_exhaust hU hω t
    · filter_upwards [hc₂] with ω hω
      exact tendsto_pi_nhds.2 fun t => tendsto_stopped_exhaust hU hω t
  exact map_eq_of_fdd_eq₂' (aemeasurable_stopped hYa₁ hc₁ hU)
    (aemeasurable_stopped hYa₂ hc₂ hU) hfdd

end BlockBand.Transmission.Dual
