module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Exhaust
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Coef
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopped-law uniqueness for a positive definite covariance

`stoppedMartingaleProblemUniquenessPosDef_holds`: for `b` locally Lipschitz and `a` of class `C²`
and positive definite on `U`, two solutions of the `(b, a)` martingale problem in a relatively
compact subdomain `W` with equal initial laws have equal laws of their paths stopped at the exit
from `W`. The proof takes a locally Lipschitz square root `σ = √a` (`exists_sqrt_of_posDef`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ}

/-- The stopped finite-dimensional law of one solution at the exit from `exhaust W m`,
transported from its Wiener extension. -/
theorem map_stopped_fst {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hYa : ∀ t, Measurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {W' : Set (Fin d → ℝ)} (hW' : IsOpen W') {τ : Ω × WienerSpace d → WithTop ℝ≥0}
    (hτ : ∀ x : Ω × WienerSpace d, (Continuous fun t => Y t x.1) → τ x = exitTimeFrom W' Y x.1)
    (I : Finset ℝ≥0) :
    (extMeasure Q d).map (fun x => I.restrict fun t => Y (stopTime (τ x) t) x.1) =
      Q.map (fun ω => I.restrict fun t => stoppedProcess Y (exitTimeFrom W' Y) t ω) := by
  have hmp := measurePreserving_fst (μ := Q) (ν := commonWienerLaw (Fin d))
  have hg : AEMeasurable (fun ω => I.restrict fun t => stoppedProcess Y (exitTimeFrom W' Y) t ω)
      Q := (Finset.measurable_restrict I).comp_aemeasurable (aemeasurable_stopped hYa hYc hW')
  have hcont' : ∀ᵐ x ∂extMeasure Q d, Continuous fun t => Y t x.1 :=
    hmp.quasiMeasurePreserving.ae hYc
  have e : (extMeasure Q d).map (fun x => I.restrict fun t => Y (stopTime (τ x) t) x.1) =
      (extMeasure Q d).map ((fun ω => I.restrict fun t => stoppedProcess Y (exitTimeFrom W' Y) t
        ω) ∘ Prod.fst) := by
    refine Measure.map_congr ?_
    filter_upwards [hcont'] with x hx
    simp only [Function.comp_apply, stoppedProcess_eq_stopTime, hτ x hx]
  rw [e, ← AEMeasurable.map_map_of_aemeasurable (by rw [hmp.map_eq]; exact hg)
    measurable_fst.aemeasurable, hmp.map_eq]

/-- **`StoppedMartingaleProblemUniquenessPosDef` holds.** -/
theorem stoppedMartingaleProblemUniquenessPosDef_holds (d : ℕ) :
    StoppedMartingaleProblemUniquenessPosDef d := by
  intro b a U W hU hb ha hpos hWU Ω₁ _ Q₁ _ 𝓖₁ Y₁ Ω₂ _ Q₂ _ 𝓖₂ Y₂ hY₁ hY₂ h0
  obtain ⟨σ, hσL, hσa, hdet⟩ := exists_sqrt_of_posDef hU ha hpos
  have hWsubU : W ⊆ U := subset_closure.trans hWU.2.2
  have hY₁' := isMPSolutionOn_congr hY₁ (fun y hy => (hσa y (hWsubU hy)).symm)
  have hY₂' := isMPSolutionOn_congr hY₂ (fun y hy => (hσa y (hWsubU hy)).symm)
  have hYa₁ : ∀ t, Measurable[𝓖₁ t] (Y₁ t) := fun t => (hY₁.adapted t).measurable
  have hYa₂ : ∀ t, Measurable[𝓖₂ t] (Y₂ t) := fun t => (hY₂.adapted t).measurable
  have hm : ∀ (m : ℕ) (I : Finset ℝ≥0),
      Q₁.map (fun ω => I.restrict fun t => stoppedProcess Y₁ (exitTimeFrom (exhaust W m) Y₁) t ω) =
        Q₂.map (fun ω => I.restrict fun t =>
          stoppedProcess Y₂ (exitTimeFrom (exhaust W m) Y₂) t ω) := by
    intro m I
    have hW'W : IsInteriorDomain (exhaust W m) W :=
      ⟨isOpen_exhaust m, isCompact_closure_exhaust m, closure_exhaust_subset_U m⟩
    have hW'U : closure (exhaust W m) ⊆ U := hW'W.2.2.trans hWsubU
    obtain ⟨c, hcb, hcσ⟩ := exists_lipCoef hb hσL hW'W.2.1 hW'U
    obtain ⟨S₁, hS₁Y, hS₁ξ, hS₁τ⟩ := exists_eulerSetup hU hb.continuousOn hσL.continuousOn hW'W
      hW'U (fun y hy => hdet y (hW'U hy)) hcb hcσ hY₁'
    obtain ⟨S₂, hS₂Y, hS₂ξ, hS₂τ⟩ := exists_eulerSetup hU hb.continuousOn hσL.continuousOn hW'W
      hW'U (fun y hy => hdet y (hW'U hy)) hcb hcσ hY₂'
    have hξ : (extMeasure Q₁ d).map S₁.ξ = (extMeasure Q₂ d).map S₂.ξ := by
      rw [hS₁ξ, hS₂ξ]
      have h1 := (measurePreserving_fst (μ := Q₁) (ν := commonWienerLaw (Fin d))).map_eq
      have h2 := (measurePreserving_fst (μ := Q₂) (ν := commonWienerLaw (Fin d))).map_eq
      rw [show (fun x : Ω₁ × WienerSpace d => Y₁ 0 x.1) = Y₁ 0 ∘ Prod.fst from rfl,
        show (fun x : Ω₂ × WienerSpace d => Y₂ 0 x.1) = Y₂ 0 ∘ Prod.fst from rfl,
        ← Measure.map_map ((hYa₁ 0).mono (𝓖₁.le 0) le_rfl) measurable_fst,
        ← Measure.map_map ((hYa₂ 0).mono (𝓖₂.le 0) le_rfl) measurable_fst, h1, h2, h0]
    have hloc := map_stopped_eq (isOpen_exhaust m) S₁ S₂ hξ I
    rw [hS₁Y, hS₂Y] at hloc
    rw [← map_stopped_fst hYa₁ hY₁.continuous (isOpen_exhaust m) hS₁τ I,
      ← map_stopped_fst hYa₂ hY₂.continuous (isOpen_exhaust m) hS₂τ I]
    exact hloc
  have hfdd : ∀ I : Finset ℝ≥0,
      Q₁.map (fun ω => I.restrict fun t => stoppedProcess Y₁ (exitTimeFrom W Y₁) t ω) =
        Q₂.map (fun ω => I.restrict fun t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω) := by
    intro I
    refine map_eq_of_tendsto_ae
      (f₁ := fun m ω => I.restrict fun t => stoppedProcess Y₁ (exitTimeFrom (exhaust W m) Y₁) t ω)
      (f₂ := fun m ω => I.restrict fun t => stoppedProcess Y₂ (exitTimeFrom (exhaust W m) Y₂) t ω)
      (fun m => (Finset.measurable_restrict I).comp_aemeasurable
        (aemeasurable_stopped hYa₁ hY₁.continuous (isOpen_exhaust m)))
      (fun m => (Finset.measurable_restrict I).comp_aemeasurable
        (aemeasurable_stopped hYa₂ hY₂.continuous (isOpen_exhaust m))) ?_ ?_ (hm · I)
    · filter_upwards [hY₁.continuous] with ω hω
      exact tendsto_pi_nhds.2 fun t => tendsto_stopped_exhaust hWU.1 hω t
    · filter_upwards [hY₂.continuous] with ω hω
      exact tendsto_pi_nhds.2 fun t => tendsto_stopped_exhaust hWU.1 hω t
  exact map_eq_of_fdd_eq₂' (aemeasurable_stopped hYa₁ hY₁.continuous hWU.1)
    (aemeasurable_stopped hYa₂ hY₂.continuous hWU.1) hfdd

end BlockBand.SourceProcess.Stochastic.Uniqueness
