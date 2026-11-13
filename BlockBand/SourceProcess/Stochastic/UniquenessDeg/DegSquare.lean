module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegFromMP
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegLaw
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Exhaust
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Coef
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopped-law uniqueness for a square, possibly degenerate, factor

* `map_stopped_fst_ext`: the stopped finite-dimensional law of a solution transported from its
  Wiener extension (any Wiener dimension, any universe; same proof as `map_stopped_fst`).
* **`stoppedMPUniqueness_square`**: `b, σ` locally Lipschitz on the open `U` (`σ` square,
  `σσᵀ` possibly degenerate), `W` a relatively compact subdomain; two solutions of the
  `(b, σσᵀ)` martingale problem in `W` with equal initial laws have equal laws of their paths
  stopped at the exit from `W`. The argument of the positive definite case with `σ` itself in
  place of
  `√a`: exhaustion `exhaust W m`, coefficients `exists_lipCoef`, the degenerate setups
  (`exists_degSetup`), local law equality (`map_stopped_eq_deg`), limit along the exhaustion
  (`tendsto_stopped_exhaust`) and `map_eq_of_fdd_eq₂'`.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

universe u v

variable {d : ℕ}

/-- The stopped finite-dimensional law of one solution, transported from a Wiener extension. -/
theorem map_stopped_fst_ext {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (hYa : ∀ t, Measurable[𝓖 t] (Y t))
    (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) {W' : Set (Fin d → ℝ)} (hW' : IsOpen W')
    {k : ℕ} {τ : Ω × WienerSpace k → WithTop ℝ≥0}
    (hτ : ∀ x : Ω × WienerSpace k, (Continuous fun t => Y t x.1) → τ x = exitTimeFrom W' Y x.1)
    (I : Finset ℝ≥0) :
    (extMeasure Q k).map (fun x => I.restrict fun t => Y (stopTime (τ x) t) x.1) =
      Q.map (fun ω => I.restrict fun t => stoppedProcess Y (exitTimeFrom W' Y) t ω) := by
  have hmp := measurePreserving_fst (μ := Q) (ν := commonWienerLaw (Fin k))
  have hg : AEMeasurable (fun ω => I.restrict fun t => stoppedProcess Y (exitTimeFrom W' Y) t ω)
      Q := (Finset.measurable_restrict I).comp_aemeasurable (aemeasurable_stopped hYa hYc hW')
  have hcont' : ∀ᵐ x ∂extMeasure Q k, Continuous fun t => Y t x.1 :=
    hmp.quasiMeasurePreserving.ae hYc
  have e : (extMeasure Q k).map (fun x => I.restrict fun t => Y (stopTime (τ x) t) x.1) =
      (extMeasure Q k).map ((fun ω => I.restrict fun t => stoppedProcess Y (exitTimeFrom W' Y) t
        ω) ∘ Prod.fst) := by
    refine Measure.map_congr ?_
    filter_upwards [hcont'] with x hx
    simp only [Function.comp_apply, stoppedProcess_eq_stopTime, hτ x hx]
  rw [e, ← AEMeasurable.map_map_of_aemeasurable (by rw [hmp.map_eq]; exact hg)
    measurable_fst.aemeasurable, hmp.map_eq]

theorem map_ext_initial {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {f : Ω → Fin d → ℝ} (hf : Measurable f) (k : ℕ) :
    (extMeasure Q k).map (fun x => f x.1) = Q.map f := by
  have h := (measurePreserving_fst (μ := Q) (ν := commonWienerLaw (Fin k))).map_eq
  rw [show (fun x : Ω × WienerSpace k => f x.1) = f ∘ Prod.fst from rfl,
    ← Measure.map_map hf measurable_fst, h]

/-- **Stopped-law uniqueness, square possibly degenerate factor, any universes.** -/
theorem stoppedMPUniqueness_square (b : (Fin d → ℝ) → Fin d → ℝ)
    (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (U W : Set (Fin d → ℝ)) (hU : IsOpen U)
    (hb : LocallyLipschitzOn U b) (hσL : LocallyLipschitzOn U σ) (hWU : IsInteriorDomain W U)
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)} {Y₁ : ℝ≥0 → Ω₁ → Fin d → ℝ}
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin d → ℝ}
    (hY₁ : IsMPSolutionOn Q₁ 𝓖₁ b (fun y => σ y * (σ y).transpose) W Y₁)
    (hY₂ : IsMPSolutionOn Q₂ 𝓖₂ b (fun y => σ y * (σ y).transpose) W Y₂)
    (h0 : Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0)) :
    Q₁.map (fun ω t => stoppedProcess Y₁ (exitTimeFrom W Y₁) t ω) =
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω) := by
  have _hU := hU
  have hWsubU : W ⊆ U := subset_closure.trans hWU.2.2
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
    obtain ⟨S₁, hS₁Y, hS₁ξ, hS₁τ⟩ := exists_degSetup hW'W hcb hcσ hY₁
    obtain ⟨S₂, hS₂Y, hS₂ξ, hS₂τ⟩ := exists_degSetup hW'W hcb hcσ hY₂
    have hξ : (extMeasure Q₁ (d + d)).map S₁.ξ = (extMeasure Q₂ (d + d)).map S₂.ξ := by
      rw [hS₁ξ, hS₂ξ, map_ext_initial ((hYa₁ 0).mono (𝓖₁.le 0) le_rfl),
        map_ext_initial ((hYa₂ 0).mono (𝓖₂.le 0) le_rfl), h0]
    have hloc := map_stopped_eq_deg (isOpen_exhaust m) S₁ S₂ hξ I
    rw [hS₁Y, hS₂Y] at hloc
    rw [← map_stopped_fst_ext hYa₁ hY₁.continuous (isOpen_exhaust m) hS₁τ I,
      ← map_stopped_fst_ext hYa₂ hY₂.continuous (isOpen_exhaust m) hS₂τ I]
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

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
