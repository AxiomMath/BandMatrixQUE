module

public import BlockBand.SourceProcess.BornStopped.Rect
public import BlockBand.SourceProcess.Stochastic.Uniqueness.LawLimit

/-!
# `BornStoppedLaw` from `GramHorizonLaw`

Write `X = tildeG(α'(z)) = (G - J)(α'(z)) + J(0)`.
1. `cond_law_horizon`: for measurable `A` with `Q{z ∈ A} > 0`, the conditional laws of `X`
   given `{z ∈ A}` agree. At the dyadic horizons below `α'(z)` they agree by `rect_dy`, and
   `dyX n → X` a.s. because `G - J` is continuous (`tendsto_dyX`), so the limits agree
   (`Uniqueness.map_eq_of_tendsto_ae`).
2. `rect_horizon`: the masses of `{z ∈ A, X ∈ B}` agree.
3. `bornStoppedLaw_of_horizon`: rectangles form a π-system generating the product σ-algebra, so
   the laws of `(z, X)` agree. Finally `(z, (G - J)(α'(z))) = (z, X - J(0))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

variable {c F Z : Type} [Fintype c] [DecidableEq c] [Fintype F] [MeasurableSpace Z] {D0 : ℝ}
  {D : Matrix c c ℂ} {j : F → GramState c} {b : Z → F → ℝ} {α' : Z → ℝ≥0}
  {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω}
  {z : Ω → Z} {G : ℝ≥0 → Ω → GramState c}
  {Ω' : Type} {m' : MeasurableSpace Ω'} {𝓖' : Filtration ℝ≥0 m'} {Q' : Measure Ω'}
  {z' : Ω' → Z} {G' : ℝ≥0 → Ω' → GramState c}

omit [Fintype c] [DecidableEq c] [MeasurableSpace Z] in
theorem tendsto_dyX
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => G t ω - birthSum j (b (z ω)) (t : ℝ)) :
    ∀ᵐ ω ∂Q, Tendsto (fun n => dyX j b α' z G n ω) atTop
      (𝓝 (tildeG j (fun ω => b (z ω)) G (α' (z ω)) ω)) := by
  filter_upwards [hc] with ω h
  have hc' : Continuous fun t => tildeG j (fun ω => b (z ω)) G t ω := h.add continuous_const
  exact (hc'.tendsto _).comp (tendsto_dyTime _)

/-- **Conditional laws at the horizon `α'(z)`.** -/
theorem cond_law_horizon (hH : GramHorizonLaw) (hD0 : 0 < D0) (hD : IsSignature D)
    (hb : Measurable b) (hα : Measurable α') (hb' : ∀ x f, b x f ≤ 0 ∨ (α' x : ℝ) ≤ b x f)
    [IsProbabilityMeasure Q] (hz : Measurable[𝓖 0] z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G)
    [IsProbabilityMeasure Q'] (hz' : Measurable[𝓖' 0] z')
    (hG' : IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (b (z' ω)) (t : ℝ)) G')
    (h0 : Q.map (fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω)) =
      Q'.map (fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' 0 ω)))
    {A : Set Z} (hA : MeasurableSet A) :
    (Q[|z ⁻¹' A]).map (fun ω => tildeG j (fun ω => b (z ω)) G (α' (z ω)) ω) =
      (Q'[|z' ⁻¹' A]).map (fun ω => tildeG j (fun ω => b (z' ω)) G' (α' (z' ω)) ω) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix c c ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → c → ℂ))
  have hzm : Measurable z := hz.mono (𝓖.le 0) le_rfl
  have hzm' : Measurable z' := hz'.mono (𝓖'.le 0) le_rfl
  have hn : ∀ n, (Q[|z ⁻¹' A]).map (dyX j b α' z G n) =
      (Q'[|z' ⁻¹' A]).map (dyX j b α' z' G' n) := by
    intro n
    ext B hB
    rw [Measure.map_apply (measurable_dyX hα hzm hG n) hB,
      Measure.map_apply (measurable_dyX hα hzm' hG' n) hB, cond_apply (hzm hA),
      cond_apply (hzm' hA), mass_eq hz hG hz' hG' h0 hA,
      rect_dy hH hD0 hD hb hα hb' hz hG hz' hG' h0 hA hB n]
  exact map_eq_of_tendsto_ae (fun n => (measurable_dyX hα hzm hG n).aemeasurable)
    (fun n => (measurable_dyX hα hzm' hG' n).aemeasurable)
    (ae_cond_of_ae (tendsto_dyX hG.continuous) _)
    (ae_cond_of_ae (tendsto_dyX hG'.continuous) _) hn

theorem aemeasurable_horizon (hα : Measurable α') (hz : Measurable z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G) :
    AEMeasurable (fun ω => tildeG j (fun ω => b (z ω)) G (α' (z ω)) ω) Q := by
  have : BorelSpace (GramState c) := gramState_borel
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix c c ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → c → ℂ))
  exact aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_dyX hα hz hG n).aemeasurable)
    (tendsto_dyX hG.continuous)

/-- **Rectangles at the horizon `α'(z)`.** -/
theorem rect_horizon (hH : GramHorizonLaw) (hD0 : 0 < D0) (hD : IsSignature D)
    (hb : Measurable b) (hα : Measurable α') (hb' : ∀ x f, b x f ≤ 0 ∨ (α' x : ℝ) ≤ b x f)
    [IsProbabilityMeasure Q] (hz : Measurable[𝓖 0] z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G)
    [IsProbabilityMeasure Q'] (hz' : Measurable[𝓖' 0] z')
    (hG' : IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (b (z' ω)) (t : ℝ)) G')
    (h0 : Q.map (fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω)) =
      Q'.map (fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' 0 ω)))
    {A : Set Z} (hA : MeasurableSet A) {B : Set (GramState c)} (hB : MeasurableSet B) :
    Q (z ⁻¹' A ∩ (fun ω => tildeG j (fun ω => b (z ω)) G (α' (z ω)) ω) ⁻¹' B) =
      Q' (z' ⁻¹' A ∩ (fun ω => tildeG j (fun ω => b (z' ω)) G' (α' (z' ω)) ω) ⁻¹' B) := by
  have hzm : Measurable z := hz.mono (𝓖.le 0) le_rfl
  have hzm' : Measurable z' := hz'.mono (𝓖'.le 0) le_rfl
  by_cases hA0 : Q (z ⁻¹' A) = 0
  · have hA0' : Q' (z' ⁻¹' A) = 0 := by rwa [← mass_eq hz hG hz' hG' h0 hA]
    rw [measure_mono_null Set.inter_subset_left hA0, measure_mono_null Set.inter_subset_left hA0']
  · rw [← cond_mul_eq_inter (hzm hA) _ Q, ← cond_mul_eq_inter (hzm' hA) _ Q',
      mass_eq hz hG hz' hG' h0 hA, ← Measure.map_apply_of_aemeasurable
        ((aemeasurable_horizon hα hzm hG).mono_ac cond_absolutelyContinuous) hB,
      ← Measure.map_apply_of_aemeasurable
        ((aemeasurable_horizon hα hzm' hG').mono_ac cond_absolutelyContinuous) hB,
      cond_law_horizon hH hD0 hD hb hα hb' hz hG hz' hG' h0 hA]

/-- **`BornStoppedLaw` from `GramHorizonLaw`.** -/
theorem bornStoppedLaw_of_horizon (hH : GramHorizonLaw) : BornStoppedLaw := by
  intro c F Z _ _ _ _ D0 D hD0 hD j b α' hb hα hb' Ω m 𝓖 Q z G hQ hz hG Ω' m' 𝓖' Q' z' G' hQ'
    hz' hG' h0
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  have hzm : Measurable z := hz.mono (𝓖.le 0) le_rfl
  have hzm' : Measurable z' := hz'.mono (𝓖'.le 0) le_rfl
  have hV := hzm.aemeasurable.prodMk (aemeasurable_horizon hα hzm hG)
  have hV' := hzm'.aemeasurable.prodMk (aemeasurable_horizon hα hzm' hG')
  have hjoint : Q.map (fun ω => (z ω, tildeG j (fun ω => b (z ω)) G (α' (z ω)) ω)) =
      Q'.map (fun ω => (z' ω, tildeG j (fun ω => b (z' ω)) G' (α' (z' ω)) ω)) := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod (fun s hs => ?_) ?_
    · obtain ⟨A, hA, B, hB, rfl⟩ := hs
      rw [Measure.map_apply_of_aemeasurable hV (hA.prod hB),
        Measure.map_apply_of_aemeasurable hV' (hA.prod hB), Set.mk_preimage_prod,
        Set.mk_preimage_prod]
      exact rect_horizon hH hD0 hD hb hα hb' hz hG hz' hG' h0 hA hB
    · rw [Measure.map_apply_of_aemeasurable hV MeasurableSet.univ,
        Measure.map_apply_of_aemeasurable hV' MeasurableSet.univ, Set.preimage_univ,
        Set.preimage_univ, measure_univ, measure_univ]
  have hΦ : Measurable fun p : Z × GramState c =>
      (p.1, p.2 - birthSum j (b p.1) ((0 : ℝ≥0) : ℝ)) :=
    measurable_fst.prodMk (measurable_snd.sub ((measurable_birthSum j _).comp
      (hb.comp measurable_fst)))
  have e : ∀ {Ω₁ : Type} (z₁ : Ω₁ → Z) (G₁ : ℝ≥0 → Ω₁ → GramState c),
      (fun ω => (z₁ ω, bornCont j (fun ω => b (z₁ ω)) G₁ (α' (z₁ ω)) ω)) =
        (fun p : Z × GramState c => (p.1, p.2 - birthSum j (b p.1) ((0 : ℝ≥0) : ℝ))) ∘
          fun ω => (z₁ ω, tildeG j (fun ω => b (z₁ ω)) G₁ (α' (z₁ ω)) ω) := by
    intro _ z₁ G₁
    funext ω
    simp only [Function.comp, bornCont, tildeG, add_sub_cancel_right]
  rw [e z G, e z' G', ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hV,
    ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hV', hjoint]

end BlockBand.SourceProcess.BornStopped
