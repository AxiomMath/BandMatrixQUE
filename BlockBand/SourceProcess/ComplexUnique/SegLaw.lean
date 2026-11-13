module

public import BlockBand.SourceProcess.ComplexUnique.SegCond
public import BlockBand.SourceProcess.BornUnique.Concat

/-!
# The segment law from the restarted processes

**`segment_law`**: given, for two models, restarted real joint processes `Y_i` with the conclusions
of `segModel`, equal laws of `(G_i(a), 𝒦_i(a))` give equal laws of `(G_i(a + h), 𝒦_i(a + h))`.
Split over the strata of `G(a)` (`map_eq_of_cond_strata`); on each stratum use
`seg_cond_facts` and `stratum_law_eq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

variable {K : ℕ} {π : Type} [Fintype π] [DecidableEq π]

omit [DecidableEq π] in
theorem measurable_GK {Ω : Type*} {mΩ : MeasurableSpace Ω} {G : Ω → GramState (SrcCol K π)}
    {Kc : Ω → Matrix π π ℂ} (hG : StronglyMeasurable G) (hK : StronglyMeasurable Kc) :
    Measurable fun ω => (G ω, Kc ω) := by
  have : BorelSpace (GramState (SrcCol K π)) := SourceProcessLaw.gramState_borel
  have : SecondCountableTopology (GramState (SrcCol K π)) := gramState_secondCountable
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix (SrcCol K π) (SrcCol K π) ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (SrcCol K π → SrcCol K π → ℂ))
  have : BorelSpace (Matrix π π ℂ) := inferInstanceAs (BorelSpace (π → π → ℂ))
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix π π ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (π → π → ℂ))
  exact hG.measurable.prodMk hK.measurable

omit [DecidableEq π] in
theorem measurable_toR_jvec (t : ℝ) :
    Measurable fun p : GramState (SrcCol K π) × Matrix π π ℂ => toR t (jvec p.1 p.2) := by
  have : BorelSpace (GramState (SrcCol K π)) := SourceProcessLaw.gramState_borel
  have : SecondCountableTopology (GramState (SrcCol K π)) := gramState_secondCountable
  have : BorelSpace (Matrix π π ℂ) := inferInstanceAs (BorelSpace (π → π → ℂ))
  have : SecondCountableTopology (Matrix π π ℂ) :=
    inferInstanceAs (SecondCountableTopology (π → π → ℂ))
  exact (continuous_toR.comp (continuous_const.prodMk continuous_jvec)).measurable

omit [DecidableEq π] in
theorem measurable_gk :
    Measurable fun y : Fin (rDim (JIdx (SrcCol K π) π)) → ℝ => (gramOf (zOf y), kOf (zOf y)) := by
  have : BorelSpace (GramState (SrcCol K π)) := SourceProcessLaw.gramState_borel
  have : SecondCountableTopology (GramState (SrcCol K π)) := gramState_secondCountable
  have : BorelSpace (Matrix π π ℂ) := inferInstanceAs (BorelSpace (π → π → ℂ))
  have : SecondCountableTopology (Matrix π π ℂ) :=
    inferInstanceAs (SecondCountableTopology (π → π → ℂ))
  exact ((continuous_gramOf.comp continuous_zOf).prodMk
    ((continuous_pi fun _ => continuous_pi fun _ => continuous_apply _).comp
      continuous_zOf)).measurable

variable {D0 η : ℝ} {D : Matrix (SrcCol K π) (SrcCol K π) ℂ} {a h : ℝ≥0}

/-- **The segment law.** -/
theorem segment_law (hD0 : 0 ≤ D0) (hD : IsSignature D)
    {Ω₁ : Type} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {Y₁ : ℝ≥0 → Ω₁ → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ}
    {G₁ : ℝ≥0 → Ω₁ → GramState (SrcCol K π)} {K₁ : ℝ≥0 → Ω₁ → Matrix π π ℂ}
    (hY₁ : IsMPSolutionOn Q₁ 𝓖₁ (realDrift (jβ D0 D)) (realCov (jΓ D0 η D) (jΓ' D0 η D))
      {y | tOf y < h} Y₁)
    (ht₁ : ∀ ω u, tOf (Y₁ u ω) = ((min u h : ℝ≥0) : ℝ))
    (hz₁ : ∀ ω u, u ≤ h → zOf (Y₁ u ω) = jvec (G₁ (a + u) ω) (K₁ (a + u) ω))
    (hf₁ : ∀ᵐ ω ∂Q₁, ∀ u, GramFeasible D (G₁ u ω))
    (hr₁ : ∀ k, ∀ᵐ ω ∂Q₁, RankProp k (fun u => G₁ (a + u) ω) (Iio h))
    (hm₁ : Measurable fun ω => (G₁ a ω, K₁ a ω))
    {Ω₂ : Type} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {Y₂ : ℝ≥0 → Ω₂ → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ}
    {G₂ : ℝ≥0 → Ω₂ → GramState (SrcCol K π)} {K₂ : ℝ≥0 → Ω₂ → Matrix π π ℂ}
    (hY₂ : IsMPSolutionOn Q₂ 𝓖₂ (realDrift (jβ D0 D)) (realCov (jΓ D0 η D) (jΓ' D0 η D))
      {y | tOf y < h} Y₂)
    (ht₂ : ∀ ω u, tOf (Y₂ u ω) = ((min u h : ℝ≥0) : ℝ))
    (hz₂ : ∀ ω u, u ≤ h → zOf (Y₂ u ω) = jvec (G₂ (a + u) ω) (K₂ (a + u) ω))
    (hf₂ : ∀ᵐ ω ∂Q₂, ∀ u, GramFeasible D (G₂ u ω))
    (hr₂ : ∀ k, ∀ᵐ ω ∂Q₂, RankProp k (fun u => G₂ (a + u) ω) (Iio h))
    (hm₂ : Measurable fun ω => (G₂ a ω, K₂ a ω))
    (h0 : Q₁.map (fun ω => (G₁ a ω, K₁ a ω)) = Q₂.map (fun ω => (G₂ a ω, K₂ a ω))) :
    Q₁.map (fun ω => (G₁ (a + h) ω, K₁ (a + h) ω)) =
      Q₂.map (fun ω => (G₂ (a + h) ω, K₂ (a + h) ω)) := by
  have hYm₁ : ∀ u, Measurable (Y₁ u) := fun u => (hY₁.adapted u).measurable.mono (𝓖₁.le u) le_rfl
  have hYm₂ : ∀ u, Measurable (Y₂ u) := fun u => (hY₂.adapted u).measurable.mono (𝓖₂.le u) le_rfl
  have hY0 : ∀ {Ω : Type} (Y : ℝ≥0 → Ω → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ)
      (G : ℝ≥0 → Ω → GramState (SrcCol K π)) (Kc : ℝ≥0 → Ω → Matrix π π ℂ),
      (∀ ω u, tOf (Y u ω) = ((min u h : ℝ≥0) : ℝ)) →
      (∀ ω u, u ≤ h → zOf (Y u ω) = jvec (G (a + u) ω) (Kc (a + u) ω)) →
      Y 0 = (fun p => toR 0 (jvec p.1 p.2)) ∘ fun ω => (G a ω, Kc a ω) := by
    intro Ω Y G Kc ht hz
    funext ω
    rw [← toR_tOf_zOf (Y 0 ω), ht, hz ω 0 zero_le, add_zero, min_eq_left zero_le]; rfl
  have h0Y : Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0) := by
    rw [hY0 Y₁ G₁ K₁ ht₁ hz₁, hY0 Y₂ G₂ K₂ ht₂ hz₂, ← Measure.map_map (measurable_toR_jvec 0) hm₁,
      ← Measure.map_map (measurable_toR_jvec 0) hm₂, h0]
  have hst : Measurable (fun y : Fin (rDim (JIdx (SrcCol K π) π)) → ℝ => stratumIdx (gOf y)) := by
    have : BorelSpace (GramState (SrcCol K π)) := SourceProcessLaw.gramState_borel
    exact measurable_stratumIdx.comp continuous_gOf.measurable
  have hh' : Q₁.map (Y₁ h) = Q₂.map (Y₂ h) := by
    refine map_eq_of_cond_strata (k₁ := fun ω => stratumIdx (gOf (Y₁ 0 ω)))
      (k₂ := fun ω => stratumIdx (gOf (Y₂ 0 ω))) (hst.comp (hYm₁ 0)) (hst.comp (hYm₂ 0))
      (hYm₁ h) (hYm₂ h)
      (fun x => mass_eq_of_map_eq (hYm₁ 0) (hYm₂ 0) h0Y (hst (measurableSet_singleton x)))
      fun x hx0 => ?_
    have hx0' : Q₂ ((fun ω => stratumIdx (gOf (Y₂ 0 ω))) ⁻¹' {x}) ≠ 0 := by
      have := mass_eq_of_map_eq (hYm₁ 0) (hYm₂ 0) h0Y (hst (measurableSet_singleton x))
      exact this ▸ hx0
    have := cond_isProbabilityMeasure hx0
    have := cond_isProbabilityMeasure hx0'
    have hA₁ : MeasurableSet[𝓖₁ 0] ((fun ω => stratumIdx (gOf (Y₁ 0 ω))) ⁻¹' {x}) :=
      (hst.comp (hY₁.adapted 0).measurable) (measurableSet_singleton x)
    have hA₂ : MeasurableSet[𝓖₂ 0] ((fun ω => stratumIdx (gOf (Y₂ 0 ω))) ⁻¹' {x}) :=
      (hst.comp (hY₂.adapted 0).measurable) (measurableSet_singleton x)
    obtain ⟨hF₁, hp₁⟩ := seg_cond_facts ht₁ hz₁ hf₁ hr₁ x
      ((hst.comp (hYm₁ 0)) (measurableSet_singleton x))
    obtain ⟨hF₂, hp₂⟩ := seg_cond_facts ht₂ hz₂ hf₂ hr₂ x
      ((hst.comp (hYm₂ 0)) (measurableSet_singleton x))
    exact stratum_law_eq hD0 η hD (isMPSolutionOn_cond hY₁ hA₁ hx0) ht₁ hF₁ hp₁
      (isMPSolutionOn_cond hY₂ hA₂ hx0') ht₂ hF₂ hp₂
      (cond_map_eq_of_map_eq (hYm₁ 0) (hYm₂ 0) h0Y (hst (measurableSet_singleton x)))
  have hYt : ∀ {Ω : Type} (Y : ℝ≥0 → Ω → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ)
      (G : ℝ≥0 → Ω → GramState (SrcCol K π)) (Kc : ℝ≥0 → Ω → Matrix π π ℂ),
      (∀ ω u, u ≤ h → zOf (Y u ω) = jvec (G (a + u) ω) (Kc (a + u) ω)) →
      (fun ω => (G (a + h) ω, Kc (a + h) ω)) =
        (fun y => (gramOf (zOf y), kOf (zOf y))) ∘ Y h := by
    intro Ω Y G Kc hz
    funext ω
    simp only [Function.comp, hz ω h le_rfl, gramOf_jvec, kOf_jvec]
  rw [hYt Y₁ G₁ K₁ hz₁, hYt Y₂ G₂ K₂ hz₂, ← Measure.map_map measurable_gk (hYm₁ h),
    ← Measure.map_map measurable_gk (hYm₂ h), hh']

end BlockBand.SourceProcess.ComplexUnique
