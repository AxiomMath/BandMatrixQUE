module

public import BlockBand.SourceProcess.CapLimit.Model
public import BlockBand.SourceProcess.SourceProcessLaw.ModelValue
public import BlockBand.SourceProcess.CutoffLimit.Estimate

/-!
# Comparing the model values at caps `K ≤ K'`

On `A = {t_K ≤ h²}` both the conditioned cap-`K` model (`condModel`) and the conditioned and
restricted cap-`K'` model (`capRestrict`) are cap-`K` models with the entrance
`entrance[|capSet K h]`, so `ModelUnique` gives the same law of the final Gram state; the
transform only reads the probe block, which the restriction keeps. Hence `∫_A F` agrees
(`setIntegral_capSet_eq`). Off `A` both transforms lie in `[0,1]` (feasibility,
`transform_mem`), so each `∫_{Aᶜ} F ∈ [0, P(Aᶜ)]`, and `P(Aᶜ) = entrance (capSet K h)ᶜ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h : ℝ} {K K' M : ℕ} {J : ℕ}
  {a : Fin J → Fin p → ℝ} {entrance : Measure (Measure unitInterval)}

section OneModel

variable {Ω : Type} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {Q : Measure Ω} {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
  {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}

theorem model_measurable_G (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G)
    (t : ℝ≥0) : Measurable (G t) :=
  measurable_of_stronglyMeasurable_gram (𝓖.le _) (hM.solution.adapted t)

theorem measurable_transform (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G)
    (t : ℝ≥0) : Measurable fun ω => sampledTransformValue a (G t ω) :=
  (measurable_sampledTransformValue a).comp (model_measurable_G hM t)

theorem ae_transform_mem (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G)
    (ha : ∀ j i, 0 ≤ a j i) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 ≤ sampledTransformValue a (G t ω) ∧ sampledTransformValue a (G t ω) ≤ 1 := by
  filter_upwards [hM.solution.feasible] with ω hf
  obtain ⟨n, P, V, -, -, -, hV⟩ := hf t
  rw [← hV]
  exact CutoffLimit.transform_mem (P := P) ha V

theorem integrable_transform (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G)
    (ha : ∀ j i, 0 ≤ a j i) (t : ℝ≥0) :
    Integrable (fun ω => sampledTransformValue a (G t ω)) Q := by
  have := hM.prob
  refine Integrable.of_bound (measurable_transform hM t).aestronglyMeasurable 1 ?_
  filter_upwards [ae_transform_mem hM ha t] with ω hω
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hω.1, hω.2]

theorem setIntegral_transform_mem (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G)
    (ha : ∀ j i, 0 ≤ a j i) (t : ℝ≥0) (B : Set Ω) :
    0 ≤ ∫ ω in B, sampledTransformValue a (G t ω) ∂Q ∧
      ∫ ω in B, sampledTransformValue a (G t ω) ∂Q ≤ (Q B).toReal := by
  have := hM.prob
  have hb := ae_transform_mem hM ha t
  refine ⟨integral_nonneg_of_ae (ae_restrict_of_ae (hb.mono fun ω hω => hω.1)), ?_⟩
  have h1 : ∫ ω in B, sampledTransformValue a (G t ω) ∂Q ≤ ∫ _ in B, (1 : ℝ) ∂Q :=
    integral_mono_ae (integrable_transform hM ha t).integrableOn (integrable_const _)
      (ae_restrict_of_ae (hb.mono fun ω hω => hω.2))
  rwa [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at h1

end OneModel

/-- **The two caps agree on `{t_K ≤ h²}`** (by `ModelUnique`). -/
theorem setIntegral_capSet_eq (hB2 : ModelUnique) (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hs : 0 < s) (hsT : s < T) (hq : ∀ i, IsSourceTest s T (q i)) (hh : 0 < h)
    (hMp : 0 < M) (hK : K ≤ K')
    {Ω : Type} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Q : Measure Ω} {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
    {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}
    (hM : IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G)
    {Ω' : Type} [MeasurableSpace Ω'] {𝓖' : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω')}
    {Q' : Measure Ω'} {tseq' : Ω' → ℕ → ℝ} {τ' : Ω' → Fin p × Fin M → ℝ}
    {G' : ℝ≥0 → Ω' → GramState (SrcCol K' (Fin p × Fin M))}
    (hM' : IsFiniteSourceModel b E s T q h K' M entrance 𝓖' Q' tseq' τ' G') (t : ℝ≥0) :
    ∫ ω in entEvent tseq (capSet K h), sampledTransformValue a (G t ω) ∂Q =
      ∫ ω in entEvent tseq' (capSet K h), sampledTransformValue a (G' t ω) ∂Q' := by
  have hS := measurableSet_capSet K h
  have hQA := measure_entEvent hM hS
  have hQA' := measure_entEvent hM' hS
  by_cases h0 : entrance (capSet K h) = 0
  · rw [setIntegral_measure_zero _ (hQA.trans h0), setIntegral_measure_zero _ (hQA'.trans h0)]
  have hM1 := condModel hM hS h0
  have hM2 := capRestrict hK hM' h0
  have hlaw := hB2 b hb0 hb E hE1 hE2 s T hs hsT p q hq _ h K M hh hMp Ω _ 𝓖 _ _ _ _ hM1
    Ω' _ 𝓖' _ _ _ _ hM2 t
  have hf := measurable_sampledTransformValue (K := K) (M := M) a
  have e1 : ∫ ω, sampledTransformValue a (G t ω) ∂(Q[|entEvent tseq (capSet K h)]) =
      ∫ ω, sampledTransformValue a (G' t ω) ∂(Q'[|entEvent tseq' (capSet K h)]) := by
    have := (model_measurable_G hM2 t).aemeasurable (μ := Q'[|entEvent tseq' (capSet K h)])
    rw [← integral_map (model_measurable_G hM1 t).aemeasurable hf.aestronglyMeasurable, hlaw,
      integral_map this hf.aestronglyMeasurable]
    rfl
  have hfin : entrance (capSet K h) ≠ ∞ := by
    rw [← hQA]
    have := hM.prob
    exact measure_ne_top _ _
  have hc : ((entrance (capSet K h))⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 hfin, ENNReal.inv_ne_top.2 h0⟩
  simp only [ProbabilityTheory.cond, integral_smul_measure, hQA, hQA', smul_eq_mul] at e1
  exact mul_left_cancel₀ hc e1

/-- **`|Φ(K) − Φ(K')| ≤ P(t_K > h²)`** for `K ≤ K'`. -/
theorem abs_value_sub_le (hB2 : ModelUnique) (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hs : 0 < s) (hsT : s < T) (hq : ∀ i, IsSourceTest s T (q i))
    (ha : ∀ j i, 0 ≤ a j i) (hh : 0 < h) (hMp : 0 < M) (hK : K ≤ K') {v v' : ℝ}
    (hv : FiniteSourceModelValue b E s T q h K M entrance a v)
    (hv' : FiniteSourceModelValue b E s T q h K' M entrance a v') :
    |v - v'| ≤ (entrance (capSet K h)ᶜ).toReal := by
  obtain ⟨Ω, m, 𝓖, Q, tseq, τ, G, hM⟩ := hv.1
  obtain ⟨Ω', m', 𝓖', Q', tseq', τ', G', hM'⟩ := hv'.1
  have e := hv.2 Ω m 𝓖 Q tseq τ G hM
  have e' := hv'.2 Ω' m' 𝓖' Q' tseq' τ' G' hM'
  have hS := measurableSet_capSet K h
  have hA := 𝓖.le 0 _ (measurableSet_entEvent hM hS)
  have hA' := 𝓖'.le 0 _ (measurableSet_entEvent hM' hS)
  have hsplit := integral_add_compl hA (integrable_transform hM ha (T - s).toNNReal)
  have hsplit' := integral_add_compl hA' (integrable_transform hM' ha (T - s).toNNReal)
  have heq := setIntegral_capSet_eq (a := a) hB2 hb0 hb hE1 hE2 hs hsT hq hh hMp hK hM hM'
    (T - s).toNNReal
  have hc : Q (entEvent tseq (capSet K h))ᶜ = entrance (capSet K h)ᶜ :=
    measure_entEvent hM hS.compl
  have hc' : Q' (entEvent tseq' (capSet K h))ᶜ = entrance (capSet K h)ᶜ :=
    measure_entEvent hM' hS.compl
  have b1 := setIntegral_transform_mem hM ha (T - s).toNNReal (entEvent tseq (capSet K h))ᶜ
  have b2 := setIntegral_transform_mem hM' ha (T - s).toNNReal (entEvent tseq' (capSet K h))ᶜ
  rw [hc] at b1
  rw [hc'] at b2
  rw [← e, ← e', ← hsplit, ← hsplit', heq, add_sub_add_left_eq_sub]
  exact abs_sub_le_iff.2 ⟨by linarith [b1.1, b2.2], by linarith [b1.2, b2.1]⟩

end BlockBand.SourceProcess.CapLimit
