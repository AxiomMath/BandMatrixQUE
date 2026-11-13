module

public import BlockBand.SourceProcess.ComplexCapLimit.Model
public import BlockBand.SourceProcess.ComplexSourceLaw.Interface

/-!
# Comparing the complex model values at caps `K ≤ K'`

Under `ComplexFiniteUniqueness`, the complex finite source models at caps `K ≤ K'` have the same
integral of a bounded continuous function `Φ` of the final source data on `{t_K ≤ h²}`
(`setIntegral_capSet_eq`). Hence their values differ by at most `2‖Φ‖ P(t_K > h²)`
(`abs_value_sub_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCapLimit

open MeasureTheory ProbabilityTheory Function Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {b E s T : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {h : ℝ} {K K' : ℕ}
  {entrance : Measure (Measure unitInterval)}

theorem continuous_probeBlock {π : Type*} : Continuous (probeBlock (K := K) (π := π)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply_apply _ _

theorem continuous_modelSourceData (D : Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) :
    Continuous fun p : Matrix (Fin np) (Fin np) ℂ × GramState (SrcCol K (Fin np)) =>
      modelSourceData D p.1 p.2 := by
  have h1 : Continuous fun p : Matrix (Fin np) (Fin np) ℂ × GramState (SrcCol K (Fin np)) =>
      p.2.1 := continuous_fst.comp continuous_snd
  refine continuous_pi fun r => ?_
  fin_cases r
  · exact continuous_fst
  · exact continuous_probeBlock.comp h1
  · exact continuous_probeBlock.comp (continuous_snd.comp continuous_snd)
  · exact continuous_probeBlock.comp ((h1.matrix_mul continuous_const).matrix_mul h1)

section OneModel

variable {Ω : Type*} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {Q : Measure Ω} {tseq : Ω → ℕ → ℝ} {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
  {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

theorem stronglyMeasurable_final
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (t : ℝ≥0) :
    StronglyMeasurable fun ω => Φ (modelSourceData (srcSignature K (Fin np)) (Kc t ω) (G t ω)) :=
  ((Φ.continuous.comp (continuous_modelSourceData _)).comp_stronglyMeasurable
    ((hM.complex.adapted t).prodMk (hM.solution.adapted t))).mono (𝓖.le t)

theorem integrable_final
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (t : ℝ≥0) :
    Integrable (fun ω => Φ (modelSourceData (srcSignature K (Fin np)) (Kc t ω) (G t ω))) Q := by
  have := hM.prob
  exact Integrable.of_bound (stronglyMeasurable_final hM Φ t).aestronglyMeasurable ‖Φ‖
    (ae_of_all _ fun ω => Φ.norm_coe_le_norm _)

end OneModel

/-- **The two caps agree on `{t_K ≤ h²}`** (by `ComplexFiniteUniqueness`). -/
theorem setIntegral_capSet_eq (hU : ComplexFiniteUniqueness) (hdom : ComplexSourceLawDomain b E τ m T)
    (hs : 0 < s) (hsτ : ∀ j, s < τ j) (hh : 0 < h)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (hK : K ≤ K')
    {Ω : Type} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Q : Measure Ω} {tseq : Ω → ℕ → ℝ} {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc)
    {Ω' : Type} [MeasurableSpace Ω'] {𝓖' : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω')}
    {Q' : Measure Ω'} {tseq' : Ω' → ℕ → ℝ} {G' : ℝ≥0 → Ω' → GramState (SrcCol K' (Fin np))}
    {Kc' : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}
    (hM' : IsFiniteComplexSourceModel b E s τ m h K' entrance 𝓖' Q' tseq' G' Kc') :
    ∫ ω in entEvent tseq (capSet K h),
        Φ (modelSourceData (srcSignature K (Fin np)) (Kc (T - s).toNNReal ω)
          (G (T - s).toNNReal ω)) ∂Q =
      ∫ ω in entEvent tseq' (capSet K h),
        Φ (modelSourceData (srcSignature K' (Fin np)) (Kc' (T - s).toNNReal ω)
          (G' (T - s).toNNReal ω)) ∂Q' := by
  have hS := measurableSet_capSet K h
  have hQA := cmeasure_entEvent hM hS
  have hQA' := cmeasure_entEvent hM' hS
  by_cases h0 : entrance (capSet K h) = 0
  · rw [setIntegral_measure_zero _ (hQA.trans h0), setIntegral_measure_zero _ (hQA'.trans h0)]
  have hM1 := ccondModel hM hS h0
  have hM2 := ccapRestrict hK hM' h0
  have e0 := hU b E np τ m T hdom s hs hsτ h hh K _ Φ Ω _ 𝓖 _ _ _ _ hM1 Ω' _ 𝓖' _ _ _ _ hM2
  unfold modelExpectation at e0
  have hA' : MeasurableSet (entEvent tseq' (capSet K h)) :=
    𝓖'.le 0 _ (cmeasurableSet_entEvent hM' hS)
  have hcongr : (fun ω => Φ (modelSourceData (srcSignature K (Fin np)) (Kc' (T - s).toNNReal ω)
        (pRestrict (capEmb hK (Fin np)) G' (T - s).toNNReal ω))) =ᵐ[Q'[|entEvent tseq' (capSet K h)]]
      fun ω => Φ (modelSourceData (srcSignature K' (Fin np)) (Kc' (T - s).toNNReal ω)
        (G' (T - s).toNNReal ω)) := by
    have := hM'.prob
    refine ae_cond_of_ae_on hA' ?_
    filter_upwards [cae_gsupp_capEmb hK hM'] with ω hz hωA
    simp only [pRestrict]
    rw [modelSourceData_gRestrict hK _ (hz hωA _)]
  rw [integral_congr_ae hcongr] at e0
  have hfin : entrance (capSet K h) ≠ ∞ := by
    rw [← hQA]
    have := hM.prob
    exact measure_ne_top _ _
  have hc : ((entrance (capSet K h))⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 hfin, ENNReal.inv_ne_top.2 h0⟩
  simp only [ProbabilityTheory.cond, integral_smul_measure, hQA, hQA', smul_eq_mul] at e0
  exact mul_left_cancel₀ hc e0

/-- The tail of one model: `|∫_{Aᶜ} Φ| ≤ ‖Φ‖ P(t_K > h²)`. -/
theorem abs_setIntegral_compl_le {Ω : Type*} [MeasurableSpace Ω]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Q : Measure Ω} {tseq : Ω → ℕ → ℝ} {G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin np))}
    {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hM : IsFiniteComplexSourceModel b E s τ m h K' entrance 𝓖 Q tseq G Kc)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (t : ℝ≥0) :
    |∫ ω in (entEvent tseq (capSet K h))ᶜ,
        Φ (modelSourceData (srcSignature K' (Fin np)) (Kc t ω) (G t ω)) ∂Q| ≤
      ‖Φ‖ * (entrance (capSet K h)ᶜ).toReal := by
  have := hM.prob
  have hc : Q (entEvent tseq (capSet K h))ᶜ = entrance (capSet K h)ᶜ :=
    cmeasure_entEvent hM (measurableSet_capSet K h).compl
  have := norm_setIntegral_le_of_norm_le_const (μ := Q) (s := (entEvent tseq (capSet K h))ᶜ)
    (C := ‖Φ‖) (measure_lt_top _ _)
    (f := fun ω => Φ (modelSourceData (srcSignature K' (Fin np)) (Kc t ω) (G t ω)))
    (fun ω _ => Φ.norm_coe_le_norm _)
  rwa [Real.norm_eq_abs, measureReal_def, hc] at this

/-- **`|Ψ(K) − Ψ(K')| ≤ 2‖Φ‖ P(t_K > h²)`** for `K ≤ K'`. -/
theorem abs_value_sub_le (hU : ComplexFiniteUniqueness) (hdom : ComplexSourceLawDomain b E τ m T)
    (hs : 0 < s) (hsτ : ∀ j, s < τ j) (hh : 0 < h)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (hK : K ≤ K') {v v' : ℝ}
    (hv : ComplexModelValue b E s T τ m h K entrance Φ v)
    (hv' : ComplexModelValue b E s T τ m h K' entrance Φ v') :
    |v - v'| ≤ 2 * ‖Φ‖ * (entrance (capSet K h)ᶜ).toReal := by
  obtain ⟨Ω, mΩ, 𝓖, Q, tseq, G, Kc, hM⟩ := hv.1
  obtain ⟨Ω', mΩ', 𝓖', Q', tseq', G', Kc', hM'⟩ := hv'.1
  have e := hv.2 Ω mΩ 𝓖 Q tseq G Kc hM
  have e' := hv'.2 Ω' mΩ' 𝓖' Q' tseq' G' Kc' hM'
  have hS := measurableSet_capSet K h
  have hA := 𝓖.le 0 _ (cmeasurableSet_entEvent hM hS)
  have hA' := 𝓖'.le 0 _ (cmeasurableSet_entEvent hM' hS)
  have hsplit := integral_add_compl hA (integrable_final hM Φ (T - s).toNNReal)
  have hsplit' := integral_add_compl hA' (integrable_final hM' Φ (T - s).toNNReal)
  have heq := setIntegral_capSet_eq (T := T) hU hdom hs hsτ hh Φ hK hM hM'
  have b1 := abs_setIntegral_compl_le (K := K) hM Φ (T - s).toNNReal
  have b2 := abs_setIntegral_compl_le (K := K) hM' Φ (T - s).toNNReal
  rw [← e, ← e', ← hsplit, ← hsplit', heq, add_sub_add_left_eq_sub]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add b1 b2
    _ = _ := by ring

end BlockBand.SourceProcess.ComplexCapLimit
