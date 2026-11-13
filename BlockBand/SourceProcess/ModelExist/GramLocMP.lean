module

public import BlockBand.SourceProcess.ModelExist.GramLoc
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.MartingaleTools

/-!
# The Gram martingale problem gives complex `LocMart`s

* `cLocMart_of_mm`: a progressive, a.s. continuous complex `Z` with `Z₀ = 0` whose compensated
  process `Z − ∫β` has martingale modifications along a localizing sequence is a `CLocMart`.
* `gramLoc_drift`, `gramLoc_bracket`: the instances for a progressive Gram martingale-problem
  solution.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  SourceSDE.frobBorelSpace SourceSDE.matrixPseudoMetrizable

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem continuous_setIntegral_Ioc_C {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, f s := by
  have := (intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable (μ := volume) a b) 0).comp
    NNReal.continuous_coe
  refine this.congr fun t => ?_
  exact intervalIntegral.integral_of_le t.2

theorem hmm_re {X : ℝ≥0 → Ω → ℂ} (h : HasMartingaleModification Q 𝓖 X) :
    HasMartingaleModification Q 𝓖 (fun t ω => (X t ω).re) := by
  obtain ⟨M, hM, hMX⟩ := h
  refine ⟨fun t ω => Complex.reCLM (M t ω), martingale_clm hM _, fun t => ?_⟩
  filter_upwards [hMX t] with ω h
  simp only [Complex.reCLM_apply, h]

theorem hmm_im {X : ℝ≥0 → Ω → ℂ} (h : HasMartingaleModification Q 𝓖 X) :
    HasMartingaleModification Q 𝓖 (fun t ω => (X t ω).im) := by
  obtain ⟨M, hM, hMX⟩ := h
  refine ⟨fun t ω => Complex.imCLM (M t ω), martingale_clm hM _, fun t => ?_⟩
  filter_upwards [hMX t] with ω h
  simp only [Complex.imCLM_apply, h]

/-- A complex `LocMart` from martingale modifications of the compensated process. -/
theorem cLocMart_of_mm {Z β : ℝ≥0 → Ω → ℂ} (hp : IsStronglyProgressive 𝓖 Z)
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω)
    (hi : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => β s.toNNReal ω) (Ioc 0 t))
    (hZ0 : ∀ ω, Z 0 ω = 0) (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ n, IsStoppingTime 𝓖 (τ n))
    (hl : ∀ᵐ ω ∂Q, Tendsto (fun n => τ n ω) atTop (𝓝 ⊤))
    (hm : ∀ n, HasMartingaleModification Q 𝓖
      (stoppedProcess (fun t ω => Z t ω - ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω) (τ n))) :
    CLocMart Q 𝓖 Z β := by
  refine ⟨⟨IsStronglyProgressive.re' hp, hc.mono fun ω h => Complex.continuous_re.comp h,
    hi.mono fun ω h t => (h t).re, τ, hτ, hl, fun n => ?_⟩,
    ⟨IsStronglyProgressive.im' hp, hc.mono fun ω h => Complex.continuous_im.comp h,
    hi.mono fun ω h t => (h t).im, τ, hτ, hl, fun n => ?_⟩⟩
  · have h1 : HasMartingaleModification Q 𝓖 (stoppedProcess
        (fun t ω => (Z t ω - ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω).re) (τ n)) := hmm_re (hm n)
    refine hmm_congr h1 ?_
    filter_upwards [hi] with ω h t
    simp only [locComp, hZ0, Complex.zero_re, sub_zero, Complex.sub_re]
    congr 1
    exact integral_re (h t)
  · have h1 : HasMartingaleModification Q 𝓖 (stoppedProcess
        (fun t ω => (Z t ω - ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω).im) (τ n)) := hmm_im (hm n)
    refine hmm_congr h1 ?_
    filter_upwards [hi] with ω h t
    simp only [locComp, hZ0, Complex.zero_im, sub_zero, Complex.sub_im]
    congr 1
    exact integral_im (h t)

variable {c : Type*} [Fintype c] [DecidableEq c] {D0 : ℝ} {D : Matrix c c ℂ}
  {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ}

omit [MeasurableSpace Ω] [DecidableEq c] in
theorem gramCompensated_zero (D0 : ℝ) (D : Matrix c c ℂ)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (e : Fin 2 × c × c) (ω : Ω) :
    gramCompensated D0 D G e 0 ω = 0 := by
  simp [gramCompensated]

omit [MeasurableSpace Ω] [DecidableEq c] in
theorem continuous_gramCompensated {ω : Ω} (hc : Continuous fun t => G t ω)
    (e : Fin 2 × c × c) : Continuous fun t => gramCompensated D0 D G e t ω :=
  (((continuous_gramEntry e).comp hc).sub continuous_const).sub
    (continuous_setIntegral_Ioc_C (((continuous_gramDriftEntry D0 D e).comp hc).comp
      continuous_real_toNNReal))

omit [MeasurableSpace Ω] [Fintype c] [DecidableEq c] in
theorem integrableOn_comp_path {ω : Ω} (hc : Continuous fun t => G t ω)
    {g : Matrix c c ℂ × Matrix c c ℂ → ℂ} (hg : Continuous g) (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ => g (G s.toNNReal ω)) (Ioc 0 t) :=
  (((hg.comp hc).comp continuous_real_toNNReal).integrableOn_Icc).mono_set Ioc_subset_Icc_self

section Sol
variable [IsProbabilityMeasure Q] (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
  (hp : IsStronglyProgressive 𝓖 G)
include hG hp

omit [DecidableEq c] [IsProbabilityMeasure Q] hp in
/-- Martingale modifications at the trace stops transfer to the raw hitting times. -/
theorem hmm_trHit {X : ℝ≥0 → Ω → ℂ} (n : ℕ)
    (h : ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
      N t =ᵐ[Q] stoppedProcess X (gramTraceStop G n) t) :
    HasMartingaleModification Q 𝓖 (stoppedProcess X (trHit G n)) := by
  obtain ⟨N, hN, hNX⟩ := h
  refine ⟨N, hN, fun t => ?_⟩
  filter_upwards [hNX t, trHit_ae hG n] with ω h1 h2
  rw [h1]
  simp only [stoppedProcess_eq_stopTime, h2]

omit [DecidableEq c] [IsProbabilityMeasure Q] in
/-- **Compensated Gram coordinates are complex `LocMart`s with drift `0`.** -/
theorem gramLoc_drift (e : Fin 2 × c × c) :
    CLocMart Q 𝓖 (gramCompensated D0 D G e) (fun _ _ => 0) := by
  refine cLocMart_of_mm (isStronglyProgressive_gramCompensated (hG.adapted 0) hp e)
    (hG.continuous.mono fun ω h => continuous_gramCompensated h e)
    (ae_of_all _ fun ω t => integrableOn_zero) (gramCompensated_zero D0 D G e) (trHit G)
    (isStoppingTime_trHit hG) (tendsto_trHit hG) fun n => ?_
  simpa only [integral_zero, sub_zero] using hmm_trHit hG n (hG.drift n e)

omit [DecidableEq c] [IsProbabilityMeasure Q] in
/-- **Products of compensated Gram coordinates are complex `LocMart`s with drift `Γ`.** -/
theorem gramLoc_bracket (e e' : Fin 2 × c × c) :
    CLocMart Q 𝓖 (fun t ω => gramCompensated D0 D G e t ω * gramCompensated D0 D G e' t ω)
      (fun s ω => gramCovEntry D0 D e e' (G s ω)) := by
  have hpe := isStronglyProgressive_gramCompensated (D0 := D0) (D := D) (hG.adapted 0) hp e
  have hpe' := isStronglyProgressive_gramCompensated (D0 := D0) (D := D) (hG.adapted 0) hp e'
  refine cLocMart_of_mm (fun T => (hpe T).mul (hpe' T))
    (hG.continuous.mono fun ω h => (continuous_gramCompensated h e).mul
      (continuous_gramCompensated h e'))
    (hG.continuous.mono fun ω h t => integrableOn_comp_path h (continuous_gramCovEntry D0 D e e') t)
    (fun ω => by simp only [gramCompensated_zero, zero_mul]) (trHit G)
    (isStoppingTime_trHit hG) (tendsto_trHit hG) fun n => hmm_trHit hG n (hG.bracket n e e')

end Sol

end BlockBand.SourceProcess.ModelExist
