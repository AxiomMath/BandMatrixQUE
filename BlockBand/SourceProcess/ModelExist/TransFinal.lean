module

public import BlockBand.SourceProcess.ModelExist.TransBound
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientLocal

/-!
# From a complex `LocMart` to a stopped martingale clause

* `setIntegral_ite_ge`: `∫_0^u 1{r ≤ v} f = ∫_0^u f − ∫_0^{u∧r} f`;
* `exists_martingale_of_cLocMart`: if `Z` is a `CLocMart` with drift `β`, `Z₀ = 0`, a process `Y`
  equals `Z − ∫β` a.s., and `Y` stopped at `σ` is bounded on bounded time intervals, where `σ`
  agrees a.s. with a stopping time, then `Y^σ` has a complex martingale modification
  (`hasMartingaleModification_stopped_of_localized` for the real and imaginary parts).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

theorem setIntegral_ite_ge {f : ℝ → ℂ} (r : WithTop ℝ≥0) (u : ℝ≥0)
    (hf : IntegrableOn f (Ioc 0 u)) :
    ∫ v in Ioc (0 : ℝ) u, (if r ≤ (v.toNNReal : WithTop ℝ≥0) then f v else 0) =
      (∫ v in Ioc (0 : ℝ) u, f v) - ∫ v in Ioc (0 : ℝ) (stopTime r u), f v := by
  have hm : MeasurableSet {v : ℝ | (v.toNNReal : WithTop ℝ≥0) < r} :=
    measurableSet_lt (WithTop.measurable_coe.comp measurable_real_toNNReal) measurable_const
  have hI : IntegrableOn (fun v => if (v.toNNReal : WithTop ℝ≥0) < r then f v else 0)
      (Ioc 0 u) := by
    refine (hf.indicator hm).congr_fun (fun v _ => ?_) measurableSet_Ioc
    by_cases h : (v.toNNReal : WithTop ℝ≥0) < r
    · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) < r} from h)]
      split_ifs; rfl
    · rw [Set.indicator_of_notMem (show v ∉ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) < r} from h)]
      split_ifs; rfl
  have e1 : (fun v : ℝ => if r ≤ (v.toNNReal : WithTop ℝ≥0) then f v else 0) =
      fun v => f v - (if (v.toNNReal : WithTop ℝ≥0) < r then f v else 0) := by
    funext v
    split_ifs with h1 h2 h2
    · exact absurd h2 (not_lt.2 h1)
    · rw [sub_zero]
    · rw [sub_self]
    · exact absurd (not_le.1 h1) h2
  have e2 : ∫ v in Ioc (0 : ℝ) u, (if (v.toNNReal : WithTop ℝ≥0) < r then f v else 0) =
      ∫ v in Ioc (0 : ℝ) u, (if (v.toNNReal : WithTop ℝ≥0) ≤ r then f v else 0) := by
    refine integral_congr_ae ?_
    induction r with
    | top =>
      refine ae_of_all _ fun v => ?_
      beta_reduce
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd le_top h2
      · exact absurd (WithTop.coe_lt_top _) h1
      · rfl
    | coe r0 =>
      have hne : ∀ᵐ v ∂(volume.restrict (Ioc (0 : ℝ) u)), v ≠ (r0 : ℝ) :=
        Measure.ae_ne _ _
      filter_upwards [hne, ae_restrict_mem measurableSet_Ioc] with v hv hvI
      have hv' : v.toNNReal ≠ r0 := fun h => hv (by
        rw [← h, Real.coe_toNNReal _ hvI.1.le])
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.le h2
      · exact absurd (lt_of_le_of_ne h2 (fun h => hv' (WithTop.coe_injective h))) h1
      · rfl
  rw [e1, integral_sub hf hI, e2, setIntegral_switch]

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem hmm_part {Z β : ℝ≥0 → Ω → ℝ} (h : LocMart Q 𝓖 Z β) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime 𝓖 ρ) {σ : Ω → WithTop ℝ≥0} (hρσ : ∀ᵐ ω ∂Q, ρ ω = σ ω)
    {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ᵐ ω ∂Q, ∀ t, Y t ω = locComp Z β t ω)
    (hbd : ∀ t, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t, |stoppedProcess Y σ s ω| ≤ C) :
    HasMartingaleModification Q 𝓖 (stoppedProcess Y σ) := by
  obtain ⟨τ, -, hτl, hm⟩ := h.loc
  have h1 := hasMartingaleModification_stopped_of_localized hτl hm h.cont_comp hρ fun t => by
    obtain ⟨C, hC⟩ := hbd t
    refine ⟨C, ?_⟩
    filter_upwards [hC, hY, hρσ] with ω h1 h2 h3 s hs
    simpa only [stoppedProcess_eq_stopTime, h3, h2] using h1 s hs
  refine hmm_congr' h1 ?_
  filter_upwards [hY, hρσ] with ω h1 h2 t
  simp only [stoppedProcess_eq_stopTime, h2, h1]

/-- **A stopped martingale clause from a complex `LocMart`.** -/
theorem exists_martingale_of_cLocMart {Z β : ℝ≥0 → Ω → ℂ} (h : CLocMart Q 𝓖 Z β)
    (hZ0 : ∀ ω, Z 0 ω = 0)
    (hi : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => β s.toNNReal ω) (Ioc 0 t))
    {Y : ℝ≥0 → Ω → ℂ}
    (hY : ∀ᵐ ω ∂Q, ∀ t, Y t ω = Z t ω - ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω)
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ) (hρσ : ∀ᵐ ω ∂Q, ρ ω = σ ω)
    (hbd : ∀ t, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t, ‖stoppedProcess Y σ s ω‖ ≤ C) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t, N t =ᵐ[Q] stoppedProcess Y σ t := by
  have hre := hmm_part h.1 hρ hρσ (Y := fun t ω => (Y t ω).re) (by
    filter_upwards [hY, hi] with ω h1 h2 t
    simp only [h1, locComp, hZ0, Complex.sub_re, Complex.zero_re, sub_zero]
    congr 1
    exact (integral_re (h2 t)).symm) fun t => by
      obtain ⟨C, hC⟩ := hbd t
      exact ⟨C, by filter_upwards [hC] with ω h s hs using (Complex.abs_re_le_norm _).trans (h s hs)⟩
  have him := hmm_part h.2 hρ hρσ (Y := fun t ω => (Y t ω).im) (by
    filter_upwards [hY, hi] with ω h1 h2 t
    simp only [h1, locComp, hZ0, Complex.sub_im, Complex.zero_im, sub_zero]
    congr 1
    exact (integral_im (h2 t)).symm) fun t => by
      obtain ⟨C, hC⟩ := hbd t
      exact ⟨C, by filter_upwards [hC] with ω h s hs using (Complex.abs_im_le_norm _).trans (h s hs)⟩
  obtain ⟨M0, hM0, e0⟩ := hre
  obtain ⟨M1, hM1, e1⟩ := him
  refine ⟨fun t ω => Complex.ofRealCLM (M0 t ω) + (Complex.I • Complex.ofRealCLM) (M1 t ω),
    (martingale_clm hM0 _).add (martingale_clm hM1 _), fun t => ?_⟩
  filter_upwards [e0 t, e1 t] with ω h0 h1
  simp only [Complex.ofRealCLM_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, h0, h1]
  simp only [stoppedProcess_eq_stopTime]
  rw [mul_comm]
  exact Complex.re_add_im _

end BlockBand.SourceProcess.ModelExist
