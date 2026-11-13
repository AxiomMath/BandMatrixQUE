module
public import BlockBand.SourceProcess.Stochastic.Integral.Dyadic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopping at a bounded augmented stopping time

Measure `driverLaw μ` (sample space) and `dt ⊗ driverLaw μ` on `(0,T]` (integrands); augmented
filtration `F_t ∨ N`. Let `σ ≤ u` be a finite random time with `{σ ≤ t} ∈ F_t ∨ N` for all `t`,
and `g` an integrand with draft continuous representative `X`. Then `g · 1{s ≤ σ}` is an
integrand and `X_σ` equals its terminal integral a.s.

Proof: the dyadic upper approximations `ρ_n = dyadicUp n σ` are grid-valued augmented
stopping times bounded by `dyadicUp n u`, so `stopped_grid_identity` applies. As `n → ∞`,
`g 1{s ≤ ρ_n} → g 1{s ≤ σ}` pointwise with domination by `|g|`, hence in `L²(dt ⊗ P)`
(this also gives predictable measurability of the limit, `lpMeas` being closed); by the
isometry the terminal integrals converge in `L²(P)`, hence in measure, while
`X_{ρ_n} → X_σ` a.s. by path continuity.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

omit [MeasurableSpace S] [Fintype κ] in
/-- Pointwise convergence of the dyadically stopped integrands. -/
theorem tendsto_stopFn_dyadic (σ : DriverSample S κ → ℝ≥0) (g : κ → ℝ × DriverSample S κ → ℝ)
    (a : κ) (p : ℝ × DriverSample S κ) :
    Tendsto (fun n => stopFn (fun x => dyadicUp n (σ x)) g a p) atTop
      (𝓝 (stopFn σ g a p)) := by
  by_cases hp : p.1.toNNReal ≤ σ p.2
  · have he (n : ℕ) : stopFn (fun x => dyadicUp n (σ x)) g a p = stopFn σ g a p := by
      simp only [stopFn, hp, hp.trans (le_dyadicUp n (σ p.2)), ite_true]
    simp only [he]
    exact tendsto_const_nhds
  · have hev : ∀ᶠ n in atTop, dyadicUp n (σ p.2) < p.1.toNNReal :=
      (tendsto_dyadicUp (σ p.2)).eventually (gt_mem_nhds (lt_of_not_ge hp))
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    simp only [stopFn, hp, not_le.2 hn, ite_false]

omit [MeasurableSpace S] [Fintype κ] in
theorem stopFn_diff_sq_le (ρ σ : DriverSample S κ → ℝ≥0) (g : κ → ℝ × DriverSample S κ → ℝ)
    (a : κ) (p : ℝ × DriverSample S κ) :
    ‖(stopFn ρ g a p - stopFn σ g a p) ^ 2‖ ≤ (g a p) ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold stopFn
  split_ifs <;> simp <;> positivity

variable [DecidableEq κ]

/-- **Stopped identity at a bounded augmented stopping time.** -/
theorem stopped_identity_of_bounded {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) {σ : DriverSample S κ → ℝ≥0} {u : ℝ≥0} (hσu : ∀ x, σ x ≤ u)
    (hσ : ∀ t : ℝ≥0, MeasurableSet[driverAugmented (κ := κ) μ t] {x | σ x ≤ t}) :
    ∃ hs : NativeIntegrand μ T (stopFn σ g),
      (fun x => nativeAdaptedLimit μ T hg.family (σ x) x) =ᵐ[driverLaw (κ := κ) μ]
        (nativeIntegralOf hs : DriverSample S κ → ℝ) := by
  let ν := timeProbMeasure T (driverLaw (κ := κ) μ)
  let ρ : ℕ → DriverSample S κ → ℝ≥0 := fun n x => dyadicUp n (σ x)
  have hgrid (n : ℕ) (x : DriverSample S κ) : ∃ m : ℕ, ρ n x = m * dyadicStep n := ⟨_, rfl⟩
  have hρ (n N : ℕ) : MeasurableSet[driverAugmented (κ := κ) μ (N * dyadicStep n)]
      {x | ρ n x ≤ N * dyadicStep n} := by
    have he : {x | ρ n x ≤ N * dyadicStep n} = {x | σ x ≤ N * dyadicStep n} := by
      ext x
      exact dyadicUp_le_iff n N (σ x)
    rw [he]
    exact hσ _
  have hmin (n : ℕ) (x : DriverSample S κ) :
      min (ρ n x) ((⌈u / dyadicStep n⌉₊ : ℕ) * dyadicStep n) = ρ n x :=
    min_eq_left (dyadicUp_mono n (hσu x))
  choose F hF hI using fun n => stopped_grid_identity hg (hgrid n) (hρ n) ⌈u / dyadicStep n⌉₊
  have hF' (n : ℕ) (a : κ) : (((F n a : ScalarPredictable (κ := κ) μ T) :
      Lp ℝ 2 ν) : ℝ × DriverSample S κ → ℝ) =ᵐ[ν] stopFn (ρ n) g a := by
    simpa only [hmin] using hF n a
  have hI' (n : ℕ) : (fullNativeIntegral (κ := κ) μ T (F n) : DriverSample S κ → ℝ)
      =ᵐ[driverLaw (κ := κ) μ] fun x => nativeAdaptedLimit μ T hg.family (ρ n x) x := by
    simpa only [hmin] using hI n
  have hGmem (n : ℕ) (a : κ) : MemLp (stopFn (ρ n) g a) 2 ν := (Lp.memLp _).ae_eq (hF' n a)
  have hG0aesm (a : κ) : AEStronglyMeasurable (stopFn σ g a) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hGmem n a).aestronglyMeasurable)
      (ae_of_all _ (tendsto_stopFn_dyadic σ g a))
  have hG0mem (a : κ) : MemLp (stopFn σ g a) 2 ν :=
    MemLp.of_le (hg a).2 (hG0aesm a) (ae_of_all _ fun p => by
      unfold stopFn
      split_ifs <;> simp)
  have hint (a : κ) : Tendsto (fun n => ∫ p, (stopFn (ρ n) g a p - stopFn σ g a p) ^ 2 ∂ν)
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := fun n p => (stopFn (ρ n) g a p - stopFn σ g a p) ^ 2) (f := fun _ => 0)
      (fun p => (g a p) ^ 2)
      (fun n => ((hGmem n a).aestronglyMeasurable.sub (hG0aesm a)).pow 2)
      ((hg a).2.integrable_sq) (fun n => ae_of_all _ fun p => stopFn_diff_sq_le _ σ g a p)
      (ae_of_all _ fun p => by
        have ht := ((tendsto_stopFn_dyadic σ g a p).sub_const (stopFn σ g a p)).pow 2
        rw [sub_self, zero_pow two_ne_zero] at ht
        exact ht)
    simpa only [integral_zero] using h
  have hLp (a : κ) := tendsto_toLp_of_integral_sq (hGmem · a) (hG0mem a) (hint a)
  have hFeq (n : ℕ) (a : κ) : ((F n a : ScalarPredictable (κ := κ) μ T) : Lp ℝ 2 ν) =
      (hGmem n a).toLp (stopFn (ρ n) g a) :=
    Lp.ext ((hF' n a).trans (MemLp.coeFn_toLp (f := stopFn (ρ n) g a) (hGmem n a)).symm)
  have hpred (a : κ) : AEStronglyMeasurable[rawPredictable S κ] (stopFn σ g a) ν := by
    have hcl := isClosed_aestronglyMeasurable (F := ℝ) (p := 2) (μ := ν)
      (predictableSpace_le (enlargedPredictableFiltration (S := S) (κ := κ)))
    have hmem := hcl.mem_of_tendsto (hLp a) (Eventually.of_forall fun n => by
      rw [← hFeq n a]
      exact lpMeas.aestronglyMeasurable (F n a))
    exact hmem.congr (MemLp.coeFn_toLp (f := stopFn σ g a) (hG0mem a))
  let hs : NativeIntegrand μ T (stopFn σ g) := fun a => ⟨hpred a, hG0mem a⟩
  refine ⟨hs, ?_⟩
  have hFam : Tendsto F atTop (𝓝 hs.family) := by
    let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ScalarPredictable (κ := κ) μ T)
    have h1 : Tendsto (fun n => e (F n)) atTop (𝓝 (e hs.family)) := by
      rw [tendsto_pi_nhds]
      intro a
      rw [tendsto_subtype_rng]
      change Tendsto (fun n => ((F n a : ScalarPredictable (κ := κ) μ T) : Lp ℝ 2 ν)) atTop
        (𝓝 ((hG0mem a).toLp (stopFn σ g a)))
      simp_rw [hFeq]
      exact hLp a
    have h2 := (e.symm.continuous.tendsto _).comp h1
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h2
  have hItend := ((fullNativeIntegral (κ := κ) μ T).continuous.tendsto _).comp hFam
  have hmeas := (tendstoInMeasure_of_tendsto_Lp hItend).congr_left hI'
  have hae : ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto
      (fun n => nativeAdaptedLimit μ T hg.family (ρ n x) x) atTop
      (𝓝 (nativeAdaptedLimit μ T hg.family (σ x) x)) := by
    filter_upwards [nativeAdaptedLimit_continuous_all_ae μ T hg.family] with x hx
    exact (hx.tendsto (σ x)).comp (tendsto_dyadicUp (σ x))
  have hmeas2 := tendstoInMeasure_of_tendsto_ae
    (fun n => (Lp.aestronglyMeasurable (fullNativeIntegral (κ := κ) μ T (F n))).congr (hI' n)) hae
  exact tendstoInMeasure_ae_unique hmeas2 hmeas

end BlockBand.SourceProcess.Stochastic.Integral
