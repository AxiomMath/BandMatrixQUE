module

public import BlockBand.Transmission.DualLift.LOne

/-!
# The `dualMartingale` of the lifted realization is a martingale

**`martingale_dualMartingale₂`**: for `f ∈ C_c^∞(𝒞₁)` (`ContDiff ℝ ⊤`, compact support,
`tsupport f ⊆ 𝒞₁`), `dualMartingale D₀ 1 f N₂ X₂ Y₂` is an `L𝓖 μ`-martingale under `LP μ`.
It is `L𝓖 μ t`-measurable at every `ω` as an everywhere limit (on `good₂` of `Mraw n`, off
`good₂` the constant-start value `−t 𝒟₁f(π ξ)`), bounded by `2C + C_L t`, and the martingale
identity passes to the limit by dominated convergence. This is the analogue of
`martingale_dualMartingale` at boundary and random starts.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Transmission
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ) {f : DualCoord 1 → ℝ}

/-- **The martingale clause** of the realization. -/
theorem martingale_dualMartingale₂ (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ dualChamber 1) :
    Martingale (dualMartingale D0 1 f F.N₂ F.X₂ F.Y₂) (L𝓖 μ) (LP μ) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
  have hFc : ContDiff ℝ 2 (liftFc f) := hf2.comp (ofFlat 1).contDiff
  have hLc : Continuous (liftLc f D0) :=
    (continuous_dualGenerator D0 hf2 hfs).comp (ofFlat 1).continuous
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨CL', hCL'⟩ := (hasCompactSupport_dualGenerator D0 hfc).exists_bound_of_continuous
    (continuous_dualGenerator D0 hf2 hfs)
  set CL := max CL' 0
  have hCL0 : 0 ≤ CL := le_max_right _ _
  have hCw : ∀ w, |liftFc f w| ≤ C := fun w => by rw [← Real.norm_eq_abs]; exact hC _
  have hCLw : ∀ w, |liftLc f D0 w| ≤ CL := fun w => by
    rw [← Real.norm_eq_abs]; exact (hCL' _).trans (le_max_left _ _)
  set D := dualMartingale D0 1 f F.N₂ F.X₂ F.Y₂ with hDdef
  have hmart : ∀ n, HasMartingaleModification (LP μ) (L𝓖 μ) (F.Mraw f n) := fun n => by
    have h := F.hasMart_G hD0 hξ n hFc.continuous.measurable hFc.contDiffOn
      (by rw [L₁_liftFc f hf2]; exact hLc.continuousOn)
    rw [L₁_liftFc f hf2] at h
    exact h
  choose M hM hMe using hmart
  have hlim : ∀ t, ∀ᵐ ω ∂LP μ, Tendsto (fun n => M n t ω) atTop (𝓝 (D t ω)) := fun t => by
    filter_upwards [F.ae_good₂ hD0 hξ, ae_all_iff.2 fun n => hMe n t] with ω hω hn
    exact tendsto_const_nhds.congr' ((F.eventually_Mraw₂ hξ hfs hω t).mono fun n h =>
      ((hn n).trans h).symm)
  have hbd : ∀ t n, ∀ᵐ ω ∂LP μ, ‖M n t ω‖ ≤ 2 * C + CL * t := fun t n => by
    filter_upwards [hMe n t] with ω h
    rw [h, Real.norm_eq_abs]; exact F.abs_Mraw_le hCw hCL0 hCLw n t ω
  have hoff : ∀ t ω, ω ∉ F.good₂ →
      D t ω = -∫ u in Ioc (0 : ℝ) t, liftLc f D0 (liftProj (ξ ω)) := fun t ω hω => by
    have hN : ∀ s, F.N₂ s ω = 1 := fun s => by simp [N₂, hω]
    have hZ : ∀ s, F.Z₂ s ω = liftProj (ξ ω) := fun s => by simp [Z₂, hω]
    rw [hDdef, F.dualMartingale_eq₂ f]
    simp only [hN, hZ, ite_true, sub_self, zero_sub]
  have hadp : ∀ t, StronglyMeasurable[L𝓖 μ t] (D t) := fun t => by
    classical
    have hprog : ∀ n, IsStronglyProgressive (L𝓖 μ)
        (fun s ω => switchOff (F.e n) (fun t ω => liftLc f D0 (F.Yf n t ω)) s ω) := fun n r => by
      have h := (F.isCSM_G hD0 hξ n hFc.continuous.measurable hFc.contDiffOn).drift_progressive r
      rw [L₁_liftFc f hf2] at h
      simpa [Function.comp_def] using (continuous_apply (0 : Fin 1)).comp_stronglyMeasurable h
    have hYm : ∀ n (s : ℝ≥0), s ≤ t → Measurable[L𝓖 μ t] fun ω => liftFc f (F.Yf n s ω) :=
      fun n s hs => hFc.continuous.measurable.comp
        ((F.measurable_Yf hD0 hξ n s).mono ((L𝓖 μ).mono hs) le_rfl)
    have hoffm : StronglyMeasurable[L𝓖 μ t]
        (fun ω => -∫ u in Ioc (0 : ℝ) t, liftLc f D0 (liftProj (ξ ω))) := by
      simp only [integral_const, smul_eq_mul]
      exact (((hLc.measurable.comp (measurable_start hξ t)).const_mul
        ((volume.restrict (Ioc (0 : ℝ) t)).real univ)).neg).stronglyMeasurable
    have hg : ∀ n, StronglyMeasurable[L𝓖 μ t] (fun ω => if ω ∈ F.good₂ then F.Mraw f n t ω
        else -∫ u in Ioc (0 : ℝ) t, liftLc f D0 (liftProj (ξ ω))) := fun n =>
      StronglyMeasurable.ite (F.measurableSet_good₂_aug hD0 hξ t)
        ((((hYm n t le_rfl).sub (hYm n 0 zero_le)).stronglyMeasurable).sub
          (SemimartingaleIto.stronglyMeasurable_integral_of_progressive (hprog n) t))
        hoffm
    refine stronglyMeasurable_of_tendsto atTop hg (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ F.good₂
    · exact tendsto_const_nhds.congr' ((F.eventually_Mraw₂ hξ hfs hω t).mono fun n h => by
        simp only [hω, ite_true, h, hDdef])
    · simp only [hω, ite_false, hoff t ω hω]; exact tendsto_const_nhds
  have hDbd : ∀ t, ∀ᵐ ω ∂LP μ, ‖D t ω‖ ≤ 2 * C + CL * t := fun t => by
    filter_upwards [hlim t, ae_all_iff.2 (hbd t)] with ω h1 h2
    exact le_of_tendsto' (continuous_norm.tendsto _ |>.comp h1) h2
  have hint : ∀ t, Integrable (D t) (LP μ) := fun t =>
    Integrable.mono' (integrable_const _) ((hadp t).mono ((L𝓖 μ).le t)).aestronglyMeasurable
      (hDbd t)
  have hset : ∀ u v : ℝ≥0, u ≤ v → ∀ B, MeasurableSet[L𝓖 μ u] B →
      ∫ ω in B, D v ω ∂LP μ = ∫ ω in B, D u ω ∂LP μ := fun u v huv B hB => by
    have hDCT : ∀ t, Tendsto (fun n => ∫ ω in B, M n t ω ∂LP μ) atTop
        (𝓝 (∫ ω in B, D t ω ∂LP μ)) :=
      fun t => tendsto_integral_of_dominated_convergence (fun _ => 2 * C + CL * t)
        (fun n => ((hM n).integrable t).1.restrict) (integrable_const _)
        (fun n => ae_restrict_of_ae (hbd t n)) (ae_restrict_of_ae (hlim t))
    exact tendsto_nhds_unique ((hDCT v).congr fun n => ((hM n).setIntegral_eq huv hB).symm)
      (hDCT u)
  exact ⟨hadp, fun i j hij => (ae_eq_condExp_of_forall_setIntegral_eq ((L𝓖 μ).le i) (hint j)
    (fun _ _ _ => (hint i).integrableOn) (fun s hs _ => (hset i j hij s hs).symm)
    (hadp i).aestronglyMeasurable).symm⟩

end LiftFamily

end BlockBand.Transmission.DualLift
