module

public import BlockBand.SourceProcess.ClosedSumProof.ClosedErrs

/-!
# The window inputs of `closed_modulus_fixed` from `ClosedSummed` and `ClosedFourth`

**`window_errs`**: if at width `W` the error `closedSummedErr … e (swapE e)` and the fourth
moment `closedFourthErr … e` are at most `ε`, then on every window `n_s ≤ j₁`, `j₁ + L ≤ ⌊WT⌋`
the fourth moments and the three error integrands are integrable and all four window sums are
at most `max ε 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum
open scoped ENNReal

variable {W p K M : ℕ} {b E s T h : ℝ} {q : Fin p → ℝ → ℝ} {R : ℝ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M))

/-- The fourth-moment integrand on the window. -/
def phi4 (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) (j₁ L k : ℕ)
    (y : SampledPath W p M × ℝ) : ℝ :=
  if k < L then ‖(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
    zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) y‖ ^ 4 else 0

theorem measurable_zc_full (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j : ℕ}
    (hj : closeLen s W ≤ j) : Measurable (zc (M := M) b E s T h q W Vs e j) :=
  (measurable_zc e hVs hj).mono (closedSigma_le j) le_rfl

theorem measurableSet_am_full (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j : ℕ}
    (hj : closeLen s W ≤ j) : MeasurableSet (am (M := M) b E s T h q R W Vs j) :=
  closedSigma_le j _ (measurableSet_am hVs hj)

theorem am_ae_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hq : ∀ i x, 0 ≤ q i x) (j : ℕ) :
    closedAlive (M := M) b E s T h q R W j Vs ∩ noBirth j =ᵐ[lawW b T q M W]
      am b E s T h q R W Vs j :=
  (closedAlive_ae_eq hb hE1 hE2 s T h hq _ R j Vs).inter (Filter.EventuallyEq.refl _ _)

theorem bm_ae_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hq : ∀ i x, 0 ≤ q i x) (j : ℕ) :
    closedAlive (M := M) b E s T h q R W j Vs \ noBirth j =ᵐ[lawW b T q M W]
      bm b E s T h q R W Vs j :=
  (closedAlive_ae_eq hb hE1 hE2 s T h hq _ R j Vs).diff (Filter.EventuallyEq.refl _ _)

/-- **The window inputs.** -/
theorem window_errs (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hq : ∀ i x, 0 ≤ q i x)
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j₁ L N ℓ : ℕ}
    (hj₁ : closeLen s W ≤ j₁) (hL : j₁ + L ≤ ⌊(W : ℝ) * T⌋₊) (hNL : L ≤ N * ℓ) {ε : ℝ}
    (hS : closedSummedErr b E s T h q R W Vs e (swapE e) ≤ ENNReal.ofReal ε)
    (hF : closedFourthErr b E s T h q R W Vs e ≤ ENNReal.ofReal ε) :
    (∀ k < L, Integrable (phi4 b E s T h q R W Vs e j₁ L k) (lawW b T q M W)) ∧
    (∀ k < L, Integrable (fErr b E s T h q R W Vs e j₁ L k) (lawW b T q M W)) ∧
    (∀ k < L, Integrable (gErr b E s T h q R W Vs e j₁ L k) (lawW b T q M W)) ∧
    (∀ k < L, Integrable (betaErr b E s T h q R W Vs e j₁ L k) (lawW b T q M W)) ∧
    ∑ i ∈ range (N * ℓ), ∫ y, phi4 b E s T h q R W Vs e j₁ L i y ∂lawW b T q M W ≤ max ε 0 ∧
    ∑ i ∈ range (N * ℓ), ∫ y, fErr b E s T h q R W Vs e j₁ L i y ∂lawW b T q M W ≤ max ε 0 ∧
    ∑ i ∈ range (N * ℓ), ∫ y, gErr b E s T h q R W Vs e j₁ L i y ∂lawW b T q M W ≤ max ε 0 ∧
    ∑ i ∈ range (N * ℓ), ∫ y, betaErr b E s T h q R W Vs e j₁ L i y ∂lawW b T q M W ≤
      max ε 0 := by
  set μ := lawW b T q M W
  set steps := Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊
  have hs : ∀ i < L, j₁ + i ∈ steps := fun i hi => Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hjs : ∀ i < L, closeLen s W ≤ j₁ + i := fun i _ => by omega
  rw [closedSummedErr_eq] at hS
  have hS1 := le_trans (le_trans le_self_add le_self_add) hS
  have hS2 := le_trans (le_trans le_add_self le_self_add) hS
  have hS3 := le_trans le_add_self hS
  -- the four families
  set Ug : ℕ → SampledPath W p M × ℝ → ℂ := fun j => (am b E s T h q R W Vs j).indicator fun y =>
    μ[(am b E s T h q R W Vs j).indicator (fun y => zc b E s T h q W Vs e (j + 1) y -
      zc b E s T h q W Vs e j y) | closedSigma W j p M] y - (W : ℂ)⁻¹ * gramDriftEntry
        (transportD0 b E) (srcSignature K (Fin p × Fin M)) e (closedGramAt b E s T h q W j Vs y)
  set Uf : ℕ → SampledPath W p M × ℝ → ℂ := fun j => (am b E s T h q R W Vs j).indicator fun y =>
    μ[(am b E s T h q R W Vs j).indicator (fun y => (zc b E s T h q W Vs e (j + 1) y -
      zc b E s T h q W Vs e j y) * (zc b E s T h q W Vs (swapE e) (j + 1) y -
        zc b E s T h q W Vs (swapE e) j y)) | closedSigma W j p M] y - (W : ℂ)⁻¹ *
      gramCovEntry (transportD0 b E) (srcSignature K (Fin p × Fin M)) e (swapE e)
        (closedGramAt b E s T h q W j Vs y)
  set Ub : ℕ → SampledPath W p M × ℝ → ℂ := fun j => (bm b E s T h q R W Vs j).indicator fun y =>
    gramEntry e (closedGramAt b E s T h q W (j + 1) Vs y - closedGramAt b E s T h q W j Vs y -
      birthAt b s T q j y)
  set U4 : ℕ → SampledPath W p M × ℝ → ℂ := fun j y => ((‖(am b E s T h q R W Vs j).indicator
    (fun y => zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) y‖ ^ 4 : ℝ) : ℂ)
  have hGm : ∀ {j}, closeLen s W ≤ j → Measurable (closedGramAt (M := M) b E s T h q W j Vs) :=
    fun hj => (measurable_closedGramAt_past b E s T h q hj hVs).mono (closedSigma_le _) le_rfl
  have hUg : ∀ i < L, AEStronglyMeasurable (Ug (j₁ + i)) μ := fun i hi =>
    ((stronglyMeasurable_condExp.mono (closedSigma_le _)).aestronglyMeasurable.sub
      (((measurable_drift_comp _ _ e (hGm (hjs i hi))).const_mul
        _).aestronglyMeasurable)).indicator (measurableSet_am_full hVs (hjs i hi))
  have hUf : ∀ i < L, AEStronglyMeasurable (Uf (j₁ + i)) μ := fun i hi =>
    ((stronglyMeasurable_condExp.mono (closedSigma_le _)).aestronglyMeasurable.sub
      (((measurable_cov_comp _ _ e _ (hGm (hjs i hi))).const_mul
        _).aestronglyMeasurable)).indicator (measurableSet_am_full hVs (hjs i hi))
  have hUb : ∀ i < L, AEStronglyMeasurable (Ub (j₁ + i)) μ := fun i hi => by
    have e1 : (fun y => gramEntry e (closedGramAt b E s T h q W (j₁ + i + 1) Vs y -
        closedGramAt b E s T h q W (j₁ + i) Vs y - birthAt b s T q (j₁ + i) y)) = fun y =>
        zc b E s T h q W Vs e (j₁ + i + 1) y - zc b E s T h q W Vs e (j₁ + i) y -
          gramEntry e (birthAt b s T q (j₁ + i) y) := by
      funext y; simp only [zc, gramEntry_sub]
    have hbm : MeasurableSet (bm (M := M) b E s T h q R W Vs (j₁ + i)) :=
      closedSigma_le _ _ ((measurableSet_aliveM b E s T h q R (hjs i hi) hVs).diff
        (measurableSet_noBirth _))
    refine AEStronglyMeasurable.indicator ?_ hbm
    rw [e1]
    exact ((((measurable_zc_full e hVs (by omega)).sub (measurable_zc_full e hVs (hjs i hi))).sub
      (measurable_gramEntry_birthAt e b s T q _))).aestronglyMeasurable
  have hU4 : ∀ i < L, AEStronglyMeasurable (U4 (j₁ + i)) μ := fun i hi =>
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((aestronglyMeasurable_step e hVs (hjs i hi) μ).norm.pow 4)
  -- the lintegral identifications
  have hEg : ∑ j ∈ steps, ∫⁻ y, ‖Ug j y‖ₑ ∂μ ≤ ENNReal.ofReal ε := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hS1
    exact (lintegral_condErr_congr (am_ae_eq hb hE1 hE2 hq j) _ _).symm
  have hEf : ∑ j ∈ steps, ∫⁻ y, ‖Uf j y‖ₑ ∂μ ≤ ENNReal.ofReal ε := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hS2
    exact (lintegral_condErr_congr (am_ae_eq hb hE1 hE2 hq j) _ _).symm
  have hEb : ∑ j ∈ steps, ∫⁻ y, ‖Ub j y‖ₑ ∂μ ≤ ENNReal.ofReal ε := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hS3
    refine lintegral_congr_ae ?_
    filter_upwards [indicator_ae_eq_of_ae_eq_set (f := fun y => gramEntry e
      (closedGramAt b E s T h q W (j + 1) Vs y - closedGramAt b E s T h q W j Vs y -
        birthAt b s T q j y)) (bm_ae_eq hb hE1 hE2 hq j)] with y hy
    rw [hy]
  have hE4 : ∑ j ∈ steps, ∫⁻ y, ‖U4 j y‖ₑ ∂μ ≤ ENNReal.ofReal ε := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hF
    rw [lintegral_indicator_congr (am_ae_eq hb hE1 hE2 hq j)]
    refine lintegral_congr fun y => ?_
    simp only [U4]
    rw [← enorm_norm, Complex.norm_real, enorm_norm, enorm_pow, enorm_norm]
    rfl
  -- the windows
  have hzero : ∀ {φ : ℕ → ℕ → SampledPath W p M × ℝ → ℝ}, (∀ k y, φ k y = if k < L then
      φ k y else 0) → ∀ k, ¬ k < L → φ k = 0 := fun h k hk => by
    funext y; rw [h k y, ite_eq_right hk]; rfl
  obtain ⟨i4, s4⟩ := window_of_steps U4 steps j₁ L N ℓ hU4 hs hNL hE4
    (phi4 b E s T h q R W Vs e j₁ L) (fun k hk => funext fun y => by
      simp only [phi4, ite_eq_left hk, U4, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_of_nonneg (by positivity)).symm)
    (fun k hk => funext fun y => by simp only [phi4, ite_eq_right hk, Pi.zero_apply])
  obtain ⟨ig, sg⟩ := window_of_steps Ug steps j₁ L N ℓ hUg hs hNL hEg
    (gErr b E s T h q R W Vs e j₁ L) (fun k hk => funext fun y => by
      simp only [gErr, ite_eq_left hk, Ug, ofReal_inv_natCast]; rfl)
    (fun k hk => funext fun y => by simp only [gErr, ite_eq_right hk, Pi.zero_apply])
  obtain ⟨if', sf⟩ := window_of_steps Uf steps j₁ L N ℓ hUf hs hNL hEf
    (fErr b E s T h q R W Vs e j₁ L) (fun k hk => funext fun y => by
      simp only [fErr, ite_eq_left hk, Uf, ofReal_inv_natCast]; rfl)
    (fun k hk => funext fun y => by simp only [fErr, ite_eq_right hk, Pi.zero_apply])
  obtain ⟨ib, sb⟩ := window_of_steps Ub steps j₁ L N ℓ hUb hs hNL hEb
    (betaErr b E s T h q R W Vs e j₁ L) (fun k hk => funext fun y => by
      simp only [betaErr, ite_eq_left hk, Ub])
    (fun k hk => funext fun y => by simp only [betaErr, ite_eq_right hk, Pi.zero_apply])
  exact ⟨i4, if', ig, ib, s4, sf, sg, sb⟩

end BlockBand.SourceProcess.ClosedSumProof
