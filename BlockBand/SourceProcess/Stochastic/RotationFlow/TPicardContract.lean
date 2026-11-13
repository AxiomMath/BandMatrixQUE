module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.TPicardProps
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Volterra contraction of the time-dependent Picard map

Time-inhomogeneous version of the Picard contraction estimate; notation of `TPicardMap`,
`Q_t(Z,Z') = picardGap Z Z' t`. For `t ≤ N`:
* drift: `E‖D_Z(t) − D_{Z'}(t)‖² ≤ K² t Q_t` (pathwise Cauchy–Schwarz);
* noise: `E|M_Z^j(t) − M_{Z'}^j(t)|² ≤ |κ| ‖ℓ_j‖² K² Q_t` (Itô isometry);
* `Q_t(ΓZ, ΓZ') ≤ L_c ∫_0^t Q_s(Z,Z') ds` (`tPicardGap_map_le`).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.NativeSDE

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (c : TLipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
  (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ)

include hξ in
/-- Drift part of the contraction. -/
theorem lintegral_tPicardDrift_sub_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0}
    (ht : t ≤ N) :
    ∫⁻ x, ‖tPicardDrift c ξ Z t x - tPicardDrift c ξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      (c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal t * picardGap Z Z' t := by
  have hmin : min t N = t := min_eq_left ht
  have hF := stronglyMeasurable_tDriftIntegrand c hξ Z
  have hF' := stronglyMeasurable_tDriftIntegrand c hξ Z'
  have hpt : ∀ x, ‖tPicardDrift c ξ Z t x - tPicardDrift c ξ Z' t x‖ₑ ^ 2 ≤
      ENNReal.ofReal t * ((c.K : ℝ≥0∞) ^ 2 *
        ∫⁻ s in Ioc 0 (t : ℝ), ‖rep Z (s, x) - rep Z' (s, x)‖ₑ ^ 2) := by
    intro x
    unfold tPicardDrift
    rw [hmin]
    have hint (W : PicardSpace (κ := κ) μ N E) (hW : StronglyMeasurable
        fun p : ℝ × DriverSample S κ => c.b p.1.toNNReal (ξ p.2 + rep W p)) :
        IntegrableOn (fun s : ℝ => c.b s.toNNReal (ξ x + rep W (s, x))) (Ioc (0 : ℝ) (t : ℝ)) :=
      (intervalIntegrable_of_bound (hW.comp_measurable measurable_prodMk_right)
        (fun s => (c.bd_b _ _).trans (le_max_left c.C 0)) 0 t).1
    have h := enorm_sq_integral_sub_le (hint Z hF) (hint Z' hF')
      (h := fun s => (c.K : ℝ≥0∞) * ‖rep Z (s, x) - rep Z' (s, x)‖ₑ) (fun s _ => by
        refine (enorm_lip_sub (c.b s.toNNReal) (c.lip_b _) _ _).trans (le_of_eq ?_)
        rw [add_sub_add_left_eq_sub])
      (((((Lp.stronglyMeasurable _).sub (Lp.stronglyMeasurable _)).comp_measurable
        measurable_prodMk_right).measurable.enorm).const_mul _).aemeasurable
    refine h.trans (le_of_eq ?_)
    simp_rw [mul_pow]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  calc ∫⁻ x, ‖tPicardDrift c ξ Z t x - tPicardDrift c ξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
      ≤ ∫⁻ x, ENNReal.ofReal t * ((c.K : ℝ≥0∞) ^ 2 *
          ∫⁻ s in Ioc 0 (t : ℝ), ‖rep Z (s, x) - rep Z' (s, x)‖ₑ ^ 2) ∂driverLaw (κ := κ) μ :=
        lintegral_mono hpt
    _ = (c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal t *
          ∫⁻ x, (∫⁻ s in Ioc 0 (t : ℝ), ‖rep Z (s, x) - rep Z' (s, x)‖ₑ ^ 2)
            ∂driverLaw (κ := κ) μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
        ring
    _ = _ := by
        congr 1
        have h := aemeasurable_gap Z Z' t
        unfold picardGap
        unfold timeProbMeasure at h ⊢
        exact (lintegral_prod_symm _ h).symm

omit [MeasurableSpace E] [BorelSpace E] in
/-- Noise part of the contraction. -/
theorem lintegral_tPicardNoise_sub_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0}
    (ht : t ≤ N) (j : Fin (Module.finrank ℝ E)) :
    ∫⁻ x, ‖tPicardNoise c hξ Z j t x - tPicardNoise c hξ Z' j t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      Fintype.card κ * (‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t) := by
  obtain ⟨hs, h1⟩ := nativeAdaptedLimit_stopped (nativeIntegrand_tPicardNoiseFun c hξ Z j)
    isStoppingTime_top t
  obtain ⟨hs', h2⟩ := nativeAdaptedLimit_stopped (nativeIntegrand_tPicardNoiseFun c hξ Z' j)
    isStoppingTime_top t
  have hst (X : ℝ≥0 → DriverSample S κ → ℝ) : stoppedProcess X (fun _ => ⊤) t = X t :=
    funext fun _ => stoppedProcess_eq_of_le le_top
  rw [hst] at h1 h2
  have hJ : (fun x => tPicardNoise c hξ Z j t x - tPicardNoise c hξ Z' j t x)
      =ᵐ[driverLaw (κ := κ) μ]
      (nativeIntegralOf (nativeIntegrand_sub hs hs') : DriverSample S κ → ℝ) := by
    rw [nativeIntegralOf_sub hs hs']
    filter_upwards [h1, h2, Lp.coeFn_sub (nativeIntegralOf hs) (nativeIntegralOf hs')] with
      x hx1 hx2 hx3
    rw [hx3, Pi.sub_apply, ← hx1, ← hx2]
    rfl
  have hJ' : (fun x => ‖tPicardNoise c hξ Z j t x - tPicardNoise c hξ Z' j t x‖ₑ ^ 2)
      =ᵐ[driverLaw (κ := κ) μ] fun x =>
        ‖(nativeIntegralOf (nativeIntegrand_sub hs hs') : DriverSample S κ → ℝ) x‖ₑ ^ 2 := by
    filter_upwards [hJ] with x hx
    exact congrArg (fun r : ℝ => ‖r‖ₑ ^ 2) hx
  rw [lintegral_congr_ae hJ', lintegral_sq_nativeIntegralOf]
  have hterm : ∀ a, ∫⁻ p, ‖stopIntegrand (fun _ => min (t : WithTop ℝ≥0) ⊤)
        (tPicardNoiseFun c ξ Z j) a p - stopIntegrand (fun _ => min (t : WithTop ℝ≥0) ⊤)
        (tPicardNoiseFun c ξ Z' j) a p‖ₑ ^ 2 ∂timeProbMeasure N (driverLaw (κ := κ) μ) ≤
      ‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t := by
    intro a
    calc _ ≤ ∫⁻ p, (window S κ t).indicator
            (fun p => ‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * ‖rep Z p - rep Z' p‖ₑ ^ 2) p
            ∂timeProbMeasure N (driverLaw (κ := κ) μ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [timeProbMeasure_horizon (κ := κ) μ N] with p hpT
          simp only [stopIntegrand, tPicardNoiseFun]
          split_ifs with h
          · have hw : p ∈ window S κ t := by
              refine ⟨⟨hpT.1, ?_⟩, mem_univ _⟩
              rw [min_top_right, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe] at h
              exact h
            rw [Set.indicator_of_mem hw, ← map_sub]
            calc ‖coordCLM E j (c.σ a p.1.toNNReal (ξ p.2 + rep Z p) -
                    c.σ a p.1.toNNReal (ξ p.2 + rep Z' p))‖ₑ ^ 2
                ≤ (‖coordCLM E j‖ₑ * ((c.K : ℝ≥0∞) * ‖rep Z p - rep Z' p‖ₑ)) ^ 2 := by
                  refine pow_le_pow_left₀ zero_le ((ContinuousLinearMap.le_opENorm _ _).trans
                    (mul_le_mul_right ?_ _)) 2
                  refine (enorm_lip_sub _ (c.lip_σ a _) _ _).trans (le_of_eq ?_)
                  rw [add_sub_add_left_eq_sub]
              _ = _ := by ring
          · simp
      _ = _ := by
          rw [lintegral_indicator (measurableSet_window t), timeProbMeasure_restrict_window ht,
            lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top)
              (ENNReal.pow_ne_top ENNReal.coe_ne_top))]
          rfl
  calc _ ≤ ∑ _a : κ, ‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The Volterra constant of the time-dependent Picard map. -/
def tPicardConst (c : TLipCoeff κ E) (N : ℝ≥0) : ℝ≥0∞ :=
  2 * (c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal N +
    2 * (coordConst E * ∑ j, (Fintype.card κ : ℝ≥0∞) * (‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2))

omit [MeasurableSpace E] [BorelSpace E] in
theorem tPicardConst_ne_top : tPicardConst c N ≠ ⊤ := by
  unfold tPicardConst
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)) ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top coordConst_ne_top (ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top enorm_ne_top) (ENNReal.pow_ne_top ENNReal.coe_ne_top))))⟩

/-- Time-`t` second-moment contraction of the Picard process. -/
theorem lintegral_tPicardProc_sub_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0}
    (ht : t ≤ N) :
    ∫⁻ x, ‖tPicardProc c hξ Z t x - tPicardProc c hξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      tPicardConst c N * picardGap Z Z' t := by
  set D : DriverSample S κ → E := fun x => tPicardDrift c ξ Z t x - tPicardDrift c ξ Z' t x
  set M : Fin (Module.finrank ℝ E) → DriverSample S κ → ℝ := fun j x =>
    tPicardNoise c hξ Z j t x - tPicardNoise c hξ Z' j t x
  have hdecomp : ∀ x, tPicardProc c hξ Z t x - tPicardProc c hξ Z' t x =
      D x + ∑ j, M j x • Module.finBasis ℝ E j := by
    intro x
    simp only [D, M, tPicardProc, sub_smul, Finset.sum_sub_distrib]
    abel
  have hpt : ∀ x, ‖tPicardProc c hξ Z t x - tPicardProc c hξ Z' t x‖ₑ ^ 2 ≤
      2 * ‖D x‖ₑ ^ 2 + 2 * (coordConst E * ∑ j, ‖M j x‖ₑ ^ 2) := fun x => by
    rw [hdecomp]
    exact (enorm_sq_add_le _ _).trans (add_le_add_right (mul_le_mul_right
      (enorm_sq_basis_sum_le _) 2) _)
  have hmeas : ∀ j, AEMeasurable (fun x => ‖M j x‖ₑ ^ 2) (driverLaw (κ := κ) μ) := fun j =>
    ((((nativeAdaptedLimit_adapted μ N _ t).mono ((commonWienerFiltration S κ).le t) le_rfl).sub
      ((nativeAdaptedLimit_adapted μ N _ t).mono ((commonWienerFiltration S κ).le t)
        le_rfl)).enorm.pow_const 2).aemeasurable
  have hle : ENNReal.ofReal t ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal (by exact_mod_cast ht)
  calc ∫⁻ x, ‖tPicardProc c hξ Z t x - tPicardProc c hξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
      ≤ ∫⁻ x, (2 * ‖D x‖ₑ ^ 2 + 2 * (coordConst E * ∑ j, ‖M j x‖ₑ ^ 2)) ∂driverLaw (κ := κ) μ :=
        lintegral_mono hpt
    _ = 2 * ∫⁻ x, ‖D x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ +
          2 * (coordConst E * ∑ j, ∫⁻ x, ‖M j x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ) := by
        rw [lintegral_add_right' _ (((Finset.aemeasurable_fun_sum _ fun j _ => hmeas j).const_mul
          _).const_mul _), lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ coordConst_ne_top, lintegral_finsetSum' _ fun j _ => hmeas j]
    _ ≤ 2 * ((c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal t * picardGap Z Z' t) +
          2 * (coordConst E * ∑ j, (Fintype.card κ : ℝ≥0∞) *
            (‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t)) := by
        gcongr with j
        · exact lintegral_tPicardDrift_sub_le c hξ Z Z' ht
        · exact lintegral_tPicardNoise_sub_le c hξ Z Z' ht j
    _ ≤ 2 * ((c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal N * picardGap Z Z' t) +
          2 * (coordConst E * ∑ j, (Fintype.card κ : ℝ≥0∞) *
            (‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t)) := by
        gcongr
    _ = tPicardConst c N * picardGap Z Z' t := by
        unfold tPicardConst
        rw [add_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, mul_assoc 2,
          Finset.mul_sum, Finset.sum_mul]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun j _ => by ring

/-- **Volterra contraction** of the time-dependent Picard map in the gap `Q`. -/
theorem tPicardGap_map_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0} (ht : t ≤ N) :
    picardGap (tPicardMap c hξ Z) (tPicardMap c hξ Z') t ≤
      tPicardConst c N * ∫⁻ s in Ioc 0 (t : ℝ), picardGap Z Z' s.toNNReal := by
  have hae : ∀ᵐ p ∂timeProbMeasure t (driverLaw (κ := κ) μ),
      ‖rep (tPicardMap c hξ Z) p - rep (tPicardMap c hξ Z') p‖ₑ ^ 2 =
        ‖tPicardProcFun c hξ Z p - tPicardProcFun c hξ Z' p‖ₑ ^ 2 := by
    refine ae_mono (timeProbMeasure_le_of_le ht) ?_
    filter_upwards [rep_tPicardMap c hξ Z, rep_tPicardMap c hξ Z'] with p h1 h2
    rw [h1, h2]
  have hm : AEMeasurable (fun p => ‖tPicardProcFun c hξ Z p - tPicardProcFun c hξ Z' p‖ₑ ^ 2)
      (timeProbMeasure t (driverLaw (κ := κ) μ)) :=
    ((((aesm_tPicardProcFun c hξ Z).mono (predictableSpace_le _)).sub
      ((aesm_tPicardProcFun c hξ Z').mono (predictableSpace_le _))).enorm.pow_const 2).mono_measure
      (timeProbMeasure_le_of_le ht)
  unfold picardGap
  rw [lintegral_congr_ae hae, lintegral_timeProb hm,
    ← lintegral_const_mul' _ _ (tPicardConst_ne_top c)]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  have hst : s.toNNReal ≤ N := by
    rw [Real.toNNReal_le_iff_le_coe]
    exact hs.2.trans (by exact_mod_cast ht)
  have h := lintegral_tPicardProc_sub_le c hξ Z Z' hst
  exact h

end BlockBand.SourceProcess.Stochastic.RotationFlow
