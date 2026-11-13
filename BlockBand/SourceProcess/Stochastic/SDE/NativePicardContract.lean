module
public import BlockBand.SourceProcess.Stochastic.SDE.NativePicardProps
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Volterra contraction of the Picard map

Notation of `NativePicardMap`; `Q_t(Z,Z') = ∫⁻ ‖Z − Z'‖² d(dt ⊗ P)` over `(0,t]`
(`picardGap`). For `t ≤ N`:
* drift: `E‖D_Z(t) − D_{Z'}(t)‖² ≤ K² t Q_t` (pathwise Cauchy–Schwarz);
* noise: `E|M_Z^j(t) − M_{Z'}^j(t)|² ≤ |κ| ‖ℓ_j‖² K² Q_t` (Itô isometry);
* process: `E‖Γ-process_Z(t) − Γ-process_{Z'}(t)‖² ≤ L_c Q_t` (`lintegral_picardProc_sub_le`).

Integrating in time gives the Volterra contraction
`Q_t(ΓZ, ΓZ') ≤ L_c ∫_0^t Q_s(Z,Z') ds` (`picardGap_map_le`), which is the hypothesis of
`SDE.picard_fixedPoint` with `δ = Q.toReal`.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (c : LipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
  (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ)

/-- `Q_t(Z,Z') = ∫⁻_{(0,t] × Ω} ‖Z − Z'‖²`. -/
def picardGap (Z Z' : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ p, ‖rep Z p - rep Z' p‖ₑ ^ 2 ∂timeProbMeasure t (driverLaw (κ := κ) μ)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem enorm_lip_sub (f : E → E) {K : ℝ≥0} (hf : LipschitzWith K f) (a b : E) :
    ‖f a - f b‖ₑ ≤ K * ‖a - b‖ₑ := by
  have := hf.edist_le_mul a b
  simpa [edist_eq_enorm_sub] using this

omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] in
theorem aemeasurable_gap (Z Z' : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) :
    AEMeasurable (fun p => ‖rep Z p - rep Z' p‖ₑ ^ 2) (timeProbMeasure t (driverLaw (κ := κ) μ)) :=
  (((Lp.stronglyMeasurable _).sub (Lp.stronglyMeasurable _)).measurable.enorm.pow_const 2).aemeasurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem picardGap_mono (Z Z' : PicardSpace (κ := κ) μ N E) : Monotone (picardGap Z Z') :=
  fun _ _ h => lintegral_mono' (timeProbMeasure_le_of_le h) le_rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem picardGap_lt_top (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0} (ht : t ≤ N) :
    picardGap Z Z' t < ⊤ := by
  refine lt_of_le_of_lt (picardGap_mono Z Z' ht) ?_
  exact lintegral_enorm_sq_lt_top ((Lp.memLp _).sub (Lp.memLp _))

include hξ in
/-- Drift part of the contraction. -/
theorem lintegral_picardDrift_sub_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0} (ht : t ≤ N) :
    ∫⁻ x, ‖picardDrift c ξ Z t x - picardDrift c ξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      (c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal t * picardGap Z Z' t := by
  have hmin : min t N = t := min_eq_left ht
  have hF := stronglyMeasurable_driftIntegrand c hξ Z
  have hF' := stronglyMeasurable_driftIntegrand c hξ Z'
  have hpt : ∀ x, ‖picardDrift c ξ Z t x - picardDrift c ξ Z' t x‖ₑ ^ 2 ≤
      ENNReal.ofReal t * ((c.K : ℝ≥0∞) ^ 2 *
        ∫⁻ s in Ioc 0 (t : ℝ), ‖rep Z (s, x) - rep Z' (s, x)‖ₑ ^ 2) := by
    intro x
    unfold picardDrift
    rw [hmin]
    have hint (W : PicardSpace (κ := κ) μ N E)
        (hW : StronglyMeasurable fun p : ℝ × DriverSample S κ => c.b (ξ p.2 + rep W p)) :
        IntegrableOn (fun s : ℝ => c.b (ξ x + rep W (s, x))) (Ioc (0 : ℝ) (t : ℝ)) :=
      (intervalIntegrable_of_bound (hW.comp_measurable measurable_prodMk_right)
        (fun s => (c.bd_b _).trans (le_max_left c.C 0)) 0 t).1
    have h := enorm_sq_integral_sub_le (hint Z hF) (hint Z' hF')
      (h := fun s => (c.K : ℝ≥0∞) * ‖rep Z (s, x) - rep Z' (s, x)‖ₑ) (fun s _ => by
        refine (enorm_lip_sub c.b c.lip_b _ _).trans (le_of_eq ?_)
        rw [add_sub_add_left_eq_sub])
      (((((Lp.stronglyMeasurable _).sub (Lp.stronglyMeasurable _)).comp_measurable
        measurable_prodMk_right).measurable.enorm).const_mul _).aemeasurable
    refine h.trans (le_of_eq ?_)
    simp_rw [mul_pow]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  calc ∫⁻ x, ‖picardDrift c ξ Z t x - picardDrift c ξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
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
theorem lintegral_picardNoise_sub_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0} (ht : t ≤ N)
    (j : Fin (Module.finrank ℝ E)) :
    ∫⁻ x, ‖picardNoise c hξ Z j t x - picardNoise c hξ Z' j t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      Fintype.card κ * (‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t) := by
  obtain ⟨hs, h1⟩ := nativeAdaptedLimit_stopped (nativeIntegrand_picardNoiseFun c hξ Z j)
    isStoppingTime_top t
  obtain ⟨hs', h2⟩ := nativeAdaptedLimit_stopped (nativeIntegrand_picardNoiseFun c hξ Z' j)
    isStoppingTime_top t
  have hst (X : ℝ≥0 → DriverSample S κ → ℝ) : stoppedProcess X (fun _ => ⊤) t = X t :=
    funext fun _ => stoppedProcess_eq_of_le le_top
  rw [hst] at h1 h2
  have hJ : (fun x => picardNoise c hξ Z j t x - picardNoise c hξ Z' j t x) =ᵐ[driverLaw (κ := κ) μ]
      (nativeIntegralOf (nativeIntegrand_sub hs hs') : DriverSample S κ → ℝ) := by
    rw [nativeIntegralOf_sub hs hs']
    filter_upwards [h1, h2, Lp.coeFn_sub (nativeIntegralOf hs) (nativeIntegralOf hs')] with
      x hx1 hx2 hx3
    rw [hx3, Pi.sub_apply, ← hx1, ← hx2]
    rfl
  have hJ' : (fun x => ‖picardNoise c hξ Z j t x - picardNoise c hξ Z' j t x‖ₑ ^ 2)
      =ᵐ[driverLaw (κ := κ) μ] fun x =>
        ‖(nativeIntegralOf (nativeIntegrand_sub hs hs') : DriverSample S κ → ℝ) x‖ₑ ^ 2 := by
    filter_upwards [hJ] with x hx
    exact congrArg (fun r : ℝ => ‖r‖ₑ ^ 2) hx
  rw [lintegral_congr_ae hJ', lintegral_sq_nativeIntegralOf]
  have hterm : ∀ a, ∫⁻ p, ‖stopIntegrand (fun _ => min (t : WithTop ℝ≥0) ⊤)
        (picardNoiseFun c ξ Z j) a p - stopIntegrand (fun _ => min (t : WithTop ℝ≥0) ⊤)
        (picardNoiseFun c ξ Z' j) a p‖ₑ ^ 2 ∂timeProbMeasure N (driverLaw (κ := κ) μ) ≤
      ‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t := by
    intro a
    calc _ ≤ ∫⁻ p, (window S κ t).indicator
            (fun p => ‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * ‖rep Z p - rep Z' p‖ₑ ^ 2) p
            ∂timeProbMeasure N (driverLaw (κ := κ) μ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [timeProbMeasure_horizon (κ := κ) μ N] with p hpT
          simp only [stopIntegrand, picardNoiseFun]
          split_ifs with h
          · have hw : p ∈ window S κ t := by
              refine ⟨⟨hpT.1, ?_⟩, mem_univ _⟩
              rw [min_top_right, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe] at h
              exact h
            rw [Set.indicator_of_mem hw, ← map_sub]
            calc ‖coordCLM E j (c.σ a (ξ p.2 + rep Z p) - c.σ a (ξ p.2 + rep Z' p))‖ₑ ^ 2
                ≤ (‖coordCLM E j‖ₑ * ((c.K : ℝ≥0∞) * ‖rep Z p - rep Z' p‖ₑ)) ^ 2 := by
                  refine pow_le_pow_left₀ zero_le ((ContinuousLinearMap.le_opENorm _ _).trans
                    (mul_le_mul_right ?_ _)) 2
                  refine (enorm_lip_sub _ (c.lip_σ a) _ _).trans (le_of_eq ?_)
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

/-- Tonelli on `dt ⊗ P` over `(0,t]`. -/
theorem lintegral_timeProb {t : ℝ≥0} {f : ℝ × DriverSample S κ → ℝ≥0∞}
    (hf : AEMeasurable f (timeProbMeasure t (driverLaw (κ := κ) μ))) :
    ∫⁻ p, f p ∂timeProbMeasure t (driverLaw (κ := κ) μ) =
      ∫⁻ s in Ioc 0 (t : ℝ), ∫⁻ x, f (s, x) ∂driverLaw (κ := κ) μ := by
  unfold timeProbMeasure at hf ⊢
  exact lintegral_prod f hf

variable (E) in
/-- The coordinate constant `C_E` of `enorm_sq_le_coord`. -/
def coordConst : ℝ≥0∞ := (enorm_sq_le_coord E).choose

omit [MeasurableSpace E] [BorelSpace E] in
theorem coordConst_ne_top : coordConst E ≠ ⊤ := (enorm_sq_le_coord E).choose_spec.1

omit [MeasurableSpace E] [BorelSpace E] in
theorem enorm_sq_basis_sum_le (r : Fin (Module.finrank ℝ E) → ℝ) :
    ‖∑ j, r j • Module.finBasis ℝ E j‖ₑ ^ 2 ≤ coordConst E * ∑ j, ‖r j‖ₑ ^ 2 := by
  refine ((enorm_sq_le_coord E).choose_spec.2 _).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordCLM_apply]
  simp [Finsupp.single_apply]

/-- The Volterra constant of the Picard map. -/
def picardConst (c : LipCoeff κ E) (N : ℝ≥0) : ℝ≥0∞ :=
  2 * (c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal N +
    2 * (coordConst E * ∑ j, (Fintype.card κ : ℝ≥0∞) * (‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2))

omit [MeasurableSpace E] [BorelSpace E] in
theorem picardConst_ne_top : picardConst c N ≠ ⊤ := by
  unfold picardConst
  refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)) ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top coordConst_ne_top (ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top enorm_ne_top) (ENNReal.pow_ne_top ENNReal.coe_ne_top))))⟩

/-- Time-`t` second-moment contraction of the Picard process. -/
theorem lintegral_picardProc_sub_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0} (ht : t ≤ N) :
    ∫⁻ x, ‖picardProc c hξ Z t x - picardProc c hξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      picardConst c N * picardGap Z Z' t := by
  set D : DriverSample S κ → E := fun x => picardDrift c ξ Z t x - picardDrift c ξ Z' t x
  set M : Fin (Module.finrank ℝ E) → DriverSample S κ → ℝ := fun j x =>
    picardNoise c hξ Z j t x - picardNoise c hξ Z' j t x
  have hdecomp : ∀ x, picardProc c hξ Z t x - picardProc c hξ Z' t x =
      D x + ∑ j, M j x • Module.finBasis ℝ E j := by
    intro x
    simp only [D, M, picardProc, sub_smul, Finset.sum_sub_distrib]
    abel
  have hpt : ∀ x, ‖picardProc c hξ Z t x - picardProc c hξ Z' t x‖ₑ ^ 2 ≤
      2 * ‖D x‖ₑ ^ 2 + 2 * (coordConst E * ∑ j, ‖M j x‖ₑ ^ 2) := fun x => by
    rw [hdecomp]
    exact (enorm_sq_add_le _ _).trans (add_le_add_right (mul_le_mul_right
      (enorm_sq_basis_sum_le _) 2) _)
  have hmeas : ∀ j, AEMeasurable (fun x => ‖M j x‖ₑ ^ 2) (driverLaw (κ := κ) μ) := fun j =>
    ((((nativeAdaptedLimit_adapted μ N _ t).mono ((commonWienerFiltration S κ).le t) le_rfl).sub
      ((nativeAdaptedLimit_adapted μ N _ t).mono ((commonWienerFiltration S κ).le t)
        le_rfl)).enorm.pow_const 2).aemeasurable
  have hle : ENNReal.ofReal t ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal (by exact_mod_cast ht)
  calc ∫⁻ x, ‖picardProc c hξ Z t x - picardProc c hξ Z' t x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
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
        · exact lintegral_picardDrift_sub_le c hξ Z Z' ht
        · exact lintegral_picardNoise_sub_le c hξ Z Z' ht j
    _ ≤ 2 * ((c.K : ℝ≥0∞) ^ 2 * ENNReal.ofReal N * picardGap Z Z' t) +
          2 * (coordConst E * ∑ j, (Fintype.card κ : ℝ≥0∞) *
            (‖coordCLM E j‖ₑ ^ 2 * (c.K : ℝ≥0∞) ^ 2 * picardGap Z Z' t)) := by
        gcongr
    _ = picardConst c N * picardGap Z Z' t := by
        unfold picardConst
        rw [add_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, mul_assoc 2,
          Finset.mul_sum, Finset.sum_mul]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun j _ => by ring

/-- **Volterra contraction** of the Picard map in the gap `Q`. -/
theorem picardGap_map_le (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ≥0} (ht : t ≤ N) :
    picardGap (picardMap c hξ Z) (picardMap c hξ Z') t ≤
      picardConst c N * ∫⁻ s in Ioc 0 (t : ℝ), picardGap Z Z' s.toNNReal := by
  have hae : ∀ᵐ p ∂timeProbMeasure t (driverLaw (κ := κ) μ),
      ‖rep (picardMap c hξ Z) p - rep (picardMap c hξ Z') p‖ₑ ^ 2 =
        ‖picardProcFun c hξ Z p - picardProcFun c hξ Z' p‖ₑ ^ 2 := by
    refine ae_mono (timeProbMeasure_le_of_le ht) ?_
    filter_upwards [rep_picardMap c hξ Z, rep_picardMap c hξ Z'] with p h1 h2
    rw [h1, h2]
  have hm : AEMeasurable (fun p => ‖picardProcFun c hξ Z p - picardProcFun c hξ Z' p‖ₑ ^ 2)
      (timeProbMeasure t (driverLaw (κ := κ) μ)) :=
    ((((aesm_picardProcFun c hξ Z).mono (predictableSpace_le _)).sub
      ((aesm_picardProcFun c hξ Z').mono (predictableSpace_le _))).enorm.pow_const 2).mono_measure
      (timeProbMeasure_le_of_le ht)
  unfold picardGap
  rw [lintegral_congr_ae hae, lintegral_timeProb hm, ← lintegral_const_mul' _ _ (picardConst_ne_top c)]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  have hst : s.toNNReal ≤ N := by
    rw [Real.toNNReal_le_iff_le_coe]
    exact hs.2.trans (by exact_mod_cast ht)
  have h := lintegral_picardProc_sub_le c hξ Z Z' hst
  exact h

end BlockBand.SourceProcess.Stochastic.NativeSDE
