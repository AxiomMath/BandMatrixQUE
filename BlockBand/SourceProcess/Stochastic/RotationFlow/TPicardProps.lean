module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.TPicardMap
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Regularity of the time-dependent Picard process

Time-inhomogeneous version of the properties of the Picard map; notation of `TPicardMap`.
For `Z` in the Picard space:
* the drift `D_Z` has continuous paths everywhere, is `F_t ∨ N`-adapted and bounded by `C⁺ N`;
* the Picard process is `F_t ∨ N`-adapted with a.s. continuous paths;
* `tPicardMap : PicardSpace → PicardSpace` is its `L²(dt ⊗ P)` class (`rep_tPicardMap`).
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
omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem stronglyMeasurable_tDriftIntegrand (Z : PicardSpace (κ := κ) μ N E) :
    StronglyMeasurable fun p : ℝ × DriverSample S κ => c.b p.1.toNNReal (ξ p.2 + rep Z p) :=
  c.cont_b.comp_stronglyMeasurable
    ((measurable_fst.real_toNNReal.stronglyMeasurable).prodMk
      (((hξ.mono ((driverAugmented (κ := κ) μ).le 0)).comp_measurable measurable_snd).add
        (Lp.stronglyMeasurable _)))

omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_tPicardDrift_le (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) (x : DriverSample S κ) :
    ‖tPicardDrift c ξ Z t x‖ ≤ max c.C 0 * N := by
  unfold tPicardDrift
  refine (norm_setIntegral_le_of_norm_le_const (C := max c.C 0) (by simp) fun s _ =>
    (c.bd_b _ _).trans (le_max_left c.C 0)).trans ?_
  rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right t N) (le_max_right _ _)

include hξ in
omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_tPicardDrift (Z : PicardSpace (κ := κ) μ N E) (x : DriverSample S κ) :
    Continuous fun t => tPicardDrift c ξ Z t x := by
  have hF := stronglyMeasurable_tDriftIntegrand c hξ Z
  have hsec : StronglyMeasurable fun s : ℝ => c.b s.toNNReal (ξ x + rep Z (s, x)) :=
    hF.comp_measurable measurable_prodMk_right
  have hprim := intervalIntegral.continuous_primitive
    (intervalIntegrable_of_bound hsec (fun s => (c.bd_b _ _).trans (le_max_left c.C 0))) 0
  have he : (fun t => tPicardDrift c ξ Z t x) =
      (fun u : ℝ => ∫ s in (0 : ℝ)..u, c.b s.toNNReal (ξ x + rep Z (s, x))) ∘
        fun t : ℝ≥0 => ((min t N : ℝ≥0) : ℝ) := by
    funext t
    simp only [Function.comp_apply, tPicardDrift]
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
  rw [he]
  exact hprim.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

include hξ in
theorem stronglyMeasurable_tPicardDrift (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] (tPicardDrift c ξ Z t) := by
  classical
  set u : ℝ≥0 := min t N
  have hF := stronglyMeasurable_tDriftIntegrand c hξ Z
  have hamb : StronglyMeasurable (tPicardDrift c ξ Z t) :=
    hF.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) (u : ℝ)))
  let B := Module.finBasis ℝ E
  have hG (j : Fin (Module.finrank ℝ E)) : AEStronglyMeasurable[rawPredictable S κ]
      (fun p : ℝ × DriverSample S κ => coordCLM E j (c.b p.1.toNNReal (ξ p.2 + rep Z p)))
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
    (coordCLM E j).continuous.comp_aestronglyMeasurable
      (aesm_coeff_comp c.cont_b ((aesm_initial (N := N) hξ).add (aesm_rep Z)))
  choose D hD hDe using fun j => exists_adapted_integral_Ioc (hG j) (min_le_right t N)
  have hcoord (j : Fin (Module.finrank ℝ E)) (x : DriverSample S κ) :
      coordCLM E j (tPicardDrift c ξ Z t x) =
        ∫ s in Ioc (0 : ℝ) (u : ℝ), coordCLM E j (c.b s.toNNReal (ξ x + rep Z (s, x))) := by
    unfold tPicardDrift
    have hsec : StronglyMeasurable fun s : ℝ => c.b s.toNNReal (ξ x + rep Z (s, x)) :=
      hF.comp_measurable measurable_prodMk_right
    have hint : IntegrableOn (fun s : ℝ => c.b s.toNNReal (ξ x + rep Z (s, x)))
        (Ioc (0 : ℝ) (u : ℝ)) :=
      (intervalIntegrable_of_bound hsec (fun s => (c.bd_b _ _).trans (le_max_left c.C 0)) 0 u).1
    exact ((coordCLM E j).integral_comp_comm hint).symm
  refine stronglyMeasurable_aug_of_ae_eq hamb (g := fun x => ∑ j, D j x • B j) ?_ ?_
  · refine Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_
    refine StronglyMeasurable.smul_const ?_ _
    exact ((hD j).mono ((commonWienerFiltration S κ).mono (min_le_left t N))).mono
      (le_augmentedFiltration _ _ t)
  · filter_upwards [ae_all_iff.2 hDe] with x hx
    conv_lhs => rw [← B.sum_repr (tPicardDrift c ξ Z t x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hr : (B.repr (tPicardDrift c ξ Z t x)) j = coordCLM E j (tPicardDrift c ξ Z t x) := rfl
    rw [hr, hcoord j x]
    exact congrArg (fun r => r • B j) (hx j)

omit [MeasurableSpace E] [BorelSpace E] in
theorem stronglyMeasurable_tPicardNoise (Z : PicardSpace (κ := κ) μ N E)
    (j : Fin (Module.finrank ℝ E)) (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] (tPicardNoise c hξ Z j t) :=
  (nativeAdaptedLimit_adapted μ N _ t).stronglyMeasurable.mono (le_augmentedFiltration _ _ t)

theorem stronglyMeasurable_tPicardProc (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] (tPicardProc c hξ Z t) :=
  (stronglyMeasurable_tPicardDrift c hξ Z t).add (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    (stronglyMeasurable_tPicardNoise c hξ Z j t).smul_const _)

omit [MeasurableSpace E] [BorelSpace E] in
theorem ae_continuous_tPicardNoise (Z : PicardSpace (κ := κ) μ N E) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ j, Continuous fun t => tPicardNoise c hξ Z j t x :=
  ae_all_iff.2 fun _ => nativeAdaptedLimit_continuous_all_ae μ N _

omit [MeasurableSpace E] [BorelSpace E] in
theorem ae_continuous_tPicardProc (Z : PicardSpace (κ := κ) μ N E) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => tPicardProc c hξ Z t x := by
  filter_upwards [ae_continuous_tPicardNoise c hξ Z] with x hx
  exact (continuous_tPicardDrift c hξ Z x).add
    (continuous_finsetSum _ fun j _ => (hx j).smul continuous_const)

/-- The Picard process as a function on `ℝ × Ω`. -/
abbrev tPicardProcFun (Z : PicardSpace (κ := κ) μ N E) : ℝ × DriverSample S κ → E :=
  fun p => tPicardProc c hξ Z p.1.toNNReal p.2

theorem aesm_tPicardProcFun (Z : PicardSpace (κ := κ) μ N E) :
    AEStronglyMeasurable[rawPredictable S κ] (tPicardProcFun c hξ Z)
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
  aesm_processFun (stronglyMeasurable_tPicardProc c hξ Z) (ae_continuous_tPicardProc c hξ Z)

theorem memLp_tPicardProcFun (Z : PicardSpace (κ := κ) μ N E) :
    MemLp (tPicardProcFun c hξ Z) 2 (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
  classical
  have hdrift : MemLp (fun p : ℝ × DriverSample S κ => tPicardDrift c ξ Z p.1.toNNReal p.2) 2
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
    MemLp.of_bound ((aesm_processFun (T := N) (stronglyMeasurable_tPicardDrift c hξ Z)
      (Eventually.of_forall (continuous_tPicardDrift c hξ Z))).mono (predictableSpace_le _))
      (max c.C 0 * N) (Eventually.of_forall fun p => norm_tPicardDrift_le c Z _ _)
  have hnoise (j : Fin (Module.finrank ℝ E)) : MemLp (fun p : ℝ × DriverSample S κ =>
      tPicardNoise c hξ Z j p.1.toNNReal p.2) 2 (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
    refine memLp_two_of_time_bound ((aesm_processFun (stronglyMeasurable_tPicardNoise c hξ Z j)
      (nativeAdaptedLimit_continuous_all_ae μ N _)).mono (predictableSpace_le _))
      (c := ENNReal.ofReal (‖(nativeIntegrand_tPicardNoiseFun c hξ Z j).family‖ ^ 2))
      ENNReal.ofReal_ne_top fun s => ?_
    have hm := nativeAdaptedLimit_memLp_all μ N
      (nativeIntegrand_tPicardNoiseFun c hξ Z j).family s
    unfold tPicardNoise
    rw [lintegral_enorm_sq_eq_ofReal hm, ← norm_sq_toLp hm]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    exact nativeAdaptedLimit_L2_norm_le μ N _ s
  have hsum : MemLp (fun p : ℝ × DriverSample S κ => ∑ j, tPicardNoise c hξ Z j p.1.toNNReal p.2 •
      Module.finBasis ℝ E j) 2 (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
    exact memLp_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (f := fun j (p : ℝ × DriverSample S κ) => tPicardNoise c hξ Z j p.1.toNNReal p.2 •
        Module.finBasis ℝ E j) fun j _ =>
      (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ E j)).comp_memLp' (hnoise j)
  exact hdrift.add hsum

/-- **The time-dependent Picard map** `Γ : Z ↦ [D_Z + ∑_j M_Z^j e_j]`. -/
def tPicardMap (Z : PicardSpace (κ := κ) μ N E) : PicardSpace (κ := κ) μ N E :=
  ⟨(memLp_tPicardProcFun c hξ Z).toLp _, mem_lpMeas_iff_aestronglyMeasurable.2
    ((aesm_tPicardProcFun c hξ Z).congr (memLp_tPicardProcFun c hξ Z).coeFn_toLp.symm)⟩

theorem rep_tPicardMap (Z : PicardSpace (κ := κ) μ N E) :
    rep (tPicardMap c hξ Z) =ᵐ[timeProbMeasure N (driverLaw (κ := κ) μ)] tPicardProcFun c hξ Z :=
  (memLp_tPicardProcFun c hξ Z).coeFn_toLp

end BlockBand.SourceProcess.Stochastic.RotationFlow
