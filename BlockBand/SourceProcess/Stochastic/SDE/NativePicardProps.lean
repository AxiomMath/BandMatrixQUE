module
public import BlockBand.SourceProcess.Stochastic.SDE.NativePicardMap
public import BlockBand.SourceProcess.Stochastic.Integral.BracketAdapted
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Regularity of the Picard process and the Picard map

Notation of `NativePicardMap`. For `Z` in the Picard space:
* the drift `D_Z` has continuous paths everywhere (`continuous_picardDrift`), is
  `F_t ∨ N`-adapted (`stronglyMeasurable_picardDrift`; coordinatewise via
  `exists_adapted_integral_Ioc`) and is bounded by `C⁺ N` (`norm_picardDrift_le`);
* the Picard process `D_Z + ∑_j M_Z^j e_j` is `F_t ∨ N`-adapted with a.s. continuous paths;
* `picardMap : PicardSpace → PicardSpace` is its class in `L²(dt ⊗ P)`
  (`rep_picardMap`: the representative is a.e. the Picard process).
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

include hξ in
omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem stronglyMeasurable_driftIntegrand (Z : PicardSpace (κ := κ) μ N E) :
    StronglyMeasurable fun p : ℝ × DriverSample S κ => c.b (ξ p.2 + rep Z p) :=
  c.lip_b.continuous.comp_stronglyMeasurable
    (((hξ.mono ((driverAugmented (κ := κ) μ).le 0)).comp_measurable measurable_snd).add
      (Lp.stronglyMeasurable _))

omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_picardDrift_le (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) (x : DriverSample S κ) :
    ‖picardDrift c ξ Z t x‖ ≤ max c.C 0 * N := by
  unfold picardDrift
  refine (norm_setIntegral_le_of_norm_le_const (C := max c.C 0) (by simp) fun s _ =>
    (c.bd_b _).trans (le_max_left c.C 0)).trans ?_
  rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right t N) (le_max_right _ _)

include hξ in
omit [IsProbabilityMeasure μ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_picardDrift (Z : PicardSpace (κ := κ) μ N E) (x : DriverSample S κ) :
    Continuous fun t => picardDrift c ξ Z t x := by
  have hF := stronglyMeasurable_driftIntegrand c hξ Z
  have hsec : StronglyMeasurable fun s : ℝ => c.b (ξ x + rep Z (s, x)) :=
    hF.comp_measurable measurable_prodMk_right
  have hprim := intervalIntegral.continuous_primitive
    (intervalIntegrable_of_bound hsec (fun s => (c.bd_b _).trans (le_max_left c.C 0))) 0
  have he : (fun t => picardDrift c ξ Z t x) =
      (fun u : ℝ => ∫ s in (0 : ℝ)..u, c.b (ξ x + rep Z (s, x))) ∘
        fun t : ℝ≥0 => ((min t N : ℝ≥0) : ℝ) := by
    funext t
    simp only [Function.comp_apply, picardDrift]
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
  rw [he]
  exact hprim.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const))

include hξ in
theorem stronglyMeasurable_picardDrift (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] (picardDrift c ξ Z t) := by
  classical
  set u : ℝ≥0 := min t N
  have hF := stronglyMeasurable_driftIntegrand c hξ Z
  have hamb : StronglyMeasurable (picardDrift c ξ Z t) :=
    hF.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) (u : ℝ)))
  let B := Module.finBasis ℝ E
  have hG (j : Fin (Module.finrank ℝ E)) : AEStronglyMeasurable[rawPredictable S κ]
      (fun p : ℝ × DriverSample S κ => coordCLM E j (c.b (ξ p.2 + rep Z p)))
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
    ((coordCLM E j).continuous.comp c.lip_b.continuous).comp_aestronglyMeasurable
      ((aesm_initial (N := N) hξ).add (aesm_rep Z))
  choose D hD hDe using fun j => exists_adapted_integral_Ioc (hG j) (min_le_right t N)
  have hcoord (j : Fin (Module.finrank ℝ E)) (x : DriverSample S κ) :
      coordCLM E j (picardDrift c ξ Z t x) =
        ∫ s in Ioc (0 : ℝ) (u : ℝ), coordCLM E j (c.b (ξ x + rep Z (s, x))) := by
    unfold picardDrift
    have hsec : StronglyMeasurable fun s : ℝ => c.b (ξ x + rep Z (s, x)) :=
      hF.comp_measurable measurable_prodMk_right
    have hint : IntegrableOn (fun s : ℝ => c.b (ξ x + rep Z (s, x))) (Ioc (0 : ℝ) (u : ℝ)) :=
      (intervalIntegrable_of_bound hsec (fun s => (c.bd_b _).trans (le_max_left c.C 0)) 0 u).1
    exact ((coordCLM E j).integral_comp_comm hint).symm
  refine stronglyMeasurable_aug_of_ae_eq hamb (g := fun x => ∑ j, D j x • B j) ?_ ?_
  · refine Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_
    refine StronglyMeasurable.smul_const ?_ _
    exact ((hD j).mono ((commonWienerFiltration S κ).mono (min_le_left t N))).mono
      (le_augmentedFiltration _ _ t)
  · filter_upwards [ae_all_iff.2 hDe] with x hx
    conv_lhs => rw [← B.sum_repr (picardDrift c ξ Z t x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hr : (B.repr (picardDrift c ξ Z t x)) j = coordCLM E j (picardDrift c ξ Z t x) := rfl
    rw [hr, hcoord j x]
    exact congrArg (fun r => r • B j) (hx j)

omit [MeasurableSpace E] [BorelSpace E] in
theorem stronglyMeasurable_picardNoise (Z : PicardSpace (κ := κ) μ N E)
    (j : Fin (Module.finrank ℝ E)) (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] (picardNoise c hξ Z j t) :=
  (nativeAdaptedLimit_adapted μ N _ t).stronglyMeasurable.mono (le_augmentedFiltration _ _ t)

theorem stronglyMeasurable_picardProc (Z : PicardSpace (κ := κ) μ N E) (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] (picardProc c hξ Z t) :=
  (stronglyMeasurable_picardDrift c hξ Z t).add (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    (stronglyMeasurable_picardNoise c hξ Z j t).smul_const _)

omit [MeasurableSpace E] [BorelSpace E] in
theorem ae_continuous_picardNoise (Z : PicardSpace (κ := κ) μ N E) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ j, Continuous fun t => picardNoise c hξ Z j t x :=
  ae_all_iff.2 fun _ => nativeAdaptedLimit_continuous_all_ae μ N _

omit [MeasurableSpace E] [BorelSpace E] in
theorem ae_continuous_picardProc (Z : PicardSpace (κ := κ) μ N E) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => picardProc c hξ Z t x := by
  filter_upwards [ae_continuous_picardNoise c hξ Z] with x hx
  exact (continuous_picardDrift c hξ Z x).add
    (continuous_finsetSum _ fun j _ => (hx j).smul continuous_const)

/-- The Picard process as a function on `ℝ × Ω`. -/
abbrev picardProcFun (Z : PicardSpace (κ := κ) μ N E) : ℝ × DriverSample S κ → E :=
  fun p => picardProc c hξ Z p.1.toNNReal p.2

theorem aesm_picardProcFun (Z : PicardSpace (κ := κ) μ N E) :
    AEStronglyMeasurable[rawPredictable S κ] (picardProcFun c hξ Z)
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
  aesm_processFun (stronglyMeasurable_picardProc c hξ Z) (ae_continuous_picardProc c hξ Z)

theorem memLp_picardProcFun (Z : PicardSpace (κ := κ) μ N E) :
    MemLp (picardProcFun c hξ Z) 2 (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
  classical
  have hdrift : MemLp (fun p : ℝ × DriverSample S κ => picardDrift c ξ Z p.1.toNNReal p.2) 2
      (timeProbMeasure N (driverLaw (κ := κ) μ)) :=
    MemLp.of_bound ((aesm_processFun (T := N) (stronglyMeasurable_picardDrift c hξ Z)
      (Eventually.of_forall (continuous_picardDrift c hξ Z))).mono (predictableSpace_le _))
      (max c.C 0 * N) (Eventually.of_forall fun p => norm_picardDrift_le c Z _ _)
  have hnoise (j : Fin (Module.finrank ℝ E)) : MemLp (fun p : ℝ × DriverSample S κ =>
      picardNoise c hξ Z j p.1.toNNReal p.2) 2 (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
    refine memLp_two_of_time_bound ((aesm_processFun (stronglyMeasurable_picardNoise c hξ Z j)
      (nativeAdaptedLimit_continuous_all_ae μ N _)).mono (predictableSpace_le _))
      (c := ENNReal.ofReal (‖(nativeIntegrand_picardNoiseFun c hξ Z j).family‖ ^ 2))
      ENNReal.ofReal_ne_top fun s => ?_
    have hm := nativeAdaptedLimit_memLp_all μ N (nativeIntegrand_picardNoiseFun c hξ Z j).family s
    unfold picardNoise
    rw [lintegral_enorm_sq_eq_ofReal hm, ← norm_sq_toLp hm]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    exact nativeAdaptedLimit_L2_norm_le μ N _ s
  have hsum : MemLp (fun p : ℝ × DriverSample S κ => ∑ j, picardNoise c hξ Z j p.1.toNNReal p.2 •
      Module.finBasis ℝ E j) 2 (timeProbMeasure N (driverLaw (κ := κ) μ)) := by
    exact memLp_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (f := fun j (p : ℝ × DriverSample S κ) => picardNoise c hξ Z j p.1.toNNReal p.2 •
        Module.finBasis ℝ E j) fun j _ =>
      (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ E j)).comp_memLp' (hnoise j)
  exact hdrift.add hsum

/-- **The Picard map** `Γ : Z ↦ [D_Z + ∑_j M_Z^j e_j]`. -/
def picardMap (Z : PicardSpace (κ := κ) μ N E) : PicardSpace (κ := κ) μ N E :=
  ⟨(memLp_picardProcFun c hξ Z).toLp _, mem_lpMeas_iff_aestronglyMeasurable.2
    ((aesm_picardProcFun c hξ Z).congr (memLp_picardProcFun c hξ Z).coeFn_toLp.symm)⟩

theorem rep_picardMap (Z : PicardSpace (κ := κ) μ N E) :
    rep (picardMap c hξ Z) =ᵐ[timeProbMeasure N (driverLaw (κ := κ) μ)] picardProcFun c hξ Z :=
  (memLp_picardProcFun c hξ Z).coeFn_toLp

end BlockBand.SourceProcess.Stochastic.NativeSDE
