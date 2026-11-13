module

public import BlockBand.SourceProcess.PhysApprox.B3MomMax
public import BlockBand.SourceProcess.PhysApprox.B3BirthReduce

/-!
# The summed births of the stopped `𝒦` step

* `birthK_sum_pow_four_le`: `(Σ_F a_i)⁴ ≤ |F|³ Σ_F a_i⁴` (power mean, `ℝ≥0∞`).
* `lintegral_kStopStep_pow_four_le`: one stopped step `Z_i = 1_{A_i}(X_{i+1} − X_i)` has
  `E|Z_i|⁴ ≤ 8 E[1_{A_i}|X_{i+1}|⁴] + 8 E[1_{A_i}|X_i|⁴]`, and the second term is `0` at
  `i = n_s` (`X_{n_s} = 0`) and at most `E[1_{A_{i-1}}|X_i|⁴]` otherwise (`A_i ⊆ A_{i-1}`).
* **`kStopBirthSum_of_stopped`**: the per-length stopped fourth moment
  `ComplexKStoppedMoment` implies `KStopBirthSum`, since there are at most
  `np` birth steps (`Birth.card_steps_le`): `E(Σ_{births}|Z_i|)⁴ ≤ np³ · np · 16C`.

No birth-specific estimate is needed: the births enter only through their number. With
`complexKStoppedMoment_of_corr`, `KStopBirthSum` follows from `RawTagMoments` and `ComplexKCorrMoment`
(`kStopBirthSum_of_corr`, `kStopBirthSum_of_baseContracts`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal ENNReal

variable {W np K : ℕ}

/-- `(Σ_F a_i)⁴ ≤ |F|³ Σ_F a_i⁴`. -/
theorem birthK_sum_pow_four_le {ι : Type*} (F : Finset ι) (a : ι → ℝ≥0∞) :
    (∑ i ∈ F, a i) ^ 4 ≤ (F.card : ℝ≥0∞) ^ 3 * ∑ i ∈ F, a i ^ 4 := by
  have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := F) (f := a) (p := 4) (by norm_num)
  have e : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ (4 : ℕ) := fun x => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [e] at h
  rwa [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast] at h

/-- The stopped closed `𝒦` one step ahead, `1_{A_i}|X_{i+1}|⁴`, is a.e. measurable. -/
theorem aemeasurable_stoppedK_pow {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i n : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (ij : Fin np × Fin np) :
    AEMeasurable ((b3Alive b E s h τ m R W i Vs).indicator
      (fun y => ‖b3ClosedKAt b E s h τ m W n y ij.1 ij.2‖ₑ ^ 4)) (closedLaw b W np) := by
  have hf : Measurable fun y : ProbedPath W np × ℝ =>
      ‖b3ClosedKAt b E s h τ m W n y ij.1 ij.2‖ₑ ^ 4 :=
    ((measurable_b3ClosedKAt b E s h τ m W n).eval_matrix).enorm.pow_const 4
  exact (hf.indicator (measurableSet_b3AliveM b E s h τ m R W i hV)).aemeasurable.congr
    (indicator_ae_eq_of_ae_eq_set (b3Alive_ae_eq hb hE1 hE2 s h τ m R W i Vs)).symm

/-- **One stopped step**: `E|Z_i|⁴ ≤ 8 E[1_{A_i}|X_{i+1}|⁴] + 8 E[1_{A_i}|X_i|⁴]`. -/
theorem lintegral_kStopStep_pow_four_le {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (ij : Fin np × Fin np) :
    ∫⁻ y, ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
      8 * ∫⁻ y, (b3Alive b E s h τ m R W i Vs).indicator
          (fun y => ‖b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2‖ₑ ^ 4) y ∂closedLaw b W np +
        8 * ∫⁻ y, (b3Alive b E s h τ m R W i Vs).indicator
          (fun y => ‖b3ClosedKAt b E s h τ m W i y ij.1 ij.2‖ₑ ^ 4) y ∂closedLaw b W np := by
  set A := b3Alive b E s h τ m R W i Vs
  have hpt : ∀ y, ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ≤
      8 * A.indicator (fun y => ‖b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2‖ₑ ^ 4) y +
        8 * A.indicator (fun y => ‖b3ClosedKAt b E s h τ m W i y ij.1 ij.2‖ₑ ^ 4) y := by
    intro y
    by_cases hy : y ∈ A
    · simp only [kStopStep, Set.indicator_of_mem hy, A]
      calc ‖b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2 -
            b3ClosedKAt b E s h τ m W i y ij.1 ij.2‖ₑ ^ 4
          ≤ (‖b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2‖ₑ +
              ‖b3ClosedKAt b E s h τ m W i y ij.1 ij.2‖ₑ) ^ 4 :=
            pow_le_pow_left₀ zero_le enorm_sub_le 4
        _ ≤ 8 * (‖b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2‖ₑ ^ 4 +
              ‖b3ClosedKAt b E s h τ m W i y ij.1 ij.2‖ₑ ^ 4) := add_pow_four_le _ _
        _ = _ := by ring
    · simp only [kStopStep, Set.indicator_of_notMem hy, A, enorm_zero]
      norm_num
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_add_left' ((aemeasurable_stoppedK_pow hb hE1 hE2 s h τ m R W i (i + 1) hV
      ij).const_mul 8), lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]

/-- The lagged term: `E[1_{A_i}|X_i|⁴] ≤ C` from `ComplexKStoppedMoment` at `i − 1` (and `= 0` at
`i = n_s`). -/
theorem lintegral_lagged_le {b E s h : ℝ} {τ m : Fin np → ℝ} (hτ : ∀ i, s < τ i) (R : ℝ)
    (W : ℕ) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (ij : Fin np × Fin np) {i : ℕ} (hi : closeLen s W ≤ i) {c : ℝ≥0∞}
    (hP : closeLen s W < i → ∫⁻ y, (b3Alive b E s h τ m R W (i - 1) Vs).indicator
      (fun y => ‖b3ClosedKAt b E s h τ m W (i - 1 + 1) y ij.1 ij.2‖ₑ ^ 4) y
        ∂closedLaw b W np ≤ c) :
    ∫⁻ y, (b3Alive b E s h τ m R W i Vs).indicator
      (fun y => ‖b3ClosedKAt b E s h τ m W i y ij.1 ij.2‖ₑ ^ 4) y ∂closedLaw b W np ≤ c := by
  rcases hi.eq_or_lt with he | hlt
  · subst he
    have h0 : ∀ y, (b3Alive b E s h τ m R W (closeLen s W) Vs).indicator
        (fun y => ‖b3ClosedKAt b E s h τ m W (closeLen s W) y ij.1 ij.2‖ₑ ^ 4) y = 0 := by
      intro y
      simp [b3ClosedKAt_start hτ]
    simp only [h0, lintegral_zero]
    exact zero_le
  · refine le_trans (lintegral_mono fun y => ?_) (hP hlt)
    have hii : i - 1 + 1 = i := by omega
    by_cases hy : y ∈ b3Alive b E s h τ m R W i Vs
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_mem (b3Alive_anti (Nat.sub_le i 1) hy), hii]
    · rw [Set.indicator_of_notMem hy]
      exact zero_le

/-- **`KStopBirthSum` from the per-length stopped fourth moment.** -/
theorem kStopBirthSum_of_stopped (hK : ComplexKStoppedMoment) : KStopBirthSum := by
  intro b E np τ m T s h K Vs hF R
  have hτ := hF.2.2.1
  obtain ⟨C, hC⟩ := hK b E np τ m T s h K Vs hF R
  set C' : ℝ := max C 0
  refine ⟨(np : ℝ) ^ 3 * ((np : ℝ) * (8 * (C' + C'))), ?_⟩
  have hb1 : b < 1 := by linarith [hF.1.2.1]
  have hE1 := hF.1.2.2.1
  have hE2 := hF.1.2.2.2.1
  filter_upwards [hC, hF.2.2.2.2.2] with W hW hVW ij
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set N := ⌊(W : ℝ) * T⌋₊
  set F := (Finset.Ico (closeLen s W) N).filter (fun i => IsBirthStep τ W i)
  have hcard : F.card ≤ np := Birth.card_steps_le τ W _
  have hstep : ∀ i ∈ F, ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4
      ∂closedLaw b W np ≤ 8 * (ENNReal.ofReal C' + ENNReal.ofReal C') := by
    intro i hiF
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 hiF).1
    refine (lintegral_kStopStep_pow_four_le hb1 hE1 hE2 s h τ m R W i hmV ij).trans ?_
    rw [mul_add]
    gcongr
    · exact (hW i hi1 hi2 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))
    · refine lintegral_lagged_le hτ R W (Vs W) ij hi1 fun hlt => ?_
      exact (hW (i - 1) (by omega) (by omega) ij).trans
        (ENNReal.ofReal_le_ofReal (le_max_left C 0))
  have hae : ∀ i ∈ F, AEMeasurable (fun y => ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4)
      (closedLaw b W np) := fun i _ =>
    (aemeasurable_kStopStep hb1 hE1 hE2 s h τ m R W i hmV ij).enorm.pow_const 4
  calc ∫⁻ y, (∑ i ∈ F, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ) ^ 4 ∂closedLaw b W np
      ≤ ∫⁻ y, (F.card : ℝ≥0∞) ^ 3 *
          ∑ i ∈ F, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np :=
        lintegral_mono fun y => birthK_sum_pow_four_le F _
    _ = (F.card : ℝ≥0∞) ^ 3 *
          ∑ i ∈ F, ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum' _ hae]
    _ ≤ (np : ℝ≥0∞) ^ 3 * (F.card • (8 * (ENNReal.ofReal C' + ENNReal.ofReal C'))) := by
        gcongr
        exact Finset.sum_le_card_nsmul _ _ _ hstep
    _ ≤ (np : ℝ≥0∞) ^ 3 * ((np : ℝ≥0∞) * (8 * (ENNReal.ofReal C' + ENNReal.ofReal C'))) := by
        rw [nsmul_eq_mul]
        gcongr
    _ = ENNReal.ofReal ((np : ℝ) ^ 3 * ((np : ℝ) * (8 * (C' + C')))) := by
        have hC' : 0 ≤ C' := le_max_right C 0
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hC' hC',
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
        norm_num

/-- **`KStopBirthSum` from the raw moments and the correction estimate**
(`complexKStoppedMoment_of_corr`). -/
theorem kStopBirthSum_of_corr (hR : RawTagMoments) (hC : ComplexKCorrMoment) : KStopBirthSum :=
  kStopBirthSum_of_stopped (complexKStoppedMoment_of_corr hR hC)

/-- **`KStopBirthSum` from the input hypotheses and the correction estimate
`ComplexKCorrMoment`.** -/
theorem kStopBirthSum_of_baseContracts (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : ComplexKCorrMoment) : KStopBirthSum :=
  kStopBirthSum_of_stopped (complexKStoppedMoment_of_baseContracts hGA hLp hSR hMT hC)

end BlockBand.SourceProcess.PhysApprox.B3
