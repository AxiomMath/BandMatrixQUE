module

public import BlockBand.SourceProcess.PhysApprox.B3GramStepSmall
public import BlockBand.SourceProcess.PhysApprox.B3BirthMOther
public import BlockBand.SourceProcess.PhysApprox.B3BirthPAssembly

/-!
# `ComplexBirthCrossGram` from the weak-rate Gram estimate

`complexBirthOtherColL2_of` uses `ComplexBirthOldL2` only at the Gram coordinate `(0, c, c)` of an
old column, and only through `E[1_{A_j}|dM_cc|²] ≤ CO/W ≤ 1`. At the weak rate
(`ClosedGramStepFourSmall`, `W r_W → 0`) the same quantity is `≤ W r_W + 1/W ≤ 1` eventually:

* **`gramBirthOldOne_of_small`**: the old Gram rows at a birth step have
  `E[1_{A_j}|dX_e|²] ≤ 1`, eventually (the bounded form of the Gram rows of `ComplexBirthOldL2`);
* **`complexBirthOtherColL2_of_small`**: `ComplexBirthOtherColL2`. The newborn-column branch is
  the argument of `complexBirthOtherColL2_of`, reproduced because that theorem takes
  `ComplexBirthOldL2` as a whole; only the old-column branch changes;
* **`complexBirthCrossGram_of_small`**: `ComplexBirthCrossGram`, through
  `complexBirthCrossGram_of`;
* **`genReqBirth_of_small`**: `GenReqBirth`, the conclusion of `genReqBirth_of_baseContracts`, with
  `ComplexBirthOldL2` and `ComplexBirthCrossGram` replaced by `KCorrStepFourAt` and
  `ClosedGramStepFourSmall`. `genReqBirth_of_pins` uses `ComplexBirthOldL2` only through
  `complexBirthOld_of_L2`, i.e. as the `L¹` estimate `ComplexBirthOld`, which
  `complexBirthOld_of_small` gives.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal ComplexConjugate ComplexOrder

open BirthM

variable {W : ℕ}

/-- **The old Gram rows at a birth step are bounded in `L²`** at the weak rate:
`E[1_{A_j}|dX_e|²] ≤ W r_W + 1/W ≤ 1`, eventually. -/
theorem gramBirthOldOne_of_small (hG : ClosedGramStepFourSmall) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : SrcCol K (Fin np)),
        ∀ᶠ W : ℕ in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j →
          ¬ IsNewCoord τ W j (Sum.inl (0, c, c) : CIdx K np) →
          ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3dX b E s h τ m W j (Vs W) (Sum.inl (0, c, c) : CIdx K np)) y‖ₑ ^ 2
            ∂closedLaw b W np ≤ ENNReal.ofReal 1 := by
  intro b E np τ m T s h K Vs hD R c
  obtain ⟨r, hr0, hr, hev⟩ := hG b E np τ m T s h K Vs hD R
  have h1 : Tendsto (fun W : ℕ => 1 / (W : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun W : ℕ => (W : ℝ) * r W + 1 / (W : ℝ)) atTop (𝓝 0) := by
    have := hr.add h1
    rwa [add_zero] at this
  have hsmall : ∀ᶠ W : ℕ in atTop, (W : ℝ) * r W + 1 / (W : ℝ) ≤ 1 :=
    hsum.eventually (ge_mem_nhds one_pos)
  filter_upwards [hev, hsmall, eventually_ge_atTop 1] with W hW hWs hW1 j hj1 hj2 _ hn
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  set f : ProbedPath W np × ℝ → ℝ≥0∞ := fun y => ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
    (b3dX b E s h τ m W j (Vs W) (Sum.inl (0, c, c) : CIdx K np)) y‖ₑ
  calc ∫⁻ y, f y ^ 2 ∂closedLaw b W np
      ≤ ∫⁻ y, ((W : ℝ≥0∞) * f y ^ 4 + ENNReal.ofReal (1 / W)) ∂closedLaw b W np :=
        lintegral_mono fun y => sq_le_mul_pow_four_add (f y) hW1
    _ = (W : ℝ≥0∞) * ∫⁻ y, f y ^ 4 ∂closedLaw b W np + ENNReal.ofReal (1 / W) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top W), lintegral_const, measure_univ,
          mul_one]
    _ ≤ (W : ℝ≥0∞) * ENNReal.ofReal (r W) + ENNReal.ofReal (1 / W) := by
        gcongr
        exact hW j (Finset.mem_Ico.2 ⟨hj1, hj2⟩) (0, c, c) hn
    _ = ENNReal.ofReal ((W : ℝ) * r W + 1 / (W : ℝ)) := by
        rw [← ENNReal.ofReal_natCast W, ← ENNReal.ofReal_mul hWr.le,
          ← ENNReal.ofReal_add (mul_nonneg hWr.le (hr0 W)) (by positivity)]
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hWs

/-- **`ComplexBirthOtherColL2` from the weak-rate Gram estimate** (old columns: the bounded `L²`
form; newborn columns: the argument of `complexBirthOtherColL2_of`). -/
theorem complexBirthOtherColL2_of_small (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hG : ClosedGramStepFourSmall) :
    ComplexBirthOtherColL2 := by
  intro b E np τ m T s h K Vs hD R i c hc
  have hCO := gramBirthOldOne_of_small hG b E np τ m T s h K Vs hD R c
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, hm0, hτT⟩, hs, hsτ, hh0, hh1, -⟩ := hD
  have hTB := TagBirth.tagBirthValue_holds hMT hGA
    BlockBand.GaussianCalculus.gaussianLpGradient_holds
  have hsT : s / 2 < T := by linarith [hsτ i, hτT i]
  obtain ⟨Wt, hWt⟩ := hTB.trace b hb0 hb E hE1 hE2 (s / 2) T 1 (by positivity) hsT le_rfl 1
    one_pos
  obtain ⟨C, Ws, hWs⟩ := hTB.square b hb0 hb E hE1 hE2 (s / 2) T (by positivity) hsT
  set C' := max C 0
  set CO' := (0 : ℝ)
  obtain ⟨μc, hμc, hμeq⟩ : ∃ μ : ℝ, 0 ≤ μ ∧ ∀ i' : Fin np, c = Sum.inr i' → μ = m i' := by
    rcases c with k | i'
    · exact ⟨0, le_rfl, fun i' h => absurd h Sum.inl_ne_inr⟩
    · exact ⟨m i', hm0 i', fun i'' h => by rw [Sum.inr_injective h]⟩
  have hd : 0 ≤ dStar b := by
    unfold dStar; have : 0 < 1 - b := by linarith
    positivity
  refine ⟨max (max R 0 + 1 / 2 + 1 / 2) (2 * (μc * (1 + 1) + μc * dStar b) + 2 * (2 * (μc * 1))),
    ?_⟩
  filter_upwards [hCO, newbornFarMass_holds hMT hGA b hb0 hb E hE1 hE2 s T hs 1 one_pos,
    eventually_ge_atTop (max (max Wt Ws) (max (⌈2 / s⌉₊ + 1) (⌈CO'⌉₊ + ⌈C'⌉₊ + 1)))]
    with W hOW hFar hW j hj1 hj2 hij
  have hWt' : Wt ≤ W := le_trans (by simp) hW
  have hWs' : Ws ≤ W := le_trans (by simp) hW
  have hW2 : ⌈2 / s⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hWC : ⌈CO'⌉₊ + ⌈C'⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW1
  have hCW : C' / W ≤ 1 := by
    rw [div_le_one hWr]
    have := Nat.le_ceil C'
    have : ((⌈C'⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈C'⌉₊ ≤ W)
    linarith
  by_cases hnew : IsNewCol τ W j c
  · -- another newborn of the same step
    rcases c with k | i'
    · exact absurd hnew id
    have hi' : ⌊(W : ℝ) * τ i'⌋₊ = j := hnew
    have hμ : μc = m i' := hμeq i' rfl
    have hm := hm0 i'
    subst hi'
    set k := ⌊(W : ℝ) * τ i'⌋₊ with hkdef
    have hWsr : 2 ≤ (W : ℝ) * s := by
      have : 2 / s ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 / s⌉₊ ≤ W))
      rw [div_le_iff₀ hs] at this; linarith
    have hns : (W : ℝ) * s - 1 < ⌊(W : ℝ) * s⌋₊ := Nat.sub_one_lt_floor _
    have hkε : s / 2 * W ≤ k := by
      have : ((⌊(W : ℝ) * s⌋₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hj1
      nlinarith
    have hkT : ((k + 1 : ℕ) : ℝ) ≤ T * W := by
      have hpos : 0 < ⌊(W : ℝ) * T⌋₊ := by omega
      have h1 : (1 : ℝ) ≤ W * T := Nat.floor_pos.mp hpos
      have h2 : ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ W * T := Nat.floor_le (by linarith)
      have h3 : k + 1 ≤ ⌊(W : ℝ) * T⌋₊ := hj2
      have h4 : ((k + 1 : ℕ) : ℝ) ≤ ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast h3
      linarith [mul_comm (W : ℝ) T]
    have hlt : k < k + 1 := Nat.lt_succ_self k
    have hTr := hWt W hWt' k hkε hkT
    have hYm : Measurable fun ω : GrowthPath W =>
        (W : ℂ)⁻¹ * (tagResponse b E W (k + 1) k ω).trace - (dStar b : ℂ) :=
      (measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
        (FullSourceStops.measurable_tagResponse b E (k + 1) k))).sub_const _
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hYm.aestronglyMeasurable] at hTr
    have hSq := lintegral_sqrt_trace_sq_le b E hlt (hWs W hWs' k hkε hkT)
    have hsq : Real.sqrt (C' / W) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hCW
    have hVm : Measurable fun x : ProbedPath W np => fun w => probeFrame b E W (k + 1) τ m x w i' :=
      measurable_probeFrame_col b E τ m i'
    have hCm : Measurable fun y : ProbedPath W np × ℝ =>
        physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2) :=
      measurable_physClosingMapAt_comp b E s h (k + 1) (measurable_fst.comp measurable_fst)
        (measurable_phase.comp measurable_snd)
    have hf1 : Measurable fun x : ProbedPath W np =>
        ENNReal.ofReal (l2 (fun w => probeFrame b E W (k + 1) τ m x w i') ^ 2) :=
      ((continuous_l2.measurable.comp hVm).pow_const 2).ennreal_ofReal
    have hf1' : Measurable fun x : ProbedPath W np =>
        ENNReal.ofReal |l2 (fun w => probeFrame b E W (k + 1) τ m x w i') ^ 2 -
          m i' * dStar b| :=
      (((continuous_l2.measurable.comp hVm).pow_const 2).sub_const _).abs.ennreal_ofReal
    -- `E‖V‖² ≤ m(2) + m d`
    have hV2 : ∫⁻ y, ENNReal.ofReal (l2 (fun w => probeFrame b E W (k + 1) τ m y.1 w i') ^ 2)
        ∂closedLaw b W np ≤ ENNReal.ofReal (m i' * (1 + 1) + m i' * dStar b) := by
      rw [Birth.lintegral_closedLaw_fst hf1]
      have hpt : ∀ x : ProbedPath W np,
          ENNReal.ofReal (l2 (fun w => probeFrame b E W (k + 1) τ m x w i') ^ 2) ≤
            ENNReal.ofReal |l2 (fun w => probeFrame b E W (k + 1) τ m x w i') ^ 2 -
              m i' * dStar b| + ENNReal.ofReal (m i' * dStar b) := by
        intro x
        rw [← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
        have := le_abs_self (l2 (fun w => probeFrame b E W (k + 1) τ m x w i') ^ 2 - m i' * dStar b)
        exact ENNReal.ofReal_le_ofReal (by linarith)
      refine (lintegral_mono hpt).trans ?_
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      have e := lintegral_newborn_sq_sub_le (W := W) (n := k + 1) b E τ m i' hm hlt (dStar b)
      rw [← hkdef] at e
      refine (add_le_add e le_rfl).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (q := 1 + 1) hm]
      refine add_le_add (mul_le_mul_right ?_ _) le_rfl
      refine (le_of_eq (lintegral_add_left ?_ _)).trans ?_
      · exact (measurable_const.mul (Real.continuous_sqrt.measurable.comp
          (Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
            (measurable_matrix_mul' (FullSourceStops.measurable_tagResponse b E (k + 1) k)
              (FullSourceStops.measurable_tagResponse b E (k + 1) k)))))).ennreal_ofReal
      rw [ENNReal.ofReal_add zero_le_one zero_le_one]
      exact add_le_add (hSq.trans (ENNReal.ofReal_le_ofReal hsq))
        (hTr.trans_eq ENNReal.ofReal_one.symm)
    have hL : ∫⁻ y, ENNReal.ofReal (l2 ((physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2))ᴴ *ᵥ
          (fun w => probeFrame b E W (k + 1) τ m y.1 w i') -
            fun w => probeFrame b E W (k + 1) τ m y.1 w i') ^ 2) ∂closedLaw b W np ≤
        ENNReal.ofReal (2 * (m i' * 1)) := by
      refine (lintegral_closed_leak_le hb0 hb hE1 hE2 hW1 s h hh0 hh1 (by omega) τ m i').trans ?_
      rw [lintegral_newborn_far_eq b E τ m i' hm hlt, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul hm]
      exact mul_le_mul_right (mul_le_mul_right (hFar k hj1 hj2) _) _
    have hm3 : Measurable fun y : ProbedPath W np × ℝ => ENNReal.ofReal
        (l2 ((physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2))ᴴ *ᵥ
          (fun w => probeFrame b E W (k + 1) τ m y.1 w i') -
            fun w => probeFrame b E W (k + 1) τ m y.1 w i') ^ 2) :=
      ((continuous_l2.measurable.comp ((RawTag.measurable_mulVec'
        (measurable_matrix_conjTranspose' hCm) (hVm.comp measurable_fst)).sub
          (hVm.comp measurable_fst))).pow_const 2).ennreal_ofReal
    have hpt : ∀ y, (b3Alive b E s h τ m R W k (Vs W)).indicator (fun y => ENNReal.ofReal
        (l2 (fun z => b3ClosedFrameAt b E s h τ m W (k + 1) (Vs W) y z (Sum.inr i')) ^ 2)) y ≤
          ENNReal.ofReal 2 *
            ENNReal.ofReal (l2 (fun w => probeFrame b E W (k + 1) τ m y.1 w i') ^ 2) +
          ENNReal.ofReal 2 * ENNReal.ofReal (l2 ((physClosingMapAt b E s h W (k + 1) y.1.1
            (phase y.2))ᴴ *ᵥ (fun w => probeFrame b E W (k + 1) τ m y.1 w i') -
              fun w => probeFrame b E W (k + 1) τ m y.1 w i') ^ 2) := by
      intro y
      refine (enorm_indicator_le' _ _ _).trans ?_
      rw [b3ClosedFrameAt_col, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (l2_sq_le_two
        ((physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2))ᴴ *ᵥ
          fun w => probeFrame b E W (k + 1) τ m y.1 w i')
        (fun w => probeFrame b E W (k + 1) τ m y.1 w i'))
    refine (lintegral_mono hpt).trans ?_
    refine (le_of_eq (lintegral_two_eq (hf1.comp measurable_fst) hm3 _ _)).trans ?_
    calc _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (m i' * (1 + 1) + m i' * dStar b) +
          ENNReal.ofReal 2 * ENNReal.ofReal (2 * (m i' * 1)) :=
          add_le_add (mul_le_mul_right hV2 _) (mul_le_mul_right hL _)
      _ = ENNReal.ofReal (2 * (μc * (1 + 1) + μc * dStar b) + 2 * (2 * (μc * 1))) := by
          rw [hμ, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  · -- an old column
    have hOj := hOW j hj1 hj2 ⟨i, hij⟩ (fun h => h.elim hnew hnew)
    refine (lintegral_mono fun y => indicator_l2_sq_old_le b E s h τ m R hj1 (Vs W) c y).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc _ ≤ ENNReal.ofReal (max R 0 + 1 / 2) + ENNReal.ofReal (1 / 2) * ENNReal.ofReal 1 := by
          exact add_le_add le_rfl (mul_le_mul_right hOj _)
      _ = ENNReal.ofReal (max R 0 + 1 / 2 + 1 / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by norm_num)]
          norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- **`ComplexBirthCrossGram` from the weak-rate Gram hypothesis** `ClosedGramStepFourSmall` and the
input hypotheses. -/
theorem complexBirthCrossGram_of_small (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hG : ClosedGramStepFourSmall) : ComplexBirthCrossGram :=
  complexBirthCrossGram_of hMT hGA (complexBirthOtherColL2_of_small hMT hGA hG)

/-- **`GenReqBirth` from the weak-rate Gram hypothesis** `ClosedGramStepFourSmall`,
`KCorrStepFourAt`, the input hypotheses and the two birth hypotheses `ComplexBirthGramDiag`,
`ComplexBirthKClosing` (the conclusion of `genReqBirth_of_baseContracts`).
-/
theorem genReqBirth_of_small (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hC : KCorrStepFourAt)
    (hG : ClosedGramStepFourSmall) (hGd : ComplexBirthGramDiag) (hCl : ComplexBirthKClosing) :
    GenReqBirth :=
  genReqBirth_of_parts (complexBirthOld_of_small hGA hLp hSR hMT hC hG) hGd
    (complexBirthKDiag_of_parts
      (complexBirthKFresh_of_trace (complexBirthKFreshTrace_holds hMT hGA hLp)) hCl)
    (complexBirthCross_of_parts (complexBirthCrossGram_of_small hMT hGA hG)
      (complexBirthCrossK_of_parts (complexBirthKFreshCross_holds hGA hLp hSR) hCl))

end BlockBand.SourceProcess.PhysApprox.B3
