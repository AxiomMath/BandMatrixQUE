module

public import BlockBand.SourceProcess.PhysApprox.B3BirthMCross
public import BlockBand.SourceProcess.PhysApprox.B3BirthOld

/-!
# The one-step moment of the other columns

At the birth step `j = ⌊Wτ_i⌋` and a closed column `c ≠ i`:
* if `c` is old at `j`: on the alive set `‖F_c(j)‖² ≤ Re Tr M_j < R` (`l2_sq_col_le_trace`) and
  `‖F_c(j+1)‖² = ‖F_c(j)‖² + Re dM_cc` (`l2_sq_col_succ`), so
  `1_{A_j}‖F_c(j+1)‖² ≤ R + 1/2 + |1_{A_j} dM_cc|²/2`, paid by the estimate `ComplexBirthOldL2`;
* if `c` is another newborn of the same step: `‖F_c‖² ≤ 2‖V_c‖² + 2‖F_c − V_c‖²`, paid by the
  newborn estimates `lintegral_newborn_sq_sub_le` and `lintegral_closed_leak_le`.

**`complexBirthOtherColL2_of`**: under `MatchedTracesContract` and `GaussianAbsorptionContract`,
`ComplexBirthOldL2` implies `ComplexBirthOtherColL2`; **`complexBirthCrossGram_holds`**: the same
hypotheses give `ComplexBirthCrossGram`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal ComplexConjugate ComplexOrder

namespace BirthM

variable {W : ℕ}

theorem gramEntry_diag_l2 {c : Type*} [Fintype c] (k : c) (F : Matrix (Fin 2 × Fin W) c ℂ) :
    gramEntry (0, k, k) (gramPair (nearPortProj W) F) = ((l2 (fun z => F z k) ^ 2 : ℝ) : ℂ) := by
  rw [gramEntry_gramPair, show gramQ W 0 = 1 by simp [gramQ], one_mulVec, dot_self_eq_l2_sq]

theorem l2_sq_col_le_trace {c : Type*} [Fintype c] (k : c) (F : Matrix (Fin 2 × Fin W) c ℂ) :
    l2 (fun z => F z k) ^ 2 ≤ ((gramPair (nearPortProj W) F).1.trace).re := by
  have e : ∀ d, (gramPair (nearPortProj W) F).1 d d = ((l2 (fun z => F z d) ^ 2 : ℝ) : ℂ) :=
    fun d => gramEntry_diag_l2 d F
  simp only [Matrix.trace, Matrix.diag, e, Complex.re_sum, Complex.ofReal_re]
  exact Finset.single_le_sum (f := fun d => l2 (fun z => F z d) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ k)

/-- `‖F_c(j+1)‖² = ‖F_c(j)‖² + Re dM_cc`. -/
theorem l2_sq_col_succ (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    l2 (fun z => b3ClosedFrameAt b E s h τ m W (j + 1) Vs y z c) ^ 2 =
      l2 (fun z => b3ClosedFrameAt b E s h τ m W j Vs y z c) ^ 2 +
        (b3dX b E s h τ m W j Vs (Sum.inl (0, c, c)) y).re := by
  have e1 := gramEntry_diag_l2 c (b3ClosedFrameAt b E s h τ m W (j + 1) Vs y)
  have e0 := gramEntry_diag_l2 c (b3ClosedFrameAt b E s h τ m W j Vs y)
  simp only [b3dX, b3X, cEntry, b3ClosedGramAt]
  rw [e1, e0, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
  ring

/-- **The old-column bound on the alive set**:
`1_{A_j}‖F_c(j+1)‖² ≤ R + 1/2 + |1_{A_j}dM_cc|²/2`. -/
theorem indicator_l2_sq_old_le (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (c : SrcCol K (Fin np)) (y : ProbedPath W np × ℝ) :
    (b3Alive b E s h τ m R W j Vs).indicator (fun y => ENNReal.ofReal
        (l2 (fun z => b3ClosedFrameAt b E s h τ m W (j + 1) Vs y z c) ^ 2)) y ≤
      ENNReal.ofReal (max R 0 + 1 / 2) + ENNReal.ofReal (1 / 2) *
        ‖(b3Alive b E s h τ m R W j Vs).indicator
          (b3dX b E s h τ m W j Vs (Sum.inl (0, c, c))) y‖ₑ ^ 2 := by
  by_cases hy : y ∈ b3Alive b E s h τ m R W j Vs
  · simp only [Set.indicator_of_mem hy]
    set d := b3dX b E s h τ m W j Vs (Sum.inl (0, c, c)) y
    have h1 := l2_sq_col_succ b E s h τ m j Vs c y
    have h2 := l2_sq_col_le_trace c (b3ClosedFrameAt b E s h τ m W j Vs y)
    have h3 : ((gramPair (nearPortProj W) (b3ClosedFrameAt b E s h τ m W j Vs y)).1.trace).re
        < R := hy.2 j hj le_rfl
    have h4 : d.re ≤ ‖d‖ := Complex.re_le_norm d
    have h5 : ‖d‖ ≤ 1 / 2 + 1 / 2 * ‖d‖ ^ 2 := by nlinarith [sq_nonneg (‖d‖ - 1)]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : R ≤ max R 0 := le_max_left _ _
    linarith
  · simp only [Set.indicator_of_notMem hy]
    exact zero_le

theorem enorm_indicator_le' {α : Type*} (A : Set α) (f : α → ℝ≥0∞) (y : α) :
    A.indicator f y ≤ f y := by
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]; exact zero_le

theorem lintegral_two_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (a c : ℝ≥0∞) :
    ∫⁻ y, (a * f y + c * g y) ∂μ = a * ∫⁻ y, f y ∂μ + c * ∫⁻ y, g y ∂μ := by
  rw [lintegral_add_left (f := fun y => a * f y) (hf.const_mul a), lintegral_const_mul a hf,
    lintegral_const_mul c hg]

theorem l2_sq_le_two (a V : Fin 2 × Fin W → ℂ) : l2 a ^ 2 ≤ 2 * l2 V ^ 2 + 2 * l2 (a - V) ^ 2 := by
  have h := abs_l2_sub_le a V
  have h1 : l2 a ≤ l2 V + l2 (a - V) := by linarith [le_abs_self (l2 a - l2 V)]
  have h0 := l2_nonneg a
  nlinarith [sq_nonneg (l2 V - l2 (a - V)), l2_nonneg V, l2_nonneg (a - V)]

end BirthM

open BirthM

/-- **`ComplexBirthOtherColL2`** from the input hypotheses and the one-step hypothesis on
the old columns, `ComplexBirthOldL2`. -/
theorem complexBirthOtherColL2_of (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hO : ComplexBirthOldL2) : ComplexBirthOtherColL2 := by
  intro b E np τ m T s h K Vs hD R i c hc
  obtain ⟨CO, hCO⟩ := hO b E np τ m T s h K Vs hD R (Sum.inl (0, c, c))
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, hm0, hτT⟩, hs, hsτ, hh0, hh1, -⟩ := hD
  have hTB := TagBirth.tagBirthValue_holds hMT hGA
    BlockBand.GaussianCalculus.gaussianLpGradient_holds
  have hsT : s / 2 < T := by linarith [hsτ i, hτT i]
  obtain ⟨Wt, hWt⟩ := hTB.trace b hb0 hb E hE1 hE2 (s / 2) T 1 (by positivity) hsT le_rfl 1
    one_pos
  obtain ⟨C, Ws, hWs⟩ := hTB.square b hb0 hb E hE1 hE2 (s / 2) T (by positivity) hsT
  set C' := max C 0
  set CO' := max CO 0
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
  have hCOW : CO' / W ≤ 1 := by
    rw [div_le_one hWr]
    have := Nat.le_ceil CO'
    have : ((⌈CO'⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈CO'⌉₊ ≤ W)
    linarith
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
          refine add_le_add le_rfl (mul_le_mul_right (hOj.trans (ENNReal.ofReal_le_ofReal ?_)) _)
          exact (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg W)).trans hCOW
      _ = ENNReal.ofReal (max R 0 + 1 / 2 + 1 / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by norm_num)]
          norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- **`ComplexBirthCrossGram` holds** given the one-step estimate on the old columns, `ComplexBirthOldL2`. -/
theorem complexBirthCrossGram_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hO : ComplexBirthOldL2) : ComplexBirthCrossGram :=
  complexBirthCrossGram_of hMT hGA (complexBirthOtherColL2_of hMT hGA hO)

end BlockBand.SourceProcess.PhysApprox.B3
