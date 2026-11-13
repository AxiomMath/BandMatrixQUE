module

public import BlockBand.SourceProcess.FullSourceStops.TagSup

/-!
# The field `supMoments` of `FullSourceStopsEnergyUniformContract`

* A tag source is `Tr Q = W⁻¹Re Tr Y_{j;k_a} = t_{j;k_a}`; its supremum is bounded by `TagSupBulk`.
* An interval source is `Tr Q = Σ_{i<j} (q_a((i+1)/W)/W) t_{j;i}`, so with `0 ≤ q_a ≤ Q_a` and
  `M_i = sup_{j ≤ TW} t_{j;i}`, `sup_j Tr Q ≤ (Q_a/W) Σ_{i ≤ N} M_i`, `N = ⌊T₀W⌋`. The power-mean
  inequality and `TagSupBulk` at the integer exponent `n ≥ p` give
  `E[(sup_j Tr Q)^n] ≤ (Q_a(T₀+1))^n C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSource
open scoped ENNReal

variable {W : ℕ}

/-- An admissible interval test is bounded: `0 ≤ q ≤ Q`. -/
theorem intervalTest_bounded {q : ℝ → ℝ} {s T : ℝ} (h : IsSourceTest s T q) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x, 0 ≤ q x ∧ q x ≤ Q := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h.2.2
  refine ⟨max C 0, le_max_right _ _, fun x => ⟨h.1 x, ?_⟩⟩
  by_cases hx : x ∈ Set.Icc s T
  · exact ((Real.le_norm_self _).trans (hC x hx)).trans (le_max_left _ _)
  · rw [h.2.1 x hx]; exact le_max_right _ _

theorem sourceTrace_tag (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (ω : GrowthPath W) (a : Fin nT) :
    sourceTrace b E k q W j ω (Sum.inl a) = tagMass b E W j (k a) ω := by
  simp only [sourceTrace, sourceLetter, Sum.elim_inl, letterMatrix, Matrix.trace_smul, tagMass,
    smul_eq_mul]
  rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]

theorem sourceTrace_interval (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (ω : GrowthPath W) (a : Fin nI) :
    sourceTrace b E k q W j ω (Sum.inr a) =
      ∑ i ∈ Finset.range j, q a (((i + 1 : ℕ) : ℝ) / W) / W * tagMass b E W j i ω := by
  simp only [sourceTrace, sourceLetter, Sum.elim_inr, letterMatrix, intervalSource,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul,
    tagMass]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos W with hW | hW
  · simp [hW]
  · field_simp

/-- **Interval sources**: `sup_j Tr Q_a ≤ (Q/W) Σ_{i ≤ N} M_i`. -/
theorem enorm_sourceTrace_interval_le (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ)
    (q : Fin nI → ℝ → ℝ) (a : Fin nI) {Q : ℝ} (hq : ∀ x, 0 ≤ q a x ∧ q a x ≤ Q) {T : ℝ}
    {N j : ℕ} (hjN : j ≤ N) (hjT : (j : ℝ) ≤ T * W) (ω : GrowthPath W) :
    ‖sourceTrace b E k q W j ω (Sum.inr a)‖ₑ ≤ ENNReal.ofReal (Q / W) *
      ∑ i ∈ Finset.range (N + 1), ⨆ (j' : ℕ) (_ : (j' : ℝ) ≤ T * W),
        ENNReal.ofReal (tagMass b E W j' i ω) := by
  have hQ : 0 ≤ Q := (hq 0).1.trans (hq 0).2
  have hterm : ∀ i, 0 ≤ q a (((i + 1 : ℕ) : ℝ) / W) / W * tagMass b E W j i ω := fun i =>
    mul_nonneg (div_nonneg (hq _).1 (Nat.cast_nonneg W)) (tagMass_nonneg b E j i ω)
  have hnn : 0 ≤ sourceTrace b E k q W j ω (Sum.inr a) := by
    rw [sourceTrace_interval]; exact Finset.sum_nonneg fun i _ => hterm i
  have hle : sourceTrace b E k q W j ω (Sum.inr a) ≤
      ∑ i ∈ Finset.range (N + 1), Q / W * tagMass b E W j i ω := by
    rw [sourceTrace_interval]
    refine (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hq _).2 (Nat.cast_nonneg W)) (tagMass_nonneg b E j i ω)).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => mul_nonneg (div_nonneg hQ (Nat.cast_nonneg W)) (tagMass_nonneg b E j i ω)
  rw [Real.enorm_eq_ofReal hnn]
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      mul_nonneg (div_nonneg hQ (Nat.cast_nonneg W)) (tagMass_nonneg b E j i ω),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ENNReal.ofReal_mul (div_nonneg hQ (Nat.cast_nonneg W))]
  gcongr
  exact le_iSup₂_of_le (f := fun (j' : ℕ) (_ : (j' : ℝ) ≤ T * W) =>
    ENNReal.ofReal (tagMass b E W j' i ω)) j hjT le_rfl

/-- The power-mean step for the interval bound. -/
theorem lintegral_intervalBound_le (b E T : ℝ) (N n : ℕ) (hn : 1 ≤ n) {Qm C : ℝ} (hQm : 0 ≤ Qm)
    (hM : ∀ i, ∫⁻ ω, (⨆ (j' : ℕ) (_ : (j' : ℝ) ≤ T * W),
      ENNReal.ofReal (tagMass b E W j' i ω)) ^ (n : ℝ) ∂growthPathLaw W b ≤ ENNReal.ofReal C) :
    ∫⁻ ω, (ENNReal.ofReal (Qm / W) * ∑ i ∈ Finset.range (N + 1), ⨆ (j' : ℕ)
        (_ : (j' : ℝ) ≤ T * W), ENNReal.ofReal (tagMass b E W j' i ω)) ^ n ∂growthPathLaw W b ≤
      ENNReal.ofReal ((Qm / W) ^ n * (((N : ℝ) + 1) ^ ((n : ℝ) - 1) * (((N : ℝ) + 1) * C))) := by
  set M : ℕ → GrowthPath W → ℝ≥0∞ := fun i ω => ⨆ (j' : ℕ) (_ : (j' : ℝ) ≤ T * W),
    ENNReal.ofReal (tagMass b E W j' i ω)
  have hMm : ∀ i, Measurable (M i) := fun i =>
    Measurable.iSup fun j => Measurable.iSup_Prop _ (measurable_tagMass b E j i).ennreal_ofReal
  have hSm : Measurable fun ω => ∑ i ∈ Finset.range (N + 1), M i ω :=
    Finset.measurable_sum _ fun i _ => hMm i
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcard : ((Finset.range (N + 1)).card : ℝ≥0∞) = ENNReal.ofReal ((N : ℝ) + 1) := by
    rw [Finset.card_range, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]; push_cast; rfl
  calc ∫⁻ ω, (ENNReal.ofReal (Qm / W) * ∑ i ∈ Finset.range (N + 1), M i ω) ^ n ∂growthPathLaw W b
      = ENNReal.ofReal (Qm / W) ^ n *
          ∫⁻ ω, (∑ i ∈ Finset.range (N + 1), M i ω) ^ (n : ℝ) ∂growthPathLaw W b := by
        simp only [mul_pow, ENNReal.rpow_natCast]
        exact lintegral_const_mul _ (hSm.pow_const n)
    _ ≤ ENNReal.ofReal (Qm / W) ^ n * (ENNReal.ofReal ((N : ℝ) + 1) ^ ((n : ℝ) - 1) *
          ∑ i ∈ Finset.range (N + 1), ∫⁻ ω, M i ω ^ (n : ℝ) ∂growthPathLaw W b) := by
        gcongr
        calc ∫⁻ ω, (∑ i ∈ Finset.range (N + 1), M i ω) ^ (n : ℝ) ∂growthPathLaw W b
            ≤ ∫⁻ ω, ((Finset.range (N + 1)).card : ℝ≥0∞) ^ ((n : ℝ) - 1) *
                ∑ i ∈ Finset.range (N + 1), M i ω ^ (n : ℝ) ∂growthPathLaw W b :=
              lintegral_mono fun ω => ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hn1
          _ = _ := by
              rw [hcard, lintegral_const_mul _ (Finset.measurable_sum _ fun i _ =>
                (hMm i).pow_const _), lintegral_finsetSum _ fun i _ => (hMm i).pow_const _]
    _ ≤ ENNReal.ofReal (Qm / W) ^ n * (ENNReal.ofReal ((N : ℝ) + 1) ^ ((n : ℝ) - 1) *
          (ENNReal.ofReal ((N : ℝ) + 1) * ENNReal.ofReal C)) := by
        gcongr
        refine (Finset.sum_le_sum fun i _ => hM i).trans (le_of_eq ?_)
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = ENNReal.ofReal ((Qm / W) ^ n * (((N : ℝ) + 1) ^ ((n : ℝ) - 1) * (((N : ℝ) + 1) * C))) := by
        rw [← ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]

/-- **The field `supMoments`** of `FullSourceStopsEnergyUniformContract`, from `TagSupBulk`. -/
theorem supMoments_of (h : TagSupBulk) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ ε T p : ℝ, 0 < ε → ε < T →
    0 < p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ (k : Fin nT → ℕ) (a : Fin nT ⊕ Fin nI),
      ∫⁻ ω, (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W), ‖sourceTrace b E k q W j ω a‖ₑ) ^ p
        ∂growthPathLaw W b ≤ ENNReal.ofReal C := by
  intro b hb0 hb κI hκ nT nI q hq ε T p hε hεT hp
  have hT : 0 < T := hε.trans hεT
  set n : ℕ := max 1 ⌈p⌉₊
  have hn : 1 ≤ n := le_max_left _ _
  have hpn : p ≤ n := (Nat.le_ceil p).trans (by exact_mod_cast le_max_right 1 ⌈p⌉₊)
  obtain ⟨C1, W1, h1⟩ := h b hb0 hb κI T p hκ hp
  obtain ⟨Cn, Wn, hCn⟩ := h b hb0 hb κI T n hκ (by exact_mod_cast hn)
  have hQ : ∀ a, ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x, 0 ≤ q a x ∧ q a x ≤ Q := fun a => by
    obtain ⟨s, T', hs⟩ := hq a; exact intervalTest_bounded hs
  choose Q hQ0 hQ using hQ
  set Qm := ∑ a, Q a
  have hQm : 0 ≤ Qm := Finset.sum_nonneg fun a _ => hQ0 a
  have hQa : ∀ a x, 0 ≤ q a x ∧ q a x ≤ Qm := fun a x =>
    ⟨(hQ a x).1, (hQ a x).2.trans (Finset.single_le_sum (fun a _ => hQ0 a) (Finset.mem_univ a))⟩
  set Cn' := max Cn 0
  refine ⟨max C1 (1 + (Qm * (T + 1)) ^ n * Cn'), max (max W1 Wn) 1, fun W hW E hE k a => ?_⟩
  have hW1' : W1 ≤ W := le_trans (by simp) hW
  have hWn : Wn ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := le_trans (by simp) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  rcases a with a | a
  · refine le_trans ?_ ((h1 W hW1' E hE (k a)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp.le
    refine iSup₂_mono' fun j hj => ⟨j, hj.2, ?_⟩
    rw [sourceTrace_tag, Real.enorm_eq_ofReal (tagMass_nonneg b E j (k a) ω)]
    rfl
  · set N := ⌊T * W⌋₊
    have hNT : (N : ℝ) ≤ T * W := Nat.floor_le (by positivity)
    set Z : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal (Qm / W) *
      ∑ i ∈ Finset.range (N + 1), ⨆ (j' : ℕ) (_ : (j' : ℝ) ≤ T * W),
        ENNReal.ofReal (tagMass b E W j' i ω)
    have hpt : ∀ ω, (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W),
        ‖sourceTrace b E k q W j ω (Sum.inr a)‖ₑ) ≤ Z ω := fun ω =>
      iSup₂_le fun j hj => enorm_sourceTrace_interval_le b E k q a (hQa a)
        (Nat.le_floor hj.2) hj.2 ω
    have hZ := lintegral_intervalBound_le (W := W) b E T N n hn hQm
      fun i => (hCn W hWn E hE i).trans (ENNReal.ofReal_le_ofReal (le_max_left Cn 0))
    have hreal : (Qm / W) ^ n * (((N : ℝ) + 1) ^ ((n : ℝ) - 1) * (((N : ℝ) + 1) * Cn')) ≤
        (Qm * (T + 1)) ^ n * Cn' := by
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have e : ((N : ℝ) + 1) ^ ((n : ℝ) - 1) * ((N : ℝ) + 1) = ((N : ℝ) + 1) ^ n := by
        rw [Real.rpow_sub_one hN1.ne', Real.rpow_natCast, div_mul_cancel₀ _ hN1.ne']
      have hNW : ((N : ℝ) + 1) / W ≤ T + 1 := by
        rw [div_le_iff₀ hW0]
        have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
        nlinarith
      calc (Qm / W) ^ n * (((N : ℝ) + 1) ^ ((n : ℝ) - 1) * (((N : ℝ) + 1) * Cn'))
          = (Qm * (((N : ℝ) + 1) / W)) ^ n * Cn' := by
            rw [← mul_assoc (((N : ℝ) + 1) ^ ((n : ℝ) - 1)), e, mul_div_assoc', div_pow, div_pow,
              mul_pow]
            field_simp
        _ ≤ (Qm * (T + 1)) ^ n * Cn' := by
            gcongr
    calc ∫⁻ ω, (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W),
          ‖sourceTrace b E k q W j ω (Sum.inr a)‖ₑ) ^ p ∂growthPathLaw W b
        ≤ ∫⁻ ω, (1 + Z ω ^ n) ∂growthPathLaw W b :=
          lintegral_mono fun ω => (ENNReal.rpow_le_rpow (hpt ω) hp.le).trans
            (rpow_le_one_add_pow _ hp.le hpn)
      _ = 1 + ∫⁻ ω, Z ω ^ n ∂growthPathLaw W b := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + ENNReal.ofReal ((Qm * (T + 1)) ^ n * Cn') := by
          gcongr; exact hZ.trans (ENNReal.ofReal_le_ofReal hreal)
      _ = ENNReal.ofReal (1 + (Qm * (T + 1)) ^ n * Cn') := by
          rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)

end BlockBand.SourceProcess.FullSourceStops
