module

public import BlockBand.Window.SmallCritical.Common

/-!
# The small-ratio critical theorem: mode clause

The mode variances of a critical marked limit satisfy
`v_m(P) ≤ C min(1, [τ/|m| + τ^{3/2}/m²]^{1-η})` for `m ≠ 0`.

Proof: the mode bound (`ModeBoundContract`, margin `ϑ`, ratio bound `T + 1`) with
`d_m ≥ 4|m|/n` bounds `E|A_{α,m}|² ≤ C(τ_W/|m| + τ_W^{3/2}/m²)`; the window transfer theorem
(`WindowTransferContract`, `q = 1/η`, the fixed window `refWeight`) applied to
`A_α = min(1, |A_{α,m}|²)` (scalar-shift invariant) bounds the finite window expectation; Fatou
under weak convergence passes to `P` (`markedLimit_lintegral_le`); spectral stationarity of `P`
(the translation clause of the stationarity proposition) makes the bound uniform in `w`
(`weightFunctional_le_four`). Constants depend only on `b, E, T, η` (through `ϑ` and the two
contracts); the remainder `r(n,W)` of the window transfer tends to zero along the subsequence.

Hypotheses: `WindowTransferContract` and `ModeBoundContract`; no other input.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

attribute [local instance] massProfile_opensMeasurableSpace

/-- The mark functional `g_m(ν) = |∫ e^{-2πimr} ν(dr)|²`. -/
def modeMark (m : ℤ) (ν : MassProfile) : ℝ :=
  ‖∫ r, fourier (-m) r ∂(ν : Measure Torus)‖ ^ 2

theorem continuous_modeMark (m : ℤ) : Continuous (modeMark m) :=
  ((continuous_profile_integral_complex _ (fourier (-m)).continuous).norm).pow 2

theorem modeMark_nonneg (m : ℤ) (ν : MassProfile) : 0 ≤ modeMark m ν := sq_nonneg _

theorem modeVariance_eq_weightFunctional (P : ProbabilityMeasure MarkedPointMeasure)
    (w : SpectralWeight) (m : ℤ) :
    modeVariance P w m = weightFunctional P (modeMark m) w := rfl

/-- The window observable `A_α = min(1, |A_{α,m}|²)`. -/
def modeObservable (p : Parameters) (m : ℤ) (α : Fin p.N) (H : p.SiteMatrix) : ℝ :=
  min 1 (‖physicalMode p α (m : ZMod p.n) H‖ ^ 2)

variable {p : Parameters}

theorem measurable_modeObservable (m : ℤ) (α : Fin p.N) :
    Measurable (modeObservable p m α) :=
  measurable_const.min ((measurable_physicalMode p α _).norm.pow_const 2)

theorem modeObservable_mem (m : ℤ) (α : Fin p.N) (H : p.SiteMatrix) :
    0 ≤ modeObservable p m α H ∧ modeObservable p m α H ≤ 1 :=
  ⟨le_min zero_le_one (sq_nonneg _), min_le_left _ _⟩

theorem modeObservable_shift (m : ℤ) (α : Fin p.N) :
    IsScalarShiftInvariant (modeObservable p m α) :=
  isScalarShiftInvariant_blockMass α
    (fun pk => min 1 (‖mode (fun k => (pk k : ℂ)) (m : ZMod p.n)‖ ^ 2))

theorem integral_modeObservable_le (model : p.GaussianRingModel) (m : ℤ) (α : Fin p.N) :
    ∫ H, modeObservable p m α H ∂(model.law : Measure p.SiteMatrix) ≤
      min 1 (∫ H, ‖physicalMode p α (m : ZMod p.n) H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) := by
  have hi : Integrable (modeObservable p m α) (model.law : Measure p.SiteMatrix) :=
    (integrable_const (1 : ℝ)).mono' (measurable_modeObservable m α).aestronglyMeasurable
      (Eventually.of_forall fun H => by
        rw [Real.norm_eq_abs, abs_of_nonneg (modeObservable_mem m α H).1]
        exact (modeObservable_mem m α H).2)
  refine le_min ?_ ?_
  · calc _ ≤ ∫ _H, (1 : ℝ) ∂(model.law : Measure p.SiteMatrix) :=
          integral_mono hi (integrable_const _) fun H => (modeObservable_mem m α H).2
      _ = 1 := by simp
  · exact integral_mono hi (integrable_physicalMode_sq p model α _) fun H => min_le_right _ _

/-- Almost surely `g_m(ν_α) = |A_{α,m}|² = A_α` (block masses sum to one). -/
theorem modeMark_le_observable_ae (model : p.GaussianRingModel) (m : ℤ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α,
      modeMark m (physicalOrderedProfile p H α) ≤ 1 * modeObservable p m α H := by
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable,
    ae_all_iff.2 (fun α => physicalMode_norm_le_one_ae p model α (m : ZMod p.n))]
    with H hH hsep hn α
  rw [modeMark, fourier_profile_eq_physicalMode H hH hsep α m, one_mul, modeObservable,
    min_eq_right]
  exact pow_le_one₀ (norm_nonneg _) (hn α)

/-- Deterministic mode scale: with `d ≥ 4|m|/n`,
`1/(Wd) + 1/(√n W^{3/2} d²) ≤ (n/W)/|m| + (n/W)^{3/2}/m²`. -/
theorem mode_scale_le {n W d : ℝ} (hn : 0 < n) (hW : 0 < W) {m : ℝ} (hm : m ≠ 0)
    (hd : 4 * |m| / n ≤ d) :
    1 / (W * d) + 1 / (Real.sqrt n * (W * Real.sqrt W) * d ^ 2) ≤
      (n / W) / |m| + (n / W) ^ (3 / 2 : ℝ) / m ^ 2 := by
  have hma : 0 < |m| := abs_pos.mpr hm
  have hd4 : 0 < 4 * |m| / n := by positivity
  have hdpos : 0 < d := lt_of_lt_of_le hd4 hd
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  have h32 : (n / W) ^ (3 / 2 : ℝ) = n * Real.sqrt n / (W * Real.sqrt W) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (div_pos hn hW), Real.rpow_one,
      ← Real.sqrt_eq_rpow, Real.sqrt_div hn.le]
    field_simp
  rw [h32, hm2]
  have h1 : 1 / (W * d) ≤ (n / W) / |m| := by
    calc 1 / (W * d) ≤ 1 / (W * (4 * |m| / n)) :=
          one_div_le_one_div_of_le (by positivity) (by gcongr)
      _ = n / (4 * |m| * W) := by field_simp
      _ ≤ n / (|m| * W) := by
          apply div_le_div_of_nonneg_left hn.le (by positivity); nlinarith
      _ = (n / W) / |m| := by field_simp
  have h2 : 1 / (Real.sqrt n * (W * Real.sqrt W) * d ^ 2) ≤
      n * Real.sqrt n / (W * Real.sqrt W) / |m| ^ 2 := by
    have hdd : (4 * |m| / n) ^ 2 ≤ d ^ 2 := by gcongr
    calc 1 / (Real.sqrt n * (W * Real.sqrt W) * d ^ 2) ≤
          1 / (Real.sqrt n * (W * Real.sqrt W) * (4 * |m| / n) ^ 2) :=
          one_div_le_one_div_of_le (by positivity) (by gcongr)
      _ = n * Real.sqrt n / (16 * |m| ^ 2 * (W * Real.sqrt W)) := by
          have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn.le
          field_simp
          nlinarith [hsq]
      _ ≤ n * Real.sqrt n / (|m| ^ 2 * (W * Real.sqrt W)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [sq_nonneg |m|, mul_pos hW hsW]
      _ = _ := by field_simp
  linarith

/-- `2^{3/2} ≤ 3`. -/
theorem two_rpow_three_halves_le : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
  have h0 : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hsq : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  nlinarith

/-- Monotone comparison `X(t) ≤ 3 X(τ)` for `0 ≤ t ≤ 2τ`, `X(t) = t/|m| + t^{3/2}/m²`. -/
theorem modeRate_le_three {t τ m : ℝ} (ht : 0 ≤ t) (htτ : t ≤ 2 * τ) :
    t / |m| + t ^ (3 / 2 : ℝ) / m ^ 2 ≤ 3 * (τ / |m| + τ ^ (3 / 2 : ℝ) / m ^ 2) := by
  have hτ : 0 ≤ τ := by linarith
  have h1 : t / |m| ≤ 3 * (τ / |m|) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (abs_nonneg _)
  have h2 : t ^ (3 / 2 : ℝ) / m ^ 2 ≤ 3 * (τ ^ (3 / 2 : ℝ) / m ^ 2) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc t ^ (3 / 2 : ℝ) ≤ (2 * τ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ht htτ (by norm_num)
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * τ ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hτ
      _ ≤ 3 * τ ^ (3 / 2 : ℝ) := by
          gcongr
          exact two_rpow_three_halves_le
  linarith

/-- The mode clause of the small-ratio critical theorem, from the window transfer theorem and the
mode bound. -/
theorem smallCritical_mode (hWT : WindowTransferContract)
    (hMode : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      ModeBoundContract b θ T hb hb') :
    ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), E ^ 2 < 4 →
      ∀ T η : ℝ, 0 < η → η < 1 → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ P : ProbabilityMeasure MarkedPointMeasure,
          IsCriticalMarkedLimit τ b E hb hb' P →
          ∀ (w : SpectralWeight) (m : ℤ), m ≠ 0 →
            modeVariance P w m ≤ ENNReal.ofReal (C * min 1
              ((τ / |(m : ℝ)| + τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2) ^ (1 - η))) := by
  intro b hb hb' E hE T η hη hη1
  obtain ⟨ϑ, hϑ0, hϑ1, hϑl, hϑr⟩ := exists_bulk_margin hE
  have hρ := Parameters.semicircleDensity_pos_of_sq_lt_four E hE
  set q : ℝ := 1 / η with hqdef
  have hq : 1 < q := by rw [hqdef, lt_div_iff₀ hη]; linarith
  have hqe : 1 - 1 / q = 1 - η := by simp [hqdef]
  obtain ⟨C₁, r, hr, hWTb⟩ := hWT b hb hb' (T + 1) E (Parameters.semicircleDensity E) hE hρ
    refWeight continuous_refWeight hasCompactSupport_refWeight refWeight_nonneg integral_refWeight
    ϑ hϑ0 hϑ1 hϑl hϑr q hq
  obtain ⟨Cm, hCm0, hCm⟩ := hMode b ϑ (T + 1) hb hb' hϑ0 hϑ1
  set D : ℝ := max (3 * Cm) 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  set Cp : ℝ := max C₁ 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  refine ⟨8 * refMass * Cp * D, by have := refMass_pos; positivity, ?_⟩
  intro τ hτ hτT P hP w m hm
  set X : ℝ := τ / |(m : ℝ)| + τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2 with hX
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hX0 : 0 < X := by
    have : 0 < τ / |(m : ℝ)| := div_pos hτ (abs_pos.mpr hmR)
    have : 0 ≤ τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2 := by positivity
    linarith
  set ε : ℝ := min 1 (D * X) with hε
  have hε0 : 0 < ε := lt_min zero_lt_one (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hstat := stationary_of_criticalLimit hτ hE hP
  -- Step 1: the reference window at the limit.
  have hstep1 : weightFunctional P (modeMark m) refWeight ≤
      ENNReal.ofReal (2 * Cp * ε ^ (1 - η)) := by
    obtain ⟨s, R, φ, hφ, hlim⟩ := hP
    refine markedLimit_lintegral_le s R φ P hlim
      (continuous_prodTest continuous_refWeight (continuous_modeMark m))
      (hasCompactSupport_prodTest hasCompactSupport_refWeight _)
      (prodTest_nonneg refWeight_nonneg (modeMark_nonneg m)) _
      (fun j => r (s.n (φ j)) (s.W (φ j))) ((hr τ s hτ).comp hφ.tendsto_atTop) ?_
    have hev := hφ.tendsto_atTop.eventually
      (critical_eventually s hτ b hb hb' (by linarith : τ < T + 1) (2 * |(m : ℝ)|))
    filter_upwards [hev] with j hj
    obtain ⟨hj1, hj2, hj3, hj4⟩ := hj
    set p : Parameters := s.parameters b hb hb' (φ j) with hp
    have hn : (0 : ℝ) < s.n (φ j) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) (s.n_ge_four (φ j)))
    have hW : (0 : ℝ) < s.W (φ j) := by exact_mod_cast s.W_pos (φ j)
    have hnW : (s.n (φ j) : ℝ) ≤ (T + 1) * s.W (φ j) := by
      rw [div_lt_iff₀ hW] at hj1; linarith
    -- the rankwise bound
    have hmean : ∀ α, IsBulkRank p ϑ α →
        ∫ H, modeObservable p m α H ∂((R (φ j)).model.law : Measure p.SiteMatrix) ≤ ε := by
      intro α hα
      have hm0 : ((m : ZMod p.n)) ≠ 0 := by
        intro h0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
        have hle := Int.le_of_dvd (abs_pos.mpr hm) ((dvd_abs _ _).mpr h0)
        have hpn : (p.n : ℝ) ≤ |(m : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast hle
        have : (0 : ℝ) < |(m : ℝ)| := abs_pos.mpr hmR
        have h' : ((s.n (φ j) : ℕ) : ℝ) ≤ |(m : ℝ)| := hpn
        linarith
      have hγ := (hCm (s.n (φ j)) (s.W (φ j)) (s.n_ge_four (φ j)) (s.W_pos (φ j)) hnW
        (R (φ j)).model α hα (m : ZMod p.n) hm0).1
      have hdsep := modeSeparation_ge p m hj3
      have hscale := mode_scale_le hn hW hmR hdsep
      have hthree := modeRate_le_three (t := (s.n (φ j) : ℝ) / s.W (φ j)) (m := (m : ℝ))
        (div_nonneg hn.le hW.le) hj2.le
      refine (integral_modeObservable_le _ m α).trans ?_
      refine min_le_min le_rfl ?_
      calc _ ≤ Cm * (1 / ((s.W (φ j) : ℝ) * modeSeparation p m) +
            1 / (Real.sqrt (s.n (φ j)) * ((s.W (φ j) : ℝ) * Real.sqrt (s.W (φ j))) *
              modeSeparation p m ^ 2)) := hγ
        _ ≤ Cm * (3 * X) := by
            apply mul_le_mul_of_nonneg_left (hscale.trans hthree) hCm0
        _ = (3 * Cm) * X := by ring
        _ ≤ D * X := mul_le_mul_of_nonneg_right (le_max_left _ _) hX0.le
    have hwin := hWTb (s.n (φ j)) (s.W (φ j)) (s.n_ge_four (φ j)) (s.W_pos (φ j)) hnW
      (R (φ j)).model ε hε0 hε1 (modeObservable p m) (measurable_modeObservable m)
      (modeObservable_mem m) (modeObservable_shift m) hmean
    have hbridge := lintegral_le_windowExpectation (R (φ j)).model E continuous_refWeight
      hasCompactSupport_refWeight refWeight_nonneg (modeMark_nonneg m) (modeObservable p m)
      (measurable_modeObservable m) (modeObservable_mem m) zero_le_one
      (modeMark_le_observable_ae _ m)
    refine hbridge.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [one_mul]
    refine hwin.trans ?_
    rw [hqe]
    have he0 : 0 ≤ ε ^ (1 - η) := Real.rpow_nonneg hε0.le _
    have ha0 : 0 ≤ countScale (s.n (φ j)) (s.W (φ j)) / Real.sqrt (s.n (φ j)) := by
      unfold countScale
      have : 0 ≤ Real.log (2 * (s.W (φ j) : ℝ)) :=
        Real.log_nonneg (by have : (1 : ℝ) ≤ s.W (φ j) := by exact_mod_cast s.W_pos (φ j)
                            linarith)
      positivity
    have hC : C₁ * (countScale (s.n (φ j)) (s.W (φ j)) / Real.sqrt (s.n (φ j))) * ε ^ (1 - η) ≤
        2 * Cp * ε ^ (1 - η) := by
      apply mul_le_mul_of_nonneg_right _ he0
      calc C₁ * _ ≤ Cp * (countScale (s.n (φ j)) (s.W (φ j)) / Real.sqrt (s.n (φ j))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
        _ ≤ Cp * 2 := mul_le_mul_of_nonneg_left hj4 hCp0
        _ = 2 * Cp := by ring
    linarith
  -- Step 2: uniformity in the weight.
  have hstep2 : weightFunctional P (modeMark m) w ≤
      4 * (ENNReal.ofReal refMass * weightFunctional P (modeMark m) refWeight) := by
    have h4 := weightFunctional_le_four P hstat (continuous_modeMark m) (modeMark_nonneg m)
      continuous_refPsi hasCompactSupport_refPsi refPsi_nonneg refPsi_ge_one
      w.toContinuousMap.continuous w.compactSupport w.nonnegative w.integral_eq_one
    have hpsi : weightFunctional P (modeMark m) refPsi =
        ENNReal.ofReal refMass * weightFunctional P (modeMark m) refWeight := by
      rw [← weightFunctional_const_mul P _ _ refMass_pos.le]
      congr 1
      funext u
      exact refPsi_eq u
    rw [hpsi] at h4
    exact h4
  -- Step 3: algebra.
  rw [modeVariance_eq_weightFunctional]
  refine hstep2.trans ?_
  have halg : 4 * (refMass * (2 * Cp * ε ^ (1 - η))) ≤
      8 * refMass * Cp * D * min 1 (X ^ (1 - η)) := by
    have hmr := min_rpow_le hD1 hX0.le hη hη1
    have hm0 : 0 ≤ 8 * refMass * Cp := by have := refMass_pos; positivity
    calc 4 * (refMass * (2 * Cp * ε ^ (1 - η))) = (8 * refMass * Cp) * ε ^ (1 - η) := by ring
      _ ≤ (8 * refMass * Cp) * (D * min 1 (X ^ (1 - η))) :=
          mul_le_mul_of_nonneg_left hmr hm0
      _ = _ := by ring
  calc 4 * (ENNReal.ofReal refMass * weightFunctional P (modeMark m) refWeight) ≤
        4 * (ENNReal.ofReal refMass * ENNReal.ofReal (2 * Cp * ε ^ (1 - η))) := by gcongr
    _ = ENNReal.ofReal (4 * (refMass * (2 * Cp * ε ^ (1 - η)))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_mul refMass_pos.le]
        norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal halg

end BlockBand.Window.SmallCritical
