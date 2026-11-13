module

public import BlockBand.Endpoints.Response.ClockEntranceJensenCovariance
public import BlockBand.Endpoints.Response.ClockEntranceLayerWeight

/-!
# The covariance gap on the retained event `‖L‖ ≤ K₀`

Part of the clock fractional-entrance lemma: the fourth bilinear moment and the fresh operator
moments let us retain `‖LL*‖ ≤ K` with half the lower bound, for a fixed `K`.

* `cej_ofReal_integral_le` — `ofReal (∫ f) ≤ ∫⁻ ofReal f` for `f ≥ 0` (no integrability needed).
* `cej_sq_le_of_gt` — the pointwise AM–GM split on the complement `‖L‖ > K₀`:
  `|x|² ≤ (W/(2K₀²))|x|⁴ + ‖L‖⁴/(2K₀²W)`.
* `cej_event_gap` — from `cej_covariance_gap`,
  `PassiveSourceMixingContract.oneStepFluctuation` at `p = 4` (fourth bilinear moment
  `‖u*U⁰v‖_4 ≤ C/√W`) and `OnePortOperatorMoments` at `r = 2` (`E‖L‖⁴ ≤ C`): there are
  `κ, d, K_min > 0` and `W₀` such that for every `K₀ ≥ K_min`,
  `κ/W ≤ E_ν[1{‖L‖ ≤ K₀} |(V*U⁰V)_ij|²]` for retained `i, j` in any orthonormal basis.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws

variable {W : ℕ}

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for a nonnegative `f` (both sides vanish-compatible: the
Bochner integral of a non-integrable `f` is `0`). -/
theorem cej_ofReal_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have h := enorm_integral_le_lintegral_enorm (μ := μ) f
  rw [Real.enorm_of_nonneg (integral_nonneg hf)] at h
  refine h.trans (le_of_eq (lintegral_congr fun x => ?_))
  rw [Real.enorm_of_nonneg (hf x)]

/-- `‖f‖_4 ≤ B` gives `∫⁻ ‖f‖ₑ⁴ ≤ B⁴`. -/
theorem cej_lintegral_pow_four_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (h : eLpNorm f (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal B) :
    ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂μ ≤ ENNReal.ofReal B ^ (4 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp) hf] at h
  have h4 : (ENNReal.ofReal 4).toReal = ((4 : ℕ) : ℝ) := by norm_num
  rw [h4, one_div, ENNReal.rpow_inv_le_iff (by norm_num)] at h
  simpa only [ENNReal.rpow_natCast] using h

/-- **AM–GM on the complement of the retained event**: for `a, K₀ > 0` (`a = W`) and
`K₀ < ℓ`, `x² ≤ (a/(2K₀²))x⁴ + ℓ⁴/(2K₀²a)`. -/
theorem cej_sq_le_of_gt {x ℓ K₀ a : ℝ} (ha : 0 < a) (hK : 0 < K₀) (hℓ : K₀ < ℓ) :
    x ^ 2 ≤ a / (2 * K₀ ^ 2) * x ^ 4 + ℓ ^ 4 / (2 * K₀ ^ 2 * a) := by
  have hK4 : K₀ ^ 4 ≤ ℓ ^ 4 := pow_le_pow_left₀ hK.le hℓ.le 4
  have h1 : x ^ 2 ≤ a / (2 * K₀ ^ 2) * x ^ 4 + K₀ ^ 4 / (2 * K₀ ^ 2 * a) := by
    have e : a / (2 * K₀ ^ 2) * x ^ 4 + K₀ ^ 4 / (2 * K₀ ^ 2 * a) - x ^ 2 =
        (a * x ^ 2 - K₀ ^ 2) ^ 2 / (2 * K₀ ^ 2 * a) := by
      field_simp; ring
    have : 0 ≤ (a * x ^ 2 - K₀ ^ 2) ^ 2 / (2 * K₀ ^ 2 * a) := by positivity
    linarith
  have h2 : K₀ ^ 4 / (2 * K₀ ^ 2 * a) ≤ ℓ ^ 4 / (2 * K₀ ^ 2 * a) :=
    div_le_div_of_nonneg_right hK4 (by positivity)
  linarith

/-- **The covariance gap on the retained event.** From `PassiveCovarianceContract`,
`TransmissionLawContract.jetGap` and `PassiveSourceMixingContract.oneStepFluctuation` (`p = 4`),
and `OnePortOperatorMoments` (`r = 2`): constants `κ, d, K_min > 0`, `W₀` (depending on `b, E, s`)
such that for `W ≥ W₀`, passive `X` in the jet domain of radius `d`, every `K₀ ≥ K_min`, every
unitary `V` and `(V*TV)_ii, (V*TV)_jj ≤ 1/2`,
`κ/W ≤ ∫⁻_{‖L‖ ≤ K₀} |(V*(LL* - E_νLL*)V)_ij|² dν`. -/
theorem cej_event_gap (hPC : PassiveCovarianceContract) (hTL : TransmissionLawContract)
    (hPSM : PassiveSourceMixingContract) (hOp : OnePortOperatorMoments)
    {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {s : ℂ}
    (hs : IsStationaryJet b E s) :
    ∃ (κ d Kmin : ℝ) (W₀ : ℕ), 0 < κ ∧ 0 < d ∧ 0 < Kmin ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X → ∀ K₀ : ℝ, Kmin ≤ K₀ →
        ∀ V : Matrix (Fin W) (Fin W) ℂ, V ∈ unitaryGroup (Fin W) ℂ → ∀ i j : Fin W,
          ((star V * passiveTransmission b E X * V) i i).re ≤ 1 / 2 →
          ((star V * passiveTransmission b E X * V) j j).re ≤ 1 / 2 →
            ENNReal.ofReal (κ / W) ≤ ∫⁻ ν in {ν | ‖freshL b E X ν‖ ≤ K₀},
              ENNReal.ofReal (‖(star V * (freshU b E X ν -
                matrixExpect (freshLaw W b) (freshU b E X)) * V) i j‖ ^ 2) ∂freshLaw W b := by
  obtain ⟨κ₁, d₁, W₁, hκ₁, hd₁, hgap⟩ := cej_covariance_gap hPC hTL hb0 hb1 hE1 hE2 hs
  obtain ⟨Cf, Wf, hCf⟩ := hPSM.oneStepFluctuation b hb0 hb1 E hE1 hE2 4 (by norm_num)
  obtain ⟨db, hdb, hOpb⟩ := hOp b hb0 hb1 E hE1 hE2 s hs
  obtain ⟨Cb, Wb, hCb⟩ := hOpb 2
  set Cf' := |Cf|
  set Cb' := |Cb|
  refine ⟨κ₁ / 2, min d₁ db, 1 + (Cf' ^ 4 + Cb') / κ₁, max (max W₁ Wf) (max Wb 1),
    by positivity, lt_min hd₁ hdb, by positivity, ?_⟩
  intro W hW X hX K₀ hK₀ V hV i j hi hj
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWf : Wf ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWb : Wb ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWpos : (0 : ℝ) < W := by
    have : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
    exact_mod_cast this
  have hX1 : cel_InJetDomain b E s d₁ X := hX.mono (min_le_left _ _)
  have hXb : cel_InJetDomain b E s db X := hX.mono (min_le_right _ _)
  have hK1 : 1 ≤ K₀ := by
    have : 0 ≤ (Cf' ^ 4 + Cb') / κ₁ := by positivity
    linarith
  have hK0 : 0 < K₀ := by linarith
  have hKsq : (Cf' ^ 4 + Cb') / κ₁ ≤ K₀ ^ 2 := by nlinarith
  set Ubar := matrixExpect (freshLaw W b) (freshU b E X)
  set x : LayerSample W .oneBlockOnePort → ℂ :=
    fun ν => (star V * (freshU b E X ν - Ubar) * V) i j
  set G : Set (LayerSample W .oneBlockOnePort) := {ν | ‖freshL b E X ν‖ ≤ K₀}
  have hLm := cel_measurable_freshL b E X
  have hGm : MeasurableSet G :=
    measurableSet_le (continuous_norm.measurable.comp hLm) measurable_const
  have hxm : Measurable x := by
    have hU : Measurable fun ν => freshU b E X ν := by
      unfold freshU
      exact (Continuous.matrix_mul continuous_fst
        (continuous_snd.matrix_conjTranspose)).measurable.comp (hLm.prodMk hLm)
    have : Measurable fun ν => star V * (freshU b E X ν - Ubar) * V :=
      ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul
        continuous_const).measurable.comp hU
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp this)
  -- the full gap
  have hfull : ENNReal.ofReal (κ₁ / W) ≤ ∫⁻ ν, ENNReal.ofReal (‖x ν‖ ^ 2) ∂freshLaw W b :=
    (ENNReal.ofReal_le_ofReal (hgap W hW1 X hX1 V hV i j hi hj)).trans
      (cej_ofReal_integral_le fun ν => by positivity)
  -- the fourth moment of `x`
  have hx4 : ∫⁻ ν, ‖x ν‖ₑ ^ (4 : ℕ) ∂freshLaw W b ≤ ENNReal.ofReal (Cf' / Real.sqrt W) ^ (4 : ℕ) := by
    have h := (hCf W hWf X hX.1 (fun a => V a i) (fun a => V a j)).1
    rw [cej_vecNorm_col hV, cej_vecNorm_col hV, mul_one, mul_one] at h
    have h' : eLpNorm x (ENNReal.ofReal 4) (freshLaw W b) ≤ ENNReal.ofReal (Cf' / Real.sqrt W) := by
      refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (le_abs_self Cf) (Real.sqrt_nonneg _))))
      congr 1
      funext ν
      simp only [x, Ubar]
      rw [cej_bilinear_col]
    exact cej_lintegral_pow_four_le hxm.aestronglyMeasurable h'
  have hL4 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 4) ∂freshLaw W b ≤ ENNReal.ofReal Cb' := by
    have := hCb W hWb X hXb
    rw [show 2 * 2 = 4 from rfl] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (le_abs_self Cb))
  -- the complement
  have hcomp : ∫⁻ ν in Gᶜ, ENNReal.ofReal (‖x ν‖ ^ 2) ∂freshLaw W b ≤
      ENNReal.ofReal (κ₁ / 2 / W) := by
    have hpt : ∀ ν ∈ Gᶜ, ENNReal.ofReal (‖x ν‖ ^ 2) ≤
        ENNReal.ofReal (W / (2 * K₀ ^ 2)) * ‖x ν‖ₑ ^ (4 : ℕ) +
          ENNReal.ofReal (1 / (2 * K₀ ^ 2 * W)) * ENNReal.ofReal (‖freshL b E X ν‖ ^ 4) := by
      intro ν hν
      have hlt : K₀ < ‖freshL b E X ν‖ := not_le.mp hν
      have h := cej_sq_le_of_gt (x := ‖x ν‖) hWpos hK0 hlt
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
      ring
    have hmeas : Measurable fun ν => ENNReal.ofReal (1 / (2 * K₀ ^ 2 * W)) *
        ENNReal.ofReal (‖freshL b E X ν‖ ^ 4) :=
      (ENNReal.measurable_ofReal.comp
        ((continuous_norm.measurable.comp hLm).pow_const 4)).const_mul _
    calc ∫⁻ ν in Gᶜ, ENNReal.ofReal (‖x ν‖ ^ 2) ∂freshLaw W b
        ≤ ∫⁻ ν in Gᶜ, (ENNReal.ofReal (W / (2 * K₀ ^ 2)) * ‖x ν‖ₑ ^ (4 : ℕ) +
          ENNReal.ofReal (1 / (2 * K₀ ^ 2 * W)) * ENNReal.ofReal (‖freshL b E X ν‖ ^ 4))
            ∂freshLaw W b := setLIntegral_mono' hGm.compl hpt
      _ ≤ ∫⁻ ν, (ENNReal.ofReal (W / (2 * K₀ ^ 2)) * ‖x ν‖ₑ ^ (4 : ℕ) +
          ENNReal.ofReal (1 / (2 * K₀ ^ 2 * W)) * ENNReal.ofReal (‖freshL b E X ν‖ ^ 4))
            ∂freshLaw W b := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (W / (2 * K₀ ^ 2)) * ∫⁻ ν, ‖x ν‖ₑ ^ (4 : ℕ) ∂freshLaw W b +
          ENNReal.ofReal (1 / (2 * K₀ ^ 2 * W)) *
            ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 4) ∂freshLaw W b := by
        rw [lintegral_add_right _ hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (W / (2 * K₀ ^ 2)) * ENNReal.ofReal (Cf' / Real.sqrt W) ^ (4 : ℕ) +
          ENNReal.ofReal (1 / (2 * K₀ ^ 2 * W)) * ENNReal.ofReal Cb' := by gcongr
      _ = ENNReal.ofReal ((Cf' ^ 4 + Cb') / (2 * K₀ ^ 2 * W)) := by
        have hsq : Real.sqrt W ^ 4 = (W : ℝ) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hWpos.le]
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
        congr 1
        rw [div_pow, hsq]
        field_simp
      _ ≤ ENNReal.ofReal (κ₁ / 2 / W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_div_iff₀ (by positivity) hWpos]
        rw [div_le_iff₀ hκ₁] at hKsq
        nlinarith
  -- conclude
  have hsplit := lintegral_add_compl (fun ν => ENNReal.ofReal (‖x ν‖ ^ 2)) (μ := freshLaw W b) hGm
  have e : ENNReal.ofReal (κ₁ / W) = ENNReal.ofReal (κ₁ / 2 / W) + ENNReal.ofReal (κ₁ / 2 / W) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have h3 : ENNReal.ofReal (κ₁ / 2 / W) + ENNReal.ofReal (κ₁ / 2 / W) ≤
      (∫⁻ ν in G, ENNReal.ofReal (‖x ν‖ ^ 2) ∂freshLaw W b) + ENNReal.ofReal (κ₁ / 2 / W) := by
    rw [← e]
    calc ENNReal.ofReal (κ₁ / W) ≤ ∫⁻ ν, ENNReal.ofReal (‖x ν‖ ^ 2) ∂freshLaw W b := hfull
      _ = (∫⁻ ν in G, ENNReal.ofReal (‖x ν‖ ^ 2) ∂freshLaw W b) +
          ∫⁻ ν in Gᶜ, ENNReal.ofReal (‖x ν‖ ^ 2) ∂freshLaw W b := hsplit.symm
      _ ≤ _ := by gcongr
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h3

end BlockBand.Endpoints
