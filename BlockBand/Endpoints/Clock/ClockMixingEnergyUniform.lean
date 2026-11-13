module

public import BlockBand.Endpoints.Clock.ClockMixing
public import BlockBand.Endpoints.Clock.OpenInputsEnergyUniform
public import BlockBand.Internal.Contracts.TransmissionUniform3

/-!
# The clock-mixing lemma, energy-uniform at fixed `b`

`ClockMixingEnergyUniformBound` is `ClockMixingUniformBound` with the energy quantifier
`-2 < E < 2` replaced by `κ > 0` before the constants and `E ∈ bulkInterval κ` after `W ≥ W₀`;
the conclusion is the same.

## Hypotheses (`clockMixingEnergyUniform_of`)
* `TransmissionUniform3.PassiveSourceMixingEnergyUniformContract`: `oneStepMean` and
  `oneStepFluctuation` with `κ` before `C, W₀`.
* `PassiveSourceMixingContract`: only the jet-existence conjunct `∃ s, IsStationaryJet b E s` of
  `oneStepMean`, at each `E` (after `W` is fixed); its constants are not used, and any jet will
  do since the uniform bounds hold for every jet.
* `GaussianAbsorptionContract` at `η₀ = etaLow b κ`, `M = 3`.
* `MovingEnergy.OpenInputsMomentsEnergyUniform`, at moment order `2p`.

## The `E`-uniform constants
After the reduction `κ ↦ min κ 1` (`bulkInterval_mono`):
* `‖θ_*(E, s)‖ ≤ thetaMax b κ = b/(b + g_κ) < 1` for every `E ∈ bulkInterval κ` and every
  stationary jet `s` (`norm_thetaStar_le_thetaMax`, from `|k₋| ≤ r_κ` and `|s| ≤ d_*`);
* `(Im z)⁻¹ + |c₀| ≤ 2/η_κ` (`fBound_le`, from `η_κ ≤ Im z` and `|c₀| = (2 Im z)⁻¹`).

The rest of the proof of `clockMixingUniform_of` is unchanged, with `E` introduced after the
constants.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

namespace MovingEnergy

variable {b κ E : ℝ}

/-- `θ_max = b/(b + g_κ)`, the uniform bound of `|θ_*|` on `bulkInterval κ`. -/
def thetaMax (b κ : ℝ) : ℝ := b / (b + gapLow b κ)

/-- `0 ≤ θ_max`. -/
theorem thetaMax_nonneg (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) : 0 ≤ thetaMax b κ := by
  have := gapLow_pos hb0 hb1 hκ
  unfold thetaMax; positivity

/-- `θ_max < 1`, since `g_κ > 0`. -/
theorem thetaMax_lt_one (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) : thetaMax b κ < 1 := by
  have := gapLow_pos hb0 hb1 hκ
  unfold thetaMax
  rw [div_lt_one (by positivity)]
  linarith

/-- **`|θ_*| ≤ θ_max`, uniformly** in `E ∈ bulkInterval κ` and in the stationary jet `s`: `|1 + k₋s| ≥ 1 - r_κ d_* = b + g_κ`. -/
theorem norm_thetaStar_le_thetaMax (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) :
    ‖thetaStar b E s‖ ≤ thetaMax b κ := by
  obtain ⟨hE1, hE2⟩ := mem_bulk_lt hκ hE
  have hEa : |E| ≤ 2 := abs_le.mpr ⟨hE1.le, hE2.le⟩
  have hk := norm_kMinus_le_kHigh hb1 hκ hE
  have hg := gapLow_pos hb0 hb1 hκ
  have hks : ‖kMinus b E * s‖ ≤ kHigh b κ * dStar b := by
    rw [norm_mul]
    exact mul_le_mul hk hs.2 (norm_nonneg _) (Real.sqrt_nonneg _)
  have hden : b + gapLow b κ ≤ ‖1 + kMinus b E * s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(kMinus b E * s))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this
    unfold gapLow
    linarith
  unfold thetaStar thetaMax
  rw [norm_div, norm_mul, norm_pow, BlockBand.Layers.norm_matchedA hEa, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hb0, one_pow, mul_one]
  exact div_le_div_of_nonneg_left hb0.le (by positivity) hden

/-- `|c₀| = (2 Im z)⁻¹`. -/
theorem norm_cZero_eq (hz : 0 < (boundaryZ b E).im) :
    ‖cZero b E‖ = (2 * (boundaryZ b E).im)⁻¹ := by
  unfold cZero etaZ
  rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hz]
  norm_num

/-- The deterministic bound of `f`, uniformly: `(Im z)⁻¹ + |c₀| ≤ 2/η_κ`. -/
theorem fBound_le (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) (hE : E ∈ bulkInterval κ) :
    (boundaryZ b E).im⁻¹ + ‖cZero b E‖ ≤ 2 / etaLow b κ := by
  have hη := etaLow_pos hb1 hκ hκ4
  have hle := etaLow_le_im hb1 hκ hE
  have hz : 0 < (boundaryZ b E).im := hη.trans_le hle
  rw [norm_cZero_eq hz]
  have h1 : (boundaryZ b E).im⁻¹ ≤ (etaLow b κ)⁻¹ := inv_anti₀ hη hle
  have h2 : (2 * (boundaryZ b E).im)⁻¹ ≤ (boundaryZ b E).im⁻¹ :=
    inv_anti₀ hz (by linarith)
  rw [div_eq_mul_inv]
  linarith

open BlockBand.Internal.Contracts.TransmissionUniform3

/-- **The clock-mixing lemma, uniformly in the
energy** `E ∈ bulkInterval κ` (`b` fixed) and in a small deterministic
Hermitian initial matrix `X_0 = D` (`‖D‖ ≤ ε`, operator norm). `b, κ, T, q, p` first; then
`ε > 0`, `C`, `W₀`; for `W ≥ W₀`, every `E ∈ bulkInterval κ`, every such `D` and
`j₀ = ⌈(log W)²⌉ ≤ j ≤ TW`: `‖Z_j‖_p + ‖√S_j‖_p ≤ C W^{-1/2}`. -/
def ClockMixingEnergyUniformBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (T : ℝ) (q : ℝ → ℝ), IsClockWeight q →
    ∀ p : ℝ, 1 ≤ p → ∃ (ε C : ℝ) (W₀ : ℕ), 0 < ε ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
        ∀ j : ℕ, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W →
          eLpNorm (openClockZ b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) +
              eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
            ENNReal.ofReal (C / Real.sqrt W)

open ClockMixingAlg ClockMixingProb in

/-- **The clock-mixing bound, uniformly in `E ∈ bulkInterval κ` and in the initial matrix**
(`ClockMixingEnergyUniformBound`), from `PassiveSourceMixingEnergyUniformContract` (`oneStepMean`,
`oneStepFluctuation`), `PassiveSourceMixingContract` (jet existence only),
`GaussianAbsorptionContract` and `OpenInputsMomentsEnergyUniform`.
-/
theorem clockMixingEnergyUniform_of (hPSMU : PassiveSourceMixingEnergyUniformContract)
    (hPSM : PassiveSourceMixingContract) (hGA : GaussianAbsorptionContract)
    (hOIU : OpenInputsMomentsEnergyUniform) : ClockMixingEnergyUniformBound := by
  intro b hb0 hb1 κ₀ hκ₀ T q hq p hp
  set κ := min κ₀ 1 with hκdef
  have hκ : 0 < κ := lt_min hκ₀ one_pos
  have hκ4 : κ < 4 := by have := min_le_right κ₀ 1; linarith
  have hη := etaLow_pos hb1 hκ hκ4
  set Kf := 2 / etaLow b κ with hKfdef
  have hKf : 0 ≤ Kf := by positivity
  set θm := thetaMax b κ with hθmdef
  have hθm0 : 0 ≤ θm := thetaMax_nonneg hb0 hb1 hκ
  have hθm1 : θm < 1 := thetaMax_lt_one hb0 hb1 hκ
  obtain ⟨hqc, hq0, Kq, hqK⟩ := hq
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  obtain ⟨Cm, Wm, hm⟩ := hPSMU.oneStepMean b hb0 hb1 κ hκ
  obtain ⟨Cf, Wf, hf⟩ := hPSMU.oneStepFluctuation b hb0 hb1 κ hκ (max p 2)
    (le_trans hp (le_max_left _ _))
  obtain ⟨ε₁, Cg, hε₁, hCg, hga⟩ := hGA b hb0 hb1 (etaLow b κ) 3 hη
  obtain ⟨ε, Co, Wo, hε, hoi⟩ := hOIU b hb0 hb1 κ hκ T q ⟨hqc, hq0, Kq, hqK⟩ (2 * p)
    (by linarith)
  set Cm' := max Cm 0
  set Cf' := max Cf 0
  set Co' := max Co 0
  have hCm' : 0 ≤ Cm' := le_max_right _ _
  have hCf' : 0 ≤ Cf' := le_max_right _ _
  have hCo' : 0 ≤ Co' := le_max_right _ _
  set Tb := |T| + 1
  have hTb : 0 ≤ Tb := by positivity
  set H0 := Cm' * (Co' * (Co' * Tb)) + Cm' * (Co' * (Co' * Tb)) + (Cm' + Cf') * (Co' * Tb)
  set FZ := H0 + Kf * Kq * Cg ^ 2
  set FS := H0 + Kf * Kq * Cg ^ 2 + Kf * (Co' * Tb)
  set A0 := Kf * (Co' * 18)
  have hH0 : 0 ≤ H0 := by positivity
  have hFZ : 0 ≤ FZ := by positivity
  have hFS : 0 ≤ FS := by positivity
  have hA0 : 0 ≤ A0 := by positivity
  have h1θ : 0 < 1 - θm := by linarith
  refine ⟨ε, (A0 + FZ / (1 - θm)) + (A0 + FS / (1 - θm)),
    max (max (max Wm Wf) Wo) (max 1 ⌈2 * p / ε₁⌉₊), hε, ?_⟩
  intro W hW E hE₀ D hD hDε j hj0 hjT
  have hE : E ∈ bulkInterval κ := bulkInterval_mono (min_le_left κ₀ 1) hE₀
  obtain ⟨hE1, hE2⟩ := mem_bulk_lt hκ hE
  have hz : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hE
  have hKfE : (boundaryZ b E).im⁻¹ + ‖cZero b E‖ ≤ Kf := fBound_le hb1 hκ hκ4 hE
  have hKfE0 : 0 ≤ (boundaryZ b E).im⁻¹ + ‖cZero b E‖ := by positivity
  obtain ⟨⟨s, hs⟩, -⟩ := hPSM.oneStepMean b hb0 hb1 E hE1 hE2
  set θ := thetaStar b E s with hθdef
  have hθ : ‖θ‖ ≤ θm := norm_thetaStar_le_thetaMax hb0 hb1 hκ hE hs
  have hWm : Wm ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hW)
  have hWf : Wf ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hW)
  have hWo : Wo ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)
  have hW1n : 1 ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hWc : ⌈2 * p / ε₁⌉₊ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  have hs1 : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW1
  have hinvW : (W : ℝ)⁻¹ ≤ (Real.sqrt W)⁻¹ := by
    rw [inv_le_inv₀ hW0 hsW]
    calc Real.sqrt W ≤ Real.sqrt W * Real.sqrt W := le_mul_of_one_le_right hsW.le hs1
      _ = W := Real.mul_self_sqrt hW0.le
  have hinvW2 : (W : ℝ)⁻¹ ^ 2 ≤ (Real.sqrt W)⁻¹ := by
    have : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ := by
      rw [sq]; exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hW1)
    exact this.trans hinvW
  have h2p : 2 * p ≤ ε₁ * W := by
    have h1 : 2 * p / ε₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWc)
    rw [div_le_iff₀ hε₁] at h1
    linarith
  -- the one-layer hypotheses at this width and energy
  have H : StepHyp W b E θ s Cm' Cf' Cg p := by
    refine ⟨fun X hX => ?_, fun X hX u v => ?_, fun X hX => ?_⟩
    · have h := hm W hWm E hE s hs X (passiveY_posSemidef hX)
      rw [passiveMass_eq_zero b E hX] at h
      simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero, div_one] at h
      refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      unfold jetDistance0 jetDistance1
      positivity
    · refine (hf W hWf E hE X (passiveY_posSemidef hX) u v).2.trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hu : 0 ≤ vecNorm u := Real.sqrt_nonneg _
      have hv : 0 ≤ vecNorm v := Real.sqrt_nonneg _
      gcongr
      exact le_max_left _ _
    · exact (hga W (by exact_mod_cast hW1n) .oneBlockOnePort (physEmbed X)
        (physEmbed_isHermitian hX) E (boundaryZ b E) (etaLow_le_im hb1 hκ hE)
        (norm_boundaryZ_le3 hb0 hb1 hκ hE)).2 (2 * p) (by linarith) h2p
  obtain ⟨hδ, hγ⟩ := hoi W hWo E hE D hD hDε
  -- ranges
  set N := ⌊T * W⌋₊
  have hTW0 : 0 ≤ T * W := le_trans (Nat.cast_nonneg j) hjT
  have hjN : j ≤ N := Nat.le_floor hjT
  have hiT : ∀ i, i ≤ N → (i : ℝ) ≤ T * W := fun i hi =>
    le_trans (by exact_mod_cast hi) (Nat.floor_le hTW0)
  have hγ2 : ∀ i, i ≤ N →
      eLpNorm (oneEndedGamma b E q D i) (ENNReal.ofReal (2 * p)) (oneEndedLaw W b i) ≤
        ENNReal.ofReal (Co' * Tb) := by
    intro i hi
    refine (hγ i (hiT i hi)).trans (ENNReal.ofReal_le_ofReal ?_)
    have ht := time_le hW1 (hiT i hi)
    calc Co * ((i : ℝ) + 1) / W ≤ Co' * (((i : ℝ) + 1) / W) := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ Co' * Tb := mul_le_mul_of_nonneg_left ht hCo'
  have hγp : ∀ i, i ≤ N →
      eLpNorm (oneEndedGamma b E q D i) (ENNReal.ofReal p) (oneEndedLaw W b i) ≤
        ENNReal.ofReal (Co' * Tb) := fun i hi =>
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans
      (hγ2 i hi)
  have hEW : ∀ i, openEntranceTime W ≤ i → i ≤ N →
      eLpNorm (errWeight b E q D s Cm' (Cf' / Real.sqrt W) i) (ENNReal.ofReal p)
        (oneEndedLaw W b i) ≤ ENNReal.ofReal (H0 / Real.sqrt W) := by
    intro i hi0 hiN
    have hδi : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D i ω))
          (ENNReal.ofReal (2 * p)) (oneEndedLaw W b i) +
        eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D i ω)) (ENNReal.ofReal (2 * p))
          (oneEndedLaw W b i) ≤ ENNReal.ofReal (Co' / W) :=
      (hδ s hs i hi0 (hiT i hiN)).trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
    refine (errWeight_le hCm' (by positivity) (by positivity) (by positivity) hp i hδi
      (hγ2 i hiN)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc1 : Co' / W ≤ Co' / Real.sqrt W := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinvW hCo'
    have e1 : Cm' * (Co' / W * (Co' * Tb)) ≤ Cm' * (Co' * (Co' * Tb)) / Real.sqrt W := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hCm'
      calc Co' / W * (Co' * Tb) ≤ Co' / Real.sqrt W * (Co' * Tb) :=
            mul_le_mul_of_nonneg_right hc1 (by positivity)
        _ = Co' * (Co' * Tb) / Real.sqrt W := by ring
    have e3 : (Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W) * (Co' * Tb) ≤
        (Cm' + Cf') * (Co' * Tb) / Real.sqrt W := by
      have : Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W ≤ (Cm' + Cf') / Real.sqrt W := by
        rw [add_div, div_eq_mul_inv Cm']
        exact add_le_add (mul_le_mul_of_nonneg_left hinvW2 hCm') le_rfl
      calc (Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W) * (Co' * Tb)
          ≤ (Cm' + Cf') / Real.sqrt W * (Co' * Tb) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring
    calc Cm' * (Co' / W * (Co' * Tb)) + Cm' * (Co' / W * (Co' * Tb)) +
          (Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W) * (Co' * Tb)
        ≤ Cm' * (Co' * (Co' * Tb)) / Real.sqrt W + Cm' * (Co' * (Co' * Tb)) / Real.sqrt W +
            (Cm' + Cf') * (Co' * Tb) / Real.sqrt W := add_le_add (add_le_add e1 e1) e3
      _ = H0 / Real.sqrt W := by simp only [H0]; ring
  have hinj : ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / W * Cg ^ 2 ≤
      Kf * Kq * Cg ^ 2 / Real.sqrt W := by
    have h1 : ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / W * Cg ^ 2 ≤ Kf * Kq / W * Cg ^ 2 := by
      gcongr
    refine h1.trans ?_
    rw [div_eq_mul_inv (Kf * Kq), div_eq_mul_inv (Kf * Kq * Cg ^ 2)]
    have := mul_le_mul_of_nonneg_left hinvW (by positivity : 0 ≤ Kf * Kq * Cg ^ 2)
    linarith [this, show Kf * Kq * (W : ℝ)⁻¹ * Cg ^ 2 = Kf * Kq * Cg ^ 2 * (W : ℝ)⁻¹ by ring]
  have hθle : ∀ a : ℝ≥0∞, ENNReal.ofReal ‖θ‖ * a ≤ ENNReal.ofReal θm * a := fun a =>
    mul_le_mul_left (ENNReal.ofReal_le_ofReal hθ) a
  -- the two recursions
  set aZ : ℕ → ℝ≥0∞ := fun i =>
    eLpNorm (openClockZ b E q D i) (ENNReal.ofReal p) (oneEndedLaw W b i)
  set aS : ℕ → ℝ≥0∞ := fun i =>
    eLpNorm (openClockSqrtS b E q D i) (ENNReal.ofReal p) (oneEndedLaw W b i)
  have hstepZ : ∀ i, openEntranceTime W ≤ i → i < N →
      aZ (i + 1) ≤ ENNReal.ofReal θm * aZ i + ENNReal.ofReal (FZ / Real.sqrt W) := by
    intro i hi0 hiN
    refine (stepZ hD hq0 hqK hW1 hz θ hCf' hCg.le hp H i).trans ?_
    rw [add_assoc]
    refine add_le_add (hθle _) ?_
    calc eLpNorm (errWeight b E q D s Cm' (Cf' / Real.sqrt W) i) (ENNReal.ofReal p)
          (oneEndedLaw W b i) +
          ENNReal.ofReal (((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / W * Cg ^ 2)
        ≤ ENNReal.ofReal (H0 / Real.sqrt W) + ENNReal.ofReal (Kf * Kq * Cg ^ 2 / Real.sqrt W) :=
          add_le_add (hEW i hi0 hiN.le) (ENNReal.ofReal_le_ofReal hinj)
      _ = ENNReal.ofReal (FZ / Real.sqrt W) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; simp only [FZ]; ring
  have hstepS : ∀ i, openEntranceTime W ≤ i → i < N →
      aS (i + 1) ≤ ENNReal.ofReal θm * aS i + ENNReal.ofReal (FS / Real.sqrt W) := by
    intro i hi0 hiN
    refine (stepS hD hq0 hqK hW1 hz θ hCf' hCg.le hp H i).trans ?_
    rw [add_assoc, add_assoc]
    refine add_le_add (hθle _) ?_
    have hg : ENNReal.ofReal (((boundaryZ b E).im⁻¹ + ‖cZero b E‖) / Real.sqrt W) *
        eLpNorm (oneEndedGamma b E q D (i + 1)) (ENNReal.ofReal p) (oneEndedLaw W b (i + 1)) ≤
        ENNReal.ofReal (Kf * (Co' * Tb) / Real.sqrt W) := by
      rw [show Kf * (Co' * Tb) / Real.sqrt W = Kf / Real.sqrt W * (Co' * Tb) by ring,
        ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact hγp (i + 1) hiN
    have hk : ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / Real.sqrt W * Cg ^ 2 ≤
        Kf * Kq * Cg ^ 2 / Real.sqrt W := by
      rw [show Kf * Kq * Cg ^ 2 / Real.sqrt W = Kf * Kq / Real.sqrt W * Cg ^ 2 by ring]
      gcongr
    calc eLpNorm (errWeight b E q D s Cm' (Cf' / Real.sqrt W) i) (ENNReal.ofReal p)
          (oneEndedLaw W b i) +
          (ENNReal.ofReal (((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / Real.sqrt W * Cg ^ 2) +
          ENNReal.ofReal (((boundaryZ b E).im⁻¹ + ‖cZero b E‖) / Real.sqrt W) *
            eLpNorm (oneEndedGamma b E q D (i + 1)) (ENNReal.ofReal p)
              (oneEndedLaw W b (i + 1)))
        ≤ ENNReal.ofReal (H0 / Real.sqrt W) +
            (ENNReal.ofReal (Kf * Kq * Cg ^ 2 / Real.sqrt W) +
            ENNReal.ofReal (Kf * (Co' * Tb) / Real.sqrt W)) :=
          add_le_add (hEW i hi0 hiN.le) (add_le_add (ENNReal.ofReal_le_ofReal hk) hg)
      _ = ENNReal.ofReal (FS / Real.sqrt W) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; simp only [FS]; ring
  -- the initial bound at `j₀`
  set j₀ := openEntranceTime W
  have hj0N : j₀ ≤ N := le_trans hj0 hjN
  have hinit : ∀ a : ℕ → ℝ≥0∞, (a = aZ ∨ a = aS) →
      a j₀ ≤ ENNReal.ofReal (A0 / Real.sqrt W) := by
    intro a ha
    have hib := init_bound (W := W) (b := b) (E := E) (q := q) hD hq0 hz j₀ (ENNReal.ofReal p)
    have hg0 : eLpNorm (oneEndedGamma b E q D j₀) (ENNReal.ofReal p) (oneEndedLaw W b j₀) ≤
        ENNReal.ofReal (Co' * (((j₀ : ℝ) + 1) / W)) := by
      refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans
        ((hγ j₀ (hiT j₀ hj0N)).trans (ENNReal.ofReal_le_ofReal ?_))
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hfin : ENNReal.ofReal ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) *
        ENNReal.ofReal (Co' * (((j₀ : ℝ) + 1) / W)) ≤ ENNReal.ofReal (A0 / Real.sqrt W) := by
      rw [← ENNReal.ofReal_mul hKfE0]
      refine ENNReal.ofReal_le_ofReal ?_
      have he := entrance_le hW1
      calc ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * (Co' * (((j₀ : ℝ) + 1) / W))
          ≤ Kf * (Co' * (18 / Real.sqrt W)) := by gcongr
        _ = A0 / Real.sqrt W := by simp only [A0]; ring
    rcases ha with rfl | rfl
    · exact hib.1.trans ((mul_le_mul_of_nonneg_left hg0 zero_le).trans hfin)
    · exact hib.2.trans ((mul_le_mul_of_nonneg_left hg0 zero_le).trans hfin)
  have hZ := geom_bound hθm0 hθm1 (by positivity) (by positivity) (hinit aZ (Or.inl rfl)) hstepZ
    j hj0 hjN
  have hS := geom_bound hθm0 hθm1 (by positivity) (by positivity) (hinit aS (Or.inr rfl)) hstepS
    j hj0 hjN
  calc aZ j + aS j
      ≤ ENNReal.ofReal (A0 / Real.sqrt W + FZ / Real.sqrt W / (1 - θm)) +
          ENNReal.ofReal (A0 / Real.sqrt W + FS / Real.sqrt W / (1 - θm)) := add_le_add hZ hS
    _ = ENNReal.ofReal (((A0 + FZ / (1 - θm)) + (A0 + FS / (1 - θm))) / Real.sqrt W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- `ClockMixingEnergyUniformBound` implies the fixed-energy
`ClockMixingUniformBound` (with `κ` from `MovingEnergy.exists_kappa`). -/
theorem clockMixingUniform_of_energyUniform (h : ClockMixingEnergyUniformBound) :
    ClockMixingUniformBound := by
  intro b hb0 hb1 E hE0 hE1 T q hq p hp
  obtain ⟨κ, hκ, hE⟩ := exists_kappa hE0 hE1
  obtain ⟨ε, C, W₀, hε, hC⟩ := h b hb0 hb1 κ hκ T q hq p hp
  exact ⟨ε, C, W₀, hε, fun W hW D hD hDε j hj0 hjT => hC W hW E hE D hD hDε j hj0 hjT⟩

/-- **The clock-mixing bound, energy-uniform at fixed `b`**, from
`PassiveSourceMixingEnergyUniformContract` and `PassiveSourceMixingContract` (jet existence),
`GaussianAbsorptionContract`, `TraceMatrixContract` and `WeightedLayerContract` (the last
three through `openInputsMomentsEnergyUniform_of`).
-/
theorem clockMixingEnergyUniform_of_contracts
    (hPSMU : PassiveSourceMixingEnergyUniformContract) (hPSM : PassiveSourceMixingContract)
    (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract)
    (hWL : WeightedLayerContract) : ClockMixingEnergyUniformBound :=
  clockMixingEnergyUniform_of hPSMU hPSM hGA (openInputsMomentsEnergyUniform_of hGA hTM hWL)

end MovingEnergy

end BlockBand.Endpoints.Clock
