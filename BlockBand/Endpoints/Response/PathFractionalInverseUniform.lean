module

public import BlockBand.Endpoints.Response.PathFractionalInverse
public import BlockBand.Endpoints.Response.PassDerivativeLimitPass
public import BlockBand.Endpoints.Sine.GUELawBridge

/-!
# The path fractional inverse moment uniformly in the microscopic energy window

`pathFractionalInverseEnergyUniform_of_contracts` proves `PathFractionalInverseEnergyUniform`: for
`0 < b < 1/2`, `-2 < E < 2`, `τ > 0`, `j W / W → τ`, `0 < s < 1` and every window constant
`C_e`, there are `C, W₀` such that for `W ≥ W₀` and every `E'` with `|E' - E| ≤ C_e W⁻²`, under
`growthPathLaw W b`: (a) `fullPathMatrix b E' W (j W)` is a.s. invertible; (b)
`E (‖G₀(E')‖/W²)^s ≤ C` (Euclidean operator norm). The only hypothesis is
`Inputs.ConditionalBlockGUECount`; the GUE law bridge is `guelawBridge_holds`.

Proof. `pfiu_bound_at` is the proof of `pathFractionalInverse_holds` at one energy with the
explicit constant `(C'(τ+1))^s/(1-s) + (2|z|⁻¹)^s β^{-s/2}(C'(τ+1))^{s/2}/(1-s/2) +
(|z|⁻¹ + |z|⁻²/β)^s`, `C'` the constant of `lintegral_schur_inv_rpow_le`
(`2 C_count / √(1-2b)`), valid for every `W ≥ 1` and `n ≤ (τ+1)W`. The energy enters only
through `z = z_∂(E')` and `β = Im z/|z|²`; on the compact bulk neighbourhood
`|E' - E| ≤ δ₀ = (2-|E|)/2` one has `|z| ≥ 1 - b ≥ 1/2`, `|z| ≤ 2`, and
`β ≥ (1-b)√(4-m²)/8 ≥ √(4-m²)/16`, `m = (2+|E|)/2` (`pfiu_norm_boundaryZ_ge`,
`pfiu_pfiBeta_ge`). For `W` large the window `C_e W⁻²` lies inside `δ₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory ProbabilityTheory Complex Set Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-- The bound of `pathFractionalInverse_holds` at one energy, with its explicit constant. -/
theorem pfiu_bound_at {C : ℝ} (hC : 0 < C)
    (hmom : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ (W n : ℕ), 0 < W → ∀ s : ℝ, 0 < s → s < 1 →
        ∫⁻ ω, ENNReal.ofReal (‖(pfiSchur b E W n ω)⁻¹‖ ^ s) ∂growthPathLaw W b ≤
          ENNReal.ofReal ((C / Real.sqrt (1 - 2 * b) * ((n * W : ℕ) : ℝ)) ^ s / (1 - s)))
    (hCount : ConditionalBlockGUECount) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {τ s : ℝ} (hτ : 0 < τ) (hs0 : 0 < s) (hs1 : s < 1) {W m : ℕ}
    (hW1 : 1 ≤ W) (hn : ((m : ℕ) : ℝ) ≤ (τ + 1) * W) :
    (∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b E W m ω).det) ∧
      ∫⁻ ω, ENNReal.ofReal ((‖fullInverse b E W m ω‖ / (W : ℝ) ^ 2) ^ s) ∂growthPathLaw W b ≤
        ENNReal.ofReal ((C / Real.sqrt (1 - 2 * b) * (τ + 1)) ^ s / (1 - s) +
          (2 * ‖boundaryZ b E‖⁻¹) ^ s * (pfiBeta b E ^ (s / 2))⁻¹ *
            ((C / Real.sqrt (1 - 2 * b) * (τ + 1)) ^ (s / 2) / (1 - s / 2)) +
          (‖boundaryZ b E‖⁻¹ + ‖boundaryZ b E‖⁻¹ ^ 2 / pfiBeta b E) ^ s) := by
  have hGUE := guelawBridge_holds
  have hb : b < 1 := by linarith
  set z := boundaryZ b E with hz
  set β := pfiBeta b E with hβdef
  have hβ : 0 < β := pfiBeta_pos hb hE1 hE2
  have hz0 : z ≠ 0 := boundaryZ_ne_zero hb hE1 hE2
  have hzim : 0 < z.im := pfi_boundaryZ_im_pos hb hE1 hE2
  set C' := C / Real.sqrt (1 - 2 * b) with hC'def
  have hC' : 0 ≤ C' := div_nonneg hC.le (Real.sqrt_nonneg _)
  set K1 := 2 * ‖z‖⁻¹ with hK1
  set K2 := ‖z‖⁻¹ + ‖z‖⁻¹ ^ 2 / β with hK2
  have hK1n : 0 ≤ K1 := by positivity
  have hK2n : 0 ≤ K2 := by positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWpos : 0 < W := hW1
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hSinv := ae_isUnit_schur hCount hGUE hb1 hE1 hE2 hWpos m
  refine ⟨?_, ?_⟩
  · -- part (a)
    filter_upwards [hSinv] with ω hω
    rw [fullPathMatrix_eq]
    exact isUnit_det_fromBlocks_of_schur hz0 hω
  · -- part (b)
    set X : GrowthPath W → ℝ := fun ω => ‖(pfiSchur b E W m ω)⁻¹‖ with hXdef
    set Y : GrowthPath W → ℝ := fun ω => X ω / (W : ℝ) ^ 2 with hYdef
    have hX0 : ∀ ω, 0 ≤ X ω := fun ω => norm_nonneg _
    have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => div_nonneg (hX0 ω) (by positivity)
    have hXm : Measurable X :=
      continuous_norm.measurable.comp (pfi_measurable_inv.comp (measurable_pfiSchur b E W m))
    have hYm : Measurable Y := hXm.div_const _
    -- pointwise bound
    have hpt : ∀ᵐ ω ∂growthPathLaw W b,
        (‖fullInverse b E W m ω‖ / (W : ℝ) ^ 2) ^ s ≤
          Y ω ^ s + K1 ^ s * (β ^ (s / 2))⁻¹ * Y ω ^ (s / 2) + K2 ^ s := by
      filter_upwards [hSinv, ae_growthPath_isHermitian W b] with ω hω hH
      have hG := norm_fromBlocks_inv_le (pfiInt_isHermitian E W m hH) (pfiCoup W m ω.2)
        hzim hω
      rw [← fullPathMatrix_eq] at hG
      change ‖fullInverse b E W m ω‖ ≤ X ω + 2 * ‖z‖⁻¹ * Real.sqrt (X ω / β) +
        ‖z‖⁻¹ + ‖z‖⁻¹ ^ 2 / β at hG
      have hXY : X ω = Y ω * (W : ℝ) ^ 2 := by
        rw [hYdef]; field_simp
      have hsq : Real.sqrt (X ω / β) = W * Real.sqrt (Y ω / β) := by
        rw [hXY, mul_comm, mul_div_assoc, Real.sqrt_mul (by positivity),
          Real.sqrt_sq hW0.le]
      have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW1)
      have hbound : ‖fullInverse b E W m ω‖ / (W : ℝ) ^ 2 ≤
          Y ω + K1 * Real.sqrt (Y ω / β) + K2 := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : K1 * Real.sqrt (X ω / β) ≤ K1 * Real.sqrt (Y ω / β) * (W : ℝ) ^ 2 := by
          rw [hsq]
          have : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
          have h0 : 0 ≤ K1 * Real.sqrt (Y ω / β) := by positivity
          nlinarith
        have h2 : K2 ≤ K2 * (W : ℝ) ^ 2 := le_mul_of_one_le_right hK2n hW2
        calc ‖fullInverse b E W m ω‖ ≤ X ω + K1 * Real.sqrt (X ω / β) + K2 := by
              rw [hK1, hK2]; linarith
          _ ≤ Y ω * (W : ℝ) ^ 2 + K1 * Real.sqrt (Y ω / β) * (W : ℝ) ^ 2 +
              K2 * (W : ℝ) ^ 2 := by rw [← hXY]; linarith
          _ = (Y ω + K1 * Real.sqrt (Y ω / β) + K2) * (W : ℝ) ^ 2 := by ring
      refine (Real.rpow_le_rpow (by positivity) hbound hs0.le).trans ?_
      refine (rpow_add_add_le (hY0 ω) (by positivity) hK2n hs0.le hs1.le).trans ?_
      have hmid : (K1 * Real.sqrt (Y ω / β)) ^ s = K1 ^ s * (β ^ (s / 2))⁻¹ * Y ω ^ (s / 2) := by
        rw [Real.mul_rpow hK1n (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul
          (div_nonneg (hY0 ω) hβ.le), Real.div_rpow (hY0 ω) hβ.le]
        rw [show 1 / 2 * s = s / 2 by ring]
        ring
      rw [hmid]
    -- integrate
    have hm1 : Measurable (fun ω => ENNReal.ofReal (Y ω ^ s)) :=
      (hYm.pow_const s).ennreal_ofReal
    have hm2 : Measurable (fun ω => ENNReal.ofReal (K1 ^ s * (β ^ (s / 2))⁻¹ * Y ω ^ (s / 2))) :=
      (measurable_const.mul (hYm.pow_const _)).ennreal_ofReal
    have hI1 := lintegral_div_sq_rpow_le hC' hW1 hn hs0 hs1
      (hmom b hb0 hb1 E hE1 hE2 W m hWpos s hs0 hs1) hX0
    have hI2 := lintegral_div_sq_rpow_le hC' hW1 hn (by linarith : 0 < s / 2)
      (by linarith : s / 2 < 1) (hmom b hb0 hb1 E hE1 hE2 W m hWpos (s / 2) (by linarith)
        (by linarith)) hX0
    have hc2 : 0 ≤ K1 ^ s * (β ^ (s / 2))⁻¹ := by positivity
    calc ∫⁻ ω, ENNReal.ofReal ((‖fullInverse b E W m ω‖ / (W : ℝ) ^ 2) ^ s)
          ∂growthPathLaw W b
        ≤ ∫⁻ ω, (ENNReal.ofReal (Y ω ^ s) +
            ENNReal.ofReal (K1 ^ s * (β ^ (s / 2))⁻¹ * Y ω ^ (s / 2)) +
            ENNReal.ofReal (K2 ^ s)) ∂growthPathLaw W b := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with ω hω
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal hω
      _ = ∫⁻ ω, ENNReal.ofReal (Y ω ^ s) ∂growthPathLaw W b +
            ENNReal.ofReal (K1 ^ s * (β ^ (s / 2))⁻¹) *
              ∫⁻ ω, ENNReal.ofReal (Y ω ^ (s / 2)) ∂growthPathLaw W b +
            ENNReal.ofReal (K2 ^ s) := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left hm1, lintegral_const,
            measure_univ, mul_one, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 3
          funext ω
          rw [← ENNReal.ofReal_mul hc2]
      _ ≤ ENNReal.ofReal ((C' * (τ + 1)) ^ s / (1 - s)) +
            ENNReal.ofReal (K1 ^ s * (β ^ (s / 2))⁻¹) *
              ENNReal.ofReal ((C' * (τ + 1)) ^ (s / 2) / (1 - s / 2)) +
            ENNReal.ofReal (K2 ^ s) := by
          gcongr
      _ = _ := by
          have t1 : 0 ≤ (C' * (τ + 1)) ^ s / (1 - s) :=
            div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
          have t2 : 0 ≤ K1 ^ s * (β ^ (s / 2))⁻¹ * ((C' * (τ + 1)) ^ (s / 2) / (1 - s / 2)) :=
            mul_nonneg hc2 (div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith))
          have t3 : 0 ≤ K2 ^ s := Real.rpow_nonneg hK2n _
          rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add t1 t2,
            ← ENNReal.ofReal_add (add_nonneg t1 t2) t3]

/-!
### Uniform control of `z` and `β`
-/

theorem pfiu_boundaryZ_im_eq (b : ℝ) {E : ℝ} (he : E ^ 2 ≤ 4) :
    (boundaryZ b E).im = (1 - b) * Real.sqrt (4 - E ^ 2) / 2 := by
  rw [boundaryZ, Complex.add_im, Complex.inv_im, pfi_matchedA_normSq he, Complex.mul_im]
  simp [matchedA]
  ring

theorem pfiu_norm_matchedA {E : ℝ} (he : E ^ 2 ≤ 4) : ‖matchedA E‖ = 1 := by
  have h := pfi_matchedA_normSq he
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (matchedA E)]

theorem pfiu_norm_boundaryZ_ge {b E : ℝ} (hb0 : 0 ≤ b) (he : E ^ 2 ≤ 4) :
    1 - b ≤ ‖boundaryZ b E‖ := by
  have h1 := pfiu_norm_matchedA he
  have h2 : ‖(matchedA E)⁻¹‖ = 1 := by rw [norm_inv, h1, inv_one]
  have h3 : ‖(b : ℂ) * matchedA E‖ = b := by
    rw [norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
  have := norm_sub_norm_le (matchedA E)⁻¹ (-((b : ℂ) * matchedA E))
  rw [norm_neg, h2, h3, sub_neg_eq_add] at this
  rw [boundaryZ]; linarith

theorem pfiu_norm_boundaryZ_le {b E : ℝ} (hb0 : 0 ≤ b) (he : E ^ 2 ≤ 4) :
    ‖boundaryZ b E‖ ≤ 1 + b := by
  have h1 := pfiu_norm_matchedA he
  rw [boundaryZ]
  refine (norm_add_le _ _).trans ?_
  rw [norm_inv, h1, inv_one, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb0]

theorem pfiu_pfiBeta_ge {b E m : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (hm : m ^ 2 < 4)
    (hE : E ^ 2 ≤ m ^ 2) : Real.sqrt (4 - m ^ 2) / 16 ≤ pfiBeta b E := by
  have he : E ^ 2 ≤ 4 := by linarith
  have hz0 : boundaryZ b E ≠ 0 := by
    intro h; have := pfiu_norm_boundaryZ_ge hb0 he; rw [h, norm_zero] at this; linarith
  have hβ : pfiBeta b E = (boundaryZ b E).im / ‖boundaryZ b E‖ ^ 2 := by
    rw [pfiBeta, Complex.inv_im, neg_div, neg_neg, Complex.normSq_eq_norm_sq]
  rw [hβ, pfiu_boundaryZ_im_eq b he]
  have hn := pfiu_norm_boundaryZ_le hb0 he
  have hnp : 0 < ‖boundaryZ b E‖ := norm_pos_iff.2 hz0
  have hsq : Real.sqrt (4 - m ^ 2) ≤ Real.sqrt (4 - E ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hs0 := Real.sqrt_nonneg (4 - m ^ 2)
  rw [le_div_iff₀ (by positivity)]
  have h4 : ‖boundaryZ b E‖ ^ 2 ≤ 4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hs0]

/-- **The path fractional-inverse bound uniformly in the microscopic energy window**, from
`ConditionalBlockGUECount` only. -/
theorem pathFractionalInverseEnergyUniform_of_contracts (hCount : ConditionalBlockGUECount) :
    PathFractionalInverseEnergyUniform := by
  intro b hb0 hb1 E hE1 hE2 τ hτ j hj s hs0 hs1 Ce
  obtain ⟨C, hC, hmom⟩ := lintegral_schur_inv_rpow_le hCount guelawBridge_holds
  set C' := C / Real.sqrt (1 - 2 * b)
  have hC' : 0 ≤ C' := div_nonneg hC.le (Real.sqrt_nonneg _)
  set m := (2 + |E|) / 2 with hmdef
  have hE : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
  have hm0 : 0 ≤ m := by positivity
  have hm2 : m < 2 := by rw [hmdef]; linarith
  have hm : m ^ 2 < 4 := by nlinarith
  set βm := Real.sqrt (4 - m ^ 2) / 16
  have hβm : 0 < βm := div_pos (Real.sqrt_pos.2 (by linarith)) (by norm_num)
  set δ0 := (2 - |E|) / 2 with hδ0def
  have hδ0 : 0 < δ0 := by positivity
  refine ⟨(C' * (τ + 1)) ^ s / (1 - s) + (2 * 2) ^ s * (βm ^ (s / 2))⁻¹ *
      ((C' * (τ + 1)) ^ (s / 2) / (1 - s / 2)) + (2 + 2 ^ 2 / βm) ^ s, ?_⟩
  have hev : ∀ᶠ W : ℕ in atTop, (j W : ℝ) / W < τ + 1 :=
    hj.eventually (Iio_mem_nhds (by linarith))
  have hev2 : ∀ᶠ W : ℕ in atTop, |Ce| / (W : ℝ) < δ0 :=
    (tendsto_const_div_atTop_nhds_zero_nat |Ce|).eventually (Iio_mem_nhds hδ0)
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.1 (hev.and hev2)
  refine ⟨max W₁ 1, fun W hW E' hE' => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  obtain ⟨hjW, hCeW⟩ := hW₁ W (le_trans (le_max_left _ _) hW)
  have hn : ((j W : ℕ) : ℝ) ≤ (τ + 1) * W := by
    rw [div_lt_iff₀ hW0] at hjW; exact hjW.le
  -- the energy stays in the compact bulk neighbourhood
  have hEE : |E' - E| ≤ δ0 := by
    have h1 : Ce / (W : ℝ) ^ 2 ≤ |Ce| / W := by
      have hW2 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
        nlinarith
      calc Ce / (W : ℝ) ^ 2 ≤ |Ce| / (W : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |Ce| / W := div_le_div_of_nonneg_left (abs_nonneg _) hW0 hW2
    exact (hE'.trans h1).trans hCeW.le
  have hE'abs : |E'| ≤ m := by
    have := abs_sub_abs_le_abs_sub E' E
    rw [hmdef]; rw [hδ0def] at hEE; linarith
  have hE'1 : -2 < E' := by linarith [neg_abs_le E']
  have hE'2 : E' < 2 := by linarith [le_abs_self E']
  have hE'sq : E' ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hE'abs 2
  obtain ⟨ha, hbd⟩ := pfiu_bound_at hC hmom hCount hb0 hb1 hE'1 hE'2 hτ hs0 hs1 hW1 hn
  refine ⟨ha, hbd.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  -- monotonicity of the constant in `|z|⁻¹ ≤ 2` and `β ≥ βm`
  have he' : E' ^ 2 ≤ 4 := by linarith
  have hzi : ‖boundaryZ b E'‖⁻¹ ≤ 2 := by
    have := pfiu_norm_boundaryZ_ge hb0.le he'
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hzi0 : 0 ≤ ‖boundaryZ b E'‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hβ := pfiu_pfiBeta_ge hb0.le hb1.le hm hE'sq
  have hβ0 : 0 < pfiBeta b E' := hβm.trans_le hβ
  have hA : 0 ≤ (C' * (τ + 1)) ^ (s / 2) / (1 - s / 2) :=
    div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
  have hk1 : (2 * ‖boundaryZ b E'‖⁻¹) ^ s ≤ (2 * 2) ^ s :=
    Real.rpow_le_rpow (by positivity) (by linarith) hs0.le
  have hk2 : (pfiBeta b E' ^ (s / 2))⁻¹ ≤ (βm ^ (s / 2))⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos hβm _) (Real.rpow_le_rpow hβm.le hβ (by linarith))
  have hk3 : (‖boundaryZ b E'‖⁻¹ + ‖boundaryZ b E'‖⁻¹ ^ 2 / pfiBeta b E') ^ s ≤
      (2 + 2 ^ 2 / βm) ^ s := by
    refine Real.rpow_le_rpow (by positivity) (add_le_add hzi ?_) hs0.le
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hzi0 hzi 2) hβm hβ
  have hk12 : (2 * ‖boundaryZ b E'‖⁻¹) ^ s * (pfiBeta b E' ^ (s / 2))⁻¹ ≤
      (2 * 2) ^ s * (βm ^ (s / 2))⁻¹ :=
    mul_le_mul hk1 hk2 (inv_nonneg.2 (Real.rpow_nonneg hβ0.le _)) (by positivity)
  have := mul_le_mul_of_nonneg_right hk12 hA
  linarith

end BlockBand.Endpoints
