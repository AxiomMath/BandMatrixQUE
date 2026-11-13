module

public import BlockBand.Endpoints.Response.PathFractionalInverseMoment

/-!
# The path fractional inverse moment

This file proves `PathFractionalInverse` from `ConditionalBlockGUECount` and the GUE law bridge
(`pathFractionalInverse_holds`).

The proof has three steps.
1. Schur out the two leads (`norm_fromBlocks_inv_le`, `isUnit_det_fromBlocks_of_schur`):
   `‖𝓜⁻¹‖ ≤ X + 2|z|⁻¹√(X/β) + |z|⁻¹ + |z|⁻²/β`, `X = ‖S⁻¹‖`, `S = H_path - E - z⁻¹CC*`;
   the Ward identity removes the need for moments of the endpoint-coupling norms.
2. The Wegner estimate (through `ConditionalBlockGUECount`) and tail integration on the real
   axis; subharmonicity of `‖·‖^s` on the Cayley disk and Tonelli; Fatou in the positive height:
   `E X^p ≤ (C/√c · nW)^p/(1-p)` for `0 < p < 1` (`lintegral_schur_inv_rpow_le`).
3. With `p = s` and `p = s/2`, `W ≥ 1` and `n = j W ≤ (τ+1)W`:
   `E (‖𝓜⁻¹‖/W²)^s ≤ (C'(τ+1))^s/(1-s) + (2|z|⁻¹)^s β^{-s/2}(C'(τ+1))^{s/2}/(1-s/2) + K₂^s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory ProbabilityTheory Complex Set Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-- Normalized moments: `E (X/W²)^p ≤ (C'(τ+1))^p/(1-p)` when `n ≤ (τ+1)W`, `W ≥ 1`. -/
theorem lintegral_div_sq_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {C' τ : ℝ} (hC' : 0 ≤ C') {W n : ℕ} (hW : 1 ≤ W)
    (hn : (n : ℝ) ≤ (τ + 1) * W) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h : ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂P ≤
      ENNReal.ofReal ((C' * ((n * W : ℕ) : ℝ)) ^ p / (1 - p))) (hX : ∀ ω, 0 ≤ X ω) :
    ∫⁻ ω, ENNReal.ofReal ((X ω / (W : ℝ) ^ 2) ^ p) ∂P ≤
      ENNReal.ofReal ((C' * (τ + 1)) ^ p / (1 - p)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  have e : ∀ ω, ENNReal.ofReal ((X ω / (W : ℝ) ^ 2) ^ p) =
      ENNReal.ofReal (X ω ^ p) * ENNReal.ofReal (((W : ℝ) ^ 2) ^ p)⁻¹ := fun ω => by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hX ω) _), Real.div_rpow (hX ω) hW2.le,
      div_eq_mul_inv]
  simp_rw [e]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_left h _).trans ?_
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, ← Real.inv_rpow hW2.le, ← Real.mul_rpow (by positivity)
    (by positivity)]
  have hle : C' * ((n * W : ℕ) : ℝ) * ((W : ℝ) ^ 2)⁻¹ ≤ C' * (τ + 1) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC'
    push_cast
    rw [← div_eq_mul_inv, div_le_iff₀ hW2]
    have : (n : ℝ) * W ≤ (τ + 1) * W * W := mul_le_mul_of_nonneg_right hn hW0.le
    nlinarith
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hle hp0.le)
    (by linarith)

/-- `(a + b + c)^s ≤ a^s + b^s + c^s` for `a, b, c ≥ 0`, `0 ≤ s ≤ 1`. -/
theorem rpow_add_add_le {a b c s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : (a + b + c) ^ s ≤ a ^ s + b ^ s + c ^ s :=
  (Real.rpow_add_le_add_rpow (add_nonneg ha hb) hc hs0 hs1).trans
    (add_le_add_left (Real.rpow_add_le_add_rpow ha hb hs0 hs1) _)

/-- The path fractional inverse moment, including the almost-sure invertibility (a). -/
theorem pathFractionalInverse_holds (hCount : ConditionalBlockGUECount)
    (hGUE : GUELawBridge) : PathFractionalInverse := by
  intro b hb0 hb1 E hE1 hE2 τ hτ j hj s hs0 hs1
  obtain ⟨C, hC, hmom⟩ := lintegral_schur_inv_rpow_le hCount hGUE
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
  refine ⟨(C' * (τ + 1)) ^ s / (1 - s) +
      K1 ^ s * (β ^ (s / 2))⁻¹ * ((C' * (τ + 1)) ^ (s / 2) / (1 - s / 2)) + K2 ^ s, ?_⟩
  -- the threshold `W₀`
  have hev : ∀ᶠ W : ℕ in atTop, (j W : ℝ) / W < τ + 1 :=
    hj.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.1 hev
  refine ⟨max W₁ 1, fun W hW => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWpos : 0 < W := hW1
  have hn : ((j W : ℕ) : ℝ) ≤ (τ + 1) * W := by
    have := hW₁ W (le_trans (le_max_left _ _) hW)
    rw [div_lt_iff₀ hW0] at this
    exact this.le
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hSinv := ae_isUnit_schur hCount hGUE hb1 hE1 hE2 hWpos (j W)
  refine ⟨?_, ?_⟩
  · -- part (a)
    filter_upwards [hSinv] with ω hω
    rw [fullPathMatrix_eq]
    exact isUnit_det_fromBlocks_of_schur hz0 hω
  · -- part (b)
    set X : GrowthPath W → ℝ := fun ω => ‖(pfiSchur b E W (j W) ω)⁻¹‖ with hXdef
    set Y : GrowthPath W → ℝ := fun ω => X ω / (W : ℝ) ^ 2 with hYdef
    have hX0 : ∀ ω, 0 ≤ X ω := fun ω => norm_nonneg _
    have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => div_nonneg (hX0 ω) (by positivity)
    have hXm : Measurable X :=
      continuous_norm.measurable.comp (pfi_measurable_inv.comp (measurable_pfiSchur b E W (j W)))
    have hYm : Measurable Y := hXm.div_const _
    -- pointwise bound
    have hpt : ∀ᵐ ω ∂growthPathLaw W b,
        (‖fullInverse b E W (j W) ω‖ / (W : ℝ) ^ 2) ^ s ≤
          Y ω ^ s + K1 ^ s * (β ^ (s / 2))⁻¹ * Y ω ^ (s / 2) + K2 ^ s := by
      filter_upwards [hSinv, ae_growthPath_isHermitian W b] with ω hω hH
      have hG := norm_fromBlocks_inv_le (pfiInt_isHermitian E W (j W) hH) (pfiCoup W (j W) ω.2)
        hzim hω
      rw [← fullPathMatrix_eq] at hG
      change ‖fullInverse b E W (j W) ω‖ ≤ X ω + 2 * ‖z‖⁻¹ * Real.sqrt (X ω / β) +
        ‖z‖⁻¹ + ‖z‖⁻¹ ^ 2 / β at hG
      have hXY : X ω = Y ω * (W : ℝ) ^ 2 := by
        rw [hYdef]; field_simp
      have hsq : Real.sqrt (X ω / β) = W * Real.sqrt (Y ω / β) := by
        rw [hXY, mul_comm, mul_div_assoc, Real.sqrt_mul (by positivity),
          Real.sqrt_sq hW0.le]
      have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW1)
      have hbound : ‖fullInverse b E W (j W) ω‖ / (W : ℝ) ^ 2 ≤
          Y ω + K1 * Real.sqrt (Y ω / β) + K2 := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : K1 * Real.sqrt (X ω / β) ≤ K1 * Real.sqrt (Y ω / β) * (W : ℝ) ^ 2 := by
          rw [hsq]
          have : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
          have h0 : 0 ≤ K1 * Real.sqrt (Y ω / β) := by positivity
          nlinarith
        have h2 : K2 ≤ K2 * (W : ℝ) ^ 2 := le_mul_of_one_le_right hK2n hW2
        calc ‖fullInverse b E W (j W) ω‖ ≤ X ω + K1 * Real.sqrt (X ω / β) + K2 := by
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
      (hmom b hb0 hb1 E hE1 hE2 W (j W) hWpos s hs0 hs1) hX0
    have hI2 := lintegral_div_sq_rpow_le hC' hW1 hn (by linarith : 0 < s / 2)
      (by linarith : s / 2 < 1) (hmom b hb0 hb1 E hE1 hE2 W (j W) hWpos (s / 2) (by linarith)
        (by linarith)) hX0
    have hc2 : 0 ≤ K1 ^ s * (β ^ (s / 2))⁻¹ := by positivity
    calc ∫⁻ ω, ENNReal.ofReal ((‖fullInverse b E W (j W) ω‖ / (W : ℝ) ^ 2) ^ s)
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

end BlockBand.Endpoints
