module

public import BlockBand.Native.ErdosRiabov.Flow.Traj
public import BlockBand.Native.ErdosRiabov.Kernel.Control

/-!
# Scales along the VS flow

Bounds on the localization length `ℓ(η)` and the scale ratios along the VS flow.

`ℓ(η) = localizationLength N W η = min (W/√η) N` (the Erdős–Riabov localization length),
`ℓ_t = ℓ(η_t)` with
`η_t = vsHeight z t`. Height-level facts (any `η ≥ N^{-1+δ₀}`, `W² ≥ N^{1+ζ₀}`, `δ₀ ≤ ζ₀`):
`ℓη ≥ N^{δ₀}` (`loc_mul_ge_rpow`), `√(Nη)/(ℓη) ≤ N^{-δ₀/2}` (`sqrt_div_loc_mul_le`),
`ℓ²η ≤ W²` with equality iff `η ≥ (W/N)²` (`loc_sq_mul`). The VS statement is `vsScales`.
No lower bound `N ≥ N₀` is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Flow

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Adapters.ErdosRiabov (loc_mul_eq loc_antitone loc_mul_mono loc_le_N loc_eq_N)

/-- `W² ≥ N^{1+ζ₀}` gives `W ≥ N^{(1+ζ₀)/2}`. -/
theorem rpow_le_W {N W : ℕ} (hN : 0 < N) {ζ₀ : ℝ} (hP6 : (N : ℝ) ^ (1 + ζ₀) ≤ (W : ℝ) ^ 2) :
    (N : ℝ) ^ ((1 + ζ₀) / 2) ≤ W := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ((N : ℝ) ^ ((1 + ζ₀) / 2)) ^ 2 = (N : ℝ) ^ (1 + ζ₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  rw [← hsq] at hP6
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hN0.le _) (Nat.cast_nonneg _)
    two_ne_zero).mp hP6

/-- `√η ≥ N^{(-1+δ₀)/2}` for `η ≥ N^{-1+δ₀}`. -/
theorem rpow_le_sqrt {N : ℕ} (hN : 0 < N) {δ₀ η : ℝ} (hη : (N : ℝ) ^ (-1 + δ₀) ≤ η) :
    (N : ℝ) ^ ((-1 + δ₀) / 2) ≤ Real.sqrt η := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow]
  calc (N : ℝ) ^ ((-1 + δ₀) / 2) = ((N : ℝ) ^ (-1 + δ₀)) ^ (1 / (2 : ℝ)) := by
        rw [← Real.rpow_mul hN0.le]
        ring_nf
    _ ≤ η ^ (1 / (2 : ℝ)) := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hη (by norm_num)

/-- **Scales (a), lower bound**: `ℓ(η) η ≥ N^{δ₀}` for `η ≥ N^{-1+δ₀}`, under
`W² ≥ N^{1+ζ₀}` and `δ₀ ≤ ζ₀`. -/
theorem loc_mul_ge_rpow {N W : ℕ} (hN : 0 < N) {δ₀ ζ₀ η : ℝ} (hδζ : δ₀ ≤ ζ₀)
    (hP6 : (N : ℝ) ^ (1 + ζ₀) ≤ (W : ℝ) ^ 2) (hη : (N : ℝ) ^ (-1 + δ₀) ≤ η) :
    (N : ℝ) ^ δ₀ ≤ localizationLength N W η * η := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hηpos : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hη
  rw [loc_mul_eq N W hηpos]
  apply le_min
  · calc (N : ℝ) ^ δ₀ ≤ (N : ℝ) ^ ((1 + ζ₀) / 2 + (-1 + δ₀) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (N : ℝ) ^ ((1 + ζ₀) / 2) * (N : ℝ) ^ ((-1 + δ₀) / 2) := Real.rpow_add hN0 _ _
      _ ≤ (W : ℝ) * Real.sqrt η :=
          mul_le_mul (rpow_le_W hN hP6) (rpow_le_sqrt hN hη) (Real.rpow_nonneg hN0.le _)
            (Nat.cast_nonneg _)
  · calc (N : ℝ) ^ δ₀ = (N : ℝ) ^ ((1 : ℝ) + (-1 + δ₀)) := by
          congr 1
          ring
      _ = (N : ℝ) * (N : ℝ) ^ (-1 + δ₀) := by rw [Real.rpow_add hN0, Real.rpow_one]
      _ ≤ (N : ℝ) * η := mul_le_mul_of_nonneg_left hη hN0.le

/-- **Scales (c)**: `√(Nη)/(ℓ(η)η) ≤ N^{-δ₀/2}` for `η ≥ N^{-1+δ₀}`, under `W² ≥ N^{1+ζ₀}` and
`δ₀ ≤ ζ₀`. -/
theorem sqrt_div_loc_mul_le {N W : ℕ} (hN : 0 < N) {δ₀ ζ₀ η : ℝ} (hδζ : δ₀ ≤ ζ₀)
    (hP6 : (N : ℝ) ^ (1 + ζ₀) ≤ (W : ℝ) ^ 2) (hη : (N : ℝ) ^ (-1 + δ₀) ≤ η) :
    Real.sqrt ((N : ℝ) * η) / (localizationLength N W η * η) ≤ (N : ℝ) ^ (-δ₀ / 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hηpos : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hη
  have hL := loc_mul_ge_rpow hN hδζ hP6 hη
  have hW := rpow_le_W hN hP6
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hW
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hηpos
  rw [loc_mul_eq N W hηpos] at hL ⊢
  rcases min_cases ((W : ℝ) * Real.sqrt η) ((N : ℝ) * η) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · calc Real.sqrt ((N : ℝ) * η) / ((W : ℝ) * Real.sqrt η) = (N : ℝ) ^ (1 / (2 : ℝ)) / W := by
          have := hsη.ne'
          have := hWpos.ne'
          rw [Real.sqrt_mul hN0.le, ← Real.sqrt_eq_rpow]
          field_simp
      _ ≤ (N : ℝ) ^ (1 / (2 : ℝ)) / (N : ℝ) ^ ((1 + ζ₀) / 2) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) (Real.rpow_pos_of_pos hN0 _) hW
      _ = (N : ℝ) ^ (-ζ₀ / 2) := by
          rw [← Real.rpow_sub hN0]
          ring_nf
      _ ≤ (N : ℝ) ^ (-δ₀ / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · rw [h] at hL
    set u := Real.sqrt ((N : ℝ) * η)
    have hNη : 0 < (N : ℝ) * η := mul_pos hN0 hηpos
    have hu : 0 < u := Real.sqrt_pos.mpr hNη
    have hu2 : (N : ℝ) * η = u * u := (Real.mul_self_sqrt hNη.le).symm
    have hlow : (N : ℝ) ^ (δ₀ / 2) ≤ u := by
      have : (N : ℝ) ^ (δ₀ / 2) = Real.sqrt ((N : ℝ) ^ δ₀) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
        ring_nf
      rw [this]
      exact Real.sqrt_le_sqrt hL
    rw [hu2, div_mul_cancel_right₀ hu.ne', show -δ₀ / 2 = -(δ₀ / 2) by ring,
      Real.rpow_neg hN0.le]
    exact (inv_le_inv₀ hu (Real.rpow_pos_of_pos hN0 _)).mpr hlow

/-- Above `(W/N)²` the localization length is `W/√η`. -/
theorem loc_eq_W_div_sqrt {N W : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η)
    (hbig : ((W : ℝ) / N) ^ 2 ≤ η) : localizationLength N W η = (W : ℝ) / Real.sqrt η := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  unfold localizationLength
  apply min_eq_left
  have h1 : (W : ℝ) / N ≤ Real.sqrt η := by
    rw [show (W : ℝ) / N = Real.sqrt (((W : ℝ) / N) ^ 2) by
      rw [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) hN0.le)]]
    exact Real.sqrt_le_sqrt hbig
  rw [div_le_iff₀ hN0] at h1
  rw [div_le_iff₀ hs]
  linarith

/-- **Scales (d)**: `ℓ(η)² η ≤ W²`, with equality iff `η ≥ (W/N)²` (`N ≥ 1`, `η > 0`). -/
theorem loc_sq_mul {N W : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    localizationLength N W η ^ 2 * η ≤ (W : ℝ) ^ 2 ∧
      (localizationLength N W η ^ 2 * η = (W : ℝ) ^ 2 ↔ ((W : ℝ) / N) ^ 2 ≤ η) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hss : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη.le
  have hℓ0 : 0 ≤ localizationLength N W η :=
    le_min (div_nonneg (Nat.cast_nonneg _) hs.le) (Nat.cast_nonneg _)
  have hℓW : localizationLength N W η * Real.sqrt η ≤ W := by
    calc localizationLength N W η * Real.sqrt η ≤ (W : ℝ) / Real.sqrt η * Real.sqrt η :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le
      _ = W := div_mul_cancel₀ _ hs.ne'
  have hsq : localizationLength N W η ^ 2 * η = (localizationLength N W η * Real.sqrt η) ^ 2 := by
    rw [mul_pow, sq (Real.sqrt η), hss]
  refine ⟨?_, ⟨fun heq => ?_, fun hbig => ?_⟩⟩
  · rw [hsq]
    exact pow_le_pow_left₀ (mul_nonneg hℓ0 hs.le) hℓW 2
  · by_contra hlt
    rw [not_le] at hlt
    rw [loc_eq_N hN hη hlt.le] at heq
    have h1 : (N : ℝ) ^ 2 * η < (N : ℝ) ^ 2 * ((W : ℝ) / N) ^ 2 :=
      mul_lt_mul_of_pos_left hlt (by positivity)
    have h2 : (N : ℝ) ^ 2 * ((W : ℝ) / N) ^ 2 = (W : ℝ) ^ 2 := by
      have := hN0.ne'
      field_simp
    linarith
  · have := hη.ne'
    rw [loc_eq_W_div_sqrt hN hη hbig, div_pow, Real.sq_sqrt hη.le]
    field_simp

/-- Let `N ≥ 1`, `W ≤ N`, `0 < κ`, `C₀ ≥ 0`,
`δ₀ ≤ ζ₀`, P6 `W² ≥ N^{1+ζ₀}`, `z ∈ 𝒟 = BulkDomain N δ₀ κ C₀ z`, `η_r = vsHeight z r`,
`ℓ_r = localizationLength N W η_r`, `c_m = imLower κ C₀`.
For `0 ≤ s ≤ t ≤ 1`:
(a) `ℓ_s ≤ ℓ_t`, `ℓ_tη_t ≤ ℓ_sη_s`, `N^{δ₀} ≤ ℓ_tη_t`;
(b) `W/√(C₀+1) ≤ ℓ_t ≤ N`;
(c) `√(Nη_t)/(ℓ_tη_t) ≤ N^{-δ₀/2}`;
(d) `ℓ_t²η_t ≤ W²`, with equality iff `η_t ≥ (W/N)²`;
(e) `η_s - η_t ≤ t - s ≤ (η_s - η_t)/c_m`.
Uniform in `N, W, z, s, t`; no `N₀`.
-/
theorem vsScales {N W : ℕ} {δ₀ ζ₀ κ C₀ : ℝ} {z : ℂ} (hN : 0 < N) (hWN : W ≤ N) (hκ : 0 < κ)
    (hC₀ : 0 ≤ C₀) (hδζ : δ₀ ≤ ζ₀) (hP6 : (N : ℝ) ^ (1 + ζ₀) ≤ (W : ℝ) ^ 2)
    (hz : BulkDomain N δ₀ κ C₀ z) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    localizationLength N W (vsHeight z s) ≤ localizationLength N W (vsHeight z t) ∧
      localizationLength N W (vsHeight z t) * vsHeight z t ≤
        localizationLength N W (vsHeight z s) * vsHeight z s ∧
      (N : ℝ) ^ δ₀ ≤ localizationLength N W (vsHeight z t) * vsHeight z t ∧
      (W : ℝ) / Real.sqrt (C₀ + 1) ≤ localizationLength N W (vsHeight z t) ∧
      localizationLength N W (vsHeight z t) ≤ N ∧
      Real.sqrt ((N : ℝ) * vsHeight z t) /
          (localizationLength N W (vsHeight z t) * vsHeight z t) ≤ (N : ℝ) ^ (-δ₀ / 2) ∧
      localizationLength N W (vsHeight z t) ^ 2 * vsHeight z t ≤ (W : ℝ) ^ 2 ∧
      (localizationLength N W (vsHeight z t) ^ 2 * vsHeight z t = (W : ℝ) ^ 2 ↔
        ((W : ℝ) / N) ^ 2 ≤ vsHeight z t) ∧
      vsHeight z s - vsHeight z t ≤ t - s ∧
      t - s ≤ (vsHeight z s - vsHeight z t) / imLower κ C₀ := by
  obtain ⟨_, _, _, hy1, hbd, _, hC, _, _, hsub, hdiff⟩ := vsFlow_b hN hκ hC₀ hz
  have hη := hz.im_pos hN
  have hy := semicircleM_im_pos hη
  have hbt := hbd t (hs0.trans hst) ht1
  have hbs := hbd s hs0 (hst.trans ht1)
  have hηt : (N : ℝ) ^ (-1 + δ₀) ≤ vsHeight z t := hz.2.1.trans hbt.1
  have hηtpos : 0 < vsHeight z t := hη.trans_le hbt.1
  have hts : vsHeight z t ≤ vsHeight z s := by
    rw [← sub_nonneg, hsub]
    exact mul_nonneg (by linarith) hy.le
  refine ⟨loc_antitone N W hηtpos hts, loc_mul_mono N W hηtpos hts,
    loc_mul_ge_rpow hN hδζ hP6 hηt, ?_, loc_le_N N W _, sqrt_div_loc_mul_le hN hδζ hP6 hηt,
    (loc_sq_mul hN hηtpos).1, (loc_sq_mul hN hηtpos).2, ?_, (hdiff s t hst ht1).1⟩
  · exact (loc_bounds_of_le hWN (by linarith) hηtpos (hbt.2.trans hC)).1
  · rw [hsub]
    nlinarith

end BlockBand.Native.ErdosRiabov.Flow
