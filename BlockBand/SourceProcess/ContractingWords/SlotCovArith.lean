module

public import BlockBand.SourceProcess.ContractingWords.SlotCovAlg

/-!
# The arithmetic of the slot covariance bound

Real inequalities in `W`, `√W`, the error scale `e` and the conductance `g`, combined in
`cov_arith` to bound the slot covariance error.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

theorem arith_a {r W : ℝ} (hr1 : 1 ≤ r) (hrr : r * r = W) : W⁻¹ ^ 2 ≤ W⁻¹ / r := by
  rw [← hrr]
  have hr0 : 0 < r := by linarith
  have h : (r * r)⁻¹ ^ 2 = (r * r)⁻¹ / r * r⁻¹ := by field_simp
  rw [h]
  have h1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have h2 : 0 ≤ (r * r)⁻¹ / r := by positivity
  calc (r * r)⁻¹ / r * r⁻¹ ≤ (r * r)⁻¹ / r * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := mul_one _

theorem arith_c {r W e : ℝ} (hr1 : 1 ≤ r) (hrr : r * r = W) :
    r⁻¹ * (1 / r + e) ^ 2 ≤ 2 * (W⁻¹ / r + e ^ 2) := by
  have hr0 : 0 < r := by linarith
  have h1 : (1 / r + e) ^ 2 ≤ 2 * ((1 / r) ^ 2 + e ^ 2) := by nlinarith [sq_nonneg (1 / r - e)]
  have h2 : r⁻¹ * (1 / r) ^ 2 = W⁻¹ / r := by rw [← hrr]; field_simp
  have h3 : r⁻¹ * e ^ 2 ≤ e ^ 2 := by
    have := inv_le_one_of_one_le₀ hr1
    have := inv_pos.mpr hr0
    nlinarith [sq_nonneg e]
  calc r⁻¹ * (1 / r + e) ^ 2 ≤ r⁻¹ * (2 * ((1 / r) ^ 2 + e ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * (r⁻¹ * (1 / r) ^ 2 + r⁻¹ * e ^ 2) := by ring
    _ ≤ 2 * (W⁻¹ / r + e ^ 2) := by rw [h2]; linarith

theorem arith_d1 {W g δ₀ q : ℝ} (hq : q ^ 2 = g / W) :
    (g / W + δ₀ * q) ^ 2 ≤ 2 * ((g / W) ^ 2 + δ₀ ^ 2 * (g / W)) := by
  have := sq_nonneg (g / W - δ₀ * q)
  have e : (δ₀ * q) ^ 2 = δ₀ ^ 2 * (g / W) := by rw [mul_pow, hq]
  nlinarith [e]

theorem arith_d {r W e δ₀ g q : ℝ} (hr1 : 1 ≤ r) (hrr : r * r = W) (hδ : δ₀ ≤ e)
    (hδ0 : 0 ≤ δ₀) (hg : 0 ≤ g) (hq : q ^ 2 = g / W) :
    (r + 1) * (g / W + δ₀ * q) ^ 2 ≤ 4 * ((g ^ 2 + g) * (W⁻¹ / r + e ^ 2)) := by
  have hr0 : 0 < r := by linarith
  have h1 := arith_d1 (δ₀ := δ₀) hq
  have h2 : r * (g / W) ^ 2 = g ^ 2 * (W⁻¹ / r) := by rw [← hrr]; field_simp
  have h3 : r * (δ₀ ^ 2 * (g / W)) ≤ g * e ^ 2 := by
    have e1 : r * (δ₀ ^ 2 * (g / W)) = δ₀ ^ 2 * g * r⁻¹ := by rw [← hrr]; field_simp
    rw [e1]
    have hi := inv_le_one_of_one_le₀ hr1
    have hd2 : δ₀ ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
    have hri : 0 ≤ r⁻¹ := by positivity
    calc δ₀ ^ 2 * g * r⁻¹ ≤ e ^ 2 * g * 1 := by gcongr
      _ = g * e ^ 2 := by ring
  have hA0 : 0 ≤ W⁻¹ / r := by rw [← hrr]; positivity
  have h4 : 0 ≤ (g / W + δ₀ * q) ^ 2 := sq_nonneg _
  calc (r + 1) * (g / W + δ₀ * q) ^ 2 ≤ (2 * r) * (g / W + δ₀ * q) ^ 2 := by gcongr; linarith
    _ ≤ (2 * r) * (2 * ((g / W) ^ 2 + δ₀ ^ 2 * (g / W))) := by gcongr
    _ = 4 * (r * (g / W) ^ 2 + r * (δ₀ ^ 2 * (g / W))) := by ring
    _ ≤ 4 * (g ^ 2 * (W⁻¹ / r) + g * e ^ 2) := by rw [h2]; linarith
    _ ≤ 4 * ((g ^ 2 + g) * (W⁻¹ / r + e ^ 2)) := by
        nlinarith [mul_nonneg (sq_nonneg g) (sq_nonneg e), mul_nonneg hg hA0]

theorem arith_final {CF C₂ CΓ g A e T1 T2 T3 : ℝ} (hCF : 0 ≤ CF)
    (hg : 0 ≤ g) (hAe : 0 ≤ A + e ^ 2) (h1 : T1 ≤ CF * (A + e ^ 2))
    (h2 : T2 ≤ C₂ ^ 2 * (2 * (A + e ^ 2))) (h3 : T3 ≤ CΓ ^ 2 * (4 * ((g ^ 2 + g) * (A + e ^ 2)))) :
    T1 + T2 + T3 ≤ (CF + 2 * C₂ ^ 2 + 4 * CΓ ^ 2) * (1 + g) ^ 2 * (A + e ^ 2) := by
  have hg1 : 1 ≤ (1 + g) ^ 2 := by nlinarith
  have hg2 : g ^ 2 + g ≤ (1 + g) ^ 2 := by nlinarith
  have k1 : CF * (A + e ^ 2) ≤ CF * (1 + g) ^ 2 * (A + e ^ 2) := by
    have := mul_le_mul_of_nonneg_right hg1 hAe
    nlinarith
  have k2 : C₂ ^ 2 * (2 * (A + e ^ 2)) ≤ 2 * C₂ ^ 2 * (1 + g) ^ 2 * (A + e ^ 2) := by
    have := mul_le_mul_of_nonneg_right hg1 hAe
    nlinarith [sq_nonneg C₂]
  have k3 : CΓ ^ 2 * (4 * ((g ^ 2 + g) * (A + e ^ 2))) ≤
      4 * CΓ ^ 2 * (1 + g) ^ 2 * (A + e ^ 2) := by
    have := mul_le_mul_of_nonneg_right hg2 hAe
    nlinarith [sq_nonneg CΓ]
  nlinarith

theorem cov_arith {W e δ₀ δ₁ g CF C₂ CΓ : ℝ} (hW : 1 ≤ W) (he : W⁻¹ ≤ e) (hδ : δ₀ ≤ e)
    (hsum : δ₀ + δ₁ + g / W ≤ e) (hδ0 : 0 ≤ δ₀) (hδ1 : 0 ≤ δ₁) (hg : 0 ≤ g) (hCF : 0 ≤ CF) :
    CF * (W⁻¹ ^ 2 + W⁻¹ * (δ₀ + δ₁ + g / W)) +
        (Real.sqrt W)⁻¹ * (C₂ * (1 / Real.sqrt W + e)) ^ 2 +
        (Real.sqrt W + 1) * (CΓ * (g / W + δ₀ * Real.sqrt (g / W))) ^ 2 ≤
      (CF + 2 * C₂ ^ 2 + 4 * CΓ ^ 2) * (1 + g) ^ 2 * (W⁻¹ / Real.sqrt W + e ^ 2) := by
  have hr1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.mpr hW
  have hrr : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt (by linarith)
  have hW0 : 0 < W := by linarith
  have he0 : 0 ≤ e := (inv_nonneg.mpr hW0.le).trans he
  have hq : Real.sqrt (g / W) ^ 2 = g / W := Real.sq_sqrt (div_nonneg hg hW0.le)
  have hA0 : 0 ≤ W⁻¹ / Real.sqrt W := by positivity
  have hs0 : 0 ≤ δ₀ + δ₁ + g / W := by positivity
  refine arith_final hCF hg (by positivity) ?_ ?_ ?_
  · refine mul_le_mul_of_nonneg_left ?_ hCF
    have := arith_a hr1 hrr
    have : W⁻¹ * (δ₀ + δ₁ + g / W) ≤ e ^ 2 := by
      rw [sq]; exact mul_le_mul he hsum hs0 he0
    linarith
  · calc (Real.sqrt W)⁻¹ * (C₂ * (1 / Real.sqrt W + e)) ^ 2 =
          C₂ ^ 2 * ((Real.sqrt W)⁻¹ * (1 / Real.sqrt W + e) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (arith_c hr1 hrr) (sq_nonneg _)
  · calc (Real.sqrt W + 1) * (CΓ * (g / W + δ₀ * Real.sqrt (g / W))) ^ 2 =
          CΓ ^ 2 * ((Real.sqrt W + 1) * (g / W + δ₀ * Real.sqrt (g / W)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (arith_d hr1 hrr hδ hδ0 hg hq) (sq_nonneg _)

end BlockBand.SourceProcess.ContractingWords
