module

public import BlockBand.SourceProcess.PhysApprox.B3FracMomPath

/-!
# The one-sided moment lift at `q = 4` and the step algebra

* `lift_four`: for `P ≥ 0`, `0 ≤ Y ≤ P + X`,
  `Y⁴ ≤ (P+X)⁴ - (1/8)P³(P+X-Y) + (1/2)P²X²` (the indicator `1_{X < -P/2}` of the note is
  majorized by `4X²/P²`);
* `lift_four_expand`: the same with `(P+X)⁴ ≤ P⁴ + 4P³X + 8P²X² + 3X⁴`;
* `sq_wsum_le`: weighted Cauchy–Schwarz `(Σ wY)² ≤ (Σ w)(Σ wY²)`;
* `pow_four_wsum_le`: `(Σ wY)⁴ ≤ (Σ w)³ Σ wY⁴`;
* **`step4_alg`**: the regular-state bound `E P'⁴ ≤ P⁴ + H(δ₀ + 1/W)P⁴ - (c/8W)P³ℓ²` with
  `ℓ ≥ P - 2g` gives `E P'⁴ ≤ P⁴ - (3c/128W)P⁵ + A(W⁴δ₀⁵ + 1/W + g⁵/W)`
  (`ℓ² ≥ P²/2 - 4g²` and Young, as in the note).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.FracMom

/-- **The one-sided lift at `q = 4`.** -/
theorem lift_four {P X Y : ℝ} (hP : 0 ≤ P) (hY0 : 0 ≤ Y) (hY : Y ≤ P + X) :
    Y ^ 4 ≤ (P + X) ^ 4 - 1 / 8 * P ^ 3 * (P + X - Y) + 1 / 2 * P ^ 2 * X ^ 2 := by
  set A := P + X with hA
  have hD : 0 ≤ A - Y := by linarith
  have hYA3 : Y ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ hY0 hY 3
  have hYA4 : Y ^ 4 ≤ A ^ 4 := pow_le_pow_left₀ hY0 hY 4
  have hPX : 0 ≤ 1 / 2 * P ^ 2 * X ^ 2 := by positivity
  rcases le_or_gt (-(P / 2)) X with hX | hX
  · have hAP : P / 2 ≤ A := by rw [hA]; linarith
    have hA3 : (P / 2) ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (by positivity) hAP 3
    have h1 : Y ^ 4 ≤ A ^ 4 - A ^ 3 * (A - Y) := by
      have : 0 ≤ Y * (A ^ 3 - Y ^ 3) := mul_nonneg hY0 (by linarith)
      nlinarith
    have h2 : 1 / 8 * P ^ 3 * (A - Y) ≤ A ^ 3 * (A - Y) := by
      have : 1 / 8 * P ^ 3 = (P / 2) ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hA3 hD
    linarith
  · have hDP : A - Y ≤ P / 2 := by rw [hA]; linarith
    have hX2 : P ^ 2 / 4 ≤ X ^ 2 := by nlinarith
    have hP3 : 0 ≤ P ^ 3 := by positivity
    have h1 : 1 / 8 * P ^ 3 * (A - Y) ≤ 1 / 8 * P ^ 3 * (P / 2) :=
      mul_le_mul_of_nonneg_left hDP (by positivity)
    have h2 : 1 / 8 * P ^ 3 * (P / 2) ≤ 1 / 2 * P ^ 2 * X ^ 2 := by
      have := mul_le_mul_of_nonneg_left hX2 (by positivity : (0 : ℝ) ≤ 1 / 2 * P ^ 2)
      nlinarith
    linarith

/-- `(P+X)⁴ ≤ P⁴ + 4P³X + 8P²X² + 3X⁴`. -/
theorem add_pow_four_le (P X : ℝ) :
    (P + X) ^ 4 ≤ P ^ 4 + 4 * P ^ 3 * X + 8 * P ^ 2 * X ^ 2 + 3 * X ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg X) (sq_nonneg (P - X))]

/-- **The lift, expanded.** -/
theorem lift_four_expand {P X Y : ℝ} (hP : 0 ≤ P) (hY0 : 0 ≤ Y) (hY : Y ≤ P + X) :
    Y ^ 4 ≤ 7 / 8 * P ^ 4 + 31 / 8 * P ^ 3 * X + 17 / 2 * P ^ 2 * X ^ 2 + 3 * X ^ 4 +
      1 / 8 * P ^ 3 * Y := by
  have h1 := lift_four hP hY0 hY
  have h2 := add_pow_four_le P X
  nlinarith

/-- Weighted Cauchy–Schwarz. -/
theorem sq_wsum_le {ι : Type*} (s : Finset ι) (w Y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ s, w i * Y i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * Y i ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => hw i)
    (fun i _ => mul_nonneg (hw i) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))

/-- `(Σ wY)⁴ ≤ (Σ w)³ Σ wY⁴`. -/
theorem pow_four_wsum_le {ι : Type*} (s : Finset ι) (w Y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ s, w i * Y i) ^ 4 ≤ (∑ i ∈ s, w i) ^ 3 * ∑ i ∈ s, w i * Y i ^ 4 := by
  have hS : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg fun i _ => hw i
  have h1 := sq_wsum_le s w Y hw
  have h2 := sq_wsum_le s w (fun i => Y i ^ 2) hw
  simp only [← pow_mul] at h2
  have h1' : ((∑ i ∈ s, w i * Y i) ^ 2) ^ 2 ≤
      ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * Y i ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  calc (∑ i ∈ s, w i * Y i) ^ 4 = ((∑ i ∈ s, w i * Y i) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * Y i ^ 2) ^ 2 := h1'
    _ = (∑ i ∈ s, w i) ^ 2 * (∑ i ∈ s, w i * Y i ^ 2) ^ 2 := by ring
    _ ≤ (∑ i ∈ s, w i) ^ 2 * ((∑ i ∈ s, w i) * ∑ i ∈ s, w i * Y i ^ 4) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (∑ i ∈ s, w i) ^ 3 * ∑ i ∈ s, w i * Y i ^ 4 := by ring

/-- The constant `A` of `step4_alg`. -/
def step4A (H c : ℝ) : ℝ := max ((H + 1) * (64 * (H + 1) / c) ^ 4) (256 * c)

/-- **The step algebra at `q = 4`** (`ℓ² ≥ P²/2 - 4g²` and three Young inequalities). -/
theorem step4_alg {P δ₀ g ℓ Wr H c S4 : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ₀) (hg : 0 ≤ g)
    (hW : 1 ≤ Wr) (hH : 0 ≤ H) (hc : 0 < c) (hlg : P - 2 * g ≤ ℓ)
    (h : S4 ≤ P ^ 4 + H * (δ₀ + 1 / Wr) * P ^ 4 - c / (8 * Wr) * P ^ 3 * ℓ ^ 2) :
    S4 ≤ P ^ 4 - 3 * c / 128 / Wr * P ^ 5 + step4A H c * Wr ^ 4 * δ₀ ^ 5 + step4A H c / Wr +
      step4A H c / Wr * g ^ 5 := by
  have hW0 : 0 < Wr := by linarith
  set H₁ := H + 1 with hH₁
  have hH₁0 : 0 < H₁ := by linarith
  have hA1 : H₁ * (64 * H₁ / c) ^ 4 ≤ step4A H c := le_max_left _ _
  have hA2 : 256 * c ≤ step4A H c := le_max_right _ _
  -- `ℓ² ≥ P²/2 - 4g²`
  have hl2 : P ^ 2 / 2 - 4 * g ^ 2 ≤ ℓ ^ 2 := by
    rcases le_total (2 * g) P with h2 | h2
    · have : (P - 2 * g) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by linarith) hlg 2
      nlinarith [sq_nonneg (P - 4 * g)]
    · nlinarith [sq_nonneg ℓ]
  have hP3 : 0 ≤ P ^ 3 := by positivity
  have hneg : -(c / (8 * Wr) * P ^ 3 * ℓ ^ 2) ≤
      -(c / (16 * Wr) * P ^ 5) + c / (2 * Wr) * (P ^ 3 * g ^ 2) := by
    have := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ c / (8 * Wr) * P ^ 3)
    have e1 : c / (8 * Wr) * P ^ 3 * (P ^ 2 / 2 - 4 * g ^ 2) =
        c / (16 * Wr) * P ^ 5 - c / (2 * Wr) * (P ^ 3 * g ^ 2) := by
      field_simp; ring
    linarith
  -- Young 1: `H₁δ₀P⁴ ≤ (c/64W)P⁵ + H₁(64H₁/c)⁴W⁴δ₀⁵`
  have hy1 := young_pow hP hδ (by positivity : (0 : ℝ) < c / (64 * H₁ * Wr)) 4 1
  have hY1 : H * δ₀ * P ^ 4 ≤ c / (64 * Wr) * P ^ 5 + step4A H c * Wr ^ 4 * δ₀ ^ 5 := by
    have e : H₁ * ((c / (64 * H₁ * Wr)) ^ 4)⁻¹ = H₁ * (64 * H₁ / c) ^ 4 * Wr ^ 4 := by
      field_simp
    have hδ5 : 0 ≤ δ₀ ^ 5 := by positivity
    have hP4 : 0 ≤ P ^ 4 * δ₀ := by positivity
    calc H * δ₀ * P ^ 4 ≤ H₁ * (P ^ 4 * δ₀ ^ 1) := by
          rw [pow_one]; nlinarith
      _ ≤ H₁ * ((c / (64 * H₁ * Wr)) ^ 1 * P ^ (4 + 1) +
            ((c / (64 * H₁ * Wr)) ^ 4)⁻¹ * δ₀ ^ (4 + 1)) :=
          mul_le_mul_of_nonneg_left hy1 hH₁0.le
      _ = c / (64 * Wr) * P ^ 5 + H₁ * ((c / (64 * H₁ * Wr)) ^ 4)⁻¹ * δ₀ ^ 5 := by
          field_simp
      _ = c / (64 * Wr) * P ^ 5 + H₁ * (64 * H₁ / c) ^ 4 * Wr ^ 4 * δ₀ ^ 5 := by rw [e]
      _ ≤ c / (64 * Wr) * P ^ 5 + step4A H c * Wr ^ 4 * δ₀ ^ 5 := by
          gcongr
  -- Young 2: `(H₁/W)P⁴ ≤ (c/64W)P⁵ + H₁(64H₁/c)⁴/W`
  have hy2 := young_pow hP zero_le_one (by positivity : (0 : ℝ) < c / (64 * H₁)) 4 1
  have hY2 : H * (1 / Wr) * P ^ 4 ≤ c / (64 * Wr) * P ^ 5 + step4A H c / Wr := by
    simp only [one_pow, mul_one, pow_one] at hy2
    have hP4 : 0 ≤ P ^ 4 := by positivity
    calc H * (1 / Wr) * P ^ 4 ≤ H₁ / Wr * P ^ 4 := by
          rw [mul_one_div]; gcongr; linarith
      _ ≤ H₁ / Wr * (c / (64 * H₁) * P ^ (4 + 1) + ((c / (64 * H₁)) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left hy2 (by positivity)
      _ = c / (64 * Wr) * P ^ 5 + H₁ * (64 * H₁ / c) ^ 4 / Wr := by
          field_simp
      _ ≤ c / (64 * Wr) * P ^ 5 + step4A H c / Wr := by
          gcongr
  -- Young 3: `P³g² ≤ P⁵/64 + 512g⁵`
  have hy3 := young_pow hP hg (by norm_num : (0 : ℝ) < 1 / 8) 3 2
  have hY3 : c / (2 * Wr) * (P ^ 3 * g ^ 2) ≤ c / (128 * Wr) * P ^ 5 + step4A H c / Wr * g ^ 5 := by
    have e : c / (2 * Wr) * ((1 / 8 : ℝ) ^ 2 * P ^ (3 + 2) + ((1 / 8 : ℝ) ^ 3)⁻¹ * g ^ (3 + 2)) =
        c / (128 * Wr) * P ^ 5 + 256 * c / Wr * g ^ 5 := by
      field_simp; ring
    have hg5 : 0 ≤ g ^ 5 := by positivity
    calc c / (2 * Wr) * (P ^ 3 * g ^ 2) ≤ c / (2 * Wr) * ((1 / 8 : ℝ) ^ 2 * P ^ (3 + 2) +
          ((1 / 8 : ℝ) ^ 3)⁻¹ * g ^ (3 + 2)) := mul_le_mul_of_nonneg_left hy3 (by positivity)
      _ = c / (128 * Wr) * P ^ 5 + 256 * c / Wr * g ^ 5 := e
      _ ≤ c / (128 * Wr) * P ^ 5 + step4A H c / Wr * g ^ 5 := by
          gcongr
  have hsplit : H * (δ₀ + 1 / Wr) * P ^ 4 = H * δ₀ * P ^ 4 + H * (1 / Wr) * P ^ 4 := by ring
  have hc5 : c / (16 * Wr) * P ^ 5 - c / (64 * Wr) * P ^ 5 - c / (64 * Wr) * P ^ 5 -
      c / (128 * Wr) * P ^ 5 = 3 * c / 128 / Wr * P ^ 5 := by
    field_simp; ring
  linarith

end BlockBand.SourceProcess.PhysApprox.B3.FracMom
