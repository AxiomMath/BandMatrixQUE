module

public import BlockBand.Transmission.Absorbed.ShiftMix

/-!
# The scale of the source-mixing input shift

`sqrtW_mixErr_le`: for an absorption `0 ≤ ε ≤ K/W²`, the mixing error of the shift satisfies
`√W·mixErr(ε, q) ≤ cMix(η⁻¹, K)(q + 1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LawFinite
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawForced
open BlockBand.Transmission.PathScalar BlockBand.Transmission.Generator
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The constant of `sqrtW_mixErr_le` (`L = η_L⁻¹`). -/
def cMix (L K : ℝ) : ℝ :=
  11 * K * L ^ 2 + 3 / 2 * K * L ^ 3 + (9 / 4 * K * L ^ 4 * (8 + K * L ^ 2) + 1)

theorem sqrt_mul_le_of_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) :
    Real.sqrt (a * b) ≤ (a + 1) * b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg ha (by linarith : (0 : ℝ) ≤ b - 1)]

theorem mix_t1 {ε ι L K x q : ℝ} (hε : 0 ≤ ε) (hι0 : 0 ≤ ι) (hL : ι ≤ L) (hq0 : 0 ≤ q)
    (hK : 0 ≤ K) (hεx : ε ≤ K * x ^ 2) (hs1 : ε * ι ≤ 1) :
    2 * (((2 * (ε * ι) + (ε * ι) ^ 2) * (3 / 2 * ι) + ε * ι * ι) * q) ≤
      11 * K * L ^ 2 * x ^ 2 * q := by
  have hL0 : 0 ≤ L := hι0.trans hL
  have hsι : ε * ι ≤ K * x ^ 2 * L := mul_le_mul hεx hL hι0 (by positivity)
  have h3 : 2 * (ε * ι) + (ε * ι) ^ 2 ≤ 3 * (ε * ι) := by nlinarith [mul_nonneg hε hι0]
  have a1 : (2 * (ε * ι) + (ε * ι) ^ 2) * (3 / 2 * ι) ≤ 3 * (K * x ^ 2 * L) * (3 / 2 * L) :=
    mul_le_mul (h3.trans (by linarith)) (by linarith) (by positivity) (by positivity)
  have a2 : ε * ι * ι ≤ K * x ^ 2 * L * L := mul_le_mul hsι hL hι0 (by positivity)
  have e3 : 3 * (K * x ^ 2 * L) * (3 / 2 * L) = 9 / 2 * K * L ^ 2 * x ^ 2 := by ring
  have e4 : K * x ^ 2 * L * L = K * L ^ 2 * x ^ 2 := by ring
  have b1 : (2 * (ε * ι) + (ε * ι) ^ 2) * (3 / 2 * ι) + ε * ι * ι ≤
      11 / 2 * K * L ^ 2 * x ^ 2 := by linarith
  have := mul_le_mul_of_nonneg_right b1 hq0
  linarith

theorem mix_t2 {ε Wr ι L K x : ℝ} (hι0 : 0 ≤ ι) (hL : ι ≤ L) (hK : 0 ≤ K) (hx0 : 0 ≤ x)
    (hεW : ε * Wr ≤ K * x) :
    ε * Wr * (ι ^ 2 * (3 / 2 * ι)) ≤ 3 / 2 * K * L ^ 3 * x := by
  have h : ι ^ 2 * (3 / 2 * ι) ≤ L ^ 2 * (3 / 2 * L) :=
    mul_le_mul (pow_le_pow_left₀ hι0 hL 2) (by linarith) (by positivity)
      (by have := hι0.trans hL; positivity)
  have := mul_le_mul hεW h (by positivity) (by positivity)
  have e5 : K * x * (L ^ 2 * (3 / 2 * L)) = 3 / 2 * K * L ^ 3 * x := by ring
  linarith

theorem mix_t3 {ε Wr ι L K x q : ℝ} (hε : 0 ≤ ε) (hι0 : 0 ≤ ι) (hL : ι ≤ L) (hK : 0 ≤ K)
    (hq0 : 0 ≤ q) (hW0 : 0 ≤ Wr) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hεx : ε ≤ K * x ^ 2) (hεW : ε * Wr ≤ K * x)
    (hs1 : ε * ι ≤ 1) (hWx : Wr * x ^ 2 ≤ 1) :
    Real.sqrt Wr * Real.sqrt ((3 / 2 * ι) ^ 2 * (ε * ι ^ 2) *
      (2 * ((1 + ε * ι) ^ 2 * q) + ε * (Wr * ι ^ 2))) ≤
      (9 / 4 * K * L ^ 4 * (8 + K * L ^ 2) + 1) * (q + 1) := by
  have hL0 : 0 ≤ L := hι0.trans hL
  rw [← Real.sqrt_mul hW0]
  refine (Real.sqrt_le_sqrt ?_).trans (sqrt_mul_le_of_one_le (by positivity) (by linarith))
  have k1 : (3 / 2 * ι) ^ 2 ≤ 9 / 4 * L ^ 2 := by
    have := pow_le_pow_left₀ hι0 hL 2; nlinarith
  have k2 : ε * ι ^ 2 ≤ K * x ^ 2 * L ^ 2 :=
    mul_le_mul hεx (pow_le_pow_left₀ hι0 hL 2) (sq_nonneg _) (by positivity)
  have h2 : ε * (Wr * ι ^ 2) ≤ K * L ^ 2 := by
    have := mul_le_mul hεW (pow_le_pow_left₀ hι0 hL 2) (sq_nonneg _) (by positivity)
    have e6 : ε * (Wr * ι ^ 2) = ε * Wr * ι ^ 2 := by ring
    have h7 : K * x * L ^ 2 ≤ K * L ^ 2 := by
      have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ K * L ^ 2)
      have e : K * L ^ 2 * x = K * x * L ^ 2 := by ring
      linarith
    linarith
  have h1 : (1 + ε * ι) ^ 2 ≤ 4 := by nlinarith [mul_nonneg hε hι0]
  have k3 : 2 * ((1 + ε * ι) ^ 2 * q) + ε * (Wr * ι ^ 2) ≤ (8 + K * L ^ 2) * (q + 1) := by
    have := mul_le_mul_of_nonneg_right h1 hq0
    nlinarith [mul_nonneg hK (sq_nonneg L)]
  have hI0 : 0 ≤ 2 * ((1 + ε * ι) ^ 2 * q) + ε * (Wr * ι ^ 2) := by positivity
  have k4 := mul_le_mul (mul_le_mul k1 k2 (by positivity) (by positivity)) k3 hI0
    (by positivity)
  have k5 := mul_le_mul_of_nonneg_left k4 hW0
  have e8 : Wr * (9 / 4 * L ^ 2 * (K * x ^ 2 * L ^ 2) * ((8 + K * L ^ 2) * (q + 1))) =
      9 / 4 * K * L ^ 4 * (8 + K * L ^ 2) * (q + 1) * (Wr * x ^ 2) := by ring
  rw [e8] at k5
  have k6 : 9 / 4 * K * L ^ 4 * (8 + K * L ^ 2) * (q + 1) * (Wr * x ^ 2) ≤
      9 / 4 * K * L ^ 4 * (8 + K * L ^ 2) * (q + 1) :=
    mul_le_of_le_one_right (by positivity) hWx
  linarith

/-- **`√W·mixErr ≤ cMix·(q + 1)`.** -/
theorem sqrtW_mixErr_le {b E L K ε q : ℝ} (hη : 0 < etaZ b E) (hL : (etaZ b E)⁻¹ ≤ L)
    (hK : 0 ≤ K) (hW1 : 1 ≤ W) (hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2)
    (hs1 : ε / etaZ b E ≤ 1) (hq0 : 0 ≤ q) :
    Real.sqrt W * mixErr b E ε q W ≤ cMix L K * (q + 1) := by
  have hι0 : 0 ≤ (etaZ b E)⁻¹ := by positivity
  have hL0 : 0 ≤ L := hι0.trans hL
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hx0 : 0 < (W : ℝ)⁻¹ := by positivity
  have hx1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWr
  have hxW : (W : ℝ)⁻¹ * W = 1 := inv_mul_cancel₀ hW0.ne'
  have hsW : Real.sqrt W ≤ W := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsq0 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
  have hsq : Real.sqrt W * (W : ℝ)⁻¹ ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hsW hx0.le; linarith
  have hxx : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ := by
    calc (W : ℝ)⁻¹ ^ 2 = (W : ℝ)⁻¹ * (W : ℝ)⁻¹ := sq _
      _ ≤ 1 * (W : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hx1 hx0.le
      _ = (W : ℝ)⁻¹ := one_mul _
  have hsx2 : Real.sqrt W * (W : ℝ)⁻¹ ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hxx hsq0).trans hsq
  have hεx : ε ≤ K * (W : ℝ)⁻¹ ^ 2 := hεK.trans_eq (by rw [inv_pow, div_eq_mul_inv])
  have hεW : ε * W ≤ K * (W : ℝ)⁻¹ := by
    have := mul_le_mul_of_nonneg_right hεx hW0.le
    have e : K * (W : ℝ)⁻¹ ^ 2 * W = K * (W : ℝ)⁻¹ * ((W : ℝ)⁻¹ * W) := by ring
    rw [e, hxW, mul_one] at this; exact this
  have hWx : (W : ℝ) * (W : ℝ)⁻¹ ^ 2 ≤ 1 := by
    have e7 : (W : ℝ) * (W : ℝ)⁻¹ ^ 2 = (W : ℝ)⁻¹ * ((W : ℝ)⁻¹ * W) := by ring
    rw [e7, hxW, mul_one]; exact hx1
  have e1 : ∀ y : ℝ, y / etaZ b E = y * (etaZ b E)⁻¹ := fun y => div_eq_mul_inv _ _
  have e2 : 3 / (2 * etaZ b E) = 3 / 2 * (etaZ b E)⁻¹ := by field_simp
  rw [e1] at hs1
  unfold mixErr
  rw [e1 ε, e1 (ε * (etaZ b E)⁻¹), e2]
  have t1 := mix_t1 hε hι0 hL hq0 hK hεx hs1
  have t2 := mix_t2 hι0 hL hK hx0.le hεW
  have t3 := mix_t3 hε hι0 hL hK hq0 hW0.le hx0.le hx1 hεx hεW hs1 hWx
  rw [mul_add, mul_add]
  have u1 := mul_le_mul_of_nonneg_left t1 hsq0
  have u2 := mul_le_mul_of_nonneg_left t2 hsq0
  have v1 : Real.sqrt W * (11 * K * L ^ 2 * (W : ℝ)⁻¹ ^ 2 * q) ≤ 11 * K * L ^ 2 * q := by
    have e9 : Real.sqrt W * (11 * K * L ^ 2 * (W : ℝ)⁻¹ ^ 2 * q) = 11 * K * L ^ 2 * q *
      (Real.sqrt W * (W : ℝ)⁻¹ ^ 2) := by ring
    rw [e9]; exact mul_le_of_le_one_right (by positivity) hsx2
  have v2 : Real.sqrt W * (3 / 2 * K * L ^ 3 * (W : ℝ)⁻¹) ≤ 3 / 2 * K * L ^ 3 := by
    have e10 : Real.sqrt W * (3 / 2 * K * L ^ 3 * (W : ℝ)⁻¹) = 3 / 2 * K * L ^ 3 *
      (Real.sqrt W * (W : ℝ)⁻¹) := by ring
    rw [e10]; exact mul_le_of_le_one_right (by positivity) hsq
  have hk1 : 0 ≤ 11 * K * L ^ 2 := by positivity
  have hk2 : 0 ≤ 3 / 2 * K * L ^ 3 := by positivity
  have w1 : 11 * K * L ^ 2 * q ≤ 11 * K * L ^ 2 * (q + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hk1
  have w2 : 3 / 2 * K * L ^ 3 ≤ 3 / 2 * K * L ^ 3 * (q + 1) :=
    le_mul_of_one_le_right hk2 (by linarith)
  unfold cMix
  have e11 : (11 * K * L ^ 2 + 3 / 2 * K * L ^ 3 + (9 / 4 * K * L ^ 4 * (8 + K * L ^ 2) + 1)) *
      (q + 1) = 11 * K * L ^ 2 * (q + 1) + 3 / 2 * K * L ^ 3 * (q + 1) +
        (9 / 4 * K * L ^ 4 * (8 + K * L ^ 2) + 1) * (q + 1) := by ring
  rw [e11]
  linarith

end BlockBand.Transmission.Absorbed
