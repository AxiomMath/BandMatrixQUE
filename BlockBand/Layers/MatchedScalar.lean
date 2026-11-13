module

public import BlockBand.Internal.Contracts.Layers

/-!
# Matched scalar parameters and the scalar strict contraction

Elementary scalar facts about the matched value `a = matchedA E = (-E - i√(4-E²))/2`, the
separate-port and common-port spectral parameters `z_∂ = boundaryZ b E = a⁻¹ + b a` and
`z₀ = commonZ b E = a⁻¹ + 2b a`, and the scalar part of the strict contraction bound (in the proof
of the layer-contraction lemma): `|c + b²a²| < (1-b)²` and `q₀(E) ≤ q < 1` uniformly on the bulk
interval, with `c = 1 - 2b`.

The final theorem `strictContraction_scalar` has exactly the type of the field
`StrictContractionContract.scalar` of `BlockBand.Internal.Contracts.Layers`.

Normalization: energies `E : ℝ`; the semicircle edge is at `±2`; the bulk interval is
`bulkInterval κ = [-2+κ, 2-κ]`; norms of complex numbers are the modulus. No measure is
involved; every statement is deterministic and pointwise in `E`, with the uniform bounds on
`bulkInterval κ` depending only on `b` and `κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts.Layers
open scoped ComplexConjugate

/-!
## Components of the matched value
-/

/-- Real part of the matched value `a = (-E - i√(4-E²))/2` (the matched parameters);
every real `E`. -/
@[simp] theorem matchedA_re (E : ℝ) : (matchedA E).re = -E / 2 := rfl

/-- Imaginary part of the matched value `a = (-E - i√(4-E²))/2` (the matched
parameters); every real `E` (`Real.sqrt` is `0` on negatives). -/
@[simp] theorem matchedA_im (E : ℝ) : (matchedA E).im = -Real.sqrt (4 - E ^ 2) / 2 := rfl

/-- `|E| ≤ 2` gives `E² ≤ 4` (domain of the matched parameters). -/
theorem sq_le_four_of_abs_le_two {E : ℝ} (h : |E| ≤ 2) : E ^ 2 ≤ 4 := by
  have h' := abs_le.mp h
  nlinarith [h'.1, h'.2]

/-- `√(4-E²)² = 4-E²` for `|E| ≤ 2` (the matched parameters). -/
theorem sqrt_four_sub_sq_sq {E : ℝ} (h : |E| ≤ 2) :
    Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 :=
  Real.sq_sqrt (by linarith [sq_le_four_of_abs_le_two h])

/-!
## 1. Modulus one, inverse, and the quadratic equation (`|E| ≤ 2`)
-/

/-- `|a|² = 1` for `|E| ≤ 2` (the matched parameters). -/
theorem normSq_matchedA {E : ℝ} (h : |E| ≤ 2) : Complex.normSq (matchedA E) = 1 := by
  have hs := sqrt_four_sub_sq_sq h
  rw [Complex.normSq_apply, matchedA_re, matchedA_im]
  linear_combination (1 / 4 : ℝ) * hs

/-- `|a| = 1` for `|E| ≤ 2` (the matched parameters). -/
theorem norm_matchedA {E : ℝ} (h : |E| ≤ 2) : ‖matchedA E‖ = 1 := by
  have h2 : ‖matchedA E‖ ^ 2 = 1 := by rw [Complex.sq_norm, normSq_matchedA h]
  have h0 := norm_nonneg (matchedA E)
  nlinarith [h0, h2]

/-- `a⁻¹ = ā` for `|E| ≤ 2` (the matched parameters). -/
theorem inv_matchedA {E : ℝ} (h : |E| ≤ 2) : (matchedA E)⁻¹ = conj (matchedA E) := by
  rw [Complex.inv_def, normSq_matchedA h]
  simp

/-- `a + a⁻¹ = -E` for `|E| ≤ 2` (the matched parameters). -/
theorem matchedA_add_inv {E : ℝ} (h : |E| ≤ 2) : matchedA E + (matchedA E)⁻¹ = -(E : ℂ) := by
  rw [inv_matchedA h]
  apply Complex.ext <;> simp

/-- `a² + E a + 1 = 0` for `|E| ≤ 2` (the matched parameters). -/
theorem matchedA_quadratic {E : ℝ} (h : |E| ≤ 2) :
    matchedA E ^ 2 + (E : ℂ) * matchedA E + 1 = 0 := by
  have hs : Real.sqrt (4 - E * E) ^ 2 = 4 - E * E := by
    rw [← pow_two]; exact sqrt_four_sub_sq_sq h
  apply Complex.ext
  · simp [pow_two]
    linear_combination (-1 / 4 : ℝ) * hs
  · simp [pow_two]
    ring

/-- `a² = (E²/2 - 1) + i E√(4-E²)/2` for `|E| ≤ 2` (the matched parameters). -/
theorem matchedA_sq {E : ℝ} (h : |E| ≤ 2) :
    matchedA E ^ 2 = ⟨E ^ 2 / 2 - 1, E * Real.sqrt (4 - E ^ 2) / 2⟩ := by
  have hs : Real.sqrt (4 - E * E) ^ 2 = 4 - E * E := by
    rw [← pow_two]; exact sqrt_four_sub_sq_sq h
  apply Complex.ext
  · simp [pow_two]
    linear_combination (-1 / 4 : ℝ) * hs
  · simp [pow_two]
    ring

/-!
## 2. The sign of `Im a` and its uniform bulk bound
-/

/-- `Im a < 0` for `|E| < 2` (the matched parameters). -/
theorem matchedA_im_neg {E : ℝ} (h : |E| < 2) : (matchedA E).im < 0 := by
  have h' := abs_lt.mp h
  have hpos : 0 < 4 - E ^ 2 := by nlinarith [h'.1, h'.2]
  have := Real.sqrt_pos.mpr hpos
  rw [matchedA_im]
  linarith

/-- Points of `bulkInterval κ` satisfy `|E| ≤ 2 - κ` (in particular the interval is empty
unless `κ ≤ 2`). -/
theorem abs_le_of_mem_bulkInterval {κ E : ℝ} (hE : E ∈ bulkInterval κ) : |E| ≤ 2 - κ :=
  abs_le.mpr ⟨by linarith [hE.1], hE.2⟩

/-- Points of `bulkInterval κ` satisfy `E² ≤ (2-κ)²`. -/
theorem sq_le_of_mem_bulkInterval {κ E : ℝ} (hE : E ∈ bulkInterval κ) :
    E ^ 2 ≤ (2 - κ) ^ 2 := by
  have h1 := hE.1
  have h2 := hE.2
  nlinarith

/-- Points of `bulkInterval κ` with `0 < κ` satisfy `|E| < 2`. -/
theorem abs_lt_two_of_mem_bulkInterval {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    |E| < 2 := by
  have := abs_le_of_mem_bulkInterval hE
  linarith

/-- `0 < 4 - (2-κ)² = κ(4-κ)` for `0 < κ < 4`. -/
theorem four_sub_sq_pos {κ : ℝ} (h0 : 0 < κ) (h4 : κ < 4) : 0 < 4 - (2 - κ) ^ 2 := by
  nlinarith

/-- Uniform bulk bound `Im a ≤ -√(4-(2-κ)²)/2` on `bulkInterval κ` (the matched parameters).
This is a strictly negative bound when `0 < κ < 4`
(`four_sub_sq_pos`). -/
theorem matchedA_im_le_of_mem_bulkInterval {κ E : ℝ} (hE : E ∈ bulkInterval κ) :
    (matchedA E).im ≤ -Real.sqrt (4 - (2 - κ) ^ 2) / 2 := by
  have hsq := sq_le_of_mem_bulkInterval hE
  have := Real.sqrt_le_sqrt (show 4 - (2 - κ) ^ 2 ≤ 4 - E ^ 2 by linarith)
  rw [matchedA_im]
  linarith

/-- The uniform bulk bound on `Im a` is strictly negative for `0 < κ < 4`. -/
theorem neg_sqrt_bulk_neg {κ : ℝ} (h0 : 0 < κ) (h4 : κ < 4) :
    -Real.sqrt (4 - (2 - κ) ^ 2) / 2 < 0 := by
  have := Real.sqrt_pos.mpr (four_sub_sq_pos h0 h4)
  linarith

/-!
## 3. The spectral parameters `z_∂` and `z₀`
-/

/-- `z_∂ = a⁻¹ + b a = -E - (1-b) a` for `|E| ≤ 2`, every real `b`
(the matched parameters). -/
theorem boundaryZ_eq {b E : ℝ} (h : |E| ≤ 2) :
    boundaryZ b E = -(E : ℂ) - (1 - (b : ℂ)) * matchedA E := by
  have := matchedA_add_inv h
  unfold boundaryZ
  linear_combination this

/-- `z₀ = a⁻¹ + 2b a = -E - (1-2b) a` for `|E| ≤ 2`, every real `b`
(the matched parameters). -/
theorem commonZ_eq {b E : ℝ} (h : |E| ≤ 2) :
    commonZ b E = -(E : ℂ) - (1 - 2 * (b : ℂ)) * matchedA E := by
  have := matchedA_add_inv h
  unfold commonZ
  linear_combination this

/-- `Im z_∂ = -(1-b) Im a` for `|E| ≤ 2`, every real `b` (the matched parameters). -/
theorem boundaryZ_im {b E : ℝ} (h : |E| ≤ 2) :
    (boundaryZ b E).im = -(1 - b) * (matchedA E).im := by
  rw [boundaryZ_eq h]
  simp
  ring

/-- `Im z₀ = -(1-2b) Im a` for `|E| ≤ 2`, every real `b` (the matched parameters). -/
theorem commonZ_im {b E : ℝ} (h : |E| ≤ 2) :
    (commonZ b E).im = -(1 - 2 * b) * (matchedA E).im := by
  rw [commonZ_eq h]
  simp
  ring

/-- Uniform lower bound `Im z_∂ ≥ (1-b)√(4-(2-κ)²)/2` on `bulkInterval κ`, for `b ≤ 1`
(the matched parameters). -/
theorem boundaryZ_im_ge_of_mem_bulkInterval {b κ E : ℝ} (hb : b ≤ 1) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (boundaryZ b E).im := by
  rw [boundaryZ_im (abs_lt_two_of_mem_bulkInterval hκ hE).le]
  have := matchedA_im_le_of_mem_bulkInterval hE
  have hb' : 0 ≤ 1 - b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hb']

/-- Uniform lower bound `Im z₀ ≥ (1-2b)√(4-(2-κ)²)/2` on `bulkInterval κ`, for `b ≤ 1/2`
(the matched parameters). -/
theorem commonZ_im_ge_of_mem_bulkInterval {b κ E : ℝ} (hb : b ≤ 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (commonZ b E).im := by
  rw [commonZ_im (abs_lt_two_of_mem_bulkInterval hκ hE).le]
  have := matchedA_im_le_of_mem_bulkInterval hE
  have hb' : 0 ≤ 1 - 2 * b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hb']

/-- `Im z_∂ > 0` on `bulkInterval κ` (`0 < κ`, `b < 1`), with the uniform bound
`(1-b)√(4-(2-κ)²)/2 > 0` (the matched parameters). -/
theorem boundaryZ_im_pos_of_mem_bulkInterval {b κ E : ℝ} (hb : b < 1) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    0 < (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ∧
      (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (boundaryZ b E).im := by
  have hκ2 : κ ≤ 2 := by linarith [hE.1, hE.2]
  have hs := Real.sqrt_pos.mpr (four_sub_sq_pos hκ (by linarith))
  have hb' : 0 < 1 - b := by linarith
  exact ⟨by positivity, boundaryZ_im_ge_of_mem_bulkInterval hb.le hκ hE⟩

/-- `Im z₀ > 0` on `bulkInterval κ` (`0 < κ`, `b < 1/2`), with the uniform bound
`(1-2b)√(4-(2-κ)²)/2 > 0` (the matched parameters). -/
theorem commonZ_im_pos_of_mem_bulkInterval {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    0 < (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ∧
      (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (commonZ b E).im := by
  have hκ2 : κ ≤ 2 := by linarith [hE.1, hE.2]
  have hs := Real.sqrt_pos.mpr (four_sub_sq_pos hκ (by linarith))
  have hb' : 0 < 1 - 2 * b := by linarith
  exact ⟨by positivity, commonZ_im_ge_of_mem_bulkInterval hb.le hκ hE⟩

/-- `|z_∂| ≤ 3` for `|E| ≤ 2` and `0 ≤ b ≤ 1` (the matched parameters). -/
theorem norm_boundaryZ_le {b E : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h : |E| ≤ 2) :
    ‖boundaryZ b E‖ ≤ 3 := by
  rw [boundaryZ_eq h]
  have h1 : ‖(1 - (b : ℂ))‖ ≤ 1 := by
    rw [show (1 - (b : ℂ)) = ((1 - b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc ‖-(E : ℂ) - (1 - (b : ℂ)) * matchedA E‖
      ≤ ‖-(E : ℂ)‖ + ‖(1 - (b : ℂ)) * matchedA E‖ := norm_sub_le _ _
    _ = |E| + ‖(1 - (b : ℂ))‖ := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_matchedA h, mul_one]
    _ ≤ 3 := by linarith

/-- `|z₀| ≤ 3` for `|E| ≤ 2` and `0 ≤ b ≤ 1` (the matched parameters). -/
theorem norm_commonZ_le {b E : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h : |E| ≤ 2) :
    ‖commonZ b E‖ ≤ 3 := by
  rw [commonZ_eq h]
  have h1 : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
    rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc ‖-(E : ℂ) - (1 - 2 * (b : ℂ)) * matchedA E‖
      ≤ ‖-(E : ℂ)‖ + ‖(1 - 2 * (b : ℂ)) * matchedA E‖ := norm_sub_le _ _
    _ = |E| + ‖(1 - 2 * (b : ℂ))‖ := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_matchedA h, mul_one]
    _ ≤ 3 := by linarith

/-!
## 4. The scalar strict contraction (the strict contraction bound)
-/

/-- The exact modulus identity `|c + b²a²|² = (1-b)⁴ - 4 c b² (1 - E²/4)`, `c = 1 - 2b`,
for `|E| ≤ 2` and every real `b` (the strict contraction bound). -/
theorem norm_sq_contraction {b E : ℝ} (h : |E| ≤ 2) :
    ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ^ 2 =
      (1 - b) ^ 4 - 4 * (1 - 2 * b) * b ^ 2 * (1 - E ^ 2 / 4) := by
  have hs : Real.sqrt (4 - E * E) ^ 2 = 4 - E * E := by
    rw [← pow_two]; exact sqrt_four_sub_sq_sq h
  rw [Complex.sq_norm, matchedA_sq h, Complex.normSq_apply]
  simp [pow_two]
  linear_combination (b ^ 4 * E ^ 2 / 4) * hs

/-- On `bulkInterval κ` with `0 ≤ κ` and `b ≤ 1/2` (so `c b² ≥ 0`):
`|c + b²a²|² ≤ (1-b)⁴ - 2 c b² κ` (the strict contraction bound). -/
theorem norm_sq_contraction_le_of_mem_bulkInterval {b κ E : ℝ} (hb : b ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hE : E ∈ bulkInterval κ) :
    ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ^ 2 ≤
      (1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ := by
  have hκ2 : κ ≤ 2 := by linarith [hE.1, hE.2]
  have habs : |E| ≤ 2 := by linarith [abs_le_of_mem_bulkInterval hE, hE.1, hE.2]
  rw [norm_sq_contraction habs]
  have hsq := sq_le_of_mem_bulkInterval hE
  have hE2 : 2 * κ ≤ 4 - E ^ 2 := by nlinarith [mul_nonneg hκ (show 0 ≤ 2 - κ by linarith)]
  have hc : 0 ≤ (1 - 2 * b) * b ^ 2 := mul_nonneg (by linarith) (sq_nonneg b)
  nlinarith [mul_le_mul_of_nonneg_left hE2 hc]

/-- The explicit uniform modulus bound `r(b,κ) = √((1-b)⁴ - 2(1-2b)b²κ)` satisfies
`r < (1-b)²` for `0 < b < 1/2`, `0 < κ` (the strict contraction bound). -/
theorem contractionRadius_lt {b κ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) :
    Real.sqrt ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ) < (1 - b) ^ 2 := by
  have hpos : 0 < (1 - b) ^ 2 := by nlinarith
  rw [Real.sqrt_lt' hpos]
  have : 0 < 2 * (1 - 2 * b) * b ^ 2 * κ := by
    have : 0 < 1 - 2 * b := by linarith
    positivity
  nlinarith

/-- On `bulkInterval κ` (`0 ≤ κ`, `b ≤ 1/2`): `|c + b²a²| ≤ √((1-b)⁴ - 2(1-2b)b²κ)`
(the strict contraction bound). -/
theorem norm_contraction_le_of_mem_bulkInterval {b κ E : ℝ} (hb : b ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hE : E ∈ bulkInterval κ) :
    ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ≤
      Real.sqrt ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ) := by
  have := Real.abs_le_sqrt (norm_sq_contraction_le_of_mem_bulkInterval hb hκ hE)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- **Scalar strict contraction** (the strict contraction bound, proof of
the layer-contraction lemma), the field `StrictContractionContract.scalar`. For `0 < b < 1/2`,
`κ > 0`, `c = 1 - 2b`, `a = matchedA E`: uniformly on `bulkInterval κ = [-2+κ, 2-κ]`,
`|c + b²a²| < (1-b)²` and `q₀(E) = b(1-b)/(1 - b - |c + b²a²|) ≤ q < 1` with the explicit
`q = b(1-b)/(1 - b - √((1-b)⁴ - 2(1-2b)b²κ))`. When `κ > 2` the interval is empty and the
uniform clause is vacuous. -/
theorem strictContraction_scalar : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ q : ℝ, q < 1 ∧
    ∀ E ∈ bulkInterval κ,
      ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ < (1 - b) ^ 2 ∧
        outgoingCoefficient b E ≤ q := by
  intro b hb0 hb1 κ hκ
  have hr := contractionRadius_lt hb0 hb1 hκ
  set r := Real.sqrt ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ) with hr_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hden : 0 < 1 - b - r := by nlinarith
  refine ⟨b * (1 - b) / (1 - b - r), ?_, ?_⟩
  · rw [div_lt_one hden]
    nlinarith
  · intro E hE
    have hw := norm_contraction_le_of_mem_bulkInterval hb1.le hκ.le hE
    refine ⟨lt_of_le_of_lt hw hr, ?_⟩
    unfold outgoingCoefficient
    exact div_le_div_of_nonneg_left (mul_nonneg hb0.le (by linarith)) hden (by linarith)

/-- `strictContraction_scalar` has exactly the type of `StrictContractionContract.scalar`. -/
example (h : StrictContractionContract) : h.scalar = strictContraction_scalar := rfl

end BlockBand.Layers
