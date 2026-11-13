module

public import BlockBand.Transmission.PathScalar.MeanScalar
public import BlockBand.Transmission.PathScalar.OneStep

/-!
# Bulk scalars of the matched point, uniformly on `bulkInterval κ`

`a = matchedA E`, `z = z_∂(E) = a⁻¹ + ba`, `η = Im z`, `c = 1-2b`, `d_* = 1/(1-b)`:
`|a| = 1`, `η ≤ 1`, `|z| ≤ 2`, `-Im a = η d_*`, `z = -E - ca - ba`, `a(z - ba) = 1`, and the
uniform contraction gap `|k₋| d_* ≤ 1 - b - kGap b κ` with `kGap b κ > 0` (`k₋ = c + b²a²`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open scoped ComplexConjugate

/-- The uniform gap of the outgoing coefficient on `bulkInterval κ`. -/
def kGap (b κ : ℝ) : ℝ :=
  (1 - b) - dStar b * Real.sqrt ((1 - b) ^ 4 - 4 * (1 - 2 * b) * b ^ 2 * (min κ 2 / 2))

section Bulk

variable {b κ E : ℝ}

theorem bulk_norm_a (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : ‖matchedA E‖ = 1 :=
  norm_matchedA E (bulk_bounds hκ hE).1 (bulk_bounds hκ hE).2

theorem bulk_eta_le_one (hb0 : 0 < b) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    etaZ b E ≤ 1 := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  rw [etaZ_eq b E h1 h2, matchedA_im]
  have hs : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have := Real.sqrt_nonneg (4 - E ^ 2)
  nlinarith

theorem bulk_norm_z (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖boundaryZ b E‖ ≤ 2 := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have ha := bulk_norm_a hκ hE
  rw [boundaryZ]
  calc ‖(matchedA E)⁻¹ + (b : ℂ) * matchedA E‖ ≤ ‖(matchedA E)⁻¹‖ + ‖(b : ℂ) * matchedA E‖ :=
        norm_add_le _ _
    _ = 1 + b := by
        rw [norm_inv, ha, norm_mul, ha, Complex.norm_real, Real.norm_of_nonneg hb0.le]; simp
    _ ≤ 2 := by linarith

theorem bulk_im_a (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    -(matchedA E).im = etaZ b E * dStar b := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  rw [etaZ_eq b E h1 h2, dStar]
  have : (1 - b) ≠ 0 := by linarith
  field_simp

theorem bulk_z_eq (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : boundaryZ b E =
    -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  rw [boundaryZ, matchedA_inv E h1 h2]
  apply Complex.ext <;> simp [matchedA] <;> ring

theorem bulk_a_mul (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    matchedA E * (boundaryZ b E - (b : ℂ) * matchedA E) = 1 := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  rw [boundaryZ, add_sub_cancel_right]
  exact mul_inv_cancel₀ (matchedA_ne_zero E h1 h2)

theorem kGap_pos (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) : 0 < kGap b κ := by
  have h1b : 0 < 1 - b := by linarith
  have hm : 0 < min κ 2 := lt_min hκ (by norm_num)
  have hc : 0 < 1 - 2 * b := by linarith
  have hlt : Real.sqrt ((1 - b) ^ 4 - 4 * (1 - 2 * b) * b ^ 2 * (min κ 2 / 2)) < (1 - b) ^ 2 := by
    rw [Real.sqrt_lt' (by positivity)]
    have : 0 < 4 * (1 - 2 * b) * b ^ 2 * (min κ 2 / 2) := by positivity
    nlinarith
  rw [kGap, dStar]
  have : 1 / (1 - b) * Real.sqrt ((1 - b) ^ 4 - 4 * (1 - 2 * b) * b ^ 2 * (min κ 2 / 2)) <
      1 / (1 - b) * (1 - b) ^ 2 := by gcongr
  have e : 1 / (1 - b) * (1 - b) ^ 2 = 1 - b := by field_simp
  linarith

theorem bulk_kMinus (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖kMinus b E‖ * dStar b ≤ 1 - b - kGap b κ := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hE1 : -2 + κ ≤ E := hE.1
  have hE2 : E ≤ 2 - κ := hE.2
  have hm1 : min κ 2 ≤ κ := min_le_left _ _
  have hm2 : min κ 2 ≤ 2 := min_le_right _ _
  have hm0 : 0 < min κ 2 := lt_min hκ (by norm_num)
  have hy2 : min κ 2 / 2 ≤ (matchedA E).im ^ 2 := by
    rw [matchedA_im, div_pow, neg_sq, Real.sq_sqrt (by nlinarith)]; nlinarith
  have hc : 0 ≤ 1 - 2 * b := by linarith
  have hsq : ‖kMinus b E‖ ≤ Real.sqrt ((1 - b) ^ 4 - 4 * (1 - 2 * b) * b ^ 2 * (min κ 2 / 2)) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Complex.normSq_eq_norm_sq, normSq_kMinus b E h1 h2]
    have : 4 * (1 - 2 * b) * b ^ 2 * (min κ 2 / 2) ≤ 4 * (1 - 2 * b) * b ^ 2 * (matchedA E).im ^ 2 :=
      by gcongr
    nlinarith
  have hd : 0 ≤ dStar b := by rw [dStar]; exact div_nonneg zero_le_one (by linarith)
  rw [kGap]
  have := mul_le_mul_of_nonneg_right hsq hd
  linarith

end Bulk

/-- **The exact algebra of one mean step** (see `MeanStage1`). -/
theorem mean_identity {a z v u w fζ fz T : ℂ} {b c E : ℂ} (hw1 : w * (z - b * v) = 1)
    (ha : a * (z - b * a) = 1) (hz : z = -E - c * a - b * a)
    (hres : fζ - fz = -((-E - c * v - b * u) - z) * T) :
    (v - a) * (1 - (c + b ^ 2 * a * w) * T) =
        (fz - a) + (v - fζ) + b * T * (u * (z - b * v) - 1) * w ∧
      u - a = b * a * w * (v - a) + (u * (z - b * v) - 1) * w := by
  have hwa : w - a = b * a * w * (v - a) := by linear_combination (-w) * ha + a * hw1
  have hu : u - a = b * a * w * (v - a) + (u * (z - b * v) - 1) * w := by
    linear_combination (-u) * hw1 + hwa
  exact ⟨by linear_combination hres + T * hz + T * b * hu, hu⟩

theorem neg_im_of_mul_eq_one {w q : ℂ} (h : w * q = 1) : -w.im = q.im * ‖w‖ ^ 2 := by
  have hq : q ≠ 0 := by rintro rfl; simp at h
  have hw : w = q⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [hw, Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
  have : Complex.normSq q ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  field_simp

end BlockBand.Transmission.PathScalar
