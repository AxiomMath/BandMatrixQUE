module

public import BlockBand.Palm.RegularityScalar

/-!
# Lower bound on the root at positive height

Under the trace certificate `‖certificateChi F c E μ‖ ≤ Im μ / 2`, every root `m` of the finite
Dyson equation with `Im m > 0` at every `z` with `Im z > 0` and `|z - E| ≤ 2` satisfies
`Im m ≥ Im z · (1 + 4/(c Im μ))⁻² (2c)⁻¹` (`certificate_positive_height_lower`). The proof is direct
and uses no Stieltjes or Poisson representation.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- A bounded change in scalar spectral parameter gives a reciprocal lower
bound without a smallness assumption on that change. -/
theorem certificate_reciprocal_shift_lower {a b : ℂ} {H D : ℝ}
    (hH : 0 < H) (hD : 0 ≤ D) (ha : H ≤ ‖a‖) (hb : b ≠ 0)
    (hab : ‖b - a‖ ≤ D) :
    (1 + D / H)⁻¹ ^ 2 * Complex.normSq a⁻¹ ≤ Complex.normSq b⁻¹ := by
  have hA : 0 < ‖a‖ := hH.trans_le ha
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hf : 0 < 1 + D / H := by positivity
  have hratio : ‖b‖ ≤ (1 + D / H) * ‖a‖ := by
    have hdiff := norm_sub_norm_le b a
    have hprod := mul_le_mul_of_nonneg_left ha (div_nonneg hD hH.le)
    have hcancel : (D / H) * H = D := by field_simp [hH.ne']
    rw [hcancel] at hprod
    linarith
  have hbound : ((1 + D / H) * ‖a‖)⁻¹ ≤ ‖b‖⁻¹ := inv_anti₀ hB hratio
  rw [_root_.mul_inv_rev] at hbound
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_inv, norm_inv]
  have hinv : 0 ≤ (1 + D / H)⁻¹ * ‖a‖⁻¹ := by positivity
  have hsq : ((1 + D / H)⁻¹ * ‖a‖⁻¹) ^ 2 ≤ (‖b‖⁻¹) ^ 2 := by
    nlinarith [inv_nonneg.mpr hB.le]
  simpa only [mul_pow, mul_comm] using hsq

/-- Lower bound for the finite resolvent average after a bounded scalar shift. -/
theorem certificate_average_shift_lower
    (spectrum : ι → ℝ) {H D : ℝ} {a₀ a : ℂ}
    (hH : 0 < H) (hD : 0 ≤ D) (ha₀ : H ≤ a₀.im) (ha : 0 < a.im)
    (hshift : ‖a - a₀‖ ≤ D) :
    (1 + D / H)⁻¹ ^ 2 * certificateRealAverage
      (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) a₀)) ≤
    certificateRealAverage (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) a)) := by
  unfold certificateRealAverage
  change (1 + D / H)⁻¹ ^ 2 * (𝔼 i ∈ (Finset.univ : Finset ι), Complex.normSq (certificateScalarResolvent (spectrum i) a₀)) ≤
    (𝔼 i ∈ (Finset.univ : Finset ι), Complex.normSq (certificateScalarResolvent (spectrum i) a))
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro i _
  have hnorm : H ≤ ‖(spectrum i : ℂ) - a₀‖ := by
    have hi := Complex.abs_im_le_norm ((spectrum i : ℂ) - a₀)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
      abs_of_pos (hH.trans_le ha₀)] at hi
    exact ha₀.trans hi
  have hne : (spectrum i : ℂ) - a ≠ 0 := by
    intro heq
    have hi := congrArg Complex.im heq
    have hz : a.im = 0 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] using hi
    exact ha.ne' hz
  have hdiff : ‖((spectrum i : ℂ) - a) - ((spectrum i : ℂ) - a₀)‖ ≤ D := by
    have heq : ((spectrum i : ℂ) - a) - ((spectrum i : ℂ) - a₀) = -(a - a₀) := by ring
    rw [heq, norm_neg]
    exact hshift
  exact certificate_reciprocal_shift_lower hH hD hnorm hne hdiff

/-- The Dyson norm bound gives `s|m| ≤ 1` for `0 < s ≤ 1`. -/
theorem certificate_dyson_s_mul_norm_le_one [Nonempty ι]
    (spectrum : ι → ℝ) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hz : 0 ≤ z.im) (hmi : 0 < m.im)
    (hm : certificateDysonResidual spectrum s z m = 0) : s * ‖m‖ ≤ 1 := by
  have hsq := certificate_dyson_normSq_le spectrum hs hz hmi hm
  rw [Complex.normSq_eq_norm_sq, inv_eq_one_div, le_div_iff₀ hs] at hsq
  have hmul := mul_le_mul_of_nonneg_left hsq hs.le
  have hnonneg : 0 ≤ s * ‖m‖ := by positivity
  nlinarith

/-- The trace certificate gives `⟨|(λ - E - cμ)⁻¹|²⟩ ≥ (2c)⁻¹`. -/
theorem certificate_reference_average_lower [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E : ℝ} {μ : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) (hchi : ‖certificateChi F c E μ‖ ≤ μ.im / 2) :
    (2 * c)⁻¹ ≤ certificateRealAverage (fun i =>
      Complex.normSq (certificateScalarResolvent (hF.eigenvalues i) ((E : ℂ) + c * μ))) := by
  have hz : ((E : ℂ) + c * μ).im ≠ 0 := by simpa using (mul_pos hc hμ).ne'
  have htrace := certificateMatrixTrace_eq_average F hF hz
  have hward := certificate_average_ward hF.eigenvalues ((E : ℂ) + c * μ)
  have hchii : (certificateAverage (fun i =>
      certificateScalarResolvent (hF.eigenvalues i) ((E : ℂ) + c * μ))).im =
      μ.im + (certificateChi F c E μ).im := by
    unfold certificateChi
    rw [htrace]
    simp
  have hlo := (abs_le.mp ((Complex.abs_im_le_norm (certificateChi F c E μ)).trans hchi)).1
  rw [hchii] at hward
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    zero_mul, add_zero, zero_add] at hward
  rw [inv_eq_one_div, div_le_iff₀ (by positivity : 0 < 2 * c)]
  nlinarith

/-- Lower bound `Im m ≥ Im z · (1 + 4/(c Im μ))⁻² (2c)⁻¹` for every root `m` with `Im m > 0` of
the finite Dyson equation of `F` with parameter `0 < s ≤ 1`, at every `z` with `Im z > 0` and
`|z - E| ≤ 2`, provided `0 < c ≤ 1`, `Im μ > 0`, `|μ| ≤ 1` and
`‖certificateChi F c E μ‖ ≤ Im μ / 2`. No bound on `‖F‖` is needed. -/
theorem certificate_positive_height_lower [Nonempty ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E s : ℝ} {μ z m : ℂ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ.im) (hμnorm : ‖μ‖ ≤ 1)
    (hchi : ‖certificateChi F c E μ‖ ≤ μ.im / 2)
    (hs : 0 < s) (hs1 : s ≤ 1) (hz : 0 < z.im) (hzE : ‖z - (E : ℂ)‖ ≤ 2)
    (hmi : 0 < m.im) (hm : certificateDysonResidual hF.eigenvalues s z m = 0) :
    z.im * (1 + 4 / (c * μ.im))⁻¹ ^ 2 * (2 * c)⁻¹ ≤ m.im := by
  have hsm := certificate_dyson_s_mul_norm_le_one hF.eigenvalues hs hs1 hz.le hmi hm
  have hshift : ‖z + s * m - ((E : ℂ) + c * μ)‖ ≤ 4 := by
    have heq : z + s * m - ((E : ℂ) + c * μ) = (z - (E : ℂ)) + (s : ℂ) * m - (c : ℂ) * μ := by ring
    rw [heq]
    calc
      _ ≤ ‖z - (E : ℂ)‖ + ‖(s : ℂ) * m‖ + ‖(c : ℂ) * μ‖ := (norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖z - (E : ℂ)‖ + s * ‖m‖ + c * ‖μ‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hs, abs_of_pos hc]
      _ ≤ 4 := by nlinarith
  have hza : 0 < (z + s * m).im := by simpa using add_pos hz (mul_pos hs hmi)
  have hA := certificate_average_shift_lower hF.eigenvalues (mul_pos hc hμ)
    (by norm_num : (0 : ℝ) ≤ 4) (by simp) hza hshift
  have hA₀ := certificate_reference_average_lower F hF hc hμ hchi
  have hfac : 0 ≤ (1 + 4 / (c * μ.im))⁻¹ ^ 2 := sq_nonneg _
  have hlow := (mul_le_mul_of_nonneg_left hA₀ hfac).trans hA
  have hward := certificate_dyson_ward hF.eigenvalues s z m hm
  have hAvg0 : 0 ≤ certificateRealAverage (fun i => Complex.normSq
      (certificateScalarResolvent (hF.eigenvalues i) (z + s * m))) :=
    Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hlow hz.le
  have hother := mul_nonneg (mul_pos hs hmi).le hAvg0
  nlinarith

end BlockBand.Palm
