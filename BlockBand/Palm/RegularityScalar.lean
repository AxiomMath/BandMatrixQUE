module

public import BlockBand.Palm.RegularityTrace
public import Mathlib.Analysis.RCLike.Basic

/-!
# Finite Dyson identities and uniqueness of the root

Ward identities, the bound `|m|² ≤ 1/s`, and uniqueness of the root with positive imaginary part
of the finite scalar Dyson equation `m = ⟨(λ - z - s m)⁻¹⟩` at positive height.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Triangle inequality for the spectral average. -/
theorem certificateAverage_norm_le (f : ι → ℂ) :
    ‖certificateAverage f‖ ≤ certificateRealAverage (fun i => ‖f i‖) :=
  RCLike.norm_expect_le (K := ℂ)

/-- Complex finite Jensen, with no dimension factor. -/
theorem certificateAverage_normSq_le [Nonempty ι] (f : ι → ℂ) :
    Complex.normSq (certificateAverage f) ≤
      certificateRealAverage (fun i => Complex.normSq (f i)) := by
  rw [Complex.normSq_apply, certificateAverage_re, certificateAverage_im]
  have hr := certificate_jensen (fun i => (f i).re)
  have hi := certificate_jensen (fun i => (f i).im)
  have hh : certificateRealAverage (fun i => Complex.normSq (f i)) =
      certificateRealAverage (fun i => (f i).re ^ 2) +
      certificateRealAverage (fun i => (f i).im ^ 2) := by
    simp only [Complex.normSq_apply, ← pow_two, certificateRealAverage,
      Finset.expect_add_distrib]
  rw [hh]
  nlinarith

/-- Finite Cauchy–Schwarz for the complex cross-resolvent mean. -/
theorem certificateAverage_mul_normSq_le [Nonempty ι] (f g : ι → ℂ) :
    ‖certificateAverage (fun i => f i * g i)‖ ^ 2 ≤
      certificateRealAverage (fun i => Complex.normSq (f i)) *
        certificateRealAverage (fun i => Complex.normSq (g i)) := by
  have h := certificateAverage_norm_le (fun i => f i * g i)
  simp only [norm_mul] at h
  have h0 : 0 ≤ certificateRealAverage (fun i => ‖f i‖ * ‖g i‖) := by
    apply Finset.expect_nonneg
    intro i _
    positivity
  have hs := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => ‖f i‖) (fun i => ‖g i‖)
  simp only [← Complex.normSq_eq_norm_sq] at hs
  exact (by nlinarith [norm_nonneg (certificateAverage (fun i => f i * g i))] :
    ‖certificateAverage (fun i => f i * g i)‖ ^ 2 ≤
      certificateRealAverage (fun i => ‖f i‖ * ‖g i‖) ^ 2).trans hs

/-- The zero-residual condition is exactly the reciprocal Dyson equation. -/
theorem certificateDysonResidual_eq_zero_iff (spectrum : ι → ℝ)
    (s : ℝ) (z m : ℂ) :
    certificateDysonResidual spectrum s z m = 0 ↔
      m = certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * m)) := by
  exact sub_eq_zero

/-- Ward identity for the Dyson equation. -/
theorem certificate_dyson_ward (spectrum : ι → ℝ) (s : ℝ) (z m : ℂ)
    (hm : certificateDysonResidual spectrum s z m = 0) :
    m.im = (z.im + s * m.im) * certificateRealAverage
      (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) (z + s * m))) := by
  have heq := (certificateDysonResidual_eq_zero_iff spectrum s z m).mp hm
  have h := certificate_average_ward spectrum (z + s * m)
  rw [← heq] at h
  simpa using h

/-- Upper-half-plane Dyson solutions obey the uniform averaged Ward bound. -/
theorem certificate_dyson_ward_le (spectrum : ι → ℝ) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 ≤ z.im) (hmi : 0 < m.im)
    (hm : certificateDysonResidual spectrum s z m = 0) :
    certificateRealAverage
      (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) (z + s * m))) ≤ s⁻¹ := by
  have h := certificate_dyson_ward spectrum s z m hm
  have hA : 0 ≤ certificateRealAverage
      (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) (z + s * m))) := by
    apply Finset.expect_nonneg
    intro i _
    exact Complex.normSq_nonneg _
  rw [inv_eq_one_div, le_div_iff₀ hs]
  have hmul := mul_nonneg hz hA
  nlinarith

/-- Strict Ward bound at positive height, used for branch uniqueness. -/
theorem certificate_dyson_ward_lt [Nonempty ι]
    (spectrum : ι → ℝ) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 < z.im) (hmi : 0 < m.im)
    (hm : certificateDysonResidual spectrum s z m = 0) :
    certificateRealAverage
      (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) (z + s * m))) < s⁻¹ := by
  have h := certificate_dyson_ward spectrum s z m hm
  have hA : 0 < certificateRealAverage
      (fun i => Complex.normSq (certificateScalarResolvent (spectrum i) (z + s * m))) := by
    apply Finset.expect_pos _ Finset.univ_nonempty
    intro i _
    apply Complex.normSq_pos.mpr
    unfold certificateScalarResolvent
    apply inv_ne_zero
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    nlinarith
  rw [inv_eq_one_div, lt_div_iff₀ hs]
  have hmul := mul_pos hz hA
  nlinarith

/-- Solutions of the scalar Dyson equation satisfy `|m|² ≤ 1/s`, uniformly in `F`. -/
theorem certificate_dyson_normSq_le [Nonempty ι]
    (spectrum : ι → ℝ) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 ≤ z.im) (hmi : 0 < m.im)
    (hm : certificateDysonResidual spectrum s z m = 0) :
    Complex.normSq m ≤ s⁻¹ := by
  have heq := (certificateDysonResidual_eq_zero_iff spectrum s z m).mp hm
  calc
    Complex.normSq m = Complex.normSq (certificateAverage
      (fun i => certificateScalarResolvent (spectrum i) (z + s * m))) := congrArg _ heq
    _ ≤ _ := certificateAverage_normSq_le _
    _ ≤ s⁻¹ := certificate_dyson_ward_le spectrum hs hz hmi hm

/-- Difference of two scalar resolvents `(d - a)⁻¹ - (d - b)⁻¹`. -/
theorem certificate_scalar_resolvent_sub (d : ℝ) {a b : ℂ}
    (ha : a.im ≠ 0) (hb : b.im ≠ 0) :
    certificateScalarResolvent d a - certificateScalarResolvent d b =
      (a - b) * certificateScalarResolvent d a * certificateScalarResolvent d b := by
  have hda : (d : ℂ) - a ≠ 0 := by
    intro heq
    exact ha (by simpa only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero]
      using congrArg Complex.im heq)
  have hdb : (d : ℂ) - b ≠ 0 := by
    intro heq
    exact hb (by simpa only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero]
      using congrArg Complex.im heq)
  unfold certificateScalarResolvent
  field_simp [hda, hdb]
  ring

/-- Difference of two values of the finite Dyson residual, with the divided-difference
coefficient written through the scalar resolvents. -/
theorem certificate_dyson_sub (spectrum : ι → ℝ) (s : ℝ) (z : ℂ) {m n : ℂ}
    (hmz : (z + s * m).im ≠ 0) (hnz : (z + s * n).im ≠ 0) :
    certificateDysonResidual spectrum s z m - certificateDysonResidual spectrum s z n =
      (m - n) * (1 - (s : ℂ) * certificateAverage (fun i =>
        certificateScalarResolvent (spectrum i) (z + s * m) *
          certificateScalarResolvent (spectrum i) (z + s * n))) := by
  have heq : ∀ i, certificateScalarResolvent (spectrum i) (z + s * m) -
      certificateScalarResolvent (spectrum i) (z + s * n) =
      ((s : ℂ) * (m - n)) * (certificateScalarResolvent (spectrum i) (z + s * m) *
        certificateScalarResolvent (spectrum i) (z + s * n)) := by
    intro i
    rw [certificate_scalar_resolvent_sub _ hmz hnz]
    ring
  have havg : certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * m)) -
      certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * n)) =
      ((s : ℂ) * (m - n)) * certificateAverage (fun i =>
        certificateScalarResolvent (spectrum i) (z + s * m) *
          certificateScalarResolvent (spectrum i) (z + s * n)) := by
    unfold certificateAverage
    rw [← Finset.expect_sub_distrib]
    simp_rw [heq]
    rw [Finset.mul_expect]
  unfold certificateDysonResidual
  calc
    _ = (m - n) - (certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * m)) -
      certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * n))) := by ring
    _ = _ := by rw [havg]; ring

/-- Uniqueness of the upper-half-plane root of the finite Dyson equation at positive height
(Ward identity and Cauchy–Schwarz). -/
theorem certificate_dyson_unique [Nonempty ι]
    (spectrum : ι → ℝ) {s : ℝ} {z m n : ℂ}
    (hs : 0 < s) (hz : 0 < z.im) (hmi : 0 < m.im) (hni : 0 < n.im)
    (hm : certificateDysonResidual spectrum s z m = 0)
    (hn : certificateDysonResidual spectrum s z n = 0) : m = n := by
  have hmz : (z + s * m).im ≠ 0 := by
    have hp : 0 < (z + s * m).im := by simpa using add_pos hz (mul_pos hs hmi)
    exact hp.ne'
  have hnz : (z + s * n).im ≠ 0 := by
    have hp : 0 < (z + s * n).im := by simpa using add_pos hz (mul_pos hs hni)
    exact hp.ne'
  let A := certificateRealAverage (fun i => Complex.normSq
    (certificateScalarResolvent (spectrum i) (z + s * m)))
  let B := certificateRealAverage (fun i => Complex.normSq
    (certificateScalarResolvent (spectrum i) (z + s * n)))
  let T := certificateAverage (fun i =>
    certificateScalarResolvent (spectrum i) (z + s * m) *
      certificateScalarResolvent (spectrum i) (z + s * n))
  have hA : A < s⁻¹ := certificate_dyson_ward_lt spectrum hs hz hmi hm
  have hB : B < s⁻¹ := certificate_dyson_ward_lt spectrum hs hz hni hn
  have hB0 : 0 ≤ B := Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hAB : A * B < s⁻¹ * s⁻¹ :=
    mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hA.le hB hB0 (inv_pos.mpr hs)
  have hT : ‖T‖ ^ 2 ≤ A * B := certificateAverage_mul_normSq_le _ _
  have hnorm : ‖(s : ℂ) * T‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hsq : s ^ 2 * ‖T‖ ^ 2 < 1 := by
      have hh := mul_lt_mul_of_pos_left (hT.trans_lt hAB) (sq_pos_of_pos hs)
      have hid : s ^ 2 * (s⁻¹ * s⁻¹) = 1 := by field_simp
      simpa [hid] using hh
    nlinarith [norm_nonneg T]
  have hsub := certificate_dyson_sub spectrum s z hmz hnz
  rw [hm, hn, sub_self] at hsub
  have hfactor : 1 - (s : ℂ) * T ≠ 0 := by
    intro hzero
    have heq : (s : ℂ) * T = 1 := (sub_eq_zero.mp hzero).symm
    rw [heq, norm_one] at hnorm
    exact (lt_irrefl _ hnorm)
  have heq : m - n = 0 := (mul_eq_zero.mp hsub.symm).resolve_right hfactor
  exact sub_eq_zero.mp heq

end BlockBand.Palm
