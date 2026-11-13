module

public import BlockBand.Palm.MomentFlow.EventGamma

/-!
# Uniform stability and Lipschitz continuity of the Dyson root in `(s, z)`

The implicit-differentiation step is replaced by an exact two-point identity, valid down to the
real axis (no lower bound on `Im z`):

* `certificate_cross_stability`: for two Dyson solutions `(s, z, m)`, `(s', z', m')` of the same
  spectrum with `0 < s ≤ s'`, `Im z, Im z' ≥ 0`, `Im m, Im m' > 0`, and resolvents
  `r_i = (λ_i - z - s m)⁻¹`, `r'_i = (λ_i - z' - s' m')⁻¹`:
  `s (Im m + Im m')²/2 ≤ |1 - s ⟨r r'⟩|`.
  (Pointwise `Re(r r') ≤ (|r|² + |r'|²)/2 - (Im r + Im r')²/2`, Ward `s⟨|r|²⟩ ≤ 1`,
  `s⟨|r'|²⟩ ≤ s/s' ≤ 1`, Jensen.)
* `certificate_two_point`: `(m - m')(1 - s⟨r r'⟩) = ⟨r r'⟩((z - z') + (s - s') m')`.
* **`dyson_stable_lipschitz`**: for Hermitian `F`, `N ≥ 1`, `0 < κ ≤ s, s'`,
  `Im z, Im z' ≥ 0`, `v ≤ Im m_s(z), Im m_{s'}(z')` with `v > 0`:
  `|m_s(z) - m_{s'}(z')| ≤ (|z - z'| + |s - s'|/√κ)/(2κ²v²)`.
  Uniform in `N`, `F` and in the heights (including `Im z = 0`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

section Certificate

variable {ι : Type*} [Fintype ι]

/-- Pointwise: `Re(r r') ≤ (|r|² + |r'|²)/2 - (Im r + Im r')²/2`. -/
theorem re_mul_le_half (r b : ℂ) :
    (r * b).re ≤ Complex.normSq r / 2 + Complex.normSq b / 2 - (r.im + b.im) ^ 2 / 2 := by
  rw [Complex.mul_re, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith [sq_nonneg (r.re - b.re)]

theorem certificateScalarResolvent_im_nonneg (d : ℝ) {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ (certificateScalarResolvent d w).im := by
  rw [certificate_scalar_ward]; exact mul_nonneg hw (Complex.normSq_nonneg _)

/-- **Uniform two-point stability** (down to the real axis). -/
theorem certificate_cross_stability [Nonempty ι] (spectrum : ι → ℝ) {s s' : ℝ} {z z' m m' : ℂ}
    (hs : 0 < s) (hss : s ≤ s') (hz : 0 ≤ z.im) (hz' : 0 ≤ z'.im) (hm : 0 < m.im)
    (hm' : 0 < m'.im) (hr : certificateDysonResidual spectrum s z m = 0)
    (hr' : certificateDysonResidual spectrum s' z' m' = 0) :
    s * (m.im + m'.im) ^ 2 / 2 ≤
      ‖1 - (s : ℂ) * certificateAverage (fun i =>
        certificateScalarResolvent (spectrum i) (z + s * m) *
          certificateScalarResolvent (spectrum i) (z' + s' * m'))‖ := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  set r : ι → ℂ := fun i => certificateScalarResolvent (spectrum i) (z + s * m)
  set b : ι → ℂ := fun i => certificateScalarResolvent (spectrum i) (z' + s' * m')
  have hA : certificateRealAverage (fun i => Complex.normSq (r i)) ≤ s⁻¹ :=
    certificate_dyson_ward_le spectrum hs hz hm hr
  have hB : certificateRealAverage (fun i => Complex.normSq (b i)) ≤ s⁻¹ :=
    (certificate_dyson_ward_le spectrum hs' hz' hm' hr').trans (inv_anti₀ hs hss)
  have heq := (certificateDysonResidual_eq_zero_iff spectrum s z m).mp hr
  have heq' := (certificateDysonResidual_eq_zero_iff spectrum s' z' m').mp hr'
  have hIm : certificateRealAverage (fun i => (r i).im + (b i).im) = m.im + m'.im := by
    have h1 : m.im = certificateRealAverage (fun i => (r i).im) := by
      rw [← certificateAverage_im]; exact congrArg Complex.im heq
    have h2 : m'.im = certificateRealAverage (fun i => (b i).im) := by
      rw [← certificateAverage_im]; exact congrArg Complex.im heq'
    rw [h1, h2]
    simp only [certificateRealAverage, Finset.expect_add_distrib]
  have hJ := certificate_jensen (fun i => (r i).im + (b i).im)
  rw [hIm] at hJ
  have hpt : certificateRealAverage (fun i => (r i * b i).re) ≤
      certificateRealAverage (fun i => Complex.normSq (r i)) / 2 +
        certificateRealAverage (fun i => Complex.normSq (b i)) / 2 -
          certificateRealAverage (fun i => ((r i).im + (b i).im) ^ 2) / 2 := by
    have : certificateRealAverage (fun i => (r i * b i).re) ≤
        certificateRealAverage (fun i => Complex.normSq (r i) / 2 + Complex.normSq (b i) / 2 -
          ((r i).im + (b i).im) ^ 2 / 2) :=
      Finset.expect_le_expect fun i _ => re_mul_le_half (r i) (b i)
    refine this.trans (le_of_eq ?_)
    simp only [certificateRealAverage, Finset.expect_sub_distrib, Finset.expect_add_distrib,
      Finset.expect_div]
  have hre : (1 - (s : ℂ) * certificateAverage (fun i => r i * b i)).re =
      1 - s * certificateRealAverage (fun i => (r i * b i).re) := by
    rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, certificateAverage_re]
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [hre]
  have hsA : s * certificateRealAverage (fun i => Complex.normSq (r i)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hA hs.le; rwa [mul_inv_cancel₀ hs.ne'] at this
  have hsB : s * certificateRealAverage (fun i => Complex.normSq (b i)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hB hs.le; rwa [mul_inv_cancel₀ hs.ne'] at this
  have := mul_le_mul_of_nonneg_left hpt hs.le
  have hJ' := mul_le_mul_of_nonneg_left hJ hs.le
  nlinarith

/-- The exact two-point identity `(m - m')(1 - s⟨r r'⟩) = ⟨r r'⟩((z - z') + (s - s')m')`. -/
theorem certificate_two_point (spectrum : ι → ℝ) {s s' : ℝ} {z z' m m' : ℂ}
    (hw : (z + s * m).im ≠ 0) (hw' : (z' + s' * m').im ≠ 0)
    (hr : certificateDysonResidual spectrum s z m = 0)
    (hr' : certificateDysonResidual spectrum s' z' m' = 0) :
    (m - m') * (1 - (s : ℂ) * certificateAverage (fun i =>
        certificateScalarResolvent (spectrum i) (z + s * m) *
          certificateScalarResolvent (spectrum i) (z' + s' * m'))) =
      certificateAverage (fun i =>
        certificateScalarResolvent (spectrum i) (z + s * m) *
          certificateScalarResolvent (spectrum i) (z' + s' * m')) *
        ((z - z') + ((s : ℂ) - s') * m') := by
  set T := certificateAverage (fun i =>
    certificateScalarResolvent (spectrum i) (z + s * m) *
      certificateScalarResolvent (spectrum i) (z' + s' * m'))
  have heq := (certificateDysonResidual_eq_zero_iff spectrum s z m).mp hr
  have heq' := (certificateDysonResidual_eq_zero_iff spectrum s' z' m').mp hr'
  have h1 : certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z + s * m)) -
      certificateAverage (fun i => certificateScalarResolvent (spectrum i) (z' + s' * m')) =
      ((z + s * m) - (z' + s' * m')) * T := by
    unfold T certificateAverage
    rw [← Finset.expect_sub_distrib, Finset.mul_expect]
    refine Finset.expect_congr rfl fun i _ => ?_
    rw [certificate_scalar_resolvent_sub _ hw hw']
    ring
  have hdiff : m - m' = ((z + s * m) - (z' + s' * m')) * T := by
    rw [← h1]
    conv_lhs => rw [heq, heq']
  linear_combination hdiff

end Certificate

variable {N : ℕ}

/-- **Uniform Lipschitz bound for the Dyson root in `(s, z)`**, ordered version `s ≤ s'`. -/
theorem dyson_stable_lipschitz_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) {κ v s s' : ℝ} (hκ : 0 < κ) (hv : 0 < v) (hκs : κ ≤ s) (hss : s ≤ s')
    {z z' : ℂ} (hz : 0 ≤ z.im) (hz' : 0 ≤ z'.im) (hm : v ≤ (freshDyson F s z).im)
    (hm' : v ≤ (freshDyson F s' z').im) :
    ‖freshDyson F s z - freshDyson F s' z'‖ ≤
      (‖z - z'‖ + |s - s'| / Real.sqrt κ) / (2 * κ ^ 2 * v ^ 2) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hs : 0 < s := lt_of_lt_of_le hκ hκs
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  set m := freshDyson F s z
  set m' := freshDyson F s' z'
  have hmp : 0 < m.im := lt_of_lt_of_le hv hm
  have hmp' : 0 < m'.im := lt_of_lt_of_le hv hm'
  have hr := freshDyson_residual_eq_zero hF hs hz hmp
  have hr' := freshDyson_residual_eq_zero hF hs' hz' hmp'
  have hw : (z + s * m).im ≠ 0 := (add_ofReal_mul_im_pos hs hz hmp).ne'
  have hw' : (z' + s' * m').im ≠ 0 := (add_ofReal_mul_im_pos hs' hz' hmp').ne'
  set T := certificateAverage (fun i =>
    certificateScalarResolvent (hF.eigenvalues i) (z + s * m) *
      certificateScalarResolvent (hF.eigenvalues i) (z' + s' * m'))
  have hstab := certificate_cross_stability hF.eigenvalues hs hss hz hz' hmp hmp' hr hr'
  have hid := certificate_two_point hF.eigenvalues hw hw' hr hr'
  -- `|T| ≤ 1/√(s s') ≤ 1/κ`
  have hT : ‖T‖ ≤ 1 / κ := by
    have hcs := certificateAverage_mul_normSq_le
      (fun i => certificateScalarResolvent (hF.eigenvalues i) (z + s * m))
      (fun i => certificateScalarResolvent (hF.eigenvalues i) (z' + s' * m'))
    have hA := certificate_dyson_ward_le hF.eigenvalues hs hz hmp hr
    have hB := certificate_dyson_ward_le hF.eigenvalues hs' hz' hmp' hr'
    have hA' : s⁻¹ ≤ κ⁻¹ := inv_anti₀ hκ hκs
    have hB' : s'⁻¹ ≤ κ⁻¹ := inv_anti₀ hκ (hκs.trans hss)
    have hA0 : 0 ≤ certificateRealAverage (fun i => Complex.normSq
        (certificateScalarResolvent (hF.eigenvalues i) (z + s * m))) :=
      Finset.expect_nonneg fun _ _ => Complex.normSq_nonneg _
    have hB0 : 0 ≤ certificateRealAverage (fun i => Complex.normSq
        (certificateScalarResolvent (hF.eigenvalues i) (z' + s' * m'))) :=
      Finset.expect_nonneg fun _ _ => Complex.normSq_nonneg _
    have hsq : ‖T‖ ^ 2 ≤ (1 / κ) ^ 2 := by
      refine hcs.trans ?_
      rw [div_pow, one_pow, one_div, ← inv_pow, sq]
      exact mul_le_mul (hA.trans hA') (hB.trans hB') hB0 (inv_nonneg.2 hκ.le)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  -- `|m'| ≤ 1/√κ`
  have hm'n : ‖m'‖ ≤ 1 / Real.sqrt κ := by
    have h := certificate_dyson_normSq_le hF.eigenvalues hs' hz' hmp' hr'
    rw [Complex.normSq_eq_norm_sq] at h
    have h2 : ‖m'‖ ^ 2 ≤ (1 / Real.sqrt κ) ^ 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt hκ.le, one_div]
      exact h.trans (inv_anti₀ hκ (hκs.trans hss))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  -- the stability margin
  have hmarg : 2 * κ ^ 2 * v ^ 2 / κ ≤ ‖1 - (s : ℂ) * T‖ := by
    refine le_trans ?_ hstab
    have h1 : 2 * v ≤ m.im + m'.im := by linarith
    have h2 : (2 * v) ^ 2 ≤ (m.im + m'.im) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have : 2 * κ ^ 2 * v ^ 2 / κ = κ * (2 * v) ^ 2 / 2 := by field_simp
    rw [this]
    have := mul_le_mul hκs h2 (by positivity) hs.le
    linarith
  have hmarg0 : 0 < 2 * κ ^ 2 * v ^ 2 / κ := by positivity
  have hnorm := congrArg norm hid
  rw [norm_mul, norm_mul] at hnorm
  have hrhs : ‖(z - z') + ((s : ℂ) - s') * m'‖ ≤ ‖z - z'‖ + |s - s'| / Real.sqrt κ := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, show ((s : ℂ) - s') = ((s - s' : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hm'n (abs_nonneg _)
  have hkey : ‖m - m'‖ * (2 * κ ^ 2 * v ^ 2 / κ) ≤
      (1 / κ) * (‖z - z'‖ + |s - s'| / Real.sqrt κ) := by
    calc ‖m - m'‖ * (2 * κ ^ 2 * v ^ 2 / κ) ≤ ‖m - m'‖ * ‖1 - (s : ℂ) * T‖ :=
          mul_le_mul_of_nonneg_left hmarg (norm_nonneg _)
      _ = ‖T‖ * ‖(z - z') + ((s : ℂ) - s') * m'‖ := hnorm
      _ ≤ (1 / κ) * (‖z - z'‖ + |s - s'| / Real.sqrt κ) :=
          mul_le_mul hT hrhs (norm_nonneg _) (by positivity)
  rw [le_div_iff₀ (by positivity)]
  have e : (1 / κ) * (‖z - z'‖ + |s - s'| / Real.sqrt κ) =
      (‖z - z'‖ + |s - s'| / Real.sqrt κ) / κ := by ring
  have e2 : ‖m - m'‖ * (2 * κ ^ 2 * v ^ 2 / κ) = ‖m - m'‖ * (2 * κ ^ 2 * v ^ 2) / κ := by ring
  rw [e, e2, div_le_div_iff_of_pos_right hκ] at hkey
  exact hkey

/-- **Uniform Lipschitz bound for the Dyson root in `(s, z)`** (in the paper, "`m_s` has
bounded derivatives"): `|m_s(z) - m_{s'}(z')| ≤ (|z - z'| + |s - s'|/√κ)/(2κ²v²)` whenever
`κ ≤ s, s'`, `Im z, Im z' ≥ 0` and `v ≤ Im m` at both points. -/
theorem dyson_stable_lipschitz {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) {κ v s s' : ℝ} (hκ : 0 < κ) (hv : 0 < v) (hκs : κ ≤ s) (hκs' : κ ≤ s')
    {z z' : ℂ} (hz : 0 ≤ z.im) (hz' : 0 ≤ z'.im) (hm : v ≤ (freshDyson F s z).im)
    (hm' : v ≤ (freshDyson F s' z').im) :
    ‖freshDyson F s z - freshDyson F s' z'‖ ≤
      (‖z - z'‖ + |s - s'| / Real.sqrt κ) / (2 * κ ^ 2 * v ^ 2) := by
  rcases le_total s s' with h | h
  · exact dyson_stable_lipschitz_le hF hN hκ hv hκs h hz hz' hm hm'
  · rw [norm_sub_rev, norm_sub_rev z, abs_sub_comm]
    exact dyson_stable_lipschitz_le hF hN hκ hv hκs' h hz' hz hm' hm

/-- On the fresh-regularity window, with `κ = c₀ - s₀`: the Lipschitz constant
`dysonLipConst c₀ s₀ v₀ = 1/(2(c₀-s₀)²v₀²)`. -/
def dysonLipConst (c₀ s₀ v₀ : ℝ) : ℝ := 1 / (2 * (c₀ - s₀) ^ 2 * v₀ ^ 2)

theorem dysonLipConst_nonneg (c₀ s₀ v₀ : ℝ) :
    0 ≤ dysonLipConst c₀ s₀ v₀ := by
  unfold dysonLipConst; positivity

/-- **Lipschitz bound on the regularity window.** -/
theorem freshDyson_window_lipschitz (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {s s' : ℝ} (hs : s ∈ Icc (c₀ - s₀) c₀) (hs' : s' ∈ Icc (c₀ - s₀) c₀) {z z' : ℂ}
    (hx : |z.re - E| ≤ r₀) (hx' : |z'.re - E| ≤ r₀) (hz : 0 ≤ z.im) (hz1 : z.im ≤ 1)
    (hz' : 0 ≤ z'.im) (hz1' : z'.im ≤ 1) :
    ‖freshDyson F s z - freshDyson F s' z'‖ ≤
      dysonLipConst c₀ s₀ v₀ * (‖z - z'‖ + |s - s'| / Real.sqrt (c₀ - s₀)) := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < c₀ - s₀ := by linarith
  have h1 := (fresh_regular_bounds hC.2.2 hs hx hz hz1).1
  have h2 := (fresh_regular_bounds hC.2.2 hs' hx' hz' hz1').1
  have := dyson_stable_lipschitz hC.1 hN hκ hv0 hs.1 hs'.1 hz hz' h1 h2
  rw [dysonLipConst, one_div_mul_eq_div]
  exact this

end BlockBand.Palm.MomentFlow
