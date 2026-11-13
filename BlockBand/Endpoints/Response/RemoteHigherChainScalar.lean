module

public import BlockBand.Endpoints.Response.FractionalTraceJensenScalar

/-!
# Scalar inequalities for the higher one-layer clock step

* `rhc_rpow_tangent_ge`: the tangent line of the convex `t ↦ t^r`, `r ≥ 1`:
  `t^r + r t^{r-1}(v - t) ≤ v^r` (`t > 0`, `v ≥ 0`).
* `rhc_rpow_diff_mul_le`: `((a + ℓ)^s - a^s) ℓ ≤ s 2^{s+1} a^{s-1} ℓ²` for `s ≥ 0`, `|ℓ| ≤ a/2`.
* `rhc_pointwise`: the pointwise power inequality, for `r ≥ 1`, `a > 0`, `0 ≤ h ≤ a + ℓ`,
  `h^r + 2^{1-r} a^{r-1}(a + ℓ - h)
     ≤ a^r + r a^{r-1} ℓ + r D_{r-1} a^{r-2} ℓ² + E_r |ℓ|^{r+2}/a²`.
  It is used in place of the concavity of the fractional trace in the higher one-layer step: the
  linear term `r a^{r-1} ℓ` has mean zero, the concavity defect `a + ℓ - h ≥ 0` of `Tr(·)^p`
  (Klein) is retained with the weight `2^{1-r}a^{r-1}`, and the quadratic and tail terms are paid
  by fluctuation moments.
* `rhc_young`: `x^{r-1} G² ≤ ε x^{r+1} + ε^{-(r-1)/2} G^{r+1}` (the forcing exponents of the
  higher logistic inequality).
* `rhc_one_add_rpow_le`: `(1 + x)^r ≤ 1 + r (1 + X)^{r-1} x` for `0 ≤ x ≤ X`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

/-- Tangent inequality for the convex `t ↦ t^r`, `r ≥ 1`: `t^r + r t^{r-1}(v - t) ≤ v^r`. -/
theorem rhc_rpow_tangent_ge {r t v : ℝ} (hr : 1 ≤ r) (ht : 0 < t) (hv : 0 ≤ v) :
    t ^ r + r * t ^ (r - 1) * (v - t) ≤ v ^ r := by
  have hs : -1 ≤ (v - t) / t := by rw [le_div_iff₀ ht]; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hr
  have hvt : v = t * (1 + (v - t) / t) := by field_simp; ring
  have ht0 : t ≠ 0 := ht.ne'
  calc t ^ r + r * t ^ (r - 1) * (v - t) = t ^ r * (1 + r * ((v - t) / t)) := by
        rw [Real.rpow_sub_one ht0]; field_simp
    _ ≤ t ^ r * (1 + (v - t) / t) ^ r :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le _)
    _ = v ^ r := by
        conv_rhs => rw [hvt]
        exact (Real.mul_rpow ht.le (by linarith)).symm

/-- The constant `D_s = s 2^{s+1}` of `rhc_rpow_diff_mul_le`. -/
def rhc_D (s : ℝ) : ℝ := s * 2 ^ (s + 1)

theorem rhc_D_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ rhc_D s := by
  unfold rhc_D; positivity

/-- The second-order difference bound `((a + ℓ)^s - a^s) ℓ ≤ D_s a^{s-1} ℓ²` for `s ≥ 0`,
`a > 0`, `|ℓ| ≤ a/2`. -/
theorem rhc_rpow_diff_mul_le {s a ℓ : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hℓ : |ℓ| ≤ a / 2) :
    ((a + ℓ) ^ s - a ^ s) * ℓ ≤ rhc_D s * a ^ (s - 1) * ℓ ^ 2 := by
  have hℓ1 := neg_abs_le ℓ
  have hℓ2 := le_abs_self ℓ
  set y := a + ℓ with hy
  have hy2 : a / 2 ≤ y := by rw [hy]; linarith
  have hyp : 0 < y := by linarith
  have hya : y ≤ 2 * a := by rw [hy]; linarith
  have has : 0 ≤ a ^ (s - 1) := Real.rpow_nonneg ha.le _
  have hℓsq : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have h2s : (1 : ℝ) ≤ 2 ^ (s + 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have hsD : s * a ^ (s - 1) * ℓ ^ 2 ≤ rhc_D s * a ^ (s - 1) * ℓ ^ 2 := by
    unfold rhc_D
    have : s ≤ s * 2 ^ (s + 1) := le_mul_of_one_le_right hs h2s
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this has) hℓsq
  rcases le_total 1 s with hs1 | hs1
  · rcases le_total 0 ℓ with hl | hl
    · -- convex, `ℓ ≥ 0`: tangent at `y`
      have ht := rhc_rpow_tangent_ge hs1 hyp ha.le
      have h1 : y ^ s - a ^ s ≤ s * y ^ (s - 1) * ℓ := by
        have : a - y = -ℓ := by rw [hy]; ring
        rw [this] at ht; linarith
      have h2 : y ^ (s - 1) ≤ 2 ^ (s - 1) * a ^ (s - 1) := by
        rw [← Real.mul_rpow (by norm_num) ha.le]
        exact Real.rpow_le_rpow hyp.le hya (by linarith)
      have h3 : (2 : ℝ) ^ (s - 1) ≤ 2 ^ (s + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      calc (y ^ s - a ^ s) * ℓ ≤ s * y ^ (s - 1) * ℓ * ℓ := mul_le_mul_of_nonneg_right h1 hl
        _ ≤ s * (2 ^ (s - 1) * a ^ (s - 1)) * ℓ * ℓ := by
            have := mul_le_mul_of_nonneg_left h2 hs
            have hll : 0 ≤ ℓ * ℓ := mul_nonneg hl hl
            nlinarith
        _ ≤ s * (2 ^ (s + 1) * a ^ (s - 1)) * ℓ * ℓ := by
            have := mul_le_mul_of_nonneg_right h3 has
            have hll : 0 ≤ ℓ * ℓ := mul_nonneg hl hl
            have := mul_le_mul_of_nonneg_left this hs
            nlinarith
        _ = rhc_D s * a ^ (s - 1) * ℓ ^ 2 := by unfold rhc_D; ring
    · -- convex, `ℓ ≤ 0`: tangent at `a`
      have ht := rhc_rpow_tangent_ge hs1 ha hyp.le
      have h1 : s * a ^ (s - 1) * ℓ ≤ y ^ s - a ^ s := by
        have : y - a = ℓ := by rw [hy]; ring
        rw [this] at ht; linarith
      have : (y ^ s - a ^ s) * ℓ ≤ s * a ^ (s - 1) * ℓ * ℓ :=
        mul_le_mul_of_nonpos_right h1 hl
      nlinarith
  · rcases le_total 0 ℓ with hl | hl
    · -- concave, `ℓ ≥ 0`: tangent at `a`
      have ht := ftj_rpow_tangent hs hs1 ha hyp.le
      have h1 : y ^ s - a ^ s ≤ s * a ^ (s - 1) * ℓ := by
        have : y - a = ℓ := by rw [hy]; ring
        rw [this] at ht; linarith
      have : (y ^ s - a ^ s) * ℓ ≤ s * a ^ (s - 1) * ℓ * ℓ := mul_le_mul_of_nonneg_right h1 hl
      nlinarith
    · -- concave, `ℓ ≤ 0`: tangent at `y`
      have ht := ftj_rpow_tangent hs hs1 hyp ha.le
      have h1 : s * y ^ (s - 1) * ℓ ≤ y ^ s - a ^ s := by
        have : a - y = -ℓ := by rw [hy]; ring
        rw [this] at ht; linarith
      have h2 : y ^ (s - 1) ≤ (a / 2) ^ (s - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hy2 (by linarith)
      have h3 : (a / 2) ^ (s - 1) ≤ 2 ^ (s + 1) * a ^ (s - 1) := by
        rw [Real.div_rpow ha.le (by norm_num), div_eq_mul_inv, mul_comm,
          ← Real.rpow_neg (by norm_num)]
        refine mul_le_mul_of_nonneg_right ?_ has
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h4 : (y ^ s - a ^ s) * ℓ ≤ s * y ^ (s - 1) * ℓ * ℓ :=
        mul_le_mul_of_nonpos_right h1 hl
      have hll : 0 ≤ ℓ * ℓ := mul_nonneg_of_nonpos_of_nonpos hl hl
      have h5 : s * y ^ (s - 1) * ℓ * ℓ ≤ s * (2 ^ (s + 1) * a ^ (s - 1)) * ℓ * ℓ := by
        have := mul_le_mul_of_nonneg_left (h2.trans h3) hs
        nlinarith
      calc (y ^ s - a ^ s) * ℓ ≤ s * (2 ^ (s + 1) * a ^ (s - 1)) * ℓ * ℓ := h4.trans h5
        _ = rhc_D s * a ^ (s - 1) * ℓ ^ 2 := by unfold rhc_D; ring

/-- The tail constant `E_r = 4 (r + 4) 3^r` of `rhc_pointwise`. -/
def rhc_E (r : ℝ) : ℝ := 4 * (r + 4) * 3 ^ r

theorem rhc_E_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ rhc_E r := by
  unfold rhc_E; positivity

/-- The pointwise power inequality. For `r ≥ 1`, `a > 0` and `0 ≤ h ≤ a + ℓ`:
`h^r + 2^{1-r} a^{r-1}(a + ℓ - h) ≤ a^r + r a^{r-1} ℓ + r D_{r-1} a^{r-2} ℓ² + E_r |ℓ|^{r+2}/a²`. -/
theorem rhc_pointwise {r a h ℓ : ℝ} (hr : 1 ≤ r) (ha : 0 < a) (hh : 0 ≤ h) (hhy : h ≤ a + ℓ) :
    h ^ r + 2 ^ (1 - r) * a ^ (r - 1) * (a + ℓ - h) ≤
      a ^ r + r * a ^ (r - 1) * ℓ + r * rhc_D (r - 1) * a ^ (r - 2) * ℓ ^ 2 +
        rhc_E r * |ℓ| ^ (r + 2) / a ^ 2 := by
  have hr0 : 0 < r := by linarith
  set y := a + ℓ with hy
  have hy0 : 0 ≤ y := hh.trans hhy
  have hD : 0 ≤ rhc_D (r - 1) := rhc_D_nonneg (by linarith)
  have hE : 0 ≤ rhc_E r := rhc_E_nonneg hr0.le
  have har1 : 0 ≤ a ^ (r - 1) := Real.rpow_nonneg ha.le _
  have hDterm : 0 ≤ r * rhc_D (r - 1) * a ^ (r - 2) * ℓ ^ 2 := by
    have := Real.rpow_nonneg ha.le (r - 2); positivity
  have hEterm : 0 ≤ rhc_E r * |ℓ| ^ (r + 2) / a ^ 2 := by
    have := Real.rpow_nonneg (abs_nonneg ℓ) (r + 2); positivity
  have h21 : (2 : ℝ) ^ (1 - r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h20 : 0 ≤ (2 : ℝ) ^ (1 - r) := Real.rpow_nonneg (by norm_num) _
  have hhr : h ^ r ≤ y ^ r := Real.rpow_le_rpow hh hhy hr0.le
  rcases le_or_gt |ℓ| (a / 2) with hl | hl
  · -- the small fluctuations: second order
    have hℓ1 := neg_abs_le ℓ
    have hy2 : a / 2 ≤ y := by rw [hy]; linarith
    have hyp : 0 < y := by linarith
    -- `h^r ≤ y^{r-1} h`
    have h1 : h ^ r ≤ y ^ (r - 1) * h := by
      rcases hh.eq_or_lt with h0 | h0
      · rw [← h0, Real.zero_rpow hr0.ne']; simp
      · have e : h ^ r = h ^ (r - 1) * h := by
          rw [Real.rpow_sub_one h0.ne']; field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hh hhy (by linarith)) hh
    have e2 : y ^ (r - 1) * h = y ^ r - y ^ (r - 1) * (y - h) := by
      rw [Real.rpow_sub_one hyp.ne']; field_simp; ring
    -- `y^r ≤ a^r + r y^{r-1} ℓ`
    have h3 : y ^ r ≤ a ^ r + r * y ^ (r - 1) * ℓ := by
      have ht := rhc_rpow_tangent_ge hr hyp ha.le
      have : a - y = -ℓ := by rw [hy]; ring
      rw [this] at ht; linarith
    have h4 : r * y ^ (r - 1) * ℓ ≤ r * a ^ (r - 1) * ℓ + r * rhc_D (r - 1) * a ^ (r - 2) * ℓ ^ 2 := by
      have hd := rhc_rpow_diff_mul_le (s := r - 1) (by linarith) ha hl
      rw [show r - 1 - 1 = r - 2 by ring] at hd
      have := mul_le_mul_of_nonneg_left hd hr0.le
      nlinarith
    have h5 : 2 ^ (1 - r) * a ^ (r - 1) * (y - h) ≤ y ^ (r - 1) * (y - h) := by
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      have : (a / 2) ^ (r - 1) ≤ y ^ (r - 1) := Real.rpow_le_rpow (by linarith) hy2 (by linarith)
      rw [Real.div_rpow ha.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        neg_sub] at this
      linarith
    linarith
  · -- the large fluctuations: everything is `O(|ℓ|^r)`
    have hlp : 0 < |ℓ| := lt_of_le_of_lt (by positivity) hl
    have ha2 : a < 2 * |ℓ| := by linarith
    have hy3 : y ≤ 3 * |ℓ| := by rw [hy]; linarith [le_abs_self ℓ]
    have hyr : y ^ r ≤ 3 ^ r * |ℓ| ^ r := by
      rw [← Real.mul_rpow (by norm_num) hlp.le]
      exact Real.rpow_le_rpow hy0 hy3 hr0.le
    have har : a ^ (r - 1) ≤ 2 ^ (r - 1) * |ℓ| ^ (r - 1) := by
      rw [← Real.mul_rpow (by norm_num) hlp.le]
      exact Real.rpow_le_rpow ha.le ha2.le (by linarith)
    have hlr : |ℓ| ^ (r - 1) * |ℓ| = |ℓ| ^ r := by
      rw [Real.rpow_sub_one hlp.ne']; field_simp
    have h23 : (2 : ℝ) ^ (r - 1) ≤ 3 ^ r :=
      (Real.rpow_le_rpow (by norm_num) (by norm_num : (2 : ℝ) ≤ 3) (by linarith)).trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    have hlr0 : 0 ≤ |ℓ| ^ r := Real.rpow_nonneg hlp.le _
    have hlr1 : 0 ≤ |ℓ| ^ (r - 1) := Real.rpow_nonneg hlp.le _
    -- the left side minus the linear part is at most `(r + 4) 3^r |ℓ|^r`
    have hA : h ^ r + 2 ^ (1 - r) * a ^ (r - 1) * (y - h) - (a ^ r + r * a ^ (r - 1) * ℓ) ≤
        (r + 4) * 3 ^ r * |ℓ| ^ r := by
      have i1 : 2 ^ (1 - r) * a ^ (r - 1) * (y - h) ≤ a ^ (r - 1) * y := by
        have : 2 ^ (1 - r) * a ^ (r - 1) ≤ a ^ (r - 1) := by nlinarith
        have hyh : y - h ≤ y := by linarith
        calc 2 ^ (1 - r) * a ^ (r - 1) * (y - h) ≤ a ^ (r - 1) * (y - h) :=
              mul_le_mul_of_nonneg_right this (by linarith)
          _ ≤ a ^ (r - 1) * y := mul_le_mul_of_nonneg_left hyh har1
      have i2 : a ^ (r - 1) * y ≤ 3 * 3 ^ r * |ℓ| ^ r := by
        calc a ^ (r - 1) * y ≤ (2 ^ (r - 1) * |ℓ| ^ (r - 1)) * (3 * |ℓ|) :=
              mul_le_mul har hy3 hy0 (by positivity)
          _ = 3 * 2 ^ (r - 1) * |ℓ| ^ r := by rw [← hlr]; ring
          _ ≤ 3 * 3 ^ r * |ℓ| ^ r := by
              have := mul_le_mul_of_nonneg_right h23 hlr0; nlinarith
      have i3 : -(r * a ^ (r - 1) * ℓ) ≤ r * 3 ^ r * |ℓ| ^ r := by
        have : -(r * a ^ (r - 1) * ℓ) ≤ r * a ^ (r - 1) * |ℓ| := by
          have := neg_abs_le ℓ
          have : -(a ^ (r - 1) * ℓ) ≤ a ^ (r - 1) * |ℓ| := by nlinarith [neg_le_abs ℓ]
          nlinarith
        calc -(r * a ^ (r - 1) * ℓ) ≤ r * a ^ (r - 1) * |ℓ| := this
          _ ≤ r * (2 ^ (r - 1) * |ℓ| ^ (r - 1)) * |ℓ| := by
              have := mul_le_mul_of_nonneg_left har hr0.le
              exact mul_le_mul_of_nonneg_right this hlp.le
          _ = r * 2 ^ (r - 1) * |ℓ| ^ r := by rw [← hlr]; ring
          _ ≤ r * 3 ^ r * |ℓ| ^ r := by
              have := mul_le_mul_of_nonneg_right h23 hlr0
              have := mul_le_mul_of_nonneg_left this hr0.le
              nlinarith
      have ha0 : 0 ≤ a ^ r := Real.rpow_nonneg ha.le _
      nlinarith
    -- `|ℓ|^r ≤ 4 |ℓ|^{r+2}/a²`
    have hB : |ℓ| ^ r ≤ 4 * |ℓ| ^ (r + 2) / a ^ 2 := by
      have e : |ℓ| ^ (r + 2) = |ℓ| ^ r * |ℓ| ^ 2 := by
        rw [Real.rpow_add hlp, Real.rpow_two]
      rw [e, le_div_iff₀ (by positivity)]
      have : a ^ 2 ≤ 4 * |ℓ| ^ 2 := by nlinarith
      nlinarith
    have hC : (r + 4) * 3 ^ r * |ℓ| ^ r ≤ rhc_E r * |ℓ| ^ (r + 2) / a ^ 2 := by
      unfold rhc_E
      have h3r : (0 : ℝ) ≤ (r + 4) * 3 ^ r := by positivity
      calc (r + 4) * 3 ^ r * |ℓ| ^ r ≤ (r + 4) * 3 ^ r * (4 * |ℓ| ^ (r + 2) / a ^ 2) :=
            mul_le_mul_of_nonneg_left hB h3r
        _ = 4 * (r + 4) * 3 ^ r * |ℓ| ^ (r + 2) / a ^ 2 := by ring
    linarith

/-- Young's inequality at the forcing exponents: for `r ≥ 1`, `x, G ≥ 0` and `ε > 0`,
`x^{r-1} G² ≤ ε x^{r+1} + ε^{-(r-1)/2} G^{r+1}`. -/
theorem rhc_young {r x G ε : ℝ} (hr : 1 ≤ r) (hx : 0 ≤ x) (hG : 0 ≤ G) (hε : 0 < ε) :
    x ^ (r - 1) * G ^ 2 ≤ ε * x ^ (r + 1) + ε ^ (-((r - 1) / 2)) * G ^ (r + 1) := by
  have hxr : 0 ≤ x ^ (r + 1) := Real.rpow_nonneg hx _
  have hGr : 0 ≤ G ^ (r + 1) := Real.rpow_nonneg hG _
  have hεr : 0 ≤ ε ^ (-((r - 1) / 2)) := Real.rpow_nonneg hε.le _
  have hx1 : 0 ≤ x ^ (r - 1) := Real.rpow_nonneg hx _
  rcases le_or_gt (ε * x ^ 2) (G ^ 2) with h | h
  · -- `x ≤ G ε^{-1/2}`
    have hxG : x ≤ ε ^ (-(1 / 2 : ℝ)) * G := by
      have hε2 : (ε ^ (-(1 / 2 : ℝ))) ^ 2 = ε⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
        norm_num
        exact Real.rpow_neg_one ε
      have h' : x ^ 2 ≤ (ε ^ (-(1 / 2 : ℝ)) * G) ^ 2 := by
        rw [mul_pow, hε2, le_inv_mul_iff₀ hε]; linarith
      exact (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).mp h'
    have h1 : x ^ (r - 1) ≤ ε ^ (-((r - 1) / 2)) * G ^ (r - 1) := by
      calc x ^ (r - 1) ≤ (ε ^ (-(1 / 2 : ℝ)) * G) ^ (r - 1) :=
            Real.rpow_le_rpow hx hxG (by linarith)
        _ = ε ^ (-((r - 1) / 2)) * G ^ (r - 1) := by
            rw [Real.mul_rpow (by positivity) hG, ← Real.rpow_mul hε.le]
            congr 2; ring
    have e : G ^ (r - 1) * G ^ 2 = G ^ (r + 1) := by
      rw [← Real.rpow_two, ← Real.rpow_add' hG (by linarith)]; ring_nf
    calc x ^ (r - 1) * G ^ 2 ≤ ε ^ (-((r - 1) / 2)) * G ^ (r - 1) * G ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg G)
      _ = ε ^ (-((r - 1) / 2)) * G ^ (r + 1) := by rw [mul_assoc, e]
      _ ≤ _ := by linarith [mul_nonneg hε.le hxr]
  · have e : x ^ (r - 1) * x ^ 2 = x ^ (r + 1) := by
      rw [← Real.rpow_two, ← Real.rpow_add' hx (by linarith)]; ring_nf
    calc x ^ (r - 1) * G ^ 2 ≤ x ^ (r - 1) * (ε * x ^ 2) :=
          mul_le_mul_of_nonneg_left h.le hx1
      _ = ε * x ^ (r + 1) := by rw [← e]; ring
      _ ≤ _ := by linarith [mul_nonneg hεr hGr]

/-- `(1 + x)^r ≤ 1 + r (1 + X)^{r-1} x` for `r ≥ 1`, `0 ≤ x ≤ X`. -/
theorem rhc_one_add_rpow_le {r x X : ℝ} (hr : 1 ≤ r) (hx : 0 ≤ x) (hxX : x ≤ X) :
    (1 + x) ^ r ≤ 1 + r * (1 + X) ^ (r - 1) * x := by
  have ht := rhc_rpow_tangent_ge hr (by linarith : (0 : ℝ) < 1 + x) zero_le_one
  rw [Real.one_rpow] at ht
  have h1 : (1 + x) ^ (r - 1) ≤ (1 + X) ^ (r - 1) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have : r * (1 + x) ^ (r - 1) * x ≤ r * (1 + X) ^ (r - 1) * x := by
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ r)
    exact mul_le_mul_of_nonneg_right this hx
  nlinarith

end BlockBand.Endpoints
