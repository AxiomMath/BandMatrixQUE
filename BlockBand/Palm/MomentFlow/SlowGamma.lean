module

public import BlockBand.Palm.MomentFlow.AvgDyson
public import BlockBand.Palm.MomentFlow.EventTimeDet

/-!
# Slow variation of the relative quadratic form `q*Im M_s(z)q / Im m_s(z)`

*Domain:* `N ≥ 1`, `FreshConstants c₀ r₀ s₀ v₀`, `FreshClass F A c₀ E r₀ s₀ v₀`,
`s ∈ [c₀ - s₀, c₀]`, `z = x + ih`, `|x - E| ≤ r₀`, `0 ≤ h ≤ 1`, any `q` (no normalization).

* `resolvent_l2_compare`: `‖(F - w)⁻¹q - (F - w₀)⁻¹q‖ ≤ |w - w₀|/Im w · ‖(F - w₀)⁻¹q‖`.
* `nsq_compare_rel`: `|‖u‖² - ‖u₀‖²| ≤ δ(2 + δ)‖u₀‖²` when `‖u - u₀‖ ≤ δ‖u₀‖`.
* `freshW_sub_le`: `|w_s(z) - w_{c₀}(E)| ≤ slowWConst · d`, `d = |x - E| + h + (c₀ - s)`
  (uniform Lipschitz bound `freshDyson_window_lipschitz` at the real point `E`).
* **`gamma_relative_slow`**: `|q*Im M_s(z)q / Im m_s(z) - q*Γq| ≤ slowConst · d · q*Γq`,
  `slowConst` depending on `(c₀, r₀, s₀, v₀)` only (uniform in `N`, `A`, `F`, `E`, `s`, `z`, `q`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative
open scoped ComplexConjugate

variable {N : ℕ}

theorem resolvent_l2_compare {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {w w₀ : ℂ}
    (hw : 0 < w.im) (hw0 : w₀.im ≠ 0) (q : Fin N → ℂ) :
    l2Norm ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q -
        (F - w₀ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q) ≤
      ‖w - w₀‖ / w.im * l2Norm ((F - w₀ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q) := by
  set R := (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  set R₀ := (F - w₀ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have hid := hermitian_resolvent_sub hF hw.ne' hw0
  have e : R *ᵥ q - R₀ *ᵥ q = (w - w₀) • (R *ᵥ (R₀ *ᵥ q)) := by
    rw [← Matrix.sub_mulVec, hid, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  rw [e, l2Norm_eq_sqrt_nsq, nsq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have h := l2Norm_resolvent_le hF hw.ne' (R₀ *ᵥ q)
  rw [abs_of_pos hw] at h
  rw [← l2Norm_eq_sqrt_nsq, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

theorem nsq_compare_rel {u u₀ : Fin N → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : l2Norm (u - u₀) ≤ δ * l2Norm u₀) :
    |nsq u - nsq u₀| ≤ δ * (2 + δ) * nsq u₀ := by
  have hu := nsq_nonneg u
  have hu0 := nsq_nonneg u₀
  set a := l2Norm u
  set b := l2Norm u₀
  have ha : a ^ 2 = nsq u := by simp only [a, l2Norm_eq_sqrt_nsq]; exact Real.sq_sqrt hu
  have hb : b ^ 2 = nsq u₀ := by simp only [b, l2Norm_eq_sqrt_nsq]; exact Real.sq_sqrt hu0
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have h1 : a ≤ b + δ * b := by
    have := sqrt_nsq_add_le (u - u₀) u₀
    rw [sub_add_cancel] at this
    simp only [a, b, l2Norm_eq_sqrt_nsq] at h ⊢
    linarith
  have h2 : b ≤ a + δ * b := by
    have := sqrt_nsq_add_le u (u₀ - u)
    rw [add_sub_cancel] at this
    have e : nsq (u₀ - u) = nsq (u - u₀) := by
      rw [show u₀ - u = (-1 : ℂ) • (u - u₀) by module, nsq_smul]; simp
    rw [e] at this
    simp only [a, b, l2Norm_eq_sqrt_nsq] at h ⊢
    linarith
  have hδb : 0 ≤ δ * b := mul_nonneg hδ hb0
  rw [← ha, ← hb, abs_le]
  constructor <;> nlinarith [hδb]

/-- `slowWConst = 1 + 1/(κ v₀) + c₀ L (1 + 1/√κ)`, `κ = c₀ - s₀`, `L = dysonLipConst`. -/
def slowWConst (c₀ s₀ v₀ : ℝ) : ℝ :=
  1 + 1 / ((c₀ - s₀) * v₀) + c₀ * dysonLipConst c₀ s₀ v₀ * (1 + 1 / Real.sqrt (c₀ - s₀))

theorem slowWConst_nonneg {c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) :
    0 ≤ slowWConst c₀ s₀ v₀ := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have : 0 < c₀ - s₀ := by linarith
  unfold slowWConst
  have := dysonLipConst_nonneg c₀ s₀ v₀
  positivity

/-- `|w_s(z) - w_{c₀}(E)| ≤ slowWConst · (|x - E| + h + (c₀ - s))`. -/
theorem freshW_sub_le (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀) {s : ℝ}
    (hs : s ∈ Icc (c₀ - s₀) c₀) {z : ℂ} (hx : |z.re - E| ≤ r₀) (hz : 0 ≤ z.im) (hz1 : z.im ≤ 1) :
    ‖freshW F s z - freshW F c₀ (E : ℂ)‖ ≤
      slowWConst c₀ s₀ v₀ * (|z.re - E| + z.im + (c₀ - s)) := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < c₀ - s₀ := by linarith
  have hc' : c₀ ∈ Icc (c₀ - s₀) c₀ := ⟨by linarith, le_rfl⟩
  have hE : |((E : ℂ)).re - E| ≤ r₀ := by simp [hr0.le]
  have hlip := freshDyson_window_lipschitz hN hK' hC hs hc' hx hE hz hz1 (by simp) (by simp)
  set d := |z.re - E| + z.im + (c₀ - s)
  have hd1 : |z.re - E| ≤ d := by simp only [d]; linarith [hs.2]
  have hd2 : z.im ≤ d := by simp only [d]; linarith [abs_nonneg (z.re - E), hs.2]
  have hd3 : |s - c₀| ≤ d := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hs.2])]
    simp only [d]; linarith [abs_nonneg (z.re - E)]
  have hzE : ‖z - (E : ℂ)‖ ≤ 2 * d := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [abs_of_nonneg hz]; linarith
  have hzE1 : ‖z - (E : ℂ)‖ ≤ |z.re - E| + z.im := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [abs_of_nonneg hz]
  have hm := (fresh_regular_bounds hC.2.2 hs hx hz hz1).1
  have hσ0 : 0 < s := lt_of_lt_of_le hκ hs.1
  have hmn : ‖freshDyson F s z‖ ≤ 1 / ((c₀ - s₀) * v₀) := by
    have h := freshDyson_norm_le hC.1 hN hσ0 hz (lt_of_lt_of_le hv0 hm)
    refine h.trans ?_
    rw [freshW_im, one_div]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [hs.1]
  set m := freshDyson F s z
  set m₀ := freshDyson F c₀ (E : ℂ)
  have e : freshW F s z - freshW F c₀ (E : ℂ) =
      (z - (E : ℂ)) + ((s : ℂ) - c₀) * m + (c₀ : ℂ) * (m - m₀) := by
    simp only [freshW, m, m₀]; ring
  have hL := dysonLipConst_nonneg c₀ s₀ v₀
  have hsq : 0 < Real.sqrt (c₀ - s₀) := Real.sqrt_pos.2 hκ
  rw [e]
  have t1 : ‖((s : ℂ) - c₀) * m‖ ≤ d * (1 / ((c₀ - s₀) * v₀)) := by
    rw [norm_mul, show ((s : ℂ) - c₀) = ((s - c₀ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul hd3 hmn (norm_nonneg _) ((abs_nonneg _).trans hd3)
  have t2 : ‖(c₀ : ℂ) * (m - m₀)‖ ≤ c₀ * dysonLipConst c₀ s₀ v₀ *
      (1 + 1 / Real.sqrt (c₀ - s₀)) * d := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    have : ‖z - (E : ℂ)‖ + |s - c₀| / Real.sqrt (c₀ - s₀) ≤ (1 + 1 / Real.sqrt (c₀ - s₀)) * d := by
      have : |s - c₀| / Real.sqrt (c₀ - s₀) ≤ d / Real.sqrt (c₀ - s₀) :=
        div_le_div_of_nonneg_right hd3 hsq.le
      have h' : ‖z - (E : ℂ)‖ ≤ d := hzE1.trans (by simp only [d]; linarith [hs.2])
      have : (1 + 1 / Real.sqrt (c₀ - s₀)) * d = d + d / Real.sqrt (c₀ - s₀) := by ring
      linarith
    calc c₀ * ‖m - m₀‖ ≤ c₀ * (dysonLipConst c₀ s₀ v₀ *
          (‖z - (E : ℂ)‖ + |s - c₀| / Real.sqrt (c₀ - s₀))) :=
          mul_le_mul_of_nonneg_left hlip hc0.le
      _ ≤ c₀ * (dysonLipConst c₀ s₀ v₀ * ((1 + 1 / Real.sqrt (c₀ - s₀)) * d)) := by gcongr
      _ = _ := by ring
  have t0 : ‖z - (E : ℂ)‖ ≤ d := hzE1.trans (by simp only [d]; linarith [hs.2])
  calc ‖(z - (E : ℂ)) + ((s : ℂ) - c₀) * m + (c₀ : ℂ) * (m - m₀)‖
      ≤ ‖z - (E : ℂ)‖ + ‖((s : ℂ) - c₀) * m‖ + ‖(c₀ : ℂ) * (m - m₀)‖ := norm_add₃_le
    _ ≤ d + d * (1 / ((c₀ - s₀) * v₀)) +
          c₀ * dysonLipConst c₀ s₀ v₀ * (1 + 1 / Real.sqrt (c₀ - s₀)) * d := by linarith
    _ = slowWConst c₀ s₀ v₀ * d := by unfold slowWConst; ring

/-- `C₁ = slowWConst/(κ v₀)`. -/
def slowC1 (c₀ s₀ v₀ : ℝ) : ℝ := slowWConst c₀ s₀ v₀ / ((c₀ - s₀) * v₀)

/-- `d̄ = r₀ + 1 + s₀`, `slowConst = (1/v₀ + 1)(1 + C₁ d̄)²/c₀ + C₁(2 + C₁ d̄)`. -/
def slowConst (c₀ r₀ s₀ v₀ : ℝ) : ℝ :=
  (1 / v₀ + 1) * (1 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀)) ^ 2 / c₀ +
    slowC1 c₀ s₀ v₀ * (2 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀))

theorem slowConst_nonneg {c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) :
    0 ≤ slowConst c₀ r₀ s₀ v₀ := by
  have hW := slowWConst_nonneg hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have : 0 < c₀ - s₀ := by linarith
  have : 0 ≤ slowC1 c₀ s₀ v₀ := by unfold slowC1; positivity
  unfold slowConst
  positivity

/-- **Slow variation.**
`|q*Im M_s(z)q / Im m_s(z) - q*Γq| ≤ slowConst · (|x - E| + h + (c₀ - s)) · q*Γq`. -/
theorem gamma_relative_slow (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} {A c₀ E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀) {s : ℝ}
    (hs : s ∈ Icc (c₀ - s₀) c₀) {z : ℂ} (hx : |z.re - E| ≤ r₀) (hz : 0 ≤ z.im) (hz1 : z.im ≤ 1)
    (q : Fin N → ℂ) :
    |(star q ⬝ᵥ (freshM F s z *ᵥ q)).im / (freshDyson F s z).im -
        quadForm (freshGamma F c₀ E) q| ≤
      slowConst c₀ r₀ s₀ v₀ * (|z.re - E| + z.im + (c₀ - s)) * quadForm (freshGamma F c₀ E) q := by
  have hK' := hK
  have hW := freshW_sub_le hN hK' hC hs hx hz hz1
  have hW0 := slowWConst_nonneg hK'
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ : 0 < c₀ - s₀ := by linarith
  have hF := hC.1
  have hσ0 : 0 < s := lt_of_lt_of_le hκ hs.1
  have hm := (fresh_regular_bounds hC.2.2 hs hx hz hz1).1
  have hmp : 0 < (freshDyson F s z).im := lt_of_lt_of_le hv0 hm
  have hc' : c₀ ∈ Icc (c₀ - s₀) c₀ := ⟨by linarith, le_rfl⟩
  have hE : |((E : ℂ)).re - E| ≤ r₀ := by simp [hr0.le]
  have hm₀ := (fresh_regular_bounds hC.2.2 hc' hE (by simp) (by simp)).1
  set w := freshW F s z
  set w₀ := freshW F c₀ (E : ℂ)
  have hwim : w.im = z.im + s * (freshDyson F s z).im := freshW_im F s z
  have hw0im : w₀.im = c₀ * (freshDyson F c₀ (E : ℂ)).im := by simp [w₀, freshW_im]
  have hwpos : (c₀ - s₀) * v₀ ≤ w.im := by rw [hwim]; nlinarith [hs.1]
  have hw0pos : 0 < w₀.im := by rw [hw0im]; exact mul_pos hc0 (lt_of_lt_of_le hv0 hm₀)
  set u := freshM F s z *ᵥ q
  set u₀ := freshM F c₀ (E : ℂ) *ᵥ q
  have hγ : quadForm (freshGamma F c₀ E) q = c₀ * nsq u₀ := freshGamma_quad_eq hF c₀ E q
  have hqim : (star q ⬝ᵥ (freshM F s z *ᵥ q)).im =
      (z.im + s * (freshDyson F s z).im) * nsq u :=
    freshM_quad_im hF (lt_of_lt_of_le (mul_pos hκ hv0) hwpos).ne' q
  set d := |z.re - E| + z.im + (c₀ - s)
  have hd0 : 0 ≤ d := by simp only [d]; linarith [abs_nonneg (z.re - E), hs.2]
  have hdbar : d ≤ r₀ + 1 + s₀ := by simp only [d]; linarith [hs.1]
  have hC₁ : 0 ≤ slowC1 c₀ s₀ v₀ := by unfold slowC1; positivity
  -- relative closeness of `u` and `u₀`
  set δ := ‖w - w₀‖ / w.im
  have hδ0 : 0 ≤ δ := div_nonneg (norm_nonneg _) (by linarith [mul_pos hκ hv0])
  have hδ : δ ≤ slowC1 c₀ s₀ v₀ * d := by
    simp only [δ, slowC1]
    rw [div_le_iff₀ (by linarith [mul_pos hκ hv0])]
    calc ‖w - w₀‖ ≤ slowWConst c₀ s₀ v₀ * d := hW
      _ = slowWConst c₀ s₀ v₀ / ((c₀ - s₀) * v₀) * d * ((c₀ - s₀) * v₀) := by field_simp
      _ ≤ slowWConst c₀ s₀ v₀ / ((c₀ - s₀) * v₀) * d * w.im := by
          gcongr
  have hδbar : δ ≤ slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀) := hδ.trans (mul_le_mul_of_nonneg_left hdbar hC₁)
  have hcl : l2Norm (u - u₀) ≤ δ * l2Norm u₀ :=
    resolvent_l2_compare (w := w) (w₀ := w₀) hF (lt_of_lt_of_le (mul_pos hκ hv0) hwpos)
      hw0pos.ne' q
  have hn := nsq_compare_rel hδ0 hcl
  have hu0 := nsq_nonneg u₀
  have hu := nsq_nonneg u
  -- `nsq u ≤ (1 + δ)² nsq u₀`
  have hub : nsq u ≤ (1 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀)) ^ 2 * nsq u₀ := by
    have h1 : nsq u ≤ nsq u₀ + δ * (2 + δ) * nsq u₀ := by linarith [(abs_le.1 hn).2]
    have h2 : (1 + δ) ^ 2 ≤ (1 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith
  -- the ratio
  have hratio : (star q ⬝ᵥ (freshM F s z *ᵥ q)).im / (freshDyson F s z).im =
      (z.im / (freshDyson F s z).im + s) * nsq u := by
    rw [hqim]; field_simp
  have hfac : |z.im / (freshDyson F s z).im + s - c₀| ≤ (1 / v₀ + 1) * d := by
    have h1 : z.im / (freshDyson F s z).im ≤ z.im / v₀ :=
      div_le_div_of_nonneg_left hz hv0 hm
    have h0 : 0 ≤ z.im / (freshDyson F s z).im := div_nonneg hz hmp.le
    have hzd : z.im ≤ d := by simp only [d]; linarith [abs_nonneg (z.re - E), hs.2]
    have hcs : c₀ - s ≤ d := by simp only [d]; linarith [abs_nonneg (z.re - E)]
    have hzv : z.im / v₀ ≤ d / v₀ := div_le_div_of_nonneg_right hzd hv0.le
    have hdv : 0 ≤ d / v₀ := div_nonneg hd0 hv0.le
    have e : (1 / v₀ + 1) * d = d / v₀ + d := by ring
    have hs2 := hs.2
    rw [e, abs_le]; constructor <;> linarith
  rw [hratio, hγ]
  have e : (z.im / (freshDyson F s z).im + s) * nsq u - c₀ * nsq u₀ =
      (z.im / (freshDyson F s z).im + s - c₀) * nsq u + c₀ * (nsq u - nsq u₀) := by ring
  rw [e]
  have hA : |(z.im / (freshDyson F s z).im + s - c₀) * nsq u| ≤
      (1 / v₀ + 1) * d * ((1 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀)) ^ 2 * nsq u₀) := by
    rw [abs_mul, abs_of_nonneg hu]
    exact mul_le_mul hfac hub hu (by positivity)
  have hB : |c₀ * (nsq u - nsq u₀)| ≤ c₀ * (slowC1 c₀ s₀ v₀ * d * (2 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀)) * nsq u₀) := by
    rw [abs_mul, abs_of_pos hc0]
    refine mul_le_mul_of_nonneg_left (hn.trans ?_) hc0.le
    refine mul_le_mul_of_nonneg_right (mul_le_mul hδ (by linarith) (by linarith) (by positivity))
      hu0
  calc |(z.im / (freshDyson F s z).im + s - c₀) * nsq u + c₀ * (nsq u - nsq u₀)|
      ≤ |(z.im / (freshDyson F s z).im + s - c₀) * nsq u| + |c₀ * (nsq u - nsq u₀)| :=
        abs_add_le _ _
    _ ≤ (1 / v₀ + 1) * d * ((1 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀)) ^ 2 * nsq u₀) +
          c₀ * (slowC1 c₀ s₀ v₀ * d * (2 + slowC1 c₀ s₀ v₀ * (r₀ + 1 + s₀)) * nsq u₀) := add_le_add hA hB
    _ = slowConst c₀ r₀ s₀ v₀ * d * (c₀ * nsq u₀) := by
        unfold slowConst; field_simp

end BlockBand.Palm.MomentFlow
