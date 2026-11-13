module

public import BlockBand.Critical.RelativeVectors.Coarse
public import BlockBand.Palm.MomentFlow.AvgDyson
public import BlockBand.Palm.MomentFlow.LocalSpectral

/-!
# Relative stability of the covariance

Deterministic. *Domain:* `N ≥ 1`, fixed `A`, `FreshConstants c r₀ s₀ v₀`, `F` in
`FreshClass F A c E r₀ s₀ v₀`, `s ∈ [c - s₀, c]`, real `x` with `|x - E| ≤ r₀`.
*Uniformity:* the constant `gammaShiftConst c r₀ s₀ v₀` depends on the fixed constants only
(uniform in `N`, `A`, `F`, `E`, `s`, `x`, `q` and the frame).

* `relGamma_quad_eq`: `Im(q^*M_s(x)q)/Im m_s(x) = q^*Γ(s,x)q` with `Γ(s,x) = freshGamma F s x
  = s|F - x - s m_s(x)|^{-2}`; so `Γ_i(s) = V^* freshGamma F s λ_i(s) V`.
* `nsq_sub_le_of_close`: `u = v + δy`, `|δ|²‖y‖² ≤ ε²‖v‖²` give `|‖u‖² - ‖v‖²| ≤ (2ε+ε²)‖v‖²`.
* `frame_gamma_shift_le`: for `V^*ΓV = I_r` and every `p ∈ ℂ^r`,
  `|p^*(Γ_i(s) - I_r)p| ≤ C (|x - E| + t) ‖p‖²` whenever `c - t ≤ s` (the quadratic-form, hence
  operator-norm, form of the third line of the interval bound, at `x = λ_i(s)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative

variable {N r : ℕ}

/-- `Im(q^*M_s(x)q)/Im m_s(x) = q^*Γ(s,x)q` for real `x` and `Im m_s(x) > 0`. -/
theorem relGamma_quad_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s x : ℝ}
    (hs : 0 < s) (hm : 0 < (freshDyson F s x).im) (q : Fin N → ℂ) :
    (star q ⬝ᵥ (freshM F s x *ᵥ q)).im / (freshDyson F s x).im =
      quadForm (freshGamma F s x) q := by
  have hw : (freshW F s (x : ℂ)).im ≠ 0 := by
    rw [freshW_im]; simp only [Complex.ofReal_im, zero_add]; exact (mul_pos hs hm).ne'
  rw [freshM_quad_im hF hw q, freshGamma_quad_eq hF s x q]
  simp only [Complex.ofReal_im, zero_add]
  field_simp

/-- Perturbation of a squared Euclidean norm. -/
theorem nsq_sub_le_of_close {u v y : Fin N → ℂ} {δ : ℂ} {ε : ℝ} (hu : u = v + δ • y)
    (hε0 : 0 ≤ ε) (hy : ‖δ‖ ^ 2 * nsq y ≤ ε ^ 2 * nsq v) :
    |nsq u - nsq v| ≤ (2 * ε + ε ^ 2) * nsq v := by
  set a := ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖
  set b := ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖
  set d := ‖δ‖ * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin N))‖
  have hua : nsq u = a ^ 2 := nsq_eq_euclidean u
  have hvb : nsq v = b ^ 2 := nsq_eq_euclidean v
  have hyd : ‖δ‖ ^ 2 * nsq y = d ^ 2 := by rw [nsq_eq_euclidean y]; ring
  have hsum : (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N)) =
      WithLp.toLp 2 v + δ • WithLp.toLp 2 y := by
    rw [hu]; rfl
  have hd0 : 0 ≤ d := by positivity
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hdn : d = ‖δ • (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin N))‖ := by rw [norm_smul]
  have hab : a ≤ b + d := by
    have ha : a = ‖WithLp.toLp 2 v + δ • (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin N))‖ := by
      rw [← hsum]
    rw [ha, hdn]; exact norm_add_le _ _
  have hba : b ≤ a + d := by
    have hb : b = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N)) -
        δ • (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin N))‖ := by
      rw [hsum, add_sub_cancel_right]
    rw [hb, hdn]; exact norm_sub_le _ _
  have hdε : d ≤ ε * b := by
    have h2 : d ^ 2 ≤ (ε * b) ^ 2 := by rw [← hyd, mul_pow, ← hvb]; exact hy
    exact (pow_le_pow_iff_left₀ hd0 (by positivity) (by norm_num)).1 h2
  rw [hua, hvb, abs_le]
  constructor
  · rcases le_or_gt b a with h | h
    · nlinarith
    · nlinarith
  · nlinarith

/-- The constant of `gamma_shift_le`. With `κ' = c - s₀`, `κ = κ'v₀`,
`L = 1 + c(1 + 1/√κ')/(2κ'²v₀²) + 1/κ`, `E₁ = L(r₀ + s₀)/κ`:
`C = (c(2 + E₁)L/κ + 1)/c`. -/
def gammaShiftConst (c r₀ s₀ v₀ : ℝ) : ℝ :=
  let κ' := c - s₀
  let κ := κ' * v₀
  let L := 1 + c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) + 1 / κ
  let E₁ := L * (r₀ + s₀) / κ
  (c * (2 + E₁) * L / κ + 1) / c

/-- **Relative stability of `Γ`** (third line of the interval bound, deterministic form). -/
theorem gamma_shift_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀) {s x : ℝ}
    (hs : s ∈ Icc (c - s₀) c) (hx : |x - E| ≤ r₀) (q : Fin N → ℂ) :
    |quadForm (freshGamma F s x) q - quadForm (freshGamma F c E) q| ≤
      gammaShiftConst c r₀ s₀ v₀ * (|x - E| + (c - s)) * quadForm (freshGamma F c E) q := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hF := hC.1
  set κ' := c - s₀ with hκ'
  have hκ'0 : 0 < κ' := by linarith
  set κ := κ' * v₀ with hκ
  have hκ0 : 0 < κ := mul_pos hκ'0 hv0
  set L := 1 + c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) + 1 / κ with hL
  set E₁ := L * (r₀ + s₀) / κ with hE₁
  have hspos : 0 < s := lt_of_lt_of_le hκ'0 hs.1
  -- Dyson bounds
  have hcreg : c ∈ Icc (c - s₀) c := ⟨by linarith, le_rfl⟩
  obtain ⟨hm1, -⟩ := fresh_regular_bounds hC.2.2 hs (z := (x : ℂ)) (by simpa using hx)
    (by simp) (by simp)
  obtain ⟨hm01, -⟩ := fresh_regular_bounds hC.2.2 hcreg (z := (E : ℂ)) (by simp [hr0.le])
    (by simp) (by simp)
  set m := freshDyson F s x with hmdef
  set m₀ := freshDyson F c E with hm₀def
  set w := freshW F s (x : ℂ) with hwdef
  set w₀ := freshW F c (E : ℂ) with hw₀def
  have hwim : w.im = s * m.im := by
    rw [hwdef, freshW_im]; simp only [Complex.ofReal_im, zero_add]; rfl
  have hw₀im : w₀.im = c * m₀.im := by
    rw [hw₀def, freshW_im]; simp only [Complex.ofReal_im, zero_add]; rfl
  have hwκ : κ ≤ w.im := by rw [hwim]; exact mul_le_mul hs.1 hm1 hv0.le hspos.le
  have hw₀κ : κ ≤ w₀.im := by rw [hw₀im]; exact mul_le_mul (by linarith) hm01 hv0.le hc0.le
  have hwpos : 0 < w.im := lt_of_lt_of_le hκ0 hwκ
  have hw₀pos : 0 < w₀.im := lt_of_lt_of_le hκ0 hw₀κ
  -- Lipschitz bound on the shift
  have hlip := dyson_stable_lipschitz hF hN hκ'0 hv0 hs.1 (le_of_lt (by linarith) : κ' ≤ c)
    (z := (x : ℂ)) (z' := (E : ℂ)) (by simp) (by simp) hm1 hm01
  have hm₀n : ‖m₀‖ ≤ 1 / κ := by
    have := freshDyson_norm_le hF hN hc0 (z := (E : ℂ)) (by simp) (lt_of_lt_of_le hv0 hm01)
    refine this.trans ?_
    rw [one_div]; exact inv_anti₀ hκ0 hw₀κ
  set δ := |x - E| + (c - s) with hδ
  have hcs : 0 ≤ c - s := by linarith [hs.2]
  have hδ0 : 0 ≤ δ := by positivity
  have hxE : ‖((x : ℂ) - (E : ℂ))‖ = |x - E| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hsqrt : 0 < Real.sqrt κ' := Real.sqrt_pos.2 hκ'0
  have hww : ‖w - w₀‖ ≤ L * δ := by
    have e : w - w₀ = ((x : ℂ) - E) + ((s : ℂ) * (m - m₀) + ((s : ℂ) - c) * m₀) := by
      rw [hwdef, hw₀def]; unfold freshW; ring
    rw [e]
    have h1 : ‖(s : ℂ) * (m - m₀)‖ ≤ c * ((|x - E| + (c - s) / Real.sqrt κ') /
        (2 * κ' ^ 2 * v₀ ^ 2)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
      have := hlip
      rw [hxE, abs_sub_comm s c, abs_of_nonneg hcs] at this
      exact mul_le_mul hs.2 this (norm_nonneg _) hc0.le
    have h2 : ‖((s : ℂ) - c) * m₀‖ ≤ (c - s) * (1 / κ) := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
        abs_of_nonneg hcs]
      exact mul_le_mul_of_nonneg_left hm₀n hcs
    have h3 : c * ((|x - E| + (c - s) / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2)) ≤
        c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) * δ := by
      have hden : 0 < 2 * κ' ^ 2 * v₀ ^ 2 := by positivity
      rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden]
      have : |x - E| + (c - s) / Real.sqrt κ' ≤ (1 + 1 / Real.sqrt κ') * δ := by
        rw [hδ]
        have ha : 0 ≤ |x - E| := abs_nonneg _
        have hb : (c - s) / Real.sqrt κ' = 1 / Real.sqrt κ' * (c - s) := by ring
        have hp : 0 ≤ 1 / Real.sqrt κ' := by positivity
        nlinarith
      nlinarith
    calc ‖((x : ℂ) - E) + ((s : ℂ) * (m - m₀) + ((s : ℂ) - c) * m₀)‖
        ≤ ‖(x : ℂ) - E‖ + (‖(s : ℂ) * (m - m₀)‖ + ‖((s : ℂ) - c) * m₀‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ |x - E| + (c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) * δ +
            (c - s) * (1 / κ)) := by
          rw [hxE]; exact add_le_add le_rfl (add_le_add (h1.trans h3) h2)
      _ ≤ L * δ := by
          rw [hL, hδ]
          have hp : 0 ≤ c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) := by positivity
          have hq : 0 ≤ 1 / κ := by positivity
          have ha : 0 ≤ |x - E| := abs_nonneg _
          nlinarith
  -- the perturbation of the resolvent vector
  set R := (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  set R₀ := (F - w₀ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have hid := hermitian_resolvent_sub hF hwpos.ne' hw₀pos.ne'
  have hRq : R *ᵥ q = R₀ *ᵥ q + (w - w₀) • (R *ᵥ (R₀ *ᵥ q)) := by
    have : R = R₀ + (w - w₀) • (R * R₀) := by rw [← hid]; abel
    calc R *ᵥ q = (R₀ + (w - w₀) • (R * R₀)) *ᵥ q := by rw [← this]
      _ = _ := by rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  set ε := ‖w - w₀‖ / w.im with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hy : ‖w - w₀‖ ^ 2 * nsq (R *ᵥ (R₀ *ᵥ q)) ≤ ε ^ 2 * nsq (R₀ *ᵥ q) := by
    have hop := hermitian_resolvent_nsq_le hF hwpos.ne' (R₀ *ᵥ q)
    calc ‖w - w₀‖ ^ 2 * nsq (R *ᵥ (R₀ *ᵥ q))
        ≤ ‖w - w₀‖ ^ 2 * ((w.im ^ 2)⁻¹ * nsq (R₀ *ᵥ q)) :=
          mul_le_mul_of_nonneg_left hop (by positivity)
      _ = ε ^ 2 * nsq (R₀ *ᵥ q) := by rw [hεdef, div_pow]; ring
  have hpert := nsq_sub_le_of_close hRq hε0 hy
  have hεL : ε ≤ L / κ * δ := by
    rw [hεdef, div_le_iff₀ hwpos]
    have : L / κ * δ * κ ≤ L / κ * δ * w.im :=
      mul_le_mul_of_nonneg_left hwκ (by positivity)
    have e : L / κ * δ * κ = L * δ := by field_simp
    linarith
  have hδb : δ ≤ r₀ + s₀ := by rw [hδ]; linarith [hs.1]
  have hεE : ε ≤ E₁ := by
    refine hεL.trans ?_
    rw [hE₁, mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hδb (by positivity)
  -- assemble
  have hΓs : quadForm (freshGamma F s x) q = s * nsq (R *ᵥ q) := freshGamma_quad_eq hF s x q
  have hΓ : quadForm (freshGamma F c E) q = c * nsq (R₀ *ᵥ q) := freshGamma_quad_eq hF c E q
  rw [hΓs, hΓ]
  set U := nsq (R *ᵥ q)
  set Y := nsq (R₀ *ᵥ q)
  have hY : 0 ≤ Y := nsq_nonneg _
  have hE0 : 0 ≤ E₁ := hε0.trans hεE
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hε2 : 2 * ε + ε ^ 2 ≤ (2 + E₁) * (L / κ) * δ := by
    have : ε ^ 2 ≤ E₁ * ε := by rw [sq]; exact mul_le_mul_of_nonneg_right hεE hε0
    have h2 : (2 + E₁) * ε ≤ (2 + E₁) * (L / κ * δ) :=
      mul_le_mul_of_nonneg_left hεL (by positivity)
    linarith
  have hkey : |s * U - c * Y| ≤ s * ((2 * ε + ε ^ 2) * Y) + (c - s) * Y := by
    have e : s * U - c * Y = s * (U - Y) - (c - s) * Y := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hspos, abs_mul, abs_of_nonneg hcs, abs_of_nonneg hY]
    exact add_le_add (mul_le_mul_of_nonneg_left hpert hspos.le) le_rfl
  refine hkey.trans ?_
  have hconst : gammaShiftConst c r₀ s₀ v₀ * c = c * (2 + E₁) * L / κ + 1 := by
    unfold gammaShiftConst
    simp only []
    rw [← hκ', ← hκ, ← hL, ← hE₁]
    field_simp
  have hgoal : gammaShiftConst c r₀ s₀ v₀ * δ * (c * Y) =
      (c * (2 + E₁) * L / κ + 1) * δ * Y := by
    rw [← hconst]; ring
  rw [hgoal]
  have h1 : s * ((2 * ε + ε ^ 2) * Y) ≤ c * ((2 + E₁) * (L / κ) * δ) * Y := by
    have := mul_le_mul_of_nonneg_right hε2 hY
    calc s * ((2 * ε + ε ^ 2) * Y) ≤ c * ((2 * ε + ε ^ 2) * Y) :=
          mul_le_mul_of_nonneg_right hs.2 (by positivity)
      _ ≤ c * ((2 + E₁) * (L / κ) * δ * Y) := mul_le_mul_of_nonneg_left this hc0.le
      _ = _ := by ring
  have h2 : (c - s) * Y ≤ δ * Y := by
    apply mul_le_mul_of_nonneg_right _ hY
    rw [hδ]; linarith [abs_nonneg (x - E)]
  have e3 : (c * (2 + E₁) * L / κ + 1) * δ * Y =
      c * ((2 + E₁) * (L / κ) * δ) * Y + δ * Y := by ring
  linarith

/-- `q^*Γq` of a frame image is `‖p‖²` when `V^*ΓV = I_r`. -/
theorem quadForm_frame {Γ : Matrix (Fin N) (Fin N) ℂ} {V : Matrix (Fin N) (Fin r) ℂ}
    (hV : Vᴴ * Γ * V = 1) (p : Fin r → ℂ) : quadForm Γ (V *ᵥ p) = nsq p := by
  unfold quadForm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hV,
    one_mulVec, star_dotProduct_self_eq, Complex.ofReal_re]

/-- **Third line of the interval bound** in the frame, quadratic-form (hence operator-norm)
form: `|p^*(V^*Γ(s,x)V - I_r)p| ≤ C(|x - E| + t)‖p‖²` for `c - t ≤ s ≤ c`. -/
theorem frame_gamma_shift_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1) {s x t : ℝ}
    (hs : s ∈ Icc (c - s₀) c) (hst : c - t ≤ s) (hx : |x - E| ≤ r₀) (p : Fin r → ℂ) :
    |quadForm (freshGamma F s x) (V *ᵥ p) - nsq p| ≤
      gammaShiftConst c r₀ s₀ v₀ * (|x - E| + t) * nsq p := by
  have h := gamma_shift_le hN hK hC hs hx (V *ᵥ p)
  rw [quadForm_frame hV] at h
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ?_)
    (nsq_nonneg p))
  have hκ'0 : 0 < c - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
  have hv0 := hK.2.2.2.2.2
  have hc0 := hK.1
  have hr0 := hK.2.2.1
  have hs0 := hK.2.2.2.1
  unfold gammaShiftConst
  positivity

end BlockBand.Critical.RelativeVectors
