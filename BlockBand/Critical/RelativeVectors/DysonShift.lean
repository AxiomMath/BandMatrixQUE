module

public import BlockBand.Critical.RelativeVectors.GammaShift

/-!
# Relative stability of `M_s(z)` in `(s, z)`

Deterministic bounds used for the middle line of the interval bound.
*Domain:* `N ≥ 1`, `FreshConstants c r₀ s₀ v₀`, `F` in `FreshClass`, two points
`(s₁, z₁)`, `(s₂, z₂)` with `s_i ∈ [c - s₀, c]`, `|Re z_i - E| ≤ r₀`, `0 ≤ Im z_i ≤ 1`.
*Uniformity:* the constants depend on `(c, r₀, s₀, v₀)` only.

* `rnsq_shift_le`: `|‖M_{s₁}(z₁)q‖² - ‖M_{s₂}(z₂)q‖²| ≤ C (|z₁ - z₂| + |s₁ - s₂|) ‖M_{s₂}(z₂)q‖²`
  (`C = dysonShiftConst`), by the same argument as `gamma_shift_le` (resolvent identity at the
  Dyson shifts, Lipschitz bound of the Dyson root).
* `rnsq_le_gamma`: `‖M_s(z)q‖² ≤ C' q^*Γq` (`C' = dysonGammaConst`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative

variable {N : ℕ}

/-- The Lipschitz constant of the Dyson shift `w = z + s m_s(z)`. -/
def dysonShiftLip (c s₀ v₀ : ℝ) : ℝ :=
  1 + c * (1 + 1 / Real.sqrt (c - s₀)) / (2 * (c - s₀) ^ 2 * v₀ ^ 2) + 1 / ((c - s₀) * v₀)

/-- The constant of `rnsq_shift_le`. -/
def dysonShiftConst (c r₀ s₀ v₀ : ℝ) : ℝ :=
  (2 + dysonShiftLip c s₀ v₀ * (2 * r₀ + 1 + s₀) / ((c - s₀) * v₀)) *
    (dysonShiftLip c s₀ v₀ / ((c - s₀) * v₀))

theorem dysonShiftConst_nonneg {c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    0 ≤ dysonShiftConst c r₀ s₀ v₀ := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hκ' : 0 < c - s₀ := by linarith
  unfold dysonShiftConst dysonShiftLip
  positivity

/-- **Relative stability of `‖M_s(z)q‖²`.** -/
theorem rnsq_shift_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀) {s₁ s₂ : ℝ}
    (hs₁ : s₁ ∈ Icc (c - s₀) c) (hs₂ : s₂ ∈ Icc (c - s₀) c) {z₁ z₂ : ℂ}
    (hx₁ : |z₁.re - E| ≤ r₀) (hη₁ : 0 ≤ z₁.im) (hη₁' : z₁.im ≤ 1)
    (hx₂ : |z₂.re - E| ≤ r₀) (hη₂ : 0 ≤ z₂.im) (hη₂' : z₂.im ≤ 1) (q : Fin N → ℂ) :
    |nsq (freshM F s₁ z₁ *ᵥ q) - nsq (freshM F s₂ z₂ *ᵥ q)| ≤
      dysonShiftConst c r₀ s₀ v₀ * (‖z₁ - z₂‖ + |s₁ - s₂|) * nsq (freshM F s₂ z₂ *ᵥ q) := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hF := hC.1
  set κ' := c - s₀ with hκ'
  have hκ'0 : 0 < κ' := by linarith
  set κ := κ' * v₀ with hκ
  have hκ0 : 0 < κ := mul_pos hκ'0 hv0
  set L := dysonShiftLip c s₀ v₀ with hL
  have hL' : L = 1 + c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) + 1 / κ := rfl
  have hs₁pos : 0 < s₁ := lt_of_lt_of_le hκ'0 hs₁.1
  have hs₂pos : 0 < s₂ := lt_of_lt_of_le hκ'0 hs₂.1
  obtain ⟨hm1, -⟩ := fresh_regular_bounds hC.2.2 hs₁ hx₁ hη₁ hη₁'
  obtain ⟨hm2, -⟩ := fresh_regular_bounds hC.2.2 hs₂ hx₂ hη₂ hη₂'
  set m₁ := freshDyson F s₁ z₁ with hm₁def
  set m₂ := freshDyson F s₂ z₂ with hm₂def
  set w₁ := freshW F s₁ z₁ with hw₁def
  set w₂ := freshW F s₂ z₂ with hw₂def
  have hw₁κ : κ ≤ w₁.im := by
    rw [hw₁def, freshW_im]
    have := mul_le_mul hs₁.1 hm1 hv0.le hs₁pos.le
    linarith
  have hw₂κ : κ ≤ w₂.im := by
    rw [hw₂def, freshW_im]
    have := mul_le_mul hs₂.1 hm2 hv0.le hs₂pos.le
    linarith
  have hw₁pos : 0 < w₁.im := lt_of_lt_of_le hκ0 hw₁κ
  have hw₂pos : 0 < w₂.im := lt_of_lt_of_le hκ0 hw₂κ
  have hlip := dyson_stable_lipschitz hF hN hκ'0 hv0 hs₁.1 hs₂.1 hη₁ hη₂ hm1 hm2
  have hm₂n : ‖m₂‖ ≤ 1 / κ := by
    have := freshDyson_norm_le hF hN hs₂pos hη₂ (lt_of_lt_of_le hv0 hm2)
    refine this.trans ?_
    rw [one_div]; exact inv_anti₀ hκ0 hw₂κ
  set δ := ‖z₁ - z₂‖ + |s₁ - s₂| with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hsqrt : 0 < Real.sqrt κ' := Real.sqrt_pos.2 hκ'0
  have hww : ‖w₁ - w₂‖ ≤ L * δ := by
    have e : w₁ - w₂ = (z₁ - z₂) + ((s₁ : ℂ) * (m₁ - m₂) + ((s₁ : ℂ) - s₂) * m₂) := by
      rw [hw₁def, hw₂def]; unfold freshW; ring
    rw [e]
    have h1 : ‖(s₁ : ℂ) * (m₁ - m₂)‖ ≤ c * ((‖z₁ - z₂‖ + |s₁ - s₂| / Real.sqrt κ') /
        (2 * κ' ^ 2 * v₀ ^ 2)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs₁pos]
      exact mul_le_mul hs₁.2 hlip (norm_nonneg _) hc0.le
    have h2 : ‖((s₁ : ℂ) - s₂) * m₂‖ ≤ |s₁ - s₂| * (1 / κ) := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hm₂n (abs_nonneg _)
    have h3 : c * ((‖z₁ - z₂‖ + |s₁ - s₂| / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2)) ≤
        c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) * δ := by
      have hden : 0 < 2 * κ' ^ 2 * v₀ ^ 2 := by positivity
      rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden]
      have : ‖z₁ - z₂‖ + |s₁ - s₂| / Real.sqrt κ' ≤ (1 + 1 / Real.sqrt κ') * δ := by
        rw [hδ]
        have ha : 0 ≤ ‖z₁ - z₂‖ := norm_nonneg _
        have hb0 : 0 ≤ |s₁ - s₂| := abs_nonneg _
        have hb : |s₁ - s₂| / Real.sqrt κ' = 1 / Real.sqrt κ' * |s₁ - s₂| := by ring
        have hp : 0 ≤ 1 / Real.sqrt κ' := by positivity
        nlinarith
      nlinarith
    calc ‖(z₁ - z₂) + ((s₁ : ℂ) * (m₁ - m₂) + ((s₁ : ℂ) - s₂) * m₂)‖
        ≤ ‖z₁ - z₂‖ + (‖(s₁ : ℂ) * (m₁ - m₂)‖ + ‖((s₁ : ℂ) - s₂) * m₂‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ ‖z₁ - z₂‖ + (c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) * δ +
            |s₁ - s₂| * (1 / κ)) := add_le_add le_rfl (add_le_add (h1.trans h3) h2)
      _ ≤ L * δ := by
          rw [hL', hδ]
          have hp : 0 ≤ c * (1 + 1 / Real.sqrt κ') / (2 * κ' ^ 2 * v₀ ^ 2) := by positivity
          have hq : 0 ≤ 1 / κ := by positivity
          have ha : 0 ≤ ‖z₁ - z₂‖ := norm_nonneg _
          have hb : 0 ≤ |s₁ - s₂| := abs_nonneg _
          nlinarith
  -- the perturbation of the resolvent vector
  set R₁ := (F - w₁ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  set R₂ := (F - w₂ • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have hid := hermitian_resolvent_sub hF hw₁pos.ne' hw₂pos.ne'
  have hRq : R₁ *ᵥ q = R₂ *ᵥ q + (w₁ - w₂) • (R₁ *ᵥ (R₂ *ᵥ q)) := by
    have : R₁ = R₂ + (w₁ - w₂) • (R₁ * R₂) := by rw [← hid]; abel
    calc R₁ *ᵥ q = (R₂ + (w₁ - w₂) • (R₁ * R₂)) *ᵥ q := by rw [← this]
      _ = _ := by rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  set ε := ‖w₁ - w₂‖ / w₁.im with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hy : ‖w₁ - w₂‖ ^ 2 * nsq (R₁ *ᵥ (R₂ *ᵥ q)) ≤ ε ^ 2 * nsq (R₂ *ᵥ q) := by
    have hop := hermitian_resolvent_nsq_le hF hw₁pos.ne' (R₂ *ᵥ q)
    calc ‖w₁ - w₂‖ ^ 2 * nsq (R₁ *ᵥ (R₂ *ᵥ q))
        ≤ ‖w₁ - w₂‖ ^ 2 * ((w₁.im ^ 2)⁻¹ * nsq (R₂ *ᵥ q)) :=
          mul_le_mul_of_nonneg_left hop (by positivity)
      _ = ε ^ 2 * nsq (R₂ *ᵥ q) := by rw [hεdef, div_pow]; ring
  have hpert := nsq_sub_le_of_close hRq hε0 hy
  have hεL : ε ≤ L / κ * δ := by
    rw [hεdef, div_le_iff₀ hw₁pos]
    have : L / κ * δ * κ ≤ L / κ * δ * w₁.im :=
      mul_le_mul_of_nonneg_left hw₁κ (by
        have : 0 ≤ L := by rw [hL']; positivity
        positivity)
    have e : L / κ * δ * κ = L * δ := by field_simp
    linarith
  have hz12 : ‖z₁ - z₂‖ ≤ 2 * r₀ + 1 := by
    have h1 : ‖z₁ - z₂‖ ≤ |(z₁ - z₂).re| + |(z₁ - z₂).im| := Complex.norm_le_abs_re_add_abs_im _
    have h2 : |(z₁ - z₂).re| ≤ 2 * r₀ := by
      rw [Complex.sub_re]
      have := abs_sub_le z₁.re E z₂.re
      rw [abs_sub_comm E] at this
      linarith
    have h3 : |(z₁ - z₂).im| ≤ 1 := by
      rw [Complex.sub_im, abs_le]; constructor <;> linarith
    linarith
  have hs12 : |s₁ - s₂| ≤ s₀ := by
    rw [abs_le]; constructor <;> linarith [hs₁.1, hs₁.2, hs₂.1, hs₂.2]
  have hδb : δ ≤ 2 * r₀ + 1 + s₀ := by rw [hδ]; linarith
  have hL0 : 0 ≤ L := by rw [hL']; positivity
  set E₁ := L * (2 * r₀ + 1 + s₀) / κ with hE₁
  have hεE : ε ≤ E₁ := by
    refine hεL.trans ?_
    rw [hE₁, mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hδb (by positivity)
  have hε2 : 2 * ε + ε ^ 2 ≤ (2 + E₁) * (L / κ) * δ := by
    have : ε ^ 2 ≤ E₁ * ε := by rw [sq]; exact mul_le_mul_of_nonneg_right hεE hε0
    have hE0 : 0 ≤ E₁ := hε0.trans hεE
    have h2 : (2 + E₁) * ε ≤ (2 + E₁) * (L / κ * δ) :=
      mul_le_mul_of_nonneg_left hεL (by positivity)
    linarith
  have hconst : dysonShiftConst c r₀ s₀ v₀ = (2 + E₁) * (L / κ) := rfl
  rw [hconst]
  have hY := nsq_nonneg (R₂ *ᵥ q)
  calc |nsq (freshM F s₁ z₁ *ᵥ q) - nsq (freshM F s₂ z₂ *ᵥ q)|
      = |nsq (R₁ *ᵥ q) - nsq (R₂ *ᵥ q)| := rfl
    _ ≤ (2 * ε + ε ^ 2) * nsq (R₂ *ᵥ q) := hpert
    _ ≤ (2 + E₁) * (L / κ) * δ * nsq (R₂ *ᵥ q) := mul_le_mul_of_nonneg_right hε2 hY
    _ = _ := rfl

/-- The constant of `rnsq_le_gamma`. -/
def dysonGammaConst (c r₀ s₀ v₀ : ℝ) : ℝ :=
  (1 + dysonShiftConst c r₀ s₀ v₀ * (r₀ + 1 + s₀)) / c

/-- **`‖M_s(z)q‖² ≤ C' q^*Γq`** on the regularity domain. -/
theorem rnsq_le_gamma {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀) {s : ℝ}
    (hs : s ∈ Icc (c - s₀) c) {z : ℂ} (hx : |z.re - E| ≤ r₀) (hη : 0 ≤ z.im) (hη1 : z.im ≤ 1)
    (q : Fin N → ℂ) :
    nsq (freshM F s z *ᵥ q) ≤ dysonGammaConst c r₀ s₀ v₀ * quadForm (freshGamma F c E) q := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK'
  have hcreg : c ∈ Icc (c - s₀) c := ⟨by linarith, le_rfl⟩
  have h := rnsq_shift_le hN hK hC hs hcreg (z₂ := (E : ℂ)) hx hη hη1 (by simp [hr0.le])
    (by simp) (by simp) q
  have hΓ := freshGamma_quad_eq hC.1 c E q
  have hY := nsq_nonneg (freshM F c (E : ℂ) *ᵥ q)
  have hD := dysonShiftConst_nonneg hK
  have hzE : ‖z - (E : ℂ)‖ ≤ r₀ + 1 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
      abs_of_nonneg hη]
    linarith
  have hsc : |s - c| ≤ s₀ := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hb : nsq (freshM F s z *ᵥ q) ≤ (1 + dysonShiftConst c r₀ s₀ v₀ * (r₀ + 1 + s₀)) *
      nsq (freshM F c (E : ℂ) *ᵥ q) := by
    have h1 := (abs_le.1 h).2
    have h2 : dysonShiftConst c r₀ s₀ v₀ * (‖z - (E : ℂ)‖ + |s - c|) ≤
        dysonShiftConst c r₀ s₀ v₀ * (r₀ + 1 + s₀) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    nlinarith
  rw [hΓ] at *
  unfold dysonGammaConst
  have : (1 + dysonShiftConst c r₀ s₀ v₀ * (r₀ + 1 + s₀)) / c * (c * nsq (freshM F c (E : ℂ) *ᵥ q))
      = (1 + dysonShiftConst c r₀ s₀ v₀ * (r₀ + 1 + s₀)) * nsq (freshM F c (E : ℂ) *ᵥ q) := by
    field_simp
  rw [this]
  exact hb

end BlockBand.Critical.RelativeVectors
