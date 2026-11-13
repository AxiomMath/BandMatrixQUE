module

public import BlockBand.Critical.RelativeVectors.DysonShift

/-!
# The deterministic covariance weight

Bounds on the covariance weight `φ_s(x)` entering the middle line of the interval bound.
Deterministic. *Domain:* `N ≥ 1`, `FreshConstants c r₀ s₀ v₀`, `F` in `FreshClass`,
`s, σ ∈ [c - s₀, c]`, `|x - E|, |x' - E| ≤ r₀`, `0 < h ≤ 1`. All bounds are relative to `q^*Γq`
(no `‖q‖` or `‖V‖` factor); the constants depend on `(c, r₀, s₀, v₀)` only.

* `phi_le`: `φ_s(x) ≤ c C' q^*Γq`;
* `phi_lipschitz`: `|φ_s(x) - φ_s(x')| ≤ c C_s C' |x - x'| q^*Γq`;
* `phi_time_shift`: `|φ_σ(x) - φ_s(x)| ≤ (1 + c C_s) C' |σ - s| q^*Γq`;
* `phi_eta_shift`: `|Im q^*M_σ(x+ih)q - φ_σ(x) Im m_σ(x+ih)| ≤ (C' + c v₀⁻¹ C_s C') h q^*Γq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative

variable {N : ℕ}

section
variable {F : Matrix (Fin N) (Fin N) ℂ} {A c E r₀ s₀ v₀ : ℝ}

theorem phi_le (hN : 0 < N) (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {s x : ℝ} (hs : s ∈ Icc (c - s₀) c) (hx : |x - E| ≤ r₀) (q : Fin N → ℂ) :
    quadForm (freshGamma F s x) q ≤ c * dysonGammaConst c r₀ s₀ v₀ * quadForm (freshGamma F c E) q := by
  rw [freshGamma_quad_eq hC.1 s x q]
  have h := rnsq_le_gamma hN hK hC hs (z := (x : ℂ)) (by simpa using hx) (by simp) (by simp) q
  have hs0 : 0 ≤ s := le_trans (by linarith [hK.2.2.2.2.1, hK.1]) hs.1
  have hn := nsq_nonneg (freshM F s (x : ℂ) *ᵥ q)
  calc s * nsq (freshM F s (x : ℂ) *ᵥ q) ≤ c * nsq (freshM F s (x : ℂ) *ᵥ q) :=
        mul_le_mul_of_nonneg_right hs.2 hn
    _ ≤ c * (dysonGammaConst c r₀ s₀ v₀ * quadForm (freshGamma F c E) q) :=
        mul_le_mul_of_nonneg_left h hK.1.le
    _ = _ := by ring

theorem phi_lipschitz (hN : 0 < N) (hK : FreshConstants c r₀ s₀ v₀)
    (hC : FreshClass F A c E r₀ s₀ v₀) {s x x' : ℝ} (hs : s ∈ Icc (c - s₀) c)
    (hx : |x - E| ≤ r₀) (hx' : |x' - E| ≤ r₀) (q : Fin N → ℂ) :
    |quadForm (freshGamma F s x) q - quadForm (freshGamma F s x') q| ≤
      c * dysonShiftConst c r₀ s₀ v₀ * dysonGammaConst c r₀ s₀ v₀ * |x - x'| *
        quadForm (freshGamma F c E) q := by
  rw [freshGamma_quad_eq hC.1 s x q, freshGamma_quad_eq hC.1 s x' q, ← mul_sub, abs_mul]
  have hs0 : 0 ≤ s := le_trans (by linarith [hK.2.2.2.2.1, hK.1]) hs.1
  have h1 := rnsq_shift_le hN hK hC hs hs (z₁ := (x : ℂ)) (z₂ := (x' : ℂ)) (by simpa using hx)
    (by simp) (by simp) (by simpa using hx') (by simp) (by simp) q
  have h2 := rnsq_le_gamma hN hK hC hs (z := (x' : ℂ)) (by simpa using hx') (by simp) (by simp) q
  rw [sub_self, abs_zero, add_zero, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h1
  have hD := dysonShiftConst_nonneg hK
  have hn := nsq_nonneg (freshM F s (x' : ℂ) *ᵥ q)
  rw [abs_of_nonneg hs0]
  calc s * |nsq (freshM F s (x : ℂ) *ᵥ q) - nsq (freshM F s (x' : ℂ) *ᵥ q)|
      ≤ c * (dysonShiftConst c r₀ s₀ v₀ * |x - x'| * nsq (freshM F s (x' : ℂ) *ᵥ q)) :=
        mul_le_mul hs.2 h1 (abs_nonneg _) hK.1.le
    _ ≤ c * (dysonShiftConst c r₀ s₀ v₀ * |x - x'| *
          (dysonGammaConst c r₀ s₀ v₀ * quadForm (freshGamma F c E) q)) := by
        apply mul_le_mul_of_nonneg_left _ hK.1.le
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem phi_time_shift (hN : 0 < N) (hK : FreshConstants c r₀ s₀ v₀)
    (hC : FreshClass F A c E r₀ s₀ v₀) {s σ x : ℝ} (hs : s ∈ Icc (c - s₀) c)
    (hσ : σ ∈ Icc (c - s₀) c) (hx : |x - E| ≤ r₀) (q : Fin N → ℂ) :
    |quadForm (freshGamma F σ x) q - quadForm (freshGamma F s x) q| ≤
      (1 + c * dysonShiftConst c r₀ s₀ v₀) * dysonGammaConst c r₀ s₀ v₀ * |σ - s| *
        quadForm (freshGamma F c E) q := by
  rw [freshGamma_quad_eq hC.1 σ x q, freshGamma_quad_eq hC.1 s x q]
  set a := nsq (freshM F σ (x : ℂ) *ᵥ q)
  set b := nsq (freshM F s (x : ℂ) *ᵥ q)
  have hs0 : 0 ≤ s := le_trans (by linarith [hK.2.2.2.2.1, hK.1]) hs.1
  have h1 := rnsq_shift_le hN hK hC hσ hs (z₁ := (x : ℂ)) (z₂ := (x : ℂ)) (by simpa using hx)
    (by simp) (by simp) (by simpa using hx) (by simp) (by simp) q
  rw [sub_self, norm_zero, zero_add] at h1
  have ha := rnsq_le_gamma hN hK hC hσ (z := (x : ℂ)) (by simpa using hx) (by simp) (by simp) q
  have hb := rnsq_le_gamma hN hK hC hs (z := (x : ℂ)) (by simpa using hx) (by simp) (by simp) q
  have hD := dysonShiftConst_nonneg hK
  have hb0 : 0 ≤ b := nsq_nonneg _
  have ha0 : 0 ≤ a := nsq_nonneg _
  have hΓ0 : 0 ≤ quadForm (freshGamma F c E) q := by
    have := nsq_nonneg (freshM F c (E : ℂ) *ᵥ q)
    rw [freshGamma_quad_eq hC.1 c E q]; exact mul_nonneg hK.1.le this
  have e : σ * a - s * b = (σ - s) * a + s * (a - b) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg ha0]
  set G := quadForm (freshGamma F c E) q
  set C' := dysonGammaConst c r₀ s₀ v₀
  set Cs := dysonShiftConst c r₀ s₀ v₀
  have t1 : |σ - s| * a ≤ |σ - s| * (C' * G) := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have t2 : s * |a - b| ≤ c * (Cs * |σ - s| * (C' * G)) := by
    refine mul_le_mul hs.2 (h1.trans ?_) (abs_nonneg _) hK.1.le
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  nlinarith [abs_nonneg (σ - s)]

theorem phi_eta_shift (hN : 0 < N) (hK : FreshConstants c r₀ s₀ v₀)
    (hC : FreshClass F A c E r₀ s₀ v₀) {σ x h : ℝ} (hσ : σ ∈ Icc (c - s₀) c)
    (hx : |x - E| ≤ r₀) (hh : 0 < h) (hh1 : h ≤ 1) (q : Fin N → ℂ) :
    |(star q ⬝ᵥ (freshM F σ ⟨x, h⟩ *ᵥ q)).im -
        quadForm (freshGamma F σ x) q * (freshDyson F σ ⟨x, h⟩).im| ≤
      (dysonGammaConst c r₀ s₀ v₀ +
        c * v₀⁻¹ * dysonShiftConst c r₀ s₀ v₀ * dysonGammaConst c r₀ s₀ v₀) * h *
        quadForm (freshGamma F c E) q := by
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hK' : FreshConstants c r₀ s₀ v₀ := ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩
  have hσ0 : 0 < σ := lt_of_lt_of_le (by linarith) hσ.1
  set z : ℂ := ⟨x, h⟩
  have hzre : |z.re - E| ≤ r₀ := hx
  obtain ⟨hm1, hm2⟩ := fresh_regular_bounds hC.2.2 hσ hzre hh.le hh1
  have hw : (freshW F σ z).im ≠ 0 := by
    rw [freshW_im]; exact (add_pos hh (mul_pos hσ0 (lt_of_lt_of_le hv0 hm1))).ne'
  rw [freshM_quad_im hC.1 hw q, freshGamma_quad_eq hC.1 σ x q]
  have hz : z.im = h := rfl
  rw [hz]
  set a := nsq (freshM F σ z *ᵥ q)
  set b := nsq (freshM F σ (x : ℂ) *ᵥ q)
  set mi := (freshDyson F σ z).im
  have h1 := rnsq_shift_le hN hK' hC hσ hσ (z₁ := z) (z₂ := (x : ℂ)) hzre hh.le hh1
    (by simpa using hx) (by simp) (by simp) q
  have hzx : z - (x : ℂ) = (h : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [z]
  rw [hzx, sub_self, abs_zero, add_zero, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_pos hh] at h1
  have ha := rnsq_le_gamma hN hK' hC hσ (z := z) hzre hh.le hh1 q
  have hb := rnsq_le_gamma hN hK' hC hσ (z := (x : ℂ)) (by simpa using hx) (by simp) (by simp) q
  have hD := dysonShiftConst_nonneg hK'
  have hb0 : 0 ≤ b := nsq_nonneg _
  have ha0 : 0 ≤ a := nsq_nonneg _
  have hmi0 : 0 ≤ mi := hv0.le.trans hm1
  set G := quadForm (freshGamma F c E) q
  set C' := dysonGammaConst c r₀ s₀ v₀
  set Cs := dysonShiftConst c r₀ s₀ v₀
  have e : (h + σ * mi) * a - σ * b * mi = h * a + σ * mi * (a - b) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh, abs_of_pos hσ0, abs_of_nonneg hmi0,
    abs_of_nonneg ha0]
  have t1 : h * a ≤ h * (C' * G) := mul_le_mul_of_nonneg_left ha hh.le
  have t2 : σ * mi * |a - b| ≤ c * v₀⁻¹ * (Cs * h * (C' * G)) := by
    refine mul_le_mul (mul_le_mul hσ.2 hm2 hmi0 hc0.le) (h1.trans ?_) (abs_nonneg _)
      (by positivity)
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  nlinarith

end

end BlockBand.Critical.RelativeVectors
