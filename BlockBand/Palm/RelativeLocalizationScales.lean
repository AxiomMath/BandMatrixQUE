module

public import BlockBand.Palm.RelativeLocalizationShortCore
public import BlockBand.Palm.RelativeLocalizationAsymp

/-!
# Relative localization: the rate bound and the §8 scales

* `rowKappa_le` : with `ν d = 1`, `ν ℓ/N = 1`, `1 ≤ ν ≤ N`, the tilt rate is
  `κ ≤ kappaConst · ν (1 + log N)` (`kappaConst` depends only on the fixed constants);
* `s8_scales` : at `τ = N^{-1/100}`, `ℓ = ⌊N^{1-(1/100)/3}⌋`, `ν = N/ℓ`, eventually in `N`:
  `ℓ ≥ 1`, `ℓ/N ≤ r₀/64`, `c - τ > 0`, `kappaConst ν (1 + log N) τ ≤ 1`, `2νC√τ ≤ 1`,
  `ν N^{-1/100} ≤ 1`, `1 ≤ ν ≤ N`, `2e⁴ N^{D+1} e^{-c'N^ε} ≤ 1`, `N ≥ 2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

/-- `κ ≤ M₀ ν (1 + log N)` at `νd = 1`, `νℓ/N = 1`, `1 ≤ ν ≤ N`. -/
theorem rowKappa_le {N ℓ : ℕ} {ν d Rc c₁ C₁ : ℝ} (hN : (1 : ℝ) ≤ N) (hRc : 0 < Rc)
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hν1 : 1 ≤ ν) (hνN : ν ≤ N) (hνd : ν * d = 1)
    (hνl : ν * (ℓ / N) = 1) :
    rowKappa N ℓ ν d Rc c₁ C₁ ≤
      (3 * Real.exp (2 * weightConst * C₁) *
          (weightConst / Rc + weightConst + weightConst ^ 2) + 4 * weightConst / c₁) *
        ν * (1 + Real.log N) := by
  have hC0 := weightConst_pos
  have hν0 : 0 < ν := lt_of_lt_of_le one_pos hν1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hd : d = 1 / ν := by field_simp; linarith
  have hlN : (ℓ : ℝ) / N = 1 / ν := by rw [eq_div_iff hν0.ne', mul_comm]; exact hνl
  set X := weightConst / Rc + weightConst + weightConst ^ 2 with hX
  have hX0 : 0 < X := by positivity
  set e := Real.exp (2 * weightConst * C₁) with he
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have hexp : Real.exp (|ν| * weightConst * (2 * C₁ * ℓ / N)) = e := by
    have : |ν| * weightConst * (2 * C₁ * ℓ / N) = 2 * weightConst * C₁ := by
      rw [abs_of_pos hν0, show (2 * C₁ * ℓ / N) = 2 * C₁ * ((ℓ : ℝ) / N) by ring, hlN]
      field_simp
    rw [this]
  have hB : |ν| * (weightConst / Rc + weightConst / d) + ν ^ 2 * weightConst ^ 2 =
      ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2) := by
    rw [abs_of_pos hν0, hd]; field_simp; ring
  unfold rowKappa
  rw [hexp, hB, abs_of_pos hν0]
  have hT1 : 2 * ℓ * (ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2)) * e / N =
      2 * e * (weightConst / Rc + ν * (weightConst + weightConst ^ 2)) := by
    have : (2 * ℓ * (ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2)) * e / N) =
        2 * e * (ν * ((ℓ : ℝ) / N)) * (weightConst / Rc + ν * (weightConst + weightConst ^ 2)) := by
      field_simp
    rw [this, hνl]; ring
  have hT3 : (ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2)) / (2 * N) ≤
      ν * X / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : ν * (weightConst / Rc) ≤ ν * (weightConst / Rc) * N :=
      le_mul_of_one_le_right (by positivity) hN
    have h2 : ν ^ 2 * (weightConst + weightConst ^ 2) ≤ ν * (weightConst + weightConst ^ 2) * N := by
      have : ν ^ 2 ≤ ν * N := by nlinarith
      nlinarith [this, (by positivity : (0 : ℝ) ≤ weightConst + weightConst ^ 2)]
    rw [hX]; nlinarith
  rw [hT1]
  have hT2 : 2 * (ν * weightConst) * (1 + Real.log N) / (c₁ / 2) =
      4 * weightConst / c₁ * ν * (1 + Real.log N) := by field_simp; ring
  rw [hT2]
  have hA : 2 * e * (weightConst / Rc + ν * (weightConst + weightConst ^ 2)) ≤ 2 * e * X * ν := by
    have h1 : weightConst / Rc ≤ weightConst / Rc * ν :=
      le_mul_of_one_le_right (div_pos hC0 hRc).le hν1
    have h2 : weightConst / Rc + ν * (weightConst + weightConst ^ 2) ≤ X * ν := by
      rw [hX]; nlinarith
    calc _ ≤ 2 * e * (X * ν) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * e * X * ν := by ring
  have h1l : 1 ≤ 1 + Real.log N := by linarith
  have hXν : 0 ≤ X * ν := by positivity
  have h3a : ν * X / 2 ≤ e * X * ν := by nlinarith
  have h3b : 3 * e * X * ν ≤ 3 * e * X * ν * (1 + Real.log N) :=
    le_mul_of_one_le_right (by positivity) h1l
  have hfin : 2 * e * X * ν + 4 * weightConst / c₁ * ν * (1 + Real.log N) + ν * X / 2 ≤
      (3 * e * X + 4 * weightConst / c₁) * ν * (1 + Real.log N) := by
    have : (3 * e * X + 4 * weightConst / c₁) * ν * (1 + Real.log N) =
        3 * e * X * ν * (1 + Real.log N) + 4 * weightConst / c₁ * ν * (1 + Real.log N) := by ring
    rw [this]; linarith
  linarith

end BlockBand.Palm.RelativeLocalization

namespace BlockBand.Palm.RelativeLocalization

open Filter Real

/-- The constant of `rowKappa_le`. -/
def kappaConst (Rc c₁ C₁ : ℝ) : ℝ :=
  3 * Real.exp (2 * weightConst * C₁) * (weightConst / Rc + weightConst + weightConst ^ 2) +
    4 * weightConst / c₁

theorem kappaConst_pos {Rc c₁ C₁ : ℝ} (hRc : 0 < Rc) (hc₁ : 0 < c₁) : 0 < kappaConst Rc c₁ C₁ := by
  have := weightConst_pos
  unfold kappaConst; positivity

theorem rpow_mul_rpow' {x : ℝ} (hx : 0 < x) (p q : ℝ) : x ^ p * x ^ q = x ^ (p + q) :=
  (Real.rpow_add hx p q).symm

/-- **The §8 scales.** -/
theorem s8_scales {r₀ c C c₁ C₁ ε c' : ℝ} (hr₀ : 0 < r₀) (hc : 0 < c) (hC : 0 < C)
    (hc₁ : 0 < c₁) (hε : 0 < ε) (hc' : 0 < c') (D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ∧
      (⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ : ℝ) / N ≤ r₀ / 64 ∧
      0 < c - (N : ℝ) ^ (-(1 / 100 : ℝ)) ∧
      kappaConst (r₀ / 128) c₁ C₁ * ((N : ℝ) / ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊) *
          (1 + Real.log N) * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 ∧
      ((N : ℝ) / ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊) *
          (2 * (C * Real.sqrt ((N : ℝ) ^ (-(1 / 100 : ℝ))))) ≤ 1 ∧
      ((N : ℝ) / ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊) * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 ∧
      1 ≤ (N : ℝ) / ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ∧
      (N : ℝ) / ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ N ∧
      2 * Real.exp 4 * ((N : ℝ) ^ (D + 1) * Real.exp (-(c' * (N : ℝ) ^ ε))) ≤ 1 ∧
      (2 : ℝ) ≤ N := by
  have hM := kappaConst_pos (by positivity : (0 : ℝ) < r₀ / 128) hc₁ (C₁ := C₁)
  filter_upwards [ev_rpow_ge (p := 1 - (1 / 100 : ℝ) / 3) (by norm_num) 2,
    ev_rpow_neg_le (p := (1 / 100 : ℝ) / 3) (by norm_num) (by positivity : 0 < r₀ / 64),
    ev_rpow_neg_le (p := (1 / 100 : ℝ)) (by norm_num) (by positivity : 0 < c / 2),
    ev_log_le (r := 2 / 300) (by norm_num) (2 * kappaConst (r₀ / 128) c₁ C₁),
    ev_rpow_neg_le (p := (1 / 600 : ℝ)) (by norm_num) (by positivity : 0 < 1 / (4 * C)),
    ev_rpow_neg_le (p := (2 / 300 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2),
    ev_poly_exp_le (D + 1) hc' hε (by positivity : (0 : ℝ) < 1 / (2 * Real.exp 4)),
    ev_natCast_ge 2] with N hP hP' hτ hlog h600 h300 hexp hN2
  set x : ℝ := (N : ℝ) with hx
  have hx0 : 0 < x := by linarith
  set P := x ^ (1 - (1 / 100 : ℝ) / 3) with hPdef
  set ℓ := ⌊P⌋₊ with hℓdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hx0.le _
  have hℓP : (ℓ : ℝ) ≤ P := Nat.floor_le hP0
  have hℓP2 : P / 2 ≤ ℓ := floor_ge_half hP
  have hℓ1 : (1 : ℝ) ≤ ℓ := by linarith
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  -- `P = x · x^{-1/300}`
  have hPx : P = x * x ^ (-((1 / 100 : ℝ) / 3)) := by
    rw [hPdef, show (1 - (1 / 100 : ℝ) / 3) = 1 + (-((1 / 100 : ℝ) / 3)) by ring,
      Real.rpow_add hx0, Real.rpow_one]
  have hq0 : 0 < x ^ (-((1 / 100 : ℝ) / 3)) := Real.rpow_pos_of_pos hx0 _
  have hPlex : P ≤ x := by
    rw [hPx]
    have : x ^ (-((1 / 100 : ℝ) / 3)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (by norm_num)
    nlinarith
  -- `ν ≤ 2 x^{1/300}`
  have hνle : x / ℓ ≤ 2 * x ^ ((1 / 100 : ℝ) / 3) := by
    rw [div_le_iff₀ hℓ0]
    have h1 : x ^ ((1 / 100 : ℝ) / 3) * x ^ (-((1 / 100 : ℝ) / 3)) = 1 := by
      rw [← Real.rpow_add hx0]; simp
    have h2 : x = x ^ ((1 / 100 : ℝ) / 3) * P := by rw [hPx]; nlinarith [h1]
    nlinarith [Real.rpow_pos_of_pos hx0 ((1 / 100 : ℝ) / 3)]
  have hνpos : 0 ≤ 2 * x ^ ((1 / 100 : ℝ) / 3) := by positivity
  refine ⟨hℓ1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hN2⟩
  · rw [div_le_iff₀ hx0]
    calc (ℓ : ℝ) ≤ P := hℓP
      _ = x ^ (-((1 / 100 : ℝ) / 3)) * x := by rw [hPx]; ring
      _ ≤ r₀ / 64 * x := mul_le_mul_of_nonneg_right hP' hx0.le
  · linarith
  · have hlog0 : 0 ≤ 1 + Real.log x := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x); linarith
    calc kappaConst (r₀ / 128) c₁ C₁ * (x / ℓ) * (1 + Real.log x) * x ^ (-(1 / 100 : ℝ))
        ≤ kappaConst (r₀ / 128) c₁ C₁ * (2 * x ^ ((1 / 100 : ℝ) / 3)) * (1 + Real.log x) *
            x ^ (-(1 / 100 : ℝ)) := by gcongr
      _ = (2 * kappaConst (r₀ / 128) c₁ C₁ * (1 + Real.log x)) * x ^ (-(2 / 300 : ℝ)) := by
          rw [show (2 / 300 : ℝ) = -((1 / 100 : ℝ) / 3 + -(1 / 100 : ℝ)) by norm_num, neg_neg,
            Real.rpow_add hx0]; ring
      _ ≤ x ^ (2 / 300 : ℝ) * x ^ (-(2 / 300 : ℝ)) :=
          mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hx0.le _)
      _ = 1 := by rw [← Real.rpow_add hx0]; simp
  · have hs : Real.sqrt (x ^ (-(1 / 100 : ℝ))) = x ^ (-(1 / 200 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
    rw [hs]
    calc x / ℓ * (2 * (C * x ^ (-(1 / 200 : ℝ))))
        ≤ 2 * x ^ ((1 / 100 : ℝ) / 3) * (2 * (C * x ^ (-(1 / 200 : ℝ)))) := by
          gcongr
      _ = 4 * C * x ^ (-(1 / 600 : ℝ)) := by
          rw [show -(1 / 600 : ℝ) = (1 / 100 : ℝ) / 3 + -(1 / 200 : ℝ) by norm_num,
            Real.rpow_add hx0]; ring
      _ ≤ 4 * C * (1 / (4 * C)) := mul_le_mul_of_nonneg_left h600 (by positivity)
      _ = 1 := by field_simp
  · calc x / ℓ * x ^ (-(1 / 100 : ℝ)) ≤ 2 * x ^ ((1 / 100 : ℝ) / 3) * x ^ (-(1 / 100 : ℝ)) := by
          gcongr
      _ = 2 * x ^ (-(2 / 300 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hx0]; norm_num
      _ ≤ 2 * (1 / 2) := mul_le_mul_of_nonneg_left h300 (by norm_num)
      _ = 1 := by norm_num
  · rw [le_div_iff₀ hℓ0]; linarith
  · rw [div_le_iff₀ hℓ0]; nlinarith
  · have := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 2 * Real.exp 4)
    calc _ ≤ 2 * Real.exp 4 * (1 / (2 * Real.exp 4)) := this
      _ = 1 := by field_simp

end BlockBand.Palm.RelativeLocalization
