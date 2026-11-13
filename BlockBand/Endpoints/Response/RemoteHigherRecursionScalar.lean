module

public import BlockBand.Endpoints.Response.ClockEntranceStep

/-!
# Scalar inequalities for the higher clock recursion

* `rhr_young_pointwise`, `rhr_lintegral_indicator_le_young` — Young in the weighted AM–GM form
  `H^r ≤ (r/(r+1)) l H^{r+1}/G + (1/(r+1)) l^{-r} G^r` (`θ = r/(r+1)`), pointwise and integrated
  over a set `D` (no measurability of `D` or `H` is needed);
* `rhr_rpow_le_of_forall` — the real Hölder bound `x^{1+1/r} ≤ M^{1/r} n` from the Young bound
  at every `l > 0` (as in the paper: `E(H^{r+1}/γ^p) ≥ (E H^r)^{(r+1)/r}/(E γ^{pr})^{1/r}`);
* `rhr_rpow_sub_le` — Bernoulli: `Y ≤ Z + ε` gives `Y^q - q Y^{q-1} ε ≤ Z^q` (`q ≥ 1`);
* `rhr_real_step` — the real algebra of one step:
  `y' ≤ y + W⁻¹(C' y - c' y^{1+1/r} + C') + (error)`;
* `rhr_forcing_le` — the forcing envelope `|g|^a x ≤ 1 + |g|^m + x⁸` for `2a ≤ m`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory
open scoped ENNReal

/-- **Young in weighted AM–GM form**: for `H ≥ 0`, `G > 0`, `r > 0`, `l > 0`,
`H^r ≤ (r/(r+1)) l (H^{r+1}/G) + (1/(r+1)) l^{-r} G^r`. -/
theorem rhr_young_pointwise {H G r l : ℝ} (hH : 0 ≤ H) (hG : 0 < G) (hr : 0 < r) (hl : 0 < l) :
    H ^ r ≤ r / (r + 1) * l * (H ^ (r + 1) / G) + 1 / (r + 1) * l ^ (-r) * G ^ r := by
  have hr1 : 0 < r + 1 := by linarith
  have hw : r / (r + 1) + 1 / (r + 1) = 1 := by field_simp
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := r / (r + 1)) (w₂ := 1 / (r + 1))
    (p₁ := l * (H ^ (r + 1) / G)) (p₂ := l ^ (-r) * G ^ r) (by positivity) (by positivity)
    (by positivity) (by positivity) hw
  have eq : (l * (H ^ (r + 1) / G)) ^ (r / (r + 1)) * (l ^ (-r) * G ^ r) ^ (1 / (r + 1)) =
      H ^ r := by
    rw [Real.mul_rpow hl.le (by positivity), Real.div_rpow (by positivity) hG.le,
      ← Real.rpow_mul hH, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hl.le, ← Real.rpow_mul hG.le]
    have e1 : (r + 1) * (r / (r + 1)) = r := by field_simp
    have e2 : -r * (1 / (r + 1)) = -(r / (r + 1)) := by ring
    have e3 : r * (1 / (r + 1)) = r / (r + 1) := by ring
    rw [e1, e2, e3, Real.rpow_neg hl.le]
    have h1 : 0 < l ^ (r / (r + 1)) := Real.rpow_pos_of_pos hl _
    have h2 : 0 < G ^ (r / (r + 1)) := Real.rpow_pos_of_pos hG _
    field_simp
  rw [eq] at key
  calc H ^ r ≤ _ := key
    _ = _ := by ring

section Integrals

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **Young integrated over a set** (the `r`-analogue of `ce_lintegral_indicator_le_cs`): for
`H, G ≥ 0` with `H = 0` where `G = 0`, `r > 0`, `l > 0`:
`∫ 1_D H^r ≤ (r/(r+1)) l ∫ 1_D H^{r+1}/G + (1/(r+1)) l^{-r} ∫ G^r` (`G^r` a.e. measurable). -/
theorem rhr_lintegral_indicator_le_young (D : Set Ω) (H G : Ω → ℝ) {r : ℝ} (hr : 0 < r)
    (hG : AEMeasurable (fun ω => ENNReal.ofReal (G ω ^ r)) μ) (hG0 : ∀ ω, 0 ≤ G ω)
    (hH0 : ∀ ω, 0 ≤ H ω) (hHG : ∀ ω, G ω = 0 → H ω = 0) {l : ℝ} (hl : 0 < l) :
    ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (H ω ^ r)) ω ∂μ ≤
      ENNReal.ofReal (r / (r + 1) * l) *
          ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (H ω ^ (r + 1) / G ω)) ω ∂μ +
        ENNReal.ofReal (1 / (r + 1) * l ^ (-r)) * ∫⁻ ω, ENNReal.ofReal (G ω ^ r) ∂μ := by
  have hpt : ∀ ω, D.indicator (fun ω => ENNReal.ofReal (H ω ^ r)) ω ≤
      ENNReal.ofReal (r / (r + 1) * l) *
          D.indicator (fun ω => ENNReal.ofReal (H ω ^ (r + 1) / G ω)) ω +
        ENNReal.ofReal (1 / (r + 1) * l ^ (-r)) * ENNReal.ofReal (G ω ^ r) := by
    intro ω
    by_cases hω : ω ∈ D
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      rcases (hG0 ω).eq_or_lt with h0 | hpos
      · rw [hHG ω h0.symm, Real.zero_rpow hr.ne', ENNReal.ofReal_zero]; exact bot_le
      · have hHr : 0 ≤ H ω ^ (r + 1) / G ω := by
          have := Real.rpow_nonneg (hH0 ω) (r + 1); positivity
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg (by positivity) (Real.rpow_nonneg (hG0 ω) _))]
        refine ENNReal.ofReal_le_ofReal ?_
        have := rhr_young_pointwise (hH0 ω) hpos hr hl
        linarith
    · rw [Set.indicator_of_notMem hω]; exact bot_le
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal (r / (r + 1) * l) *
          D.indicator (fun ω => ENNReal.ofReal (H ω ^ (r + 1) / G ω)) ω +
        ENNReal.ofReal (1 / (r + 1) * l ^ (-r)) * ENNReal.ofReal (G ω ^ r)) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_add_right' _ (hG.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Integrals

/-- **Hölder in real form**: the Young bound
`x ≤ (r/(r+1)) l n + (1/(r+1)) l^{-r} M` at every `l > 0` gives `x^{1+1/r} ≤ M^{1/r} n`
(the choice `l = (M/x)^{1/r}`). -/
theorem rhr_rpow_le_of_forall {x n M r : ℝ} (hx : 0 ≤ x) (hn : 0 ≤ n) (hM : 0 < M) (hr : 0 < r)
    (h : ∀ l : ℝ, 0 < l → x ≤ r / (r + 1) * l * n + 1 / (r + 1) * l ^ (-r) * M) :
    x ^ (1 + 1 / r) ≤ M ^ (1 / r) * n := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity)]
    exact mul_nonneg (Real.rpow_nonneg hM.le _) hn
  · have hr1 : 0 < r + 1 := by linarith
    set l := (M / x) ^ (1 / r) with hl
    have hl0 : 0 < l := Real.rpow_pos_of_pos (by positivity) _
    have hlr : l ^ (-r) = x / M := by
      rw [hl, ← Real.rpow_mul (by positivity)]
      have : 1 / r * -r = -1 := by field_simp
      rw [this, Real.rpow_neg_one, inv_div]
    have h1 := h l hl0
    rw [hlr] at h1
    have h2 : 1 / (r + 1) * (x / M) * M = x / (r + 1) := by field_simp
    rw [h2] at h1
    have h3 : x ≤ l * n := by
      have e : x - x / (r + 1) = r / (r + 1) * x := by field_simp; ring
      have h4 : r / (r + 1) * x ≤ r / (r + 1) * (l * n) := by
        have : r / (r + 1) * l * n = r / (r + 1) * (l * n) := by ring
        linarith
      exact le_of_mul_le_mul_left h4 (by positivity)
    have hxr : 0 < x ^ (1 / r) := Real.rpow_pos_of_pos hpos _
    have hl' : l = M ^ (1 / r) / x ^ (1 / r) := by
      rw [hl, Real.div_rpow hM.le hx]
    rw [Real.rpow_add hpos, Real.rpow_one]
    rw [hl', div_mul_eq_mul_div, le_div_iff₀ hxr] at h3
    linarith

/-- **Bernoulli**: for `Y, Z, ε ≥ 0`, `q ≥ 1` and `Y ≤ Z + ε`: `Y^q - q Y^{q-1} ε ≤ Z^q`. -/
theorem rhr_rpow_sub_le {Y Z ε q : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hε : 0 ≤ ε) (hq : 1 ≤ q)
    (h : Y ≤ Z + ε) : Y ^ q - q * Y ^ (q - 1) * ε ≤ Z ^ q := by
  have hq0 : 0 < q := by linarith
  have hZq : 0 ≤ Z ^ q := Real.rpow_nonneg hZ _
  rcases hY.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hq0.ne']
    have : 0 ≤ q * (0 : ℝ) ^ (q - 1) * ε :=
      mul_nonneg (mul_nonneg hq0.le (Real.rpow_nonneg le_rfl _)) hε
    linarith
  · have hYq : Y ^ q = Y ^ (q - 1) * Y := by
      rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
    have hY1 : 0 ≤ Y ^ (q - 1) := Real.rpow_nonneg hY _
    by_cases hYε : Y ≤ ε
    · rw [hYq]
      have : Y ^ (q - 1) * Y ≤ q * Y ^ (q - 1) * ε := by
        have h1 : Y ^ (q - 1) * Y ≤ Y ^ (q - 1) * ε := mul_le_mul_of_nonneg_left hYε hY1
        have h2 : Y ^ (q - 1) * ε ≤ q * Y ^ (q - 1) * ε := by
          have := mul_nonneg hY1 hε
          nlinarith
        linarith
      linarith
    · rw [not_le] at hYε
      set u := Y - ε with hu
      have hu0 : 0 < u := by linarith
      have huZ : u ≤ Z := by linarith
      have hb := one_add_mul_self_le_rpow_one_add (s := u / Y - 1)
        (by have := div_nonneg hu0.le hY; linarith) hq
      rw [add_sub_cancel, Real.div_rpow hu0.le hY,
        le_div_iff₀ (Real.rpow_pos_of_pos hpos q)] at hb
      have e : (1 + q * (u / Y - 1)) * Y ^ q = Y ^ q - q * Y ^ (q - 1) * ε := by
        rw [hYq, hu]; field_simp; ring
      rw [e] at hb
      exact hb.trans (Real.rpow_le_rpow hu0.le huZ hq0.le)

/-- **One step of the higher expectation recursion** (real algebra). From the
integrated one-step inequality (with the exceptional part `ex ≤ ε` of the new length added), the
split `y ≤ (1 + Kd) x + ε`, Hölder `x^{1+1/r} ≤ M_r n` and the a priori bound
`y^{1/r} ≤ W A_y`:
`y' ≤ y + W⁻¹(C' y - c' y^{1+1/r} + C') + e + ε + c'(1 + 1/r) A_y ε`, `C' = C + C F̄`,
`c' = c/((1 + Kd)^{1+1/r} M_r)`. -/
theorem rhr_real_step {W y y' x n C c K d Mr Fb Fv ex ε e Ay r : ℝ} (hW : 0 < W) (hy : 0 ≤ y)
    (hx : 0 ≤ x) (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 ≤ K) (hd : 0 < d) (hMr : 0 < Mr)
    (hr : 0 < r) (hFv0 : 0 ≤ Fv) (hFv : Fv ≤ Fb) (hex : ex ≤ ε) (hε : 0 ≤ ε)
    (hstep : y' + c / W * n ≤ (1 + C / W) * y + C / W * Fv + ex + e)
    (hsplit : y ≤ (1 + K * d) * x + ε) (hhol : x ^ (1 + 1 / r) ≤ Mr * n)
    (hyW : y ^ (1 / r) ≤ W * Ay) :
    y' ≤ y + W⁻¹ * ((C + C * Fb) * y -
        c / ((1 + K * d) ^ (1 + 1 / r) * Mr) * y ^ (1 + 1 / r) + (C + C * Fb)) +
      (e + (ε + c / ((1 + K * d) ^ (1 + 1 / r) * Mr) * (1 + 1 / r) * Ay * ε)) := by
  set a := 1 + K * d with ha
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  set q := 1 + 1 / r with hq
  have hq1 : 1 ≤ q := by rw [hq]; have : 0 < 1 / r := by positivity
                         linarith
  have hqr : q - 1 = 1 / r := by rw [hq]; ring
  set κ := a ^ q * Mr with hκ
  have haq : 0 < a ^ q := Real.rpow_pos_of_pos (by rw [ha]; nlinarith) _
  have hκ0 : 0 < κ := by positivity
  -- Bernoulli against `a x`
  have hb := rhr_rpow_sub_le hy (mul_nonneg ha0 hx) hε hq1 hsplit
  rw [Real.mul_rpow ha0 hx, hqr] at hb
  set Yq := y ^ q with hYq
  set Y1 := y ^ (1 / r) with hY1
  have hY10 : 0 ≤ Y1 := Real.rpow_nonneg hy _
  have hn : Yq - q * Y1 * ε ≤ κ * n := by
    have : a ^ q * x ^ q ≤ a ^ q * (Mr * n) := mul_le_mul_of_nonneg_left hhol haq.le
    rw [hκ]; nlinarith
  set c' := c / κ with hc'
  have hc'0 : 0 < c' := by positivity
  have hcn : c' / W * (Yq - q * Y1 * ε) ≤ c / W * n := by
    have h1 : c' / W * (Yq - q * Y1 * ε) ≤ c' / W * (κ * n) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have e1 : c' / W * (κ * n) = c / W * n := by rw [hc']; field_simp
    linarith
  have hY1W : c' / W * (q * Y1 * ε) ≤ c' * q * Ay * ε := by
    have h1 : Y1 / W ≤ Ay := by rw [div_le_iff₀ hW]; linarith
    have e1 : c' / W * (q * Y1 * ε) = c' * q * (Y1 / W) * ε := by ring
    rw [e1]
    have hq0 : 0 ≤ c' * q := by positivity
    have := mul_le_mul_of_nonneg_left h1 hq0
    nlinarith
  have hFb : 0 ≤ Fb := hFv0.trans hFv
  have hCy : C * y / W ≤ (C + C * Fb) * y / W := by
    apply div_le_div_of_nonneg_right _ hW.le
    nlinarith [mul_nonneg hC hFb, mul_nonneg (mul_nonneg hC hFb) hy]
  have hCF : C * Fv / W ≤ (C + C * Fb) / W := by
    apply div_le_div_of_nonneg_right _ hW.le
    nlinarith [mul_le_mul_of_nonneg_left hFv hC]
  have expand : W⁻¹ * ((C + C * Fb) * y - c' * Yq + (C + C * Fb)) =
      (C + C * Fb) * y / W - c' / W * Yq + (C + C * Fb) / W := by ring
  have e2 : (1 + C / W) * y + C / W * Fv = y + C * y / W + C * Fv / W := by ring
  have e3 : c' / W * (Yq - q * Y1 * ε) = c' / W * Yq - c' / W * (q * Y1 * ε) := by ring
  rw [expand]
  linarith

/-- **The higher forcing envelope**: `|g|^a x ≤ 1 + |g|^m + x⁸` for `0 ≤ a`, `2a ≤ m`, `x ≥ 0`. -/
theorem rhr_forcing_le {g x a m : ℝ} (ha : 0 ≤ a) (ham : 2 * a ≤ m) (hx : 0 ≤ x) :
    |g| ^ a * x ≤ 1 + |g| ^ m + x ^ 8 := by
  set G := |g| ^ a with hG
  have hG0 : 0 ≤ G := Real.rpow_nonneg (abs_nonneg g) _
  have hm : 0 ≤ |g| ^ m := Real.rpow_nonneg (abs_nonneg g) _
  have hG2 : G ^ 2 ≤ 1 + |g| ^ m := by
    have e : G ^ 2 = |g| ^ (a * (2 : ℕ)) := by
      rw [hG, Real.rpow_mul_natCast (abs_nonneg g)]
    rw [e]
    rcases le_total |g| 1 with h | h
    · have : |g| ^ (a * (2 : ℕ)) ≤ 1 :=
        Real.rpow_le_one (abs_nonneg g) h (by push_cast; nlinarith)
      linarith
    · have : |g| ^ (a * (2 : ℕ)) ≤ |g| ^ m :=
        Real.rpow_le_rpow_of_exponent_le h (by push_cast; linarith)
      linarith
  have hx2 : x ^ 2 ≤ 1 + x ^ 8 := ce_sq_le_one_add_pow hx (by norm_num)
  have : 0 ≤ x ^ 8 := pow_nonneg hx _
  nlinarith [sq_nonneg (G - x)]

end BlockBand.Endpoints
