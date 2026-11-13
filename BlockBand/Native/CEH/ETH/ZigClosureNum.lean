module

public import BlockBand.Native.CEH.ETH.ZigClosureHyp
public import BlockBand.Native.CEH.LocalLaw.Holds

/-!
# CEH ETH: the numeric hypotheses of the closure for large `N`

Elementary inequalities that reduce the window-form numeric hypotheses of `zpc_closure_rpow`, the
grid length and the tail union bound to explicit conditions that hold for large `N`.

* `zcl_numY`, `zcl_numX`, `zcl_numZ`: the window-form closing inequalities `hY`, `hX`, `hZ` of
  `zpc_closure_rpow` from `16Λ < u`, `2 C₅₆ Λ < κ_ρ √N` (`ρ₁ρ₂ ≥ κ_ρ²`) and
  `π² + 8 s_hi C₅₆² π² + 7 ≤ u`;
* `zcl_grid`: `P₀ ≤ (1 + C_g N)² P_s` when `cᵢ s ≤ C_g` and `N ηᵢ ≥ 1`;
* `zcl_two_pow_ceil`: `x² ≤ 2^{2⌈x⌉}`;
* `zcl_tail_small`: `17 (2⌈1 + C_g N⌉ + 1) · 2 e^{-q} ≤ N^{-D}/2` when
  `log(68(5 + 2C_g)) + (1 + D) log N < q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Filter Set
open BlockBand.Native.CEH.Zig

/-!
## The closing inequalities in the variable `u`
-/

theorem zcl_sqrt_three_le : Real.sqrt 3 ≤ 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem zcl_pow_le_ne {u ne : ℝ} (hu : 1 ≤ u) (hne : u ^ 80 ≤ ne) {k : ℕ} (hk : k ≤ 80) :
    u ^ k ≤ ne :=
  (pow_le_pow_right₀ hu hk).trans hne

/-- `hY` of `zpc_closure_rpow` in the variable `u`. -/
theorem zcl_numY {u ne Λ Lmax : ℝ} (hu : 1 ≤ u) (hne : u ^ 80 ≤ ne) (hL : 0 ≤ Lmax)
    (hΛ : 1 + Lmax ≤ Λ) (hΛu : 16 * Λ < u) :
    (1 + Lmax) * (4 * Real.sqrt 3 * u + (u ^ 8) ^ 2 / (3 * (Real.pi * ne)) + 3 * u ^ 2) <
      u ^ 8 := by
  have hpi := Real.pi_gt_three
  have hne0 : 0 < ne := lt_of_lt_of_le (by positivity) hne
  have h16 : (u ^ 8) ^ 2 ≤ ne := by
    rw [← pow_mul]; exact zcl_pow_le_ne hu hne (by norm_num)
  have h1 : (u ^ 8) ^ 2 / (3 * (Real.pi * ne)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h2 := zcl_sqrt_three_le
  have hu2 : u ≤ u ^ 2 := by nlinarith
  have hT : 4 * Real.sqrt 3 * u + (u ^ 8) ^ 2 / (3 * (Real.pi * ne)) + 3 * u ^ 2 ≤
      12 * u ^ 2 := by nlinarith
  have hT0 : 0 ≤ 4 * Real.sqrt 3 * u + (u ^ 8) ^ 2 / (3 * (Real.pi * ne)) + 3 * u ^ 2 := by
    positivity
  have hu3 : u ^ 3 ≤ u ^ 8 := pow_le_pow_right₀ hu (by norm_num)
  calc (1 + Lmax) * (4 * Real.sqrt 3 * u + (u ^ 8) ^ 2 / (3 * (Real.pi * ne)) + 3 * u ^ 2)
      ≤ Λ * (12 * u ^ 2) := mul_le_mul hΛ hT hT0 (by linarith)
    _ < u / 16 * (12 * u ^ 2) := by
        exact mul_lt_mul_of_pos_right (by linarith) (by positivity)
    _ ≤ u ^ 3 := by nlinarith
    _ ≤ u ^ 8 := hu3

/-- `hX` of `zpc_closure_rpow` in the variable `u` (`n = N`, `ρρ = ρ₁ρ₂ ≥ κ_ρ²`). -/
theorem zcl_numX {u ne Λ Lmax Cm n ρρ κρ : ℝ} (hu : 1 ≤ u) (hne : u ^ 80 ≤ ne)
    (hL : 0 ≤ Lmax) (hΛ : 1 + Lmax / 2 ≤ Λ) (hΛu : 16 * Λ < u) (hn : 0 < n) (hκ : 0 < κρ)
    (hρ : κρ ^ 2 ≤ ρρ) (hCm : 0 ≤ Cm) (hA : 2 * Cm * Λ < κρ * Real.sqrt n) :
    (1 + Lmax / 2) * (2 * u * Real.sqrt (4 * u ^ 4 / (Real.pi * ne)) +
      Cm * u ^ 8 / Real.sqrt (n * ρρ) + u ^ 8 * u ^ 8 / (2 * (Real.pi * ne)) +
      2 * u ^ 2 * Real.sqrt (3 / 2 * u ^ 4) / Real.sqrt (Real.pi * ne)) < u ^ 8 := by
  have hpi := Real.pi_gt_three
  have hne0 : 0 < ne := lt_of_lt_of_le (by positivity) hne
  have hu0 : 0 < u := by linarith
  have hΛ0 : 0 < Λ := by linarith
  -- the four terms
  have a1 : Real.sqrt (4 * u ^ 4 / (Real.pi * ne)) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (by positivity)]
    have := zcl_pow_le_ne hu hne (k := 4) (by norm_num)
    nlinarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have a2 : Cm * u ^ 8 / Real.sqrt (n * ρρ) ≤ Cm * u ^ 8 / (κρ * Real.sqrt n) := by
    have hk : κρ * Real.sqrt n ≤ Real.sqrt (n * ρρ) := by
      rw [show κρ * Real.sqrt n = Real.sqrt (n * κρ ^ 2) by
        rw [Real.sqrt_mul hn.le, Real.sqrt_sq hκ.le, mul_comm]]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hρ hn.le)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hk
  have a3 : u ^ 8 * u ^ 8 / (2 * (Real.pi * ne)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := zcl_pow_le_ne hu hne (k := 8 + 8) (by norm_num)
    rw [pow_add] at this
    nlinarith
  have a4 : 2 * u ^ 2 * Real.sqrt (3 / 2 * u ^ 4) / Real.sqrt (Real.pi * ne) ≤ 3 := by
    have hs1 : Real.sqrt (3 / 2 * u ^ 4) ≤ 3 / 2 * u ^ 2 := by
      rw [show 3 / 2 * u ^ 2 = Real.sqrt ((3 / 2 * u ^ 2) ^ 2) by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith [pow_pos hu0 4])
    have hs2 : u ^ 4 ≤ Real.sqrt (Real.pi * ne) := by
      rw [show u ^ 4 = Real.sqrt ((u ^ 4) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt ?_
      rw [← pow_mul]
      have := zcl_pow_le_ne hu hne (k := 4 * 2) (by norm_num)
      nlinarith
    have hp : 0 < Real.sqrt (Real.pi * ne) := Real.sqrt_pos.2 (by positivity)
    rw [div_le_iff₀ hp]
    have h4 : 0 < u ^ 4 := by positivity
    calc 2 * u ^ 2 * Real.sqrt (3 / 2 * u ^ 4) ≤ 2 * u ^ 2 * (3 / 2 * u ^ 2) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = 3 * u ^ 4 := by ring
      _ ≤ 3 * Real.sqrt (Real.pi * ne) := by linarith
  have hT0 : 0 ≤ 2 * u * Real.sqrt (4 * u ^ 4 / (Real.pi * ne)) +
      Cm * u ^ 8 / Real.sqrt (n * ρρ) + u ^ 8 * u ^ 8 / (2 * (Real.pi * ne)) +
      2 * u ^ 2 * Real.sqrt (3 / 2 * u ^ 4) / Real.sqrt (Real.pi * ne) := by positivity
  have hT : 2 * u * Real.sqrt (4 * u ^ 4 / (Real.pi * ne)) +
      Cm * u ^ 8 / Real.sqrt (n * ρρ) + u ^ 8 * u ^ 8 / (2 * (Real.pi * ne)) +
      2 * u ^ 2 * Real.sqrt (3 / 2 * u ^ 4) / Real.sqrt (Real.pi * ne) ≤
      8 * u + Cm * u ^ 8 / (κρ * Real.sqrt n) := by
    have : 2 * u * Real.sqrt (4 * u ^ 4 / (Real.pi * ne)) ≤ 4 * u := by nlinarith
    linarith
  have hB : Λ * (Cm * u ^ 8 / (κρ * Real.sqrt n)) ≤ u ^ 8 / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have hu8 : 0 < u ^ 8 := by positivity
    nlinarith
  have hu2 : u ^ 2 ≤ u ^ 8 := pow_le_pow_right₀ hu (by norm_num)
  calc (1 + Lmax / 2) * (2 * u * Real.sqrt (4 * u ^ 4 / (Real.pi * ne)) +
        Cm * u ^ 8 / Real.sqrt (n * ρρ) + u ^ 8 * u ^ 8 / (2 * (Real.pi * ne)) +
        2 * u ^ 2 * Real.sqrt (3 / 2 * u ^ 4) / Real.sqrt (Real.pi * ne))
      ≤ Λ * (8 * u + Cm * u ^ 8 / (κρ * Real.sqrt n)) := mul_le_mul hΛ hT hT0 hΛ0.le
    _ = Λ * (8 * u) + Λ * (Cm * u ^ 8 / (κρ * Real.sqrt n)) := by ring
    _ < u ^ 8 / 2 + u ^ 8 / 2 := by
        refine add_lt_add_of_lt_of_le ?_ hB
        nlinarith
    _ = u ^ 8 := by ring

/-- `hZ` of `zpc_closure_rpow` in the variable `u` (`s ≤ s_hi`). -/
theorem zcl_numZ {u ne s sHi Cm : ℝ} (hu : 1 ≤ u) (hne : u ^ 80 ≤ ne) (hsHi : s ≤ sHi)
    (hZ : Real.pi ^ 2 + 8 * sHi * Cm ^ 2 * Real.pi ^ 2 + 7 ≤ u) :
    Real.pi ^ 2 + u * u ^ 4 * Real.sqrt (4 / (Real.pi * ne)) +
      6 * u ^ 2 * u ^ 4 / (Real.pi * ne) + 8 * s * Cm ^ 2 * Real.pi ^ 2 +
      8 * (u ^ 8) ^ 2 / (Real.pi * ne) ≤ u ^ 2 := by
  have hpi := Real.pi_gt_three
  have hne0 : 0 < ne := lt_of_lt_of_le (by positivity) hne
  have hu0 : 0 < u := by linarith
  have hpn : 0 < Real.pi * ne := by positivity
  have b1 : u * u ^ 4 * Real.sqrt (4 / (Real.pi * ne)) ≤ 2 := by
    have e : u * u ^ 4 * Real.sqrt (4 / (Real.pi * ne)) =
        Real.sqrt ((u ^ 5) ^ 2 * (4 / (Real.pi * ne))) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; ring
    rw [e, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    refine Real.sqrt_le_sqrt ?_
    rw [← mul_div_assoc, div_le_iff₀ hpn, ← pow_mul]
    have := zcl_pow_le_ne hu hne (k := 5 * 2) (by norm_num)
    nlinarith
  have b2 : 6 * u ^ 2 * u ^ 4 / (Real.pi * ne) ≤ 2 := by
    rw [div_le_iff₀ hpn, mul_assoc, ← pow_add]
    have := zcl_pow_le_ne hu hne (k := 2 + 4) (by norm_num)
    nlinarith
  have b3 : 8 * (u ^ 8) ^ 2 / (Real.pi * ne) ≤ 3 := by
    rw [div_le_iff₀ hpn, ← pow_mul]
    have := zcl_pow_le_ne hu hne (k := 8 * 2) (by norm_num)
    nlinarith
  have b4 : 8 * s * Cm ^ 2 * Real.pi ^ 2 ≤ 8 * sHi * Cm ^ 2 * Real.pi ^ 2 := by
    have : 0 ≤ Cm ^ 2 * Real.pi ^ 2 := by positivity
    nlinarith
  have hu2 : u ≤ u ^ 2 := by nlinarith
  linarith

/-!
## Grid and logarithmic loss
-/

/-- `η + c s ≤ η (1 + C_g N)` when `c s ≤ C_g` and `N η ≥ 1`. -/
theorem zcl_height_le {η c s Cg n : ℝ} (hcs : c * s ≤ Cg) (hCg : 0 ≤ Cg)
    (hnη : 1 ≤ n * η) : η + c * s ≤ η * (1 + Cg * n) := by
  nlinarith

/-- `P₀ ≤ (1 + C_g N)² P_s` for the heights `η_{i,t} = ηᵢ + cᵢ (s - t)`. -/
theorem zcl_grid {η₁ c₁ η₂ c₂ s Cg n : ℝ} (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (hc₁ : c₁ * s ≤ Cg) (hc₂ : c₂ * s ≤ Cg) (hc₁0 : 0 ≤ c₁) (hc₂0 : 0 ≤ c₂) (hs : 0 ≤ s)
    (hCg : 0 ≤ Cg) (h₁ : 1 ≤ n * η₁) (h₂ : 1 ≤ n * η₂) :
    zigHeightProd η₁ c₁ η₂ c₂ s 0 ≤ (1 + Cg * n) ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s s := by
  simp only [zigHeightProd, zigHeight, sub_zero, sub_self, mul_zero, add_zero]
  have a1 := zcl_height_le hc₁ hCg h₁
  have a2 := zcl_height_le hc₂ hCg h₂
  have p1 : 0 ≤ η₁ + c₁ * s := by positivity
  have p2 : 0 ≤ η₂ + c₂ * s := by positivity
  calc (η₁ + c₁ * s) * (η₂ + c₂ * s) ≤ (η₁ * (1 + Cg * n)) * (η₂ * (1 + Cg * n)) :=
        mul_le_mul a1 a2 p2 (by nlinarith)
    _ = (1 + Cg * n) ^ 2 * (η₁ * η₂) := by ring

/-- `x² ≤ 2^{2⌈x⌉}` for `x ≥ 0`. -/
theorem zcl_two_pow_ceil {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ (2 : ℝ) ^ (2 * ⌈x⌉₊) := by
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : ((⌈x⌉₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ⌈x⌉₊ := by
    exact_mod_cast (Nat.lt_two_pow_self).le
  rw [pow_mul']
  exact pow_le_pow_left₀ hx (h1.trans h2) 2

/-!
## The tail union bound
-/

/-- `17 (2⌈1 + C_g N⌉ + 1) · 2 e^{-q} ≤ N^{-D}/2` once
`log(68(5 + 2C_g)) + (1 + D) log N < q` (`N ≥ 1`, `C_g ≥ 0`). -/
theorem zcl_tail_small {N : ℕ} (hN : 1 ≤ N) {Cg D q : ℝ} (hCg : 0 ≤ Cg)
    (h : Real.log (68 * (5 + 2 * Cg)) + (1 + D) * Real.log N < q) :
    (((17 * (2 * ⌈1 + Cg * N⌉₊ + 1) : ℕ) : ℝ)) * (2 * Real.exp (-q)) ≤ (N : ℝ) ^ (-D) / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB : 0 ≤ 1 + Cg * N := by positivity
  have hceil : ((⌈1 + Cg * N⌉₊ : ℕ) : ℝ) < 1 + Cg * N + 1 := Nat.ceil_lt_add_one hB
  have hcast : (((17 * (2 * ⌈1 + Cg * N⌉₊ + 1) : ℕ) : ℝ)) ≤ 17 * (5 + 2 * Cg) * N := by
    push_cast
    nlinarith
  have hD : (0 : ℝ) < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 D
  have hC : (0 : ℝ) < 68 * (5 + 2 * Cg) := by positivity
  have hlog : Real.log (68 * (5 + 2 * Cg) * N * (N : ℝ) ^ D) < q := by
    rw [Real.log_mul (by positivity) hD.ne', Real.log_mul hC.ne' hN0.ne', Real.log_rpow hN0]
    linarith
  have hexp : 68 * (5 + 2 * Cg) * N * (N : ℝ) ^ D < Real.exp q :=
    (Real.log_lt_iff_lt_exp (by positivity)).1 hlog
  have hE : 0 < Real.exp (-q) := Real.exp_pos _
  have key : 17 * (5 + 2 * Cg) * N * (2 * Real.exp (-q)) ≤ (N : ℝ) ^ (-D) / 2 := by
    rw [Real.rpow_neg hN0.le, Real.exp_neg]
    have hq : 0 < Real.exp q := Real.exp_pos q
    rw [show 17 * (5 + 2 * Cg) * (N : ℝ) * (2 * (Real.exp q)⁻¹) =
      68 * (5 + 2 * Cg) * N / (2 * Real.exp q) by field_simp; ring,
      show ((N : ℝ) ^ D)⁻¹ / 2 = 1 / (2 * (N : ℝ) ^ D) by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact (mul_le_mul_of_nonneg_right hcast (by positivity)).trans key

/-!
## Eventual inequalities
-/

/-- `∀ᶠ N, A + B log N < κ N^r` (`κ, r > 0`). -/
theorem zcl_eventually_log_lt {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (A B : ℝ) :
    ∀ᶠ N : ℕ in atTop, A + B * Real.log N < κ * (N : ℝ) ^ r := by
  filter_upwards [LocalLaw.eventually_nat_add_mul_log_lt hr (A / κ) (B / κ)] with N hN
  have e : A + B * Real.log N = κ * (A / κ + B / κ * Real.log N) := by field_simp
  rw [e]
  exact mul_lt_mul_of_pos_left hN hκ

end BlockBand.Native.CEH.ETH
