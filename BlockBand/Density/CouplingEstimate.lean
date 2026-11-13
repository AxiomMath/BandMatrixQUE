module

public import BlockBand.Density.ResolventComparisonMean
public import BlockBand.Density.Estimate
public import BlockBand.Adapters.ErdosRiabov.ShortRingLocalLaw

/-!
# The mean resolvent bound from the short-ring local law, and the critical density theorem

Exponent bookkeeping for `m = ⌈W^{15/16}⌉`, `N_K = mW`, `η = W^{-7/4}`, `ℓ = W^{15/8}` (for
`W ≥ 2^{32}`): `W^{31/16} ≤ N_K ≤ W^{63/32}`, `N_K^{1+1/128} ≤ W²`, `η ≥ N_K^{-1+1/256}`,
`N_K^{1/64} ≤ W^{1/32}`, and the site control at distance `≥ N_K/4` with `D = 384`. The assembly
`meanResolventBound_holds` uses `BlockBand.Adapters.ErdosRiabov.shortRingLocalLaw_holds` (from
`ErdosRiabov.SourceContract`) with `ζ₀ = 1/128`, `δ₀ = 1/256`, `C₀ = 3`, `D = 384`, `ε = 1/64`,
`D₁ = 4`, on the coupled short ring of `coupledShortModel`, the mean comparison
`norm_integral_resolvent_sub_le` and the rotation `integral_resolvent_diag_block`;
`criticalDensity_holds` combines it with `criticalDensity_of_meanResolventBound` (PSSS).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory BlockBand.External

section Scales

variable {w : ℝ}

theorem rpow_mono_exp (hw : 1 ≤ w) {a b : ℝ} (h : a ≤ b) : w ^ a ≤ w ^ b :=
  Real.rpow_le_rpow_of_exponent_le hw h

theorem two_le_rpow_one_div_32 (hw : (2 : ℝ) ^ 32 ≤ w) : 2 ≤ w ^ ((1 : ℝ) / 32) := by
  have h : ((2 : ℝ) ^ 32) ^ ((1 : ℝ) / 32) = 2 := by
    rw [show (1 : ℝ) / 32 = ((32 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  calc (2 : ℝ) = ((2 : ℝ) ^ 32) ^ ((1 : ℝ) / 32) := h.symm
    _ ≤ w ^ ((1 : ℝ) / 32) := Real.rpow_le_rpow (by positivity) hw (by norm_num)

theorem one_le_of_two_pow_le (hw : (2 : ℝ) ^ 32 ≤ w) : 1 ≤ w :=
  le_trans (by norm_num) hw

/-- `16 ≤ m = ⌈W^{15/16}⌉`. -/
theorem sixteen_le_ceil (hw : (2 : ℝ) ^ 32 ≤ w) : 16 ≤ ⌈w ^ ((15 : ℝ) / 16)⌉₊ := by
  have hw0 : 0 ≤ w := (one_le_of_two_pow_le hw).trans' zero_le_one
  have h2 := two_le_rpow_one_div_32 hw
  have h30 : w ^ ((15 : ℝ) / 16) = (w ^ ((1 : ℝ) / 32)) ^ (30 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0]; norm_num
  have : (16 : ℝ) ≤ w ^ ((15 : ℝ) / 16) := by
    rw [h30]
    calc (16 : ℝ) ≤ 2 ^ (30 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 _
  have := this.trans (Nat.le_ceil _)
  exact_mod_cast this

/-- `W^{31/16} ≤ N_K = mW`. -/
theorem rpow_le_shortN (hw : (2 : ℝ) ^ 32 ≤ w) :
    w ^ ((31 : ℝ) / 16) ≤ (⌈w ^ ((15 : ℝ) / 16)⌉₊ : ℝ) * w := by
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  have : w ^ ((31 : ℝ) / 16) = w ^ ((15 : ℝ) / 16) * w := by
    rw [show w ^ ((15 : ℝ) / 16) * w = w ^ ((15 : ℝ) / 16) * w ^ (1 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hw0]; norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) hw0.le

/-- `N_K = mW ≤ W^{63/32}`. -/
theorem shortN_le_rpow (hw : (2 : ℝ) ^ 32 ≤ w) :
    (⌈w ^ ((15 : ℝ) / 16)⌉₊ : ℝ) * w ≤ w ^ ((63 : ℝ) / 32) := by
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  have h2 := two_le_rpow_one_div_32 hw
  have h1 : 1 ≤ w ^ ((15 : ℝ) / 16) := Real.one_le_rpow hw1 (by norm_num)
  have hc : (⌈w ^ ((15 : ℝ) / 16)⌉₊ : ℝ) ≤ w ^ ((15 : ℝ) / 16) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have e : w ^ ((63 : ℝ) / 32) = w ^ ((1 : ℝ) / 32) * w ^ ((15 : ℝ) / 16) * w := by
    rw [show w ^ ((1 : ℝ) / 32) * w ^ ((15 : ℝ) / 16) * w =
        w ^ ((1 : ℝ) / 32) * w ^ ((15 : ℝ) / 16) * w ^ (1 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hw0, ← Real.rpow_add hw0]; norm_num
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hw0.le
  nlinarith

theorem shortN_rpow_le_sq {NK : ℝ} (hw : (2 : ℝ) ^ 32 ≤ w) (h0 : 0 ≤ NK)
    (h : NK ≤ w ^ ((63 : ℝ) / 32)) : NK ^ ((1 : ℝ) + 1 / 128) ≤ w ^ 2 := by
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : 0 ≤ w := zero_le_one.trans hw1
  calc NK ^ ((1 : ℝ) + 1 / 128) ≤ (w ^ ((63 : ℝ) / 32)) ^ ((1 : ℝ) + 1 / 128) :=
        Real.rpow_le_rpow h0 h (by norm_num)
    _ = w ^ ((63 : ℝ) / 32 * (1 + 1 / 128)) := (Real.rpow_mul hw0 _ _).symm
    _ ≤ w ^ ((2 : ℕ) : ℝ) := rpow_mono_exp hw1 (by norm_num)
    _ = w ^ 2 := Real.rpow_natCast w 2

theorem shortN_rpow_le_eta {NK : ℝ} (hw : (2 : ℝ) ^ 32 ≤ w)
    (h : w ^ ((31 : ℝ) / 16) ≤ NK) : NK ^ ((-1 : ℝ) + 1 / 256) ≤ w ^ (-(7 : ℝ) / 4) := by
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : 0 ≤ w := zero_le_one.trans hw1
  calc NK ^ ((-1 : ℝ) + 1 / 256) ≤ (w ^ ((31 : ℝ) / 16)) ^ ((-1 : ℝ) + 1 / 256) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (by linarith) _) h (by norm_num)
    _ = w ^ ((31 : ℝ) / 16 * (-1 + 1 / 256)) := (Real.rpow_mul hw0 _ _).symm
    _ ≤ w ^ (-(7 : ℝ) / 4) := rpow_mono_exp hw1 (by norm_num)

theorem shortN_rpow_eps_le {NK : ℝ} (hw : (2 : ℝ) ^ 32 ≤ w) (h0 : 0 ≤ NK)
    (h : NK ≤ w ^ ((63 : ℝ) / 32)) : NK ^ ((1 : ℝ) / 64) ≤ w ^ ((1 : ℝ) / 32) := by
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : 0 ≤ w := zero_le_one.trans hw1
  calc NK ^ ((1 : ℝ) / 64) ≤ (w ^ ((63 : ℝ) / 32)) ^ ((1 : ℝ) / 64) :=
        Real.rpow_le_rpow h0 h (by norm_num)
    _ = w ^ ((63 : ℝ) / 32 * (1 / 64)) := (Real.rpow_mul hw0 _ _).symm
    _ ≤ w ^ ((1 : ℝ) / 32) := rpow_mono_exp hw1 (by norm_num)

/-- `ℓ = min(W/√η, N_K) = W^{15/8}` at `η = W^{-7/4}`. -/
theorem localizationLength_eq {N W : ℕ} (hw : (2 : ℝ) ^ 32 ≤ (W : ℝ))
    (h : (W : ℝ) ^ ((31 : ℝ) / 16) ≤ N) :
    ErdosRiabov.localizationLength N W ((W : ℝ) ^ (-(7 : ℝ) / 4)) = (W : ℝ) ^ ((15 : ℝ) / 8) := by
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : 0 < (W : ℝ) := lt_of_lt_of_le zero_lt_one hw1
  have hs : Real.sqrt ((W : ℝ) ^ (-(7 : ℝ) / 4)) = (W : ℝ) ^ (-(7 : ℝ) / 8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hw0.le]; norm_num
  have hd : (W : ℝ) / (W : ℝ) ^ (-(7 : ℝ) / 8) = (W : ℝ) ^ ((15 : ℝ) / 8) := by
    rw [div_eq_iff (Real.rpow_pos_of_pos hw0 _).ne', ← Real.rpow_add hw0]
    conv_lhs => rw [← Real.rpow_one (W : ℝ)]
    norm_num
  unfold ErdosRiabov.localizationLength
  rw [hs, hd]
  exact min_eq_left ((rpow_mono_exp hw1 (by norm_num)).trans h)

end Scales

section Distance

/-- Arithmetic of the cyclic distance between block `⌊m/2⌋` and an end block. -/
theorem four_mul_dist {m W k a c j : ℕ} (hk : k = m / 2) (hm : 16 ≤ m) (ha : a < W)
    (hc : c < W) (hj : j = 0 ∨ j = m - 1) :
    m * W ≤ 4 * min (max (k * W + a) (j * W + c) - min (k * W + a) (j * W + c))
      (m * W - (max (k * W + a) (j * W + c) - min (k * W + a) (j * W + c))) := by
  have hk2 : 2 * k ≤ m ∧ m ≤ 2 * k + 1 := by omega
  rcases hj with rfl | rfl
  · have hA : m * W + 4 * W ≤ 4 * (k * W) := by
      have := Nat.mul_le_mul_right W (show m + 4 ≤ 4 * k by omega)
      simp only [add_mul, mul_assoc] at this; omega
    have hC : 4 * (k * W) + 4 * W ≤ 3 * (m * W) := by
      have := Nat.mul_le_mul_right W (show 4 * k + 4 ≤ 3 * m by omega)
      simp only [add_mul, mul_assoc] at this; omega
    have hE : k * W + W ≤ m * W := by
      have := Nat.mul_le_mul_right W (show k + 1 ≤ m by omega)
      simp only [add_mul, one_mul] at this; omega
    have hW : W ≤ k * W := by
      have := Nat.mul_le_mul_right W (show 1 ≤ k by omega)
      simp only [one_mul] at this; omega
    simp only [zero_mul, zero_add]
    omega
  · obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hR : (m₁ + 1) * W = m₁ * W + W := by ring
    have hB : 4 * (k * W) + 4 * W + (m₁ + 1) * W ≤ 4 * (m₁ * W) := by
      have := Nat.mul_le_mul_right W (show 4 * k + 4 + (m₁ + 1) ≤ 4 * m₁ by omega)
      simp only [add_mul, mul_assoc, one_mul] at this ⊢; omega
    have hD : (m₁ + 1) * W ≤ 4 * (k * W) := by
      have := Nat.mul_le_mul_right W (show m₁ + 1 ≤ 4 * k by omega)
      simp only [mul_assoc] at this; omega
    have hF : k * W + W ≤ m₁ * W := by
      have := Nat.mul_le_mul_right W (show k + 1 ≤ m₁ by omega)
      simp only [add_mul, one_mul] at this; omega
    omega

/-- A site in block `⌊n/2⌋` is at cyclic distance `≥ N/4` from both end blocks (`n ≥ 16`). -/
theorem four_mul_siteDistance_ge (q : Parameters) (hq : 16 ≤ q.n) (x y : q.Site)
    (hx : x.1.val = q.n / 2) (hy : y.1.val = 0 ∨ y.1.val = q.n - 1) :
    q.N ≤ 4 * Internal.Contracts.Inputs.siteDistance q x y := by
  unfold Internal.Contracts.Inputs.siteDistance Parameters.siteIndex Parameters.N
  rw [hx]
  exact four_mul_dist rfl hq x.2.isLt y.2.isLt hy

end Distance

section Control

open Internal.Contracts.Inputs

theorem ell_mul_eta {N W : ℕ} (hw : (2 : ℝ) ^ 32 ≤ (W : ℝ))
    (h : (W : ℝ) ^ ((31 : ℝ) / 16) ≤ N) :
    ErdosRiabov.localizationLength N W ((W : ℝ) ^ (-(7 : ℝ) / 4)) * (W : ℝ) ^ (-(7 : ℝ) / 4) =
      (W : ℝ) ^ ((1 : ℝ) / 8) := by
  have hw0 : 0 < (W : ℝ) := lt_of_lt_of_le (by norm_num) hw
  rw [localizationLength_eq hw h, ← Real.rpow_add hw0]; norm_num

/-- Diagonal site control: `N^{1/64} √Υ(x,x) ≤ W^{-1/32}` at `η = W^{-7/4}`. -/
theorem diag_threshold_le (q : Parameters) (hw : (2 : ℝ) ^ 32 ≤ (q.W : ℝ))
    (h1 : (q.W : ℝ) ^ ((31 : ℝ) / 16) ≤ q.N) (h2 : (q.N : ℝ) ≤ (q.W : ℝ) ^ ((63 : ℝ) / 32))
    (D : ℝ) (x : q.Site) :
    (q.N : ℝ) ^ ((1 : ℝ) / 64) * Real.sqrt (siteControl q D ((q.W : ℝ) ^ (-(7 : ℝ) / 4)) x x) ≤
      (q.W : ℝ) ^ (-(1 : ℝ) / 32) := by
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : 0 < (q.W : ℝ) := lt_of_lt_of_le zero_lt_one hw1
  have hc : siteControl q D ((q.W : ℝ) ^ (-(7 : ℝ) / 4)) x x = (q.W : ℝ) ^ (-(1 : ℝ) / 8) := by
    unfold siteControl siteDistance
    rw [ell_mul_eta hw h1]
    simp only [max_self, Nat.sub_self, min_self]
    rw [← Real.rpow_neg hw0.le]; norm_num
  have hs : Real.sqrt ((q.W : ℝ) ^ (-(1 : ℝ) / 8)) = (q.W : ℝ) ^ (-(1 : ℝ) / 16) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hw0.le]; norm_num
  rw [hc, hs]
  calc (q.N : ℝ) ^ ((1 : ℝ) / 64) * (q.W : ℝ) ^ (-(1 : ℝ) / 16)
      ≤ (q.W : ℝ) ^ ((1 : ℝ) / 32) * (q.W : ℝ) ^ (-(1 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right (shortN_rpow_eps_le hw (Nat.cast_nonneg _) h2)
          (Real.rpow_pos_of_pos hw0 _).le
    _ = (q.W : ℝ) ^ (-(1 : ℝ) / 32) := by rw [← Real.rpow_add hw0]; norm_num

/-- Far site control (`D = 384`): at distance `≥ N/4`, `√Υ(x,y) ≤ 2^{384} W^{-12}`. -/
theorem sqrt_siteControl_far_le (q : Parameters) (hw : (2 : ℝ) ^ 32 ≤ (q.W : ℝ))
    (h1 : (q.W : ℝ) ^ ((31 : ℝ) / 16) ≤ q.N) (x y : q.Site)
    (hd : (q.N : ℝ) ≤ 4 * siteDistance q x y) :
    Real.sqrt (siteControl q 384 ((q.W : ℝ) ^ (-(7 : ℝ) / 4)) x y) ≤
      2 ^ 384 / (q.W : ℝ) ^ 12 := by
  set w : ℝ := (q.W : ℝ)
  have hw1 : 1 ≤ w := one_le_of_two_pow_le hw
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw1
  have hℓ := localizationLength_eq hw h1
  have hℓη := ell_mul_eta hw h1
  set ℓ := ErdosRiabov.localizationLength q.N q.W (w ^ (-(7 : ℝ) / 4))
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact Real.rpow_pos_of_pos hw0 _
  have hq16 : 0 < w ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos hw0 _
  -- `d / ℓ ≥ W^{1/16} / 4`
  have hdl : w ^ ((1 : ℝ) / 16) / 4 ≤ (siteDistance q x y : ℝ) / ℓ := by
    rw [le_div_iff₀ hℓ0, hℓ]
    have e : w ^ ((1 : ℝ) / 16) / 4 * w ^ ((15 : ℝ) / 8) = w ^ ((31 : ℝ) / 16) / 4 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hw0]; norm_num
    rw [e]
    linarith
  have hpow : (w ^ ((1 : ℝ) / 16) / 4) ^ (384 : ℕ) = w ^ (24 : ℕ) / 4 ^ (384 : ℕ) := by
    rw [div_pow, ← Real.rpow_natCast (w ^ ((1 : ℝ) / 16)), ← Real.rpow_mul hw0.le,
      ← Real.rpow_natCast w 24]
    norm_num
  have hbase : 0 < w ^ ((1 : ℝ) / 16) / 4 := by positivity
  have hdec : (1 + (siteDistance q x y : ℝ) / ℓ) ^ (-(384 : ℝ)) ≤
      4 ^ (384 : ℕ) / w ^ (24 : ℕ) := by
    rw [Real.rpow_neg (by positivity), show (384 : ℝ) = ((384 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    have hle : (w ^ ((1 : ℝ) / 16) / 4) ^ (384 : ℕ) ≤
        (1 + (siteDistance q x y : ℝ) / ℓ) ^ (384 : ℕ) :=
      pow_le_pow_left₀ hbase.le (by linarith) _
    calc ((1 + (siteDistance q x y : ℝ) / ℓ) ^ (384 : ℕ))⁻¹
        ≤ ((w ^ ((1 : ℝ) / 16) / 4) ^ (384 : ℕ))⁻¹ :=
          inv_anti₀ (pow_pos hbase _) hle
      _ = 4 ^ (384 : ℕ) / w ^ (24 : ℕ) := by rw [hpow, inv_div]
  have hpre : (ℓ * w ^ (-(7 : ℝ) / 4))⁻¹ ≤ 1 := by
    rw [hℓη]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hw1 (by norm_num))
  have hctrl : siteControl q 384 (w ^ (-(7 : ℝ) / 4)) x y ≤ 4 ^ (384 : ℕ) / w ^ (24 : ℕ) := by
    unfold siteControl
    have h0 : 0 ≤ (1 + (siteDistance q x y : ℝ) / ℓ) ^ (-(384 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    calc (ℓ * w ^ (-(7 : ℝ) / 4))⁻¹ * (1 + (siteDistance q x y : ℝ) / ℓ) ^ (-(384 : ℝ))
        ≤ 1 * (1 + (siteDistance q x y : ℝ) / ℓ) ^ (-(384 : ℝ)) :=
          mul_le_mul_of_nonneg_right hpre h0
      _ ≤ 4 ^ (384 : ℕ) / w ^ (24 : ℕ) := by rw [one_mul]; exact hdec
  have hsq : 4 ^ (384 : ℕ) / w ^ (24 : ℕ) = (2 ^ 384 / w ^ 12) ^ 2 := by
    rw [div_pow, ← pow_mul, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  calc Real.sqrt (siteControl q 384 (w ^ (-(7 : ℝ) / 4)) x y)
      ≤ Real.sqrt (4 ^ (384 : ℕ) / w ^ (24 : ℕ)) := Real.sqrt_le_sqrt hctrl
    _ = 2 ^ 384 / w ^ 12 := by rw [hsq, Real.sqrt_sq (by positivity)]

end Control

section Assembly

open Internal.Contracts.Inputs

/-- Final real arithmetic of the assembly. -/
theorem final_bound {w T A ηi δ NK N β t : ℝ} (hw : 1 ≤ w) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hηi : ηi ≤ w ^ 2) (hδ : δ = A / w ^ 11) (hNK0 : 0 ≤ NK) (hNK : NK ≤ w ^ 2)
    (hN0 : 0 ≤ N) (hN : N ≤ T * w ^ 2) (hβ0 : 0 ≤ β) (hNβ : NK * β ≤ (w ^ 3)⁻¹)
    (hβ : β ≤ (w ^ 4)⁻¹) (ht : t ≤ w ^ (-(1 : ℝ) / 32)) :
    ηi * δ * (NK * N * (2 + 2 * NK)) + 2 * ηi * (NK * β) + (t + (ηi + 1) * β) ≤
      (4 * T * A + 5) * w ^ (-(1 : ℝ) / 32) := by
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  set u := w ^ (-(1 : ℝ) / 32)
  have hu1 : w⁻¹ ≤ u := by
    rw [← Real.rpow_neg_one]
    exact rpow_mono_exp hw (by norm_num)
  have hw2 : (w ^ 2)⁻¹ ≤ w⁻¹ := inv_anti₀ hw0 (by nlinarith)
  have hw3 : (w ^ 3)⁻¹ ≤ w⁻¹ := inv_anti₀ hw0 (by nlinarith [pow_pos hw0 2])
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- first term
  have hX : NK * N * (2 + 2 * NK) ≤ w ^ 2 * (T * w ^ 2) * (4 * w ^ 2) := by
    have h1 : NK * N ≤ w ^ 2 * (T * w ^ 2) := mul_le_mul hNK hN hN0 (by positivity)
    have h2 : 2 + 2 * NK ≤ 4 * w ^ 2 := by nlinarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have h1 : ηi * δ * (NK * N * (2 + 2 * NK)) ≤ 4 * T * A * (w ^ 3)⁻¹ := by
    calc ηi * δ * (NK * N * (2 + 2 * NK)) ≤ w ^ 2 * δ * (w ^ 2 * (T * w ^ 2) * (4 * w ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hηi hδ0) hX (by positivity) (by positivity)
      _ = 4 * T * A * (w ^ 3)⁻¹ := by
          rw [hδ]; field_simp
  have h2 : 2 * ηi * (NK * β) ≤ 2 * w⁻¹ := by
    calc 2 * ηi * (NK * β) ≤ 2 * w ^ 2 * (w ^ 3)⁻¹ :=
          mul_le_mul (by linarith) hNβ (mul_nonneg hNK0 hβ0) (by positivity)
      _ = 2 * w⁻¹ := by field_simp
  have h3 : (ηi + 1) * β ≤ 2 * (w ^ 2)⁻¹ := by
    calc (ηi + 1) * β ≤ (2 * w ^ 2) * (w ^ 4)⁻¹ :=
          mul_le_mul (by nlinarith) hβ hβ0 (by positivity)
      _ = 2 * (w ^ 2)⁻¹ := by field_simp
  have hT0 : 0 ≤ 4 * T * A := by positivity
  have := mul_le_mul_of_nonneg_left (hw3.trans hu1) hT0
  nlinarith

/-- **`MeanResolventBound`**: for fixed `b, κ, T` there are `C, W₀` such that, for every admissible
`p` with bond `b`, `4⌈W^{15/16}⌉ ≤ n ≤ TW`, `W ≥ W₀`, every realization of the physical law, every
bulk `|e| ≤ 2 - κ` and every site `x`, `‖E G_xx(e + iW^{-7/4}) - m_sc‖ ≤ C W^{-1/32}`. Hypothesis:
`ErdosRiabov.SourceContract` only (through `shortRingLocalLaw_holds`, with `ζ₀ = 1/128`,
`δ₀ = 1/256`, `C₀ = 3`, `D = 384`, `ε = 1/64`, `D₁ = 4`); `C = 4T·2^{384} + 5`,
`W₀ = max(N₀, 2^{32})`. Proof: rotate `x` to block `⌊m/2⌋`, couple `H` with the short ring `K` of
`m = ⌈W^{15/16}⌉` blocks (`coupledShortModel`, exactly the short-ring law), compare means
(`norm_integral_resolvent_sub_le`, end-block entries above the threshold `2^{384} W^{-11}` with
failure probability `N_K^{-4}`, by the site control at distance `≥ N_K/4`) and apply the diagonal
local law (`norm_integral_resolvent_diag_sub_le`). -/
theorem meanResolventBound_holds (hER : ErdosRiabov.SourceContract.{0}) :
    MeanResolventBound := by
  intro b κ T hb hb' hκ hT
  obtain ⟨N₀, hN₀⟩ := BlockBand.Adapters.ErdosRiabov.shortRingLocalLaw_holds hER b (1 / 128)
    (1 / 256) κ 3 hb hb' (by norm_num) (by norm_num) hκ (by norm_num) 384 (by norm_num) (1 / 64) 4
    (by norm_num) (by norm_num)
  refine ⟨4 * T * 2 ^ 384 + 5, max (N₀ : ℝ) (2 ^ 32), by positivity, ?_⟩
  intro p hpb hceil hnT hW₀ model e he x
  have hw : (2 : ℝ) ^ 32 ≤ (p.W : ℝ) := (le_max_right _ _).trans hW₀
  have hwN₀ : (N₀ : ℝ) ≤ (p.W : ℝ) := (le_max_left _ _).trans hW₀
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : (0 : ℝ) < p.W := lt_of_lt_of_le zero_lt_one hw1
  have hm16 := sixteen_le_ceil hw
  set m := ⌈(p.W : ℝ) ^ ((15 : ℝ) / 16)⌉₊ with hmdef
  have hm4 : 4 ≤ m := by omega
  have hmn : m < p.n := by omega
  set q := shortParameters p m hm4 with hqdef
  have hqN : ((q.N : ℕ) : ℝ) = (m : ℝ) * (p.W : ℝ) := by
    change ((m * p.W : ℕ) : ℝ) = _
    push_cast; rfl
  have hqW : (q.W : ℝ) = (p.W : ℝ) := rfl
  have hqn : q.n = m := rfl
  have hN1 : (q.W : ℝ) ^ ((31 : ℝ) / 16) ≤ q.N := by rw [hqN, hqW]; exact rpow_le_shortN hw
  have hN2 : (q.N : ℝ) ≤ (q.W : ℝ) ^ ((63 : ℝ) / 32) := by rw [hqN, hqW]; exact shortN_le_rpow hw
  have hNK1 : (p.W : ℝ) ≤ q.N := by
    rw [hqN]
    have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    nlinarith
  set η := resolventScale p.W with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos hw0 _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hw1 (by norm_num)
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I with hz
  set model' := q.constructGaussianRingModel
  set K := coupledShortModel hmn model model'
  -- the local law on the coupled short ring
  have hNq : N₀ ≤ q.N := by exact_mod_cast hwN₀.trans hNK1
  have hζ : (q.N : ℝ) ^ ((1 : ℝ) + 1 / 128) ≤ (q.W : ℝ) ^ 2 :=
    shortN_rpow_le_sq hw (Nat.cast_nonneg _) hN2
  have hδ₀ : (q.N : ℝ) ^ ((-1 : ℝ) + 1 / 256) ≤ η := shortN_rpow_le_eta hw hN1
  have hC₀ : ‖(e : ℂ) + (η : ℂ) * Complex.I‖ ≤ 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hη]
    linarith [abs_nonneg e]
  have hLL := hN₀ q hpb hNq hζ K e η he hδ₀ hC₀
  -- the retained site
  set x' : q.Site := (((m / 2 : ℕ) : ZMod q.n), x.2) with hx'def
  have hx'v : x'.1.val = q.n / 2 := by
    change (((m / 2 : ℕ) : ZMod q.n)).val = m / 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show m / 2 < q.n by rw [hqn]; omega)]
  have hιx' : segmentEmbedding p hm4 x' = (((m / 2 : ℕ) : ZMod p.n), x.2) := by
    apply Prod.ext
    · change ((x'.1.val : ℕ) : ZMod p.n) = _
      rw [hx'v]
      rfl
    · rfl
  -- rotation
  have hrot := integral_resolvent_diag_block p model z x ((m / 2 : ℕ) : ZMod p.n)
  change ‖(∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ x x ∂(model.law : Measure p.SiteMatrix)) -
    ErdosRiabov.semicircleM z‖ ≤ _
  rw [hrot, ← hιx']
  -- the end-block events
  set δ : ℝ := 2 ^ 384 / (p.W : ℝ) ^ 11
  set β : ℝ := (q.N : ℝ) ^ (-(4 : ℝ))
  have hβ0 : 0 ≤ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbad : ∀ u ∈ endBlocks p m hm4,
      (Measure.map coupledShortMatrix (coupledLaw model model'))
        {G | δ < ‖(G - z • (1 : q.SiteMatrix))⁻¹ x' u‖} ≤ ENNReal.ofReal β := by
    intro u hu
    have hu' : u.1.val = 0 ∨ u.1.val = q.n - 1 := (Finset.mem_filter.mp hu).2
    have hne : x' ≠ u := by
      intro h
      have := congrArg (fun s : q.Site => s.1.val) h
      rw [hx'v] at this
      omega
    have hd : (q.N : ℝ) ≤ 4 * siteDistance q x' u := by
      exact_mod_cast four_mul_siteDistance_ge q (by rw [hqn]; exact hm16) x' u hx'v hu'
    have hfar := sqrt_siteControl_far_le q hw hN1 x' u hd
    have hthr : (q.N : ℝ) ^ ((1 : ℝ) / 64) *
        Real.sqrt (siteControl q 384 η x' u) ≤ δ := by
      have heps := shortN_rpow_eps_le hw (Nat.cast_nonneg _) hN2
      have hw32 : (q.W : ℝ) ^ ((1 : ℝ) / 32) ≤ q.W := by
        conv_rhs => rw [← Real.rpow_one (q.W : ℝ)]
        exact rpow_mono_exp hw1 (by norm_num)
      calc (q.N : ℝ) ^ ((1 : ℝ) / 64) * Real.sqrt (siteControl q 384 η x' u)
          ≤ (q.W : ℝ) * (2 ^ 384 / (q.W : ℝ) ^ 12) :=
            mul_le_mul (heps.trans hw32) hfar (Real.sqrt_nonneg _) (by positivity)
        _ = δ := by
            change (p.W : ℝ) * (2 ^ 384 / (p.W : ℝ) ^ 12) = 2 ^ 384 / (p.W : ℝ) ^ 11
            field_simp
    refine le_trans (measure_mono ?_) (hLL x' u)
    intro G hG
    change δ < ‖(G - z • (1 : q.SiteMatrix))⁻¹ x' u‖ at hG
    change (q.N : ℝ) ^ ((1 : ℝ) / 64) * Real.sqrt (siteControl q 384 η x' u) <
      ‖(G - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : q.SiteMatrix))⁻¹ x' u -
        (if x' = u then ErdosRiabov.semicircleM ((e : ℂ) + (η : ℂ) * Complex.I) else 0)‖
    simp only [hne, ite_false, sub_zero]
    exact lt_of_le_of_lt hthr hG
  have hA := norm_integral_resolvent_sub_le hmn model model' e hη x'
    (by positivity : (0 : ℝ) ≤ δ) hβ0 hbad
  -- the diagonal event
  set t : ℝ := (q.N : ℝ) ^ ((1 : ℝ) / 64) * Real.sqrt (siteControl q 384 η x' x')
  have ht0 : 0 ≤ t := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)
  have hc : ‖ErdosRiabov.semicircleM z‖ ≤ 1 :=
    (ErdosRiabov.norm_semicircleM_lt_one (by simp [hz, hη.ne'])).le
  have hbadD : (K.law : Measure q.SiteMatrix)
      {G | t < ‖(G - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : q.SiteMatrix))⁻¹ x' x' -
        ErdosRiabov.semicircleM z‖} ≤ ENNReal.ofReal β := by
    have := hLL x' x'
    simp only [ite_true] at this
    exact this
  have hD := norm_integral_resolvent_diag_sub_le q K e hη x' (ErdosRiabov.semicircleM z) hc ht0
    hβ0 hbadD
  have hKlaw : (K.law : Measure q.SiteMatrix) =
      Measure.map coupledShortMatrix (coupledLaw model model') := rfl
  rw [hKlaw] at hD
  -- arithmetic
  have hηi : η⁻¹ ≤ (p.W : ℝ) ^ 2 := by
    rw [hηdef, resolventScale, show -(7 : ℝ) / 4 = -((7 : ℝ) / 4) by ring,
      Real.rpow_neg hw0.le, inv_inv, ← Real.rpow_natCast]
    exact rpow_mono_exp hw1 (by norm_num)
  have hNKw : (q.N : ℝ) ≤ (p.W : ℝ) ^ 2 := by
    refine hN2.trans ?_
    rw [hqW, ← Real.rpow_natCast]
    exact rpow_mono_exp hw1 (by norm_num)
  have hpN : (p.N : ℝ) ≤ T * (p.W : ℝ) ^ 2 := by
    have : (p.N : ℝ) = (p.n : ℝ) * p.W := by
      change ((p.n * p.W : ℕ) : ℝ) = _
      push_cast; ring
    rw [this]
    nlinarith
  have hNK0 : (0 : ℝ) < q.N := lt_of_lt_of_le hw0 hNK1
  have hβe : β = ((q.N : ℝ) ^ 4)⁻¹ := by
    change (q.N : ℝ) ^ (-(4 : ℝ)) = _
    rw [Real.rpow_neg hNK0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hNβ : (q.N : ℝ) * β ≤ ((p.W : ℝ) ^ 3)⁻¹ := by
    rw [hβe]
    have e1 : (q.N : ℝ) * ((q.N : ℝ) ^ 4)⁻¹ = ((q.N : ℝ) ^ 3)⁻¹ := by
      field_simp
    rw [e1]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hw0.le hNK1 3)
  have hβw : β ≤ ((p.W : ℝ) ^ 4)⁻¹ := by
    rw [hβe]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hw0.le hNK1 4)
  have ht : t ≤ (p.W : ℝ) ^ (-(1 : ℝ) / 32) := diag_threshold_le q hw hN1 hN2 384 x'
  have hfin := final_bound hw1 hT.le (by positivity : (0 : ℝ) ≤ 2 ^ 384)
    hηi rfl (Nat.cast_nonneg _) hNKw
    (Nat.cast_nonneg _) hpN hβ0 hNβ hβw ht
  calc ‖(∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ (segmentEmbedding p hm4 x')
          (segmentEmbedding p hm4 x') ∂(model.law : Measure p.SiteMatrix)) -
        ErdosRiabov.semicircleM z‖
      ≤ ‖(∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ (segmentEmbedding p hm4 x')
          (segmentEmbedding p hm4 x') ∂(model.law : Measure p.SiteMatrix)) -
          ∫ G, (G - z • (1 : q.SiteMatrix))⁻¹ x' x'
            ∂(Measure.map coupledShortMatrix (coupledLaw model model'))‖ +
        ‖(∫ G, (G - z • (1 : q.SiteMatrix))⁻¹ x' x'
            ∂(Measure.map coupledShortMatrix (coupledLaw model model'))) -
          ErdosRiabov.semicircleM z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (4 * T * 2 ^ 384 + 5) * (p.W : ℝ) ^ (-(1 : ℝ) / 32) := by
        refine le_trans (add_le_add hA hD) ?_
        exact hfin

/-- **The critical density theorem**, both the density estimate and the unit-intensity
consequence, from the inputs: `inputs.psss` (density bounds, smoothing) and
`inputs.erdosRiabov` (short-ring local law). -/
theorem criticalDensity_holds (inputs : BlockBand.External.NativeInputs.{0}) :
    Internal.Contracts.Inputs.CriticalDensity :=
  criticalDensity_of_meanResolventBound inputs.psss (meanResolventBound_holds inputs.erdosRiabov)

end Assembly

end BlockBand.Density
