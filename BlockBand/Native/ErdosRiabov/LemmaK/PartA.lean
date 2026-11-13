module

public import BlockBand.Native.ErdosRiabov.LemmaK.Theta
public import BlockBand.Native.ErdosRiabov.Kernel.Control

/-!
# The kernel lemma: the constant `C_K`, short times `t ≤ 1/4`, and (K4)

For short times the VS kernels are bounded by the polynomial control through their Neumann
series, and the profile `S` is bounded by and acts boundedly on `Υ_h`.

Setting: `S = shortRingProfile b m W` on `Fin (mW)`, `0 < b < 1/2`, `m ≥ 4`, `W ≥ 1`;
`Υ_h = polynomialControl (mW) W D h`, `D ≥ 0`; ceiling `H = C₀ + 1`, `r = √(C₀+1)`, `C₀ ≥ 1`.

* `lemmaK_partA`: for `|μ|, |μ'| < 1`, `t ∈ [0, 1/4]` and all sites, with `A_t = vsKernel S μ μ' t`:
  `|A_t(x,y)| ≤ 4/(3W)` and `|A_t(x,y)| ≤ C_A Υ_h(x,y)` for every `h ∈ (0, C₀+1]`.
  Proof: `|A_t(x,y)| ≤ Σ_k 4^{-k} (S^{k+1})_{xy}`; the term `k` vanishes unless
  `d(x,y) < (k+2)W` (`shortRingProfile_pow_eq_zero_of_far`), and then
  `(S^{k+1})_{xy} ≤ 1/W ≤ r^{1+D} (k+3)^{⌈D⌉} Υ_h(x,y)` (`polynomialControl_lower`).
* `lemmaK_K4_explicit` / `lemmaK_K4` (clause (K4)): for `h ∈ (0, C₀+1]`,
  `S ≤ r(1+2r)^D Υ_h` and `S Υ_h ≤ (1+2r)^D Υ_h ≤ r(1+2r)^D Υ_h` entrywise.

Constants (explicit, depending only on `b, κ, C₀, D`):
* `lemmaKGeomSum D = Σ_k (k+3)^{⌈D⌉} 4^{-k}` (finite);
* `lemmaKPartAConst C₀ D = C_A = lemmaKGeomSum D · r · r^D`;
* `lemmaKConst b κ C₀ D = C_K = max (4 C_A/(3 c_m)) (max (8 C₁'' (C₀+1)^{1+D/2}) (r(1+2r)^D))`,
  `c_m = imLower κ C₀`, `C₁'' = lemmaKC1 b κ C₀ D`.

`C_K` is an explicit majorant of `max{C_N √(4/(3c_m)), 4√2 C₁''(C₀+1)^{1+D/2}, r(1+2r)^D}`
(same dependencies, no `δ₀`); each clause of the kernel lemma is proved with a constant `≤ C_K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LemmaK

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

/-!
## Constants
-/

/-- `Σ_k (k+3)^{⌈D⌉} 4^{-k}`, the short-time series constant. -/
def lemmaKGeomSum (D : ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 3) ^ ⌈D⌉₊ * (1 / 4 : ℝ) ^ k

/-- `C_A = lemmaKGeomSum D · r · r^D`, `r = √(C₀+1)` (short-time constant). -/
def lemmaKPartAConst (C₀ D : ℝ) : ℝ :=
  lemmaKGeomSum D * (Real.sqrt (C₀ + 1) * Real.sqrt (C₀ + 1) ^ D)

/-- The kernel constant `C_K` (explicit; depends only on `b, κ, C₀, D`). -/
def lemmaKConst (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) (κ C₀ D : ℝ) : ℝ :=
  max (4 * lemmaKPartAConst C₀ D / (3 * imLower κ C₀))
    (max (8 * lemmaKC1 b hb0 hb κ C₀ D * (C₀ + 1) ^ (1 + D / 2))
      (Real.sqrt (C₀ + 1) * (1 + 2 * Real.sqrt (C₀ + 1)) ^ D))

/-- The short-time series `Σ_k (k+3)^n 4^{-k}` converges. -/
theorem lemmaKGeomSum_summable (n : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + 3) ^ n * (1 / 4 : ℝ) ^ k) := by
  have h4 : ‖(1 / 4 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have hb : Summable (fun k : ℕ => ((k + 3 : ℕ) : ℝ) ^ n * (1 / 4 : ℝ) ^ (k + 3)) :=
    (summable_nat_add_iff (f := fun j : ℕ => (j : ℝ) ^ n * (1 / 4 : ℝ) ^ j) 3).mpr
      (summable_pow_mul_geometric_of_norm_lt_one n h4)
  refine (hb.mul_left 64).congr (fun k => ?_)
  rw [pow_add, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- `r = √(C₀+1) ≥ 1` for `C₀ ≥ 1`. -/
theorem lemmaK_one_le_sqrt {C₀ : ℝ} (hC₀ : 1 ≤ C₀) : 1 ≤ Real.sqrt (C₀ + 1) := by
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ C₀ + 1 by linarith)
  rwa [Real.sqrt_one] at h

/-- `C_A ≥ 1`. -/
theorem lemmaKPartAConst_ge_one {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ lemmaKPartAConst C₀ D := by
  have hr := lemmaK_one_le_sqrt hC₀
  have hrD : 1 ≤ Real.sqrt (C₀ + 1) ^ D := Real.one_le_rpow hr hD
  have hG : 1 ≤ lemmaKGeomSum D := by
    have h0 := (lemmaKGeomSum_summable ⌈D⌉₊).le_tsum 0 (fun j _ => by positivity)
    refine le_trans ?_ h0
    simp only [Nat.cast_zero, zero_add, pow_zero, mul_one]
    exact one_le_pow₀ (by norm_num)
  unfold lemmaKPartAConst
  have : 1 ≤ Real.sqrt (C₀ + 1) * Real.sqrt (C₀ + 1) ^ D := by nlinarith
  nlinarith

/-- `0 < c_m ≤ 1/2` for `κ > 0`, `C₀ ≥ 1`. -/
theorem lemmaK_imLower_bounds {κ C₀ : ℝ} (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) :
    0 < imLower κ C₀ ∧ imLower κ C₀ ≤ 1 / 2 := by
  have hk0 : 0 < min κ 2 := lt_min hκ two_pos
  have hk2 : min κ 2 ≤ 2 := min_le_right _ _
  have hs0 : 0 < bulkSin κ := by
    unfold bulkSin
    exact div_pos (Real.sqrt_pos.2 (mul_pos hk0 (by linarith))) two_pos
  have hs1 : bulkSin κ ≤ 1 := by
    unfold bulkSin
    have h := Real.sqrt_le_sqrt (show min κ 2 * (4 - min κ 2) ≤ 2 ^ 2 by nlinarith)
    rw [Real.sqrt_sq (by norm_num)] at h
    linarith
  unfold imLower
  refine ⟨div_pos hs0 (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The pieces of `C_K` used in the proofs. -/
theorem lemmaKConst_facts {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ C₀ D : ℝ} (hκ : 0 < κ)
    (hC₀ : 1 ≤ C₀) (hD : 0 ≤ D) :
    lemmaKPartAConst C₀ D ≤ lemmaKConst b hb0 hb κ C₀ D ∧
    4 * lemmaKPartAConst C₀ D / (3 * imLower κ C₀) ≤ lemmaKConst b hb0 hb κ C₀ D ∧
    8 / 3 ≤ lemmaKConst b hb0 hb κ C₀ D ∧
    8 * lemmaKC1 b hb0 hb κ C₀ D ≤ lemmaKConst b hb0 hb κ C₀ D ∧
    4 * lemmaKC1 b hb0 hb κ C₀ D * (C₀ + 1) ^ (1 + D / 2) ≤ lemmaKConst b hb0 hb κ C₀ D ∧
    Real.sqrt (C₀ + 1) * (1 + 2 * Real.sqrt (C₀ + 1)) ^ D ≤ lemmaKConst b hb0 hb κ C₀ D ∧
    0 < lemmaKConst b hb0 hb κ C₀ D := by
  obtain ⟨hc0, hc1⟩ := lemmaK_imLower_bounds hκ hC₀
  have hA := lemmaKPartAConst_ge_one hC₀ hD
  have hC1 := lemmaKC1_ge_one hb0 hb κ C₀ D
  have hp : 1 ≤ (C₀ + 1) ^ (1 + D / 2) := Real.one_le_rpow (by linarith) (by linarith)
  set A := lemmaKPartAConst C₀ D
  set c := imLower κ C₀
  set C1 := lemmaKC1 b hb0 hb κ C₀ D
  have h1 : A ≤ 4 * A / (3 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : 8 / 3 ≤ 4 * A / (3 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hm1 : 4 * A / (3 * c) ≤ lemmaKConst b hb0 hb κ C₀ D := le_max_left _ _
  have hm2 : 8 * C1 * (C₀ + 1) ^ (1 + D / 2) ≤ lemmaKConst b hb0 hb κ C₀ D :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hm3 : Real.sqrt (C₀ + 1) * (1 + 2 * Real.sqrt (C₀ + 1)) ^ D ≤
      lemmaKConst b hb0 hb κ C₀ D :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨h1.trans hm1, hm1, h2.trans hm1, le_trans ?_ hm2, le_trans ?_ hm2, hm3, ?_⟩
  · nlinarith
  · nlinarith
  · linarith

/-!
## A lower bound for `Υ_h` at distance `≤ cW`
-/

/-- For `d(x,y) ≤ cW` (`c ≥ 0`), `h ∈ (0, H]`, `H ≥ 1`, `1 ≤ W ≤ N`, `D ≥ 0`:
`1/W ≤ √H (1 + c√H)^D Υ_h(x,y)`. -/
theorem lemmaK_inv_width_le {N W : ℕ} (hWN : W ≤ N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {H h : ℝ} (hH : 1 ≤ H) (hh : 0 < h) (hhH : h ≤ H) {c : ℝ} (hc : 0 ≤ c) (x y : Fin N)
    (hd : (ErdosRiabov.cyclicDistance N x y : ℝ) ≤ c * W) :
    1 / (W : ℝ) ≤ Real.sqrt H * (1 + c * Real.sqrt H) ^ D * polynomialControl N W D h x y := by
  have hlow := polynomialControl_lower hWN hW hD hH hh hhH x y
  have hr1 : 1 ≤ Real.sqrt H := by
    have h1 := Real.sqrt_le_sqrt hH
    rwa [Real.sqrt_one] at h1
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set r := Real.sqrt H with hr
  set d : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ) with hdd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hr0 : 0 < r := by linarith
  have hX1 : 1 ≤ 1 + r * d / W := by
    have : 0 ≤ r * d / W := by positivity
    linarith
  have hXle : 1 + r * d / W ≤ 1 + c * r := by
    have : r * d / W ≤ c * r := by
      rw [div_le_iff₀ hWr]
      nlinarith
    linarith
  have hXpos : 0 < (1 + r * d / W) ^ D := Real.rpow_pos_of_pos (by linarith) D
  have hle : (1 + r * d / W) ^ D ≤ (1 + c * r) ^ D := Real.rpow_le_rpow (by linarith) hXle hD
  rw [Real.rpow_neg (by linarith)] at hlow
  have hcpos : 0 < (1 + c * r) ^ D := Real.rpow_pos_of_pos (by positivity) D
  calc 1 / (W : ℝ) = r * (1 + c * r) ^ D * (((W : ℝ) * r)⁻¹ * ((1 + c * r) ^ D)⁻¹) := by
        field_simp
    _ ≤ r * (1 + c * r) ^ D * (((W : ℝ) * r)⁻¹ * ((1 + r * d / W) ^ D)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (inv_anti₀ hXpos hle) (by positivity)) (by positivity)
    _ ≤ r * (1 + c * r) ^ D * polynomialControl N W D h x y :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-!
## The Neumann series for `t ≤ 1/4`
-/

/-- **Part A of Lemma K**.
For
`S = shortRingProfile b m W` (`0 < b < 1/2`, `m ≥ 4`, `W ≥ 1`), `|μ|, |μ'| < 1`,
`t ∈ [0, 1/4]`, all sites:
`|A_t(x,y)| ≤ 4/(3W)`, and for every `h ∈ (0, C₀+1]`
(`C₀ ≥ 1`, `D ≥ 0`):
`|A_t(x,y)| ≤ C_A Υ_h(x,y)`.
Holds for Θ- and Ξ-type pairs alike.
-/
theorem lemmaK_partA {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W)
    {C₀ D : ℝ} (hC₀ : 1 ≤ C₀) (hD : 0 ≤ D) {μ μ' : ℂ} (hμ : ‖μ‖ < 1) (hμ' : ‖μ'‖ < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (x y : Fin (m * W)) :
    ‖vsKernel (shortRingProfile b m W) μ μ' t x y‖ ≤ 4 / (3 * W) ∧
    ∀ h : ℝ, 0 < h → h ≤ C₀ + 1 →
      ‖vsKernel (shortRingProfile b m W) μ μ' t x y‖ ≤
        lemmaKPartAConst C₀ D * polynomialControl (m * W) W D h x y := by
  set S := shortRingProfile b m W with hSdef
  have hS : StochasticSymm S := shortRingProfile_stochasticSymm hb0 hb (by omega) hW
  have hμμ : ‖μ‖ * ‖μ'‖ ≤ 1 := by nlinarith [norm_nonneg μ, norm_nonneg μ']
  have ha : ‖(t : ℂ) * (μ * μ')‖ ≤ 1 / 4 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg μ, norm_nonneg μ']
  have ha1 : ‖(t : ℂ) * (μ * μ')‖ < 1 := by linarith
  set a := (t : ℂ) * (μ * μ') with hadef
  have hsumm := summable_norm_term hS ha1 1 x y
  have hbase : ‖vsKernel S μ μ' t x y‖ ≤ ∑' k : ℕ, ‖a ^ k * ((S ^ (k + 1)) x y : ℂ)‖ := by
    rw [vsKernel_apply hS ha1 x y, norm_mul]
    calc ‖μ * μ'‖ * ‖∑' k : ℕ, a ^ k * ((S ^ (k + 1)) x y : ℂ)‖
        ≤ 1 * ‖∑' k : ℕ, a ^ k * ((S ^ (k + 1)) x y : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (by rw [norm_mul]; exact hμμ) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact norm_tsum_le_tsum_norm hsumm
  have hterm : ∀ k : ℕ,
      ‖a ^ k * ((S ^ (k + 1)) x y : ℂ)‖ ≤ (1 / 4 : ℝ) ^ k * (S ^ (k + 1)) x y := by
    intro k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hS.pow_nonneg _ x y)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ha k)
      (hS.pow_nonneg _ x y)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hpowle : ∀ k : ℕ, (S ^ (k + 1)) x y ≤ 1 / (W : ℝ) := fun k =>
    (shortRingProfile_pow_le hb0 hb (by omega) hW (by omega) x y).2
  refine ⟨?_, fun h hh hhC => ?_⟩
  · have hg : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k * (1 / (W : ℝ))) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
    calc ‖vsKernel S μ μ' t x y‖ ≤ ∑' k : ℕ, ‖a ^ k * ((S ^ (k + 1)) x y : ℂ)‖ := hbase
      _ ≤ ∑' k : ℕ, (1 / 4 : ℝ) ^ k * (1 / (W : ℝ)) :=
          Summable.tsum_le_tsum (fun k => (hterm k).trans
            (mul_le_mul_of_nonneg_left (hpowle k) (by positivity))) hsumm hg
      _ = 4 / (3 * W) := by
          rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          field_simp
          norm_num
  · have hN : 0 < m * W := Nat.mul_pos (by omega) hW
    have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
    have hH : (1 : ℝ) ≤ C₀ + 1 := by linarith
    have hr1 := lemmaK_one_le_sqrt hC₀
    set r := Real.sqrt (C₀ + 1) with hrdef
    set n := ⌈D⌉₊ with hndef
    have hΥ := polynomialControl_pos hN hW D hh x y
    set B := r * r ^ D * polynomialControl (m * W) W D h x y with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hg : Summable (fun k : ℕ => ((k : ℝ) + 3) ^ n * (1 / 4 : ℝ) ^ k * B) :=
      (lemmaKGeomSum_summable n).mul_right B
    have hk : ∀ k : ℕ,
        ‖a ^ k * ((S ^ (k + 1)) x y : ℂ)‖ ≤ ((k : ℝ) + 3) ^ n * (1 / 4 : ℝ) ^ k * B := by
      intro k
      refine (hterm k).trans ?_
      by_cases hfar : (k + 1 + 1) * W ≤ ErdosRiabov.cyclicDistance (m * W) x y
      · rw [hSdef, shortRingProfile_pow_eq_zero_of_far b (k + 1) hfar, mul_zero]
        positivity
      · rw [not_le] at hfar
        have hk3 : (1 : ℝ) ≤ (k : ℝ) + 3 := by
          have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
          linarith
        have hd : (ErdosRiabov.cyclicDistance (m * W) x y : ℝ) ≤ ((k : ℝ) + 2) * W := by
          have h1 : ErdosRiabov.cyclicDistance (m * W) x y ≤ (k + 2) * W := by
            have : (k + 1 + 1) * W = (k + 2) * W := by ring
            omega
          have h2 : ((ErdosRiabov.cyclicDistance (m * W) x y : ℕ) : ℝ) ≤
              (((k + 2) * W : ℕ) : ℝ) := by exact_mod_cast h1
          push_cast at h2
          exact h2
        have hinv := lemmaK_inv_width_le hWN hW hD hH hh hhC (c := (k : ℝ) + 2)
          (by positivity) x y hd
        have hpow : (1 + ((k : ℝ) + 2) * r) ^ D ≤ r ^ D * ((k : ℝ) + 3) ^ n := by
          calc (1 + ((k : ℝ) + 2) * r) ^ D ≤ (r * ((k : ℝ) + 3)) ^ D :=
                Real.rpow_le_rpow (by positivity) (by nlinarith) hD
            _ = r ^ D * ((k : ℝ) + 3) ^ D := Real.mul_rpow (by linarith) (by linarith)
            _ ≤ r ^ D * ((k : ℝ) + 3) ^ (n : ℝ) :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_exponent_le hk3 (Nat.le_ceil D)) (by positivity)
            _ = r ^ D * ((k : ℝ) + 3) ^ n := by rw [Real.rpow_natCast]
        have hq : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ k := by positivity
        calc (1 / 4 : ℝ) ^ k * (S ^ (k + 1)) x y ≤ (1 / 4 : ℝ) ^ k * (1 / (W : ℝ)) :=
              mul_le_mul_of_nonneg_left (hpowle k) hq
          _ ≤ (1 / 4 : ℝ) ^ k *
                (r * (1 + ((k : ℝ) + 2) * r) ^ D * polynomialControl (m * W) W D h x y) :=
              mul_le_mul_of_nonneg_left hinv hq
          _ ≤ (1 / 4 : ℝ) ^ k *
                (r * (r ^ D * ((k : ℝ) + 3) ^ n) * polynomialControl (m * W) W D h x y) := by
              gcongr
          _ = ((k : ℝ) + 3) ^ n * (1 / 4 : ℝ) ^ k * B := by rw [hBdef]; ring
    calc ‖vsKernel S μ μ' t x y‖ ≤ ∑' k : ℕ, ‖a ^ k * ((S ^ (k + 1)) x y : ℂ)‖ := hbase
      _ ≤ ∑' k : ℕ, ((k : ℝ) + 3) ^ n * (1 / 4 : ℝ) ^ k * B :=
          Summable.tsum_le_tsum hk hsumm hg
      _ = lemmaKPartAConst C₀ D * polynomialControl (m * W) W D h x y := by
          rw [tsum_mul_right, hBdef, lemmaKPartAConst, lemmaKGeomSum]
          ring

/-!
## (K4)
-/

/-- Shift of `Υ_h` by a site at distance `≤ 2W`. -/
theorem lemmaK_control_shift {N W : ℕ} (hN : 0 < N) (hWN : W ≤ N) (hW : 0 < W) {D : ℝ}
    (hD : 0 ≤ D) {H h : ℝ} (hH : 1 ≤ H) (hh : 0 < h) (hhH : h ≤ H) (x a y : Fin N)
    (hxa : (ErdosRiabov.cyclicDistance N x a : ℝ) ≤ 2 * W) :
    polynomialControl N W D h a y ≤
      (1 + 2 * Real.sqrt H) ^ D * polynomialControl N W D h x y := by
  have hl := loc_pos hN hW hh
  obtain ⟨hlW, -⟩ := loc_bounds_of_le hWN hH hh hhH
  have htri : (ErdosRiabov.cyclicDistance N x y : ℝ) ≤
      ErdosRiabov.cyclicDistance N x a + ErdosRiabov.cyclicDistance N a y := by
    exact_mod_cast cyclicDistance_triangle N x a y
  simp only [polynomialControl]
  set ℓ := ErdosRiabov.localizationLength N W h with hℓ
  set r := Real.sqrt H with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hWl : (W : ℝ) ≤ r * ℓ := by
    rw [div_le_iff₀ hr0] at hlW
    linarith
  set day : ℝ := (ErdosRiabov.cyclicDistance N a y : ℝ) with hday
  set dxy : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ) with hdxy
  have hday0 : 0 ≤ day := Nat.cast_nonneg _
  have hdxy0 : 0 ≤ dxy := Nat.cast_nonneg _
  have hA1 : 1 ≤ 1 + day / ℓ := by
    have : 0 ≤ day / ℓ := by positivity
    linarith
  have hB1 : 1 ≤ 1 + dxy / ℓ := by
    have : 0 ≤ dxy / ℓ := by positivity
    linarith
  have hBA : 1 + dxy / ℓ ≤ (1 + 2 * r) * (1 + day / ℓ) := by
    have h1 : dxy / ℓ ≤ 2 * r + day / ℓ := by
      rw [div_le_iff₀ hl]
      have : (2 * r + day / ℓ) * ℓ = 2 * r * ℓ + day := by
        rw [add_mul, div_mul_cancel₀ _ hl.ne']
      rw [this]
      linarith
    have : 0 ≤ 2 * r * (day / ℓ) := by positivity
    nlinarith
  have hc : 0 < (1 + 2 * r) ^ D := Real.rpow_pos_of_pos (by linarith) D
  have hApos : 0 < (1 + day / ℓ) ^ D := Real.rpow_pos_of_pos (by linarith) D
  have hBpos : 0 < (1 + dxy / ℓ) ^ D := Real.rpow_pos_of_pos (by linarith) D
  have hle : (1 + dxy / ℓ) ^ D ≤ (1 + 2 * r) ^ D * (1 + day / ℓ) ^ D := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hBA hD
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith)]
  have key : ((1 + day / ℓ) ^ D)⁻¹ ≤ (1 + 2 * r) ^ D * ((1 + dxy / ℓ) ^ D)⁻¹ := by
    calc ((1 + day / ℓ) ^ D)⁻¹ =
          (1 + 2 * r) ^ D * ((1 + 2 * r) ^ D * (1 + day / ℓ) ^ D)⁻¹ := by
          field_simp
      _ ≤ (1 + 2 * r) ^ D * ((1 + dxy / ℓ) ^ D)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hBpos hle) hc.le
  have hlh : 0 ≤ (ℓ * h)⁻¹ := by positivity
  calc (ℓ * h)⁻¹ * ((1 + day / ℓ) ^ D)⁻¹
      ≤ (ℓ * h)⁻¹ * ((1 + 2 * r) ^ D * ((1 + dxy / ℓ) ^ D)⁻¹) :=
        mul_le_mul_of_nonneg_left key hlh
    _ = _ := by ring

/-- (K4) with the explicit constants `r(1+2r)^D` and `(1+2r)^D`, `r = √(C₀+1)`. -/
theorem lemmaK_K4_explicit {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {m W : ℕ} (hm : 4 ≤ m)
    (hW : 0 < W) {C₀ D : ℝ} (hC₀ : 1 ≤ C₀) (hD : 0 ≤ D) {h : ℝ} (hh : 0 < h)
    (hhC : h ≤ C₀ + 1) (x y : Fin (m * W)) :
    shortRingProfile b m W x y ≤ Real.sqrt (C₀ + 1) * (1 + 2 * Real.sqrt (C₀ + 1)) ^ D *
      polynomialControl (m * W) W D h x y ∧
    (shortRingProfile b m W * polynomialControl (m * W) W D h) x y ≤
      (1 + 2 * Real.sqrt (C₀ + 1)) ^ D * polynomialControl (m * W) W D h x y := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  have hH : (1 : ℝ) ≤ C₀ + 1 := by linarith
  have hr1 := lemmaK_one_le_sqrt hC₀
  have hΥ := polynomialControl_pos hN hW D hh x y
  have hnear : ∀ u v : Fin (m * W), shortRingProfile b m W u v ≠ 0 →
      (ErdosRiabov.cyclicDistance (m * W) u v : ℝ) ≤ 2 * W := by
    intro u v huv
    have h1 := shortRingProfile_support huv
    have h2 := cyclicDistance_add_one_le u v
    have h3 : ErdosRiabov.cyclicDistance (m * W) u v ≤ 2 * W := by nlinarith
    exact_mod_cast h3
  refine ⟨?_, ?_⟩
  · by_cases h0 : shortRingProfile b m W x y = 0
    · rw [h0]
      positivity
    · have hS1 : shortRingProfile b m W x y ≤ 1 / (W : ℝ) := by
        have := (shortRingProfile_pow_le hb0 hb (by omega) hW le_rfl x y).2
        rwa [pow_one] at this
      exact hS1.trans (lemmaK_inv_width_le hWN hW hD hH hh hhC (by norm_num) x y
        (hnear x y h0))
  · rw [Matrix.mul_apply]
    calc ∑ a, shortRingProfile b m W x a * polynomialControl (m * W) W D h a y
        ≤ ∑ a, shortRingProfile b m W x a *
            ((1 + 2 * Real.sqrt (C₀ + 1)) ^ D * polynomialControl (m * W) W D h x y) := by
          refine Finset.sum_le_sum fun a _ => ?_
          by_cases h0 : shortRingProfile b m W x a = 0
          · rw [h0, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left
              (lemmaK_control_shift hN hWN hW hD hH hh hhC x a y (hnear x a h0))
              (shortRingProfile_nonneg hb0 hb m W x a)
      _ = (1 + 2 * Real.sqrt (C₀ + 1)) ^ D * polynomialControl (m * W) W D h x y := by
          rw [← Finset.sum_mul, shortRingProfile_rowSum b (by omega) hW x, one_mul]

/-- For `0 < b < 1/2`,
`κ > 0`, `C₀ ≥ 1`, `D ≥ 0`, `m ≥ 4`, `W ≥ 1`, every height `h ∈ (0, C₀+1]` and all sites:
`S_{xy} ≤ C_K Υ_h(x,y)` and `(S Υ_h)_{xy} ≤ C_K Υ_h(x,y)`, `S = shortRingProfile b m W`,
`Υ_h = polynomialControl (mW) W D h`, `C_K = lemmaKConst b κ C₀ D`.
-/
theorem lemmaK_K4 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ C₀ D : ℝ} (hκ : 0 < κ)
    (hC₀ : 1 ≤ C₀) (hD : 0 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {h : ℝ} (hh : 0 < h)
    (hhC : h ≤ C₀ + 1) (x y : Fin (m * W)) :
    shortRingProfile b m W x y ≤
      lemmaKConst b hb0 hb κ C₀ D * polynomialControl (m * W) W D h x y ∧
    (shortRingProfile b m W * polynomialControl (m * W) W D h) x y ≤
      lemmaKConst b hb0 hb κ C₀ D * polynomialControl (m * W) W D h x y := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hΥ := polynomialControl_pos hN hW D hh x y
  obtain ⟨h1, h2⟩ := lemmaK_K4_explicit hb0 hb hm hW hC₀ hD hh hhC x y
  have hK := (lemmaKConst_facts hb0 hb hκ hC₀ hD).2.2.2.2.2.1
  have hr1 := lemmaK_one_le_sqrt hC₀
  have hp : 0 ≤ (1 + 2 * Real.sqrt (C₀ + 1)) ^ D := by positivity
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right hK hΥ.le), h2.trans ?_⟩
  refine mul_le_mul_of_nonneg_right (le_trans ?_ hK) hΥ.le
  nlinarith

end BlockBand.Native.ErdosRiabov.LemmaK
