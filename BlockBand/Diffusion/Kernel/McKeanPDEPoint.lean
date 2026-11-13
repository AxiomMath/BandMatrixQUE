module

public import BlockBand.Diffusion.Kernel.McKeanContinuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Pointwise calculus of McKean's integrand

For `T > 0` and `w > 1` write `S = arcosh w`, `R = √(w² - 1)` (`= sinh S`) and
`E = e^{-S²/(4T)}`, so that McKean's integrand is `mkMcKeanG T w = G_T(w) = 2 (S/R) E`.
We give closed forms for its derivatives:
* `mk_hasDerivAt_mcKeanG`: `∂_w G = mkGw1 T w = 2 E N₁ / R³`,
  `N₁ = R - S w - R S²/(2T)`;
* `mk_hasDerivAt_gw1`: `∂_w² G = mkGw2 T w = 2 E N₂ / R⁵`,
  `N₂ = -(S/(2T)) N₁ R + N₁' R - 3 w N₁`, `N₁' = -S R - w S²/(2T) - R S/T`;
* `mk_hasDerivAt_mcKeanG_T`: `∂_T G = mkGT T w = G · S²/(4T²)` (any `w`, `T ≠ 0`);
* `mk_gT_eq` (**the `H³` radial heat equation**): for `w > 1`,
  `∂_T G = (w² - 1) ∂_w² G + 3 w ∂_w G + (3/(2T) + 1) G`. (Equivalently the `H³` heat kernel
  `k₃ = (4πT)^{-3/2} e^{-T} G/2` satisfies `∂_T k₃ = (w²-1) k₃'' + 3 w k₃'`.)
* `mk_hasDerivAt_gT_T`, `mk_hasDerivAt_gT_w`, `mk_hasDerivAt_gw1_T`: `∂_T² G = mkGTT`,
  `∂_w ∂_T G = ∂_T ∂_w G = mkGTw` (closed forms, `w > 1`);
* `mk_gw_le`: on `T ∈ [T₁, T₂] ⊂ (0,∞)`, `w ≥ c₀ > 1`, each of `G, ∂_w G, ∂_w² G, ∂_T G,
  ∂_T² G, ∂_T∂_w G` is bounded in absolute value by `mkBd T₁ T₂ c₀ · w⁻⁶`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-!
### Definitions
-/

/-- `N₁ = R - S w - R S²/(2T)`. -/
def mkN1 (T S R w : ℝ) : ℝ := R - S * w - R * S ^ 2 / (2 * T)

/-- `N₁' = -S R - w S²/(2T) - R S/T` (the `s`-derivative of `N₁`). -/
def mkN1d (T S R w : ℝ) : ℝ := -(S * R) - w * S ^ 2 / (2 * T) - R * S / T

/-- `N₂ = -(S/(2T)) N₁ R + N₁' R - 3 w N₁`. -/
def mkN2 (T S R w : ℝ) : ℝ :=
  -(S / (2 * T)) * mkN1 T S R w * R + mkN1d T S R w * R - 3 * w * mkN1 T S R w

/-- The closed form of `∂_w G_T(w)` (valid for `w > 1`). -/
def mkGw1 (T w : ℝ) : ℝ :=
  2 * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) *
    mkN1 T (Real.arcosh w) (Real.sqrt (w ^ 2 - 1)) w / Real.sqrt (w ^ 2 - 1) ^ 3

/-- The closed form of `∂_w² G_T(w)` (valid for `w > 1`). -/
def mkGw2 (T w : ℝ) : ℝ :=
  2 * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) *
    mkN2 T (Real.arcosh w) (Real.sqrt (w ^ 2 - 1)) w / Real.sqrt (w ^ 2 - 1) ^ 5

/-- The closed form of `∂_T G_T(w)`. -/
def mkGT (T w : ℝ) : ℝ := mkMcKeanG T w * ((Real.arcosh w) ^ 2 / (4 * T ^ 2))

/-!
### Derivatives
-/

theorem mk_sqrt_pos {w : ℝ} (hw : 1 < w) : 0 < Real.sqrt (w ^ 2 - 1) :=
  Real.sqrt_pos.2 (by nlinarith)

theorem mk_mcKeanG_eq {T w : ℝ} (hw : 1 < w) :
    mkMcKeanG T w = 2 * (Real.arcosh w / Real.sqrt (w ^ 2 - 1)) *
      Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) := by
  rw [mkMcKeanG, mkSdivSinh, Real.sinh_arcosh hw.le]
  split_ifs with h
  · exact absurd h (Real.arcosh_pos hw).ne'
  · rfl

theorem mk_hasDerivAt_sqrt {w : ℝ} (hw : 1 < w) :
    HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - 1)) (w / Real.sqrt (w ^ 2 - 1)) w := by
  have h := ((hasDerivAt_pow 2 w).sub_const 1).sqrt (by nlinarith : w ^ 2 - 1 ≠ 0)
  convert h using 1
  have := (mk_sqrt_pos hw).ne'
  field_simp
  ring

theorem mk_hasDerivAt_mcKeanG {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    HasDerivAt (mkMcKeanG T) (mkGw1 T w) w := by
  have hR0 := (mk_sqrt_pos hw).ne'
  have hS := Real.hasDerivAt_arcosh (show w ∈ Ioi 1 from hw)
  have hR := mk_hasDerivAt_sqrt hw
  have hE := ((hS.pow 2).neg.div_const (4 * T)).exp
  have h := ((hS.div hR hR0).const_mul 2).mul hE
  have heq : mkMcKeanG T =ᶠ[𝓝 w] fun u => 2 * (Real.arcosh u / Real.sqrt (u ^ 2 - 1)) *
      Real.exp (-(Real.arcosh u) ^ 2 / (4 * T)) := by
    filter_upwards [lt_mem_nhds hw] with u hu
    exact mk_mcKeanG_eq hu
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold mkGw1 mkN1
  simp only [Pi.div_apply, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat]
  field_simp
  ring

theorem mk_hasDerivAt_gw1 {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    HasDerivAt (mkGw1 T) (mkGw2 T w) w := by
  have hR0 := (mk_sqrt_pos hw).ne'
  have hS := Real.hasDerivAt_arcosh (show w ∈ Ioi 1 from hw)
  have hR := mk_hasDerivAt_sqrt hw
  have hE := ((hS.pow 2).neg.div_const (4 * T)).exp
  have hN : HasDerivAt (fun u => mkN1 T (Real.arcosh u) (Real.sqrt (u ^ 2 - 1)) u)
      (mkN1d T (Real.arcosh w) (Real.sqrt (w ^ 2 - 1)) w / Real.sqrt (w ^ 2 - 1)) w := by
    unfold mkN1
    have h := (hR.sub (hS.mul (hasDerivAt_id w))).sub (hR.mul ((hS.pow 2).div_const (2 * T)))
    convert h using 1
    · funext u
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
      ring
    unfold mkN1d
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat]
    field_simp
    ring
  have h := (((hE.const_mul 2).mul hN).div (hR.pow 3) (pow_ne_zero 3 hR0))
  unfold mkGw1
  convert h using 1
  unfold mkGw2 mkN2
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat]
  field_simp
  ring

theorem mk_hasDerivAt_mcKeanG_T {T w : ℝ} (hT : T ≠ 0) :
    HasDerivAt (fun T' => mkMcKeanG T' w) (mkGT T w) T := by
  unfold mkGT
  unfold mkMcKeanG
  have h : HasDerivAt (fun T' => -(Real.arcosh w) ^ 2 / (4 * T'))
      ((Real.arcosh w) ^ 2 / (4 * T ^ 2)) T := by
    have := ((hasDerivAt_id T).const_mul 4).inv (by simpa using hT)
    convert this.const_mul (-(Real.arcosh w) ^ 2) using 1
    · ext T'; simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  convert (h.exp.const_mul (2 * mkSdivSinh (Real.arcosh w))) using 1
  ring

/-- **The `H³` radial heat equation for McKean's integrand.** For `T > 0` (indeed `T ≠ 0`) and
`w > 1`: `∂_T G = (w² - 1) ∂_w² G + 3 w ∂_w G + (3/(2T) + 1) G`. -/
theorem mk_gT_eq {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    mkGT T w = (w ^ 2 - 1) * mkGw2 T w + 3 * w * mkGw1 T w +
      (3 / (2 * T) + 1) * mkMcKeanG T w := by
  have hR0 := (mk_sqrt_pos hw).ne'
  have hsq : (w ^ 2 - 1) * mkGw2 T w = Real.sqrt (w ^ 2 - 1) ^ 2 * mkGw2 T w := by
    rw [Real.sq_sqrt (by nlinarith)]
  unfold mkGT
  rw [mk_mcKeanG_eq hw, hsq]
  unfold mkGw1 mkGw2 mkN2 mkN1d mkN1
  field_simp
  ring

/-!
### Bounds
-/

theorem mk_exp_mul_gauss_le {T : ℝ} (hT : 0 < T) (n S : ℝ) :
    Real.exp (n * S) * Real.exp (-S ^ 2 / (4 * T)) ≤ Real.exp (n ^ 2 * T) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h0 : 0 ≤ (S - 2 * n * T) ^ 2 / (4 * T) := by positivity
  have h1 : (S - 2 * n * T) ^ 2 / (4 * T) = S ^ 2 / (4 * T) - n * S + n ^ 2 * T := by
    field_simp; ring
  rw [neg_div]; linarith

/-- The polynomial factors of the closed forms, in terms of `X = e^S ≥ 1`. -/
theorem mk_N_le {T a X S R w : ℝ} (hT : 0 < T) (ha : 1 ≤ a) (hTa : T⁻¹ ≤ a)
    (hX : 1 ≤ X) (hS : 0 ≤ S) (hSX : S ≤ X) (hR : 0 ≤ R) (hRX : R ≤ X) (hw : 0 ≤ w)
    (hwX : w ≤ X) :
    |mkN1 T S R w| ≤ 3 * a * X ^ 3 ∧ |mkN1d T S R w| ≤ 3 * a * X ^ 3 ∧
      |mkN2 T S R w| ≤ 15 * a ^ 2 * X ^ 5 := by
  have hT' : 0 ≤ T⁻¹ := inv_nonneg.2 hT.le
  have hX0 : 0 ≤ X := by linarith
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have e1 : mkN1 T S R w = R - S * w - R * S ^ 2 * T⁻¹ / 2 := by unfold mkN1; field_simp
  have e2 : mkN1d T S R w = -(S * R) - w * S ^ 2 * T⁻¹ / 2 - R * S * T⁻¹ := by
    unfold mkN1d; field_simp
  have h1 : |mkN1 T S R w| ≤ 3 * a * X ^ 3 := by
    rw [e1]
    have t1 : R ≤ X ^ 3 := by linarith
    have t2 : S * w ≤ X ^ 3 := by nlinarith [mul_le_mul hSX hwX hw hX0]
    have t3 : R * S ^ 2 * T⁻¹ / 2 ≤ a * X ^ 3 := by
      have : R * S ^ 2 ≤ X ^ 3 := by
        have := mul_le_mul hRX (pow_le_pow_left₀ hS hSX 2) (by positivity) hX0
        nlinarith
      have := mul_le_mul this hTa hT' (by positivity)
      nlinarith
    have p3 : 0 ≤ R * S ^ 2 * T⁻¹ / 2 := by positivity
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hS hw]
  have h2 : |mkN1d T S R w| ≤ 3 * a * X ^ 3 := by
    rw [e2]
    have t1 : S * R ≤ X ^ 3 := by nlinarith [mul_le_mul hSX hRX hR hX0]
    have t2 : w * S ^ 2 * T⁻¹ / 2 ≤ a * X ^ 3 := by
      have : w * S ^ 2 ≤ X ^ 3 := by
        have := mul_le_mul hwX (pow_le_pow_left₀ hS hSX 2) (by positivity) hX0
        nlinarith
      have := mul_le_mul this hTa hT' (by positivity)
      nlinarith
    have t3 : R * S * T⁻¹ ≤ a * X ^ 3 := by
      have : R * S ≤ X ^ 3 := by nlinarith [mul_le_mul hRX hSX hS hX0]
      have := mul_le_mul this hTa hT' (by positivity)
      linarith
    have p1 : 0 ≤ S * R := mul_nonneg hS hR
    have p2 : 0 ≤ w * S ^ 2 * T⁻¹ / 2 := by positivity
    have p3 : 0 ≤ R * S * T⁻¹ := by positivity
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨h1, h2, ?_⟩
  have e3 : mkN2 T S R w = -(S * T⁻¹ / 2) * mkN1 T S R w * R + mkN1d T S R w * R -
      3 * w * mkN1 T S R w := by unfold mkN2; field_simp
  rw [e3]
  have hST : S * T⁻¹ / 2 ≤ a * X := by nlinarith [mul_le_mul hSX hTa hT' hX0]
  have hX45 : X ^ 4 ≤ X ^ 5 := by nlinarith
  have hX34 : X ^ 3 ≤ X ^ 4 := by nlinarith
  have q1 : |-(S * T⁻¹ / 2) * mkN1 T S R w * R| ≤ 3 * a ^ 2 * X ^ 5 := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ S * T⁻¹ / 2),
      abs_of_nonneg hR]
    calc S * T⁻¹ / 2 * |mkN1 T S R w| * R ≤ (a * X) * (3 * a * X ^ 3) * X := by
          gcongr
      _ = 3 * a ^ 2 * X ^ 5 := by ring
  have q2 : |mkN1d T S R w * R| ≤ 3 * a ^ 2 * X ^ 5 := by
    rw [abs_mul, abs_of_nonneg hR]
    calc |mkN1d T S R w| * R ≤ (3 * a * X ^ 3) * X := by gcongr
      _ = 3 * a * X ^ 4 := by ring
      _ ≤ 3 * a ^ 2 * X ^ 5 := by gcongr; nlinarith
  have q3 : |3 * w * mkN1 T S R w| ≤ 9 * a ^ 2 * X ^ 5 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    calc 3 * w * |mkN1 T S R w| ≤ 3 * X * (3 * a * X ^ 3) := by gcongr
      _ = 9 * a * X ^ 4 := by ring
      _ ≤ 9 * a ^ 2 * X ^ 5 := by gcongr; nlinarith
  calc |-(S * T⁻¹ / 2) * mkN1 T S R w * R + mkN1d T S R w * R - 3 * w * mkN1 T S R w|
      ≤ |-(S * T⁻¹ / 2) * mkN1 T S R w * R + mkN1d T S R w * R| +
          |3 * w * mkN1 T S R w| := abs_sub _ _
    _ ≤ |-(S * T⁻¹ / 2) * mkN1 T S R w * R| + |mkN1d T S R w * R| +
          |3 * w * mkN1 T S R w| := by gcongr; exact abs_add_le _ _
    _ ≤ 15 * a ^ 2 * X ^ 5 := by linarith

/-!
### Second `T`-derivatives
-/

/-- The closed form of `∂_T² G_T(w)`. -/
def mkGTT (T w : ℝ) : ℝ :=
  mkGT T w * ((Real.arcosh w) ^ 2 / (4 * T ^ 2)) -
    mkMcKeanG T w * ((Real.arcosh w) ^ 2 / (2 * T ^ 3))

/-- The closed form of `∂_w ∂_T G_T(w) = ∂_T ∂_w G_T(w)` (valid for `w > 1`). -/
def mkGTw (T w : ℝ) : ℝ :=
  mkGw1 T w * ((Real.arcosh w) ^ 2 / (4 * T ^ 2)) +
    mkMcKeanG T w * (Real.arcosh w / (2 * T ^ 2 * Real.sqrt (w ^ 2 - 1)))

theorem mk_hasDerivAt_inv_sq {T : ℝ} (hT : T ≠ 0) (S : ℝ) :
    HasDerivAt (fun T' : ℝ => S ^ 2 / (4 * T' ^ 2)) (-(S ^ 2 / (2 * T ^ 3))) T := by
  have h := ((hasDerivAt_pow 2 T).const_mul 4).inv (by positivity)
  convert h.const_mul (S ^ 2) using 1
  · funext T'; simp [div_eq_mul_inv]
  · field_simp; ring

theorem mk_hasDerivAt_gT_T {T w : ℝ} (hT : T ≠ 0) :
    HasDerivAt (fun T' => mkGT T' w) (mkGTT T w) T := by
  have h := (mk_hasDerivAt_mcKeanG_T (w := w) hT).mul (mk_hasDerivAt_inv_sq hT (Real.arcosh w))
  unfold mkGT
  convert h using 1
  unfold mkGTT mkGT; ring

theorem mk_hasDerivAt_gT_w {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    HasDerivAt (mkGT T) (mkGTw T w) w := by
  have hR0 := (mk_sqrt_pos hw).ne'
  have hS := Real.hasDerivAt_arcosh (show w ∈ Ioi 1 from hw)
  have h := (mk_hasDerivAt_mcKeanG hT hw).mul ((hS.pow 2).div_const (4 * T ^ 2))
  unfold mkGT
  convert h using 1
  unfold mkGTw
  simp only [Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

theorem mk_hasDerivAt_gauss_T {T : ℝ} (hT : T ≠ 0) (S : ℝ) :
    HasDerivAt (fun T' => -S ^ 2 / (4 * T')) (S ^ 2 / (4 * T ^ 2)) T := by
  have := ((hasDerivAt_id T).const_mul 4).inv (by simpa using hT)
  convert this.const_mul (-S ^ 2) using 1
  · ext T'; simp [div_eq_mul_inv]
  · simp only [id]; field_simp

theorem mk_hasDerivAt_gw1_T {T w : ℝ} (hT : T ≠ 0) (hw : 1 < w) :
    HasDerivAt (fun T' => mkGw1 T' w) (mkGTw T w) T := by
  have hR0 := (mk_sqrt_pos hw).ne'
  have hE := (mk_hasDerivAt_gauss_T hT (Real.arcosh w)).exp
  have hN : HasDerivAt (fun T' => mkN1 T' (Real.arcosh w) (Real.sqrt (w ^ 2 - 1)) w)
      (Real.sqrt (w ^ 2 - 1) * (Real.arcosh w) ^ 2 / (2 * T ^ 2)) T := by
    unfold mkN1
    have h := ((hasDerivAt_id T).const_mul 2).inv (by simpa using hT)
    have h2 := (h.const_mul (Real.sqrt (w ^ 2 - 1) * (Real.arcosh w) ^ 2)).const_sub
      (Real.sqrt (w ^ 2 - 1) - Real.arcosh w * w)
    convert h2 using 1
    · funext T'; simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  have h := ((hE.const_mul 2).mul hN).div_const (Real.sqrt (w ^ 2 - 1) ^ 3)
  unfold mkGw1
  convert h using 1
  unfold mkGTw mkGw1
  rw [mk_mcKeanG_eq hw]
  field_simp

/-!
### Uniform bounds away from `w = 1`
-/

/-- The uniform constant of `mk_gw_le`. -/
def mkBd (T₁ T₂ c₀ : ℝ) : ℝ :=
  30 * (1 + T₁⁻¹) ^ 4 * (1 + (Real.sqrt (c₀ ^ 2 - 1))⁻¹) ^ 5 * Real.exp (169 * T₂)

theorem mk_bd_nonneg {T₁ T₂ c₀ : ℝ} (hT₁ : 0 < T₁) (hc₀ : 1 < c₀) : 0 ≤ mkBd T₁ T₂ c₀ := by
  unfold mkBd
  have := mk_sqrt_pos hc₀
  have : 0 < T₁⁻¹ := inv_pos.2 hT₁
  positivity

theorem mk_mono_bd {a b X E : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hX : 1 ≤ X) (hE : 0 ≤ E)
    {i j k : ℕ} (hi : i ≤ 4) (hj : j ≤ 5) (hk : k ≤ 7) :
    a ^ i * b ^ j * (E * X ^ k) ≤ a ^ 4 * b ^ 5 * (E * X ^ 7) := by
  have h1 : a ^ i ≤ a ^ 4 := pow_le_pow_right₀ ha hi
  have h2 : b ^ j ≤ b ^ 5 := pow_le_pow_right₀ hb hj
  have h3 : X ^ k ≤ X ^ 7 := pow_le_pow_right₀ hX hk
  have : 0 ≤ a ^ i := by positivity
  have : 0 ≤ b ^ j := by positivity
  have : 0 ≤ X ^ k := by positivity
  gcongr

/-- **Uniform bounds.** For `0 < T₁ ≤ T ≤ T₂` and `1 < c₀ ≤ w`, each of `G_T(w)`, `∂_w G`,
`∂_w² G`, `∂_T G`, `∂_T² G`, `∂_T∂_w G` is at most `mkBd T₁ T₂ c₀ · w⁻⁶` in absolute value. -/
theorem mk_gw_le {T₁ T₂ T c₀ w : ℝ} (hT₁ : 0 < T₁) (h₁ : T₁ ≤ T) (h₂ : T ≤ T₂) (hc₀ : 1 < c₀)
    (hw : c₀ ≤ w) :
    |mkMcKeanG T w| ≤ mkBd T₁ T₂ c₀ * (w ^ 6)⁻¹ ∧ |mkGw1 T w| ≤ mkBd T₁ T₂ c₀ * (w ^ 6)⁻¹ ∧
      |mkGw2 T w| ≤ mkBd T₁ T₂ c₀ * (w ^ 6)⁻¹ ∧ |mkGT T w| ≤ mkBd T₁ T₂ c₀ * (w ^ 6)⁻¹ ∧
      |mkGTT T w| ≤ mkBd T₁ T₂ c₀ * (w ^ 6)⁻¹ ∧ |mkGTw T w| ≤ mkBd T₁ T₂ c₀ * (w ^ 6)⁻¹ := by
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hT : 0 < T := lt_of_lt_of_le hT₁ h₁
  have hgE : mkMcKeanG T w ≤ 2 * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) := by
    unfold mkMcKeanG
    have := mk_sdivSinh_le_one (Real.arcosh w)
    calc 2 * mkSdivSinh (Real.arcosh w) * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T))
        ≤ 2 * 1 * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) := by gcongr
      _ = _ := by ring
  have hg0 := mk_mcKeanG_pos T w
  unfold mkGTT mkGTw
  unfold mkGT
  unfold mkGw1 mkGw2
  set g := mkMcKeanG T w with hgdef
  set S := Real.arcosh w with hSdef
  set R := Real.sqrt (w ^ 2 - 1) with hRdef
  set X := Real.exp S with hXdef
  have hS0 : 0 ≤ S := Real.arcosh_nonneg hw1
  have hXe : X = w + R := Real.exp_arcosh hw1
  have hR0' : 0 ≤ R := Real.sqrt_nonneg _
  have hwX : w ≤ X := by linarith
  have hRX : R ≤ X := by linarith
  have hSX : S ≤ X := by linarith [Real.add_one_le_exp S]
  have hX1 : 1 ≤ X := Real.one_le_exp hS0
  have hX0 : 0 < X := by linarith
  set R₀ := Real.sqrt (c₀ ^ 2 - 1) with hR₀def
  have hR₀ : 0 < R₀ := mk_sqrt_pos hc₀
  have hR₀R : R₀ ≤ R := Real.sqrt_le_sqrt (by nlinarith)
  have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR₀R
  set a := 1 + T₁⁻¹ with hadef
  set b := 1 + R₀⁻¹ with hbdef
  have ha1 : 1 ≤ a := by have := inv_pos.2 hT₁; linarith
  have hTa : T⁻¹ ≤ a := by have := inv_anti₀ hT₁ h₁; linarith
  have hb1 : 1 ≤ b := by have := inv_pos.2 hR₀; linarith
  have hRb : R⁻¹ ≤ b := (inv_anti₀ hR₀ hR₀R).trans (by linarith)
  set E := Real.exp (-S ^ 2 / (4 * T)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hEX : E * X ^ 7 ≤ Real.exp (169 * T₂) * (w ^ 6)⁻¹ := by
    have hET : E ≤ Real.exp (-S ^ 2 / (4 * T₂)) := by
      apply Real.exp_le_exp.2
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h13 := mk_exp_mul_gauss_le (lt_of_lt_of_le hT h₂) 13 S
    have hX7 : X ^ 7 = Real.exp (13 * S) * Real.exp (-(6 * S)) := by
      rw [← Real.exp_add, hXdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hX6 : Real.exp (-(6 * S)) ≤ (w ^ 6)⁻¹ := by
      rw [Real.exp_neg]
      apply inv_anti₀ (by positivity)
      rw [show 6 * S = (6 : ℕ) * S by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ hw0.le hwX 6
    rw [hX7]
    calc E * (Real.exp (13 * S) * Real.exp (-(6 * S)))
        ≤ Real.exp (-S ^ 2 / (4 * T₂)) * (Real.exp (13 * S) * Real.exp (-(6 * S))) := by
          gcongr
      _ = Real.exp (13 * S) * Real.exp (-S ^ 2 / (4 * T₂)) * Real.exp (-(6 * S)) := by ring
      _ ≤ Real.exp (13 ^ 2 * T₂) * (w ^ 6)⁻¹ := by gcongr
      _ = _ := by norm_num
  have hP : 0 ≤ a ^ 4 * b ^ 5 * (E * X ^ 7) := by positivity
  have key : ∀ y : ℝ, |y| ≤ 30 * (a ^ 4 * b ^ 5 * (E * X ^ 7)) →
      |y| ≤ mkBd T₁ T₂ c₀ * (w ^ 6)⁻¹ := fun y hy => by
    refine hy.trans ?_
    have : mkBd T₁ T₂ c₀ = 30 * a ^ 4 * b ^ 5 * Real.exp (169 * T₂) := rfl
    rw [this]
    have := mul_le_mul_of_nonneg_left hEX (by positivity : (0 : ℝ) ≤ 30 * a ^ 4 * b ^ 5)
    calc 30 * (a ^ 4 * b ^ 5 * (E * X ^ 7)) = 30 * a ^ 4 * b ^ 5 * (E * X ^ 7) := by ring
      _ ≤ 30 * a ^ 4 * b ^ 5 * (Real.exp (169 * T₂) * (w ^ 6)⁻¹) := this
      _ = _ := by ring
  have mono := fun (i j k : ℕ) (hi : i ≤ 4) (hj : j ≤ 5) (hk : k ≤ 7) =>
    mk_mono_bd ha1 hb1 hX1 hE0.le hi hj hk
  obtain ⟨hN1, -, hN2⟩ := mk_N_le hT ha1 hTa hX1 hS0 hSX hR0' hRX hw0.le hwX
  have hTa2 : T⁻¹ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hT.le) hTa 2
  have hTa3 : T⁻¹ ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (inv_nonneg.2 hT.le) hTa 3
  have hS2 : S ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hS0 hSX 2
  have hST : S ^ 2 / (4 * T ^ 2) ≤ a ^ 2 * X ^ 2 := by
    rw [div_eq_mul_inv, mul_inv, ← inv_pow]
    calc S ^ 2 * ((4 : ℝ)⁻¹ * T⁻¹ ^ 2) ≤ X ^ 2 * (1 * a ^ 2) := by gcongr; norm_num
      _ = a ^ 2 * X ^ 2 := by ring
  have hST3 : S ^ 2 / (2 * T ^ 3) ≤ a ^ 3 * X ^ 2 := by
    rw [div_eq_mul_inv, mul_inv, ← inv_pow]
    calc S ^ 2 * ((2 : ℝ)⁻¹ * T⁻¹ ^ 3) ≤ X ^ 2 * (1 * a ^ 3) := by gcongr; norm_num
      _ = a ^ 3 * X ^ 3 / X := by field_simp
      _ = a ^ 3 * X ^ 2 := by field_simp
  have hST1 : S / (2 * T ^ 2 * R) ≤ a ^ 2 * b * X := by
    rw [div_eq_mul_inv, mul_inv, mul_inv, ← inv_pow]
    calc S * ((2 : ℝ)⁻¹ * T⁻¹ ^ 2 * R⁻¹) ≤ X * (1 * a ^ 2 * b) := by
          gcongr; norm_num
      _ = a ^ 2 * b * X := by ring
  have hG1 : |2 * E * mkN1 T S R w / R ^ 3| ≤ 6 * (a ^ 1 * b ^ 3 * (E * X ^ 3)) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hE0, abs_of_pos (pow_pos hRpos 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv, ← inv_pow]
    calc 2 * E * |mkN1 T S R w| * R⁻¹ ^ 3 ≤ 2 * E * (3 * a * X ^ 3) * b ^ 3 := by gcongr
      _ = 6 * (a ^ 1 * b ^ 3 * (E * X ^ 3)) := by ring
  have hGT : |g * (S ^ 2 / (4 * T ^ 2))| ≤ 2 * (a ^ 2 * b ^ 0 * (E * X ^ 2)) := by
    rw [abs_mul, abs_of_pos hg0, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (4 * T ^ 2))]
    calc g * (S ^ 2 / (4 * T ^ 2)) ≤ (2 * E) * (a ^ 2 * X ^ 2) := by gcongr
      _ = 2 * (a ^ 2 * b ^ 0 * (E * X ^ 2)) := by ring
  refine ⟨key _ ?_, key _ ?_, key _ ?_, key _ ?_, key _ ?_, key _ ?_⟩
  · rw [abs_of_pos hg0]
    calc g ≤ 2 * E := hgE
      _ = 2 * (a ^ 0 * b ^ 0 * (E * X ^ 0)) := by ring
      _ ≤ 2 * (a ^ 4 * b ^ 5 * (E * X ^ 7)) := by
          exact mul_le_mul_of_nonneg_left (mono 0 0 0 (by norm_num) (by norm_num) (by norm_num))
            (by norm_num)
      _ ≤ _ := by linarith
  · calc _ ≤ 6 * (a ^ 1 * b ^ 3 * (E * X ^ 3)) := hG1
      _ ≤ 6 * (a ^ 4 * b ^ 5 * (E * X ^ 7)) := by
          exact mul_le_mul_of_nonneg_left (mono 1 3 3 (by norm_num) (by norm_num) (by norm_num))
            (by norm_num)
      _ ≤ _ := by linarith
  · rw [abs_div, abs_mul, abs_mul, abs_of_pos hE0, abs_of_pos (pow_pos hRpos 5),
      abs_of_pos (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv, ← inv_pow]
    calc 2 * E * |mkN2 T S R w| * R⁻¹ ^ 5 ≤ 2 * E * (15 * a ^ 2 * X ^ 5) * b ^ 5 := by
          gcongr
      _ = 30 * (a ^ 2 * b ^ 5 * (E * X ^ 5)) := by ring
      _ ≤ 30 * (a ^ 4 * b ^ 5 * (E * X ^ 7)) := by
          exact mul_le_mul_of_nonneg_left (mono 2 5 5 (by norm_num) (by norm_num) (by norm_num))
            (by norm_num)
  · calc _ ≤ 2 * (a ^ 2 * b ^ 0 * (E * X ^ 2)) := hGT
      _ ≤ 2 * (a ^ 4 * b ^ 5 * (E * X ^ 7)) := by
          exact mul_le_mul_of_nonneg_left (mono 2 0 2 (by norm_num) (by norm_num) (by norm_num))
            (by norm_num)
      _ ≤ _ := by linarith
  · have h1 : |g * (S ^ 2 / (4 * T ^ 2)) * (S ^ 2 / (4 * T ^ 2))| ≤
        2 * (a ^ 4 * b ^ 0 * (E * X ^ 4)) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (4 * T ^ 2))]
      calc |g * (S ^ 2 / (4 * T ^ 2))| * (S ^ 2 / (4 * T ^ 2))
          ≤ 2 * (a ^ 2 * b ^ 0 * (E * X ^ 2)) * (a ^ 2 * X ^ 2) := by gcongr
        _ = 2 * (a ^ 4 * b ^ 0 * (E * X ^ 4)) := by ring
    have h2 : |g * (S ^ 2 / (2 * T ^ 3))| ≤ 2 * (a ^ 3 * b ^ 0 * (E * X ^ 2)) := by
      rw [abs_mul, abs_of_pos hg0, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (2 * T ^ 3))]
      calc g * (S ^ 2 / (2 * T ^ 3)) ≤ (2 * E) * (a ^ 3 * X ^ 2) := by gcongr
        _ = 2 * (a ^ 3 * b ^ 0 * (E * X ^ 2)) := by ring
    have m1 := mono 4 0 4 (by norm_num) (by norm_num) (by norm_num)
    have m2 := mono 3 0 2 (by norm_num) (by norm_num) (by norm_num)
    calc |g * (S ^ 2 / (4 * T ^ 2)) * (S ^ 2 / (4 * T ^ 2)) - g * (S ^ 2 / (2 * T ^ 3))|
        ≤ |g * (S ^ 2 / (4 * T ^ 2)) * (S ^ 2 / (4 * T ^ 2))| + |g * (S ^ 2 / (2 * T ^ 3))| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  · have h1 : |2 * E * mkN1 T S R w / R ^ 3 * (S ^ 2 / (4 * T ^ 2))| ≤
        6 * (a ^ 3 * b ^ 3 * (E * X ^ 5)) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (4 * T ^ 2))]
      calc |2 * E * mkN1 T S R w / R ^ 3| * (S ^ 2 / (4 * T ^ 2))
          ≤ 6 * (a ^ 1 * b ^ 3 * (E * X ^ 3)) * (a ^ 2 * X ^ 2) := by gcongr
        _ = 6 * (a ^ 3 * b ^ 3 * (E * X ^ 5)) := by ring
    have h2 : |g * (S / (2 * T ^ 2 * R))| ≤ 2 * (a ^ 2 * b ^ 1 * (E * X ^ 1)) := by
      rw [abs_mul, abs_of_pos hg0, abs_of_nonneg (by positivity : 0 ≤ S / (2 * T ^ 2 * R))]
      calc g * (S / (2 * T ^ 2 * R)) ≤ (2 * E) * (a ^ 2 * b * X) := by gcongr
        _ = 2 * (a ^ 2 * b ^ 1 * (E * X ^ 1)) := by ring
    have m1 := mono 3 3 5 (by norm_num) (by norm_num) (by norm_num)
    have m2 := mono 2 1 1 (by norm_num) (by norm_num) (by norm_num)
    calc |2 * E * mkN1 T S R w / R ^ 3 * (S ^ 2 / (4 * T ^ 2)) + g * (S / (2 * T ^ 2 * R))|
        ≤ |2 * E * mkN1 T S R w / R ^ 3 * (S ^ 2 / (4 * T ^ 2))| +
            |g * (S / (2 * T ^ 2 * R))| := abs_add_le _ _
      _ ≤ _ := by linarith

end BlockBand.Diffusion
