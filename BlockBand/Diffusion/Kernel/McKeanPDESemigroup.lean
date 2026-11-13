module

public import BlockBand.Diffusion.Kernel.McKeanPDEDiag

/-!
# The backward equation for the McKean semigroup `u = ∫ pX f`

Lebesgue measure on `[0, ∞)` in `x'`; `D₀ > 0`; `f` measurable with `|f| ≤ M`. Put
`u(t, x) = mkU D0 f t x = ∫_{[0,∞)} pX_t(x, x') f(x') dx'` (this is `mkSemigroupX D0 f (t, x)`
for `t > 0`) and
`mkU1 = ∫ mkPX1 (D₀t/2) x x' f(x') dx'`, `mkU2 = ∫ mkPX2 (D₀t/2) x x' f(x') dx'`,
`mkUT = ∫ (D₀/2) mkPXT (D₀t/2) x x' f(x') dx'`.

* `mk_px_decay`: for `(T, x)` in a compact box of `(0,∞) × (0,∞)`, `|mkPX1|, |mkPX2|, |mkPXT|`
  are `≤ Q (1 + x'²)⁻¹` uniformly (from `|∂_c^j K_T(c)| ≲ c⁻⁵`, `cosh d ≥ (1+2x')/(2(1+2x))` and
  `|C_x|, |C_xx| ≲ 1 + 2x'`).
* For `t > 0`, `x > 0`: `∂_x u = mkU1` (`mk_hasDerivAt_u_x`), `∂_x mkU1 = mkU2`
  (`mk_hasDerivAt_u1_x`), `∂_t u = mkUT` (`mk_hasDerivAt_u_t`), and
  `∂_t u = (D₀/2)[x(1+x) ∂_x² u + (1+2x) ∂_x u]` (`mk_u_pde`, `deriv` form);
  `mk_u_derivs_continuousOn`: `u, mkU1, mkU2, mkUT` are jointly continuous on
  `(0,∞) × (0,∞)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped Interval

/-!
### Decay of the derivative kernels in `x'`
-/

theorem mk_beta_le {x' : ℝ} (hx' : 0 ≤ x') : Real.sqrt (x' * (1 + x')) ≤ (1 + 2 * x') / 2 := by
  rw [Real.sqrt_le_left (by positivity)]; nlinarith

/-- `|C_x|, |C_xx| ≤ L (1 + 2x')` for `x ∈ [z₁, z₂]`, `z₁ > 0`. -/
theorem mk_cx_le_lin {z₁ z₂ x x' θ : ℝ} (hz₁ : 0 < z₁) (h1 : z₁ ≤ x) (h2 : x ≤ z₂)
    (hx' : 0 ≤ x') :
    |mkCx x x' θ| ≤ (2 + (1 + 2 * z₂) / Real.sqrt (z₁ * (1 + z₁))) * (1 + 2 * x') ∧
      |mkCxx x x' θ| ≤ (4 * (z₂ * (1 + z₂)) + (1 + 2 * z₂) ^ 2) /
        (2 * Real.sqrt (z₁ * (1 + z₁)) ^ 3) * (1 + 2 * x') := by
  have hx : 0 < x := lt_of_lt_of_le hz₁ h1
  set α := Real.sqrt (x * (1 + x)) with hαdef
  set α₁ := Real.sqrt (z₁ * (1 + z₁)) with hα₁def
  set β := Real.sqrt (x' * (1 + x')) with hβdef
  set y := 1 + 2 * x' with hy
  have hα₁ : 0 < α₁ := mk_al_pos hz₁
  have hα₁α : α₁ ≤ α := Real.sqrt_le_sqrt (by nlinarith)
  have hα : 0 < α := lt_of_lt_of_le hα₁ hα₁α
  have hαsq : α ^ 2 = x * (1 + x) := Real.sq_sqrt (by positivity)
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβy : β ≤ y / 2 := mk_beta_le hx'
  have hy0 : 0 ≤ y := by positivity
  have hc := Real.abs_cos_le_one θ
  have ha : 1 + 2 * x ≤ 1 + 2 * z₂ := by linarith
  have ha0 : 0 < 1 + 2 * x := by linarith
  constructor
  · unfold mkCx
    rw [← hαdef, ← hβdef, ← hy]
    have hq : (1 + 2 * x) / (2 * α) ≤ (1 + 2 * z₂) / (2 * α₁) :=
      div_le_div₀ (by linarith) ha (by positivity) (by linarith)
    have hq0 : 0 ≤ (1 + 2 * x) / (2 * α) := by positivity
    calc |2 * y - 4 * β * Real.cos θ * ((1 + 2 * x) / (2 * α))|
        ≤ |2 * y| + |4 * β * Real.cos θ * ((1 + 2 * x) / (2 * α))| := abs_sub _ _
      _ = 2 * y + 4 * β * |Real.cos θ| * ((1 + 2 * x) / (2 * α)) := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * y), abs_mul, abs_mul,
            abs_of_nonneg (by positivity : 0 ≤ 4 * β), abs_of_nonneg hq0]
      _ ≤ 2 * y + 4 * (y / 2) * 1 * ((1 + 2 * z₂) / (2 * α₁)) := by gcongr
      _ = (2 + (1 + 2 * z₂) / α₁) * y := by field_simp; ring
  · unfold mkCxx
    rw [← hαdef, ← hβdef]
    have hn : |4 * α - (1 + 2 * x) ^ 2 / α| ≤ 4 * α + (1 + 2 * x) ^ 2 / α := by
      have : 0 ≤ (1 + 2 * x) ^ 2 / α := by positivity
      rw [abs_le]; constructor <;> linarith
    have hfrac : (4 * α + (1 + 2 * x) ^ 2 / α) / (4 * α ^ 2) =
        (4 * α ^ 2 + (1 + 2 * x) ^ 2) / (4 * α ^ 3) := by field_simp
    have hnum : 4 * α ^ 2 + (1 + 2 * x) ^ 2 ≤ 4 * (z₂ * (1 + z₂)) + (1 + 2 * z₂) ^ 2 := by
      rw [hαsq]
      have : x * (1 + x) ≤ z₂ * (1 + z₂) := by nlinarith
      have : (1 + 2 * x) ^ 2 ≤ (1 + 2 * z₂) ^ 2 := pow_le_pow_left₀ ha0.le ha 2
      linarith
    have hden : 4 * α₁ ^ 3 ≤ 4 * α ^ 3 := by gcongr
    have hz₂ : 0 < z₂ := by linarith
    have hnn : 0 ≤ 4 * (z₂ * (1 + z₂)) + (1 + 2 * z₂) ^ 2 := by positivity
    have hb : (4 * α ^ 2 + (1 + 2 * x) ^ 2) / (4 * α ^ 3) ≤
        (4 * (z₂ * (1 + z₂)) + (1 + 2 * z₂) ^ 2) / (4 * α₁ ^ 3) :=
      div_le_div₀ hnn hnum (by positivity) hden
    calc |-(4 * β * Real.cos θ) * ((4 * α - (1 + 2 * x) ^ 2 / α) / (4 * α ^ 2))|
        = 4 * β * |Real.cos θ| * (|4 * α - (1 + 2 * x) ^ 2 / α| / (4 * α ^ 2)) := by
          rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_div,
            abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num), abs_of_nonneg hβ0,
            abs_of_pos (show (0 : ℝ) < 4 * α ^ 2 by positivity)]
      _ ≤ 4 * (y / 2) * 1 * ((4 * α + (1 + 2 * x) ^ 2 / α) / (4 * α ^ 2)) := by gcongr
      _ = 2 * y * ((4 * α ^ 2 + (1 + 2 * x) ^ 2) / (4 * α ^ 3)) := by rw [hfrac]; ring
      _ ≤ 2 * y * ((4 * (z₂ * (1 + z₂)) + (1 + 2 * z₂) ^ 2) / (4 * α₁ ^ 3)) := by gcongr
      _ = _ := by field_simp; ring

/-- Uniform `c⁻⁵` bounds of `|∂_cK|, |∂_c²K|, |∂_TK|` on `T ∈ [T₀/2, 3T₀/2]`, `c > 1`. -/
theorem mk_k_box5 {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ Kb, 0 ≤ Kb ∧ ∀ T ∈ Icc (T₀ - T₀ / 2) (T₀ + T₀ / 2), ∀ c, 1 < c →
      |mkK1 T c| ≤ Kb * (c ^ 5)⁻¹ ∧ |mkK2 T c| ≤ Kb * (c ^ 5)⁻¹ ∧
        |mkKT T c| ≤ Kb * (c ^ 5)⁻¹ := by
  have hpos : ∀ T ∈ Icc (T₀ - T₀ / 2) (T₀ + T₀ / 2), 0 < T := fun T hT => by linarith [hT.1]
  obtain ⟨A, hA⟩ := mk_bound_of_continuousAt₁ fun T hT => mk_mkA_continuousAt (hpos T hT)
  obtain ⟨A1, hA1⟩ := mk_bound_of_continuousAt₁ fun T hT => mk_mkA1_continuousAt (hpos T hT)
  have hT₀m : T₀ ∈ Icc (T₀ - T₀ / 2) (T₀ + T₀ / 2) := ⟨by linarith, by linarith⟩
  have hAn : 0 ≤ A := (abs_nonneg _).trans (hA T₀ hT₀m)
  have hA1n : 0 ≤ A1 := (abs_nonneg _).trans (hA1 T₀ hT₀m)
  set B := mkBdG (T₀ - T₀ / 2) (T₀ + T₀ / 2) * (π / 2)
  have hB : 0 ≤ B := by
    have := mk_bdG_nonneg (T₂ := T₀ + T₀ / 2) (by linarith : 0 < T₀ - T₀ / 2)
    positivity
  refine ⟨(A + A1) * B, by positivity, fun T hT c hc => ?_⟩
  obtain ⟨b1, b2, bT, -, -⟩ := mk_k_global (by linarith : 0 < T₀ - T₀ / 2) hT.1 hT.2 hc
  have hA0 : |mkA T| ≤ A := hA T hT
  have hA10 : |mkA1 T| ≤ A1 := hA1 T hT
  have e : mkBdG (T₀ - T₀ / 2) (T₀ + T₀ / 2) * (π / 2) * (c ^ 5)⁻¹ = B * (c ^ 5)⁻¹ := rfl
  rw [e] at b1 b2 bT
  have hc5 : 0 ≤ (c ^ 5)⁻¹ := by have : 0 < c := by linarith
                                 positivity
  refine ⟨?_, ?_, ?_⟩
  · calc |mkK1 T c| ≤ |mkA T| * (B * (c ^ 5)⁻¹) := b1
      _ ≤ (A + A1) * (B * (c ^ 5)⁻¹) := by gcongr; linarith
      _ = (A + A1) * B * (c ^ 5)⁻¹ := by ring
  · calc |mkK2 T c| ≤ |mkA T| * (B * (c ^ 5)⁻¹) := b2
      _ ≤ (A + A1) * (B * (c ^ 5)⁻¹) := by gcongr; linarith
      _ = (A + A1) * B * (c ^ 5)⁻¹ := by ring
  · calc |mkKT T c| ≤ (|mkA1 T| + |mkA T|) * (B * (c ^ 5)⁻¹) := bT
      _ ≤ (A1 + A) * (B * (c ^ 5)⁻¹) := by gcongr
      _ = (A + A1) * B * (c ^ 5)⁻¹ := by ring

/-- `cosh d⁻⁵ ≤ L⁵ (1 + 2x')⁻⁵` with `L = 2(1 + 2z₂)` for `x ≤ z₂`. -/
theorem mk_hypCos_inv_pow_le {x x' z₂ θ : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (h2 : x ≤ z₂) :
    (mkHypCos x x' θ ^ 5)⁻¹ ≤ (2 * (1 + 2 * z₂)) ^ 5 * ((1 + 2 * x') ^ 5)⁻¹ := by
  have hb := mk_b_le_hypCos hx hx' θ
  have hC1 := (mk_hypCos_sub_one hx hx' θ).1
  have hC0 : 0 < mkHypCos x x' θ := by linarith
  have hy : 0 < 1 + 2 * x' := by linarith
  have hL : 1 + 2 * x' ≤ 2 * (1 + 2 * z₂) * mkHypCos x x' θ := by
    calc 1 + 2 * x' ≤ 2 * (1 + 2 * x) * mkHypCos x x' θ := hb
      _ ≤ 2 * (1 + 2 * z₂) * mkHypCos x x' θ := by gcongr
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
    div_le_iff₀ (by positivity)]
  calc (1 + 2 * x') ^ 5 ≤ (2 * (1 + 2 * z₂) * mkHypCos x x' θ) ^ 5 :=
        pow_le_pow_left₀ hy.le hL 5
    _ = (2 * (1 + 2 * z₂)) ^ 5 * mkHypCos x x' θ ^ 5 := by ring

/-- **Decay in `x'`.** For `T₀, x₀ > 0` there is `Q` with
`|mkPX1 T x x'|, |mkPX2 T x x'|, |mkPXT T x x'| ≤ Q (1 + x'²)⁻¹` for
`T ∈ [T₀/2, 3T₀/2]`, `x ∈ [x₀/2, 3x₀/2]`, `x' ≥ 0`. -/
theorem mk_px_decay {T₀ x₀ : ℝ} (hT₀ : 0 < T₀) (hx₀ : 0 < x₀) :
    ∃ Q, ∀ T ∈ Icc (T₀ - T₀ / 2) (T₀ + T₀ / 2), ∀ x ∈ Icc (x₀ - x₀ / 2) (x₀ + x₀ / 2),
      ∀ x', 0 ≤ x' → |mkPX1 T x x'| ≤ Q * (1 + x' ^ 2)⁻¹ ∧
        |mkPX2 T x x'| ≤ Q * (1 + x' ^ 2)⁻¹ ∧ |mkPXT T x x'| ≤ Q * (1 + x' ^ 2)⁻¹ := by
  obtain ⟨Kb, hKb0, hKb⟩ := mk_k_box5 hT₀
  set z₁ := x₀ - x₀ / 2
  set z₂ := x₀ + x₀ / 2
  have hz₁ : 0 < z₁ := by simp only [z₁]; linarith
  set Lx := 2 + (1 + 2 * z₂) / Real.sqrt (z₁ * (1 + z₁))
  set Lxx := (4 * (z₂ * (1 + z₂)) + (1 + 2 * z₂) ^ 2) / (2 * Real.sqrt (z₁ * (1 + z₁)) ^ 3)
  set L := (2 * (1 + 2 * z₂)) ^ 5
  have hα₁ := mk_al_pos hz₁
  have hLx : 0 ≤ Lx := by positivity
  have hLxx : 0 ≤ Lxx := by positivity
  have hL : 0 ≤ L := by positivity
  set P := Kb * L * (1 + Lx + Lx ^ 2 + Lxx)
  have hP : 0 ≤ P := by positivity
  refine ⟨2 * (P * (2 * π)), fun T hT x hx x' hx' => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le hz₁ hx.1
  set y := 1 + 2 * x' with hy
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hr : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), (mkHypCos x x' θ ^ 5)⁻¹ ≤ L * (y ^ 5)⁻¹ := fun θ _ =>
    mk_hypCos_inv_pow_le hx0.le hx' hx.2
  have hy3 : (y ^ 3)⁻¹ ≤ (1 + x' ^ 2)⁻¹ := mk_inv_cube_le hx'
  have hy53 : (y ^ 5)⁻¹ ≤ (y ^ 3)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hy1 (by norm_num))
  have hy54 : (y ^ 5)⁻¹ * y ≤ (y ^ 3)⁻¹ := by
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [show (y ^ 3)⁻¹ * y ^ 5 = y ^ 2 by field_simp]
    nlinarith
  have hy52 : (y ^ 5)⁻¹ * y ^ 2 = (y ^ 3)⁻¹ := by field_simp
  -- a pointwise bound `|F θ| ≤ P (y³)⁻¹` gives `|2 ∫ F| ≤ Q (1 + x'²)⁻¹`
  have key : ∀ F : ℝ → ℝ, (∀ θ ∈ Ioo (0 : ℝ) (2 * π), |F θ| ≤ P * (y ^ 3)⁻¹) →
      |2 * ∫ θ in (0 : ℝ)..(2 * π), F θ| ≤ 2 * (P * (2 * π)) * (1 + x' ^ 2)⁻¹ := by
    intro F hF
    have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := 0) (b := 2 * π)
      (C := P * (y ^ 3)⁻¹) (f := F) (mk_ae_Ioo (fun θ => ‖F θ‖ ≤ P * (y ^ 3)⁻¹)
        fun θ hθ => by rw [Real.norm_eq_abs]; exact hF θ hθ)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos] at h
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * |∫ θ in (0 : ℝ)..(2 * π), F θ| ≤ 2 * (P * (y ^ 3)⁻¹ * (2 * π)) := by gcongr
      _ = 2 * (P * (2 * π)) * (y ^ 3)⁻¹ := by ring
      _ ≤ 2 * (P * (2 * π)) * (1 + x' ^ 2)⁻¹ := by gcongr
  have hKC : ∀ θ ∈ Ioo (0 : ℝ) (2 * π),
      |mkK1 T (mkHypCos x x' θ)| ≤ Kb * L * (y ^ 5)⁻¹ ∧
        |mkK2 T (mkHypCos x x' θ)| ≤ Kb * L * (y ^ 5)⁻¹ ∧
        |mkKT T (mkHypCos x x' θ)| ≤ Kb * L * (y ^ 5)⁻¹ := fun θ hθ => by
    have hC := mk_one_lt_hypCos_Ioo hx0 hx' hθ
    obtain ⟨k1, k2, kT⟩ := hKb T hT _ hC
    have h5 : Kb * (mkHypCos x x' θ ^ 5)⁻¹ ≤ Kb * L * (y ^ 5)⁻¹ := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hr θ hθ) hKb0
    exact ⟨k1.trans h5, k2.trans h5, kT.trans h5⟩
  have hcx := fun θ => mk_cx_le_lin (θ := θ) hz₁ hx.1 hx.2 hx'
  refine ⟨key _ fun θ hθ => ?_, key _ fun θ hθ => ?_, key _ fun θ hθ => ?_⟩
  · obtain ⟨k1, -, -⟩ := hKC θ hθ
    obtain ⟨c1, -⟩ := hcx θ
    rw [abs_mul]
    calc |mkK1 T (mkHypCos x x' θ)| * |mkCx x x' θ| ≤ (Kb * L * (y ^ 5)⁻¹) * (Lx * y) := by
          gcongr
      _ = Kb * L * Lx * ((y ^ 5)⁻¹ * y) := by ring
      _ ≤ Kb * L * Lx * (y ^ 3)⁻¹ := by gcongr
      _ ≤ P * (y ^ 3)⁻¹ := by
          gcongr
          simp only [P]
          have : 0 ≤ Kb * L := by positivity
          nlinarith [sq_nonneg Lx]
  · obtain ⟨k1, k2, -⟩ := hKC θ hθ
    obtain ⟨c1, c2⟩ := hcx θ
    have hc2 : |mkCx x x' θ ^ 2| ≤ (Lx * y) ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) c1 2
    calc |mkK2 T (mkHypCos x x' θ) * mkCx x x' θ ^ 2 + mkK1 T (mkHypCos x x' θ) * mkCxx x x' θ|
        ≤ |mkK2 T (mkHypCos x x' θ)| * |mkCx x x' θ ^ 2| +
            |mkK1 T (mkHypCos x x' θ)| * |mkCxx x x' θ| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (Kb * L * (y ^ 5)⁻¹) * (Lx * y) ^ 2 + (Kb * L * (y ^ 5)⁻¹) * (Lxx * y) := by
          gcongr
      _ = Kb * L * (Lx ^ 2 * ((y ^ 5)⁻¹ * y ^ 2) + Lxx * ((y ^ 5)⁻¹ * y)) := by ring
      _ ≤ Kb * L * (Lx ^ 2 * (y ^ 3)⁻¹ + Lxx * (y ^ 3)⁻¹) := by rw [hy52]; gcongr
      _ ≤ P * (y ^ 3)⁻¹ := by
          simp only [P]
          have : 0 ≤ Kb * L := by positivity
          have : 0 ≤ (y ^ 3)⁻¹ := by positivity
          have : Kb * L * (Lx ^ 2 * (y ^ 3)⁻¹ + Lxx * (y ^ 3)⁻¹) =
              Kb * L * (Lx ^ 2 + Lxx) * (y ^ 3)⁻¹ := by ring
          rw [this]
          gcongr
          linarith
  · obtain ⟨-, -, kT⟩ := hKC θ hθ
    calc |mkKT T (mkHypCos x x' θ)| ≤ Kb * L * (y ^ 5)⁻¹ := kT
      _ ≤ Kb * L * (y ^ 3)⁻¹ := by gcongr
      _ ≤ P * (y ^ 3)⁻¹ := by
          gcongr
          simp only [P]
          have : 0 ≤ Kb * L := by positivity
          nlinarith [sq_nonneg Lx]

/-!
### Measurability in `x'`
-/

theorem mk_angular_measurable {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) :
    Measurable fun x' => ∫ θ in (0 : ℝ)..(2 * π), g x' θ := by
  simp_rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact (hg.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Ioc 0 (2 * π)))).measurable

theorem mk_px_measurable {T : ℝ} (x : ℝ) :
    Measurable (fun x' => mkPX1 T x x') ∧ Measurable (fun x' => mkPX2 T x x') ∧
      Measurable (fun x' => mkPXT T x x') := by
  have hk := mk_k_measurable T
  have hC : Continuous fun q : ℝ × ℝ => mkHypCos x q.1 q.2 := by unfold mkHypCos; fun_prop
  have hcx : Continuous fun q : ℝ × ℝ => mkCx x q.1 q.2 := by unfold mkCx; fun_prop
  have hcxx : Continuous fun q : ℝ × ℝ => mkCxx x q.1 q.2 := by unfold mkCxx; fun_prop
  refine ⟨?_, ?_, ?_⟩
  · unfold mkPX1
    exact (mk_angular_measurable (g := fun x' θ => mkK1 T (mkHypCos x x' θ) * mkCx x x' θ)
      ((hk.1.comp hC.measurable).mul hcx.measurable)).const_mul 2
  · unfold mkPX2
    have h1 : Measurable (mkK1 T) := hk.1
    have h2 : Measurable (mkK2 T) := hk.2.1
    have hCm := hC.measurable
    have hcxm := hcx.measurable
    have hcxxm := hcxx.measurable
    have hm : Measurable fun q : ℝ × ℝ => mkK2 T (mkHypCos x q.1 q.2) * mkCx x q.1 q.2 ^ 2 +
        mkK1 T (mkHypCos x q.1 q.2) * mkCxx x q.1 q.2 := by fun_prop
    exact (mk_angular_measurable (g := fun x' θ => mkK2 T (mkHypCos x x' θ) * mkCx x x' θ ^ 2 +
      mkK1 T (mkHypCos x x' θ) * mkCxx x x' θ) hm).const_mul 2
  · unfold mkPXT
    exact (mk_angular_measurable (g := fun x' θ => mkKT T (mkHypCos x x' θ))
      (hk.2.2.1.comp hC.measurable)).const_mul 2

/-!
### The semigroup and its derivatives
-/

/-- `u(t, x) = ∫_{[0,∞)} pX_t(x, x') f(x') dx'`. -/
def mkU (D0 : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ := ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * f x'

/-- `∂_x u`. -/
def mkU1 (D0 : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ x' in Ici (0 : ℝ), mkPX1 (D0 * t / 2) x x' * f x'

/-- `∂_x² u`. -/
def mkU2 (D0 : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ x' in Ici (0 : ℝ), mkPX2 (D0 * t / 2) x x' * f x'

/-- `∂_t u`. -/
def mkUT (D0 : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ x' in Ici (0 : ℝ), D0 / 2 * mkPXT (D0 * t / 2) x x' * f x'

theorem mk_semigroupX_eq_u {D0 : ℝ} (f : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) :
    mkSemigroupX D0 f (t, x) = mkU D0 f t x := by
  simp [mkSemigroupX, mkU, ht]

theorem mk_integrable_mul_f {g f : ℝ → ℝ} {Q M : ℝ} (hg : Measurable g) (hf : Measurable f)
    (hM : ∀ y, |f y| ≤ M) (hb : ∀ x', 0 ≤ x' → |g x'| ≤ Q * (1 + x' ^ 2)⁻¹) :
    IntegrableOn (fun x' => g x' * f x') (Ici 0) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (Q * M)).integrableOn)
    (hg.mul hf).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc |g x'| * |f x'| ≤ Q * (1 + x' ^ 2)⁻¹ * M :=
        mul_le_mul (hb x' hx') (hM x') (abs_nonneg _) ((abs_nonneg _).trans (hb x' hx'))
    _ = Q * M * (1 + x' ^ 2)⁻¹ := by ring

theorem mk_bound_mul_f {a b Q M x' : ℝ} (ha : |a| ≤ Q * (1 + x' ^ 2)⁻¹) (hb : |b| ≤ M) :
    ‖a * b‖ ≤ Q * M * (1 + x' ^ 2)⁻¹ := by
  rw [Real.norm_eq_abs, abs_mul]
  calc |a| * |b| ≤ Q * (1 + x' ^ 2)⁻¹ * M :=
        mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
    _ = Q * M * (1 + x' ^ 2)⁻¹ := by ring

/-- **`∂_x u = mkU1`** for `t > 0`, `x > 0`. -/
theorem mk_hasDerivAt_u_x {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (fun z => mkU D0 f t z) (mkU1 D0 f t x) x := by
  have hT₀ : 0 < D0 * t / 2 := by positivity
  obtain ⟨Q, hQ⟩ := mk_px_decay hT₀ hx
  have hTm : D0 * t / 2 ∈ Icc (D0 * t / 2 - D0 * t / 2 / 2) (D0 * t / 2 + D0 * t / 2 / 2) :=
    ⟨by linarith, by linarith⟩
  have hs : Icc (x - x / 2) (x + x / 2) ∈ 𝓝 x := Icc_mem_nhds (by linarith) (by linarith)
  unfold mkU mkU1
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x' => mkKernelX D0 t z x' * f x')
    (F' := fun z x' => mkPX1 (D0 * t / 2) z x' * f x')
    (bound := fun x' => Q * M * (1 + x' ^ 2)⁻¹) hs
    (Eventually.of_forall fun z => ((mk_kernelX_measurable_snd D0 t z).mul hf).aestronglyMeasurable)
    ((mk_integrableOn_kernelX hD0 ht hx.le).mul_bdd hf.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y))
    (((mk_px_measurable x).1.mul hf).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' z hz =>
      mk_bound_mul_f (hQ _ hTm z hz x' hx').1 (hM x')))
    ((integrable_inv_one_add_sq.const_mul (Q * M)).integrableOn)
    ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' z hz =>
      (mk_hasDerivAt_kernelX_x' hD0 ht (by linarith [hz.1]) hx').mul_const (f x')))).2

/-- **`∂_x mkU1 = mkU2`** for `t > 0`, `x > 0`. -/
theorem mk_hasDerivAt_u1_x {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (fun z => mkU1 D0 f t z) (mkU2 D0 f t x) x := by
  have hT₀ : 0 < D0 * t / 2 := by positivity
  obtain ⟨Q, hQ⟩ := mk_px_decay hT₀ hx
  have hTm : D0 * t / 2 ∈ Icc (D0 * t / 2 - D0 * t / 2 / 2) (D0 * t / 2 + D0 * t / 2 / 2) :=
    ⟨by linarith, by linarith⟩
  have hxm : x ∈ Icc (x - x / 2) (x + x / 2) := ⟨by linarith, by linarith⟩
  have hs : Icc (x - x / 2) (x + x / 2) ∈ 𝓝 x := Icc_mem_nhds (by linarith) (by linarith)
  unfold mkU1 mkU2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x' => mkPX1 (D0 * t / 2) z x' * f x')
    (F' := fun z x' => mkPX2 (D0 * t / 2) z x' * f x')
    (bound := fun x' => Q * M * (1 + x' ^ 2)⁻¹) hs
    (Eventually.of_forall fun z =>
      ((mk_px_measurable (T := D0 * t / 2) z).1.mul hf).aestronglyMeasurable)
    (mk_integrable_mul_f (mk_px_measurable x).1 hf hM fun x' hx' => (hQ _ hTm x hxm x' hx').1)
    (((mk_px_measurable x).2.1.mul hf).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' z hz =>
      mk_bound_mul_f (hQ _ hTm z hz x' hx').2.1 (hM x')))
    ((integrable_inv_one_add_sq.const_mul (Q * M)).integrableOn)
    ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' z hz =>
      (mk_hasDerivAt_kernelX_xx' hD0 ht (by linarith [hz.1]) hx').mul_const (f x')))).2

/-- **`∂_t u = mkUT`** for `t > 0`, `x > 0`. -/
theorem mk_hasDerivAt_u_t {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (fun s => mkU D0 f s x) (mkUT D0 f t x) t := by
  have hT₀ : 0 < D0 * t / 2 := by positivity
  obtain ⟨Q, hQ⟩ := mk_px_decay hT₀ hx
  have hxm : x ∈ Icc (x - x / 2) (x + x / 2) := ⟨by linarith, by linarith⟩
  have hs : Icc (t - t / 2) (t + t / 2) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hTm : ∀ s ∈ Icc (t - t / 2) (t + t / 2),
      D0 * s / 2 ∈ Icc (D0 * t / 2 - D0 * t / 2 / 2) (D0 * t / 2 + D0 * t / 2 / 2) :=
    fun s hs => ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hD : |D0 / 2| = D0 / 2 := abs_of_pos (by positivity)
  unfold mkU mkUT
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x' => mkKernelX D0 s x x' * f x')
    (F' := fun s x' => D0 / 2 * mkPXT (D0 * s / 2) x x' * f x')
    (bound := fun x' => D0 / 2 * Q * M * (1 + x' ^ 2)⁻¹) hs
    (Eventually.of_forall fun s => ((mk_kernelX_measurable_snd D0 s x).mul hf).aestronglyMeasurable)
    ((mk_integrableOn_kernelX hD0 ht hx.le).mul_bdd hf.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y))
    ((((mk_px_measurable x).2.2.const_mul (D0 / 2)).mul hf).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' s hs' => by
      have h := mk_bound_mul_f (b := f x') (M := M)
        (show |D0 / 2 * mkPXT (D0 * s / 2) x x'| ≤ D0 / 2 * Q * (1 + x' ^ 2)⁻¹ by
          rw [abs_mul, hD, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hQ _ (hTm s hs') x hxm x' hx').2.2 (by positivity))
        (hM x')
      calc _ ≤ D0 / 2 * Q * M * (1 + x' ^ 2)⁻¹ := h))
    ((integrable_inv_one_add_sq.const_mul (D0 / 2 * Q * M)).integrableOn)
    ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' s hs' =>
      (mk_hasDerivAt_kernelX_t' hD0 (by linarith [hs'.1]) hx hx').mul_const (f x')))).2

/-- The PDE identity for the integrals: `mkUT = (D₀/2)(x(1+x) mkU2 + (1+2x) mkU1)`. -/
theorem mk_u_identity {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    mkUT D0 f t x = D0 / 2 * (x * (1 + x) * mkU2 D0 f t x + (1 + 2 * x) * mkU1 D0 f t x) := by
  have hT₀ : 0 < D0 * t / 2 := by positivity
  obtain ⟨Q, hQ⟩ := mk_px_decay hT₀ hx
  have hTm : D0 * t / 2 ∈ Icc (D0 * t / 2 - D0 * t / 2 / 2) (D0 * t / 2 + D0 * t / 2 / 2) :=
    ⟨by linarith, by linarith⟩
  have hxm : x ∈ Icc (x - x / 2) (x + x / 2) := ⟨by linarith, by linarith⟩
  have i1 := mk_integrable_mul_f (mk_px_measurable (T := D0 * t / 2) x).1 hf hM
    fun x' hx' => (hQ _ hTm x hxm x' hx').1
  have i2 := mk_integrable_mul_f (mk_px_measurable (T := D0 * t / 2) x).2.1 hf hM
    fun x' hx' => (hQ _ hTm x hxm x' hx').2.1
  unfold mkUT mkU1 mkU2
  rw [← integral_const_mul (x * (1 + x)), ← integral_const_mul (1 + 2 * x),
    ← integral_add (i2.const_mul _) (i1.const_mul _), ← integral_const_mul (D0 / 2)]
  refine setIntegral_congr_fun measurableSet_Ici fun x' hx' => ?_
  rw [← mk_px_identity' hT₀ hx hx']
  ring

/-- **Backward equation for the semigroup.** For `D₀ > 0`, `f` measurable with
`|f| ≤ M`, `t > 0` and `x > 0`, `u = mkU D0 f` satisfies
`∂_t u(t, x) = (D₀/2) [x(1+x) ∂_x² u(t, x) + (1+2x) ∂_x u(t, x)]`. -/
theorem mk_u_pde {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    deriv (fun s => mkU D0 f s x) t =
      D0 / 2 * (x * (1 + x) * deriv (deriv fun z => mkU D0 f t z) x +
        (1 + 2 * x) * deriv (fun z => mkU D0 f t z) x) := by
  have hd1 : deriv (fun z => mkU D0 f t z) =ᶠ[𝓝 x] fun z => mkU1 D0 f t z := by
    filter_upwards [lt_mem_nhds hx] with z hz
    exact (mk_hasDerivAt_u_x hD0 hf hM ht hz).deriv
  rw [(mk_hasDerivAt_u_t hD0 hf hM ht hx).deriv, hd1.deriv_eq,
    (mk_hasDerivAt_u1_x hD0 hf hM ht hx).deriv, (mk_hasDerivAt_u_x hD0 hf hM ht hx).deriv,
    mk_u_identity hD0 hf hM ht hx]

/-!
### Joint continuity
-/

theorem mk_u_box_eventually {D0 : ℝ} (hD0 : 0 < D0) {t₀ x₀ : ℝ} (ht₀ : 0 < t₀) (hx₀ : 0 < x₀) :
    ∀ᶠ p in 𝓝 (t₀, x₀), (D0 * p.1 / 2, p.2) ∈
      Icc (D0 * t₀ / 2 - D0 * t₀ / 2 / 2) (D0 * t₀ / 2 + D0 * t₀ / 2 / 2) ×ˢ
        Icc (x₀ - x₀ / 2) (x₀ + x₀ / 2) := by
  have hc : ContinuousAt (fun p : ℝ × ℝ => (D0 * p.1 / 2, p.2)) (t₀, x₀) := by fun_prop
  exact hc.preimage_mem_nhds (mk_box_nhds (by positivity) hx₀)

/-- **Joint continuity.** For `D₀ > 0` and bounded measurable `f`, the maps
`u = mkU D0 f`, `∂_x u = mkU1 D0 f`, `∂_x² u = mkU2 D0 f`, `∂_t u = mkUT D0 f` are continuous on
`(0,∞) × (0,∞)` (as functions of `(t, x)`). -/
theorem mk_u_derivs_continuousOn {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ => mkU D0 f p.1 p.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => mkU1 D0 f p.1 p.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => mkU2 D0 f p.1 p.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => mkUT D0 f p.1 p.2) (Ioi 0 ×ˢ Ioi 0) := by
  have hlin : ∀ p : ℝ × ℝ, ContinuousAt (fun q : ℝ × ℝ => (D0 * q.1 / 2, q.2)) p :=
    fun p => by fun_prop
  refine ⟨(mk_kernelX_integral_continuousOn hD0 hf hM).mono
    (prod_mono le_rfl Ioi_subset_Ici_self), ?_, ?_, ?_⟩
  all_goals
    rintro ⟨t₀, x₀⟩ ⟨ht₀, hx₀⟩
    have ht₀' : 0 < t₀ := ht₀
    have hx₀' : 0 < x₀ := hx₀
    have hT₀ : 0 < D0 * t₀ / 2 := by positivity
    obtain ⟨Q, hQ⟩ := mk_px_decay hT₀ hx₀'
    have hev := mk_u_box_eventually hD0 ht₀' hx₀'
    refine ContinuousAt.continuousWithinAt ?_
  · unfold mkU1
    refine continuousAt_of_dominated (bound := fun x' => Q * M * (1 + x' ^ 2)⁻¹)
      (Eventually.of_forall fun p => ((mk_px_measurable p.2).1.mul hf).aestronglyMeasurable)
      (hev.mono fun p hp => (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' =>
        mk_bound_mul_f (hQ _ hp.1 _ hp.2 x' hx').1 (hM x')))
      ((integrable_inv_one_add_sq.const_mul (Q * M)).integrableOn)
      ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' =>
        ((mk_px1_continuousAt hT₀ hx₀' hx').comp (x := (t₀, x₀)) (hlin _)).mul
          continuousAt_const))
  · unfold mkU2
    refine continuousAt_of_dominated (bound := fun x' => Q * M * (1 + x' ^ 2)⁻¹)
      (Eventually.of_forall fun p => ((mk_px_measurable p.2).2.1.mul hf).aestronglyMeasurable)
      (hev.mono fun p hp => (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' =>
        mk_bound_mul_f (hQ _ hp.1 _ hp.2 x' hx').2.1 (hM x')))
      ((integrable_inv_one_add_sq.const_mul (Q * M)).integrableOn)
      ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' =>
        ((mk_px2_continuousAt hT₀ hx₀' hx').comp (x := (t₀, x₀)) (hlin _)).mul
          continuousAt_const))
  · unfold mkUT
    have hD : |D0 / 2| = D0 / 2 := abs_of_pos (by positivity)
    refine continuousAt_of_dominated (bound := fun x' => D0 / 2 * Q * M * (1 + x' ^ 2)⁻¹)
      (Eventually.of_forall fun p =>
        (((mk_px_measurable p.2).2.2.const_mul (D0 / 2)).mul hf).aestronglyMeasurable)
      (hev.mono fun p hp => (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' =>
        mk_bound_mul_f (b := f x') (M := M)
          (show |D0 / 2 * mkPXT (D0 * p.1 / 2) p.2 x'| ≤ D0 / 2 * Q * (1 + x' ^ 2)⁻¹ by
            rw [abs_mul, hD, mul_assoc]
            exact mul_le_mul_of_nonneg_left (hQ _ hp.1 _ hp.2 x' hx').2.2 (by positivity))
          (hM x')))
      ((integrable_inv_one_add_sq.const_mul (D0 / 2 * Q * M)).integrableOn)
      ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' =>
        (continuousAt_const.mul
          ((mk_pxT_continuousAt hT₀ hx₀' hx').comp (x := (t₀, x₀)) (hlin _))).mul
          continuousAt_const))

end BlockBand.Diffusion
