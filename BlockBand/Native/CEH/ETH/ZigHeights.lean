module

public import BlockBand.Native.CEH.Zig.Bootstrap

/-!
# CEH ETH, two-resolvent zig: two-height integrals

Setting. Variance time `r ≤ s`, two heights `η_{i,r} = zigHeight η_i c_i s r = η_i + c_i (s - r)`
with `η_i > 0`, `c_i ≥ 0` (`c_i = π ρ_i` in the application), and their product
`P_r = η_{1,r} η_{2,r}` (`zigHeightProd`). Since `P' = -(c₁ η₂ + c₂ η₁)`,

* `∫_u^t (c₁/η_{1,r} + c₂/η_{2,r}) dr = log (P_u / P_t)` (`integral_zigHeightProd_log`);
* `∫_u^t (c₁/η_{1,r} + c₂/η_{2,r}) / P_r^a dr = (1/P_t^a - 1/P_u^a) / a` for `a ≠ 0`
  (`integral_zigHeightProd_rpow`), hence `≤ 1 / (a P_t^a)` for `a > 0`, also for each of the two
  summands separately (`integral_div_zigHeight_div_zigHeightProd_rpow_le`).

Single height with real exponent (`integral_div_zigHeight_rpow`):
`∫_u^t c / η_r^α = (η_t^{1-α} - η_u^{1-α}) / (α - 1)`, `α ≠ 1`. Two heights with separate
exponents, by `η_{2,r} ≥ η_{2,t}` for `r ≤ t` (`integral_two_height_rpow_le`):
`∫_u^t c₁ / (η_{1,r}^α η_{2,r}^β) ≤ 1 / ((α - 1) η_{1,t}^{α-1} η_{2,t}^β)` (`α > 1`, `β ≥ 0`).

The CEH §7.1 combinations, all for `u ≤ t ≤ s` with exact constants (numerically sharp):
* `∫_u^t (c₁/η_{1,r} + c₂/η_{2,r}) / (N P_r) ≤ 1 / (N P_t)`; with `c_i = κ ρ_i`,
  `∫_u^t (ρ₁/η_{1,r} + ρ₂/η_{2,r}) / (N P_r) ≤ 1 / (κ N P_t)` (the `(ρ_i/η_i) / (N η η)` terms);
* `∫_u^t √(c₁ c₂ / P_r) ≤ (1/2) log (P_u / P_t)` (AM–GM; (7.7));
* `∫_u^t (1/η_{1,r}² + 1/η_{2,r}²) / (N² P_r) ≤ (1/(2 c₁ η_{1,t}) + 1/(2 c₂ η_{2,t})) / (N² P_t)
  ≤ 1 / (N² P_t ℓ_t)` with `ℓ_t = min (c₁ η_{1,t}) (c₂ η_{2,t})`; with `c_i = κ ρ_i` this is
  `1 / (κ N² P_t ℓ_t)`, `ℓ_t = min (ρ₁ η_{1,t}) (ρ₂ η_{2,t})` (CEH's `ℓ_t`; the brackets (7.4)).

The only measure is Lebesgue measure on `ℝ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Zig

/-- The product of the two heights, `P_r = η_{1,r} η_{2,r}`. -/
def zigHeightProd (η₁ c₁ η₂ c₂ s r : ℝ) : ℝ := zigHeight η₁ c₁ s r * zigHeight η₂ c₂ s r

section Single

variable {η c s : ℝ}

private theorem le_s_of_mem_uIcc {u t r : ℝ} (hu : u ≤ s) (ht : t ≤ s) (hr : r ∈ uIcc u t) :
    r ≤ s :=
  hr.2.trans (max_le hu ht)

/-- `∫_u^t c / η_r^α dr = (η_t^{1-α} - η_u^{1-α}) / (α - 1)` for `α ≠ 1`, `u, t ≤ s`. -/
theorem integral_div_zigHeight_rpow (hη : 0 < η) (hc : 0 ≤ c) {u t : ℝ} (hu : u ≤ s)
    (ht : t ≤ s) {α : ℝ} (hα : α ≠ 1) :
    ∫ r in u..t, c / zigHeight η c s r ^ α =
      (zigHeight η c s t ^ (1 - α) - zigHeight η c s u ^ (1 - α)) / (α - 1) := by
  have hα1 : α - 1 ≠ 0 := sub_ne_zero.mpr hα
  have hderiv : ∀ r ∈ uIcc u t, HasDerivAt (fun r => zigHeight η c s r ^ (1 - α) / (α - 1))
      (c / zigHeight η c s r ^ α) r := by
    intro r hr
    have hpos := zigHeight_pos hη hc (le_s_of_mem_uIcc hu ht hr)
    have h := ((hasDerivAt_zigHeight (η := η) (c := c) (s := s) r).rpow_const (p := 1 - α)
      (Or.inl hpos.ne')).div_const (α - 1)
    convert h using 1
    rw [show 1 - α - 1 = -α by ring, Real.rpow_neg hpos.le]
    have : 0 < zigHeight η c s r ^ α := Real.rpow_pos_of_pos hpos α
    field_simp
    ring
  have hint : IntervalIntegrable (fun r => c / zigHeight η c s r ^ α) volume u t := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.div ?_ fun r hr => ?_)
    · exact continuous_zigHeight.continuousOn.rpow_const fun r hr =>
        Or.inl (zigHeight_pos hη hc (le_s_of_mem_uIcc hu ht hr)).ne'
    · exact (Real.rpow_pos_of_pos (zigHeight_pos hη hc (le_s_of_mem_uIcc hu ht hr)) α).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, sub_div]

/-- `∫_u^t c / η_r^α dr ≤ 1 / ((α - 1) η_t^{α-1})` for `α > 1`, `u, t ≤ s`. -/
theorem integral_div_zigHeight_rpow_le (hη : 0 < η) (hc : 0 ≤ c) {u t : ℝ} (hu : u ≤ s)
    (ht : t ≤ s) {α : ℝ} (hα : 1 < α) :
    ∫ r in u..t, c / zigHeight η c s r ^ α ≤ 1 / ((α - 1) * zigHeight η c s t ^ (α - 1)) := by
  rw [integral_div_zigHeight_rpow hη hc hu ht hα.ne']
  have hηt := zigHeight_pos hη hc ht
  have h0 : 0 ≤ zigHeight η c s u ^ (1 - α) := Real.rpow_nonneg (zigHeight_pos hη hc hu).le _
  have e : zigHeight η c s t ^ (1 - α) = 1 / zigHeight η c s t ^ (α - 1) := by
    rw [show 1 - α = -(α - 1) by ring, Real.rpow_neg hηt.le, one_div]
  have hα1 : 0 < α - 1 := by linarith
  calc (zigHeight η c s t ^ (1 - α) - zigHeight η c s u ^ (1 - α)) / (α - 1)
      ≤ zigHeight η c s t ^ (1 - α) / (α - 1) := by gcongr; linarith
    _ = 1 / ((α - 1) * zigHeight η c s t ^ (α - 1)) := by
        rw [e]
        have : 0 < zigHeight η c s t ^ (α - 1) := Real.rpow_pos_of_pos hηt _
        field_simp

end Single

section Two

variable {η₁ c₁ η₂ c₂ s : ℝ}

theorem zigHeightProd_pos (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) {r : ℝ}
    (hr : r ≤ s) : 0 < zigHeightProd η₁ c₁ η₂ c₂ s r :=
  mul_pos (zigHeight_pos hη₁ hc₁ hr) (zigHeight_pos hη₂ hc₂ hr)

@[fun_prop]
theorem continuous_zigHeightProd : Continuous (zigHeightProd η₁ c₁ η₂ c₂ s) := by
  unfold zigHeightProd
  fun_prop

/-- `r ↦ P_r` is antitone. -/
theorem zigHeightProd_antitone (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (h₂ : t₂ ≤ s) :
    zigHeightProd η₁ c₁ η₂ c₂ s t₂ ≤ zigHeightProd η₁ c₁ η₂ c₂ s t₁ :=
  mul_le_mul (zigHeight_antitone hc₁ h) (zigHeight_antitone hc₂ h)
    (zigHeight_pos hη₂ hc₂ h₂).le (zigHeight_pos hη₁ hc₁ (h.trans h₂)).le

theorem hasDerivAt_zigHeightProd (r : ℝ) :
    HasDerivAt (zigHeightProd η₁ c₁ η₂ c₂ s)
      (-(c₁ * zigHeight η₂ c₂ s r + c₂ * zigHeight η₁ c₁ s r)) r := by
  exact ((hasDerivAt_zigHeight (η := η₁) (c := c₁) (s := s) r).mul
    (hasDerivAt_zigHeight (η := η₂) (c := c₂) (s := s) r)).congr_deriv (by ring)

private theorem continuousOn_sum_div (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {S : Set ℝ} (hS : ∀ r ∈ S, r ≤ s) :
    ContinuousOn (fun r => c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) S :=
  (continuousOn_const.div continuous_zigHeight.continuousOn fun r hr =>
      (zigHeight_pos hη₁ hc₁ (hS r hr)).ne').add
    (continuousOn_const.div continuous_zigHeight.continuousOn fun r hr =>
      (zigHeight_pos hη₂ hc₂ (hS r hr)).ne')

/-- `∫_u^t (c₁ / η_{1,r} + c₂ / η_{2,r}) dr = log (P_u / P_t)` for `u, t ≤ s`. -/
theorem integral_zigHeightProd_log (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hu : u ≤ s) (ht : t ≤ s) :
    ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) =
      Real.log (zigHeightProd η₁ c₁ η₂ c₂ s u / zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  have h1 : IntervalIntegrable (fun r => c₁ / zigHeight η₁ c₁ s r) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div continuous_zigHeight.continuousOn
      fun r hr => (zigHeight_pos hη₁ hc₁ (le_s_of_mem_uIcc hu ht hr)).ne')
  have h2 : IntervalIntegrable (fun r => c₂ / zigHeight η₂ c₂ s r) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div continuous_zigHeight.continuousOn
      fun r hr => (zigHeight_pos hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne')
  rw [intervalIntegral.integral_add h1 h2, integral_div_zigHeight hη₁ hc₁ hu ht,
    integral_div_zigHeight hη₂ hc₂ hu ht, ← Real.log_mul
      (div_pos (zigHeight_pos hη₁ hc₁ hu) (zigHeight_pos hη₁ hc₁ ht)).ne'
      (div_pos (zigHeight_pos hη₂ hc₂ hu) (zigHeight_pos hη₂ hc₂ ht)).ne']
  congr 1
  unfold zigHeightProd
  rw [mul_div_mul_comm]

/-- **Two-height identity.** For `a ≠ 0` and `u, t ≤ s`,
`∫_u^t (c₁ / η_{1,r} + c₂ / η_{2,r}) / P_r^a dr = (1 / P_t^a - 1 / P_u^a) / a`. -/
theorem integral_zigHeightProd_rpow (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hu : u ≤ s) (ht : t ≤ s) {a : ℝ} (ha : a ≠ 0) :
    ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
        zigHeightProd η₁ c₁ η₂ c₂ s r ^ a =
      (1 / zigHeightProd η₁ c₁ η₂ c₂ s t ^ a - 1 / zigHeightProd η₁ c₁ η₂ c₂ s u ^ a) / a := by
  have hderiv : ∀ r ∈ uIcc u t,
      HasDerivAt (fun r => zigHeightProd η₁ c₁ η₂ c₂ s r ^ (-a) / a)
        ((c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
          zigHeightProd η₁ c₁ η₂ c₂ s r ^ a) r := by
    intro r hr
    have hrs := le_s_of_mem_uIcc hu ht hr
    have hP := zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ hrs
    have h1 := zigHeight_pos hη₁ hc₁ hrs
    have h2 := zigHeight_pos hη₂ hc₂ hrs
    have h := ((hasDerivAt_zigHeightProd (η₁ := η₁) (c₁ := c₁) (η₂ := η₂) (c₂ := c₂)
      (s := s) r).rpow_const (p := -a) (Or.inl hP.ne')).div_const a
    convert h using 1
    rw [Real.rpow_sub_one hP.ne', Real.rpow_neg hP.le]
    have hPa : 0 < zigHeightProd η₁ c₁ η₂ c₂ s r ^ a := Real.rpow_pos_of_pos hP a
    have e : zigHeightProd η₁ c₁ η₂ c₂ s r = zigHeight η₁ c₁ s r * zigHeight η₂ c₂ s r := rfl
    rw [e] at hPa ⊢
    field_simp
  have hint : IntervalIntegrable (fun r => (c₁ / zigHeight η₁ c₁ s r +
      c₂ / zigHeight η₂ c₂ s r) / zigHeightProd η₁ c₁ η₂ c₂ s r ^ a) volume u t := by
    refine ContinuousOn.intervalIntegrable ((continuousOn_sum_div hη₁ hc₁ hη₂ hc₂
      fun r hr => le_s_of_mem_uIcc hu ht hr).div ?_ fun r hr => ?_)
    · exact continuous_zigHeightProd.continuousOn.rpow_const fun r hr =>
        Or.inl (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne'
    · exact (Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂
        (le_s_of_mem_uIcc hu ht hr)) a).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, ← sub_div,
    Real.rpow_neg (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ ht).le,
    Real.rpow_neg (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ hu).le, one_div, one_div]

/-- `∫_u^t (c₁ / η_{1,r} + c₂ / η_{2,r}) / P_r^a dr ≤ 1 / (a P_t^a)` for `a > 0`, `u, t ≤ s`. -/
theorem integral_zigHeightProd_rpow_le (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hu : u ≤ s) (ht : t ≤ s) {a : ℝ} (ha : 0 < a) :
    ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
        zigHeightProd η₁ c₁ η₂ c₂ s r ^ a ≤
      1 / (a * zigHeightProd η₁ c₁ η₂ c₂ s t ^ a) := by
  rw [integral_zigHeightProd_rpow hη₁ hc₁ hη₂ hc₂ hu ht ha.ne']
  have hPt := Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ ht) a
  have hPu := Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ hu) a
  have : 0 < 1 / zigHeightProd η₁ c₁ η₂ c₂ s u ^ a := by positivity
  calc (1 / zigHeightProd η₁ c₁ η₂ c₂ s t ^ a - 1 / zigHeightProd η₁ c₁ η₂ c₂ s u ^ a) / a
      ≤ (1 / zigHeightProd η₁ c₁ η₂ c₂ s t ^ a) / a := by gcongr; linarith
    _ = 1 / (a * zigHeightProd η₁ c₁ η₂ c₂ s t ^ a) := by field_simp

/-- A nonnegative continuous integrand dominated by the two-height integrand integrates to at
most `1 / (a P_t^a)` (for `u ≤ t ≤ s`, `a > 0`). -/
private theorem integral_le_of_le_sum (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) {a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc u t))
    (hle : ∀ r ∈ Icc u t, f r ≤ (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
        zigHeightProd η₁ c₁ η₂ c₂ s r ^ a) :
    ∫ r in u..t, f r ≤ 1 / (a * zigHeightProd η₁ c₁ η₂ c₂ s t ^ a) := by
  have hu : u ≤ s := hut.trans ht
  refine (intervalIntegral.integral_mono_on hut hf.intervalIntegrable ?_ hle).trans
    (integral_zigHeightProd_rpow_le hη₁ hc₁ hη₂ hc₂ hu ht ha)
  refine ContinuousOn.intervalIntegrable ((continuousOn_sum_div hη₁ hc₁ hη₂ hc₂
    fun r hr => le_s_of_mem_uIcc hu ht hr).div ?_ fun r hr => ?_)
  · exact continuous_zigHeightProd.continuousOn.rpow_const fun r hr =>
      Or.inl (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne'
  · exact (Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂
      (le_s_of_mem_uIcc hu ht hr)) a).ne'

/-- **First summand.** `∫_u^t c₁ / (η_{1,r} P_r^a) dr ≤ 1 / (a P_t^a)` for `a > 0`,
`u ≤ t ≤ s` (e.g. `a = 1/2`: `∫ c₁ / (η_{1,r}^{3/2} η_{2,r}^{1/2}) ≤ 2 / √P_t`). -/
theorem integral_div_zigHeight_div_zigHeightProd_rpow_le (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁)
    (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) {a : ℝ} (ha : 0 < a) :
    ∫ r in u..t, c₁ / zigHeight η₁ c₁ s r / zigHeightProd η₁ c₁ η₂ c₂ s r ^ a ≤
      1 / (a * zigHeightProd η₁ c₁ η₂ c₂ s t ^ a) := by
  have hu : u ≤ s := hut.trans ht
  refine integral_le_of_le_sum hη₁ hc₁ hη₂ hc₂ hut ht ha ?_ fun r hr => ?_
  · refine (continuousOn_const.div continuous_zigHeight.continuousOn fun r hr =>
      (zigHeight_pos hη₁ hc₁ (le_s_of_mem_uIcc hu ht hr)).ne').div ?_ fun r hr => ?_
    · exact continuous_zigHeightProd.continuousOn.rpow_const fun r hr =>
        Or.inl (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne'
    · exact (Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂
        (le_s_of_mem_uIcc hu ht hr)) a).ne'
  · have hrs : r ≤ s := hr.2.trans ht
    have := Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ hrs) a
    have := zigHeight_pos hη₂ hc₂ hrs
    have : 0 ≤ c₂ / zigHeight η₂ c₂ s r := by positivity
    gcongr
    linarith

/-- **Second summand.** `∫_u^t c₂ / (η_{2,r} P_r^a) dr ≤ 1 / (a P_t^a)` for `a > 0`,
`u ≤ t ≤ s`. -/
theorem integral_div_zigHeight_div_zigHeightProd_rpow_le' (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁)
    (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) {a : ℝ} (ha : 0 < a) :
    ∫ r in u..t, c₂ / zigHeight η₂ c₂ s r / zigHeightProd η₁ c₁ η₂ c₂ s r ^ a ≤
      1 / (a * zigHeightProd η₁ c₁ η₂ c₂ s t ^ a) := by
  have hu : u ≤ s := hut.trans ht
  refine integral_le_of_le_sum hη₁ hc₁ hη₂ hc₂ hut ht ha ?_ fun r hr => ?_
  · refine (continuousOn_const.div continuous_zigHeight.continuousOn fun r hr =>
      (zigHeight_pos hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne').div ?_ fun r hr => ?_
    · exact continuous_zigHeightProd.continuousOn.rpow_const fun r hr =>
        Or.inl (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne'
    · exact (Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂
        (le_s_of_mem_uIcc hu ht hr)) a).ne'
  · have hrs : r ≤ s := hr.2.trans ht
    have := Real.rpow_pos_of_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ hrs) a
    have := zigHeight_pos hη₁ hc₁ hrs
    have : 0 ≤ c₁ / zigHeight η₁ c₁ s r := by positivity
    gcongr
    linarith

/-- **Separate exponents.** For `u ≤ t ≤ s`, `α > 1`, `β ≥ 0`,
`∫_u^t c₁ / (η_{1,r}^α η_{2,r}^β) dr ≤ 1 / ((α - 1) η_{1,t}^{α-1} η_{2,t}^β)`. -/
theorem integral_two_height_rpow_le (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) {α β : ℝ} (hα : 1 < α) (hβ : 0 ≤ β) :
    ∫ r in u..t, c₁ / (zigHeight η₁ c₁ s r ^ α * zigHeight η₂ c₂ s r ^ β) ≤
      1 / ((α - 1) * zigHeight η₁ c₁ s t ^ (α - 1) * zigHeight η₂ c₂ s t ^ β) := by
  have hu : u ≤ s := hut.trans ht
  have hpos₁ : ∀ r ∈ uIcc u t, 0 < zigHeight η₁ c₁ s r ^ α := fun r hr =>
    Real.rpow_pos_of_pos (zigHeight_pos hη₁ hc₁ (le_s_of_mem_uIcc hu ht hr)) α
  have hpos₂ : ∀ r ∈ uIcc u t, 0 < zigHeight η₂ c₂ s r ^ β := fun r hr =>
    Real.rpow_pos_of_pos (zigHeight_pos hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)) β
  have hc1 : ContinuousOn (fun r => zigHeight η₁ c₁ s r ^ α) (uIcc u t) :=
    continuous_zigHeight.continuousOn.rpow_const fun r hr => Or.inl
      (zigHeight_pos hη₁ hc₁ (le_s_of_mem_uIcc hu ht hr)).ne'
  have hc2 : ContinuousOn (fun r => zigHeight η₂ c₂ s r ^ β) (uIcc u t) :=
    continuous_zigHeight.continuousOn.rpow_const fun _ _ => Or.inr hβ
  have hf : IntervalIntegrable (fun r => c₁ / (zigHeight η₁ c₁ s r ^ α *
      zigHeight η₂ c₂ s r ^ β)) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div (hc1.mul hc2) fun r hr =>
      (mul_pos (hpos₁ r hr) (hpos₂ r hr)).ne')
  have hg : IntervalIntegrable (fun r => 1 / zigHeight η₂ c₂ s t ^ β *
      (c₁ / zigHeight η₁ c₁ s r ^ α)) volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.mul (continuousOn_const.div hc1
      fun r hr => (hpos₁ r hr).ne'))
  have hηt₂ := zigHeight_pos hη₂ hc₂ ht
  have hβt : 0 < zigHeight η₂ c₂ s t ^ β := Real.rpow_pos_of_pos hηt₂ β
  have hmono := intervalIntegral.integral_mono_on hut hf hg fun r hr => by
    have hrs : r ≤ s := hr.2.trans ht
    have h1 := Real.rpow_pos_of_pos (zigHeight_pos hη₁ hc₁ hrs) α
    have h2le : zigHeight η₂ c₂ s t ^ β ≤ zigHeight η₂ c₂ s r ^ β :=
      Real.rpow_le_rpow hηt₂.le (zigHeight_antitone hc₂ hr.2) hβ
    rw [div_mul_div_comm, one_mul, mul_comm (zigHeight η₂ c₂ s t ^ β)]
    gcongr
  rw [intervalIntegral.integral_const_mul] at hmono
  refine hmono.trans ?_
  have h := integral_div_zigHeight_rpow_le hη₁ hc₁ hu ht hα
  have h' := mul_le_mul_of_nonneg_left h (one_div_pos.mpr hβt).le
  refine h'.trans (le_of_eq ?_)
  have : 0 < zigHeight η₁ c₁ s t ^ (α - 1) :=
    Real.rpow_pos_of_pos (zigHeight_pos hη₁ hc₁ ht) _
  have : 0 < α - 1 := by linarith
  field_simp

/-- **AM–GM, CEH (7.7).** For `u ≤ t ≤ s`, `∫_u^t √(c₁ c₂ / P_r) dr ≤ (1/2) log (P_u / P_t)`. -/
theorem integral_sqrt_div_zigHeightProd_le (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, Real.sqrt (c₁ * c₂ / zigHeightProd η₁ c₁ η₂ c₂ s r) ≤
      Real.log (zigHeightProd η₁ c₁ η₂ c₂ s u / zigHeightProd η₁ c₁ η₂ c₂ s t) / 2 := by
  have hu : u ≤ s := hut.trans ht
  have hf : IntervalIntegrable (fun r => Real.sqrt (c₁ * c₂ / zigHeightProd η₁ c₁ η₂ c₂ s r))
      volume u t :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      continuous_zigHeightProd.continuousOn fun r hr =>
        (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne').sqrt
  have hg : IntervalIntegrable (fun r =>
      (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) / 2) volume u t :=
    ContinuousOn.intervalIntegrable ((continuousOn_sum_div hη₁ hc₁ hη₂ hc₂
      fun r hr => le_s_of_mem_uIcc hu ht hr).div_const 2)
  have hmono := intervalIntegral.integral_mono_on hut hf hg fun r hr => by
    have hrs : r ≤ s := hr.2.trans ht
    have h1 := zigHeight_pos hη₁ hc₁ hrs
    have h2 := zigHeight_pos hη₂ hc₂ hrs
    set x := c₁ / zigHeight η₁ c₁ s r with hx
    set y := c₂ / zigHeight η₂ c₂ s r with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have e : c₁ * c₂ / zigHeightProd η₁ c₁ η₂ c₂ s r = x * y := by
      simp only [hx, hy, zigHeightProd]
      field_simp
    rw [e, Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [sq_nonneg (x - y)]⟩
  rw [intervalIntegral.integral_div, integral_zigHeightProd_log hη₁ hc₁ hη₂ hc₂ hu ht] at hmono
  exact hmono

/-- **CEH (7.1), `(ρ_i/η_i)/(N η₁ η₂)` terms.** For `N > 0`, `u ≤ t ≤ s`,
`∫_u^t (c₁/η_{1,r} + c₂/η_{2,r}) / (N P_r) dr ≤ 1 / (N P_t)`. -/
theorem integral_sum_div_N_zigHeightProd_le (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {N : ℝ} (hN : 0 < N) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
        (N * zigHeightProd η₁ c₁ η₂ c₂ s r) ≤ 1 / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  have h := integral_zigHeightProd_rpow_le hη₁ hc₁ hη₂ hc₂ (hut.trans ht) ht one_pos
  simp only [Real.rpow_one, one_mul] at h
  have e : ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
      (N * zigHeightProd η₁ c₁ η₂ c₂ s r) =
      (1 / N) * ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
        zigHeightProd η₁ c₁ η₂ c₂ s r := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [one_div_mul_eq_div, div_div, mul_comm N]
  rw [e]
  calc 1 / N * ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
        zigHeightProd η₁ c₁ η₂ c₂ s r ≤ 1 / N * (1 / zigHeightProd η₁ c₁ η₂ c₂ s t) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) := by rw [one_div_mul_one_div]

/-- **CEH (7.1), with densities.** If `c_i = κ ρ_i`, `κ > 0`, then for `N > 0`, `u ≤ t ≤ s`,
`∫_u^t (ρ₁/η_{1,r} + ρ₂/η_{2,r}) / (N P_r) dr ≤ 1 / (κ N P_t)`. -/
theorem integral_rho_div_N_zigHeightProd_le (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {N κ ρ₁ ρ₂ : ℝ} (hN : 0 < N) (hκ : 0 < κ) (hρ₁ : c₁ = κ * ρ₁)
    (hρ₂ : c₂ = κ * ρ₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, (ρ₁ / zigHeight η₁ c₁ s r + ρ₂ / zigHeight η₂ c₂ s r) /
        (N * zigHeightProd η₁ c₁ η₂ c₂ s r) ≤
      1 / (κ * N * zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  have h := integral_sum_div_N_zigHeightProd_le hη₁ hc₁ hη₂ hc₂ (mul_pos hκ hN) hut ht
  have e : ∫ r in u..t, (c₁ / zigHeight η₁ c₁ s r + c₂ / zigHeight η₂ c₂ s r) /
      (κ * N * zigHeightProd η₁ c₁ η₂ c₂ s r) =
      ∫ r in u..t, (ρ₁ / zigHeight η₁ c₁ s r + ρ₂ / zigHeight η₂ c₂ s r) /
        (N * zigHeightProd η₁ c₁ η₂ c₂ s r) := by
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [hρ₁, hρ₂, mul_div_assoc, mul_div_assoc, ← mul_add, mul_assoc,
      mul_div_mul_left _ _ hκ.ne']
  rw [e] at h
  exact h

private theorem rpow_three_eq (x : ℝ) : x ^ (3 : ℝ) = x ^ 3 := by norm_num

/-- `∫_u^t 1 / (η_{1,r}² P_r) dr ≤ 1 / (2 c₁ η_{1,t} P_t)` for `c₁ > 0`, `u ≤ t ≤ s`. -/
theorem integral_inv_sq_div_zigHeightProd_le (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, 1 / zigHeight η₁ c₁ s r ^ 2 / zigHeightProd η₁ c₁ η₂ c₂ s r ≤
      1 / (2 * c₁ * zigHeight η₁ c₁ s t * zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  have h := integral_two_height_rpow_le hη₁ hc₁.le hη₂ hc₂ hut ht (α := 3) (β := 1)
    (by norm_num) zero_le_one
  simp only [rpow_three_eq, Real.rpow_one, show (3 : ℝ) - 1 = 2 by norm_num,
    show ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 from fun x => by norm_num] at h
  have e : ∫ r in u..t, 1 / zigHeight η₁ c₁ s r ^ 2 / zigHeightProd η₁ c₁ η₂ c₂ s r =
      (1 / c₁) * ∫ r in u..t, c₁ / (zigHeight η₁ c₁ s r ^ 3 * zigHeight η₂ c₂ s r) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [zigHeightProd]
    field_simp
  rw [e]
  have h1 := zigHeight_pos hη₁ hc₁.le ht
  have h2 := zigHeight_pos hη₂ hc₂ ht
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans (le_of_eq ?_)
  simp only [zigHeightProd]
  field_simp

/-- `∫_u^t 1 / (η_{2,r}² P_r) dr ≤ 1 / (2 c₂ η_{2,t} P_t)` for `c₂ > 0`, `u ≤ t ≤ s`. -/
theorem integral_inv_sq_div_zigHeightProd_le' (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 < c₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, 1 / zigHeight η₂ c₂ s r ^ 2 / zigHeightProd η₁ c₁ η₂ c₂ s r ≤
      1 / (2 * c₂ * zigHeight η₂ c₂ s t * zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  have h := integral_inv_sq_div_zigHeightProd_le (s := s) hη₂ hc₂ hη₁ hc₁ hut ht
  have e : ∀ r, zigHeightProd η₂ c₂ η₁ c₁ s r = zigHeightProd η₁ c₁ η₂ c₂ s r := fun r =>
    mul_comm _ _
  simp only [e] at h
  exact h

private theorem continuousOn_inv_sq_div_prod (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {u t : ℝ} (hu : u ≤ s) (ht : t ≤ s) {η c : ℝ} (hη : 0 < η) (hc : 0 ≤ c) :
    ContinuousOn (fun r => 1 / zigHeight η c s r ^ 2 / zigHeightProd η₁ c₁ η₂ c₂ s r)
      (uIcc u t) :=
  (continuousOn_const.div (continuous_zigHeight.continuousOn.pow 2) fun _ hr =>
    pow_ne_zero 2 (zigHeight_pos hη hc (le_s_of_mem_uIcc hu ht hr)).ne').div
      continuous_zigHeightProd.continuousOn fun _ hr =>
        (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ (le_s_of_mem_uIcc hu ht hr)).ne'

/-- **CEH (7.4), brackets, sharp form.** For `c_i > 0`, `N > 0`, `u ≤ t ≤ s`,
`∫_u^t (1/η_{1,r}² + 1/η_{2,r}²) / (N² P_r) dr ≤
(1 / (2 c₁ η_{1,t}) + 1 / (2 c₂ η_{2,t})) / (N² P_t)`. -/
theorem integral_bracket_zigHeightProd_le (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 < c₂) {N : ℝ} (hN : 0 < N) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, (1 / zigHeight η₁ c₁ s r ^ 2 + 1 / zigHeight η₂ c₂ s r ^ 2) /
        (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s r) ≤
      (1 / (2 * c₁ * zigHeight η₁ c₁ s t) + 1 / (2 * c₂ * zigHeight η₂ c₂ s t)) /
        (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  have hu : u ≤ s := hut.trans ht
  have i1 := (continuousOn_inv_sq_div_prod hη₁ hc₁.le hη₂ hc₂.le hu ht hη₁ hc₁.le
    ).intervalIntegrable (μ := volume)
  have i2 := (continuousOn_inv_sq_div_prod hη₁ hc₁.le hη₂ hc₂.le hu ht hη₂ hc₂.le
    ).intervalIntegrable (μ := volume)
  have e : ∫ r in u..t, (1 / zigHeight η₁ c₁ s r ^ 2 + 1 / zigHeight η₂ c₂ s r ^ 2) /
      (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s r) =
      (1 / N ^ 2) * ((∫ r in u..t, 1 / zigHeight η₁ c₁ s r ^ 2 /
        zigHeightProd η₁ c₁ η₂ c₂ s r) +
        ∫ r in u..t, 1 / zigHeight η₂ c₂ s r ^ 2 / zigHeightProd η₁ c₁ η₂ c₂ s r) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  rw [e]
  have h1 := integral_inv_sq_div_zigHeightProd_le hη₁ hc₁ hη₂ hc₂.le hut ht
  have h2 := integral_inv_sq_div_zigHeightProd_le' hη₁ hc₁.le hη₂ hc₂ hut ht
  have hP := zigHeightProd_pos hη₁ hc₁.le hη₂ hc₂.le ht
  have ht1 := zigHeight_pos hη₁ hc₁.le ht
  have ht2 := zigHeight_pos hη₂ hc₂.le ht
  refine (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)).trans (le_of_eq ?_)
  field_simp

/-- **CEH (7.4), brackets, with `ℓ_t`.** For `c_i > 0`, `N > 0`, `u ≤ t ≤ s`,
`∫_u^t (1/η_{1,r}² + 1/η_{2,r}²) / (N² P_r) dr ≤ 1 / (N² P_t ℓ_t)`,
`ℓ_t = min (c₁ η_{1,t}) (c₂ η_{2,t})`. -/
theorem integral_bracket_zigHeightProd_le_ell (hη₁ : 0 < η₁) (hc₁ : 0 < c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 < c₂) {N : ℝ} (hN : 0 < N) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, (1 / zigHeight η₁ c₁ s r ^ 2 + 1 / zigHeight η₂ c₂ s r ^ 2) /
        (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s r) ≤
      1 / (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s t *
        min (c₁ * zigHeight η₁ c₁ s t) (c₂ * zigHeight η₂ c₂ s t)) := by
  refine (integral_bracket_zigHeightProd_le hη₁ hc₁ hη₂ hc₂ hN hut ht).trans ?_
  have hP := zigHeightProd_pos hη₁ hc₁.le hη₂ hc₂.le ht
  have ht1 := zigHeight_pos hη₁ hc₁.le ht
  have ht2 := zigHeight_pos hη₂ hc₂.le ht
  set ℓ := min (c₁ * zigHeight η₁ c₁ s t) (c₂ * zigHeight η₂ c₂ s t) with hℓ
  have hℓ0 : 0 < ℓ := lt_min (by positivity) (by positivity)
  have hℓ1 : ℓ ≤ c₁ * zigHeight η₁ c₁ s t := min_le_left _ _
  have hℓ2 : ℓ ≤ c₂ * zigHeight η₂ c₂ s t := min_le_right _ _
  have hs : 1 / (2 * c₁ * zigHeight η₁ c₁ s t) + 1 / (2 * c₂ * zigHeight η₂ c₂ s t) ≤
      1 / ℓ := by
    have a1 : 1 / (2 * c₁ * zigHeight η₁ c₁ s t) ≤ 1 / (2 * ℓ) := by
      rw [mul_assoc]
      gcongr
    have a2 : 1 / (2 * c₂ * zigHeight η₂ c₂ s t) ≤ 1 / (2 * ℓ) := by
      rw [mul_assoc]
      gcongr
    have : 1 / (2 * ℓ) + 1 / (2 * ℓ) = 1 / ℓ := by field_simp; ring
    linarith
  calc (1 / (2 * c₁ * zigHeight η₁ c₁ s t) + 1 / (2 * c₂ * zigHeight η₂ c₂ s t)) /
        (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s t)
      ≤ (1 / ℓ) / (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s t) := by gcongr
    _ = 1 / (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s t * ℓ) := by field_simp

/-- **CEH (7.4), brackets, with densities.** If `c_i = κ ρ_i`, `κ, ρ_i > 0`, then for `N > 0`,
`u ≤ t ≤ s`, `∫_u^t (1/η_{1,r}² + 1/η_{2,r}²) / (N² P_r) dr ≤ 1 / (κ N² P_t ℓ_t)` with CEH's
`ℓ_t = min (ρ₁ η_{1,t}) (ρ₂ η_{2,t})`. -/
theorem integral_bracket_zigHeightProd_le_rho (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) {N κ ρ₁ ρ₂ : ℝ}
    (hN : 0 < N) (hκ : 0 < κ) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hc₁ : c₁ = κ * ρ₁)
    (hc₂ : c₂ = κ * ρ₂) {u t : ℝ} (hut : u ≤ t) (ht : t ≤ s) :
    ∫ r in u..t, (1 / zigHeight η₁ c₁ s r ^ 2 + 1 / zigHeight η₂ c₂ s r ^ 2) /
        (N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s r) ≤
      1 / (κ * N ^ 2 * zigHeightProd η₁ c₁ η₂ c₂ s t *
        min (ρ₁ * zigHeight η₁ c₁ s t) (ρ₂ * zigHeight η₂ c₂ s t)) := by
  have hc₁0 : 0 < c₁ := hc₁ ▸ mul_pos hκ hρ₁
  have hc₂0 : 0 < c₂ := hc₂ ▸ mul_pos hκ hρ₂
  refine (integral_bracket_zigHeightProd_le_ell hη₁ hc₁0 hη₂ hc₂0 hN hut ht).trans
    (le_of_eq ?_)
  have e : min (c₁ * zigHeight η₁ c₁ s t) (c₂ * zigHeight η₂ c₂ s t) =
      κ * min (ρ₁ * zigHeight η₁ c₁ s t) (ρ₂ * zigHeight η₂ c₂ s t) := by
    rw [mul_min_of_nonneg _ _ hκ.le, ← mul_assoc, ← mul_assoc, ← hc₁, ← hc₂]
  rw [e]
  ring

end Two

end BlockBand.Native.CEH.ETH
