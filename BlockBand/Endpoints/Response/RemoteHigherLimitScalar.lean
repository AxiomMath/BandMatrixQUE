module

public import BlockBand.Endpoints.Response.NearSchattenScalar
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Scalar tools for the higher clock decay at critical limits

* `rhl_add_rpow_le`, `rhl_add_rpow_le_real`: the weighted convexity bound
  `(x + y)^r ≤ (1-t)^{1-r} x^r + t^{1-r} y^r` (`r ≥ 1`, `0 < t < 1`), in `ℝ≥0∞` and in `ℝ`.
  Unlike `(x+y)^r ≤ 2^{r-1}(x^r + y^r)` its first constant tends to `1` as `t ↓ 0`, which is
  what a sharp (constant-one) passage needs.
* `rhl_le_of_weighted`, `rhl_le_of_weighted_one`: removing the weight `(1-t)^{1-r}` as `t ↓ 0`.
* `rhl_lintegral_rpowMul_le`: Hölder `E[f^{r-1} g] ≤ (E f^r)^{(r-1)/r} (E g^r)^{1/r}`
  (`r ≥ 1`, the case `r = 1` included).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Weighted convexity in `ℝ≥0∞`: `(x + y)^r ≤ (1-t)^{1-r} x^r + t^{1-r} y^r`. -/
theorem rhl_add_rpow_le (x y : ℝ≥0∞) {r t : ℝ} (hr : 1 ≤ r) (ht : 0 < t) (ht1 : t < 1) :
    (x + y) ^ r ≤ ENNReal.ofReal ((1 - t) ^ (1 - r)) * x ^ r +
      ENNReal.ofReal (t ^ (1 - r)) * y ^ r := by
  have h1t : 0 < 1 - t := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hw : ENNReal.ofReal (1 - t) + ENNReal.ofReal t = 1 := by
    rw [← ENNReal.ofReal_add h1t.le ht.le]; simp
  have h := ENNReal.rpow_arith_mean_le_arith_mean2_rpow (ENNReal.ofReal (1 - t))
    (ENNReal.ofReal t) (x * ENNReal.ofReal (1 / (1 - t))) (y * ENNReal.ofReal (1 / t)) hw hr
  have e1 : ∀ (s : ℝ) (z : ℝ≥0∞), 0 < s →
      ENNReal.ofReal s * (z * ENNReal.ofReal (1 / s)) = z := by
    intro s z hs
    rw [mul_comm z, ← mul_assoc, ← ENNReal.ofReal_mul hs.le, mul_one_div_cancel hs.ne',
      ENNReal.ofReal_one, one_mul]
  have e2 : ∀ (s : ℝ) (z : ℝ≥0∞), 0 < s →
      ENNReal.ofReal s * (z * ENNReal.ofReal (1 / s)) ^ r = ENNReal.ofReal (s ^ (1 - r)) * z ^ r := by
    intro s z hs
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0, mul_comm (z ^ r), ← mul_assoc,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hr0, ← ENNReal.ofReal_mul hs.le]
    congr 2
    rw [Real.div_rpow zero_le_one hs.le, Real.one_rpow, Real.rpow_sub hs, Real.rpow_one]
    ring
  rw [e1 _ _ h1t, e1 _ _ ht, e2 _ _ h1t, e2 _ _ ht] at h
  exact h

/-- Weighted convexity in `ℝ` (`x, y ≥ 0`). -/
theorem rhl_add_rpow_le_real {x y r t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 1 ≤ r) (ht : 0 < t)
    (ht1 : t < 1) : (x + y) ^ r ≤ (1 - t) ^ (1 - r) * x ^ r + t ^ (1 - r) * y ^ r := by
  have hr0 : 0 ≤ r := by linarith
  have h1t : 0 < 1 - t := by linarith
  have h := rhl_add_rpow_le (ENNReal.ofReal x) (ENNReal.ofReal y) hr ht ht1
  have ha : 0 ≤ (1 - t) ^ (1 - r) := Real.rpow_nonneg h1t.le _
  have hb : 0 ≤ t ^ (1 - r) := Real.rpow_nonneg ht.le _
  rw [← ENNReal.ofReal_add hx hy, ENNReal.ofReal_rpow_of_nonneg (by positivity) hr0,
    ENNReal.ofReal_rpow_of_nonneg hx hr0, ENNReal.ofReal_rpow_of_nonneg hy hr0,
    ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg ha (Real.rpow_nonneg hx _))
      (mul_nonneg hb (Real.rpow_nonneg hy _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- `(1-t)^{1-r} ≥ 1` for `0 < t < 1`, `r ≥ 1`. -/
theorem rhl_one_le_weight {r t : ℝ} (hr : 1 ≤ r) (ht : 0 < t) (ht1 : t < 1) :
    1 ≤ ENNReal.ofReal ((1 - t) ^ (1 - r)) := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by linarith))

/-- `(1 - ε_n/2)^{1-r} → 1`. -/
theorem rhl_tendsto_weight (r : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((1 - nsEps n / 2) ^ (1 - r))) atTop (𝓝 1) := by
  have h0 : Tendsto nsEps atTop (𝓝 0) := (tendsto_nhdsWithin_iff.1 ns_tendsto_eps).1
  have h1 : Tendsto (fun n => 1 - nsEps n / 2) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (h0.div_const 2)
  have h2 := h1.rpow_const (p := 1 - r) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at h2
  rw [← ENNReal.ofReal_one]
  exact ENNReal.tendsto_ofReal h2

theorem rhl_eps_half_lt_one (n : ℕ) : nsEps n / 2 < 1 := by
  have : nsEps n ≤ 1 := by
    unfold nsEps; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

/-- Removing the weight: if `L ≤ w_t (w_t H)` for every `0 < t < 1`, `w_t = (1-t)^{1-r}`,
then `L ≤ H` (`H < ∞`). -/
theorem rhl_le_of_weighted {L H : ℝ≥0∞} (r : ℝ) (hH : H ≠ ⊤)
    (h : ∀ t : ℝ, 0 < t → t < 1 →
      L ≤ ENNReal.ofReal ((1 - t) ^ (1 - r)) * (ENNReal.ofReal ((1 - t) ^ (1 - r)) * H)) :
    L ≤ H := by
  have hw := rhl_tendsto_weight r
  have hin : Tendsto (fun n => ENNReal.ofReal ((1 - nsEps n / 2) ^ (1 - r)) * H) atTop
      (𝓝 (1 * H)) := ENNReal.Tendsto.mul_const hw (Or.inr hH)
  have hout := ENNReal.Tendsto.mul hw (Or.inr (by simpa using hH)) hin (Or.inr ENNReal.one_ne_top)
  simp only [one_mul] at hout
  exact ge_of_tendsto' hout fun n =>
    h _ (by have := ns_eps_pos n; positivity) (rhl_eps_half_lt_one n)

/-- One-factor version of `rhl_le_of_weighted` (`r ≥ 1`, so `w_t ≥ 1`). -/
theorem rhl_le_of_weighted_one {L H : ℝ≥0∞} {r : ℝ} (hr : 1 ≤ r) (hH : H ≠ ⊤)
    (h : ∀ t : ℝ, 0 < t → t < 1 → L ≤ ENNReal.ofReal ((1 - t) ^ (1 - r)) * H) : L ≤ H :=
  rhl_le_of_weighted r hH fun t ht ht1 =>
    (h t ht ht1).trans (mul_le_mul_right (le_mul_of_one_le_left bot_le
      (rhl_one_le_weight hr ht ht1)) _)

/-- Hölder `E[f^{r-1} g] ≤ M^{(r-1)/r} N^{1/r}` from `E f^r ≤ M`, `E g^r ≤ N` (`r ≥ 1`,
probability measure; at `r = 1` it is `E g ≤ N`). -/
theorem rhl_lintegral_rpowMul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f P) (hg : AEMeasurable g P) {r : ℝ} (hr : 1 ≤ r)
    {M N : ℝ≥0∞} (hM : ∫⁻ ω, f ω ^ r ∂P ≤ M) (hN : ∫⁻ ω, g ω ^ r ∂P ≤ N) :
    ∫⁻ ω, f ω ^ (r - 1) * g ω ∂P ≤ M ^ ((r - 1) / r) * N ^ (1 / r) := by
  rcases hr.eq_or_lt with h1 | h1
  · subst h1
    simp only [sub_self, ENNReal.rpow_zero, one_mul, div_one, ENNReal.rpow_one] at hN ⊢
    exact hN
  · have hpq : (r / (r - 1)).HolderConjugate r :=
      ((Real.holderConjugate_iff_eq_conjExponent h1).2 rfl).symm
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hf.pow_const (r - 1)) hg
    have e : ∀ ω, (f ω ^ (r - 1)) ^ (r / (r - 1)) = f ω ^ r := fun ω => by
      rw [← ENNReal.rpow_mul]
      congr 1
      field_simp [(by linarith : r - 1 ≠ 0)]
    have e2 : 1 / (r / (r - 1)) = (r - 1) / r := by
      field_simp [(by linarith : r - 1 ≠ 0), (by linarith : r ≠ 0)]
    simp only [Pi.mul_apply, e, e2] at hH
    exact hH.trans (mul_le_mul' (ENNReal.rpow_le_rpow hM (div_nonneg (by linarith) (by linarith)))
      (ENNReal.rpow_le_rpow hN (by positivity)))

end BlockBand.Endpoints
