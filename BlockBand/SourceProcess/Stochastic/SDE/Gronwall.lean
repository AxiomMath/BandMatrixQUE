module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Volterra iteration and the integral Gronwall inequality

Deterministic real-variable facts used by strong SDE uniqueness and Picard iteration.
Measure: Lebesgue measure on `ℝ` (interval integrals `∫ s in 0..t`); domain `[0,T]`. Functions
are only assumed interval integrable on `[0,T]` (no continuity, no measurability beyond that).

* `volterra_iterate_le`: if `v₀ ≤ C` and `v_{n+1}(t) ≤ L ∫₀ᵗ vₙ` on `[0,T]` (`L ≥ 0`), then
  `vₙ(t) ≤ C (L t)ⁿ / n!` on `[0,T]` (any sign of `C`).
* `summable_volterra_bound`, `tendsto_volterra_bound`: `∑ₙ C (L t)ⁿ/n!` converges and the terms
  tend to `0`.
* `gronwall_integral`: if `u ≥ 0` is interval integrable on `[0,T]` and
  `u(t) ≤ A + L ∫₀ᵗ u` on `[0,T]` (`L ≥ 0`), then `u(t) ≤ A e^{L t}` on `[0,T]`.
* `eq_zero_of_le_volterra`: `0 ≤ w(t) ≤ L ∫₀ᵗ w` on `[0,T]` forces `w = 0` there.
-/

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.SDE
open MeasureTheory Filter Topology Set intervalIntegral
open scoped Nat

theorem intervalIntegrable_of_le {f : ℝ → ℝ} {T t : ℝ} (hf : IntervalIntegrable f volume 0 T)
    (ht : t ∈ Icc 0 T) : IntervalIntegrable f volume 0 t :=
  hf.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2)

/-- `L ∫₀ᵗ C (L s)ⁿ / n! ds = C (L t)ⁿ⁺¹ / (n+1)!`. -/
theorem mul_integral_volterra_bound (C L t : ℝ) (n : ℕ) :
    L * ∫ s in (0 : ℝ)..t, C * (L * s) ^ n / n ! = C * (L * t) ^ (n + 1) / (n + 1)! := by
  have h : ∀ s : ℝ, C * (L * s) ^ n / n ! = C * L ^ n / n ! * s ^ n := fun s => by
    rw [mul_pow]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **Volterra iteration bound.** -/
theorem volterra_iterate_le {v : ℕ → ℝ → ℝ} {C L T : ℝ} (hL : 0 ≤ L)
    (hint : ∀ n, IntervalIntegrable (v n) volume 0 T) (h0 : ∀ t ∈ Icc 0 T, v 0 t ≤ C)
    (hstep : ∀ n, ∀ t ∈ Icc 0 T, v (n + 1) t ≤ L * ∫ s in (0 : ℝ)..t, v n s) :
    ∀ n, ∀ t ∈ Icc 0 T, v n t ≤ C * (L * t) ^ n / n ! := by
  intro n
  induction n with
  | zero => intro t ht; simpa using h0 t ht
  | succ n ih =>
    intro t ht
    refine (hstep n t ht).trans ?_
    rw [← mul_integral_volterra_bound]
    refine mul_le_mul_of_nonneg_left ?_ hL
    refine integral_mono_on ht.1 (intervalIntegrable_of_le (hint n) ht)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
    exact ih s ⟨hs.1, hs.2.trans ht.2⟩

theorem summable_volterra_bound (C x : ℝ) : Summable fun n : ℕ => C * x ^ n / n ! := by
  simpa only [mul_div_assoc] using (Real.summable_pow_div_factorial x).mul_left C

theorem tendsto_volterra_bound (C x : ℝ) :
    Tendsto (fun n : ℕ => C * x ^ n / n !) atTop (𝓝 0) := by
  simpa only [mul_div_assoc, mul_zero] using
    (FloorSemiring.tendsto_pow_div_factorial_atTop x).const_mul C

/-- A function dominated by the Volterra bounds for every `n` is nonpositive. -/
theorem nonpos_of_le_volterra_bound {a C x : ℝ} (h : ∀ n : ℕ, a ≤ C * x ^ n / n !) : a ≤ 0 :=
  ge_of_tendsto' (tendsto_volterra_bound C x) h

/-- **Integral Gronwall inequality.** -/
theorem gronwall_integral {u : ℝ → ℝ} {A L T : ℝ} (hL : 0 ≤ L)
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hint : IntervalIntegrable u volume 0 T)
    (h : ∀ t ∈ Icc 0 T, u t ≤ A + L * ∫ s in (0 : ℝ)..t, u s) :
    ∀ t ∈ Icc 0 T, u t ≤ A * Real.exp (L * t) := by
  set v : ℝ → ℝ := fun s => u s - A * Real.exp (L * s) with hv
  have hexp_int : ∀ a b : ℝ, IntervalIntegrable (fun s => A * Real.exp (L * s)) volume a b :=
    fun _ _ => Continuous.intervalIntegrable (by fun_prop) _ _
  have hvint : IntervalIntegrable v volume 0 T := hint.sub (hexp_int 0 T)
  -- `v ≤ L ∫₀ᵗ v`
  have hstep : ∀ t ∈ Icc 0 T, v t ≤ L * ∫ s in (0 : ℝ)..t, v s := by
    intro t ht
    have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (fun s => A * Real.exp (L * s))
        (L * (A * Real.exp (L * s))) s := fun s _ => by
      have := ((hasDerivAt_id s).const_mul L).exp.const_mul A
      simp only [id] at this
      convert this using 1
      ring
    have hc : Continuous fun s : ℝ => L * (A * Real.exp (L * s)) := by fun_prop
    have hderiv := integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 t)
    rw [intervalIntegral.integral_const_mul] at hderiv
    rw [integral_sub (intervalIntegrable_of_le hint ht) (hexp_int 0 t), mul_sub, hderiv,
      mul_zero, Real.exp_zero, mul_one]
    have := h t ht
    simp only [hv]
    linarith
  -- an a priori upper bound `M` for `v` on `[0,T]`
  set M : ℝ := |A| + L * (∫ s in (0 : ℝ)..T, u s) + |A| * Real.exp (L * T)
  have hM : ∀ t ∈ Icc 0 T, v t ≤ M := by
    intro t ht
    have h1 : ∫ s in (0 : ℝ)..t, u s ≤ ∫ s in (0 : ℝ)..T, u s :=
      integral_mono_interval le_rfl ht.1 ht.2
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs =>
          hu0 s ⟨hs.1.le, hs.2⟩)) hint
    have h2 : -(A * Real.exp (L * t)) ≤ |A| * Real.exp (L * T) := by
      rw [← neg_mul]
      exact mul_le_mul (neg_le_abs A) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hL))
        (Real.exp_pos _).le (abs_nonneg A)
    have h3 := h t ht
    have h4 : L * ∫ s in (0 : ℝ)..t, u s ≤ L * ∫ s in (0 : ℝ)..T, u s :=
      mul_le_mul_of_nonneg_left h1 hL
    simp only [hv]
    linarith [le_abs_self A]
  intro t ht
  have key := volterra_iterate_le (v := fun _ => v) hL (fun _ => hvint) hM
    (fun _ s hs => hstep s hs)
  have := nonpos_of_le_volterra_bound fun n => key n t ht
  simp only [hv] at this
  linarith

/-- **Gronwall with zero constant.** A nonnegative interval integrable `w` with
`w(t) ≤ L ∫₀ᵗ w` on `[0,T]` vanishes on `[0,T]`. -/
theorem eq_zero_of_le_volterra {w : ℝ → ℝ} {L T : ℝ} (hL : 0 ≤ L)
    (hw0 : ∀ t ∈ Icc 0 T, 0 ≤ w t) (hint : IntervalIntegrable w volume 0 T)
    (h : ∀ t ∈ Icc 0 T, w t ≤ L * ∫ s in (0 : ℝ)..t, w s) : ∀ t ∈ Icc 0 T, w t = 0 := by
  intro t ht
  have := gronwall_integral (A := 0) hL hw0 hint (fun s hs => by simpa using h s hs) t ht
  simp only [zero_mul] at this
  exact le_antisymm this (hw0 t ht)

end BlockBand.SourceProcess.Stochastic.SDE
