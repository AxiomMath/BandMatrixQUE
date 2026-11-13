module

public import BlockBand.Diffusion.Kernel.SphereCK

/-!
# A sharp sup bound for the sphere factor `pY`

**Proved here.**
* `skm_le_of_hasDerivAt`: a function with nonpositive derivative on `(a, b)` satisfies
  `g b ≤ g a` (generic helper);
* `sk_leg_eval_zero`: `P̃_n(0) = 1`; `sk_leg_eval_one_sub`: `P̃_n(1 - y) = (-1)ⁿ P̃_n(y)`;
* `sk_leg_abs_le_one`: **`|P̃_n(y)| ≤ 1` on `[0,1]`**, by the classical Lyapunov function
  `G = P̃_n² + y(1-y)P̃_n'²/(n(n+1))`, whose derivative is `-(1-2y)P̃_n'²/(n(n+1))` by the Legendre
  equation `sk_leg_ode` (so `G` decreases on `[0,1/2]` from `G(0) = 1`), and the reflection
  symmetry for `[1/2, 1]`;
* `sk_sum_exp_le`: `Σ_n (2n+1) e^{-(D₀/2)n(n+1)t} ≤ 1 + 3/(D₀t)` for `t > 0` (telescoping:
  `2ak ≤ e^{2ak} - 1` with `a = D₀t/2`);
* `sk_sphereSeries_abs_le`: `|pY_t(y, y')| ≤ 1 + 3/(D₀t)` for `t > 0`, `y, y' ∈ [0,1]`;
* `sk_kernelY_le_inv`: **`pY_t(y, y') ≤ 1 + 3/(D₀t)`** for `t > 0` and all real `y, y'`;
  `sk_kernelY_le_inv'`: the form `pY_t(y, y') ≤ max 1 (3/D₀) · (1 + t⁻¹)`.

The bound is of the correct order: the true diagonal value is `≈ 2/(D₀t)` as `t → 0`
(two-dimensional heat kernel times the area factor `4π`) and `→ 1` as `t → ∞`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial

/-!
### A monotonicity helper
-/

/-- If `g' ≤ 0` on `(a, b)` and `g` has derivative `g'` everywhere, then `g b ≤ g a`. -/
theorem skm_le_of_hasDerivAt {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ s, HasDerivAt g (g' s) s) (hneg : ∀ s ∈ Ioo a b, g' s ≤ 0) : g b ≤ g a := by
  have hA : AntitoneOn g (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun s _ => (hg s).continuousAt.continuousWithinAt)
      (fun s _ => (hg s).hasDerivWithinAt)
      (fun s hs => hneg s (by rwa [interior_Icc] at hs))
  exact hA ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-!
### `|P̃_n| ≤ 1` on `[0,1]`
-/

theorem sk_leg_eval_zero (n : ℕ) : (skLeg n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, sk_leg_coeff]
  simp [skLegCoeff]

/-- Reflection symmetry `P̃_n(1 - y) = (-1)ⁿ P̃_n(y)` (Mathlib's `shiftedLegendre_eval_symm`). -/
theorem sk_leg_eval_one_sub (n : ℕ) (y : ℝ) :
    (skLeg n).eval (1 - y) = (-1) ^ n * (skLeg n).eval y := by
  have e : ∀ x : ℝ, (skLeg n).eval x = aeval x (shiftedLegendre n) := fun x => by
    rw [skLeg, eval_map, aeval_def, algebraMap_int_eq]
  rw [e, e, shiftedLegendre_eval_symm n y, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_mul]

/-- The Lyapunov function `G = P̃_n² + κ y(1-y)P̃_n'²` with `κ = 1/(n(n+1))` has derivative
`-κ(1-2y)P̃_n'²`. -/
theorem sk_leg_lyap_hasDerivAt (n : ℕ) {κ : ℝ} (hκ : κ * ((n : ℝ) * (n + 1)) = 1) (s : ℝ) :
    HasDerivAt (fun x => (skLeg n).eval x ^ 2 +
        κ * ((x - x ^ 2) * (derivative (skLeg n)).eval x ^ 2))
      (-(κ * ((1 - 2 * s) * (derivative (skLeg n)).eval s ^ 2))) s := by
  have hode := congrArg (Polynomial.eval s) (sk_leg_ode n)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_X_pow, eval_add, eval_mul,
    eval_sub, eval_X, eval_pow, eval_one, eval_neg, eval_C] at hode
  push_cast at hode
  have h := ((skLeg n).hasDerivAt s).pow 2 |>.add
    ((((hasDerivAt_id' s).sub ((hasDerivAt_id' s).pow 2)).mul
      (((derivative (skLeg n)).hasDerivAt s).pow 2)).const_mul κ)
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  linear_combination (2 * κ * (derivative (skLeg n)).eval s) * hode +
    (-2 * (skLeg n).eval s * (derivative (skLeg n)).eval s) * hκ

/-- `|P̃_n(y)| ≤ 1` on `[0, 1/2]`. -/
theorem sk_leg_abs_le_one_half (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    |(skLeg n).eval y| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [sk_leg_zero, abs_one]
  have hc : 0 < (n : ℝ) * (n + 1) := by positivity
  set κ := 1 / ((n : ℝ) * (n + 1)) with hκdef
  have hκ : κ * ((n : ℝ) * (n + 1)) = 1 := by rw [hκdef]; field_simp
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hle := skm_le_of_hasDerivAt hy0 (sk_leg_lyap_hasDerivAt n hκ) fun s hs => by
    have : 0 ≤ 1 - 2 * s := by linarith [hs.2]
    have : 0 ≤ κ * ((1 - 2 * s) * (derivative (skLeg n)).eval s ^ 2) := by positivity
    linarith
  simp only [sk_leg_eval_zero] at hle
  have hyy : 0 ≤ y - y ^ 2 := by nlinarith
  have hq : 0 ≤ κ * ((y - y ^ 2) * (derivative (skLeg n)).eval y ^ 2) := by positivity
  have hsq : (skLeg n).eval y ^ 2 ≤ 1 := by
    have : (0 : ℝ) - 0 ^ 2 = 0 := by norm_num
    rw [this, zero_mul, mul_zero, add_zero, one_pow] at hle
    linarith
  exact (sq_le_one_iff_abs_le_one _).1 hsq

/-- **`|P̃_n(y)| ≤ 1` on `[0,1]`.** -/
theorem sk_leg_abs_le_one (n : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |(skLeg n).eval y| ≤ 1 := by
  rcases le_total y (1 / 2) with h | h
  · exact sk_leg_abs_le_one_half n hy.1 h
  · have e := sk_leg_eval_one_sub n (1 - y)
    rw [sub_sub_cancel] at e
    rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact sk_leg_abs_le_one_half n (by linarith [hy.2]) (by linarith)

/-!
### The sharp series bound
-/

/-- The termwise bound `|term_n| ≤ (2n+1)e^{-(D₀/2)n(n+1)t}` on `[0,1]²`. -/
theorem sk_term_abs_le_sharp {D0 t y y' : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hy' : y' ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    |skYTerm D0 t y y' n| ≤ (2 * n + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) := by
  have hc : 0 ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) := by
    positivity
  rw [skYTerm, abs_mul, abs_mul, abs_of_nonneg hc]
  calc (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) *
        |(skLeg n).eval y| * |(skLeg n).eval y'|
      ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * 1 * 1 := by
        gcongr
        · exact sk_leg_abs_le_one n hy
        · exact sk_leg_abs_le_one n hy'
    _ = _ := by ring

theorem sk_summable_sharp {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) :
    Summable fun n : ℕ => (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) := by
  simpa using skp_summable_bound_gen hD0 ht (K := 1) zero_le_one

/-- Partial sums: `Σ_{n ≤ N} (2n+1)e^{-(D₀/2)n(n+1)t} ≤ 1 + (3/(D₀t))(1 - e^{-(D₀/2)N(N+1)t})`. -/
theorem sk_sum_range_exp_le {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
        (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) ≤
      1 + 3 / (D0 * t) * (1 - Real.exp (-(D0 / 2 * ((N : ℝ) * (N + 1)) * t))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    set a := D0 * t / 2 with hadef
    have ha : 0 < a := by positivity
    set k : ℝ := (N : ℝ) + 1 with hkdef
    have hk : 1 ≤ k := by rw [hkdef]; linarith [N.cast_nonneg (α := ℝ)]
    have e1 : -(D0 / 2 * ((N : ℝ) * (N + 1)) * t) = -(D0 / 2 * (k * (k + 1)) * t) + 2 * a * k := by
      rw [hkdef, hadef]; ring
    have e2 : -(D0 / 2 * (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) * t) =
        -(D0 / 2 * (k * (k + 1)) * t) := by rw [hkdef]
    rw [e1, Real.exp_add] at ih
    rw [e2]
    set E := Real.exp (-(D0 / 2 * (k * (k + 1)) * t)) with hEdef
    have hE : 0 < E := Real.exp_pos _
    have hexp : 2 * a * k + 1 ≤ Real.exp (2 * a * k) := Real.add_one_le_exp _
    have h3 : 3 / (D0 * t) = 3 / (2 * a) := by rw [hadef]; ring
    rw [h3] at ih ⊢
    have key : (2 * k + 1) * E ≤ 3 / (2 * a) * (E * Real.exp (2 * a * k) - E) := by
      rw [show 3 / (2 * a) * (E * Real.exp (2 * a * k) - E) =
        3 / (2 * a) * E * (Real.exp (2 * a * k) - 1) by ring]
      calc (2 * k + 1) * E ≤ 3 * k * E := by nlinarith
        _ = 3 / (2 * a) * E * (2 * a * k) := by field_simp
        _ ≤ 3 / (2 * a) * E * (Real.exp (2 * a * k) - 1) := by
            gcongr; linarith
    nlinarith

/-- **The sharp series bound**: `Σ_n (2n+1)e^{-(D₀/2)n(n+1)t} ≤ 1 + 3/(D₀t)` for `t > 0`. -/
theorem sk_sum_exp_le {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) :
    ∑' n : ℕ, (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) ≤
      1 + 3 / (D0 * t) := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  rcases N with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty]; positivity
  · refine (sk_sum_range_exp_le hD0 ht N).trans ?_
    have : 0 < Real.exp (-(D0 / 2 * ((N : ℝ) * (N + 1)) * t)) := Real.exp_pos _
    have : 0 ≤ 3 / (D0 * t) := by positivity
    nlinarith

/-- `|pY_t(y, y')| ≤ 1 + 3/(D₀t)` on `[0,1]²` for `t > 0` (the series). -/
theorem sk_sphereSeries_abs_le {D0 t y y' : ℝ} (hD0 : 0 < D0) (ht : 0 < t)
    (hy : y ∈ Icc (0 : ℝ) 1) (hy' : y' ∈ Icc (0 : ℝ) 1) :
    |skSphereSeries D0 t y y'| ≤ 1 + 3 / (D0 * t) := by
  rw [skSphereSeries]
  have hs := sk_summable_term hD0 ht hy hy'
  calc |∑' n, skYTerm D0 t y y' n| ≤ ∑' n, |skYTerm D0 t y y' n| := by
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm hs.norm).trans_eq ?_
        simp only [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) :=
        Summable.tsum_le_tsum (sk_term_abs_le_sharp hy hy') hs.abs (sk_summable_sharp hD0 ht)
    _ ≤ 1 + 3 / (D0 * t) := sk_sum_exp_le hD0 ht

/-- **Sup bound** (KZ4): `pY_t(y, y') ≤ 1 + 3/(D₀t)` for `t > 0` and all real `y, y'`. -/
theorem sk_kernelY_le_inv {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (y y' : ℝ) :
    skKernelY D0 t y y' ≤ 1 + 3 / (D0 * t) := by
  unfold skKernelY
  split_ifs with h
  · exact (le_abs_self _).trans (sk_sphereSeries_abs_le hD0 ht h.2.1 h.2.2)
  · positivity

/-- **Sup bound, `C(D₀)(1 + t⁻¹)` form**: `pY_t(y, y') ≤ max 1 (3/D₀) · (1 + t⁻¹)`. -/
theorem sk_kernelY_le_inv' {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (y y' : ℝ) :
    skKernelY D0 t y y' ≤ max 1 (3 / D0) * (1 + t⁻¹) := by
  refine (sk_kernelY_le_inv hD0 ht y y').trans ?_
  have h1 : (1 : ℝ) ≤ max 1 (3 / D0) := le_max_left _ _
  have h2 : 3 / D0 ≤ max 1 (3 / D0) := le_max_right _ _
  have e : 3 / (D0 * t) = 3 / D0 * t⁻¹ := by field_simp
  rw [e, mul_add, mul_one]
  have : 0 ≤ t⁻¹ := inv_nonneg.2 ht.le
  nlinarith

end BlockBand.Diffusion
