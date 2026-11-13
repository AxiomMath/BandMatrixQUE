module

public import BlockBand.Diffusion.Kernel.SphereMoreSup
public import BlockBand.Diffusion.Kernel.SphereApprox

/-!
# Second-order expansion and increment moments of the sphere factor

We prove a second-order expansion of the spherical semigroup on polynomials and deduce a bound
on the fourth increment moment of the sphere factor `pY`.

* `skm_taylor2`: a generic second-order Taylor bound `|f h - f 0 - h f'(0)| ≤ K h²/2` when
  `|f''| ≤ K` on `(0, ∞)`, by two monotonicity arguments;
* `sk_poly_taylor2`: **second-order expansion on polynomials**: for a real polynomial `q` with
  `|skpL (skpL q)| ≤ M` on `[0,1]`, `h > 0`, `y ∈ [0,1]`,
  `|∫₀¹ pY_h(y,w) q(w) dw - q(y) - h (D₀/2)(skpL q)(y)| ≤ (D₀/2)² M h²/2`.
  Proof: `q = Σ_{m ≤ N} β_m P̃_m` (`skp_leg_span`), so `f(s) = ∫₀¹ pY_s(y,·) q` is the finite
  exponential sum `Σ β_m e^{-λ_m s} P̃_m(y)` (`skp_integral_series_legSum`); then
  `f(0) = q(y)`, `f'(0) = (D₀/2)(skpL q)(y)` and `f''(s) = (D₀/2)² ∫₀¹ pY_s(y,·) skpL (skpL q)`,
  which is at most `(D₀/2)² M` in absolute value by positivity and normalisation (contraction
  `sk_abs_integral_series_mul_le`);
* `sk_semigroupY_poly_taylor2`: the same for `skSemigroupY D0 q.eval h y = ∫ pY_h(y,y') q(y') dy'`;
* `skm_LL_quartic_abs_le`: for `q_y = (X - y)⁴`, `|skpL (skpL q_y)| ≤ 64` on `[0,1]` (`y ∈ [0,1]`),
  from the explicit form `24a² + 96abu + (24 - 168a)u² - 8bu³`, `a = w(1-w)`, `b = 1 - 2w`,
  `u = w - y`; `q_y(y) = 0` and `(skpL q_y)(y) = 0`;
* `sk_kernelY_moment4_le`: **`∫ (y' - y)⁴ pY_h(y, y') dy' ≤ 8 D₀² h²`** for `h > 0`,
  `y ∈ [0,1]`, and `sk_kernelY_moment4_nonneg`: it is `≥ 0`.

The constant `8 D₀²` is crude; the true small-`h` value is `3 (D₀ y(1-y))² h² ≤ (3/16) D₀² h²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial

/-!
### A second-order Taylor bound
-/

/-- **Second-order Taylor bound**: `|f h - f 0 - h f₁ 0| ≤ K h²/2` for `h ≥ 0` when `f' = f₁`,
`f₁' = f₂` everywhere and `|f₂| ≤ K` on `(0, ∞)`. -/
theorem skm_taylor2 {f f1 f2 : ℝ → ℝ} {K h : ℝ} (hh : 0 ≤ h)
    (hf : ∀ s, HasDerivAt f (f1 s) s) (hf1 : ∀ s, HasDerivAt f1 (f2 s) s)
    (hK : ∀ s, 0 < s → |f2 s| ≤ K) :
    |f h - f 0 - h * f1 0| ≤ K * h ^ 2 / 2 := by
  have h1 : ∀ s, 0 ≤ s → |f1 s - f1 0| ≤ K * s := by
    intro s hs
    have up := skm_le_of_hasDerivAt hs (g := fun r => f1 r - f1 0 - K * r)
      (g' := fun r => f2 r - K)
      (fun r => (((hf1 r).sub_const (f1 0)).sub ((hasDerivAt_id' r).const_mul K)).congr_deriv
        (by ring))
      (fun r hr => by linarith [(abs_le.1 (hK r hr.1)).2])
    have lo := skm_le_of_hasDerivAt hs (g := fun r => -(f1 r - f1 0) - K * r)
      (g' := fun r => -f2 r - K)
      (fun r => (((hf1 r).sub_const (f1 0)).neg.sub ((hasDerivAt_id' r).const_mul K)).congr_deriv
        (by ring))
      (fun r hr => by linarith [(abs_le.1 (hK r hr.1)).1])
    simp only [sub_self, mul_zero, neg_zero] at up lo
    rw [abs_le]; constructor <;> linarith
  have up := skm_le_of_hasDerivAt hh (g := fun r => f r - f 0 - r * f1 0 - K * r ^ 2 / 2)
    (g' := fun r => f1 r - f1 0 - K * r)
    (fun r => ((((hf r).sub_const (f 0)).sub ((hasDerivAt_id' r).mul_const (f1 0))).sub
      (((hasDerivAt_pow 2 r).const_mul K).div_const 2)).congr_deriv (by
        simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring))
    (fun r hr => by linarith [(abs_le.1 (h1 r hr.1.le)).2])
  have lo := skm_le_of_hasDerivAt hh (g := fun r => -(f r - f 0 - r * f1 0) - K * r ^ 2 / 2)
    (g' := fun r => -(f1 r - f1 0) - K * r)
    (fun r => ((((hf r).sub_const (f 0)).sub ((hasDerivAt_id' r).mul_const (f1 0))).neg.sub
      (((hasDerivAt_pow 2 r).const_mul K).div_const 2)).congr_deriv (by
        simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring))
    (fun r hr => by linarith [(abs_le.1 (h1 r hr.1.le)).1])
  simp only [sub_self, zero_mul, neg_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, zero_div] at up lo
  rw [abs_le]; constructor <;> linarith

/-!
### The Legendre operator on Legendre sums
-/

theorem skm_L_C_mul_leg (b : ℝ) (m : ℕ) :
    skpL (C b * skLeg m) = C (b * -((m : ℝ) * (m + 1))) * skLeg m := by
  rw [skp_L_C_mul, skp_L_leg]
  simp only [map_mul, map_neg]
  ring

theorem skm_L_legSum (N : ℕ) (β : ℕ → ℝ) :
    skpL (∑ m ∈ Finset.range (N + 1), C (β m) * skLeg m) =
      ∑ m ∈ Finset.range (N + 1), C (β m * -((m : ℝ) * (m + 1))) * skLeg m := by
  rw [skp_L_sum]
  exact Finset.sum_congr rfl fun m _ => skm_L_C_mul_leg (β m) m

theorem skm_exp_term_hasDerivAt (b c P s : ℝ) :
    HasDerivAt (fun r => b * Real.exp (-(c * r)) * P) (b * (-c * Real.exp (-(c * s))) * P) s :=
  ((((hasDerivAt_id' s).const_mul c).neg.exp).const_mul b |>.mul_const P).congr_deriv (by
    simp only [Pi.neg_apply]; ring)

/-!
### Second-order expansion on polynomials
-/

/-- **Second-order expansion of `P_h q`** for a polynomial `q` with `|skpL (skpL q)| ≤ M` on
`[0,1]`: `|∫₀¹ pY_h(y,w) q(w) dw - q(y) - h (D₀/2)(skpL q)(y)| ≤ (D₀/2)² M h²/2`. -/
theorem sk_poly_taylor2 {D0 : ℝ} (hD0 : 0 < D0) (q : ℝ[X]) {M : ℝ}
    (hM : ∀ w ∈ Icc (0 : ℝ) 1, |(skpL (skpL q)).eval w| ≤ M) {h y : ℝ} (hh : 0 < h)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |(∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * q.eval w) - q.eval y -
        h * (D0 / 2 * (skpL q).eval y)| ≤ (D0 / 2) ^ 2 * M * h ^ 2 / 2 := by
  obtain ⟨N, hN⟩ : ∃ N, q.natDegree = N := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ := skp_leg_span N q hN.le
  set f : ℝ → ℝ := fun s => ∑ m ∈ Finset.range (N + 1),
    β m * Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * s)) * (skLeg m).eval y with hfdef
  set f1 : ℝ → ℝ := fun s => ∑ m ∈ Finset.range (N + 1),
    β m * (-(D0 / 2 * ((m : ℝ) * (m + 1))) * Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * s))) *
      (skLeg m).eval y with hf1def
  set f2 : ℝ → ℝ := fun s => ∑ m ∈ Finset.range (N + 1),
    (β m * -(D0 / 2 * ((m : ℝ) * (m + 1)))) *
      (-(D0 / 2 * ((m : ℝ) * (m + 1))) * Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * s))) *
      (skLeg m).eval y with hf2def
  have hf : ∀ s, HasDerivAt f (f1 s) s := fun s =>
    HasDerivAt.fun_sum fun m _ => skm_exp_term_hasDerivAt _ _ _ s
  have hf1 : ∀ s, HasDerivAt f1 (f2 s) s := fun s =>
    HasDerivAt.fun_sum fun m _ => (skm_exp_term_hasDerivAt
      (β m * -(D0 / 2 * ((m : ℝ) * (m + 1)))) _ _ s).congr_of_eventuallyEq
      (Eventually.of_forall fun r => by ring)
  have hLq := skm_L_legSum N β
  have hLLq := skm_L_legSum N (fun m => β m * -((m : ℝ) * (m + 1)))
  rw [← hβ] at hLq
  rw [← hLq] at hLLq
  have hK : ∀ s, 0 < s → |f2 s| ≤ (D0 / 2) ^ 2 * M := by
    intro s hs
    have hI := skp_integral_series_legSum hD0 hs hy N
      (fun m => β m * -((m : ℝ) * (m + 1)) * -((m : ℝ) * (m + 1)))
    rw [← hLLq] at hI
    have hc := sk_abs_integral_series_mul_le hD0 hs hy
      ((skpL (skpL q)).continuous.continuousOn) hM
    rw [hI] at hc
    have e : f2 s = (D0 / 2) ^ 2 * ∑ m ∈ Finset.range (N + 1),
        β m * -((m : ℝ) * (m + 1)) * -((m : ℝ) * (m + 1)) *
          Real.exp (-(D0 / 2 * ((m : ℝ) * (m + 1)) * s)) * (skLeg m).eval y := by
      rw [hf2def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hT := skm_taylor2 hh.le hf hf1 hK
  have hI : (∫ w in (0 : ℝ)..1, skSphereSeries D0 h y w * q.eval w) = f h := by
    rw [hfdef]
    conv_lhs => rw [hβ]
    exact skp_integral_series_legSum hD0 hh hy N β
  have h0 : f 0 = q.eval y := by
    rw [hfdef]
    conv_rhs => rw [hβ]
    simp [eval_finsetSum]
  have h10 : f1 0 = D0 / 2 * (skpL q).eval y := by
    rw [hf1def, hLq]
    simp only [eval_finsetSum, eval_mul, eval_C, Finset.mul_sum, mul_zero, neg_zero,
      Real.exp_zero]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hI, ← h0, ← h10]
  calc |f h - f 0 - h * f1 0| ≤ (D0 / 2) ^ 2 * M * h ^ 2 / 2 := hT

/-- **Second-order expansion of the semigroup on polynomials** (Bochner form). -/
theorem sk_semigroupY_poly_taylor2 {D0 : ℝ} (hD0 : 0 < D0) (q : ℝ[X]) {M : ℝ}
    (hM : ∀ w ∈ Icc (0 : ℝ) 1, |(skpL (skpL q)).eval w| ≤ M) {h y : ℝ} (hh : 0 < h)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |skSemigroupY D0 (fun w => q.eval w) h y - q.eval y - h * (D0 / 2 * (skpL q).eval y)| ≤
      (D0 / 2) ^ 2 * M * h ^ 2 / 2 := by
  rw [sk_semigroupY_eq_intervalIntegral hh hy]
  exact sk_poly_taylor2 hD0 q hM hh hy

/-!
### The quartic increment
-/

theorem skm_L_quartic_eval (y w : ℝ) :
    (skpL ((X - C y) ^ 4)).eval w =
      12 * (w * (1 - w)) * (w - y) ^ 2 + 4 * (1 - 2 * w) * (w - y) ^ 3 := by
  simp only [skpL, derivative_mul, derivative_sub, derivative_X, derivative_pow, derivative_C,
    derivative_one, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C, eval_one, eval_zero,
    Nat.cast_ofNat, map_zero]
  push_cast
  ring

theorem skm_L_quartic (y : ℝ) : skpL ((X - C y) ^ 4) =
    C 12 * (X - X ^ 2) * (X - C y) ^ 2 + C 4 * (1 - C 2 * X) * (X - C y) ^ 3 := by
  refine Polynomial.funext fun w => ?_
  rw [skm_L_quartic_eval]
  simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C, eval_one]
  ring

theorem skm_LL_quartic_eval (y w : ℝ) :
    (skpL (skpL ((X - C y) ^ 4))).eval w =
      24 * (w * (1 - w)) ^ 2 + 96 * (w * (1 - w)) * (1 - 2 * w) * (w - y) +
        (24 - 168 * (w * (1 - w))) * (w - y) ^ 2 - 8 * (1 - 2 * w) * (w - y) ^ 3 := by
  rw [skm_L_quartic]
  simp only [skpL, derivative_mul, derivative_sub, derivative_X, derivative_pow, derivative_C,
    derivative_one, derivative_add, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C,
    eval_one, eval_zero, Nat.cast_ofNat, map_zero]
  push_cast
  ring

/-- `|skpL (skpL (X - y)⁴)| ≤ 64` on `[0,1]`, for `y ∈ [0,1]`. -/
theorem skm_LL_quartic_abs_le {y w : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    |(skpL (skpL ((X - C y) ^ 4))).eval w| ≤ 64 := by
  rw [skm_LL_quartic_eval]
  set a := w * (1 - w) with hadef
  set b := 1 - 2 * w with hbdef
  set u := w - y with hudef
  have ha0 : 0 ≤ a := by rw [hadef]; nlinarith [hw.1, hw.2]
  have ha1 : a ≤ 1 / 4 := by rw [hadef]; nlinarith [sq_nonneg (w - 1 / 2)]
  have hb : |b| ≤ 1 := by rw [hbdef, abs_le]; constructor <;> linarith [hw.1, hw.2]
  have hu : |u| ≤ 1 := by rw [hudef, abs_le]; constructor <;> linarith [hw.1, hw.2, hy.1, hy.2]
  have hu2 : u ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one u).2 hu
  have hbu : |b| * |u| ≤ 1 :=
    (mul_le_mul hb hu (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hu3 : |u| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
  have t1 : |24 * a ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have t2 : |96 * a * b * u| ≤ 24 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 96)]
    nlinarith [abs_nonneg b, abs_nonneg u]
  have t3 : |(24 - 168 * a) * u ^ 2| ≤ 24 := by
    have h24 : |24 - 168 * a| ≤ 24 := by rw [abs_le]; constructor <;> linarith
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
    nlinarith [abs_nonneg (24 - 168 * a), sq_nonneg u]
  have t4 : |8 * b * u ^ 3| ≤ 8 := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    nlinarith [abs_nonneg b, abs_nonneg u, pow_nonneg (abs_nonneg u) 3]
  calc |24 * a ^ 2 + 96 * a * b * u + (24 - 168 * a) * u ^ 2 - 8 * b * u ^ 3|
      ≤ |24 * a ^ 2 + 96 * a * b * u + (24 - 168 * a) * u ^ 2| + |8 * b * u ^ 3| :=
        abs_sub _ _
    _ ≤ |24 * a ^ 2| + |96 * a * b * u| + |(24 - 168 * a) * u ^ 2| + |8 * b * u ^ 3| := by
        gcongr; exact abs_add_three _ _ _
    _ ≤ 64 := by linarith

/-- **Fourth increment moment**: `∫ (y' - y)⁴ pY_h(y, y') dy' ≤ 8 D₀² h²` for `h > 0`,
`y ∈ [0,1]`. -/
theorem sk_kernelY_moment4_le {D0 h y : ℝ} (hD0 : 0 < D0) (hh : 0 < h)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫ y', (y' - y) ^ 4 * skKernelY D0 h y y' ≤ 8 * D0 ^ 2 * h ^ 2 := by
  have hT := sk_semigroupY_poly_taylor2 hD0 ((X - C y) ^ 4) (M := 64)
    (fun w hw => skm_LL_quartic_abs_le hy hw) hh hy
  have e : skSemigroupY D0 (fun w => ((X - C y) ^ 4).eval w) h y =
      ∫ y', (y' - y) ^ 4 * skKernelY D0 h y y' := by
    unfold skSemigroupY
    congr 1; funext y'
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    ring
  have h0 : ((X - C y) ^ 4).eval y = 0 := by simp
  have h1 : (skpL ((X - C y) ^ 4)).eval y = 0 := by rw [skm_L_quartic_eval]; ring
  rw [e, h0, h1] at hT
  have := (abs_le.1 hT).2
  nlinarith

/-- The fourth increment moment is nonnegative. -/
theorem sk_kernelY_moment4_nonneg {D0 : ℝ} (hD0 : 0 < D0) (h y : ℝ) :
    0 ≤ ∫ y', (y' - y) ^ 4 * skKernelY D0 h y y' :=
  integral_nonneg fun y' => mul_nonneg (by positivity) (sk_kernelY_nonneg hD0 h y y')

end BlockBand.Diffusion
