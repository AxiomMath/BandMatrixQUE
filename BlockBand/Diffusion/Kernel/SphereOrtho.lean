module

public import BlockBand.Diffusion.Kernel.SphereDefs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


/-!
# Orthogonality and norms of the shifted Legendre polynomials

We prove Rodrigues' formula, orthogonality and the `L²` norms of the shifted Legendre polynomials
on `[0,1]`, and that they span the real polynomials.
* `skp_rodrigues`: Rodrigues' formula `n! P̃_n = Dⁿ (X - X²)ⁿ` over `ℝ` (from Mathlib's
  `factorial_mul_shiftedLegendre_eq`);
* `skp_ibp`, `skp_ibp_iter`: polynomial integration by parts on `[0,1]`, iterated against the
  Rodrigues polynomial (whose first `n - 1` derivatives vanish at `0` and `1`);
* `skp_integral_leg_mul_eq_zero`: `∫₀¹ P̃_n q = 0` for `deg q < n`;
* `skp_beta`: `(∫₀¹ yᵃ (1-y)ᵇ) (a+b+1)! = a! b!`;
* `skp_integral_leg_sq`: `∫₀¹ P̃_n² = 1/(2n+1)`;
* `skp_integral_leg_leg`: `∫₀¹ P̃_m P̃_n = δ_{mn}/(2n+1)`;
* `skp_leg_span`: every real polynomial of degree `≤ N` is a combination of `P̃_0, …, P̃_N`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Polynomial

/-- **Rodrigues' formula** over `ℝ`: `n! P̃_n = Dⁿ (X - X²)ⁿ`. -/
theorem skp_rodrigues (n : ℕ) :
    (n.factorial : ℝ[X]) * skLeg n = derivative^[n] (((X : ℝ[X]) - X ^ 2) ^ n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (factorial_mul_shiftedLegendre_eq n)
  rw [Polynomial.map_mul, ← iterate_derivative_map] at h
  have e : ((X : ℝ[X]) - X ^ 2) ^ n =
      ((X ^ n * (1 - X) ^ n : ℤ[X])).map (Int.castRingHom ℝ) := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
      Polynomial.map_one]
    rw [← mul_pow, mul_one_sub, ← pow_two]
  rw [e, ← h, skLeg]
  simp

/-- Polynomial integration by parts on `[0,1]`. -/
theorem skp_ibp (f g : ℝ[X]) :
    ∫ y in (0 : ℝ)..1, (derivative f).eval y * g.eval y =
      f.eval 1 * g.eval 1 - f.eval 0 * g.eval 0 -
        ∫ y in (0 : ℝ)..1, f.eval y * (derivative g).eval y := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun y => g.eval y) (u' := fun y => (derivative g).eval y)
    (v := fun y => f.eval y) (v' := fun y => (derivative f).eval y)
    (fun x _ => g.hasDerivAt x) (fun x _ => f.hasDerivAt x)
    ((derivative g).continuous.intervalIntegrable _ _)
    ((derivative f).continuous.intervalIntegrable _ _)
  have e1 : (∫ y in (0 : ℝ)..1, (derivative f).eval y * g.eval y) =
      ∫ y in (0 : ℝ)..1, g.eval y * (derivative f).eval y := by
    congr 1; funext y; ring
  have e2 : (∫ y in (0 : ℝ)..1, f.eval y * (derivative g).eval y) =
      ∫ y in (0 : ℝ)..1, (derivative g).eval y * f.eval y := by
    congr 1; funext y; ring
  rw [e1, h, e2]
  ring

/-- The first `n - 1` derivatives of the Rodrigues polynomial vanish at `0` and `1`. -/
theorem skp_rodrigues_bdry {n i : ℕ} (hi : i < n) :
    (derivative^[i] (((X : ℝ[X]) - X ^ 2) ^ n)).eval 0 = 0 ∧
      (derivative^[i] (((X : ℝ[X]) - X ^ 2) ^ n)).eval 1 = 0 := by
  obtain ⟨r, hr⟩ := pow_sub_dvd_iterate_derivative_pow ((X : ℝ[X]) - X ^ 2) n i
  have hk : n - i ≠ 0 := by omega
  rw [hr]
  simp [zero_pow hk]

/-- Iterated integration by parts against the Rodrigues polynomial. -/
theorem skp_ibp_iter (n : ℕ) (q : ℝ[X]) {i : ℕ} (hi : i ≤ n) :
    ∫ y in (0 : ℝ)..1, (derivative^[n] (((X : ℝ[X]) - X ^ 2) ^ n)).eval y * q.eval y =
      (-1) ^ i * ∫ y in (0 : ℝ)..1,
        (derivative^[n - i] (((X : ℝ[X]) - X ^ 2) ^ n)).eval y * (derivative^[i] q).eval y := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [ih (by omega)]
    have hni : n - i = (n - (i + 1)) + 1 := by omega
    have hb := skp_rodrigues_bdry (n := n) (i := n - (i + 1)) (by omega)
    rw [hni, Function.iterate_succ_apply' derivative (n - (i + 1)), skp_ibp, hb.1, hb.2,
      Function.iterate_succ_apply' derivative i q]
    ring

/-- **Orthogonality to lower degrees**: `∫₀¹ P̃_n q = 0` for `deg q < n`. -/
theorem skp_integral_leg_mul_eq_zero {n : ℕ} {q : ℝ[X]} (hq : q.natDegree < n) :
    ∫ y in (0 : ℝ)..1, (skLeg n).eval y * q.eval y = 0 := by
  have h := skp_ibp_iter n q (le_refl n)
  rw [iterate_derivative_eq_zero hq, ← skp_rodrigues] at h
  have h2 : (n.factorial : ℝ) * ∫ y in (0 : ℝ)..1, (skLeg n).eval y * q.eval y = 0 := by
    rw [← intervalIntegral.integral_const_mul]
    simpa [mul_assoc] using h
  exact (mul_eq_zero.1 h2).resolve_left (by positivity)

/-- **The Beta integral** `(∫₀¹ yᵃ (1-y)ᵇ) (a+b+1)! = a! b!`. -/
theorem skp_beta (a b : ℕ) :
    (∫ y in (0 : ℝ)..1, y ^ a * (1 - y) ^ b) * ((a + b + 1).factorial : ℝ) =
      a.factorial * b.factorial := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, add_zero, integral_pow, one_pow, ne_eq, add_eq_zero,
      one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero, Nat.factorial_zero,
      Nat.cast_one, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    field_simp
  | succ b ih =>
    have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => (1 - y) ^ (b + 1))
        (-((b + 1 : ℝ) * (1 - x) ^ b)) x := by
      intro x _
      refine (((hasDerivAt_id x).const_sub 1).pow (b + 1)).congr_deriv ?_
      simp
    have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => y ^ (a + 1) / (a + 1)) (x ^ a) x := by
      intro x _
      refine ((hasDerivAt_pow (a + 1) x).div_const ((a : ℝ) + 1)).congr_deriv ?_
      have : (a : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -((b + 1 : ℝ) * (1 - x) ^ b)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun x : ℝ => x ^ a).intervalIntegrable 0 1)
    have key : (∫ y in (0 : ℝ)..1, y ^ a * (1 - y) ^ (b + 1)) =
        (b + 1) / (a + 1) * ∫ y in (0 : ℝ)..1, y ^ (a + 1) * (1 - y) ^ b := by
      have e1 : (∫ y in (0 : ℝ)..1, y ^ a * (1 - y) ^ (b + 1)) =
          ∫ y in (0 : ℝ)..1, (1 - y) ^ (b + 1) * y ^ a := by
        congr 1; funext y; ring
      have e2 : (∫ y in (0 : ℝ)..1, -((b + 1 : ℝ) * (1 - y) ^ b) * (y ^ (a + 1) / (a + 1))) =
          -((b + 1) / (a + 1)) * ∫ y in (0 : ℝ)..1, y ^ (a + 1) * (1 - y) ^ b := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1; funext y; ring
      rw [e1, h, e2]
      simp
    rw [key, show a + (b + 1) + 1 = (a + 1) + b + 1 by ring, mul_assoc, ih (a + 1)]
    simp only [Nat.factorial_succ, Nat.cast_mul]
    have : (a : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

theorem skp_leg_natDegree_le (n : ℕ) : (skLeg n).natDegree ≤ n :=
  natDegree_map_le.trans (natDegree_shiftedLegendre n).le

theorem skp_legCoeff_self_ne_zero (n : ℕ) : skLegCoeff n n ≠ 0 := by
  have h : ((n + n).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ n + n)).ne'
  simp [skLegCoeff, h]

/-- **The norm**: `∫₀¹ P̃_n² = 1/(2n+1)`. -/
theorem skp_integral_leg_sq (n : ℕ) :
    ∫ y in (0 : ℝ)..1, (skLeg n).eval y * (skLeg n).eval y = 1 / (2 * n + 1) := by
  have h := skp_ibp_iter n (skLeg n) (le_refl n)
  have hD : derivative^[n] (skLeg n) = C ((n.factorial : ℝ) * skLegCoeff n n) := by
    have hdeg : (derivative^[n] (skLeg n)).natDegree = 0 := by
      have := natDegree_iterate_derivative (skLeg n) n
      have h2 := skp_leg_natDegree_le n
      omega
    rw [eq_C_of_natDegree_eq_zero hdeg, coeff_iterate_derivative, zero_add, sk_leg_coeff,
      Nat.descFactorial_self, nsmul_eq_mul]
  rw [← skp_rodrigues, Nat.sub_self, Function.iterate_zero_apply, hD] at h
  set I := ∫ y in (0 : ℝ)..1, (skLeg n).eval y * (skLeg n).eval y with hIdef
  set J := ∫ y in (0 : ℝ)..1, y ^ n * (1 - y) ^ n with hJdef
  have hJ : (∫ y in (0 : ℝ)..1, (((X : ℝ[X]) - X ^ 2) ^ n).eval y *
      (C ((n.factorial : ℝ) * skLegCoeff n n)).eval y) =
      (n.factorial : ℝ) * skLegCoeff n n * J := by
    rw [hJdef, ← intervalIntegral.integral_const_mul]
    congr 1; funext y
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    rw [show y - y ^ 2 = y * (1 - y) by ring, mul_pow]
    ring
  have hI : (n.factorial : ℝ) * I = (n.factorial : ℝ) * ((-1) ^ n * skLegCoeff n n * J) := by
    rw [hIdef, ← intervalIntegral.integral_const_mul]
    have : (∫ y in (0 : ℝ)..1, (n.factorial : ℝ) * ((skLeg n).eval y * (skLeg n).eval y)) =
        ∫ y in (0 : ℝ)..1, ((n.factorial : ℝ[X]) * skLeg n).eval y * (skLeg n).eval y := by
      congr 1; funext y; simp [mul_assoc]
    rw [this, h, hJ]
    ring
  have hI' : I = (-1) ^ n * skLegCoeff n n * J :=
    mul_left_cancel₀ (by positivity : (n.factorial : ℝ) ≠ 0) hI
  have hB := skp_beta n n
  have hC : ((n + n).choose n : ℝ) * n.factorial * n.factorial = (n + n).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ n + n)
    rw [show n + n - n = n by omega] at this
    exact_mod_cast this
  rw [hI', skLegCoeff]
  simp only [Nat.choose_self, Nat.cast_one, mul_one]
  have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [show n + n + 1 = (n + n).succ by rfl, Nat.factorial_succ] at hB
  have hF : ((n + n).factorial : ℝ) ≠ 0 := by positivity
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  push_cast at hB
  rw [← mul_assoc, hsq, one_mul, eq_div_iff h2n]
  refine mul_right_cancel₀ hF ?_
  calc ((n + n).choose n : ℝ) * J * (2 * n + 1) * (n + n).factorial =
      ((n + n).choose n : ℝ) * (J * ((n + n + 1) * ((n + n).factorial : ℝ))) := by ring
    _ = ((n + n).choose n : ℝ) * (n.factorial * n.factorial) := by rw [hB]
    _ = 1 * (n + n).factorial := by rw [← hC]; ring

/-- **Orthogonality**: `∫₀¹ P̃_m P̃_n = δ_{mn}/(2n+1)`. -/
theorem skp_integral_leg_leg (m n : ℕ) :
    ∫ y in (0 : ℝ)..1, (skLeg m).eval y * (skLeg n).eval y =
      (if m = n then 1 / (2 * (n : ℝ) + 1) else 0 : ℝ) := by
  split_ifs with h
  · subst h; exact skp_integral_leg_sq m
  · rcases lt_or_gt_of_ne h with hmn | hmn
    · have := skp_integral_leg_mul_eq_zero (n := n) (q := skLeg m)
        ((skp_leg_natDegree_le m).trans_lt hmn)
      calc _ = ∫ y in (0 : ℝ)..1, (skLeg n).eval y * (skLeg m).eval y := by
            congr 1; funext y; ring
        _ = 0 := this
    · exact skp_integral_leg_mul_eq_zero ((skp_leg_natDegree_le n).trans_lt hmn)

theorem skp_leg_zero_eq : skLeg 0 = 1 := by
  simp [skLeg, shiftedLegendre]

/-- **Spanning**: every real polynomial of degree `≤ N` is a combination of `P̃_0, …, P̃_N`. -/
theorem skp_leg_span (N : ℕ) : ∀ q : ℝ[X], q.natDegree ≤ N →
    ∃ β : ℕ → ℝ, q = ∑ m ∈ Finset.range (N + 1), C (β m) * skLeg m := by
  induction N with
  | zero =>
    intro q hq
    refine ⟨fun _ => q.coeff 0, ?_⟩
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, skp_leg_zero_eq, mul_one]
    exact eq_C_of_natDegree_le_zero hq
  | succ N ih =>
    intro q hq
    set c := q.coeff (N + 1) / skLegCoeff (N + 1) (N + 1) with hcdef
    have hc0 := skp_legCoeff_self_ne_zero (N + 1)
    set r := q - C c * skLeg (N + 1) with hrdef
    have hr : r.natDegree ≤ N := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hrdef, coeff_sub, coeff_C_mul, sk_leg_coeff]
      rcases Nat.lt_or_ge (N + 1) k with hk' | hk'
      · have h1 : q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        have h2 : (N + 1).choose k = 0 := Nat.choose_eq_zero_of_lt hk'
        simp [h1, skLegCoeff, h2]
      · have hk'' : k = N + 1 := by omega
        subst hk''
        rw [hcdef]
        field_simp
        ring
    obtain ⟨β, hβ⟩ := ih r hr
    refine ⟨fun m => if m = N + 1 then c else β m, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [↓reduceIte]
    have hs : (∑ m ∈ Finset.range (N + 1),
        C (if m = N + 1 then c else β m) * skLeg m) =
        ∑ m ∈ Finset.range (N + 1), C (β m) * skLeg m := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have : m ≠ N + 1 := by have := Finset.mem_range.1 hm; omega
      simp only [this, ↓reduceIte]
    rw [hs, ← hβ, hrdef]
    ring

end BlockBand.Diffusion
