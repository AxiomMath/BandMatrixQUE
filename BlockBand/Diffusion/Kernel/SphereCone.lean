module

public import BlockBand.Diffusion.Kernel.SphereOrtho


/-!
# The Legendre operator preserves the Bernstein cone

The radial generator of the sphere, `L p = (X(1-X) p')'` (`skpL`, the operator of
`sk_leg_ode` up to the factor `D₀/2`), maps the degree-`N` Bernstein monomials
`e_j = Xʲ (1-X)^{N-j}` (`skpBern`) to a tridiagonal combination with **nonnegative
off-diagonal coefficients** (`skp_L_mono`):
`L e_j = j² e_{j-1} + (N-j)² e_{j+1} - (2j(N-j) + N) e_j`.
Hence for `0 ≤ s` small the explicit Euler step `T_s = 1 + s L` (`skpT`) maps the cone
`SkpCone N` of nonnegative combinations of `e_0, …, e_N` into itself (`skp_cone_T`), and
cone elements are nonnegative on `[0,1]` (`skp_cone_eval_nonneg`). On the Legendre basis
`T_s` is diagonal: `T_sⁱ (Σ βₘ P̃ₘ) = Σ βₘ (1 - s m(m+1))ⁱ P̃ₘ` (`skp_T_iterate_leg`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open Set Polynomial

/-- The Legendre operator `L p = (X(1-X) p')'` on real polynomials. -/
def skpL (p : ℝ[X]) : ℝ[X] := derivative ((X - X ^ 2) * derivative p)

/-- The explicit Euler step `T_s p = p + s L p`. -/
def skpT (s : ℝ) (p : ℝ[X]) : ℝ[X] := p + C s * skpL p

/-- The degree-`N` Bernstein monomial `e_j = Xʲ (1-X)^{N-j}`. -/
def skpBern (N j : ℕ) : ℝ[X] := X ^ j * (1 - X) ^ (N - j)

/-- The Bernstein cone: nonnegative combinations of `e_0, …, e_N`. -/
def SkpCone (N : ℕ) (p : ℝ[X]) : Prop :=
  ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ p = ∑ j ∈ Finset.range (N + 1), C (c j) * skpBern N j

theorem skp_L_add (p q : ℝ[X]) : skpL (p + q) = skpL p + skpL q := by
  simp [skpL, mul_add]

theorem skp_L_C_mul (c : ℝ) (p : ℝ[X]) : skpL (C c * p) = C c * skpL p := by
  unfold skpL
  rw [derivative_C_mul, mul_left_comm, derivative_C_mul]

theorem skp_L_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    skpL (∑ i ∈ s, f i) = ∑ i ∈ s, skpL (f i) := by
  simp only [skpL, derivative_sum, Finset.mul_sum]

theorem skp_L_leg (m : ℕ) : skpL (skLeg m) = -(C ((m : ℝ) * (m + 1)) * skLeg m) :=
  sk_leg_ode m

theorem skp_T_add (s : ℝ) (p q : ℝ[X]) : skpT s (p + q) = skpT s p + skpT s q := by
  simp only [skpT, skp_L_add]; ring

theorem skp_T_C_mul (s c : ℝ) (p : ℝ[X]) : skpT s (C c * p) = C c * skpT s p := by
  simp only [skpT, skp_L_C_mul]; ring

theorem skp_T_sum (s : ℝ) {ι : Type*} (t : Finset ι) (f : ι → ℝ[X]) :
    skpT s (∑ i ∈ t, f i) = ∑ i ∈ t, skpT s (f i) := by
  simp only [skpT, skp_L_sum, Finset.sum_add_distrib, Finset.mul_sum]

/-!
### Cone closure properties
-/

theorem skp_cone_zero (N : ℕ) : SkpCone N 0 :=
  ⟨fun _ => 0, fun _ => le_rfl, by simp⟩

theorem skp_cone_add {N : ℕ} {p q : ℝ[X]} (hp : SkpCone N p) (hq : SkpCone N q) :
    SkpCone N (p + q) := by
  obtain ⟨c, hc, rfl⟩ := hp
  obtain ⟨d, hd, rfl⟩ := hq
  refine ⟨fun j => c j + d j, fun j => add_nonneg (hc j) (hd j), ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_add]; ring

theorem skp_cone_smul {N : ℕ} {a : ℝ} (ha : 0 ≤ a) {p : ℝ[X]} (hp : SkpCone N p) :
    SkpCone N (C a * p) := by
  obtain ⟨c, hc, rfl⟩ := hp
  refine ⟨fun j => a * c j, fun j => mul_nonneg ha (hc j), ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_mul]; ring

theorem skp_cone_gen {N j : ℕ} (hj : j ≤ N) : SkpCone N (skpBern N j) := by
  refine ⟨fun i => if i = j then 1 else 0, fun i => by positivity, ?_⟩
  have hjm : j ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  rw [Finset.sum_eq_single_of_mem j hjm]
  · simp
  · intro i _ hij
    simp [hij]

theorem skp_cone_sum {N : ℕ} {ι : Type*} (t : Finset ι) (f : ι → ℝ[X])
    (h : ∀ i ∈ t, SkpCone N (f i)) : SkpCone N (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using skp_cone_zero N
  | insert a t hat ih =>
    rw [Finset.sum_insert hat]
    exact skp_cone_add (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem skp_bern_eval_nonneg (N j : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ (skpBern N j).eval y := by
  have h1 : 0 ≤ 1 - y := by linarith [hy.2]
  simp only [skpBern, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg h1 _)

theorem skp_cone_eval_nonneg {N : ℕ} {p : ℝ[X]} (hp : SkpCone N p) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ p.eval y := by
  obtain ⟨c, hc, rfl⟩ := hp
  rw [eval_finsetSum]
  exact Finset.sum_nonneg fun j _ => by
    rw [eval_mul, eval_C]; exact mul_nonneg (hc j) (skp_bern_eval_nonneg N j hy)

theorem skp_bern_natDegree_le (N j : ℕ) (hj : j ≤ N) : (skpBern N j).natDegree ≤ N := by
  unfold skpBern
  refine (natDegree_mul_le).trans ?_
  have h1 : (X ^ j : ℝ[X]).natDegree ≤ j := natDegree_X_pow_le j
  have h2 : ((1 - X : ℝ[X]) ^ (N - j)).natDegree ≤ N - j := by
    refine (natDegree_pow_le).trans ?_
    have : (1 - X : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_
      simp
    calc (N - j) * (1 - X : ℝ[X]).natDegree ≤ (N - j) * 1 := Nat.mul_le_mul_left _ this
      _ = N - j := mul_one _
  omega

theorem skp_cone_natDegree_le {N : ℕ} {p : ℝ[X]} (hp : SkpCone N p) : p.natDegree ≤ N := by
  obtain ⟨c, _, rfl⟩ := hp
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  exact skp_bern_natDegree_le N j (by have := Finset.mem_range.1 hj; omega)

/-!
### The operator on Bernstein monomials
-/

theorem skp_deriv_X_pow_succ (n : ℕ) :
    derivative (X ^ (n + 1) : ℝ[X]) = C ((n : ℝ) + 1) * X ^ n := by
  rw [derivative_X_pow]; simp

theorem skp_deriv_one_sub_pow_succ (n : ℕ) :
    derivative ((1 - X) ^ (n + 1) : ℝ[X]) = -(C ((n : ℝ) + 1) * (1 - X) ^ n) := by
  rw [derivative_pow]; simp

theorem skp_deriv_mono (a b : ℕ) :
    derivative (X ^ (a + 1) * (1 - X) ^ (b + 1) : ℝ[X]) =
      C ((a : ℝ) + 1) * (X ^ a * (1 - X) ^ (b + 1)) -
        C ((b : ℝ) + 1) * (X ^ (a + 1) * (1 - X) ^ b) := by
  rw [derivative_mul, skp_deriv_X_pow_succ, skp_deriv_one_sub_pow_succ]; ring

/-- **The Legendre operator on Bernstein monomials** (exponents in `ℕ`; the coefficients of the
out-of-range terms vanish). -/
theorem skp_L_mono (j k : ℕ) :
    skpL (X ^ j * (1 - X) ^ k) =
      C ((j : ℝ) ^ 2) * (X ^ (j - 1) * (1 - X) ^ (k + 1)) +
        C ((k : ℝ) ^ 2) * (X ^ (j + 1) * (1 - X) ^ (k - 1)) -
          C (2 * (j : ℝ) * k + j + k) * (X ^ j * (1 - X) ^ k) := by
  unfold skpL
  rcases j with _ | a <;> rcases k with _ | b
  · simp
  · -- `j = 0`
    have e : ((X : ℝ[X]) - X ^ 2) * derivative (X ^ 0 * (1 - X) ^ (b + 1)) =
        -(C ((b : ℝ) + 1) * (X ^ (0 + 1) * (1 - X) ^ (b + 1))) := by
      rw [pow_zero, one_mul, skp_deriv_one_sub_pow_succ]; ring
    rw [e, derivative_neg, derivative_C_mul]
    have e2 : derivative (X ^ (0 + 1) * (1 - X) ^ (b + 1) : ℝ[X]) =
        C ((0 : ℝ) + 1) * (X ^ 0 * (1 - X) ^ (b + 1)) -
          C ((b : ℝ) + 1) * (X ^ (0 + 1) * (1 - X) ^ b) := by
      simpa using skp_deriv_mono 0 b
    rw [e2]
    simp only [Nat.cast_zero, zero_add, pow_zero, one_mul, pow_one, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      map_zero, zero_mul, mul_zero, map_add, map_pow, map_one, map_natCast]
    ring
  · -- `k = 0`
    have e : ((X : ℝ[X]) - X ^ 2) * derivative (X ^ (a + 1) * (1 - X) ^ 0) =
        C ((a : ℝ) + 1) * (X ^ (a + 1) * (1 - X) ^ (0 + 1)) := by
      rw [pow_zero, mul_one, skp_deriv_X_pow_succ]; ring
    rw [e, derivative_C_mul]
    have e2 : derivative (X ^ (a + 1) * (1 - X) ^ (0 + 1) : ℝ[X]) =
        C ((a : ℝ) + 1) * (X ^ a * (1 - X) ^ (0 + 1)) -
          C ((0 : ℝ) + 1) * (X ^ (a + 1) * (1 - X) ^ 0) := by
      simpa using skp_deriv_mono a 0
    rw [e2]
    simp only [Nat.cast_zero, zero_add, pow_zero, mul_one, pow_one, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      map_zero, zero_mul, mul_zero, map_add, map_pow, map_one, map_natCast, add_zero]
    ring
  · -- `j, k ≥ 1`
    have e : ((X : ℝ[X]) - X ^ 2) * derivative (X ^ (a + 1) * (1 - X) ^ (b + 1)) =
        C ((a : ℝ) + 1) * (X ^ (a + 1) * (1 - X) ^ ((b + 1) + 1)) -
          C ((b : ℝ) + 1) * (X ^ ((a + 1) + 1) * (1 - X) ^ (b + 1)) := by
      rw [skp_deriv_mono]; ring
    rw [e, derivative_sub, derivative_C_mul, derivative_C_mul, skp_deriv_mono,
      skp_deriv_mono]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, C_add, C_mul, C_1, C_ofNat,
      C_pow]
    ring

/-- The Euler step on a Bernstein monomial stays in the cone for small `s ≥ 0`. -/
theorem skp_cone_T_bern {N j : ℕ} (hj : j ≤ N) {s : ℝ} (hs : 0 ≤ s)
    (hsN : s * (2 * ((N : ℝ) + 1) ^ 2) ≤ 1) : SkpCone N (skpT s (skpBern N j)) := by
  have hL := skp_L_mono j (N - j)
  have hexp : skpT s (skpBern N j) =
      C (1 - s * (2 * (j : ℝ) * (N - j : ℕ) + j + (N - j : ℕ))) * skpBern N j +
        C (s * (j : ℝ) ^ 2) * (X ^ (j - 1) * (1 - X) ^ (N - j + 1)) +
          C (s * ((N - j : ℕ) : ℝ) ^ 2) * (X ^ (j + 1) * (1 - X) ^ (N - j - 1)) := by
    rw [skpT, skpBern, hL]
    simp only [C_sub, C_1, C_mul]
    ring
  rw [hexp]
  refine skp_cone_add (skp_cone_add (skp_cone_smul ?_ (skp_cone_gen hj)) ?_) ?_
  · have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
    have hk : ((N - j : ℕ) : ℝ) = N - j := by push_cast [Nat.cast_sub hj]; ring
    rw [hk]
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hd : 2 * (j : ℝ) * (N - j) + j + (N - j) ≤ 2 * ((N : ℝ) + 1) ^ 2 := by
      nlinarith
    have hd0 : 0 ≤ 2 * (j : ℝ) * (N - j) + j + (N - j) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd hs]
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simpa using skp_cone_zero N
    · have hb : X ^ (j - 1) * (1 - X) ^ (N - j + 1) = skpBern N (j - 1) := by
        rw [skpBern, show N - (j - 1) = N - j + 1 by omega]
      rw [hb]
      exact skp_cone_smul (by positivity) (skp_cone_gen (by omega))
  · rcases Nat.eq_or_lt_of_le hj with h0 | h0
    · subst h0; simpa using skp_cone_zero j
    · have hb : X ^ (j + 1) * (1 - X) ^ (N - j - 1) = skpBern N (j + 1) := by
        rw [skpBern, show N - (j + 1) = N - j - 1 by omega]
      rw [hb]
      exact skp_cone_smul (by positivity) (skp_cone_gen (by omega))

/-- **Cone invariance of the Euler step.** -/
theorem skp_cone_T {N : ℕ} {p : ℝ[X]} (hp : SkpCone N p) {s : ℝ} (hs : 0 ≤ s)
    (hsN : s * (2 * ((N : ℝ) + 1) ^ 2) ≤ 1) : SkpCone N (skpT s p) := by
  obtain ⟨c, hc, rfl⟩ := hp
  rw [skp_T_sum]
  refine skp_cone_sum _ _ fun j hj => ?_
  rw [skp_T_C_mul]
  exact skp_cone_smul (hc j)
    (skp_cone_T_bern (by have := Finset.mem_range.1 hj; omega) hs hsN)

theorem skp_cone_T_iterate {N : ℕ} {p : ℝ[X]} (hp : SkpCone N p) {s : ℝ} (hs : 0 ≤ s)
    (hsN : s * (2 * ((N : ℝ) + 1) ^ 2) ≤ 1) (i : ℕ) : SkpCone N ((skpT s)^[i] p) := by
  induction i with
  | zero => exact hp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact skp_cone_T ih hs hsN

/-- **The Euler step is diagonal on the Legendre basis.** -/
theorem skp_T_iterate_leg (s : ℝ) (N : ℕ) (β : ℕ → ℝ) (i : ℕ) :
    (skpT s)^[i] (∑ m ∈ Finset.range (N + 1), C (β m) * skLeg m) =
      ∑ m ∈ Finset.range (N + 1),
        C (β m * (1 - s * ((m : ℝ) * (m + 1))) ^ i) * skLeg m := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, skp_T_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [skp_T_C_mul, skpT, skp_L_leg]
    simp only [C_mul, C_pow, C_sub, C_1, pow_succ]
    ring

end BlockBand.Diffusion
