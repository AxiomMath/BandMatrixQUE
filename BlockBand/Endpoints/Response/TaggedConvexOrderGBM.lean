module

public import BlockBand.Endpoints.Response.TaggedConvexOrderDefs
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Centered moments of geometric Brownian motion

* `tco_gbmExpect_centered`: for `t ≥ 0`, `D₀ ≥ 0`,
  `E(dG_t - d)^{2p} = d^{2p} Σ_{i ≤ 2p} (-1)^{2p-i} C(2p,i) e^{D₀ i(i-1)t/2}` (Gaussian moment
  generating function `ProbabilityTheory.mgf_id_gaussianReal`).
* `tco_gbmCentered_le`: `|Σ_{i ≤ 2p} (-1)^{2p-i} C(2p,i) e^{c i(i-1)t}| ≤ K t^p` on `[0, T₀]`:
  the `2p`-th finite difference kills every polynomial of degree `< 2p`
  (`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`), so the Taylor terms of order `< p` of the
  exponentials cancel, and the remainder of order `p` is `≤ x^p e^x/p!`.
* `tco_gbmExpect_centered_le`: the bound `≤ K t^p` for `t ∈ [0,T₀]`, with `K = K_{p,T₀,D₀,d}`.
* `tco_gbmExpect_X`: `E dG_t = d` (`φ = X`).
No hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset
open scoped ENNReal NNReal Nat

/-!
## The exponential remainder
-/

/-- `0 ≤ e^x - Σ_{m<p} x^m/m! ≤ x^p e^x/p!` for `x ≥ 0`. -/
theorem tco_exp_remainder {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    0 ≤ Real.exp x - ∑ m ∈ range p, x ^ m / m ! ∧
      Real.exp x - ∑ m ∈ range p, x ^ m / m ! ≤ x ^ p * Real.exp x / p ! := by
  have hs : HasSum (fun n : ℕ => x ^ n / n !) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have ht : HasSum (fun n : ℕ => x ^ (n + p) / (n + p) !)
      (Real.exp x - ∑ m ∈ range p, x ^ m / m !) := (hasSum_nat_add_iff' p).mpr hs
  refine ⟨ht.nonneg fun n => by positivity, ?_⟩
  have hc : HasSum (fun n : ℕ => x ^ p / p ! * (x ^ n / n !)) (x ^ p / p ! * Real.exp x) :=
    hs.mul_left _
  have hle := hasSum_le (fun n => ?_) ht hc
  · calc Real.exp x - ∑ m ∈ range p, x ^ m / m ! ≤ x ^ p / p ! * Real.exp x := hle
      _ = x ^ p * Real.exp x / p ! := by ring
  · have hf : ((n ! * p ! : ℕ) : ℝ) ≤ ((n + p) ! : ℕ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add n p)
    push_cast at hf
    rw [pow_add, div_mul_div_comm, mul_comm (x ^ p) (x ^ n), mul_comm (p ! : ℝ) (n ! : ℝ)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf

/-!
## Alternating binomial sums of polynomials
-/

/-- `Σ_{i ≤ n} (-1)^{n-i} C(n,i) (i(i-1))^m = 0` for `2m < n`. -/
theorem tco_alt_sum_eq_zero {n m : ℕ} (h : 2 * m < n) :
    ∑ i ∈ range (n + 1), ((-1 : ℝ) ^ (n - i) * n.choose i) *
      (((i : ℝ) * ((i : ℝ) - 1)) ^ m) = 0 := by
  set P : ℝ[X] := (X * (X - 1)) ^ m
  have hdeg : P.natDegree < n := by
    have h1 : (X * (X - 1) : ℝ[X]).natDegree ≤ 2 := by
      refine (natDegree_mul_le).trans ?_
      have := natDegree_X_sub_C_le (R := ℝ) 1
      simp only [map_one] at this
      have hX : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
      omega
    have h2 : P.natDegree ≤ m * 2 := (natDegree_pow_le).trans (Nat.mul_le_mul_left m h1)
    omega
  have hz := congr_fun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift] at hz
  simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one] at hz
  rw [← hz]
  refine sum_congr rfl fun i _ => ?_
  simp only [P, eval_pow, eval_mul, eval_X, eval_sub, eval_one, zsmul_eq_mul]
  push_cast
  ring

/-!
## The centered moment of geometric Brownian motion
-/

/-- `Σ_{i ≤ 2p} (-1)^{2p-i} C(2p,i) e^{(D₀/2) i(i-1) t}`, the centered `2p`-th moment of
`e^{√D₀B_t - D₀t/2}`. -/
def tco_gbmCentered (D0 t : ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ range (2 * p + 1), ((-1 : ℝ) ^ (2 * p - i) * (2 * p).choose i) *
    Real.exp (D0 / 2 * ((i : ℝ) * ((i : ℝ) - 1)) * t)

theorem tco_ii_nonneg (i : ℕ) : 0 ≤ (i : ℝ) * ((i : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    nlinarith

/-- **The centered moment is `O(t^p)`** uniformly on `[0, T₀]`. -/
theorem tco_gbmCentered_le (D0 T₀ : ℝ) (hD0 : 0 ≤ D0) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T₀ → |tco_gbmCentered D0 t p| ≤ K * t ^ p := by
  set n := 2 * p
  set μ : ℕ → ℝ := fun i => D0 / 2 * ((i : ℝ) * ((i : ℝ) - 1))
  have hμ : ∀ i, 0 ≤ μ i := fun i => mul_nonneg (by positivity) (tco_ii_nonneg i)
  set K : ℝ := ∑ i ∈ range (n + 1), (n.choose i : ℝ) * μ i ^ p * Real.exp (μ i * T₀) / (p ! : ℝ)
  refine ⟨K, sum_nonneg fun i _ => by have := hμ i; positivity, ?_⟩
  intro t ht htT
  set R : ℕ → ℝ := fun i => Real.exp (μ i * t) - ∑ m ∈ range p, (μ i * t) ^ m / (m ! : ℝ)
  have hR : ∀ i, 0 ≤ R i ∧ R i ≤ (μ i * t) ^ p * Real.exp (μ i * t) / p ! := fun i =>
    tco_exp_remainder (mul_nonneg (hμ i) ht) p
  set a : ℕ → ℝ := fun i => (-1 : ℝ) ^ (n - i) * n.choose i
  have hsplit : tco_gbmCentered D0 t p = ∑ i ∈ range (n + 1), a i * R i := by
    have hpoly : ∑ i ∈ range (n + 1), a i * ∑ m ∈ range p, (μ i * t) ^ m / m ! = 0 := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_eq_zero fun m hm => ?_
      have hm' : 2 * m < n := by have := mem_range.1 hm; omega
      have e : ∀ i, a i * ((μ i * t) ^ m / m !) =
          ((D0 / 2 * t) ^ m / m !) *
            (((-1 : ℝ) ^ (n - i) * n.choose i) * (((i : ℝ) * ((i : ℝ) - 1)) ^ m)) := by
        intro i; simp only [a, μ]; rw [mul_pow, mul_pow, mul_pow]; ring
      simp_rw [e]
      rw [← mul_sum, tco_alt_sum_eq_zero hm', mul_zero]
    unfold tco_gbmCentered
    have : ∀ i, a i * R i = a i * Real.exp (μ i * t) -
        a i * ∑ m ∈ range p, (μ i * t) ^ m / m ! := fun i => by simp only [R]; ring
    simp_rw [this]
    rw [sum_sub_distrib, hpoly, sub_zero]
  rw [hsplit]
  calc |∑ i ∈ range (n + 1), a i * R i| ≤ ∑ i ∈ range (n + 1), |a i * R i| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * ((μ i * t) ^ p * Real.exp (μ i * T₀) / p !) := by
        refine sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hR i).1]
        have ha : |a i| = n.choose i := by
          simp only [a, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
        rw [ha]
        refine mul_le_mul_of_nonneg_left ((hR i).2.trans ?_) (by positivity)
        have : Real.exp (μ i * t) ≤ Real.exp (μ i * T₀) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT (hμ i))
        have h0 : 0 ≤ (μ i * t) ^ p := pow_nonneg (mul_nonneg (hμ i) ht) p
        gcongr
    _ = K * t ^ p := by
        simp only [K, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_pow]; ring

/-!
## The Gaussian expectation
-/

theorem tco_integral_exp_gaussian (t c : ℝ) (ht : 0 ≤ t) :
    ∫ x, Real.exp (c * x) ∂gaussianReal 0 t.toNNReal = Real.exp (t * c ^ 2 / 2) := by
  have h := congr_fun (mgf_id_gaussianReal (μ := 0) (v := t.toNNReal)) c
  simp only [mgf, id_eq, zero_mul, zero_add, Real.coe_toNNReal _ ht] at h
  exact h

/-- **The centered `2p`-th moment of `dG_t`**, `G_t = e^{√D₀B_t - D₀t/2}`. -/
theorem tco_gbmExpect_centered (D0 d t : ℝ) (hD0 : 0 ≤ D0) (ht : 0 ≤ t) (p : ℕ) :
    tco_gbmExpect D0 d t ((X - C d) ^ (2 * p)) = d ^ (2 * p) * tco_gbmCentered D0 t p := by
  unfold tco_gbmExpect tco_gbmCentered
  set n := 2 * p
  have hpt : ∀ x : ℝ, ((X - C d) ^ n).eval (d * Real.exp (Real.sqrt D0 * x - D0 * t / 2)) =
      d ^ n * ∑ i ∈ range (n + 1), ((-1 : ℝ) ^ (n - i) * n.choose i) *
        (Real.exp (-(i * (D0 * t / 2))) * Real.exp ((i * Real.sqrt D0) * x)) := by
    intro x
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    have e1 : d * Real.exp (Real.sqrt D0 * x - D0 * t / 2) - d =
        d * (Real.exp (Real.sqrt D0 * x - D0 * t / 2) + (-1)) := by ring
    rw [e1, mul_pow, add_pow]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    have e2 : (i : ℝ) * (Real.sqrt D0 * x - D0 * t / 2) =
        -(i * (D0 * t / 2)) + (i * Real.sqrt D0) * x := by ring
    rw [e2]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_const_mul, tco_integral_exp_gaussian t _ ht,
      ← Real.exp_add]
    congr 2
    rw [mul_pow, Real.sq_sqrt hD0]
    ring
  · intro i _
    exact ((integrable_exp_mul_gaussianReal _).const_mul _).const_mul _

/-- **The centered moment bound** (Step 6): `E(dG_t - d)^{2p} ≤ K t^p` for
`t ∈ [0, T₀]`, with `K = K_{p,T₀,D₀,d}`. -/
theorem tco_gbmExpect_centered_le (D0 d T₀ : ℝ) (hD0 : 0 ≤ D0) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T₀ →
      tco_gbmExpect D0 d t ((X - C d) ^ (2 * p)) ≤ K * t ^ p := by
  obtain ⟨K, hK, hb⟩ := tco_gbmCentered_le D0 T₀ hD0 p
  refine ⟨d ^ (2 * p) * K, by rw [pow_mul]; positivity, fun t ht htT => ?_⟩
  rw [tco_gbmExpect_centered D0 d t hD0 ht p, mul_assoc]
  have hd : 0 ≤ d ^ (2 * p) := by rw [pow_mul]; positivity
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb t ht htT)) hd

/-- **The mean of `dG_t` is `d`** (Step 4). -/
theorem tco_gbmExpect_X (D0 d t : ℝ) (hD0 : 0 ≤ D0) (ht : 0 ≤ t) :
    tco_gbmExpect D0 d t X = d := by
  unfold tco_gbmExpect
  simp only [eval_X]
  have e : ∀ x : ℝ, d * Real.exp (Real.sqrt D0 * x - D0 * t / 2) =
      d * Real.exp (-(D0 * t / 2)) * Real.exp (Real.sqrt D0 * x) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [e]
  rw [integral_const_mul, tco_integral_exp_gaussian t _ ht, mul_assoc, ← Real.exp_add,
    Real.sq_sqrt hD0]
  rw [show -(D0 * t / 2) + t * D0 / 2 = 0 by ring, Real.exp_zero, mul_one]

end BlockBand.Endpoints
