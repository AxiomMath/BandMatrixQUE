module

public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreDefs
public import BlockBand.Endpoints.Response.TaggedConvexOrderGBM

/-!
# The backward polynomial of geometric Brownian motion

For a polynomial `φ = Σ_m φ_m X^m`, the backward polynomial
`tcc_backward D₀ t φ = Σ_m φ_m e^{(D₀/2)m(m-1)t} X^m` satisfies
`E φ(d e^{√D₀B_t - D₀t/2}) = u(t, d)` for `t ≥ 0` (`tcc_gbmExpect_eq_eval_backward`), and it stays
convex on `[0,∞)` when `φ` is (`tcc_backward_convex`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset
open scoped ENNReal NNReal

/-- The exponent `λ_m = (D₀/2) m(m-1)`. -/
def tcc_lam (D0 : ℝ) (m : ℕ) : ℝ := D0 / 2 * ((m : ℝ) * ((m : ℝ) - 1))

theorem tcc_lam_nonneg {D0 : ℝ} (hD0 : 0 ≤ D0) (m : ℕ) : 0 ≤ tcc_lam D0 m :=
  mul_nonneg (by positivity) (tco_ii_nonneg m)

theorem tcc_backward_coeff (D0 t : ℝ) (φ : ℝ[X]) (m : ℕ) :
    (tcc_backward D0 t φ).coeff m = φ.coeff m * Real.exp (tcc_lam D0 m * t) := by
  unfold tcc_backward tcc_lam
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (range (φ.natDegree + 1)) m]
  split_ifs with h
  · rfl
  · have : φ.natDegree < m := by simp at h; omega
    rw [coeff_eq_zero_of_natDegree_lt this, zero_mul]

theorem tcc_backward_natDegree_le (D0 t : ℝ) (φ : ℝ[X]) :
    (tcc_backward D0 t φ).natDegree ≤ φ.natDegree := by
  unfold tcc_backward
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hi; omega)

theorem tcc_backward_zero (D0 : ℝ) (φ : ℝ[X]) : tcc_backward D0 0 φ = φ := by
  ext m
  rw [tcc_backward_coeff, mul_zero, Real.exp_zero, mul_one]

theorem tcc_gen_coeff (D0 : ℝ) (ψ : ℝ[X]) (m : ℕ) :
    (tcc_gen D0 ψ).coeff m = tcc_lam D0 m * ψ.coeff m := by
  unfold tcc_gen tcc_lam
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  rcases m with _ | _ | m
  · simp
  · simp
  · split_ifs with h2
    · rw [show m + 2 - 2 = m by omega, coeff_derivative, coeff_derivative]
      push_cast
      ring
    · omega

theorem tcc_gen_natDegree_le (D0 : ℝ) (ψ : ℝ[X]) :
    (tcc_gen D0 ψ).natDegree ≤ ψ.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [tcc_gen_coeff, coeff_eq_zero_of_natDegree_lt hN, mul_zero]

/-- Evaluation as a sum over `range (M + 1)` for `deg ψ ≤ M`. -/
theorem tcc_eval_eq_sum {ψ : ℝ[X]} {M : ℕ} (hM : ψ.natDegree ≤ M) (x : ℝ) :
    ψ.eval x = ∑ m ∈ range (M + 1), ψ.coeff m * x ^ m :=
  eval_eq_sum_range' (by omega) x

theorem tcc_gbm_term (D0 d t x : ℝ) (m : ℕ) :
    (d * Real.exp (Real.sqrt D0 * x - D0 * t / 2)) ^ m =
      d ^ m * Real.exp (-(m * (D0 * t / 2))) * Real.exp ((m * Real.sqrt D0) * x) := by
  rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem tcc_integrable_gbm (D0 d t : ℝ) (φ : ℝ[X]) :
    Integrable (fun x => φ.eval (d * Real.exp (Real.sqrt D0 * x - D0 * t / 2)))
      (gaussianReal 0 t.toNNReal) := by
  simp_rw [tcc_eval_eq_sum (le_refl φ.natDegree), tcc_gbm_term]
  refine integrable_finsetSum _ fun m _ => ?_
  exact ((integrable_exp_mul_gaussianReal _).const_mul _).const_mul _

/-- The value of the backward polynomial: for `t ≥ 0`,
`E φ(d e^{√D₀B_t - D₀t/2}) = u(t, d) = Σ_m φ_m e^{(D₀/2)m(m-1)t} d^m`. -/
theorem tcc_gbmExpect_eq_eval_backward (D0 d t : ℝ) (hD0 : 0 ≤ D0) (ht : 0 ≤ t) (φ : ℝ[X]) :
    tco_gbmExpect D0 d t φ = (tcc_backward D0 t φ).eval d := by
  unfold tco_gbmExpect
  rw [tcc_eval_eq_sum (tcc_backward_natDegree_le D0 t φ) d]
  simp_rw [tcc_eval_eq_sum (le_refl φ.natDegree), tcc_gbm_term]
  rw [integral_finsetSum _ fun m _ =>
    ((integrable_exp_mul_gaussianReal _).const_mul _).const_mul _]
  refine sum_congr rfl fun m _ => ?_
  rw [tcc_backward_coeff, integral_const_mul, integral_const_mul,
    tco_integral_exp_gaussian t _ ht, mul_pow, Real.sq_sqrt hD0]
  have e : Real.exp (-(m * (D0 * t / 2))) * Real.exp (t * ((m : ℝ) ^ 2 * D0) / 2) =
      Real.exp (tcc_lam D0 m * t) := by
    rw [← Real.exp_add]; unfold tcc_lam; congr 1; ring
  rw [← e]
  ring

/-- The backward polynomial stays convex: for `φ` convex on `[0,∞)` and `t ≥ 0`, `x ↦ u(t, x)` is
convex on `[0,∞)`. -/
theorem tcc_backward_convex (D0 t : ℝ) (hD0 : 0 ≤ D0) (ht : 0 ≤ t) {φ : ℝ[X]}
    (hφ : ConvexOn ℝ (Set.Ici 0) (fun x => φ.eval x)) :
    ConvexOn ℝ (Set.Ici 0) (fun x => (tcc_backward D0 t φ).eval x) := by
  refine ⟨convex_Ici 0, fun x hx y hy a c ha hc hac => ?_⟩
  simp only [smul_eq_mul]
  rw [← tcc_gbmExpect_eq_eval_backward D0 _ t hD0 ht, ← tcc_gbmExpect_eq_eval_backward D0 _ t hD0 ht,
    ← tcc_gbmExpect_eq_eval_backward D0 _ t hD0 ht]
  unfold tco_gbmExpect
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((tcc_integrable_gbm D0 x t φ).const_mul a) ((tcc_integrable_gbm D0 y t φ).const_mul c)]
  refine integral_mono (tcc_integrable_gbm D0 _ t φ)
    (((tcc_integrable_gbm D0 x t φ).const_mul a).add ((tcc_integrable_gbm D0 y t φ).const_mul c))
    fun z => ?_
  set g := Real.exp (Real.sqrt D0 * z - D0 * t / 2)
  have hg : 0 ≤ g := (Real.exp_pos _).le
  have hx' : x * g ∈ Set.Ici (0 : ℝ) := mul_nonneg (Set.mem_Ici.1 hx) hg
  have hy' : y * g ∈ Set.Ici (0 : ℝ) := mul_nonneg (Set.mem_Ici.1 hy) hg
  have h := hφ.2 hx' hy' ha hc hac
  simp only [smul_eq_mul] at h
  have e : (a * x + c * y) * g = a * (x * g) + c * (y * g) := by ring
  simp only
  rw [e]
  exact h

end BlockBand.Endpoints
