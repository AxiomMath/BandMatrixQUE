module

public import BlockBand.Critical.Herglotz.GaussianMoments

/-!
# The Gaussian quadratic mark `|v^* g|²`

The quadratic form of the canonical series, `v^* 𝖢_r(z) v = π⁻¹ Σ_j |v^* g_j|² / (x_j - z)`, is a
linear statistic with mark weight `quadMark v g = |Σ_i conj(v_i) g_i|²`.

Law: `γ = circularVectorLaw (Fin r)` (independent `N(0, 1/2)` real and imaginary parts).

* `memLp_circularVectorLaw_apply` — every coordinate `g_a` is in `L^p(γ)`, `p < ∞`.
* `continuous_quadMark`, `quadMark_nonneg`.
* `integrable_quadMark_sq` — `quadMark v ∈ L²(γ)` (Gaussian fourth moments).
* `integral_quadMark` — `∫ |v^* g|² dγ = Σ_i |v_i|²` (from `E g gᴴ = I`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate NNReal ENNReal

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

/-- Every coordinate of the standard circular Gaussian vector is in `L^p`, `p < ∞`. -/
theorem memLp_circularVectorLaw_apply {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : p ≠ ∞)
    (a : ι) : MemLp (fun g : ι → ℂ => g a) p (circularVectorLaw ι) := by
  unfold circularVectorLaw
  set μ := Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)
  have hφ : Measurable (fun (r : ι × Fin 2 → ℝ) (c : ι) =>
      (r (c, 0) : ℂ) + (r (c, 1) : ℂ) * Complex.I) := by fun_prop
  rw [memLp_map_measure_iff (measurable_pi_apply a).aestronglyMeasurable hφ.aemeasurable]
  have hev (k : ι × Fin 2) := measurePreserving_eval (fun _ : ι × Fin 2 =>
    gaussianReal 0 (1 / 2 : ℝ≥0)) k
  have hL (k : ι × Fin 2) : MemLp (fun r : ι × Fin 2 → ℝ => r k) p μ := by
    exact (memLp_id_gaussianReal' (μ := 0) (v := (1 / 2 : ℝ≥0)) p hp).comp_measurePreserving
      (hev k)
  have h0 := (hL (a, 0)).ofReal (K := ℂ)
  have h1 := ((hL (a, 1)).ofReal (K := ℂ)).mul_const Complex.I
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun r => ?_) (h0.add h1)
  simp

/-- The quadratic mark `|v^* g|² = |Σ_i conj(v_i) g_i|²`. -/
def quadMark {r : ℕ} (v g : Fin r → ℂ) : ℝ := ‖∑ i, star (v i) * g i‖ ^ 2

theorem quadMark_nonneg {r : ℕ} (v g : Fin r → ℂ) : 0 ≤ quadMark v g := sq_nonneg _

theorem continuous_quadMark {r : ℕ} (v : Fin r → ℂ) : Continuous (quadMark v) := by
  unfold quadMark
  fun_prop

/-- The linear form `g ↦ v^* g` is in `L^p(γ)`. -/
theorem memLp_circularVectorLaw_linear {r : ℕ} {p : ℝ≥0∞} (hp : p ≠ ∞) (v : Fin r → ℂ) :
    MemLp (fun g : Fin r → ℂ => ∑ i, star (v i) * g i) p (circularVectorLaw (Fin r)) := by
  have h := memLp_finsetSum' (μ := circularVectorLaw (Fin r)) (p := p) Finset.univ
    (f := fun i (g : Fin r → ℂ) => star (v i) * g i)
    (fun i _ => (memLp_circularVectorLaw_apply hp i).const_mul (star (v i)))
  convert h using 1
  funext g
  simp

/-- `|v^* g|² ∈ L²(γ)`: `∫ |v^* g|⁴ dγ < ∞`. -/
theorem integrable_quadMark_sq {r : ℕ} (v : Fin r → ℂ) :
    Integrable (fun g => quadMark v g ^ 2) (circularVectorLaw (Fin r)) := by
  have h := (memLp_circularVectorLaw_linear (p := ((4 : ℕ) : ℝ≥0∞)) (by simp) v).integrable_norm_pow (p := 4)
  have h' := h (by norm_num)
  convert h' using 1
  funext g
  unfold quadMark
  ring

theorem integrable_quadMark {r : ℕ} (v : Fin r → ℂ) :
    Integrable (quadMark v) (circularVectorLaw (Fin r)) := by
  have h := (memLp_circularVectorLaw_linear (p := ((2 : ℕ) : ℝ≥0∞)) (by simp) v).integrable_norm_pow (p := 2)
  exact h (by norm_num)

/-- **Mean of the quadratic mark**: `∫ |v^* g|² dγ = Σ_i |v_i|²` (`E g gᴴ = I`). -/
theorem integral_quadMark {r : ℕ} (v : Fin r → ℂ) :
    ∫ g, quadMark v g ∂circularVectorLaw (Fin r) = ∑ i, ‖v i‖ ^ 2 := by
  set γ := circularVectorLaw (Fin r)
  have hi (a b : Fin r) : Integrable (fun g : Fin r → ℂ => g a * conj (g b)) γ := by
    have h2 := (memLp_circularVectorLaw_apply (p := 2) (by simp) a).integrable_mul
      ((memLp_circularVectorLaw_apply (p := 2) (by simp) b).star)
    convert h2 using 1
    funext g
    simp
  have hexp (g : Fin r → ℂ) : (quadMark v g : ℂ) =
      ∑ a, ∑ b, star (v a) * v b * (g a * conj (g b)) := by
    unfold quadMark
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
    ring
  have hc : ((∫ g, quadMark v g ∂γ : ℝ) : ℂ) = ∑ a, ∑ b, star (v a) * v b *
      (if a = b then 1 else 0) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hi a b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (hi a b).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_circularVectorLaw_mul_conj]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hc
  have hc' : ((∫ g, quadMark v g ∂γ : ℝ) : ℂ) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hc]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj']
  exact_mod_cast hc'

end BlockBand.Critical.Herglotz
