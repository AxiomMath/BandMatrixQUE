module

public import BlockBand.Counting.CircularGaussianMoments
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integration

/-!
# Gaussian diagonal quadratic moments

The first and second Wick identities for diagonal quadratic forms `∑ᵢ aᵢ |gᵢ|²` of a
standard circular Gaussian vector, with arbitrary real diagonal coefficients.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Counting
open MeasureTheory ProbabilityTheory

/-- Finite independent circular product law. -/
def circularVectorLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ × ℝ) :=
  Measure.pi (fun _ => standardCircularGaussian)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw
  infer_instance

/-- Squared modulus of one standard circular coordinate. -/
def circularSquare (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + z.2 ^ 2

theorem integrable_circularSquare_eval {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun z : ι → ℝ × ℝ => circularSquare (z i)) (circularVectorLaw ι) :=
  integrable_comp_eval integrable_circular_normSq

theorem integral_circularSquare_eval {ι : Type*} [Fintype ι] (i : ι) :
    (∫ z : ι → ℝ × ℝ, circularSquare (z i) ∂circularVectorLaw ι) = 1 := by
  rw [circularVectorLaw, integral_comp_eval (by unfold circularSquare; fun_prop)]
  exact integral_circular_normSq

theorem circularSquare_independent {ι : Type*} [Fintype ι] (i j : ι) (h : i ≠ j) :
    IndepFun (fun z : ι → ℝ × ℝ => circularSquare (z i))
      (fun z : ι → ℝ × ℝ => circularSquare (z j)) (circularVectorLaw ι) := by
  have hi : iIndepFun (fun i (z : ι → ℝ × ℝ) => circularSquare (z i))
      (circularVectorLaw ι) := iIndepFun_pi (fun _ => by unfold circularSquare; fun_prop)
  exact hi.indepFun h

theorem integrable_circularSquare_mul {ι : Type*} [Fintype ι] (i j : ι) :
    Integrable (fun z : ι → ℝ × ℝ => circularSquare (z i) * circularSquare (z j))
      (circularVectorLaw ι) := by
  by_cases h : i = j
  · subst j
    simpa [circularSquare, circularVectorLaw, pow_two] using
      (integrable_comp_eval (μ := fun _ : ι => standardCircularGaussian)
        integrable_circular_normSq_sq (i := i))
  · exact (circularSquare_independent i j h).integrable_mul
      (integrable_circularSquare_eval i) (integrable_circularSquare_eval j)

/-- Fourth contraction for diagonal entries, including repeated indices. -/
theorem integral_circularSquare_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (∫ z : ι → ℝ × ℝ, circularSquare (z i) * circularSquare (z j)
      ∂circularVectorLaw ι) = 1 + if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp_rw [← pow_two]
    rw [circularVectorLaw, integral_comp_eval
      (μ := fun _ : ι => standardCircularGaussian) (i := i)
      (f := fun z : ℝ × ℝ => circularSquare z ^ 2)
      (show AEStronglyMeasurable (fun z : ℝ × ℝ => circularSquare z ^ 2)
        standardCircularGaussian from by unfold circularSquare; fun_prop)]
    convert integral_circular_normSq_sq using 1 <;> norm_num [circularSquare]
  · rw [(circularSquare_independent i j h).integral_fun_mul_eq_mul_integral
      (integrable_circularSquare_eval i).aestronglyMeasurable
      (integrable_circularSquare_eval j).aestronglyMeasurable,
      integral_circularSquare_eval, integral_circularSquare_eval]
    simp [h]

/-- Diagonal quadratic form for arbitrary real diagonal entries. -/
def diagonalQuadratic {ι : Type*} [Fintype ι] (a : ι → ℝ) (z : ι → ℝ × ℝ) : ℝ :=
  ∑ i, a i * circularSquare (z i)

theorem integrable_diagonalQuadratic {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Integrable (diagonalQuadratic a) (circularVectorLaw ι) := by
  classical
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_circularSquare_eval i).const_mul (a i))

/-- First Wick identity for arbitrary real diagonal matrices. -/
theorem integral_diagonalQuadratic {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∫ z, diagonalQuadratic a z ∂circularVectorLaw ι) = ∑ i, a i := by
  classical
  unfold diagonalQuadratic
  rw [integral_finsetSum _ (fun i _ => (integrable_circularSquare_eval i).const_mul (a i))]
  simp_rw [integral_const_mul, integral_circularSquare_eval, mul_one]

/-- Second Wick identity for arbitrary real diagonal matrices.
The correction is `Tr (A B) = ∑ᵢ aᵢ bᵢ`. -/
theorem integral_diagonalQuadratic_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) :
    (∫ z, diagonalQuadratic a z * diagonalQuadratic b z ∂circularVectorLaw ι) =
      (∑ i, a i) * (∑ i, b i) + ∑ i, a i * b i := by
  simp only [diagonalQuadratic]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have he (i j : ι) (z : ι → ℝ × ℝ) :
      a i * circularSquare (z i) * (b j * circularSquare (z j)) =
        (a i * b j) * (circularSquare (z i) * circularSquare (z j)) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (integrable_circularSquare_mul i j).const_mul (a i * b j)))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (integrable_circularSquare_mul _ j).const_mul (a _ * b j)),
    integral_const_mul, integral_circularSquare_mul, mul_add, Finset.sum_add_distrib]
  simp

end BlockBand.Counting
