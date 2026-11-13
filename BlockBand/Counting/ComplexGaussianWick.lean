module

public import BlockBand.Counting.CircularMonomials
public import BlockBand.Counting.DiagonalGaussianWick
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite circular Gaussian Wick identities

For a standard circular Gaussian vector `g` on a finite index set and deterministic complex
matrices `A`, `B`, this file proves the Wick identities `E[gᴴ A g] = Tr A` and
`E[(gᴴ A g)(gᴴ B g)] = Tr A Tr B + Tr (A B)`, together with the integrability of both
sides, from the four-index and two-index contraction formulas.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

/-- Standard circular vector on the finite product sample space. -/
def circularVector {ι : Type*} (z : ι → ℝ × ℝ) : ι → ℂ :=
  fun i => circularGaussianCoordinate (z i)

/-- Product of two conjugated and two plain coordinates expressed as scalar monomials. -/
def fourthConjugatePower {ι : Type*} [DecidableEq ι] (i k m : ι) : ℕ :=
  (if m = i then 1 else 0) + (if m = k then 1 else 0)

theorem fourthConjugatePower_le {ι : Type*} [DecidableEq ι] (i k m : ι) :
    fourthConjugatePower i k m ≤ 2 := by
  unfold fourthConjugatePower
  split_ifs <;> omega

/-- Pointwise factorization on the independent product space. -/
theorem circular_fourth_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) (z : ι → ℝ × ℝ) :
    (conj (circularVector z i) * circularVector z j) *
      (conj (circularVector z k) * circularVector z l) =
    ∏ m, conj (circularGaussianCoordinate (z m)) ^ fourthConjugatePower i k m *
      circularGaussianCoordinate (z m) ^ fourthConjugatePower j l m := by
  simp only [fourthConjugatePower, pow_add, Finset.prod_mul_distrib]
  have hp (f : ι → ℂ) (a : ι) :
      (∏ m, f m ^ (if m = a then 1 else 0)) = f a := by
    calc
      (∏ m, f m ^ (if m = a then 1 else 0)) =
          ∏ m, (if m = a then f m else 1) := by
        apply Finset.prod_congr rfl
        intro m _
        split_ifs <;> simp
      _ = f a := by simp
  rw [hp, hp, hp, hp]
  unfold circularVector
  ring

/-- All four-coordinate products are integrable under the circular law. -/
theorem integrable_circular_fourth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) :
    Integrable (fun z : ι → ℝ × ℝ =>
      (conj (circularVector z i) * circularVector z j) *
        (conj (circularVector z k) * circularVector z l)) (circularVectorLaw ι) := by
  simp_rw [circular_fourth_factorization]
  exact Integrable.fintype_prod (fun m => integrable_circular_monomial _ _
    (fourthConjugatePower_le i k m) (fourthConjugatePower_le j l m))

/-- Four-index Wick contraction derived from the scalar product measure. -/
theorem integral_circular_fourth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) :
    (∫ z : ι → ℝ × ℝ,
      (conj (circularVector z i) * circularVector z j) *
        (conj (circularVector z k) * circularVector z l) ∂circularVectorLaw ι) =
      (if i = j ∧ k = l then 1 else 0) + (if i = l ∧ k = j then 1 else 0) := by
  simp_rw [circular_fourth_factorization]
  rw [circularVectorLaw, integral_fintype_prod_eq_prod
    (μ := fun _ : ι => standardCircularGaussian)
    (fun m (w : ℝ × ℝ) => conj (circularGaussianCoordinate w) ^ fourthConjugatePower i k m *
      circularGaussianCoordinate w ^ fourthConjugatePower j l m)]
  simp_rw [integral_circular_monomial _ _ (fourthConjugatePower_le _ _ _)
    (fourthConjugatePower_le _ _ _)]
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      by_cases hik : i = k
      · subst k
        trans (∏ m : ι, if m = i then (2 : ℂ) else 1)
        · apply Finset.prod_congr rfl
          intro m _
          by_cases hm : m = i <;> simp [fourthConjugatePower, hm]
        · norm_num
      · have hf (m : ι) :
            (if fourthConjugatePower i k m = fourthConjugatePower i k m then
              (if fourthConjugatePower i k m = 2 then (2 : ℂ) else 1) else 0) = 1 := by
          by_cases hmi : m = i <;> by_cases hmk : m = k <;>
            simp_all [fourthConjugatePower]
        trans (∏ _ : ι, (1 : ℂ))
        · exact Finset.prod_congr rfl (fun m _ => hf m)
        · simp [hik, Ne.symm hik]
    · have hzero : (if fourthConjugatePower i k k = fourthConjugatePower i l k then
            (if fourthConjugatePower i k k = 2 then (2 : ℂ) else 1) else 0) = 0 := by
        by_cases hki : k = i <;> simp_all [fourthConjugatePower]
      rw [Finset.prod_eq_zero (Finset.mem_univ k) hzero]
      simp_all
  · by_cases hil : i = l
    · subst l
      by_cases hkj : k = j
      · subst k
        have hf (m : ι) :
            (if fourthConjugatePower i j m = fourthConjugatePower j i m then
              (if fourthConjugatePower i j m = 2 then (2 : ℂ) else 1) else 0) = 1 := by
          by_cases hmi : m = i <;> by_cases hmj : m = j <;>
            simp_all [fourthConjugatePower]
        trans (∏ _ : ι, (1 : ℂ))
        · exact Finset.prod_congr rfl (fun m _ => hf m)
        · simp [hij, Ne.symm hij]
      · have hzero : (if fourthConjugatePower i k j = fourthConjugatePower j i j then
            (if fourthConjugatePower i k j = 2 then (2 : ℂ) else 1) else 0) = 0 := by
          simp [fourthConjugatePower, Ne.symm hij, Ne.symm hkj]
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hzero]
        simp [hij, hkj]
    · have hzero : (if fourthConjugatePower i k i = fourthConjugatePower j l i then
            (if fourthConjugatePower i k i = 2 then (2 : ℂ) else 1) else 0) = 0 := by
        by_cases hik : i = k
        · subst k
          simp [fourthConjugatePower, hij, hil]
        · simp [fourthConjugatePower, hij, hil, hik]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
      simp [hij, hil]

/-- Pointwise second contraction factorization. -/
theorem circular_second_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (z : ι → ℝ × ℝ) :
    conj (circularVector z i) * circularVector z j =
      ∏ m, conj (circularGaussianCoordinate (z m)) ^ (if m = i then 1 else 0) *
        circularGaussianCoordinate (z m) ^ (if m = j then 1 else 0) := by
  simp only [Finset.prod_mul_distrib]
  have hp (f : ι → ℂ) (a : ι) :
      (∏ m, f m ^ (if m = a then 1 else 0)) = f a := by
    calc
      (∏ m, f m ^ (if m = a then 1 else 0)) =
          ∏ m, (if m = a then f m else 1) := by
        apply Finset.prod_congr rfl
        intro m _
        split_ifs <;> simp
      _ = f a := by simp
  rw [hp, hp]
  rfl

/-- Integrability of each second contraction. -/
theorem integrable_circular_second {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    Integrable (fun z : ι → ℝ × ℝ => conj (circularVector z i) * circularVector z j)
      (circularVectorLaw ι) := by
  simp_rw [circular_second_factorization]
  exact Integrable.fintype_prod (fun m => integrable_circular_monomial _ _
    (by split_ifs <;> omega) (by split_ifs <;> omega))

/-- Second contraction in the standard circular normalization. -/
theorem integral_circular_second {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (∫ z : ι → ℝ × ℝ, conj (circularVector z i) * circularVector z j
      ∂circularVectorLaw ι) = if i = j then 1 else 0 := by
  simp_rw [circular_second_factorization]
  rw [circularVectorLaw, integral_fintype_prod_eq_prod
    (μ := fun _ : ι => standardCircularGaussian)
    (fun m (w : ℝ × ℝ) => conj (circularGaussianCoordinate w) ^ (if m = i then 1 else 0) *
      circularGaussianCoordinate w ^ (if m = j then 1 else 0))]
  have hle (m a : ι) : (if m = a then 1 else 0 : ℕ) ≤ 2 := by
    split_ifs <;> omega
  simp_rw [integral_circular_monomial _ _ (hle _ i) (hle _ j)]
  by_cases h : i = j
  · subst j
    have hf (m : ι) :
        (if (if m = i then 1 else 0 : ℕ) = (if m = i then 1 else 0) then
          (if (if m = i then 1 else 0 : ℕ) = 2 then (2 : ℂ) else 1) else 0) = 1 := by
      by_cases hm : m = i <;> simp [hm]
    trans (∏ _ : ι, (1 : ℂ))
    · exact Finset.prod_congr rfl (fun m _ => hf m)
    · simp
  · rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])]
    simp [h]

/-- The deterministic quadratic form `gᴴ A g`, written entrywise.  This
orientation puts the deterministic coefficient first, which is convenient for
Bochner integration. -/
def complexQuadraticForm {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (g : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, A i j * (conj (g i) * g j)

/-- The second-moment contraction `E[conj(gᵢ) gⱼ] = δᵢⱼ` implies the first
Wick identity `E[gᴴ A g] = Tr A`.  Integrability is explicit rather
than hidden in an expectation notation. -/
theorem integral_complexQuadraticForm_eq_trace_of_contractions
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (g : Ω → ι → ℂ) (A : Matrix ι ι ℂ)
    (hint : ∀ i j, Integrable (fun ω => conj (g ω i) * g ω j) P)
    (hsecond : ∀ i j, ∫ ω, conj (g ω i) * g ω j ∂P = if i = j then 1 else 0) :
    ∫ ω, complexQuadraticForm A (g ω) ∂P = Matrix.trace A := by
  simp_rw [complexQuadraticForm]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (A i j)))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ =>
    (hint _ j).const_mul (A _ j)), integral_const_mul, hsecond]
  simp [Matrix.trace]

/-- The entrywise four-index expansion of
`(gᴴ A g) (gᴴ B g)`. -/
def complexQuadraticFormProduct {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (g : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (A i j * B k l) * ((conj (g i) * g j) * (conj (g k) * g l))

/-- The entrywise expansion really is the product of the two quadratic forms. -/
theorem complexQuadraticFormProduct_eq_mul {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) (g : ι → ℂ) :
    complexQuadraticFormProduct A B g =
      complexQuadraticForm A g * complexQuadraticForm B g := by
  simp only [complexQuadraticFormProduct, complexQuadraticForm]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The circular fourth contraction
`E[conj(gᵢ)gⱼ conj(gₖ)gₗ] = δᵢⱼδₖₗ + δᵢₗδₖⱼ` implies the second Wick identity, with the ordering `Tr (A B)`. -/
theorem integral_complexQuadraticForm_mul_eq_trace_of_contractions
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (g : Ω → ι → ℂ) (A B : Matrix ι ι ℂ)
    (hint : ∀ i j k l, Integrable (fun ω =>
      (conj (g ω i) * g ω j) * (conj (g ω k) * g ω l)) P)
    (hfourth : ∀ i j k l, ∫ ω,
      (conj (g ω i) * g ω j) * (conj (g ω k) * g ω l) ∂P =
        (if i = j ∧ k = l then 1 else 0) +
        (if i = l ∧ k = j then 1 else 0)) :
    ∫ ω, complexQuadraticForm A (g ω) * complexQuadraticForm B (g ω) ∂P =
      Matrix.trace A * Matrix.trace B + Matrix.trace (A * B) := by
  simp_rw [← complexQuadraticFormProduct_eq_mul]
  simp_rw [complexQuadraticFormProduct]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ =>
        integrable_finsetSum Finset.univ (fun l _ =>
          (hint i j k l).const_mul (A i j * B k l)))))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ =>
        integrable_finsetSum Finset.univ (fun l _ =>
          (hint _ j k l).const_mul (A _ j * B k l)))),
    integral_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun l _ =>
        (hint _ _ k l).const_mul (A _ _ * B k l))),
    integral_finsetSum Finset.univ (fun l _ =>
      (hint _ _ _ l).const_mul (A _ _ * B _ l)),
    integral_const_mul, hfourth]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp [ite_and, Matrix.trace, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- First Wick identity for the independent standard circular law,
for every finite dimension and arbitrary deterministic complex matrix `A`. -/
theorem integral_actualComplexQuadratic_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (∫ z : ι → ℝ × ℝ, complexQuadraticForm A (circularVector z)
      ∂circularVectorLaw ι) = Matrix.trace A :=
  integral_complexQuadraticForm_eq_trace_of_contractions (circularVectorLaw ι)
    circularVector A integrable_circular_second integral_circular_second

/-- Second Wick identity for the independent standard circular law,
for arbitrary deterministic complex `A`, `B`. -/
theorem integral_actualComplexQuadratic_mul_eq_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    (∫ z : ι → ℝ × ℝ,
      complexQuadraticForm A (circularVector z) * complexQuadraticForm B (circularVector z)
      ∂circularVectorLaw ι) = Matrix.trace A * Matrix.trace B + Matrix.trace (A * B) :=
  integral_complexQuadraticForm_mul_eq_trace_of_contractions (circularVectorLaw ι)
    circularVector A B integrable_circular_fourth integral_circular_fourth

/-- Quadratic-form integrability, with arbitrary complex coefficients. -/
theorem integrable_actualComplexQuadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    Integrable (fun z : ι → ℝ × ℝ => complexQuadraticForm A (circularVector z))
      (circularVectorLaw ι) := by
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (integrable_circular_second i j).const_mul (A i j)))

/-- Product-of-quadratic-forms integrability, with arbitrary complex `A`, `B`. -/
theorem integrable_actualComplexQuadratic_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    Integrable (fun z : ι → ℝ × ℝ =>
      complexQuadraticForm A (circularVector z) * complexQuadraticForm B (circularVector z))
      (circularVectorLaw ι) := by
  simp_rw [← complexQuadraticFormProduct_eq_mul]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ =>
        integrable_finsetSum Finset.univ (fun l _ =>
          (integrable_circular_fourth i j k l).const_mul (A i j * B k l)))))

end BlockBand.Counting
