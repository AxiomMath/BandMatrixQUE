module

public import BlockBand.DeterminantScore.GaussianPolynomialGradient.CircleCoefficientCoercivity
public import BlockBand.DeterminantScore.GaussianPolynomialGradient.CircleRootKernel
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.List.OfFn

/-!
# The weighted polynomial estimate on the unit circle

For a complex polynomial `Q` of degree at most `m`, `k ≥ 0` and `2 ≤ p < 3`, the weighted angular
integrand (`weightedAngular`, the `p`-th power of the angular derivative times the `(2 - p)`-th
power of the value) has normalized circle integral at most `weightedCircleConstant k m p` times
the circle `L²` mass of `Q` (`circleAverage_weightedAngular_le`). The proof factors `Q` over its
roots (with multiplicity), bounds the logarithmic derivative by a sum of root kernels, and uses
the root-uniform quotient bound and kernel bound.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.DeterminantScore.GaussianGradient
open Polynomial MeasureTheory
open scoped BigOperators

/-- The roots of `Q`, enumerated with multiplicity. -/
def rootAt (Q : Polynomial ℂ) (i : Fin Q.roots.toList.length) : ℂ :=
  Q.roots.toList.get i

/-- A sum over the roots of `Q` (with multiplicity) as a sum over `Fin`. -/
theorem root_sum_eq_fin (Q : Polynomial ℂ) (f : ℂ → ℂ) :
    (Q.roots.map f).sum = ∑ i : Fin Q.roots.toList.length, f (rootAt Q i) := by
  have h := congrArg (fun l : List ℂ => (l.map f).sum) (List.ofFn_get Q.roots.toList)
  simpa only [List.map_ofFn, List.sum_ofFn, rootAt, Multiset.sum_map_toList, Function.comp_def] using h.symm

/-- Every enumerated root is a root of `Q`. -/
theorem rootAt_isRoot (Q : Polynomial ℂ) (i : Fin Q.roots.toList.length) :
    Q.IsRoot (rootAt Q i) := by
  apply Polynomial.isRoot_of_mem_roots
  exact Multiset.mem_toList.mp (List.get_mem Q.roots.toList i)

/-- The angular derivative numerator of `z^k Q`. -/
def angularNumerator (Q : Polynomial ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  z * Q.derivative.eval z - (k : ℂ) * Q.eval z

/-- Pointwise root-factorization estimate of the angular derivative on the unit circle away from
the zeros of `Q`, with all roots and multiplicities. -/
theorem angularNumerator_norm_le (Q : Polynomial ℂ) (k : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) (hQz : Q.eval z ≠ 0) :
    ‖angularNumerator Q k z‖ ≤ ‖Q.eval z‖ *
      ((k : ℝ) + ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹) := by
  have hsplit := IsAlgClosed.splits Q
  have hder := hsplit.eval_derivative_eq_eval_mul_sum hQz
  rw [root_sum_eq_fin] at hder
  have hb : ‖∑ i : Fin Q.roots.toList.length, 1 / (z - rootAt Q i)‖ ≤
      ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹ := by
    simpa only [one_div, norm_inv] using norm_sum_le Finset.univ
      (fun i : Fin Q.roots.toList.length => (z - rootAt Q i)⁻¹)
  calc
    ‖angularNumerator Q k z‖ ≤ ‖z * Q.derivative.eval z‖ + ‖(k : ℂ) * Q.eval z‖ := norm_sub_le _ _
    _ = ‖Q.eval z‖ * ‖∑ i : Fin Q.roots.toList.length, 1 / (z - rootAt Q i)‖ +
        (k : ℝ) * ‖Q.eval z‖ := by rw [hder]; simp [hz]
    _ ≤ ‖Q.eval z‖ * (∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹) +
        (k : ℝ) * ‖Q.eval z‖ := add_le_add (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) le_rfl
    _ = _ := by ring

/-- The monic linear-factor quotient `Q /ₘ (X - ζ)`. -/
def rootQuotient (Q : Polynomial ℂ) (ζ : ℂ) : Polynomial ℂ := Q /ₘ (X - C ζ)

/-- The factor identity `Q = (X - ζ) · (Q /ₘ (X - ζ))` for every root `ζ`. -/
theorem rootQuotient_factor (Q : Polynomial ℂ) (ζ : ℂ) (hζ : Q.IsRoot ζ) :
    (X - C ζ) * rootQuotient Q ζ = Q :=
  Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hζ

/-- The root quotient has at most the degree of `Q`. -/
theorem rootQuotient_natDegree_le (Q : Polynomial ℂ) (ζ : ℂ) :
    (rootQuotient Q ζ).natDegree ≤ Q.natDegree := by
  rw [rootQuotient, Polynomial.natDegree_divByMonic Q (Polynomial.monic_X_sub_C ζ)]
  omega

/-- Root-uniform bound of the quotient against the normalized circle `L²` mass, with the explicit
degree-only constant `(m+1)²(m+2)`. -/
theorem rootQuotient_eval_sq_le (Q : Polynomial ℂ) (ζ : ℂ) (m : ℕ)
    (hζ : Q.IsRoot ζ) (hdeg : Q.natDegree ≤ m) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(rootQuotient Q ζ).eval z‖ ^ 2 ≤ (m + 1 : ℝ) ^ 2 * (m + 2 : ℝ) *
      Real.circleAverage (fun u => ‖Q.eval u‖ ^ 2) 0 1 := by
  have hb := eval_sq_le_actual_circle_mass (rootQuotient Q ζ) ζ m
    ((rootQuotient_natDegree_le Q ζ).trans hdeg) z hz
  rwa [rootQuotient_factor Q ζ hζ] at hb

/-- Root cancellation away from the zeros of `Q`, including `p = 2`. -/
theorem root_weighted_cancel (Q : Polynomial ℂ) (ζ z : ℂ) (p : ℝ)
    (hζ : Q.IsRoot ζ) (hQz : Q.eval z ≠ 0) :
    ‖Q.eval z‖ ^ 2 * (‖z - ζ‖⁻¹) ^ p =
      ‖(rootQuotient Q ζ).eval z‖ ^ 2 * ‖z - ζ‖ ^ (2 - p) := by
  have heval : Q.eval z = (z - ζ) * (rootQuotient Q ζ).eval z := by
    have h := congrArg (fun A : Polynomial ℂ => A.eval z) (rootQuotient_factor Q ζ hζ)
    simpa using h.symm
  have hd : 0 < ‖z - ζ‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hQz
    rw [heval, h, zero_mul]
  have hp : ‖z - ζ‖ ^ 2 * (‖z - ζ‖⁻¹) ^ p = ‖z - ζ‖ ^ (2 - p) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_neg_eq_inv_rpow,
      ← Real.rpow_add hd]
    simp only [Nat.cast_ofNat, sub_eq_add_neg]
  rw [heval, norm_mul, mul_pow]
  calc
    _ = ‖(rootQuotient Q ζ).eval z‖ ^ 2 * (‖z - ζ‖ ^ 2 * (‖z - ζ‖⁻¹) ^ p) := by ring
    _ = _ := by rw [hp]

/-- The degree term and the root reciprocal terms satisfy the finite `p`-power sum inequality,
with the number of roots plus one as constant. -/
theorem root_log_power_sum_le (Q : Polynomial ℂ) (k : ℕ) (z : ℂ) (p : ℝ)
    (hp : 1 ≤ p) :
    ((k : ℝ) + ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹) ^ p ≤
      (Q.roots.toList.length + 1 : ℝ) ^ (p - 1) *
        ((k : ℝ) ^ p + ∑ i : Fin Q.roots.toList.length, (‖z - rootAt Q i‖⁻¹) ^ p) := by
  let g : Option (Fin Q.roots.toList.length) → ℝ :=
    fun i => i.elim (k : ℝ) (fun j => ‖z - rootAt Q j‖⁻¹)
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (f := g) Finset.univ hp (by
    intro i hi
    cases i with
    | none => exact Nat.cast_nonneg k
    | some j => exact inv_nonneg.mpr (norm_nonneg _))
  simpa [g, Fintype.sum_option] using h

/-- The weighted angular `p`-power is bounded by a sum over root quotients, for all `p ≥ 1`, away
from the zeros of `Q`. -/
theorem angular_weighted_le_root_quotients (Q : Polynomial ℂ) (k : ℕ)
    (z : ℂ) (p : ℝ) (hz : ‖z‖ = 1) (hp : 1 ≤ p) (hQz : Q.eval z ≠ 0) :
    ‖angularNumerator Q k z‖ ^ p * ‖Q.eval z‖ ^ (2 - p) ≤
      (Q.roots.toList.length + 1 : ℝ) ^ (p - 1) *
        ((k : ℝ) ^ p * ‖Q.eval z‖ ^ 2 +
          ∑ i : Fin Q.roots.toList.length,
            ‖(rootQuotient Q (rootAt Q i)).eval z‖ ^ 2 * ‖z - rootAt Q i‖ ^ (2 - p)) := by
  have hq : 0 < ‖Q.eval z‖ := norm_pos_iff.mpr hQz
  have hlog := angularNumerator_norm_le Q k z hz hQz
  have hp0 : 0 ≤ p := by linarith
  have hpw := Real.rpow_le_rpow (norm_nonneg (angularNumerator Q k z)) hlog hp0
  rw [Real.mul_rpow (norm_nonneg _) (add_nonneg (Nat.cast_nonneg k)
    (Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (norm_nonneg (z - rootAt Q i)))))] at hpw
  have hmul := mul_le_mul_of_nonneg_right hpw (Real.rpow_nonneg (norm_nonneg (Q.eval z)) (2 - p))
  have hcancel : ‖Q.eval z‖ ^ p * ‖Q.eval z‖ ^ (2 - p) = ‖Q.eval z‖ ^ 2 := by
    rw [← Real.rpow_add hq]
    norm_num
  have hr : ‖Q.eval z‖ ^ p *
      ((k : ℝ) + ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹) ^ p *
        ‖Q.eval z‖ ^ (2 - p) = ‖Q.eval z‖ ^ 2 *
          ((k : ℝ) + ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹) ^ p := by
    calc
      _ = (‖Q.eval z‖ ^ p * ‖Q.eval z‖ ^ (2 - p)) *
          ((k : ℝ) + ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹) ^ p := by ring
      _ = _ := by rw [hcancel]
  rw [hr] at hmul
  have hs := root_log_power_sum_le Q k z p hp
  have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖Q.eval z‖)
  calc
    _ ≤ ‖Q.eval z‖ ^ 2 *
        ((k : ℝ) + ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖⁻¹) ^ p := hmul
    _ ≤ ‖Q.eval z‖ ^ 2 * ((Q.roots.toList.length + 1 : ℝ) ^ (p - 1) *
        ((k : ℝ) ^ p + ∑ i : Fin Q.roots.toList.length, (‖z - rootAt Q i‖⁻¹) ^ p)) := hs'
    _ = _ := by
      rw [mul_left_comm (‖Q.eval z‖ ^ 2) ((Q.roots.toList.length + 1 : ℝ) ^ (p - 1)),
        mul_add, Finset.mul_sum]
      apply congrArg (fun a : ℝ => (Q.roots.toList.length + 1 : ℝ) ^ (p - 1) * a)
      apply congrArg₂ (fun a b : ℝ => a + b)
      · ring
      · apply Finset.sum_congr rfl
        intro i hi
        exact root_weighted_cancel Q (rootAt Q i) z p (rootAt_isRoot Q i) hQz

/-- The normalized circle `L²` mass of `Q`. -/
def circleSquareMass (Q : Polynomial ℂ) : ℝ :=
  Real.circleAverage (fun z => ‖Q.eval z‖ ^ 2) 0 1

/-- The degree-only root quotient coercivity constant `(m+1)²(m+2)`. -/
def quotientCoercivity (m : ℕ) : ℝ := (m + 1 : ℝ) ^ 2 * (m + 2 : ℝ)

/-- The circle `L²` mass is nonnegative. -/
theorem circleSquareMass_nonneg (Q : Polynomial ℂ) : 0 ≤ circleSquareMass Q :=
  Real.circleAverage_nonneg_of_nonneg (fun z _ => sq_nonneg ‖Q.eval z‖)

/-- The root-kernel majorant; its constants depend only on the degree `m` and the exponent `p`. -/
def weightedRootMajorant (Q : Polynomial ℂ) (k m : ℕ) (p : ℝ) (z : ℂ) : ℝ :=
  (m + 1 : ℝ) ^ (p - 1) * ((k : ℝ) ^ p * ‖Q.eval z‖ ^ 2 +
    quotientCoercivity m * circleSquareMass Q *
      ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖ ^ (2 - p))

/-- The weighted angular `p`-power is bounded by the root-kernel majorant away from the zeros of
`Q`. -/
theorem angular_weighted_le_majorant (Q : Polynomial ℂ) (k m : ℕ) (z : ℂ) (p : ℝ)
    (hz : ‖z‖ = 1) (hp : 1 ≤ p) (hdeg : Q.natDegree ≤ m) (hQz : Q.eval z ≠ 0) :
    ‖angularNumerator Q k z‖ ^ p * ‖Q.eval z‖ ^ (2 - p) ≤
      weightedRootMajorant Q k m p z := by
  have hq := angular_weighted_le_root_quotients Q k z p hz hp hQz
  have hn : Q.roots.toList.length ≤ m := by
    simpa using (Polynomial.card_roots' Q).trans hdeg
  have hc : (Q.roots.toList.length + 1 : ℝ) ^ (p - 1) ≤ (m + 1 : ℝ) ^ (p - 1) := by
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    linarith
  have hsum : (∑ i : Fin Q.roots.toList.length,
      ‖(rootQuotient Q (rootAt Q i)).eval z‖ ^ 2 * ‖z - rootAt Q i‖ ^ (2 - p)) ≤
      quotientCoercivity m * circleSquareMass Q *
        ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖ ^ (2 - p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (rootQuotient_eval_sq_le Q (rootAt Q i) m (rootAt_isRoot Q i) hdeg z hz)
      (Real.rpow_nonneg (norm_nonneg _) (2 - p))
  refine hq.trans ?_
  exact mul_le_mul hc (add_le_add le_rfl hsum)
    (add_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) p) (sq_nonneg _))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (norm_nonneg (z - rootAt Q i)) (2 - p)))))
    (Real.rpow_nonneg (by positivity) (p - 1))

/-- The zero angles of a nonzero complex polynomial form a finite set in one half-open period of
the circle, on which the circle parametrization is injective. -/
theorem finite_circle_zero_angles (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    Set.Finite {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧ Q.eval (circleMap 0 1 θ) = 0} := by
  apply Set.Finite.of_injOn (f := circleMap 0 1)
    (t := {z : ℂ | Q.IsRoot z})
  · intro θ hθ
    exact hθ.2
  · apply (injOn_circleMap_of_abs_sub_le (c := (0 : ℂ)) (R := 1)
      (a := 0) (b := 2 * Real.pi) (by norm_num) (by simp)).mono
    intro θ hθ
    simpa [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using hθ.1
  · exact Polynomial.finite_setOfPred_isRoot hQ

/-- The zeros of a nonzero polynomial are null for Lebesgue measure in the circle angle. -/
theorem ae_circle_eval_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∀ᵐ θ : ℝ ∂MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)),
      Q.eval (circleMap 0 1 θ) ≠ 0 := by
  apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [(finite_circle_zero_angles Q hQ).countable.ae_notMem MeasureTheory.volume] with θ hθ hI
  intro he
  exact hθ ⟨hI, he⟩

/-- The square of a polynomial is circle integrable. -/
theorem circleIntegrable_polynomial_sq (Q : Polynomial ℂ) :
    CircleIntegrable (fun z => ‖Q.eval z‖ ^ 2) 0 1 := by
  have h : Continuous (fun z : ℂ => ‖Q.eval z‖ ^ 2) := by fun_prop
  exact h.continuousOn.circleIntegrable (by norm_num)

/-- Scalar multiplication preserves normalized-circle integrability. -/
theorem circleIntegrable_const_mul {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) (c : ℝ) :
    CircleIntegrable (fun z => c * f z) 0 1 := by
  exact (hf : IntervalIntegrable (fun θ => f (circleMap 0 1 θ))
    MeasureTheory.volume 0 (2 * Real.pi)).const_mul c

/-- The finite sum of the root kernels is circle integrable for all `2 ≤ p < 3`. -/
theorem circleIntegrable_root_sum (Q : Polynomial ℂ) (p : ℝ) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    CircleIntegrable (fun z => ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖ ^ (2 - p)) 0 1 := by
  apply CircleIntegrable.fun_sum
  intro i hi
  simpa only [show -(p - 2) = 2 - p by ring] using
    circleIntegrable_root_kernel (rootAt Q i) (p - 2) (by linarith) (by linarith)

/-- The root-kernel majorant is circle integrable. -/
theorem circleIntegrable_weightedRootMajorant (Q : Polynomial ℂ) (k m : ℕ)
    (p : ℝ) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    CircleIntegrable (weightedRootMajorant Q k m p) 0 1 := by
  exact circleIntegrable_const_mul
    ((circleIntegrable_const_mul (circleIntegrable_polynomial_sq Q) ((k : ℝ) ^ p)).fun_add
      (circleIntegrable_const_mul (circleIntegrable_root_sum Q p hp2 hp3)
        (quotientCoercivity m * circleSquareMass Q))) ((m + 1 : ℝ) ^ (p - 1))

/-- The root kernel constant is nonnegative on its whole range. -/
theorem circleKernelMajorant_nonneg (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ circleKernelMajorant s := by
  exact (Real.circleAverage_nonneg_of_nonneg
    (fun z _ => Real.rpow_nonneg (norm_nonneg (z - (0 : ℂ))) (-s))).trans
      (circleAverage_root_kernel_le 0 s hs0 hs1)

/-- The integrated root sum has a degree-only bound over all roots, with multiplicities, including
`p = 2`. -/
theorem circleAverage_root_sum_le (Q : Polynomial ℂ) (m : ℕ) (p : ℝ)
    (hdeg : Q.natDegree ≤ m) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    Real.circleAverage
      (fun z => ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖ ^ (2 - p)) 0 1 ≤
      (m : ℝ) * circleKernelMajorant (p - 2) := by
  have hi : ∀ i : Fin Q.roots.toList.length,
      CircleIntegrable (fun z => ‖z - rootAt Q i‖ ^ (2 - p)) 0 1 := by
    intro i
    simpa only [show -(p - 2) = 2 - p by ring] using
      circleIntegrable_root_kernel (rootAt Q i) (p - 2) (by linarith) (by linarith)
  rw [Real.circleAverage_fun_sum (fun i _ => hi i)]
  have hn : Q.roots.toList.length ≤ m := by
    simpa using (Polynomial.card_roots' Q).trans hdeg
  calc
    _ ≤ ∑ _i : Fin Q.roots.toList.length, circleKernelMajorant (p - 2) := by
      apply Finset.sum_le_sum
      intro i hi'
      simpa only [show -(p - 2) = 2 - p by ring] using
        circleAverage_root_kernel_le (rootAt Q i) (p - 2) (by linarith) (by linarith)
    _ = (Q.roots.toList.length : ℝ) * circleKernelMajorant (p - 2) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn)
      (circleKernelMajorant_nonneg (p - 2) (by linarith) (by linarith))

/-- The explicit constant of the circle estimate, depending only on `k`, `m` and `p`. -/
def weightedCircleConstant (k m : ℕ) (p : ℝ) : ℝ :=
  (m + 1 : ℝ) ^ (p - 1) *
    ((k : ℝ) ^ p + quotientCoercivity m * (m : ℝ) * circleKernelMajorant (p - 2))

/-- The normalized-circle integral bound of the root-kernel majorant, for all `2 ≤ p < 3` and all
complex polynomials of degree at most `m`. -/
theorem circleAverage_weightedRootMajorant_le (Q : Polynomial ℂ) (k m : ℕ)
    (p : ℝ) (hdeg : Q.natDegree ≤ m) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    Real.circleAverage (weightedRootMajorant Q k m p) 0 1 ≤
      weightedCircleConstant k m p * circleSquareMass Q := by
  have hq := circleIntegrable_const_mul (circleIntegrable_polynomial_sq Q) ((k : ℝ) ^ p)
  have hs := circleIntegrable_const_mul (circleIntegrable_root_sum Q p hp2 hp3)
    (quotientCoercivity m * circleSquareMass Q)
  unfold weightedRootMajorant
  simp only [← smul_eq_mul, Real.circleAverage_fun_smul]
  simp only [smul_eq_mul]
  rw [Real.circleAverage_fun_add hq hs]
  have he1 : Real.circleAverage (fun z => (k : ℝ) ^ p * ‖Q.eval z‖ ^ 2) 0 1 =
      (k : ℝ) ^ p * circleSquareMass Q := by
    simpa only [smul_eq_mul, circleSquareMass] using
      (Real.circleAverage_fun_smul (a := (k : ℝ) ^ p)
        (f := fun z : ℂ => ‖Q.eval z‖ ^ 2) (c := 0) (R := 1))
  have he2 : Real.circleAverage (fun z => quotientCoercivity m * circleSquareMass Q *
      ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖ ^ (2 - p)) 0 1 =
      quotientCoercivity m * circleSquareMass Q * Real.circleAverage
        (fun z => ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖ ^ (2 - p)) 0 1 := by
    simpa only [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := quotientCoercivity m * circleSquareMass Q)
        (f := fun z : ℂ => ∑ i : Fin Q.roots.toList.length, ‖z - rootAt Q i‖ ^ (2 - p))
        (c := 0) (R := 1))
  rw [he1, he2]
  have hsum := circleAverage_root_sum_le Q m p hdeg hp2 hp3
  have hC : 0 ≤ quotientCoercivity m * circleSquareMass Q :=
    mul_nonneg (by unfold quotientCoercivity; positivity) (circleSquareMass_nonneg Q)
  have hb := mul_le_mul_of_nonneg_left hsum hC
  have hout := mul_le_mul_of_nonneg_left (add_le_add_left hb ((k : ℝ) ^ p * circleSquareMass Q))
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ m + 1) (p - 1))
  convert hout using 1
  · ring
  · unfold weightedCircleConstant
    ring

/-- The weighted angular integrand of the polynomial numerator. -/
def weightedAngular (Q : Polynomial ℂ) (k : ℕ) (p : ℝ) (z : ℂ) : ℝ :=
  ‖angularNumerator Q k z‖ ^ p * ‖Q.eval z‖ ^ (2 - p)

/-- The weighted angular integrand is measurable for all `p` (measurability of the real power, not
continuity at the zeros of `Q`). -/
theorem measurable_weightedAngular (Q : Polynomial ℂ) (k : ℕ) (p : ℝ) :
    Measurable (weightedAngular Q k p) := by
  have ha : Measurable (fun z : ℂ => ‖angularNumerator Q k z‖) := by
    unfold angularNumerator
    fun_prop
  have hq : Measurable (fun z : ℂ => ‖Q.eval z‖) := by fun_prop
  exact (ha.pow_const p).mul (hq.pow_const (2 - p))

/-- The weighted angular integrand is nonnegative. -/
theorem weightedAngular_nonneg (Q : Polynomial ℂ) (k : ℕ) (p : ℝ) (z : ℂ) :
    0 ≤ weightedAngular Q k p z :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) p)
    (Real.rpow_nonneg (norm_nonneg _) (2 - p))

/-- The weighted angular integrand is circle integrable, from the integrable majorant and the
Lebesgue-null zeros of `Q`. -/
theorem circleIntegrable_weightedAngular (Q : Polynomial ℂ) (k m : ℕ) (p : ℝ)
    (hdeg : Q.natDegree ≤ m) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    CircleIntegrable (weightedAngular Q k p) 0 1 := by
  by_cases hQ : Q = 0
  · subst Q
    have he : weightedAngular 0 k p = fun _ : ℂ => (0 : ℝ) := by
      funext z
      simp [weightedAngular, angularNumerator, Real.zero_rpow (by linarith : p ≠ 0)]
    rw [he]
    exact circleIntegrable_const (0 : ℝ) (0 : ℂ) 1
  have hmajor := circleIntegrable_weightedRootMajorant Q k m p hp2 hp3
  have hmajor' := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mp hmajor
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mpr
  refine hmajor'.mono' ((measurable_weightedAngular Q k p).comp
    (continuous_circleMap 0 1).measurable).aestronglyMeasurable ?_
  filter_upwards [ae_circle_eval_ne_zero Q hQ] with θ hθ
  rw [Real.norm_of_nonneg (weightedAngular_nonneg Q k p (circleMap 0 1 θ))]
  exact angular_weighted_le_majorant Q k m (circleMap 0 1 θ) p (by simp)
    (by linarith) hdeg hθ

/-- **The weighted polynomial estimate on the circle**, for every complex `Q` (including `Q = 0`),
all `k, m` with `natDegree Q ≤ m`, and every `2 ≤ p < 3`, with constants independent of the
coefficients. -/
theorem circleAverage_weightedAngular_le (Q : Polynomial ℂ) (k m : ℕ) (p : ℝ)
    (hdeg : Q.natDegree ≤ m) (hp2 : 2 ≤ p) (hp3 : p < 3) :
    Real.circleAverage (weightedAngular Q k p) 0 1 ≤
      weightedCircleConstant k m p * circleSquareMass Q := by
  have hf := circleIntegrable_weightedAngular Q k m p hdeg hp2 hp3
  have hg := circleIntegrable_weightedRootMajorant Q k m p hp2 hp3
  have hT : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hf' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hf
  have hg' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hg
  have hle : ∀ᵐ θ : ℝ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)),
      weightedAngular Q k p (circleMap 0 1 θ) ≤ weightedRootMajorant Q k m p (circleMap 0 1 θ) := by
    by_cases hQ : Q = 0
    · subst Q
      filter_upwards with θ
      simp [weightedAngular, angularNumerator, weightedRootMajorant, circleSquareMass,
        Real.zero_rpow (by linarith : p ≠ 0)]
    · filter_upwards [ae_circle_eval_ne_zero Q hQ] with θ hθ
      exact angular_weighted_le_majorant Q k m (circleMap 0 1 θ) p (by simp)
        (by linarith) hdeg hθ
  have hi := integral_mono_ae hf' hg' hle
  have hc : Real.circleAverage (weightedAngular Q k p) 0 1 ≤
      Real.circleAverage (weightedRootMajorant Q k m p) 0 1 := by
    simp only [Real.circleAverage_def, smul_eq_mul]
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
    exact mul_le_mul_of_nonneg_left hi (by positivity)
  exact hc.trans (circleAverage_weightedRootMajorant_le Q k m p hdeg hp2 hp3)

end BlockBand.DeterminantScore.GaussianGradient
