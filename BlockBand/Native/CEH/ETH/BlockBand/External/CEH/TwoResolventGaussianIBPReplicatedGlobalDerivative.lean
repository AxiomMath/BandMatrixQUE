module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedOperator
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPBlockAdapter

/-!
# Entrywise-topology derivative for the replicated GUE resolvent

Mathlib's bare finite matrix type carries the product topology but does not
silently carry the operator-normed-ring structure needed by the generic Banach
algebra inverse theorem.  This module therefore proves the inverse derivative, entry by entry, from the determinant/adjugate formula and the local
identity `A A⁻¹ = 1`.  The theorem applies to an arbitrary differentiable
matrix curve, not only to a single coordinate pencil.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

namespace CEHNative.BlockBand.External.CEH
namespace ReplicatedGUEEuclidean

open PencilAdapter

/-- An arbitrary entrywise differentiable nonsingular matrix curve has the
usual inverse derivative.  The domain is a real line, while the matrix uses
its finite product topology; the proof differentiates determinant,
adjugate, and finite matrix products entrywise. -/
theorem hasDerivAt_matrixInverse_entry
    {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ)
    (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (A' i j) x)
    (hMx : M x = A) (hA : IsUnit A.det) (i j : Fin n) :
    HasDerivAt (fun t => (M t)⁻¹ i j) (-(A⁻¹ * A' * A⁻¹) i j) x := by
  let G : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => (M t)⁻¹
  let Q : Matrix (Fin n) (Fin n) ℂ := fun p q => deriv (fun t => G t p q) x
  have hdiff (p q : Fin n) : DifferentiableAt ℝ (fun t => G t p q) x := by
    unfold G
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    have detDiff (B : ℝ → Matrix (Fin n) (Fin n) ℂ)
        (hB : ∀ a b, DifferentiableAt ℝ (fun t => B t a b) x) :
        DifferentiableAt ℝ (fun t => (B t).det) x := by
      simp only [Matrix.det_apply']
      apply DifferentiableAt.fun_sum
      intro σ hσ
      apply (differentiableAt_const (c := ((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
      apply DifferentiableAt.fun_finsetProd
      intro k hk
      exact hB (σ k) k
    have hdet : DifferentiableAt ℝ (fun t => (M t).det) x :=
      detDiff M fun a b => (hM a b).differentiableAt
    have hinv : DifferentiableAt ℝ (fun t => (M t).det⁻¹) x := by
      apply hdet.inv
      simpa [hMx] using hA.ne_zero
    apply hinv.mul
    simp only [Matrix.adjugate_apply]
    apply detDiff
    intro a b
    simp only [Matrix.updateRow_apply]
    split_ifs
    · fun_prop
    · exact (hM _ _).differentiableAt
  have hG (p q : Fin n) : HasDerivAt (fun t => G t p q) (Q p q) x :=
    (hdiff p q).hasDerivAt
  have hprod (p q : Fin n) :
      HasDerivAt (fun t => (M t * G t) p q)
        ((A' * G x + M x * Q) p q) x := by
    simp only [Matrix.mul_apply, Matrix.add_apply]
    convert HasDerivAt.fun_sum (u := Finset.univ) (x := x)
      (A := fun k t => M t p k * G t k q)
      (A' := fun k => A' p k * G x k q + M x p k * Q k q)
      (fun k hk => (hM p k).mul (hG k q)) using 1
    simp only [Finset.sum_add_distrib]
  have hunit : ∀ᶠ t in nhds x, IsUnit (M t).det := by
    have hdet : ContinuousAt (fun t => (M t).det) x := by
      have hd : DifferentiableAt ℝ (fun t => (M t).det) x := by
        simp only [Matrix.det_apply']
        apply DifferentiableAt.fun_sum
        intro σ hσ
        apply (differentiableAt_const (c := ((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
        apply DifferentiableAt.fun_finsetProd
        intro k hk
        exact (hM (σ k) k).differentiableAt
      exact hd.continuousAt
    filter_upwards [hdet.eventually_ne (by simpa [hMx] using hA.ne_zero)] with t ht
    exact isUnit_iff_ne_zero.mpr ht
  have hzero (p q : Fin n) : (A' * G x + M x * Q) p q = 0 := by
    have heq : (fun t => (M t * G t) p q) =ᶠ[nhds x]
        (fun _ : ℝ => (1 : Matrix (Fin n) (Fin n) ℂ) p q) := by
      filter_upwards [hunit] with t ht
      exact congrFun (congrFun (Matrix.mul_nonsing_inv (M t) ht) p) q
    exact (hprod p q).unique
      ((hasDerivAt_const x _).congr_of_eventuallyEq heq)
  have hmatrix : A' * G x + M x * Q = 0 := by
    ext p q
    exact hzero p q
  have hGx : G x = A⁻¹ := by simp [G, hMx]
  have hleft : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hQ : Q = -(A⁻¹ * A' * A⁻¹) := by
    have h := congrArg (fun X => A⁻¹ * X) hmatrix
    rw [hMx, hGx] at h
    calc
      Q = A⁻¹ * (A * Q) := by rw [← Matrix.mul_assoc, hleft, one_mul]
      _ = -(A⁻¹ * (A' * A⁻¹)) := by
        apply add_left_cancel (a := A⁻¹ * (A' * A⁻¹))
        simpa [Matrix.mul_add, Matrix.mul_assoc] using h
      _ = -(A⁻¹ * A' * A⁻¹) := by rw [Matrix.mul_assoc]
  exact (hG i j).congr_deriv (by rw [hQ]; rfl)

/-- The corresponding global derivative of the normalized trace of an
arbitrary entrywise differentiable nonsingular matrix curve.  Unlike the
pre-existing coordinate-pencilled result, the tangent matrix `A'` is entirely
arbitrary. -/
theorem hasDerivAt_normalizedTrace_matrixInverse
    {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ)
    (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ)
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (A' i j) x)
    (hMx : M x = A) (hA : IsUnit A.det) :
    HasDerivAt
      (fun t => NTrace (M t)⁻¹)
      (((n : ℂ)⁻¹) * ∑ i : Fin n, -(A⁻¹ * A' * A⁻¹) i i) x := by
  unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
    Matrix.trace
  exact (HasDerivAt.fun_sum (u := Finset.univ) (x := x)
    (fun i hi => hasDerivAt_matrixInverse_entry A A' M x hM hMx hA i i)).const_mul
      ((n : ℂ)⁻¹)

/-- Concrete Gaussian Poincaré specialization for the transported replicated
GUE law.  No probabilistic hypothesis is left: the only hypothesis for a
particular resolvent observable is its explicit uniform global
Fréchet-derivative bound. -/
theorem variance_measure_le_of_fderiv_bound
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {g : CoordinateEuclideanSpace N d → ℝ} (hg : ContDiff ℝ 1 g)
    {K : ℝ} (hK : 0 ≤ K) (hderiv : ∀ x, ‖fderiv ℝ g x‖ ≤ K) :
    Var[g; measure N d] ≤
      (Real.pi ^ 2 / 8) * (1 / (((N * d : ℕ) : ℝ))) * K ^ 2 := by
  have h := FiniteGaussianPoincare.variance_le_pi_sq_div_eight_mul_opNorm_covarianceOperator_mul_bound_sq
      (μ := measure N d) (integral_id_eq_zero N d) hg hK hderiv
  rw [norm_covarianceOperator_measure hN hd] at h
  exact h

end ReplicatedGUEEuclidean
end CEHNative.BlockBand.External.CEH
