module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.GUEMatrixLawAdapter
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventPencilAdapter
public import BlockBand.Native.CEH.ETH.BlockBand.Probability.GaussianIntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Finite-coordinate GUE integration by parts for CEH resolvents

This module works in the concrete finite Hermitian coordinate chart used by
`hermitianGUEBlock`.  It identifies
the diagonal and strict-upper variances, differentiates the non-real
matrix resolvent in every real coordinate, and exposes the exact coordinate
Gaussian integration-by-parts identity from which the CEH covariance
contraction is assembled.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

/-- The Hermitian matrix direction belonging to one finite real coordinate. -/
def gueCoordinateDirection (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    Matrix (Fin N) (Fin N) ℂ :=
  (hermitianGUEBlock N (Pi.single k 1)).1

/-- Every real coordinate direction in the GUE chart is Hermitian. -/
theorem gueCoordinateDirection_isHermitian (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    (gueCoordinateDirection N k).IsHermitian :=
  (hermitianGUEBlock N (Pi.single k 1)).2

/-- The concrete variance is `t` on diagonal coordinates. -/
theorem hermitianGUEFinCoordinateVariance_diagonal
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate N))) (i : Fin N)
    (hk : (hermitianCoordinateEquivFin N).symm k = .inl i) :
    hermitianGUEFinCoordinateVariance N t ht k = ⟨t, ht⟩ := by
  unfold hermitianGUEFinCoordinateVariance
  rw [hk]

/-- Each real or imaginary strict-upper coordinate has variance `t/2`. -/
theorem hermitianGUEFinCoordinateVariance_offDiagonal
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (c : StrictUpperIndex N ⊕ StrictUpperIndex N)
    (hk : (hermitianCoordinateEquivFin N).symm k = .inr c) :
    hermitianGUEFinCoordinateVariance N t ht k =
      ⟨t / 2, div_nonneg ht (by norm_num)⟩ := by
  unfold hermitianGUEFinCoordinateVariance
  rw [hk]

/-- At normalized GUE scale the diagonal variance is exactly `1/N`. -/
theorem normalizedCoordinateVariance_diagonal
    {N : ℕ} (hN : 0 < N)
    (k : Fin (Fintype.card (HermitianCoordinate N))) (i : Fin N)
    (hk : (hermitianCoordinateEquivFin N).symm k = .inl i) :
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
      (by positivity) k : ℝ) = 1 / (N : ℝ) := by
  rw [hermitianGUEFinCoordinateVariance_diagonal N _ _ k i hk]
  rfl

/-- At normalized GUE scale each strict-upper real coordinate has exactly
variance `1/(2N)`. -/
theorem normalizedCoordinateVariance_offDiagonal
    {N : ℕ} (hN : 0 < N)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (c : StrictUpperIndex N ⊕ StrictUpperIndex N)
    (hk : (hermitianCoordinateEquivFin N).symm k = .inr c) :
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
      (by positivity) k : ℝ) = 1 / (2 * (N : ℝ)) := by
  rw [hermitianGUEFinCoordinateVariance_offDiagonal N _ _ k c hk]
  change (1 / (N : ℝ)) / 2 = 1 / (2 * (N : ℝ))
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]

/-- Every coordinate variance is positive when the matrix variance is. -/
theorem hermitianGUEFinCoordinateVariance_pos
    (N : ℕ) {t : ℝ} (ht : 0 < t)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    0 < hermitianGUEFinCoordinateVariance N t ht.le k := by
  cases h : (hermitianCoordinateEquivFin N).symm k with
  | inl i =>
      rw [hermitianGUEFinCoordinateVariance_diagonal N t ht.le k i h]
      exact ht
  | inr c =>
      rw [hermitianGUEFinCoordinateVariance_offDiagonal N t ht.le k c h]
      exact div_pos ht (by norm_num)

/-- A matrix pencil affine in one real GUE coordinate. -/
def coordinatePencil {N : ℕ} (B D : Matrix (Fin N) (Fin N) ℂ)
    (x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  B + (x : ℂ) • D

/-- Its nonsingular inverse. -/
def coordinateResolvent {N : ℕ} (B D : Matrix (Fin N) (Fin N) ℂ)
    (x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (coordinatePencil B D x)⁻¹

/-- An affine inverse pencil is differentiable at every nonsingular point. -/
theorem differentiableAt_coordinateResolvent {N : ℕ}
    (B D : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (x : ℝ)
    (hx : IsUnit (coordinatePencil B D x).det) :
    DifferentiableAt ℝ (fun y => coordinateResolvent B D y i j) x := by
  unfold coordinateResolvent
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  have detDiff (A : ℝ → Matrix (Fin N) (Fin N) ℂ)
      (hA : ∀ p q, DifferentiableAt ℝ (fun y => A y p q) x) :
      DifferentiableAt ℝ (fun y => (A y).det) x := by
    simp only [Matrix.det_apply']
    apply DifferentiableAt.fun_sum
    intro σ hσ
    apply (differentiableAt_const (c :=
      ((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
    apply DifferentiableAt.fun_finsetProd
    intro k hk
    exact hA (σ k) k
  have hdet : DifferentiableAt ℝ
      (fun y => (coordinatePencil B D y).det) x := by
    apply detDiff
    intro p q
    unfold coordinatePencil
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hdet0 : (coordinatePencil B D x).det ≠ 0 := hx.ne_zero
  have hinv : DifferentiableAt ℝ
      (fun y => (coordinatePencil B D y).det⁻¹) x :=
    hdet.inv hdet0
  apply hinv.mul
  simp only [Matrix.adjugate_apply]
  apply detDiff
  intro p q
  simp only [Matrix.updateRow_apply]
  split_ifs
  · fun_prop
  · unfold coordinatePencil
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop

/-- The entrywise resolvent derivative, in the form used by coordinate GUE
integration by parts.  No matrix-valued normed-ring structure is required:
the proof differentiates the finite matrix product entry by entry. -/
theorem hasDerivAt_coordinateResolvent_entry {N : ℕ}
    (B D : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (x : ℝ)
    (hx : IsUnit (coordinatePencil B D x).det) :
    HasDerivAt (fun y => coordinateResolvent B D y i j)
      (-(coordinateResolvent B D x * D *
        coordinateResolvent B D x) i j) x := by
  let A := coordinatePencil B D
  let G := coordinateResolvent B D
  let Q : Matrix (Fin N) (Fin N) ℂ :=
    fun p q => deriv (fun y => G y p q) x
  have hG (p q : Fin N) :
      HasDerivAt (fun y => G y p q) (Q p q) x :=
    (differentiableAt_coordinateResolvent B D p q x hx).hasDerivAt
  have hA (p q : Fin N) :
      HasDerivAt (fun y => A y p q) (D p q) x := by
    have hv : HasDerivAt (fun y : ℝ => (y : ℂ) * D p q) (D p q) x := by
      convert Complex.ofRealCLM.hasDerivAt.const_mul (D p q) using 1 <;>
        simp [mul_comm]
    convert (hasDerivAt_const x (B p q)).add hv using 1
    · funext y
      simp [A, coordinatePencil, Matrix.add_apply, Matrix.smul_apply]
    · simp
  have hdet : DifferentiableAt ℝ (fun y => (A y).det) x := by
    simp only [Matrix.det_apply']
    apply DifferentiableAt.fun_sum
    intro σ hσ
    apply (differentiableAt_const (c :=
      ((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
    apply DifferentiableAt.fun_finsetProd
    intro k hk
    exact (hA (σ k) k).differentiableAt
  have hunit : ∀ᶠ y in nhds x, IsUnit (A y).det := by
    filter_upwards [hdet.continuousAt.eventually_ne hx.ne_zero] with y hy
    exact isUnit_iff_ne_zero.mpr hy
  have hprod (p q : Fin N) :
      HasDerivAt (fun y => (A y * G y) p q)
        ((D * G x + A x * Q) p q) x := by
    simp only [Matrix.mul_apply, Matrix.add_apply]
    convert HasDerivAt.fun_sum (u := Finset.univ) (x := x)
      (A := fun k y => A y p k * G y k q)
      (A' := fun k => D p k * G x k q + A x p k * Q k q)
      (fun k hk => (hA p k).mul (hG k q)) using 1
    simp only [Finset.sum_add_distrib]
  have hzero (p q : Fin N) :
      (D * G x + A x * Q) p q = 0 := by
    have heq :
        (fun y => (A y * G y) p q) =ᶠ[nhds x]
          (fun _ : ℝ => (1 : Matrix (Fin N) (Fin N) ℂ) p q) := by
      filter_upwards [hunit] with y hy
      exact congrFun (congrFun (Matrix.mul_nonsing_inv (A y) hy) p) q
    have hc : HasDerivAt
        (fun _ : ℝ => (1 : Matrix (Fin N) (Fin N) ℂ) p q) 0 x :=
      hasDerivAt_const x _
    exact (hprod p q).unique (hc.congr_of_eventuallyEq heq)
  have hmatrix : D * G x + A x * Q = 0 := by
    ext p q
    exact hzero p q
  have hAx : A x * G x = 1 := Matrix.mul_nonsing_inv (A x) hx
  have hGx : G x * A x = 1 := Matrix.nonsing_inv_mul (A x) hx
  have hQ : Q = -(G x * D * G x) := by
    have h := congrArg (fun M => G x * M) hmatrix
    calc
      Q = G x * (A x * Q) := by rw [← Matrix.mul_assoc, hGx, one_mul]
      _ = -(G x * (D * G x)) := by
        apply add_left_cancel (a := G x * (D * G x))
        simpa [Matrix.mul_add, Matrix.mul_assoc] using h
      _ = -(G x * D * G x) := by rw [Matrix.mul_assoc]
  exact (hG i j).congr_deriv (by
    rw [hQ]
    rfl)

/-- Varying one Hermitian direction in the concrete CEH random pencil is the
affine pencil above, with direction `λD`. -/
theorem resolventPencil_add_real_smul {N : ℕ}
    (f : PencilAdapter.Spectrum N) (lambda : ℝ)
    (W D : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (x : ℝ) :
    PencilAdapter.resolventPencil f lambda
        (W + (x : ℂ) • D) z =
      coordinatePencil (PencilAdapter.resolventPencil f lambda W z)
        ((lambda : ℂ) • D) x := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [PencilAdapter.resolventPencil, PencilAdapter.deformedMatrix,
      coordinatePencil]
    ring
  ·
    simp [PencilAdapter.resolventPencil, PencilAdapter.deformedMatrix,
      coordinatePencil, hpq]
    ring

/-- Entrywise derivative of the CEH resolvent when a real Hermitian
matrix coordinate is varied. -/
theorem hasDerivAt_pencilResolvent_realDirection {N : ℕ}
    (f : PencilAdapter.Spectrum N) (lambda : ℝ)
    (W D : Matrix (Fin N) (Fin N) ℂ)
    (hW : W.IsHermitian) (hD : D.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Fin N) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => PencilAdapter.resolvent f lambda
        (W + (y : ℂ) • D) z i j)
      (-(PencilAdapter.resolvent f lambda (W + (x : ℂ) • D) z *
        ((lambda : ℂ) • D) *
        PencilAdapter.resolvent f lambda (W + (x : ℂ) • D) z) i j) x := by
  have hWx : (W + (x : ℂ) • D).IsHermitian := by
    exact hW.add (hD.smul (RCLike.conj_ofReal x))
  have hx := PencilAdapter.isUnit_det_resolventPencil f lambda
    (W + (x : ℂ) • D) hWx hz
  have h := hasDerivAt_coordinateResolvent_entry
    (PencilAdapter.resolventPencil f lambda W z)
    ((lambda : ℂ) • D) i j x
    (by
      rw [← resolventPencil_add_real_smul]
      exact hx)
  have hfun :
      (fun y : ℝ => PencilAdapter.resolvent f lambda
        (W + (y : ℂ) • D) z i j) =
      (fun y : ℝ => coordinateResolvent
        (PencilAdapter.resolventPencil f lambda W z)
        ((lambda : ℂ) • D) y i j) := by
    funext y
    unfold PencilAdapter.resolvent coordinateResolvent
    rw [resolventPencil_add_real_smul]
  rw [hfun]
  convert h using 1
  unfold PencilAdapter.resolvent coordinateResolvent
  rw [resolventPencil_add_real_smul]

/-- **Concrete finite-coordinate GUE integration by parts for a resolvent
entry.**  The coordinate is one of the real coordinates reconstructed
by `hermitianGUEBlock`; hence its variance is definitionally `1/N` on the
diagonal and `1/(2N)` on either strict-upper component.  The derivative is
proved above from the finite-dimensional inverse equation.

The three density-integrability premises are stated explicitly because they
are exactly the analytic side conditions of the repository's proved
whole-line Gaussian IBP theorem. -/
theorem normalizedGUECoordinateResolventEntry_IBP
    {N : ℕ} (hN : 0 < N)
    (B : Matrix (Fin N) (Fin N) ℂ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) (i j : Fin N)
    (hinv : ∀ x : ℝ,
      IsUnit (coordinatePencil B (gueCoordinateDirection N k) x).det)
    (hxf : Integrable (fun x : ℝ =>
      ((x * gaussianPDFReal 0
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k) x : ℝ) : ℂ) *
        coordinateResolvent B (gueCoordinateDirection N k) x i j))
    (hdf : Integrable (fun x : ℝ =>
      ((gaussianPDFReal 0
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k) x : ℝ) : ℂ) *
        (-(coordinateResolvent B (gueCoordinateDirection N k) x *
          gueCoordinateDirection N k *
          coordinateResolvent B (gueCoordinateDirection N k) x) i j)))
    (hf : Integrable (fun x : ℝ =>
      ((gaussianPDFReal 0
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k) x : ℝ) : ℂ) *
        coordinateResolvent B (gueCoordinateDirection N k) x i j)) :
    (∫ x : ℝ, (x : ℂ) *
        coordinateResolvent B (gueCoordinateDirection N k) x i j
      ∂gaussianReal 0
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℝ) *
        ∫ x : ℝ,
          (-(coordinateResolvent B (gueCoordinateDirection N k) x *
            gueCoordinateDirection N k *
            coordinateResolvent B (gueCoordinateDirection N k) x) i j)
        ∂gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k) := by
  let v := hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
    (by positivity) k
  have hv : v ≠ 0 :=
    ne_of_gt (hermitianGUEFinCoordinateVariance_pos N
      (show 0 < 1 / (N : ℝ) by positivity) k)
  exact realGaussianIntegrationByParts_density v hv
    (fun x => coordinateResolvent B (gueCoordinateDirection N k) x i j)
    (fun x => -((coordinateResolvent B (gueCoordinateDirection N k) x *
      gueCoordinateDirection N k *
      coordinateResolvent B (gueCoordinateDirection N k) x) i j))
    (fun x => hasDerivAt_coordinateResolvent_entry
      B (gueCoordinateDirection N k) i j x (hinv x))
    hxf hdf hf

end CEHNative.BlockBand.External.CEH
