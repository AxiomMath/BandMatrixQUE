module

public import BlockBand.Model.Construction.OrderedSpectrum

/-!
# Algebraic phase-free ordered projector

For every finite complex Hermitian matrix, the Lagrange product
`∏_{j ≠ i} (A - λ_j)/(λ_i - λ_j)` over the increasing eigenvalues is a Borel measurable function
of the matrix (with inverse-zero conventions at eigenvalue collisions). On simple spectrum it is
the spectral projector onto the `i`-th ordered eigenline, the outer product of the ordered
normalized eigenvector (`orderedProjector_eq_outerProduct`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One Lagrange factor, with the selected rank replaced by the identity. -/
def orderedProjectorFactor (i j : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) : Matrix ι ι ℂ :=
  if j = i then 1 else
    (((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ)⁻¹) •
      (A.val - (orderedEigenvalue A j : ℂ) • 1)

/-- The phase-free Lagrange product over a specified ordered list of ranks. -/
def orderedProjectorProduct (i : Fin (Fintype.card ι))
    (ranks : List (Fin (Fintype.card ι))) (A : HermitianMatrix ι) : Matrix ι ι ℂ :=
  (ranks.map (fun j => orderedProjectorFactor i j A)).prod

/-- The phase-free algebraic Lagrange product, using each rank once. -/
def orderedProjector (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) : Matrix ι ι ℂ :=
  orderedProjectorProduct i (List.finRange (Fintype.card ι)) A

/-- Every Lagrange factor is Borel measurable, including at eigenvalue collisions. -/
theorem measurable_orderedProjectorFactor (i j : Fin (Fintype.card ι)) :
    Measurable (orderedProjectorFactor (ι := ι) i j) := by
  classical
  unfold orderedProjectorFactor
  split_ifs
  · exact measurable_const
  · apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro y
    change Measurable (fun A : HermitianMatrix ι =>
      (((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ)⁻¹) *
        (A.val x y - (orderedEigenvalue A j : ℂ) * (1 : Matrix ι ι ℂ) x y))
    have hi := Complex.continuous_ofReal.measurable.comp (measurable_orderedEigenvalue i)
    have hj := Complex.continuous_ofReal.measurable.comp (measurable_orderedEigenvalue j)
    have he : Measurable (fun A : HermitianMatrix ι => A.val x y) :=
      (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_subtype_coe)
    simpa only [Complex.ofReal_sub, Function.comp_apply, Pi.sub_apply, Pi.mul_apply, Pi.inv_apply] using!
      (hi.sub hj).inv.mul (he.sub (hj.mul measurable_const))

/-- Ordered finite products of matrix-valued Borel maps are Borel measurable. -/
theorem measurable_orderedProjectorProduct (i : Fin (Fintype.card ι))
    (ranks : List (Fin (Fintype.card ι))) :
    Measurable (orderedProjectorProduct (ι := ι) i ranks) := by
  induction ranks with
  | nil => exact measurable_const
  | cons j ranks ih =>
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro y
    change Measurable (fun A : HermitianMatrix ι =>
      ∑ k, orderedProjectorFactor i j A x k * orderedProjectorProduct i ranks A k y)
    apply Finset.measurable_sum
    intro k _
    exact ((measurable_pi_apply k).comp ((measurable_pi_apply x).comp
      (measurable_orderedProjectorFactor i j))).mul
        ((measurable_pi_apply y).comp ((measurable_pi_apply k).comp ih))

/-- The phase-free algebraic Lagrange product is Borel measurable. -/
theorem measurable_orderedProjector (i : Fin (Fintype.card ι)) :
    Measurable (orderedProjector (ι := ι) i) :=
  measurable_orderedProjectorProduct i _

/-- Scalar action of a Lagrange factor on another ordered eigenline. -/
def orderedProjectorScalar (i j r : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) : ℂ :=
  if j = i then 1 else
    (((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ)⁻¹) *
      ((orderedEigenvalue A r : ℂ) - (orderedEigenvalue A j : ℂ))

/-- Exact factor action on the current orthonormal eigenbasis; no simplicity
is required for this polynomial identity. -/
theorem orderedProjectorFactor_mulVec (i j r : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) :
    (orderedProjectorFactor i j A).mulVec
        (BlockBand.Foundations.Spectral.increasingEigenvector A.property r) =
      orderedProjectorScalar i j r A •
        BlockBand.Foundations.Spectral.increasingEigenvector A.property r := by
  classical
  by_cases hji : j = i
  · simp [orderedProjectorFactor, orderedProjectorScalar, hji, Matrix.one_mulVec]
  · simp only [orderedProjectorFactor, orderedProjectorScalar, hji, ite_false,
      Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [BlockBand.Foundations.Spectral.mulVec_increasingEigenvector,
      ← sub_smul, smul_smul]
    rfl

/-- Exact finite-product action on every increasing eigenbasis vector. -/
theorem orderedProjectorProduct_mulVec (i r : Fin (Fintype.card ι))
    (ranks : List (Fin (Fintype.card ι))) (A : HermitianMatrix ι) :
    (orderedProjectorProduct i ranks A).mulVec
        (BlockBand.Foundations.Spectral.increasingEigenvector A.property r) =
      (ranks.map (fun j => orderedProjectorScalar i j r A)).prod •
        BlockBand.Foundations.Spectral.increasingEigenvector A.property r := by
  induction ranks with
  | nil => simp [orderedProjectorProduct, Matrix.one_mulVec]
  | cons j ranks ih =>
    simp only [orderedProjectorProduct, List.map_cons, List.prod_cons,
      ← Matrix.mulVec_mulVec]
    change _ = _ at ih
    dsimp only [orderedProjectorProduct] at ih
    rw [ih, Matrix.mulVec_smul, orderedProjectorFactor_mulVec, smul_smul]
    rw [mul_comm]

/-- On distinct increasing eigenvalues the scalar product selects exactly
one rank (deterministic simplicity hypothesis). -/
theorem orderedProjectorScalar_prod (i r : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    ((List.finRange (Fintype.card ι)).map
      (fun j => orderedProjectorScalar i j r A)).prod = if r = i then 1 else 0 := by
  classical
  by_cases hri : r = i
  · subst r
    simp only [ite_true]
    apply List.prod_eq_one
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    by_cases hji : j = i
    · simp [orderedProjectorScalar, hji]
    · have hne : ((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr (fun h => hji (hsimple h).symm)
      simpa [orderedProjectorScalar, hji, Complex.ofReal_sub] using inv_mul_cancel₀ hne
  · simp only [hri, ite_false]
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨r, by simp, ?_⟩
    simp [orderedProjectorScalar, hri]

/-- The measurable phase-free product acts as the one-rank projection on the
current complete orthonormal eigenbasis when eigenvalues are distinct. -/
theorem orderedProjector_mulVec (i r : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    (orderedProjector i A).mulVec
        (BlockBand.Foundations.Spectral.increasingEigenvector A.property r) =
      (if r = i then (1 : ℂ) else 0) •
        BlockBand.Foundations.Spectral.increasingEigenvector A.property r := by
  unfold orderedProjector
  rw [orderedProjectorProduct_mulVec, orderedProjectorScalar_prod i r A hsimple]

/-- An exact matrix identity can be checked on the complete current ordered
orthonormal eigenbasis, independently of spectral simplicity. -/
theorem matrix_eq_of_mulVec_increasingEigenvector_eq (A : HermitianMatrix ι)
    (P Q : Matrix ι ι ℂ)
    (h : ∀ r : Fin (Fintype.card ι),
      P.mulVec (BlockBand.Foundations.Spectral.increasingEigenvector A.property r) =
      Q.mulVec (BlockBand.Foundations.Spectral.increasingEigenvector A.property r)) :
    P = Q := by
  let U := A.property.eigenvectorUnitary
  have hm : P * (U : Matrix ι ι ℂ) = Q * (U : Matrix ι ι ℂ) := by
    ext x y
    have hv : BlockBand.Foundations.Spectral.increasingEigenvector A.property
        (BlockBand.Foundations.Spectral.increasingIndex.symm y) =
        fun z => (U : Matrix ι ι ℂ) z y := by
      simp only [BlockBand.Foundations.Spectral.increasingEigenvector,
        BlockBand.Foundations.Spectral.increasingEigenbasis_apply,
        Equiv.apply_symm_apply, U, Matrix.IsHermitian.eigenvectorUnitary_apply]
    have he := congrFun (h (BlockBand.Foundations.Spectral.increasingIndex.symm y)) x
    rw [hv] at he
    exact he
  have he := congrArg (fun M : Matrix ι ι ℂ => M * star (U : Matrix ι ι ℂ)) hm
  simpa only [Matrix.mul_assoc, Unitary.mul_star_self_of_mem U.property, Matrix.mul_one] using he

/-- On simple spectrum the measurable polynomial equals the phase-free
outer product of the exact current ordered normalized eigenvector. -/
theorem orderedProjector_eq_outerProduct (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    orderedProjector i A =
      fun x y => BlockBand.Foundations.Spectral.increasingEigenvector A.property i x *
        starRingEnd ℂ (BlockBand.Foundations.Spectral.increasingEigenvector A.property i y) := by
  apply matrix_eq_of_mulVec_increasingEigenvector_eq A
  intro r
  rw [orderedProjector_mulVec i r A hsimple]
  ext x
  change (if r = i then (1 : ℂ) else 0) *
      BlockBand.Foundations.Spectral.increasingEigenvector A.property r x =
    ∑ y, (BlockBand.Foundations.Spectral.increasingEigenvector A.property i x *
      starRingEnd ℂ (BlockBand.Foundations.Spectral.increasingEigenvector A.property i y)) *
      BlockBand.Foundations.Spectral.increasingEigenvector A.property r y
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, BlockBand.Foundations.Spectral.increasingEigenvector_orthonormal]
  by_cases hri : r = i
  · simp [hri]
  · simp [hri, Ne.symm hri]

end BlockBand.Model.Construction
