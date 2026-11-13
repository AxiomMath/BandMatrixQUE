module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicAmbientCompressionPolynomial

/-!
# Fixed endpoints of the full ambient public compression

This module supplies the deterministic common-scalar witness for the full
public-coordinate endpoint polynomial, then transports its null set through
the heterogeneous public scalar law.  The witness varies every block diagonal
coordinate by the same real scalar; it does not condition on a selected block.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory MvPolynomial
open scoped ComplexOrder BigOperators

/-- Public scalar coordinates giving the common scalar matrix `s I` in every
block: diagonal coordinates are `s`, and strict-upper coordinates vanish. -/
def publicCommonScalarSample {k : ℕ} (d : Fin k → ℕ) (s : ℝ) :
    BlockGUE.PublicScalarSample d := fun q =>
  match q.2 with
  | .inl _ => s
  | .inr _ => 0

@[simp] theorem publicBlockCoordinates_publicCommonScalarSample {k : ℕ}
    (d : Fin k → ℕ) (s : ℝ) (i : Fin k) (c : HermitianCoordinate (d i)) :
    BlockGUE.publicBlockCoordinates (publicCommonScalarSample d s) i
        (hermitianCoordinateEquivFin (d i) c) =
      match c with
      | .inl _ => s
      | .inr _ => 0 := by
  rcases c with c | c <;> simp [BlockGUE.publicBlockCoordinates, publicCommonScalarSample]

/-- The common-scalar public coordinates reconstruct the full ambient scalar
matrix `s I`. -/
theorem publicBlockDiagonal_publicCommonScalarSample {k : ℕ}
    (d : Fin k → ℕ) (s : ℝ) :
    (BlockGUE.publicBlockDiagonal
      (BlockGUE.publicBlocksFromScalars (publicCommonScalarSample d s))).1 =
      (s : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ) := by
  ext p q
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  by_cases hij : i = j
  · subst j
    simp only [BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
      BlockGUE.publicBlocksFromScalars,
      hermitianGUEBlock, hermitianOfFinCoordinates, hermitianOfCoordinates,
      hermitianMatrixOfCoordinates, hermitianUpperEntry, Matrix.smul_apply]
    by_cases hpq : p = q
    · subst q
      simp
    · simp [hpq]
  · simp [BlockGUE.publicBlockDiagonal, BlockGUE.publicBlockDiagonalRaw,
      Matrix.smul_apply, hij]

/-- A sufficiently large common real scalar makes the full endpoint
matrix positive definite, hence its adjugate quadratic form in every unit
vector is nonzero.  This is the deterministic scalar-pencil witness. -/
theorem exists_commonScalar_adjugate_quadratic_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₀ : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (e : ℝ) :
    ∃ s : ℝ,
      (A₀.1 + ((s - e : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0 ∧
      star (WithLp.ofLp u) ⬝ᵥ
        ((A₀.1 + ((s - e : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).adjugate *ᵥ
          WithLp.ofLp u) ≠ 0 := by
  let c : ℝ := (∑ i, |A₀.2.eigenvalues i|) + 1
  let U : Matrix ι ι ℂ := A₀.2.eigenvectorUnitary
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (fun i => (RCLike.ofReal (A₀.2.eigenvalues i + c) : ℂ))
  have hc (i : ι) : 0 < A₀.2.eigenvalues i + c := by
    have hle : |A₀.2.eigenvalues i| ≤ ∑ j, |A₀.2.eigenvalues j| := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hneg : -|A₀.2.eigenvalues i| ≤ A₀.2.eigenvalues i := neg_abs_le _
    dsimp [c]
    linarith
  have hD : D.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact (RCLike.ofReal_pos (K := ℂ)).2 (hc i)
  have hU : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem A₀.2.eigenvectorUnitary.property
  have hUunit : IsUnit U := by
    apply isUnit_iff_exists.mpr
    exact ⟨Uᴴ, hU, Unitary.star_mul_self_of_mem
      A₀.2.eigenvectorUnitary.property⟩
  have hshape :
      A₀.1 + (c : ℂ) • (1 : Matrix ι ι ℂ) = U * D * Uᴴ := by
    have hA : A₀.1 = U *
        Matrix.diagonal (RCLike.ofReal ∘ A₀.2.eigenvalues) * Uᴴ := by
      rw [show Uᴴ = star U from rfl]
      simpa only [U, Unitary.conjStarAlgAut_apply] using A₀.2.spectral_theorem
    have hdiag : D =
        Matrix.diagonal (RCLike.ofReal ∘ A₀.2.eigenvalues) +
          (c : ℂ) • (1 : Matrix ι ι ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D]
      · simp [D, hij]
    rw [hdiag, Matrix.mul_add, Matrix.add_mul, ← hA]
    have hscalar : U * ((c : ℂ) • (1 : Matrix ι ι ℂ)) * Uᴴ =
        (c : ℂ) • (1 : Matrix ι ι ℂ) := by
      calc
        U * ((c : ℂ) • (1 : Matrix ι ι ℂ)) * Uᴴ =
            (c : ℂ) • (U * Uᴴ) := by
              rw [Matrix.mul_smul, Matrix.smul_mul, mul_one]
        _ = _ := by rw [hU]
    rw [hscalar]
  let M : Matrix ι ι ℂ := A₀.1 + (c : ℂ) • (1 : Matrix ι ι ℂ)
  have hM : M.PosDef := by
    rw [show M = U * D * Uᴴ by exact hshape]
    apply hD.mul_mul_conjTranspose_same
    exact Matrix.vecMul_injective_iff_isUnit.mpr hUunit
  have hu0 : WithLp.ofLp u ≠ 0 := by
    intro h
    have hn := congrArg norm h
    simp only [norm_zero] at hn
    have : ‖u‖ = 0 := by simpa using hn
    linarith
  have hqinv : star (WithLp.ofLp u) ⬝ᵥ
      (M⁻¹ *ᵥ WithLp.ofLp u) ≠ 0 :=
    ne_of_gt (hM.inv.dotProduct_mulVec_pos hu0)
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hinv := Matrix.nonsing_inv_apply M hdet
  have hqadj : star (WithLp.ofLp u) ⬝ᵥ
      (M.adjugate *ᵥ WithLp.ofLp u) ≠ 0 := by
    intro hz
    apply hqinv
    rw [hinv, Matrix.smul_mulVec, dotProduct_smul, hz]
    simp
  refine ⟨e + c, ?_, ?_⟩
  · have : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdet
    simpa [M] using this
  · simpa [M] using hqadj

/-- Determinant polynomial of the full public deformation at a fixed endpoint. -/
def publicEndpointDetPolynomial {k : ℕ} {d : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (e : ℝ) :
    MvPolynomial (BlockGUE.PublicScalarIndex d) ℂ :=
  (publicUniversalEndpointMatrix A₀ e).det

/-- Evaluation of the full endpoint determinant polynomial. -/
theorem eval_publicEndpointDetPolynomial {k : ℕ} {d : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (e : ℝ)
    (x : BlockGUE.PublicScalarSample d) :
    MvPolynomial.eval (fun c => (x c : ℂ))
        (publicEndpointDetPolynomial A₀ e) =
      ((publicBlockDeformation A₀ (BlockGUE.publicBlocksFromScalars x)).1 -
        (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).det := by
  rw [publicEndpointDetPolynomial, RingHom.map_det, RingHom.mapMatrix_apply]
  have hn := map_eval_publicUniversalNoise d x
  simp only [publicUniversalEndpointMatrix, publicBlockDeformation]
  congr 1
  ext i j
  have hnij := congrFun (congrFun hn i) j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, map_add, MvPolynomial.eval_C]
  change A₀.1 i j - (e : ℂ) * (1 : Matrix _ _ ℂ) i j +
      (publicUniversalNoise d).map (MvPolynomial.eval fun c => (x c : ℂ)) i j =
    A₀.1 i j +
      (BlockGUE.publicBlockDiagonal (BlockGUE.publicBlocksFromScalars x)).1 i j -
      (e : ℂ) * (1 : Matrix _ _ ℂ) i j
  rw [hnij]
  ring

/-- Under the heterogeneous full public scalar product law, both endpoint
polynomials avoid zero almost surely. -/
theorem ae_publicScalar_fullEndpoint_det_and_adjugate_ne_zero
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ i, 0 < d i)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (u : EuclideanSpace ℂ (BlockGUE.Index d)) (hu : ‖u‖ = 1) (e : ℝ) :
    ∀ᵐ x ∂BlockGUE.publicScalarMeasure d hd,
      ((publicBlockDeformation A₀ (BlockGUE.publicBlocksFromScalars x)).1 -
        (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).det ≠ 0 ∧
      star (WithLp.ofLp u) ⬝ᵥ
        (((publicBlockDeformation A₀ (BlockGUE.publicBlocksFromScalars x)).1 -
          (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).adjugate *ᵥ
            WithLp.ofLp u) ≠ 0 := by
  obtain ⟨s, hsdet, hsq⟩ :=
    exists_commonScalar_adjugate_quadratic_ne_zero A₀ u hu e
  let x₀ := publicCommonScalarSample d s
  have hmatrix :
      (publicBlockDeformation A₀ (BlockGUE.publicBlocksFromScalars x₀)).1 -
          (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ) =
        A₀.1 + ((s - e : ℝ) : ℂ) • 1 := by
    simp only [publicBlockDeformation, x₀,
      publicBlockDiagonal_publicCommonScalarSample]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    push_cast
    ring
  have hdet := ae_eval_ne_zero_publicScalarMeasure d hd
    (publicEndpointDetPolynomial A₀ e) x₀ (by
      rw [eval_publicEndpointDetPolynomial, hmatrix]
      exact hsdet)
  have hq := ae_eval_ne_zero_publicScalarMeasure d hd
    (publicAmbientCompressionEndpointPolynomial A₀ u e) x₀ (by
      rw [eval_publicAmbientCompressionEndpointPolynomial, hmatrix]
      exact hsq)
  filter_upwards [hdet, hq] with x hxdet hxq
  rw [eval_publicEndpointDetPolynomial] at hxdet
  rw [eval_publicAmbientCompressionEndpointPolynomial] at hxq
  exact ⟨hxdet, hxq⟩

/-- Full-block-law form of the fixed-endpoint determinant and adjugate
quadratic nullity. -/
theorem ae_publicBlock_fullEndpoint_det_and_adjugate_ne_zero
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ i, 0 < d i)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (u : EuclideanSpace ℂ (BlockGUE.Index d)) (hu : ‖u‖ = 1) (e : ℝ) :
    ∀ᵐ G ∂BlockGUE.publicBlockProductMeasure d hd,
      ((publicBlockDeformation A₀ G).1 -
        (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).det ≠ 0 ∧
      star (WithLp.ofLp u) ⬝ᵥ
        (((publicBlockDeformation A₀ G).1 -
          (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).adjugate *ᵥ
            WithLp.ofLp u) ≠ 0 := by
  let f : BlockGUE.PublicBlockSample d → ℂ := fun G =>
    ((publicBlockDeformation A₀ G).1 -
      (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).det
  let q : BlockGUE.PublicBlockSample d → ℂ := fun G =>
    star (WithLp.ofLp u) ⬝ᵥ
      (((publicBlockDeformation A₀ G).1 -
        (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)).adjugate *ᵥ
          WithLp.ofLp u)
  let M : BlockGUE.PublicBlockSample d →
      Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ := fun G =>
    (publicBlockDeformation A₀ G).1 -
      (e : ℂ) • (1 : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
  have hbase : Measurable (fun G : BlockGUE.PublicBlockSample d =>
      (publicBlockDeformation A₀ G).1) :=
    measurable_subtype_coe.comp (measurable_publicBlockDeformation d A₀)
  have hM : Measurable M := by
    rw [Matrix.measurable_iff]
    intro i j
    exact (Matrix.measurable_iff.mp hbase i j).sub measurable_const
  have hf : Measurable f := by
    change Measurable ((fun A : Matrix (BlockGUE.Index d)
      (BlockGUE.Index d) ℂ => A.det) ∘ M)
    exact continuous_id.matrix_det.measurable.comp hM
  have hquad : Continuous (fun A :
      Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ =>
      star (WithLp.ofLp u) ⬝ᵥ (A.adjugate *ᵥ WithLp.ofLp u)) := by
    fun_prop
  have hq : Measurable q := by
    change Measurable ((fun A : Matrix (BlockGUE.Index d)
      (BlockGUE.Index d) ℂ => star (WithLp.ofLp u) ⬝ᵥ
        (A.adjugate *ᵥ WithLp.ofLp u)) ∘ M)
    exact hquad.measurable.comp hM
  have hE : MeasurableSet {G : BlockGUE.PublicBlockSample d |
      f G ≠ 0 ∧ q G ≠ 0} :=
    (hf (measurableSet_singleton 0)).compl.inter
      (hq (measurableSet_singleton 0)).compl
  rw [← BlockGUE.map_publicBlocksFromScalars_eq_publicBlockProductMeasure d hd]
  rw [ae_map_iff]
  · simpa only [f, q] using
      ae_publicScalar_fullEndpoint_det_and_adjugate_ne_zero d hd A₀ u hu e
  · exact ((BlockGUE.measurable_publicBlocks_reconstruction d).comp
      (BlockGUE.measurable_publicBlockCoordinates_fromScalars d)).aemeasurable
  · exact hE

/-- Nonzero full determinant and adjugate quadratic form force the
codimension-one compression to avoid the fixed endpoint. -/
theorem compressionRestriction_ne_endpoint_of_det_adjugate_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (e : ℝ)
    (hdet : (K.1 - (e : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0)
    (hq : star (WithLp.ofLp u) ⬝ᵥ
      ((K.1 - (e : ℂ) • (1 : Matrix ι ι ℂ)).adjugate *ᵥ
        WithLp.ofLp u) ≠ 0) :
    ∀ x : (ℂ ∙ u)ᗮ,
      compressionRestriction K u hu x = (e : ℂ) • x → x = 0 := by
  let M : Matrix ι ι ℂ := K.1 - (e : ℂ) • (1 : Matrix ι ι ℂ)
  have hdetunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hinvleft : M⁻¹ * M = 1 := nonsing_inv_mul M hdetunit
  have hqinvraw : star (WithLp.ofLp u) ⬝ᵥ
      (M⁻¹ *ᵥ WithLp.ofLp u) ≠ 0 := by
    rw [Matrix.inv_def, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero hdet) hq
  intro x hx
  have hxorth : inner ℂ u (x : EuclideanSpace ℂ ι) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  have hcomp := congrArg Subtype.val hx
  change Matrix.toEuclideanLin (orthogonalCompression K u : Matrix ι ι ℂ)
      (x : EuclideanSpace ℂ ι) = (e : ℂ) • (x : EuclideanSpace ℂ ι) at hcomp
  have hP : Matrix.toEuclideanLin (orthogonalProjector u)
      (x : EuclideanSpace ℂ ι) = x :=
    orthogonalProjector_apply_of_inner_eq_zero u x hxorth
  have hcomp' : Matrix.toEuclideanLin K.1 x -
      inner ℂ u (Matrix.toEuclideanLin K.1 x) • u = (e : ℂ) • x := by
    change Matrix.toEuclideanLin
      (orthogonalProjector u * K.1 * (orthogonalProjector u)ᴴ) x =
        (e : ℂ) • x at hcomp
    rw [orthogonalProjector_conjTranspose] at hcomp
    let b := (EuclideanSpace.basisFun ι ℂ).toBasis
    change Matrix.toLin b b
      (orthogonalProjector u * K.1 * orthogonalProjector u) x =
        (e : ℂ) • x at hcomp
    rw [Matrix.toLin_mul_apply b b b, Matrix.toLin_mul_apply b b b] at hcomp
    change Matrix.toEuclideanLin (orthogonalProjector u)
      (Matrix.toEuclideanLin K.1
        (Matrix.toEuclideanLin (orthogonalProjector u) x)) = (e : ℂ) • x at hcomp
    rw [hP, toEuclideanLin_orthogonalProjector_apply] at hcomp
    exact hcomp
  let c : ℂ := inner ℂ u (Matrix.toEuclideanLin K.1 x)
  have hcompraw := congrArg WithLp.ofLp hcomp'
  have hMx : M *ᵥ WithLp.ofLp (x : EuclideanSpace ℂ ι) =
      c • WithLp.ofLp u := by
    dsimp only [M, c]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change K.1 *ᵥ WithLp.ofLp (x : EuclideanSpace ℂ ι) -
      (e : ℂ) • WithLp.ofLp (x : EuclideanSpace ℂ ι) =
      inner ℂ u (Matrix.toEuclideanLin K.1 x) • WithLp.ofLp u
    change K.1 *ᵥ WithLp.ofLp (x : EuclideanSpace ℂ ι) -
      inner ℂ u (Matrix.toEuclideanLin K.1 x) • WithLp.ofLp u =
      (e : ℂ) • WithLp.ofLp (x : EuclideanSpace ℂ ι) at hcompraw
    apply sub_eq_iff_eq_add.mpr
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hcompraw)
  have hxraw : WithLp.ofLp (x : EuclideanSpace ℂ ι) =
      c • (M⁻¹ *ᵥ WithLp.ofLp u) := by
    calc
      WithLp.ofLp (x : EuclideanSpace ℂ ι) =
          (1 : Matrix ι ι ℂ) *ᵥ WithLp.ofLp x := by rw [Matrix.one_mulVec]
      _ = (M⁻¹ * M) *ᵥ WithLp.ofLp x := by rw [hinvleft]
      _ = M⁻¹ *ᵥ (M *ᵥ WithLp.ofLp x) := by rw [Matrix.mulVec_mulVec]
      _ = M⁻¹ *ᵥ (c • WithLp.ofLp u) := by rw [hMx]
      _ = c • (M⁻¹ *ᵥ WithLp.ofLp u) := by rw [Matrix.mulVec_smul]
  have hxrepr : (x : EuclideanSpace ℂ ι) =
      c • Matrix.toEuclideanLin M⁻¹ u := by
    exact congrArg (WithLp.toLp 2) hxraw
  have hqinv : inner ℂ u (Matrix.toEuclideanLin M⁻¹ u) ≠ 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      hqinvraw
  have hc0 : c = 0 := by
    have hi := congrArg (inner ℂ u) hxrepr
    rw [hxorth, inner_smul_right] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_right hqinv
  apply Subtype.ext
  rw [hxrepr, hc0, zero_smul]
  rfl

/-- Deterministic endpoint-count form: the ambient compression has only its
single forced zero and the compression does not hit `e`. -/
theorem eigenCount_compressHermitian_singleton_of_det_adjugate_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (e : ℝ)
    (hdet : (K.1 - (e : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0)
    (hq : star (WithLp.ofLp u) ⬝ᵥ
      ((K.1 - (e : ℂ) • (1 : Matrix ι ι ℂ)).adjugate *ᵥ
        WithLp.ofLp u) ≠ 0) :
    eigenCount (compressHermitian K u) {e} = if e = 0 then 1 else 0 := by
  let hC := compressionRestriction_isSymmetric K u hu
  let hdim := finrank_spanOrthogonal_eq_card_sub_one u hu
  have havoid := compressionRestriction_ne_endpoint_of_det_adjugate_ne_zero
    K u hu e hdet hq
  have hnone : ∀ k : Fin (Fintype.card ι - 1),
      hC.eigenvalues hdim k ≠ e := by
    intro k hk
    let x : (ℂ ∙ u)ᗮ := hC.eigenvectorBasis hdim k
    have hxnorm : ‖x‖ = 1 := (hC.eigenvectorBasis hdim).norm_eq_one k
    have heig := hC.apply_eigenvectorBasis hdim k
    have heig' : compressionRestriction K u hu x = (e : ℂ) • x := by
      change compressionRestriction K u hu x =
        (hC.eigenvalues hdim k : ℂ) • x at heig
      rw [hk] at heig
      exact heig
    have hx0 : x = 0 := havoid x heig'
    rw [hx0, norm_zero] at hxnorm
    norm_num at hxnorm
  rw [eigenCount_compressHermitian_eq_restriction K u hu]
  have hcount : finiteSpectralCount (fun k : Fin (Fintype.card ι - 1) =>
      hC.eigenvalues hdim k) ({e} : Set ℝ) = 0 := by
    rw [finiteSpectralCount]
    simp only [Set.mem_singleton_iff]
    simp [hnone]
  rw [hcount, zero_add]
  simp only [Set.indicator_apply, Set.mem_singleton_iff]
  by_cases he : e = 0
  · simp [he]
  · have h0e : ¬(0 : ℝ) = e := fun h => he h.symm
    simp [he, h0e]

/-- Fixed-endpoint ambient-compression count under the full public
block product law.  The sole possible endpoint atom is the canonical forced
zero, counted once. -/
theorem ae_publicBlock_compressHermitian_singleton_count
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ i, 0 < d i)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (u : EuclideanSpace ℂ (BlockGUE.Index d)) (hu : ‖u‖ = 1) (e : ℝ) :
    ∀ᵐ G ∂BlockGUE.publicBlockProductMeasure d hd,
      eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {e} =
        if e = 0 then 1 else 0 := by
  filter_upwards [ae_publicBlock_fullEndpoint_det_and_adjugate_ne_zero
    d hd A₀ u hu e] with G hG
  exact eigenCount_compressHermitian_singleton_of_det_adjugate_ne_zero
    (publicBlockDeformation A₀ G) u hu e hG.1 hG.2

/-- The exact paired fixed-endpoint hypothesis consumed by
`MinamiFullCompressionFatou`: both endpoints of the fixed target `Icc a b`
are null for the full compression, apart from its canonical zero. -/
theorem ae_publicBlock_compressHermitian_fixedEndpoints
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ i, 0 < d i)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (u : EuclideanSpace ℂ (BlockGUE.Index d)) (hu : ‖u‖ = 1)
    (a b : ℝ) :
    ∀ᵐ G ∂BlockGUE.publicBlockProductMeasure d hd,
      eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {a} =
          (if a = 0 then 1 else 0) ∧
        eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {b} =
          (if b = 0 then 1 else 0) := by
  filter_upwards [ae_publicBlock_compressHermitian_singleton_count
      d hd A₀ u hu a,
    ae_publicBlock_compressHermitian_singleton_count
      d hd A₀ u hu b] with G ha hb
  exact ⟨ha, hb⟩

end PSSSNative.BlockBand.PSSS
