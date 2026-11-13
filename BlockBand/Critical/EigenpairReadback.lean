module

public import BlockBand.Critical.FiniteReadback
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant-source readback at a finite simple eigenpair

This is the deterministic finite step in the first step of the joint recovery theorem
and of the root-mark extractor: at a simple eigenvalue, the source derivatives of the
normalized determinant recover the quadratic masses of the normalized eigenvector.
The complex finite matrix can have any finite index
set, so this proof is independent of ring parity and Gaussian variance law.
The spectral data are an orthonormal diagonalization, not an assumed
adjugate/projector formula or a derivative identity. Source matrices need not
commute with the matrix or with each other. The complete finite quotient,
W⁻² source scale, Q0=I, and negative zero/unfolding sign are retained.
No probability law, asymptotic estimate or analytic recovery constructor is
assumed by these finite algebra/calculus lemmas.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace BlockBand.Critical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cofactor expansion for an arbitrary replaced row, proved from determinant
row multilinearity; no adjugate-projector identity is assumed. -/
theorem det_updateRow_eq_sum_adjugate (A : Matrix ι ι ℂ) (k : ι) (v : ι → ℂ) :
    (A.updateRow k v).det = ∑ j, v j * A.adjugate j k := by
  classical
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  calc
    (A.updateRow k v).det = (A.updateRow k (∑ j, v j • Pi.single j (1 : ℂ))).det :=
      congrArg (fun w => (A.updateRow k w).det) hv
    _ = ∑ j, (A.updateRow k (v j • Pi.single j (1 : ℂ))).det := by
      change (Matrix.detRowAlternating (R := ℂ) (n := ι))
          (Function.update (fun i j => A i j) k (∑ j, v j • Pi.single j (1 : ℂ))) =
        ∑ j, (Matrix.detRowAlternating (R := ℂ) (n := ι))
          (Function.update (fun i j => A i j) k (v j • Pi.single j (1 : ℂ)))
      exact (Matrix.detRowAlternating (R := ℂ) (n := ι)).map_update_sum Finset.univ k
        (fun j => v j • Pi.single j (1 : ℂ)) (fun i j => A i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.det_updateRow_smul, ← Matrix.adjugate_apply]

/-- A diagonal replaced-row determinant retains exactly its diagonal source
entry, even if the source row has arbitrary off-diagonal entries. -/
theorem det_diagonal_updateRow (d : ι → ℂ) (k : ι) (v : ι → ℂ) :
    ((Matrix.diagonal d).updateRow k v).det =
      v k * ∏ j ∈ Finset.univ.erase k, d j := by
  rw [det_updateRow_eq_sum_adjugate, Matrix.adjugate_diagonal]
  simp [Matrix.diagonal_apply, mul_ite]

/-- Complex differentiability of an arbitrary finite affine determinant line,
derived from the finite entire determinant proof rather than Jacobi's formula. -/
theorem differentiable_det_affineLine (A B : Matrix ι ι ℂ) :
    Differentiable ℂ (fun t : ℂ => (A + t • B).det) := by
  have h := (differentiable_finiteCharacteristicDeterminant A
    (fun _ : Fin 1 => B) 1).comp
    (show Differentiable ℂ (fun t : ℂ => fun _ : Fin 1 => t) by fun_prop)
  simpa [Function.comp_def, finiteCharacteristicDeterminant, finiteCharacteristicPencil] using h

/-- Exact zero-row factorization of the determinant for any noncommuting
source direction. -/
theorem det_diagonal_add_smul_factor (d : ι → ℂ) (k : ι) (hd : d k = 0)
    (B : Matrix ι ι ℂ) (t : ℂ) :
    (Matrix.diagonal d + t • B).det =
      t * ((Matrix.diagonal d + t • B).updateRow k (B k)).det := by
  have hrow : (Matrix.diagonal d + t • B) k = t • B k := by
    ext j
    by_cases h : k = j
    · subst j
      simp [hd]
    · simp [Matrix.diagonal_apply_ne _ h]
  calc
    (Matrix.diagonal d + t • B).det =
        ((Matrix.diagonal d + t • B).updateRow k (t • B k)).det := by
      rw [← hrow, Matrix.updateRow_eq_self]
    _ = _ := Matrix.det_updateRow_smul _ _ _ _

/-- Complex derivative at a diagonal zero. The proof factors the
vanishing row and evaluates its cofactor; no determinant derivative or
adjugate projector is a supplied hypothesis. -/
theorem hasDerivAt_det_diagonal_add_smul (d : ι → ℂ) (k : ι) (hd : d k = 0)
    (B : Matrix ι ι ℂ) :
    HasDerivAt (fun t : ℂ => (Matrix.diagonal d + t • B).det)
      ((∏ j ∈ Finset.univ.erase k, d j) * B k k) 0 := by
  let A' := (Matrix.diagonal d).updateRow k (B k)
  let B' := B.updateRow k 0
  have hminor : ∀ t : ℂ,
      (Matrix.diagonal d + t • B).updateRow k (B k) = A' + t • B' := by
    intro t
    ext i j
    by_cases h : k = i
    · subst i
      simp [A', B']
    · simp [A', B', Matrix.updateRow_apply, Ne.symm h]
  have hg : Differentiable ℂ (fun t : ℂ =>
      ((Matrix.diagonal d + t • B).updateRow k (B k)).det) := by
    simp_rw [hminor]
    exact differentiable_det_affineLine A' B'
  have hmul := (hasDerivAt_id (x := (0 : ℂ))).mul
    (hg.differentiableAt.hasDerivAt)
  convert hmul using 1
  · ext t
    exact det_diagonal_add_smul_factor d k hd B t
  · simp only [id_eq, zero_mul, add_zero, one_mul, zero_smul]
    rw [det_diagonal_updateRow]
    ring

/-- A unitary change of basis preserves every finite determinant, singular or
nonsingular, with no scalar spectral weight. -/
theorem det_unitary_conjugation (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ).det = A.det :=
  Matrix.det_conj_of_mul_eq_one U.property.2 U.property.1

/-- Diagonal conjugated source entry is the normalized-column quadratic
source mass, with arbitrary noncommuting complex source `Q`. -/
theorem unitary_source_entry_eq_quadratic (U : Matrix.unitaryGroup ι ℂ)
    (Q : Matrix ι ι ℂ) (k : ι) :
    ((U : Matrix ι ι ℂ)ᴴ * Q * (U : Matrix ι ι ℂ)) k k =
      dotProduct (star (fun i => U i k)) (Q *ᵥ fun i => U i k) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Pi.star_apply]

/-- Exact determinant source derivative after a unitary change of
basis, valid for an arbitrary noncommuting source matrix. -/
theorem hasDerivAt_det_unitary_source (U : Matrix.unitaryGroup ι ℂ)
    (d : ι → ℂ) (k : ι) (hd : d k = 0) (Q : Matrix ι ι ℂ) :
    HasDerivAt (fun t : ℂ =>
      ((U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ + t • Q).det)
      ((∏ j ∈ Finset.univ.erase k, d j) *
        ((U : Matrix ι ι ℂ)ᴴ * Q * (U : Matrix ι ι ℂ)) k k) 0 := by
  have hu : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.2
  let B := (U : Matrix ι ι ℂ)ᴴ * Q * (U : Matrix ι ι ℂ)
  have hsource : (U : Matrix ι ι ℂ) * B * (U : Matrix ι ι ℂ)ᴴ = Q := by
    calc
      (U : Matrix ι ι ℂ) * B * (U : Matrix ι ι ℂ)ᴴ =
          ((U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ) * Q *
            ((U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ) := by
        dsimp only [B]
        noncomm_ring
      _ = Q := by rw [hu]; simp
  have hline : ∀ t : ℂ,
      (U : Matrix ι ι ℂ) * (Matrix.diagonal d + t • B) * (U : Matrix ι ι ℂ)ᴴ =
        (U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ + t • Q := by
    intro t
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hsource]
  convert hasDerivAt_det_diagonal_add_smul d k hd B using 1
  ext t
  rw [← hline, det_unitary_conjugation]

/-- The source coordinate derivative is the complex derivative
of the complete normalized determinant along its affine coordinate line. -/
def finiteSourcePartial {m : ℕ} (A : Matrix ι ι ℂ)
    (Q : Fin (m + 1) → Matrix ι ι ℂ) (W : ℕ) (hA : A.det ≠ 0)
    (z : ℂ) (a : Fin (m + 1)) : ℂ :=
  deriv (fun t : ℂ => physicalFiniteDeterminant A Q W hA
    (energySource z + Pi.single a t)) 0

omit [Fintype ι] in
/-- The coordinate-line pencil identity retains both the energy source and
an arbitrary spatial source without diagonalizing the latter. -/
theorem finiteCharacteristicPencil_sourceLine {m : ℕ}
    (A : Matrix ι ι ℂ) (Q : Fin (m + 1) → Matrix ι ι ℂ)
    (s z : ℂ) (hQ : Q 0 = 1) (a : Fin (m + 1)) (t : ℂ) :
    finiteCharacteristicPencil A Q s (energySource z + Pi.single a t) =
      A + s • (z • (1 : Matrix ι ι ℂ)) + t • (s • Q a) := by
  classical
  simp [finiteCharacteristicPencil, energySource, Pi.single_apply, add_smul,
    Finset.sum_add_distrib, smul_add, smul_smul, mul_comm, hQ, add_assoc]

/-- Exact negative zero-source shift at physical scale `W⁻²`. -/
theorem widthSourceScale_root_shift (W : ℕ) (hW : W ≠ 0) (lam E : ℂ) :
    widthSourceScale W * (-(W : ℂ)^2 * (lam-E)) = E-lam := by
  have hw : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW
  unfold widthSourceScale
  field_simp
  ring

/-- A unitary diagonalization shifts by exactly the same scalar on every
spectral entry; this constructs the root matrix from the matrix itself. -/
theorem unitary_diagonal_scalar_shift (U : Matrix.unitaryGroup ι ℂ)
    (lam : ι → ℂ) (e : ℂ) :
    (U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => lam j-e) * (U : Matrix ι ι ℂ)ᴴ =
      (U : Matrix ι ι ℂ) * Matrix.diagonal lam * (U : Matrix ι ι ℂ)ᴴ -
        e • (1 : Matrix ι ι ℂ) := by
  have hd : Matrix.diagonal (fun j => lam j-e) =
      Matrix.diagonal lam - e • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_one]
  have hu : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.2
  rw [hu]

set_option maxHeartbeats 800000 in
/-- Source partial at a diagonalized root matrix. The root-pencil
identity is an explicit hypothesis here; `finiteSourcePartial_eq_spectral_mass`
proves it from the matrix and the `W⁻²` zero source. -/
theorem finiteSourcePartial_eq_at_diagonalized_root {m : ℕ}
    (A : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ)
    (k : ι) (hd : d k = 0) (W : ℕ)
    (Q : Fin (m + 1) → Matrix ι ι ℂ) (hQ : Q 0 = 1)
    (hA : A.det ≠ 0) (z : ℂ)
    (hroot : A + widthSourceScale W • (z • (1 : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ)
    (a : Fin (m + 1)) :
    finiteSourcePartial A Q W hA z a =
      ((∏ j ∈ Finset.univ.erase k, d j) * widthSourceScale W *
        dotProduct (star (fun i => U i k)) ((Q a) *ᵥ fun i => U i k)) / A.det := by
  have hfun : (fun t : ℂ => physicalFiniteDeterminant A Q W hA
      (energySource z + Pi.single a t)) =
      fun t : ℂ =>
        (((U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ +
          t • (widthSourceScale W • Q a)).det) * A.det⁻¹ := by
    funext t
    unfold physicalFiniteDeterminant normalizedEntireDeterminant finiteCharacteristicDeterminant
    have hN : ((⟨A.det, hA⟩ : EntireDeterminantNormalizer) : ℂ) = A.det := rfl
    rw [hN, finiteCharacteristicPencil_sourceLine A Q (widthSourceScale W) z hQ,
      hroot, div_eq_mul_inv]
  have h := (hasDerivAt_det_unitary_source U d k hd (widthSourceScale W • Q a)).mul_const A.det⁻¹
  unfold finiteSourcePartial
  rw [hfun, h.deriv]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    unitary_source_entry_eq_quadratic]
  rw [div_eq_mul_inv]
  ring

set_option maxHeartbeats 800000 in
/-- Exact source partial derivative of the complete physical finite
quotient at an eigenvalue zero. Its coefficient is computed from a supplied
orthonormal diagonalization, including arbitrary noncommuting sources.
The denominator nonvanishing is deterministic at this finite matrix. -/
theorem finiteSourcePartial_eq_spectral_mass {m : ℕ}
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) (lam : ι → ℂ)
    (hdiag : H = (U : Matrix ι ι ℂ) * Matrix.diagonal lam * (U : Matrix ι ι ℂ)ᴴ)
    (k : ι) (E : ℂ) (W : ℕ) (hW : W ≠ 0)
    (Q : Fin (m + 1) → Matrix ι ι ℂ) (hQ : Q 0 = 1)
    (hA : (H-E • (1 : Matrix ι ι ℂ)).det ≠ 0) (a : Fin (m + 1)) :
    finiteSourcePartial (H-E • (1 : Matrix ι ι ℂ)) Q W hA
        (-(W : ℂ)^2 * (lam k-E)) a =
      ((∏ j ∈ Finset.univ.erase k, (lam j-lam k)) * widthSourceScale W *
        dotProduct (star (fun i => U i k)) ((Q a) *ᵥ fun i => U i k)) /
        (H-E • (1 : Matrix ι ι ℂ)).det := by
  let d : ι → ℂ := fun j => lam j-lam k
  let A := H-E • (1 : Matrix ι ι ℂ)
  let z := -(W : ℂ)^2 * (lam k-E)
  have hzero : A + widthSourceScale W • (z • (1 : Matrix ι ι ℂ)) =
      H-lam k • (1 : Matrix ι ι ℂ) := by
    dsimp only [A, z]
    rw [smul_smul, widthSourceScale_root_shift W hW]
    module
  have hroot : H-lam k • (1 : Matrix ι ι ℂ) =
      (U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ := by
    rw [unitary_diagonal_scalar_shift, ← hdiag]
  have hclosed : A + widthSourceScale W • (z • (1 : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ) * Matrix.diagonal d * (U : Matrix ι ι ℂ)ᴴ := hzero.trans hroot
  have hd : d k = 0 := sub_self _
  simpa only [A, d, z] using
    finiteSourcePartial_eq_at_diagonalized_root A U d k hd W Q hQ hA z hclosed a

set_option maxHeartbeats 800000 in
/-- The finite normalized determinant vanishes at the
negative eigenvalue source `-W²(lambda_k-E)`; this is an exact identity and
introduces no spectral Palm weight. -/
theorem physicalFiniteDeterminant_eigenvalue_zero {m : ℕ}
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) (lam : ι → ℂ)
    (hdiag : H = (U : Matrix ι ι ℂ) * Matrix.diagonal lam * (U : Matrix ι ι ℂ)ᴴ)
    (k : ι) (E : ℂ) (W : ℕ) (hW : W ≠ 0)
    (Q : Fin (m + 1) → Matrix ι ι ℂ) (hQ : Q 0 = 1)
    (hA : (H-E • (1 : Matrix ι ι ℂ)).det ≠ 0) :
    physicalFiniteDeterminant (H-E • (1 : Matrix ι ι ℂ)) Q W hA
      (energySource (-(W : ℂ)^2 * (lam k-E))) = 0 := by
  have hzero : H-E • (1 : Matrix ι ι ℂ) +
      widthSourceScale W • ((-(W : ℂ)^2 * (lam k-E)) • (1 : Matrix ι ι ℂ)) =
        H-lam k • (1 : Matrix ι ι ℂ) := by
    rw [smul_smul, widthSourceScale_root_shift W hW]
    module
  have hroot : H-lam k • (1 : Matrix ι ι ℂ) =
      (U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => lam j-lam k) *
        (U : Matrix ι ι ℂ)ᴴ := by
    rw [unitary_diagonal_scalar_shift, ← hdiag]
  change (finiteCharacteristicPencil (H-E • (1 : Matrix ι ι ℂ)) Q
    (widthSourceScale W) (energySource (-(W : ℂ)^2 * (lam k-E)))).det /
      (H-E • (1 : Matrix ι ι ℂ)).det = 0
  rw [finiteCharacteristicPencil_energySource _ Q _ _ hQ, hzero, hroot,
    det_unitary_conjugation, Matrix.det_diagonal]
  have hp : (∏ j, (lam j-lam k)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (sub_self (lam k))
  rw [hp, zero_div]

/-- Every column of the supplied unitary diagonalization has mass one,
proved from orthonormality rather than inserted as an eigenvector norm field. -/
theorem unitary_column_mass_one (U : Matrix.unitaryGroup ι ℂ) (k : ι) :
    dotProduct (star (fun i => U i k)) (fun i => U i k) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => A k k) U.property.1
  simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq,
    dotProduct, Pi.star_apply] using h

set_option maxHeartbeats 800000 in
/-- Full finite eigenpair readback: a simple eigenvalue gives a nonzero energy
partial, and every source ratio is its normalized-eigenvector quadratic
mass. Simplicity is required only for the selected eigenvalue. The source
matrices may be noncommuting. This is the deterministic step in the first step of
the joint recovery theorem, with source scale `W⁻²`, `Q0 = I` and the root sign. -/
theorem finite_eigenpair_source_readback {m : ℕ}
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) (lam : ι → ℂ)
    (hdiag : H = (U : Matrix ι ι ℂ) * Matrix.diagonal lam * (U : Matrix ι ι ℂ)ᴴ)
    (k : ι) (hsimple : ∀ j, j ≠ k → lam j ≠ lam k)
    (E : ℂ) (W : ℕ) (hW : W ≠ 0)
    (Q : Fin (m + 1) → Matrix ι ι ℂ) (hQ : Q 0 = 1)
    (hA : (H-E • (1 : Matrix ι ι ℂ)).det ≠ 0) :
    let A := H-E • (1 : Matrix ι ι ℂ)
    let z := -(W : ℂ)^2 * (lam k-E)
    finiteSourcePartial A Q W hA z 0 ≠ 0 ∧
      ∀ a : Fin (m + 1),
        finiteSourcePartial A Q W hA z a / finiteSourcePartial A Q W hA z 0 =
          dotProduct (star (fun i => U i k)) ((Q a) *ᵥ fun i => U i k) := by
  dsimp only
  have hprod : (∏ j ∈ Finset.univ.erase k, (lam j-lam k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (hsimple j (Finset.mem_erase.mp hj).1)
  have hs : widthSourceScale W ≠ 0 := by
    exact pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr hW))
  have henergy :
      finiteSourcePartial (H-E • (1 : Matrix ι ι ℂ)) Q W hA
          (-(W : ℂ)^2 * (lam k-E)) 0 =
        ((∏ j ∈ Finset.univ.erase k, (lam j-lam k)) * widthSourceScale W) /
          (H-E • (1 : Matrix ι ι ℂ)).det := by
    rw [finiteSourcePartial_eq_spectral_mass H U lam hdiag k E W hW Q hQ hA,
      hQ, Matrix.one_mulVec, unitary_column_mass_one, mul_one]
  have he : finiteSourcePartial (H-E • (1 : Matrix ι ι ℂ)) Q W hA
      (-(W : ℂ)^2 * (lam k-E)) 0 ≠ 0 := by
    rw [henergy]
    exact div_ne_zero (mul_ne_zero hprod hs) hA
  refine ⟨he, ?_⟩
  intro a
  rw [finiteSourcePartial_eq_spectral_mass H U lam hdiag k E W hW Q hQ hA, henergy]
  field_simp

/-- Physical Hermitian specialization: Mathlib's proved spectral theorem
constructs the orthonormal diagonalization, so the only spectral hypothesis is
simplicity of the selected eigenvalue. The displayed source ratio is the
quadratic mass of its orthonormal eigenvector. -/
theorem hermitian_eigenpair_source_readback {m : ℕ}
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (k : ι)
    (hsimple : ∀ j, j ≠ k → hH.eigenvalues j ≠ hH.eigenvalues k)
    (E : ℝ) (W : ℕ) (hW : W ≠ 0)
    (Q : Fin (m + 1) → Matrix ι ι ℂ) (hQ : Q 0 = 1)
    (hA : (H-(E : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0) :
    let A := H-(E : ℂ) • (1 : Matrix ι ι ℂ)
    let z := -(W : ℂ)^2 * ((hH.eigenvalues k : ℂ)-(E : ℂ))
    finiteSourcePartial A Q W hA z 0 ≠ 0 ∧
      ∀ a : Fin (m + 1),
        finiteSourcePartial A Q W hA z a / finiteSourcePartial A Q W hA z 0 =
          dotProduct (star ⇑(hH.eigenvectorBasis k))
            ((Q a) *ᵥ ⇑(hH.eigenvectorBasis k)) := by
  have hd : H = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) *
        (hH.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    exact hH.spectral_theorem
  have hs : ∀ j, j ≠ k → (hH.eigenvalues j : ℂ) ≠ (hH.eigenvalues k : ℂ) := by
    intro j hj
    exact_mod_cast hsimple j hj
  simpa only [Matrix.IsHermitian.eigenvectorUnitary_apply] using
    finite_eigenpair_source_readback H hH.eigenvectorUnitary
      (fun j => (hH.eigenvalues j : ℂ)) hd k hs (E : ℂ) W hW Q hQ hA

end BlockBand.Critical
