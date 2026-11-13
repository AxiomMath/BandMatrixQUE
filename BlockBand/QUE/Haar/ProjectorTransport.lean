module

public import BlockBand.Model.Construction.SpectralPhysical
public import BlockBand.QUE.Haar.CompactUnitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import BlockBand.Model.Observables

/-!
# Unitary transport of the selected eigenvector at a fixed rank

Unitary conjugation preserves the characteristic polynomial, each increasing eigenvalue and the
Lagrange rank projector; hence the site masses of the selected eigenvector at a fixed rank
transform by the unitary, with no phase choice, and every ordered orthonormal eigensystem has the
canonical site masses on simple spectrum.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open Matrix MeasureTheory
open scoped BigOperators Classical
open BlockBand.Model.Construction BlockBand.Foundations.Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary conjugation on Hermitian matrices. -/
def unitaryConjugate (U : Matrix.unitaryGroup ι ℂ) (A : HermitianMatrix ι) :
    HermitianMatrix ι :=
  ⟨(U : Matrix ι ι ℂ) * A.val * (U : Matrix ι ι ℂ)ᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose _ A.property⟩

/-- Unitary conjugation preserves the characteristic polynomial. -/
theorem charpoly_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ) (A : HermitianMatrix ι) :
    (unitaryConjugate U A).val.charpoly = A.val.charpoly := by
  change ((U : Matrix ι ι ℂ) * A.val * (U : Matrix ι ι ℂ)ᴴ).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]

/-- Unitary conjugation preserves each increasing eigenvalue. -/
theorem orderedEigenvalue_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ) (A : HermitianMatrix ι) :
    orderedEigenvalue (unitaryConjugate U A) = orderedEigenvalue A := by
  exact (increasingEigenvalue_eq_iff_charpoly_eq (unitaryConjugate U A).property A.property).2
    (charpoly_unitaryConjugate U A)

/-- Deterministic simple-spectrum rank injectivity is preserved by conjugation. -/
theorem injective_orderedEigenvalue_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ)
    (A : HermitianMatrix ι) (hs : Function.Injective (orderedEigenvalue A)) :
    Function.Injective (orderedEigenvalue (unitaryConjugate U A)) := by
  rw [orderedEigenvalue_unitaryConjugate]
  exact hs

/-- Every Lagrange factor transforms by unitary conjugation (also at collisions). -/
theorem orderedProjectorFactor_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ)
    (A : HermitianMatrix ι) (i j : Fin (Fintype.card ι)) :
    orderedProjectorFactor i j (unitaryConjugate U A) =
      Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (orderedProjectorFactor i j A) := by
  by_cases hji : j = i
  · simp [orderedProjectorFactor, hji]
  · simp only [orderedProjectorFactor, hji, ite_false,
      orderedEigenvalue_unitaryConjugate]
    rw [map_smul, map_sub, map_smul, map_one]
    rfl

/-- Covariance of the ordered finite product (no simple-spectrum hypothesis). -/
theorem orderedProjectorProduct_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ)
    (A : HermitianMatrix ι) (i : Fin (Fintype.card ι)) (ranks : List (Fin (Fintype.card ι))) :
    orderedProjectorProduct i ranks (unitaryConjugate U A) =
      Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (orderedProjectorProduct i ranks A) := by
  induction ranks with
  | nil => simp [orderedProjectorProduct]
  | cons j ranks ih =>
    simp only [orderedProjectorProduct, List.map_cons, List.prod_cons]
    change _ = _ at ih
    dsimp only [orderedProjectorProduct] at ih
    rw [map_mul, orderedProjectorFactor_unitaryConjugate, ih]

/-- Covariance of the rank projector under unitary conjugation. -/
theorem orderedProjector_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ)
    (A : HermitianMatrix ι) (i : Fin (Fintype.card ι)) :
    orderedProjector i (unitaryConjugate U A) =
      (U : Matrix ι ι ℂ) * orderedProjector i A * (U : Matrix ι ι ℂ)ᴴ := by
  exact orderedProjectorProduct_unitaryConjugate U A i _

/-- The outer product `v v*`. -/
def vectorProjector (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec v (star v)

/-- On simple spectrum, the rank projector is the outer product of the selected normalized
eigenvector. -/
theorem orderedProjector_eq_selectedVectorProjector (A : HermitianMatrix ι)
    (i : Fin (Fintype.card ι)) (hs : Function.Injective (orderedEigenvalue A)) :
    orderedProjector i A = vectorProjector (orderedColumnSelection i A) := by
  obtain ⟨z, hz, he⟩ := orderedColumnSelection_eq_phase i A hs
  rw [orderedProjector_eq_outerProduct i A hs]
  ext x y
  simp only [vectorProjector, Matrix.vecMulVec_apply, he, Pi.smul_apply,
    Pi.star_apply, star_smul, starRingEnd_apply, smul_eq_mul]
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  symm
  calc
    _ = (z * star z) * (increasingEigenvector A.property i x *
        star (increasingEigenvector A.property i y)) := by ring
    _ = _ := by rw [hzz, one_mul]

/-- Outer products transform under unitary rotations. -/
theorem vectorProjector_mulVec (U : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    vectorProjector ((U : Matrix ι ι ℂ) *ᵥ v) =
      (U : Matrix ι ι ℂ) * vectorProjector v * (U : Matrix ι ι ℂ)ᴴ := by
  unfold vectorProjector
  rw [Matrix.star_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- Projector diagonal real parts recover the complex squared site norm. -/
theorem vectorProjector_diagonal_re (v : ι → ℂ) (x : ι) :
    (vectorProjector v x x).re = ‖v x‖ ^ 2 := by
  simp only [vectorProjector, Matrix.vecMulVec_apply, Pi.star_apply,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The selected site masses at a fixed increasing rank transform under unitary conjugation. -/
theorem orderedColumnSelection_unitary_mass (U : Matrix.unitaryGroup ι ℂ)
    (A : HermitianMatrix ι) (i : Fin (Fintype.card ι))
    (hs : Function.Injective (orderedEigenvalue A)) (x : ι) :
    ‖orderedColumnSelection i (unitaryConjugate U A) x‖ ^ 2 =
      ‖((U : Matrix ι ι ℂ) *ᵥ orderedColumnSelection i A) x‖ ^ 2 := by
  have hproj : vectorProjector (orderedColumnSelection i (unitaryConjugate U A)) =
      vectorProjector ((U : Matrix ι ι ℂ) *ᵥ orderedColumnSelection i A) := by
    rw [← orderedProjector_eq_selectedVectorProjector _ i
        (injective_orderedEigenvalue_unitaryConjugate U A hs),
      orderedProjector_unitaryConjugate,
      orderedProjector_eq_selectedVectorProjector A i hs, vectorProjector_mulVec]
  have hd := congrArg (fun P : Matrix ι ι ℂ => (P x x).re) hproj
  simpa only [vectorProjector_diagonal_re] using hd

/-- Covariance of the canonical selected site masses of the physical model at a fixed increasing
rank, on each Hermitian matrix with simple spectrum. -/
theorem physicalOrderedEigenvector_unitary_mass (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (U : Matrix.unitaryGroup p.Site ℂ) (α : Fin p.N) (x : p.Site) :
    ‖physicalOrderedEigenvector p
        ((U : p.SiteMatrix) * H * (U : p.SiteMatrix)ᴴ) α x‖ ^ 2 =
      ‖((U : p.SiteMatrix) *ᵥ physicalOrderedEigenvector p H α) x‖ ^ 2 := by
  have hs := orderedEigenvalue_injective_of_separable (⟨H, hH⟩ : HermitianMatrix p.Site) hsep
  have h := orderedColumnSelection_unitary_mass U ⟨H, hH⟩ (physicalSpectralRank p α) hs x
  unfold physicalOrderedEigenvector
  simp_rw [rawOrderedColumnSelection_eq _ _
      (Matrix.isHermitian_mul_mul_conjTranspose _ hH), rawOrderedColumnSelection_eq _ _ hH]
  exact h

/-- The square matrix of a rank-indexed vector family. -/
def rankBasisMatrix (v : Fin (Fintype.card ι) → ι → ℂ) : Matrix ι ι ℂ :=
  fun x y => v (increasingIndex.symm y) x

/-- An orthonormal rank-indexed family gives a unitary matrix. -/
theorem rankBasisMatrix_mem (v : Fin (Fintype.card ι) → ι → ℂ)
    (hv : ∀ i j, (∑ x, starRingEnd ℂ (v i x) * v j x) = if i = j then 1 else 0) :
    rankBasisMatrix v ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext x y
  have h := hv (increasingIndex.symm x) (increasingIndex.symm y)
  simpa only [rankBasisMatrix, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, starRingEnd_apply, Matrix.one_apply,
    increasingIndex.symm.injective.eq_iff] using h

/-- An ordered orthonormal eigensystem determines the characteristic polynomial from its
eigenvalues. -/
theorem charpoly_of_rank_eigenbasis (A : HermitianMatrix ι)
    (ell : Fin (Fintype.card ι) → ℝ) (v : Fin (Fintype.card ι) → ι → ℂ)
    (hv : ∀ i j, (∑ x, starRingEnd ℂ (v i x) * v j x) = if i = j then 1 else 0)
    (heig : ∀ i, A.val *ᵥ v i = (ell i : ℂ) • v i) :
    A.val.charpoly = ∏ i : Fin (Fintype.card ι), (Polynomial.X - Polynomial.C (ell i : ℂ)) := by
  let Q : Matrix.unitaryGroup ι ℂ := ⟨rankBasisMatrix v, rankBasisMatrix_mem v hv⟩
  let D := Matrix.diagonal (fun y : ι => (ell (increasingIndex.symm y) : ℂ))
  have heq : A.val * (Q : Matrix ι ι ℂ) = (Q : Matrix ι ι ℂ) * D := by
    ext x y
    change (A.val *ᵥ v (increasingIndex.symm y)) x = _
    rw [heig]
    simp only [D, Matrix.mul_diagonal, Q, rankBasisMatrix, Pi.smul_apply, smul_eq_mul]
    ring
  have hA : A.val = (Q : Matrix ι ι ℂ) * D * (Q : Matrix ι ι ℂ)ᴴ := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M * (Q : Matrix ι ι ℂ)ᴴ) heq
    simpa only [Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Unitary.mul_star_self_of_mem Q.property, Matrix.mul_one] using h
  rw [hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul, Matrix.charpoly_diagonal]
  simpa only [D, Equiv.symm_apply_apply] using
    (increasingIndex : Fin (Fintype.card ι) ≃ ι).prod_comp
      (fun y : ι => Polynomial.X - Polynomial.C (ell (increasingIndex.symm y) : ℂ)) |>.symm

/-- Every ordered orthonormal eigensystem has the increasing eigenvalues. -/
theorem orderedEigenvalue_eq_of_rank_eigenbasis (A : HermitianMatrix ι)
    (ell : Fin (Fintype.card ι) → ℝ) (v : Fin (Fintype.card ι) → ι → ℂ)
    (hv : ∀ i j, (∑ x, starRingEnd ℂ (v i x) * v j x) = if i = j then 1 else 0)
    (heig : ∀ i, A.val *ᵥ v i = (ell i : ℂ) • v i) (hell : Monotone ell) :
    orderedEigenvalue A = ell := by
  have hroot : A.val.charpoly.roots =
      Multiset.map (fun i : Fin (Fintype.card ι) => (ell i : ℂ)) Finset.univ.val := by
    rw [charpoly_of_rank_eigenbasis A ell v hv heig, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hrootRe : A.val.charpoly.roots.map Complex.re = Multiset.map ell Finset.univ.val := by
    rw [hroot, Multiset.map_map]
    simp only [Function.comp_def, Complex.ofReal_re]
  have hrev : Multiset.map ell Finset.univ.val =
      Multiset.map (fun i : Fin (Fintype.card ι) => ell i.rev) Finset.univ.val := by
    calc
      _ = Multiset.map ell (Multiset.map Fin.revPerm Finset.univ.val) := by
        rw [Multiset.map_univ_val_equiv]
      _ = _ := by rw [Multiset.map_map]; rfl
  have hanti : Antitone (fun i : Fin (Fintype.card ι) => ell i.rev) := by
    intro i j hij
    exact hell (Fin.rev_le_rev.mpr hij)
  have hsort : (A.val.charpoly.roots.map Complex.re).sort (· ≥ ·) =
      List.ofFn (fun i : Fin (Fintype.card ι) => ell i.rev) := by
    rw [hrootRe, hrev, Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hanti.sortedGE_ofFn
  have hval : A.property.eigenvalues₀ = (fun i : Fin (Fintype.card ι) => ell i.rev) := by
    apply List.ofFn_inj.mp
    rw [← A.property.sort_roots_charpoly_eq_eigenvalues₀]
    exact hsort
  funext i
  simp only [orderedEigenvalue, increasingEigenvalue, hval, Fin.rev_rev]

/-- Two matrices agreeing on an orthonormal basis are equal. -/
theorem matrix_eq_of_rank_mulVec (v : Fin (Fintype.card ι) → ι → ℂ)
    (hv : ∀ i j, (∑ x, starRingEnd ℂ (v i x) * v j x) = if i = j then 1 else 0)
    (P Q : Matrix ι ι ℂ) (h : ∀ i, P *ᵥ v i = Q *ᵥ v i) : P = Q := by
  let V : Matrix.unitaryGroup ι ℂ := ⟨rankBasisMatrix v, rankBasisMatrix_mem v hv⟩
  have hm : P * (V : Matrix ι ι ℂ) = Q * (V : Matrix ι ι ℂ) := by
    ext x y
    exact congrFun (h (increasingIndex.symm y)) x
  have he := congrArg (fun M : Matrix ι ι ℂ => M * (V : Matrix ι ι ℂ)ᴴ) hm
  simpa only [Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Unitary.mul_star_self_of_mem V.property, Matrix.mul_one] using he

/-- Action of the Lagrange factors on an eigenvector at an increasing eigenvalue. -/
theorem orderedProjectorFactor_rank_mulVec (A : HermitianMatrix ι)
    (v : Fin (Fintype.card ι) → ι → ℂ)
    (heig : ∀ r, A.val *ᵥ v r = (orderedEigenvalue A r : ℂ) • v r)
    (i j r : Fin (Fintype.card ι)) :
    orderedProjectorFactor i j A *ᵥ v r = orderedProjectorScalar i j r A • v r := by
  by_cases hji : j = i
  · simp [orderedProjectorFactor, orderedProjectorScalar, hji, Matrix.one_mulVec]
  · simp only [orderedProjectorFactor, orderedProjectorScalar, hji, ite_false,
      Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [heig, ← sub_smul, smul_smul]

/-- Action of the Lagrange product on the eigenvectors of an ordered eigensystem. -/
theorem orderedProjectorProduct_rank_mulVec (A : HermitianMatrix ι)
    (v : Fin (Fintype.card ι) → ι → ℂ)
    (heig : ∀ r, A.val *ᵥ v r = (orderedEigenvalue A r : ℂ) • v r)
    (i r : Fin (Fintype.card ι)) (ranks : List (Fin (Fintype.card ι))) :
    orderedProjectorProduct i ranks A *ᵥ v r =
      (ranks.map (fun j => orderedProjectorScalar i j r A)).prod • v r := by
  induction ranks with
  | nil => simp [orderedProjectorProduct, Matrix.one_mulVec]
  | cons j ranks ih =>
    simp only [orderedProjectorProduct, List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    change _ = _ at ih
    dsimp only [orderedProjectorProduct] at ih
    rw [ih, Matrix.mulVec_smul, orderedProjectorFactor_rank_mulVec A v heig, smul_smul]
    rw [mul_comm]

/-- On simple spectrum, the rank projector is the outer product of the eigenvector of every
ordered orthonormal eigensystem at that rank. -/
theorem orderedProjector_eq_rankVectorProjector (A : HermitianMatrix ι)
    (hs : Function.Injective (orderedEigenvalue A))
    (v : Fin (Fintype.card ι) → ι → ℂ)
    (hv : ∀ i j, (∑ x, starRingEnd ℂ (v i x) * v j x) = if i = j then 1 else 0)
    (heig : ∀ r, A.val *ᵥ v r = (orderedEigenvalue A r : ℂ) • v r)
    (i : Fin (Fintype.card ι)) : orderedProjector i A = vectorProjector (v i) := by
  apply matrix_eq_of_rank_mulVec v hv
  intro r
  unfold orderedProjector
  rw [orderedProjectorProduct_rank_mulVec A v heig, orderedProjectorScalar_prod i r A hs]
  ext x
  change (if r = i then (1 : ℂ) else 0) * v r x =
    ∑ y, (v i x * starRingEnd ℂ (v i y)) * v r y
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hv]
  by_cases hri : r = i
  · simp [hri]
  · simp [hri, Ne.symm hri]

/-- On simple spectrum, every ordered orthonormal eigensystem has the canonical selected site
masses at each rank. -/
theorem norm_rankVector_eq_selected (A : HermitianMatrix ι)
    (hs : Function.Injective (orderedEigenvalue A))
    (ell : Fin (Fintype.card ι) → ℝ) (v : Fin (Fintype.card ι) → ι → ℂ)
    (hv : ∀ i j, (∑ x, starRingEnd ℂ (v i x) * v j x) = if i = j then 1 else 0)
    (heig : ∀ r, A.val *ᵥ v r = (ell r : ℂ) • v r) (hell : Monotone ell)
    (i : Fin (Fintype.card ι)) (x : ι) :
    ‖v i x‖ ^ 2 = ‖orderedColumnSelection i A x‖ ^ 2 := by
  have heq := orderedEigenvalue_eq_of_rank_eigenbasis A ell v hv heig hell
  have hproj : vectorProjector (v i) = vectorProjector (orderedColumnSelection i A) := by
    rw [← orderedProjector_eq_rankVectorProjector A hs v hv
        (by intro r; rw [heq]; exact heig r),
      orderedProjector_eq_selectedVectorProjector A i hs]
  have hd := congrArg (fun P : Matrix ι ι ℂ => (P x x).re) hproj
  simpa only [vectorProjector_diagonal_re] using hd

/-- At each rank of the physical model, the site masses of a spectral realization agree with the
canonical ones (deterministic). -/
theorem physical_rank_mass_eq_canonical (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (ell : Fin p.N → ℝ) (v : Fin p.N → p.Site → ℂ)
    (hv : ∀ α β, (∑ x, starRingEnd ℂ (v α x) * v β x) = if α = β then 1 else 0)
    (heig : ∀ α, H *ᵥ v α = (ell α : ℂ) • v α) (hell : Monotone ell)
    (α : Fin p.N) (x : p.Site) :
    ‖v α x‖ ^ 2 = ‖physicalOrderedEigenvector p H α x‖ ^ 2 := by
  let R (i : Fin (Fintype.card p.Site)) : Fin p.N := Fin.cast (physicalSite_card p) i
  let ell₀ (i : Fin (Fintype.card p.Site)) := ell (R i)
  let v₀ (i : Fin (Fintype.card p.Site)) := v (R i)
  have hv₀ : ∀ i j, (∑ x, starRingEnd ℂ (v₀ i x) * v₀ j x) = if i = j then 1 else 0 := by
    intro i j
    simpa only [v₀, R, Fin.cast_inj] using hv (R i) (R j)
  have heig₀ : ∀ i, H *ᵥ v₀ i = (ell₀ i : ℂ) • v₀ i := fun i => heig (R i)
  have hell₀ : Monotone ell₀ := by
    intro i j hij
    exact hell hij
  have h := norm_rankVector_eq_selected (⟨H, hH⟩ : HermitianMatrix p.Site)
    (orderedEigenvalue_injective_of_separable _ hsep) ell₀ v₀ hv₀ heig₀ hell₀
    (physicalSpectralRank p α) x
  unfold physicalOrderedEigenvector
  rw [rawOrderedColumnSelection_eq _ _ hH]
  simpa only [v₀, R, physicalSpectralRank, Fin.cast_cast, Fin.cast_eq_self] using h

end BlockBand.QUE.Haar
