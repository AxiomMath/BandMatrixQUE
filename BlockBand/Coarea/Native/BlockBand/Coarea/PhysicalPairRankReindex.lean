module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalPairSchurReadback
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalEigenvectorMassProfileMeasurable

/-!
# Rank and eigenpair transport to the pair/exterior order

This module proves that the deterministic pair/exterior readback order is an
permutation of the original physical sites. It then transports ordered
ranks, eigenvalues, eigenvectors, and phase-free ordered projectors across that
permutation. All statements are pointwise and deterministic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix Set
open scoped ComplexOrder

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

private theorem adjacentPairSite_injective (p : Params) (j : ZMod p.n) :
    Function.Injective (adjacentPairSite p j) := by
  intro a b hab
  let a' : Fin (p.W + p.W) := Fin.cast (two_mul p.W) a
  let b' : Fin (p.W + p.W) := Fin.cast (two_mul p.W) b
  change (Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v)) a' :
      Site p.n p.W) =
    (Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v)) b' :
      Site p.n p.W) at hab
  let e : (Fin p.W ⊕ Fin p.W) ≃ Fin (p.W + p.W) := finSumFinEquiv
  generalize ha : e.symm a' = sa at hab
  generalize hb : e.symm b' = sb at hab
  have ha' : a' = e sa := by rw [← ha]; simp
  have hb' : b' = e sb := by rw [← hb]; simp
  rw [ha', hb'] at hab
  dsimp [e] at hab
  have hs : sa = sb := by
    rcases sa with aa | aa <;> rcases sb with bb | bb
    · simp only [finSumFinEquiv_apply_left, Fin.addCases_left,
        Prod.mk.injEq] at hab
      exact congrArg Sum.inl hab.2
    · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.addCases_left, Fin.addCases_right, Prod.mk.injEq] at hab
      exact False.elim ((add_one_ne_self
        (le_trans (by norm_num) p.n_ge_four) j) hab.1.symm)
    · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.addCases_left, Fin.addCases_right, Prod.mk.injEq] at hab
      exact False.elim ((add_one_ne_self
        (le_trans (by norm_num) p.n_ge_four) j) hab.1)
    · simp only [finSumFinEquiv_apply_right, Fin.addCases_right,
        Prod.mk.injEq] at hab
      exact congrArg Sum.inr hab.2
  apply Fin.ext
  change a'.val = b'.val
  rw [ha', hb', hs]

private theorem adjacentPairSite_range (p : Params) (j : ZMod p.n)
    (x : Site p.n p.W) :
    x ∈ Set.range (adjacentPairSite p j) ↔ x.1 = j ∨ x.1 = j + 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    let a' : Fin (p.W + p.W) := Fin.cast (two_mul p.W) a
    change ((Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v)) a' :
      Site p.n p.W).1 = j ∨
      (Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v)) a' :
        Site p.n p.W).1 = j + 1)
    let e : (Fin p.W ⊕ Fin p.W) ≃ Fin (p.W + p.W) := finSumFinEquiv
    generalize ha : e.symm a' = sa
    have ha' : a' = e sa := by rw [← ha]; simp
    rw [ha']
    dsimp [e]
    rcases sa with aa | aa <;>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.addCases_left, Fin.addCases_right] <;> simp
  · rintro (h | h)
    · refine ⟨Fin.cast (two_mul p.W).symm (Fin.castAdd p.W x.2), ?_⟩
      change Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v))
        (Fin.cast (two_mul p.W)
          (Fin.cast (two_mul p.W).symm (Fin.castAdd p.W x.2))) = x
      simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_left]
      exact Prod.ext h.symm rfl
    · refine ⟨Fin.cast (two_mul p.W).symm (Fin.natAdd p.W x.2), ?_⟩
      change Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v))
        (Fin.cast (two_mul p.W)
          (Fin.cast (two_mul p.W).symm (Fin.natAdd p.W x.2))) = x
      simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_right]
      exact Prod.ext h.symm rfl

/-- Pair/exterior readback is an equivalence with the original physical
site type. -/
def actualPairReadbackEquiv (p : Params) (j : ZMod p.n) :
    ((Unit ⊕ Fin (2 * p.W - 1)) ⊕ Fin (ActualPairExteriorDimension p j)) ≃
      Site p.n p.W :=
  Equiv.ofBijective (actualPairReadbackSite p j) (by
    constructor
    · intro a b hab
      rcases a with a | a <;> rcases b with b | b
      · apply congrArg Sum.inl
        apply (actualPairSelectedEquiv p).symm.injective
        exact adjacentPairSite_injective p j hab
      · exfalso
        have hr := (adjacentPairSite_range p j
          (((actualPairExteriorEquivFin p j).symm b).1)).mp
          ⟨(actualPairSelectedEquiv p).symm a, hab⟩
        exact hr.elim ((actualPairExteriorEquivFin p j).symm b).2.1
          ((actualPairExteriorEquivFin p j).symm b).2.2
      · exfalso
        have hr := (adjacentPairSite_range p j
          (((actualPairExteriorEquivFin p j).symm a).1)).mp
          ⟨(actualPairSelectedEquiv p).symm b, hab.symm⟩
        exact hr.elim ((actualPairExteriorEquivFin p j).symm a).2.1
          ((actualPairExteriorEquivFin p j).symm a).2.2
      · apply congrArg Sum.inr
        exact (actualPairExteriorEquivFin p j).symm.injective (Subtype.ext hab)
    · intro x
      by_cases hx : x.1 = j ∨ x.1 = j + 1
      · rcases (adjacentPairSite_range p j x).mpr hx with ⟨a, ha⟩
        exact ⟨Sum.inl (actualPairSelectedEquiv p a), by
          simpa [actualPairReadbackSite] using ha⟩
      · have hext : x.1 ≠ j ∧ x.1 ≠ j + 1 := not_or.mp hx
        exact ⟨Sum.inr (actualPairExteriorEquivFin p j ⟨x, hext⟩), by
          simp [actualPairReadbackSite]⟩)

@[simp] theorem actualPairReadbackEquiv_apply (p : Params) (j : ZMod p.n) (x) :
    actualPairReadbackEquiv p j x = actualPairReadbackSite p j x := rfl

/-- The block-product physical index is equivalent to the original site type. -/
def physicalIndexSiteEquiv (p : Params) : PhysicalIndex p ≃ Site p.n p.W :=
  Equiv.ofBijective allDiagonalSite ⟨allDiagonalSite_injective, by
    intro x
    refine ⟨⟨⟨x.1.val, x.1.val_lt⟩, x.2⟩, ?_⟩
    apply Prod.ext
    · simp [allDiagonalSite]
    · rfl⟩

/-- The pair/exterior index type has exactly the physical dimension. -/
theorem actualPairReadback_card (p : Params) (j : ZMod p.n) :
    Fintype.card ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
      Fin (ActualPairExteriorDimension p j)) = PhysicalDimension p := by
  exact Fintype.card_congr
    ((actualPairReadbackEquiv p j).trans (physicalIndexSiteEquiv p).symm)

/-- Cast a physical ordered rank to the reconstructed pair/exterior order. -/
def actualPairRankCast (p : Params) (j : ZMod p.n) :
    Fin (PhysicalDimension p) ≃
      Fin (Fintype.card ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
        Fin (ActualPairExteriorDimension p j))) :=
  finCongr (actualPairReadback_card p j).symm

/-- The original-site physical Hamiltonian as a bundled Hermitian matrix. -/
def Law.actualSiteHamiltonian {p : Params} (M : Law p) (ω : M.Ω) :
    HermitianMatrix (Site p.n p.W) :=
  ⟨M.H ω, M.H_hermitian ω⟩

/-- The reconstructed Hamiltonian in deterministic pair/exterior order. -/
def Law.actualPairReorderedHamiltonian {p : Params} (M : Law p)
    (j : ZMod p.n) (ω : M.Ω) :
    HermitianMatrix ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
      Fin (ActualPairExteriorDimension p j)) :=
  ⟨actualPairBlockReconstruction p j (M.actualAdjacentPairCoordinates j ω)
      (M.actualPairExteriorCouplingState j ω),
    actualPairBlockReconstruction_isHermitian p j _ _⟩

/-- Full reconstruction is precisely matrix reindexing by the site equivalence. -/
theorem Law.actualPairReorderedHamiltonian_eq_reindex
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    (M.actualPairReorderedHamiltonian j ω).1 =
      Matrix.reindex (actualPairReadbackEquiv p j).symm
        (actualPairReadbackEquiv p j).symm (M.H ω) := by
  rw [Law.actualPairReorderedHamiltonian]
  exact actualPairBlockReconstruction_eq_full_submatrix M j ω

/-- Ordered eigenvalues of a finite Hermitian matrix are invariant under an
arbitrary equivalence of its coordinate index. -/
theorem orderedEigenvalue_reindex_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : HermitianMatrix ι)
    (r : Fin (Fintype.card ι)) :
    orderedEigenvalue
        ⟨Matrix.reindex e e A.1, A.2.reindex e⟩
        (Fin.cast (Fintype.card_congr e) r) =
      orderedEigenvalue A r := by
  let B : HermitianMatrix κ :=
    ⟨Matrix.reindex e e A.1, A.2.reindex e⟩
  have hchar : B.1.charpoly = A.1.charpoly := by
    exact Matrix.charpoly_reindex e A.1
  have hlist : List.ofFn B.property.eigenvalues₀ =
      List.ofFn A.property.eigenvalues₀ := by
    rw [← B.property.sort_roots_charpoly_eq_eigenvalues₀,
      ← A.property.sort_roots_charpoly_eq_eigenvalues₀, hchar]
  have hc : Fintype.card ι = Fintype.card κ := Fintype.card_congr e
  have hpos : 0 < Fintype.card ι := Nat.zero_lt_of_lt r.isLt
  have hposK : 0 < Fintype.card κ := hc ▸ hpos
  have hget := congrArg (fun l : List ℝ => l[r.rev.val]?) hlist
  simp [hc, hposK] at hget
  change B.property.eigenvalues₀ (Fin.cast (Fintype.card_congr e) r).rev =
    A.property.eigenvalues₀ r.rev
  convert hget using 1
  · congr 1
  · congr 1
    apply Fin.ext
    simp [Fin.rev, hc]

/-- The physical rank index, expressed directly in original-site cardinality. -/
def actualSiteRankCast (p : Params) :
    Fin (PhysicalDimension p) ≃ Fin (Fintype.card (Site p.n p.W)) :=
  finCongr (Fintype.card_congr (physicalIndexSiteEquiv p))

/-- The selected physical ordered energy is unchanged in pair/exterior order. -/
theorem Law.orderedEigenvalue_actualPairReorderedHamiltonian
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (r : Fin (PhysicalDimension p)) :
    orderedEigenvalue (M.actualPairReorderedHamiltonian j ω)
        (actualPairRankCast p j r) =
      orderedEigenvalue (M.actualSiteHamiltonian ω)
        (actualSiteRankCast p r) := by
  have hmatrix : M.actualPairReorderedHamiltonian j ω =
      ⟨Matrix.reindex (actualPairReadbackEquiv p j).symm
          (actualPairReadbackEquiv p j).symm (M.H ω),
        (M.H_hermitian ω).reindex (actualPairReadbackEquiv p j).symm⟩ := by
    apply Subtype.ext
    exact M.actualPairReorderedHamiltonian_eq_reindex j ω
  rw [hmatrix]
  simpa [actualPairRankCast, actualSiteRankCast,
    Law.actualSiteHamiltonian] using
    orderedEigenvalue_reindex_equiv (actualPairReadbackEquiv p j).symm
      (M.actualSiteHamiltonian ω) (actualSiteRankCast p r)

/-- Mathlib's ordered eigenbasis vector at a physical increasing rank,
expressed on the original site type. -/
def Law.actualSiteOrderedEigenvector {p : Params} (M : Law p) (ω : M.Ω)
    (r : Fin (PhysicalDimension p)) : EuclideanSpace ℂ (Site p.n p.W) :=
  (M.actualSiteHamiltonian ω).property.eigenvectorBasis
    (Fintype.equivOfCardEq (Fintype.card_fin _)
      (actualSiteRankCast p r).rev)

/-- The original-site ordered vector satisfies its selected-rank equation. -/
theorem Law.actualSiteOrderedEigenvector_eigenvector
    {p : Params} (M : Law p) (ω : M.Ω)
    (r : Fin (PhysicalDimension p)) :
    M.H ω *ᵥ M.actualSiteOrderedEigenvector ω r =
      (orderedEigenvalue (M.actualSiteHamiltonian ω)
        (actualSiteRankCast p r) : ℂ) • M.actualSiteOrderedEigenvector ω r := by
  simpa [Law.actualSiteOrderedEigenvector, Law.actualSiteHamiltonian,
    orderedEigenvalue, Matrix.IsHermitian.eigenvalues] using
    (M.actualSiteHamiltonian ω).property.mulVec_eigenvectorBasis
      (Fintype.equivOfCardEq (Fintype.card_fin _)
        (actualSiteRankCast p r).rev)

/-- Transport a vector from original sites to pair/exterior coordinates. -/
def actualPairReindexVector (p : Params) (j : ZMod p.n)
    (v : Site p.n p.W → ℂ) :
    ((Unit ⊕ Fin (2 * p.W - 1)) ⊕
      Fin (ActualPairExteriorDimension p j)) → ℂ :=
  fun a => v (actualPairReadbackEquiv p j a)

/-- Matrix-vector multiplication commutes with the pair permutation. -/
theorem mulVec_actualPairReindex
    (p : Params) (j : ZMod p.n) (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (v : Site p.n p.W → ℂ) :
    Matrix.reindex (actualPairReadbackEquiv p j).symm
        (actualPairReadbackEquiv p j).symm A *ᵥ actualPairReindexVector p j v =
      actualPairReindexVector p j (A *ᵥ v) := by
  ext a
  change (∑ i, A (actualPairReadbackEquiv p j a)
      (actualPairReadbackEquiv p j i) * v (actualPairReadbackEquiv p j i)) =
    ∑ x, A (actualPairReadbackEquiv p j a) x * v x
  exact Equiv.sum_comp (actualPairReadbackEquiv p j)
    (fun b => A (actualPairReadbackEquiv p j a) b * v b)

/-- Every original-site eigenvector transports to the same ordered energy in
pair/exterior order. -/
theorem Law.actualPairReindexVector_eigenvector
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (r : Fin (PhysicalDimension p)) (v : Site p.n p.W → ℂ)
    (hv : M.H ω *ᵥ v =
      (orderedEigenvalue (M.actualSiteHamiltonian ω)
        (actualSiteRankCast p r) : ℂ) • v) :
    (M.actualPairReorderedHamiltonian j ω).1 *ᵥ
        actualPairReindexVector p j v =
      (orderedEigenvalue (M.actualPairReorderedHamiltonian j ω)
        (actualPairRankCast p j r) : ℂ) • actualPairReindexVector p j v := by
  rw [Law.actualPairReorderedHamiltonian_eq_reindex,
    mulVec_actualPairReindex, hv,
    Law.orderedEigenvalue_actualPairReorderedHamiltonian]
  rfl

/-- Reindexing preserves the phase-free rank-one projector of a vector. -/
theorem vecMulVec_actualPairReindex
    (p : Params) (j : ZMod p.n) (v : Site p.n p.W → ℂ) :
    Matrix.vecMulVec (actualPairReindexVector p j v)
        (star (actualPairReindexVector p j v)) =
      Matrix.reindex (actualPairReadbackEquiv p j).symm
        (actualPairReadbackEquiv p j).symm
        (Matrix.vecMulVec v (star v)) := by
  ext a b
  rfl

/-- The selected ordered eigenpair and its phase-free projector
transport together to the reconstructed pair/exterior state. -/
theorem Law.actualPairSelectedRankEigenpairProjector_reindex
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (r : Fin (PhysicalDimension p)) :
    let v := M.actualSiteOrderedEigenvector ω r
    let w := actualPairReindexVector p j v
    (M.actualPairReorderedHamiltonian j ω).1 *ᵥ w =
        (orderedEigenvalue (M.actualPairReorderedHamiltonian j ω)
          (actualPairRankCast p j r) : ℂ) • w ∧
      Matrix.vecMulVec w (star w) =
        Matrix.reindex (actualPairReadbackEquiv p j).symm
          (actualPairReadbackEquiv p j).symm
          (Matrix.vecMulVec v (star v)) := by
  dsimp only
  exact ⟨M.actualPairReindexVector_eigenvector j ω r _
      (M.actualSiteOrderedEigenvector_eigenvector ω r),
    vecMulVec_actualPairReindex p j _⟩

/-- A phase-free selected-rank observable on the original physical eigenline
is exactly the corresponding observable on the reconstructed reordered
projector, after deterministic matrix reindexing. -/
theorem actualPhysicalSelectedRankObservable_reindex
    (p : Params) (j : ZMod p.n) (v : Site p.n p.W → ℂ)
    (Ψ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ → ENNReal) :
    Ψ (Matrix.vecMulVec v (star v)) =
      (fun P => Ψ (Matrix.reindex (actualPairReadbackEquiv p j)
        (actualPairReadbackEquiv p j) P))
        (Matrix.vecMulVec (actualPairReindexVector p j v)
          (star (actualPairReindexVector p j v))) := by
  rw [vecMulVec_actualPairReindex]
  simp

/-- The physical selected-rank phase-free observable is read without
change from the reconstructed reordered state. -/
theorem Law.actualPhysicalSelectedRankObservable_reordered
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (r : Fin (PhysicalDimension p))
    (Ψ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ → ENNReal) :
    Ψ (Matrix.vecMulVec (M.actualSiteOrderedEigenvector ω r)
        (star (M.actualSiteOrderedEigenvector ω r))) =
      (fun P => Ψ (Matrix.reindex (actualPairReadbackEquiv p j)
        (actualPairReadbackEquiv p j) P))
        (Matrix.vecMulVec
          (actualPairReindexVector p j (M.actualSiteOrderedEigenvector ω r))
          (star (actualPairReindexVector p j
            (M.actualSiteOrderedEigenvector ω r)))) :=
  actualPhysicalSelectedRankObservable_reindex p j _ Ψ

end GaussianRing
end CoareaNative.BlockBand
