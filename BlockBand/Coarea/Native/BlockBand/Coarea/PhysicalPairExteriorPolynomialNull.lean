module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSparseGaussianPolynomialNull

/-!
# Polynomial nullity for an adjacent exposed pair

This module upgrades the one-block exterior polynomial argument to the
split of the paper, with adjacent exposed pair `S = {j,j+1}` of dimension `2W`.
The exterior is expressed in the cyclic ordering beginning at `j`: its indices
have exposed-relative position at least `2W`.  A Jacobi path with cut at `2W`,
not a diagonal fibre, is the nonzero resultant witness.  Thus the proof varies
active coupling coordinates and does not make the false claim that every fixed
off-diagonal fibre avoids common spectrum.

All statements concern the normalized finite physical Gaussian ring at fixed
`n,W,b`; there is no limiting or uniformity assertion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The cyclic successor of the first exposed block. -/
def adjacentPairNext (p : Params) (j : Fin p.n) : Fin p.n :=
  ⟨(j.val + 1) % p.n, Nat.mod_lt _ p.n_pos⟩

/-- Physical indices outside the first `2W` sites in the cyclic ordering from
`j`; these are exactly the exterior indices for the adjacent exposed pair
`{j,j+1}`. -/
abbrev PhysicalPairExteriorIndex (p : Params) (j : Fin p.n) :=
  {x : PhysicalIndex p // 2 * p.W ≤ (exposedPhysicalPos p j x).val}

/-- The normalized principal minor outside the adjacent exposed pair. -/
def Law.normalizedPhysicalPairExteriorMatrix {p : Params} (M : Law p)
    (j : Fin p.n) (ω : M.Ω) : HermitianMatrix (PhysicalPairExteriorIndex p j) :=
  ⟨(M.normalizedPhysicalMatrix ω).1.submatrix Subtype.val Subtype.val,
    (M.normalizedPhysicalMatrix ω).2.submatrix Subtype.val⟩

/-- The physical adjacent-pair exterior minor is measurable entrywise. -/
theorem Law.measurable_normalizedPhysicalPairExteriorMatrix {p : Params}
    (M : Law p) (j : Fin p.n) :
    Measurable (M.normalizedPhysicalPairExteriorMatrix j) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro a b
  exact (measurable_subtype_coe.comp M.measurable_normalizedPhysicalMatrix).eval_matrix

/-- At full ordered rank `r`, the selected energy avoids the adjacent-pair
exterior spectrum. -/
def Law.physicalSelectedEnergyPairExteriorPoleFreeEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) : Set M.Ω :=
  {ω | ∀ s : Fin (Fintype.card (PhysicalPairExteriorIndex p j)),
    orderedEigenvalue (M.normalizedPhysicalPairExteriorMatrix j ω) s ≠
      orderedEigenvalue (M.normalizedPhysicalMatrix ω) r}

/-- Selected-energy pair-exterior pole avoidance is measurable. -/
theorem Law.measurableSet_physicalSelectedEnergyPairExteriorPoleFreeEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    MeasurableSet (M.physicalSelectedEnergyPairExteriorPoleFreeEvent j r) := by
  simp only [physicalSelectedEnergyPairExteriorPoleFreeEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro s
  have hext : Measurable (fun ω =>
      orderedEigenvalue (M.normalizedPhysicalPairExteriorMatrix j ω) s) :=
    (measurable_orderedEigenvalue s).comp
      (M.measurable_normalizedPhysicalPairExteriorMatrix j)
  have hfull : Measurable (fun ω =>
      orderedEigenvalue (M.normalizedPhysicalMatrix ω) r) :=
    (measurable_orderedEigenvalue r).comp M.measurable_normalizedPhysicalMatrix
  have h := ((measurableSet_singleton 0).preimage (hext.sub hfull)).compl
  convert h using 1
  ext ω
  simp [sub_eq_zero]

/-- Measurable positive mass on the two adjacent exposed blocks, using the
globally measurable phase-free ordered-eigenline weights. -/
def Law.physicalSelectedPairMassPositiveEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) : Set M.Ω :=
  {ω | 0 < physicalMeasurableBlockMassWeight p r
      (M.normalizedPhysicalMatrix ω) j +
    physicalMeasurableBlockMassWeight p r
      (M.normalizedPhysicalMatrix ω) (adjacentPairNext p j)}

/-- Positivity of the selected adjacent-pair mass is measurable. -/
theorem Law.measurableSet_physicalSelectedPairMassPositiveEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    MeasurableSet (M.physicalSelectedPairMassPositiveEvent j r) := by
  exact (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : NNReal))).preimage
    (((measurable_physicalMeasurableBlockMassWeight p r j).comp
      M.measurable_normalizedPhysicalMatrix).add
      ((measurable_physicalMeasurableBlockMassWeight p r (adjacentPairNext p j)).comp
        M.measurable_normalizedPhysicalMatrix))

/-- The measurable selected-rank good event for the adjacent-pair Schur split. -/
def Law.physicalSelectedPairCoareaGoodEvent {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) : Set M.Ω :=
  M.physicalFullSimpleSpectrumEvent ∩
    M.physicalSelectedEnergyPairExteriorPoleFreeEvent j r ∩
      M.physicalSelectedPairMassPositiveEvent j r

/-- The adjacent-pair coarea good event is measurable. -/
theorem Law.measurableSet_physicalSelectedPairCoareaGoodEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    MeasurableSet (M.physicalSelectedPairCoareaGoodEvent j r) :=
  (M.measurableSet_physicalFullSimpleSpectrumEvent.inter
    (M.measurableSet_physicalSelectedEnergyPairExteriorPoleFreeEvent j r)).inter
      (M.measurableSet_physicalSelectedPairMassPositiveEvent j r)

/-- The exposed cyclic coordinate equivalence identifies the adjacent-pair
exterior with the Jacobi exterior `[2W,nW)`. -/
def exposedPairExteriorEquiv (p : Params) (j : Fin p.n) :
    PhysicalPairExteriorIndex p j ≃ jacobiExterior (p.n * p.W) (2 * p.W) 0 :=
  (exposedPhysicalPosEquiv p j).subtypeEquiv fun x => by
    change (2 * p.W ≤ (exposedPhysicalPos p j x).val) ↔
      (2 * p.W ≤ (exposedPhysicalPos p j x).val ∧
        (exposedPhysicalPos p j x).val < p.n * p.W)
    exact ⟨fun h => ⟨h, (exposedPhysicalPos p j x).isLt⟩, fun h => h.1⟩

/-- The Jacobi witness with its cut after the two exposed blocks, transported
back to physical sites and scaled so normalization returns the witness. -/
def exposedPairPathSiteMatrix (p : Params) (j : Fin p.n) (t : ℝ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ := fun a b =>
  (Real.sqrt p.c : ℂ) * jacobiWitness (p.n * p.W) (2 * p.W) 0 t
    ⟨exposedSitePos p j a, exposedSitePos_lt p j a⟩
    ⟨exposedSitePos p j b, exposedSitePos_lt p j b⟩

/-- The adjacent-pair path witness is Hermitian. -/
theorem exposedPairPathSiteMatrix_isHermitian (p : Params) (j : Fin p.n) (t : ℝ) :
    (exposedPairPathSiteMatrix p j t).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, exposedPairPathSiteMatrix, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  congr 1
  have hc := jacobiWitness_conj (p.n * p.W) (2 * p.W) 0 t
    ⟨exposedSitePos p j b, exposedSitePos_lt p j b⟩
    ⟨exposedSitePos p j a, exposedSitePos_lt p j a⟩
  have h := congrFun (congrFun
    (jacobiWitness_transpose (p.n * p.W) (2 * p.W) 0 t)
      ⟨exposedSitePos p j a, exposedSitePos_lt p j a⟩)
      ⟨exposedSitePos p j b, exposedSitePos_lt p j b⟩
  simp only [Matrix.transpose_apply] at h
  rw [← h]
  exact hc

/-- The path witness uses only active physical band coordinates. -/
theorem exposedPairPathSiteMatrix_band (p : Params) (j : Fin p.n) (t : ℝ)
    (a b : Site p.n p.W) (hab : a ≠ b) (hv : varianceProfile p a b = 0) :
    exposedPairPathSiteMatrix p j t a b = 0 := by
  unfold exposedPairPathSiteMatrix
  by_contra hne
  have hJ := right_ne_zero_of_mul hne
  rcases jacobiWitness_ne_zero hJ with ⟨-, -, h | h⟩ | ⟨h, -⟩
  · exact varianceProfile_ne_zero_of_exposedSitePos_succ p j h.symm hv
  · rw [varianceProfile_comm] at hv
    exact varianceProfile_ne_zero_of_exposedSitePos_succ p j h.symm hv
  · exact hab (exposedSitePos_injective p j (congrArg Fin.val h))

/-- Correct nonzero resultant witness for deletion of the adjacent exposed
pair.  It varies nearest-neighbour couplings, unlike the invalid universal
diagonal-fibre argument. -/
theorem exists_exposedPairPath_coprime (p : Params) (j : Fin p.n) :
    ∃ t : ℝ, IsCoprime
      (Matrix.of fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
        exposedPairPathSiteMatrix p j t (allDiagonalSite i) (allDiagonalSite k)).charpoly
      ((Matrix.of fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
        exposedPairPathSiteMatrix p j t (allDiagonalSite i) (allDiagonalSite k)).submatrix
          (Subtype.val : PhysicalPairExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalPairExteriorIndex p j → PhysicalIndex p)).charpoly := by
  have hW : 1 ≤ 2 * p.W := by nlinarith [p.W_pos]
  have hL : 2 * p.W + 0 < p.n * p.W := by
    have h4 : 4 ≤ p.n := p.n_ge_four
    have hWp : 1 ≤ p.W := p.W_pos
    nlinarith
  obtain ⟨t, ht⟩ := exists_jacobiWitness_coprime
    (p.n * p.W) (2 * p.W) 0 hW hL
  refine ⟨t, ?_⟩
  set J := jacobiWitness (p.n * p.W) (2 * p.W) 0 t
  have hfull : (Matrix.of fun i k : PhysicalIndex p => ((Real.sqrt p.c)⁻¹ : ℂ) *
      exposedPairPathSiteMatrix p j t (allDiagonalSite i) (allDiagonalSite k)) =
      Matrix.reindex (exposedPhysicalPosEquiv p j).symm
        (exposedPhysicalPosEquiv p j).symm J := by
    ext i k
    have hc := sqrt_c_complex_ne_zero p
    simp only [Matrix.of_apply, exposedPairPathSiteMatrix, Matrix.reindex_apply,
      Equiv.symm_symm, Matrix.submatrix_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rfl
  rw [hfull, Matrix.charpoly_reindex]
  have hext : (Matrix.reindex (exposedPhysicalPosEquiv p j).symm
      (exposedPhysicalPosEquiv p j).symm J).submatrix
        (Subtype.val : PhysicalPairExteriorIndex p j → PhysicalIndex p)
        (Subtype.val : PhysicalPairExteriorIndex p j → PhysicalIndex p) =
      Matrix.reindex (exposedPairExteriorEquiv p j).symm
        (exposedPairExteriorEquiv p j).symm
        (J.submatrix
          (Subtype.val : jacobiExterior (p.n * p.W) (2 * p.W) 0 → Fin (p.n * p.W))
          Subtype.val) := by
    ext a b
    rfl
  rw [hext, Matrix.charpoly_reindex]
  exact ht

/-- Almost surely the normalized full matrix and the adjacent-pair exterior
minor have coprime characteristic polynomials. -/
theorem Law.ae_isCoprime_normalizedPhysical_pairExterior_charpoly
    {p : Params} (M : Law p) (j : Fin p.n) :
    ∀ᵐ ω ∂M.P, IsCoprime (M.normalizedPhysicalMatrix ω).1.charpoly
      (M.normalizedPhysicalPairExteriorMatrix j ω).1.charpoly := by
  obtain ⟨t, ht⟩ := exists_exposedPairPath_coprime p j
  set x₀ := coordinatesOfMatrix p (exposedPairPathSiteMatrix p j t)
  have hrec := physicalReconstruction_coordinatesOfMatrix p
    (exposedPairPathSiteMatrix p j t)
    (exposedPairPathSiteMatrix_isHermitian p j t)
    (exposedPairPathSiteMatrix_band p j t)
  have h₀ : IsCoprime
      ((normalizedPhysicalUniversalMatrix p).map
        (MvPolynomial.eval fun c => (x₀ c : ℂ))).charpoly
      (((normalizedPhysicalUniversalMatrix p).map
        (MvPolynomial.eval fun c => (x₀ c : ℂ))).submatrix
          (Subtype.val : PhysicalPairExteriorIndex p j → PhysicalIndex p)
          (Subtype.val : PhysicalPairExteriorIndex p j → PhysicalIndex p)).charpoly := by
    rw [normalizedPhysicalUniversalMatrix_map_eval, hrec]
    exact ht
  filter_upwards [M.ae_isCoprime_charpoly_submatrix_of_polynomialFamily _ _ x₀ h₀,
    M.ae_normalizedPhysicalMatrix_eq] with ω hω hN
  rw [normalizedPhysicalUniversalMatrix_map_eval] at hω
  have hext : (M.normalizedPhysicalPairExteriorMatrix j ω).1 =
      (M.normalizedPhysicalMatrix ω).1.submatrix Subtype.val Subtype.val := rfl
  rw [hext, hN]
  exact hω

/-- Almost surely every selected full energy avoids the adjacent-pair exterior
spectrum. -/
theorem Law.ae_mem_physicalSelectedEnergyPairExteriorPoleFreeEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalSelectedEnergyPairExteriorPoleFreeEvent j r := by
  filter_upwards [M.ae_isCoprime_normalizedPhysical_pairExterior_charpoly j] with ω hω
  intro s hrs
  have h1 := charpoly_isRoot_orderedEigenvalue (M.normalizedPhysicalMatrix ω) r
  have h2 := charpoly_isRoot_orderedEigenvalue
    (M.normalizedPhysicalPairExteriorMatrix j ω) s
  rw [hrs] at h2
  exact not_isCoprime_of_isRoot h1 h2 hω

/-- Almost surely the selected measurable mass on the adjacent exposed pair is
strictly positive. -/
theorem Law.ae_mem_physicalSelectedPairMassPositiveEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalSelectedPairMassPositiveEvent j r := by
  filter_upwards [M.ae_mem_physicalSelectedExposedMassPositiveEvent j r] with ω hω
  change 0 < physicalMeasurableBlockMassWeight p r
      (M.normalizedPhysicalMatrix ω) j +
    physicalMeasurableBlockMassWeight p r
      (M.normalizedPhysicalMatrix ω) (adjacentPairNext p j)
  change 0 < physicalMeasurableBlockMassWeight p r
      (M.normalizedPhysicalMatrix ω) j at hω
  exact lt_of_lt_of_le hω (le_add_of_nonneg_right bot_le)

/-- The selected adjacent-pair good event has full probability. -/
theorem Law.ae_mem_physicalSelectedPairCoareaGoodEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalSelectedPairCoareaGoodEvent j r := by
  filter_upwards [M.ae_mem_physicalFullSimpleSpectrumEvent,
    M.ae_mem_physicalSelectedEnergyPairExteriorPoleFreeEvent j r,
    M.ae_mem_physicalSelectedPairMassPositiveEvent j r] with ω hsimple hpole hmass
  exact ⟨⟨hsimple, hpole⟩, hmass⟩

/-- The simultaneous adjacent-pair good event for every ordered rank. -/
def Law.physicalPairCoareaGoodEvent {p : Params} (M : Law p)
    (j : Fin p.n) : Set M.Ω :=
  ⋂ r : Fin (PhysicalDimension p), M.physicalSelectedPairCoareaGoodEvent j r

/-- The simultaneous adjacent-pair good event is measurable. -/
theorem Law.measurableSet_physicalPairCoareaGoodEvent
    {p : Params} (M : Law p) (j : Fin p.n) :
    MeasurableSet (M.physicalPairCoareaGoodEvent j) := by
  apply MeasurableSet.iInter
  intro r
  exact M.measurableSet_physicalSelectedPairCoareaGoodEvent j r

/-- Every ordered rank simultaneously belongs to the adjacent-pair good event
almost surely. -/
theorem Law.ae_mem_physicalPairCoareaGoodEvent
    {p : Params} (M : Law p) (j : Fin p.n) :
    ∀ᵐ ω ∂M.P, ω ∈ M.physicalPairCoareaGoodEvent j := by
  simp only [physicalPairCoareaGoodEvent, Set.mem_iInter]
  rw [ae_all_iff]
  exact M.ae_mem_physicalSelectedPairCoareaGoodEvent j

/-- The ordered normalized eigenvector has positive mass on the
adjacent exposed pair almost surely, for every rank. -/
theorem Law.ae_physicalOrderedAdjacentPairMass_pos
    {p : Params} (M : Law p) (j : Fin p.n) :
    ∀ᵐ ω ∂M.P, ∀ α : Fin (Fintype.card
      (BlockGUE.Index (physicalBlockSizes p))),
      0 < M.physicalOrderedPairMass ω α j (adjacentPairNext p j) := by
  filter_upwards [M.ae_physicalOrderedPairMass_pos] with ω hω
  exact fun α => hω α j (adjacentPairNext p j)

/-- The complement of the selected adjacent-pair good event is null. -/
theorem Law.measure_compl_physicalSelectedPairCoareaGoodEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    M.P (M.physicalSelectedPairCoareaGoodEvent j r)ᶜ = 0 :=
  ae_iff.mp (M.ae_mem_physicalSelectedPairCoareaGoodEvent j r)

/-- The simultaneous adjacent-pair good event has probability one. -/
theorem Law.measure_physicalPairCoareaGoodEvent
    {p : Params} (M : Law p) (j : Fin p.n) :
    M.P (M.physicalPairCoareaGoodEvent j) = 1 := by
  rw [← prob_compl_eq_zero_iff (M.measurableSet_physicalPairCoareaGoodEvent j)]
  exact ae_iff.mp (M.ae_mem_physicalPairCoareaGoodEvent j)

end GaussianRing
end CoareaNative.BlockBand
