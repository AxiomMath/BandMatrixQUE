module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalBlockConditioningGaussian

/-!
# Measurable reconstruction for physical Gaussian block conditioning

This module reconstructs the whole Hermitian ring matrix from the independent
upper-coordinate vectors isolated in `PhysicalBlockConditioningGaussian`.
It also records the exact `sqrt c` normalization which converts the exposed
physical diagonal block, whose entry variance is `c/W`, to the `1/W`
normalization of `BlockGUE`.

No conditional expectation or disintegration theorem is assumed here.  The
deterministic reconstruction and independence from the exterior are proved
below.  Transporting the scalar Gaussian laws through this nonzero rescaling and
packaging the normalized block as a `BlockGUE.Law` is the structure
`NormalizedDiagonalBlockGUECoupling`, constructed as
`Law.normalizedDiagonalBlockGUECoupling`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ComplexOrder ENNReal NNReal

namespace GaussianRing

/-- Membership in the exposed-coordinate finset is exactly the within-block
predicate. -/
@[simp] theorem mem_diagonalBlockUpperPairs_iff
    (p : Params) (j : ZMod p.n) (q : UpperPair p) :
    q ∈ diagonalBlockUpperPairs p j ↔ q.1.1.1 = j ∧ q.1.2.1 = j := by
  classical
  simp [diagonalBlockUpperPairs]

/-- Membership in the exterior-coordinate finset is the complementary
within-block predicate. -/
@[simp] theorem mem_exteriorUpperPairs_iff
    (p : Params) (j : ZMod p.n) (q : UpperPair p) :
    q ∈ exteriorUpperPairs p j ↔ ¬(q.1.1.1 = j ∧ q.1.2.1 = j) := by
  classical
  simp [exteriorUpperPairs]

/-- Merge the exposed and exterior coordinate vectors back into the complete
upper-triangular coordinate vector. -/
def mergeUpperCoordinates (p : Params) (j : ZMod p.n)
    (x : diagonalBlockUpperPairs p j → ℂ)
    (y : exteriorUpperPairs p j → ℂ) (q : UpperPair p) : ℂ := by
  classical
  exact if h : q ∈ diagonalBlockUpperPairs p j then x ⟨q, h⟩
    else y ⟨q, (mem_exteriorUpperPairs_iff p j q).2
      (fun hq => h ((mem_diagonalBlockUpperPairs_iff p j q).2 hq))⟩

/-- On an exposed coordinate, merging selects the exposed vector. -/
@[simp] theorem mergeUpperCoordinates_of_mem (p : Params) (j : ZMod p.n)
    (x : diagonalBlockUpperPairs p j → ℂ)
    (y : exteriorUpperPairs p j → ℂ) (q : UpperPair p)
    (hq : q ∈ diagonalBlockUpperPairs p j) :
    mergeUpperCoordinates p j x y q = x ⟨q, hq⟩ := by
  simp [mergeUpperCoordinates, hq]

/-- Merging the two coordinate projections of a sample recovers every upper
entry of that sample. -/
theorem Law.mergeUpperCoordinates_apply
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) (q : UpperPair p) :
    mergeUpperCoordinates p j (M.diagonalBlockUpperCoordinates j ω)
      (M.exteriorUpperCoordinates j ω) q = M.H ω q.1.1 q.1.2 := by
  by_cases h : q ∈ diagonalBlockUpperPairs p j
  · simp [mergeUpperCoordinates, h, Law.diagonalBlockUpperCoordinates]
  · simp [mergeUpperCoordinates, h, Law.exteriorUpperCoordinates]

/-- The coordinate-merging map is measurable for the product Borel structure
on the two finite coordinate vectors. -/
theorem measurable_mergeUpperCoordinates (p : Params) (j : ZMod p.n) :
    Measurable (fun z :
      (diagonalBlockUpperPairs p j → ℂ) × (exteriorUpperPairs p j → ℂ) =>
      mergeUpperCoordinates p j z.1 z.2) := by
  rw [measurable_pi_iff]
  intro q
  by_cases h : q ∈ diagonalBlockUpperPairs p j
  · rw [show (fun z :
        (diagonalBlockUpperPairs p j → ℂ) × (exteriorUpperPairs p j → ℂ) =>
        mergeUpperCoordinates p j z.1 z.2 q) =
        (fun z => z.1 (⟨q, h⟩ : diagonalBlockUpperPairs p j)) by
          funext z
          simp [mergeUpperCoordinates, h]]
    exact (measurable_pi_apply _).comp measurable_fst
  · have hext : q ∈ exteriorUpperPairs p j :=
      (mem_exteriorUpperPairs_iff p j q).2
        (fun hq => h ((mem_diagonalBlockUpperPairs_iff p j q).2 hq))
    rw [show (fun z :
        (diagonalBlockUpperPairs p j → ℂ) × (exteriorUpperPairs p j → ℂ) =>
        mergeUpperCoordinates p j z.1 z.2 q) =
        (fun z => z.2 (⟨q, hext⟩ : exteriorUpperPairs p j)) by
          funext z
          simp [mergeUpperCoordinates, h]]
    exact (measurable_pi_apply _).comp measurable_snd

/-- The canonical site order is total. -/
theorem siteLE_reverse_of_not (p : Params) (a b : Site p.n p.W)
    (h : ¬ siteLE p a b) : siteLE p b a := by
  unfold siteLE at h ⊢
  exact Nat.le_of_lt (Nat.lt_of_not_ge h)

/-- Reconstruct a full matrix from upper-triangular coordinates, filling the
strict lower triangle by complex conjugation. -/
def matrixOfUpperCoordinates (p : Params) (z : UpperPair p → ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ := fun a b =>
  if h : siteLE p a b then z ⟨(a, b), h⟩
  else star (z ⟨(b, a), siteLE_reverse_of_not p a b h⟩)

/-- Upper-coordinate reconstruction is measurable entrywise. -/
theorem measurable_matrixOfUpperCoordinates (p : Params) :
    Measurable (matrixOfUpperCoordinates p) := by
  rw [Matrix.measurable_iff]
  intro a b
  by_cases h : siteLE p a b
  · rw [show (fun z => matrixOfUpperCoordinates p z a b) =
        (fun z => z (⟨(a, b), h⟩ : UpperPair p)) by
          funext z
          simp [matrixOfUpperCoordinates, h]]
    exact measurable_pi_apply _
  · have hba : siteLE p b a := by
      unfold siteLE at h ⊢
      omega
    rw [show (fun z => matrixOfUpperCoordinates p z a b) =
        (fun z => star (z (⟨(b, a), hba⟩ : UpperPair p))) by
          funext z
          simp [matrixOfUpperCoordinates, h]]
    exact Complex.continuous_conj.measurable.comp (measurable_pi_apply _)

/-- A Hermitian matrix is exactly recovered from its selected upper entries. -/
theorem matrixOfUpperCoordinates_entries
    {p : Params} {A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ}
    (hA : A.IsHermitian) :
    matrixOfUpperCoordinates p (fun q => A q.1.1 q.1.2) = A := by
  ext a b
  by_cases h : siteLE p a b
  · simp [matrixOfUpperCoordinates, h]
  · have hab := congrFun (congrFun hA a) b
    simpa [matrixOfUpperCoordinates, h, Matrix.conjTranspose_apply] using hab

/-- The measurable product reconstruction from exposed and exterior vectors. -/
def reconstructFromBlockSplit (p : Params) (j : ZMod p.n)
    (z : (diagonalBlockUpperPairs p j → ℂ) ×
      (exteriorUpperPairs p j → ℂ)) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  matrixOfUpperCoordinates p (mergeUpperCoordinates p j z.1 z.2)

/-- The full split-coordinate reconstruction is measurable. -/
theorem measurable_reconstructFromBlockSplit (p : Params) (j : ZMod p.n) :
    Measurable (reconstructFromBlockSplit p j) :=
  (measurable_matrixOfUpperCoordinates p).comp
    (measurable_mergeUpperCoordinates p j)

/-- Applying the reconstruction to the two random coordinate vectors recovers
the original physical matrix pointwise. -/
theorem Law.reconstructFromBlockSplit_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    reconstructFromBlockSplit p j
      (M.diagonalBlockUpperCoordinates j ω,
        M.exteriorUpperCoordinates j ω) = M.H ω := by
  rw [reconstructFromBlockSplit]
  have hcoord : mergeUpperCoordinates p j
      (M.diagonalBlockUpperCoordinates j ω)
      (M.exteriorUpperCoordinates j ω) =
      fun q => M.H ω q.1.1 q.1.2 := by
    funext q
    exact M.mergeUpperCoordinates_apply j ω q
  rw [hcoord]
  exact matrixOfUpperCoordinates_entries (M.H_hermitian ω)

/-- Reconstruct the exposed principal block from the exposed upper vector alone.
Exterior coordinates are filled by zero, which cannot affect this principal
submatrix. -/
def diagonalBlockFromUpperCoordinates (p : Params) (j : ZMod p.n)
    (x : diagonalBlockUpperPairs p j → ℂ) :
    Matrix (Fin p.W) (Fin p.W) ℂ :=
  (reconstructFromBlockSplit p j
    (x, fun _ => 0)).submatrix (fun a => (j, a)) (fun a => (j, a))

/-- The exposed-block reconstruction is measurable. -/
theorem measurable_diagonalBlockFromUpperCoordinates
    (p : Params) (j : ZMod p.n) :
    Measurable (diagonalBlockFromUpperCoordinates p j) := by
  have hpair : Measurable (fun x : diagonalBlockUpperPairs p j → ℂ =>
      (x, fun _ : exteriorUpperPairs p j => (0 : ℂ))) :=
    measurable_id.prodMk measurable_const
  have hfull := (measurable_reconstructFromBlockSplit p j).comp hpair
  rw [Matrix.measurable_iff]
  intro a b
  exact (Matrix.measurable_iff.mp hfull) (j, a) (j, b)

/-- The exposed-coordinate reconstruction recovers the sampled principal block
pointwise. -/
theorem Law.diagonalBlockFromUpperCoordinates_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    diagonalBlockFromUpperCoordinates p j
      (M.diagonalBlockUpperCoordinates j ω) = M.diagonalBlock j ω := by
  ext a b
  change matrixOfUpperCoordinates p
      (mergeUpperCoordinates p j (M.diagonalBlockUpperCoordinates j ω)
        (fun _ => 0)) (j, a) (j, b) = M.H ω (j, a) (j, b)
  by_cases h : siteLE p (j, a) (j, b)
  · let q : UpperPair p := ⟨((j, a), (j, b)), h⟩
    have hq : q ∈ diagonalBlockUpperPairs p j :=
      (mem_diagonalBlockUpperPairs_iff p j q).2 ⟨rfl, rfl⟩
    rw [matrixOfUpperCoordinates, dite_eq_left h]
    change mergeUpperCoordinates p j (M.diagonalBlockUpperCoordinates j ω)
      (fun _ => 0) q = M.H ω (j, a) (j, b)
    rw [mergeUpperCoordinates_of_mem p j _ _ q hq]
    rfl
  · have hrev : siteLE p (j, b) (j, a) :=
      siteLE_reverse_of_not p (j, a) (j, b) h
    let q : UpperPair p := ⟨((j, b), (j, a)), hrev⟩
    have hq : q ∈ diagonalBlockUpperPairs p j :=
      (mem_diagonalBlockUpperPairs_iff p j q).2 ⟨rfl, rfl⟩
    rw [matrixOfUpperCoordinates, dite_eq_right h]
    change star (mergeUpperCoordinates p j
      (M.diagonalBlockUpperCoordinates j ω) (fun _ => 0) q) =
      M.H ω (j, a) (j, b)
    rw [mergeUpperCoordinates_of_mem p j _ _ q hq]
    exact congrFun (congrFun (M.H_hermitian ω) (j, a)) (j, b)

/-- The `sqrt c`-normalized physical diagonal block.  Its target variance is
`1/W`, exactly the one-block `BlockGUE` normalization. -/
def Law.normalizedDiagonalBlock
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    Matrix (Fin p.W) (Fin p.W) ℂ :=
  ((Real.sqrt p.c)⁻¹ : ℂ) • M.diagonalBlock j ω

/-- The normalized diagonal block remains measurable. -/
theorem Law.measurable_normalizedDiagonalBlock
    {p : Params} (M : Law p) (j : ZMod p.n) :
    Measurable (M.normalizedDiagonalBlock j) := by
  rw [Matrix.measurable_iff]
  intro a b
  change Measurable (fun ω =>
    ((Real.sqrt p.c)⁻¹ : ℂ) * M.H ω (j, a) (j, b))
  exact measurable_const.mul (M.measurable_entry (j, a) (j, b))

/-- The normalized diagonal block remains Hermitian because `sqrt c` is real. -/
theorem Law.normalizedDiagonalBlock_isHermitian
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    (M.normalizedDiagonalBlock j ω).IsHermitian := by
  rw [Matrix.IsHermitian, Law.normalizedDiagonalBlock,
    Matrix.conjTranspose_smul, M.diagonalBlock_isHermitian j ω]
  simp

/-- Multiplying the normalized block back by `sqrt c` recovers the physical
block exactly. -/
theorem Law.sqrt_smul_normalizedDiagonalBlock
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    ((Real.sqrt p.c : ℝ) : ℂ) • M.normalizedDiagonalBlock j ω =
      M.diagonalBlock j ω := by
  rw [Law.normalizedDiagonalBlock, ← mul_smul]
  have hsqrt : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  simp [hsqrt]

/-- Normalize a reconstructed exposed block by the physical factor `sqrt c`. -/
def normalizedDiagonalBlockFromUpperCoordinates
    (p : Params) (j : ZMod p.n)
    (x : diagonalBlockUpperPairs p j → ℂ) :
    Matrix (Fin p.W) (Fin p.W) ℂ :=
  ((Real.sqrt p.c)⁻¹ : ℂ) • diagonalBlockFromUpperCoordinates p j x

/-- The normalized reconstruction is measurable. -/
theorem measurable_normalizedDiagonalBlockFromUpperCoordinates
    (p : Params) (j : ZMod p.n) :
    Measurable (normalizedDiagonalBlockFromUpperCoordinates p j) := by
  rw [Matrix.measurable_iff]
  intro a b
  change Measurable (fun x => ((Real.sqrt p.c)⁻¹ : ℂ) *
    diagonalBlockFromUpperCoordinates p j x a b)
  exact measurable_const.mul
    ((Matrix.measurable_iff.mp
      (measurable_diagonalBlockFromUpperCoordinates p j)) a b)

/-- Normalized exposed-coordinate reconstruction agrees with the normalized
physical principal block. -/
theorem Law.normalizedDiagonalBlockFromUpperCoordinates_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    normalizedDiagonalBlockFromUpperCoordinates p j
      (M.diagonalBlockUpperCoordinates j ω) =
      M.normalizedDiagonalBlock j ω := by
  rw [normalizedDiagonalBlockFromUpperCoordinates,
    Law.normalizedDiagonalBlock,
    M.diagonalBlockFromUpperCoordinates_coordinates j ω]

/-- The normalized exposed physical block is independent of the complete
exterior coordinate vector.  Thus the deterministic reconstruction and
`sqrt c` rescaling preserve the product split. -/
theorem Law.indepFun_normalizedDiagonalBlock_exterior
    {p : Params} (M : Law p) (j : ZMod p.n) :
    IndepFun (M.normalizedDiagonalBlock j)
      (M.exteriorUpperCoordinates j) M.P := by
  have h := (M.indepFun_diagonalBlockUpperCoordinates_exterior j).comp
    (measurable_normalizedDiagonalBlockFromUpperCoordinates p j) measurable_id
  have heq : normalizedDiagonalBlockFromUpperCoordinates p j ∘
      M.diagonalBlockUpperCoordinates j = M.normalizedDiagonalBlock j := by
    funext ω
    exact M.normalizedDiagonalBlockFromUpperCoordinates_coordinates j ω
  rw [heq] at h
  have heq₂ : id ∘ M.exteriorUpperCoordinates j =
      M.exteriorUpperCoordinates j := rfl
  rw [heq₂] at h
  exact h

/-- The normalized block and exterior vector have the exact product
pushforward law. -/
theorem Law.map_prod_normalizedDiagonalBlock_exterior
    {p : Params} (M : Law p) (j : ZMod p.n) :
    Measure.map (fun ω =>
      (M.normalizedDiagonalBlock j ω, M.exteriorUpperCoordinates j ω)) M.P =
      (Measure.map (M.normalizedDiagonalBlock j) M.P).prod
        (Measure.map (M.exteriorUpperCoordinates j) M.P) := by
  exact (M.indepFun_normalizedDiagonalBlock_exterior j).map_prod_eq_prod_map_map
    (M.measurable_normalizedDiagonalBlock j).aemeasurable
    (M.measurable_exteriorUpperCoordinates j).aemeasurable

/-- Reindex the normalized physical block on the singleton `BlockGUE` index
space. -/
def Law.normalizedSingletonBlock
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ :=
  (M.normalizedDiagonalBlock j ω).submatrix (fun a => a.2) (fun a => a.2)

/-- The reindexed normalized singleton block is measurable. -/
theorem Law.measurable_normalizedSingletonBlock
    {p : Params} (M : Law p) (j : ZMod p.n) :
    Measurable (M.normalizedSingletonBlock j) := by
  rw [Matrix.measurable_iff]
  intro a b
  exact (Matrix.measurable_iff.mp
    (M.measurable_normalizedDiagonalBlock j)) a.2 b.2

/-- The reindexed normalized singleton block is Hermitian. -/
theorem Law.normalizedSingletonBlock_isHermitian
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    (M.normalizedSingletonBlock j ω).IsHermitian := by
  simpa only [Law.normalizedSingletonBlock] using
    (M.normalizedDiagonalBlock_isHermitian j ω).submatrix
      (fun a : BlockGUE.Index (singletonBlockSize p.W) => a.2)

/-- The law transport after deterministic reconstruction and normalization: a
standard singleton `BlockGUE.Law` with the law of the normalized block.
Constructing it amounts to transporting the real Gaussian laws under division
by `sqrt c`; it is constructed as `Law.normalizedDiagonalBlockGUECoupling`.  No
Schur or expectation assertion is stored. -/
structure NormalizedDiagonalBlockGUECoupling
    {p : Params} (M : Law p) (j : ZMod p.n) where
  exposed : BlockGUE.Law (singletonBlockSize p.W)
    (singletonBlockSize_pos p.W_pos)
  identDistrib : IdentDistrib (M.normalizedSingletonBlock j) exposed.G
    M.P exposed.P

/-- The variance scaling is exactly the PSSS normalization: division by
`sqrt c` sends `c/W` to `1/W`. -/
theorem normalizedDiagonalBlock_variance (p : Params) :
    (Real.sqrt p.c)⁻¹ ^ 2 * (p.c / (p.W : ℝ)) = 1 / (p.W : ℝ) := by
  have hc : 0 ≤ p.c := p.c_pos.le
  have hsqrt : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  rw [inv_pow, Real.sq_sqrt hc]
  field_simp [p.c_pos.ne', Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.W_pos)]

end GaussianRing

end CoareaNative.BlockBand
