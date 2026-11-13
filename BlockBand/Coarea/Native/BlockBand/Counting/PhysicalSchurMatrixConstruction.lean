module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalSchurInstantiation

/-!
# Deterministic physical-block reconstruction and the diagonal normalization

This module carries the Gaussian-ring exterior coordinates and an arbitrary normalized
singleton block back to the physical site matrix.  The reconstruction is measurable
and, on the exterior vector and normalized diagonal block, recovers `M.H`
pointwise.

The calculation also isolates an essential normalization issue in the
`PhysicalSchurMatrixData` interface.  The physical diagonal block is
`sqrt p.c • G`, whereas `schurMatrixTrace` inserts the standard `GUE_W(1/W)` matrix
`G` with coefficient one.  Consequently the raw physical absorbed resolvent cannot be
identified with that interface without either rescaling the complete pencil by
`(sqrt p.c)⁻¹` (and tracking the corresponding resolvent factor), assuming `p.c = 1`,
or extending the one-block averaging theorem to a scaled exposed GUE.  No
unscaled Schur instantiation is asserted here.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped ComplexOrder ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Read an upper-triangular physical diagonal-block coordinate from a singleton
`BlockGUE` matrix.  The unique `Fin 1` coordinate is inserted explicitly. -/
def normalizedSingletonUpperCoordinates
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (q : diagonalBlockUpperPairs p j) : ℂ :=
  G ⟨0, q.1.1.1.2⟩ ⟨0, q.1.1.2.2⟩

/-- The upper coordinates inserted into the physical diagonal block.
The coefficient is `sqrt p.c`, not one. -/
def physicalSingletonUpperCoordinates
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (q : diagonalBlockUpperPairs p j) : ℂ :=
  ((Real.sqrt p.c : ℝ) : ℂ) * normalizedSingletonUpperCoordinates p j G q

/-- Reconstruct the physical site matrix from the exterior upper coordinates and a
normalized singleton matrix.  The exposed block is multiplied by `sqrt p.c`. -/
def physicalMatrixFromExteriorNormalizedBlock
    (p : Params) (j : ZMod p.n)
    (z : (exteriorUpperPairs p j → ℂ) ×
      Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  reconstructFromBlockSplit p j
    (physicalSingletonUpperCoordinates p j z.2, z.1)

/-- Reading the physical exposed coordinates displays the exact `sqrt c` coefficient. -/
@[simp] theorem physicalSingletonUpperCoordinates_apply
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (q : diagonalBlockUpperPairs p j) :
    physicalSingletonUpperCoordinates p j G q =
      ((Real.sqrt p.c : ℝ) : ℂ) * G ⟨0, q.1.1.1.2⟩ ⟨0, q.1.1.2.2⟩ := rfl

/-- The physical reconstruction is jointly measurable in the exterior vector and the
normalized exposed matrix. -/
theorem measurable_physicalMatrixFromExteriorNormalizedBlock
    (p : Params) (j : ZMod p.n) :
    Measurable (physicalMatrixFromExteriorNormalizedBlock p j) := by
  apply (measurable_reconstructFromBlockSplit p j).comp
  apply Measurable.prodMk
  rw [measurable_pi_iff]
  · intro q
    change Measurable (fun z : (exteriorUpperPairs p j → ℂ) ×
      Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ =>
      ((Real.sqrt p.c : ℝ) : ℂ) * z.2 (⟨0, q.1.1.1.2⟩ : BlockGUE.Index (singletonBlockSize p.W))
        (⟨0, q.1.1.2.2⟩ : BlockGUE.Index (singletonBlockSize p.W)))
    have hG : Measurable (fun G :
        Matrix (BlockGUE.Index (singletonBlockSize p.W))
          (BlockGUE.Index (singletonBlockSize p.W)) ℂ =>
        G (⟨0, q.1.1.1.2⟩ : BlockGUE.Index (singletonBlockSize p.W))
          (⟨0, q.1.1.2.2⟩ : BlockGUE.Index (singletonBlockSize p.W))) :=
      (measurable_pi_apply (⟨0, q.1.1.2.2⟩ :
        BlockGUE.Index (singletonBlockSize p.W))).comp
        (measurable_pi_apply (⟨0, q.1.1.1.2⟩ :
          BlockGUE.Index (singletonBlockSize p.W)))
    exact measurable_const.mul (hG.comp measurable_snd)
  · exact measurable_fst

/-- The normalized singleton block contains exactly the entries of the normalized
physical diagonal block. -/
@[simp] theorem Law.normalizedSingletonUpperCoordinates_apply
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (q : diagonalBlockUpperPairs p j) :
    normalizedSingletonUpperCoordinates p j (M.normalizedSingletonBlock j ω) q =
      M.normalizedDiagonalBlock j ω q.1.1.1.2 q.1.1.2.2 := rfl

/-- Multiplication by `sqrt c` converts every normalized singleton upper coordinate
back to the corresponding physical upper coordinate. -/
theorem Law.physicalSingletonUpperCoordinates_normalizedSingletonBlock
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    physicalSingletonUpperCoordinates p j (M.normalizedSingletonBlock j ω) =
      M.diagonalBlockUpperCoordinates j ω := by
  funext q
  have hblocks := (mem_diagonalBlockUpperPairs_iff p j q.1).1 q.property
  rcases q with ⟨⟨⟨⟨ka, a⟩, ⟨kb, b⟩⟩, hab⟩, hmem⟩
  simp only at hblocks
  rcases hblocks with ⟨hka, hkb⟩
  subst ka
  subst kb
  have h := congrFun (congrFun (M.sqrt_smul_normalizedDiagonalBlock j ω) a) b
  change ((Real.sqrt p.c : ℝ) : ℂ) * M.normalizedDiagonalBlock j ω a b =
    M.H ω (j, a) (j, b)
  exact h

/-- On the independent exterior vector and normalized exposed block, the
measurable reconstruction recovers the original Gaussian-ring matrix pointwise. -/
theorem Law.physicalMatrixFromExteriorNormalizedBlock_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    physicalMatrixFromExteriorNormalizedBlock p j
      (M.exteriorUpperCoordinates j ω, M.normalizedSingletonBlock j ω) = M.H ω := by
  rw [physicalMatrixFromExteriorNormalizedBlock,
    M.physicalSingletonUpperCoordinates_normalizedSingletonBlock j ω]
  exact M.reconstructFromBlockSplit_coordinates j ω

/-- After division by `sqrt c`, the exposed upper coordinates have coefficient one.
This is the deterministic normalization needed before applying the current
`schurMatrixTrace`/PSSS interface. -/
theorem inv_sqrt_mul_physicalSingletonUpperCoordinates
    (p : Params) (j : ZMod p.n)
    (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
    (q : diagonalBlockUpperPairs p j) :
    ((Real.sqrt p.c)⁻¹ : ℂ) * physicalSingletonUpperCoordinates p j G q =
      normalizedSingletonUpperCoordinates p j G q := by
  have hsqrt : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  simp [physicalSingletonUpperCoordinates, hsqrt]

/-- The coefficient mismatch disappears exactly in the unit-diagonal-variance case.
This scalar statement records why the raw physical pencil cannot in general be fed to
an interface whose exposed GUE coefficient is definitionally one. -/
theorem sqrt_c_eq_one_iff (p : Params) :
    Real.sqrt p.c = 1 ↔ p.c = 1 := by
  constructor
  · intro h
    have hs := Real.sq_sqrt p.c_pos.le
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- Exact deterministic factorization of an absorbed one-block pencil.  Dividing the
complete physical pencil by `sqrt p.c` produces a coefficient-one normalized GUE,
while the background, absorber, and regulator are all divided by the same scalar. -/
theorem physicalAbsorbedPencil_eq_sqrt_smul_normalized
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Params) (G A Q : Matrix ι ι ℂ) (η : ℝ) :
    (((Real.sqrt p.c : ℝ) : ℂ) •
      (G + ((Real.sqrt p.c)⁻¹ : ℂ) • A +
        Complex.I • (((Real.sqrt p.c)⁻¹ : ℂ) • Q +
          ((Real.sqrt p.c)⁻¹ * η : ℝ) • (1 : Matrix ι ι ℂ)))) =
      ((Real.sqrt p.c : ℝ) : ℂ) • G + A +
        Complex.I • (Q + η • (1 : Matrix ι ι ℂ)) := by
  have hsqrtR : Real.sqrt p.c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.c_pos)
  have hsqrtC : (((Real.sqrt p.c : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hsqrtR
  apply Matrix.ext
  intro a b
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, smul_eq_mul]
    simp_rw [Complex.real_smul]
    push_cast
    field_simp [hsqrtC, hsqrtR]
  · simp only [hab, ite_false, smul_eq_mul]
    simp_rw [Complex.real_smul]
    push_cast
    field_simp [hsqrtC, hsqrtR]

/-- Uniformly replacing the physical exposed coefficient by the coefficient-one
`schurMatrixTrace` convention is possible exactly when `p.c = 1`.  The forward
implication tests the identity matrix at one diagonal coordinate; positivity of `W`
provides that coordinate. -/
theorem physicalSingletonUpperCoordinates_eq_normalized_iff (p : Params) :
    (∀ (j : ZMod p.n)
      (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
      (q : diagonalBlockUpperPairs p j),
      physicalSingletonUpperCoordinates p j G q =
        normalizedSingletonUpperCoordinates p j G q) ↔
      p.c = 1 := by
  constructor
  · intro h
    let a : Fin p.W := ⟨0, p.W_pos⟩
    let x : Site p.n p.W := (0, a)
    have hx : siteLE p x x := le_rfl
    let u : UpperPair p := ⟨(x, x), hx⟩
    have hu : u ∈ diagonalBlockUpperPairs p 0 :=
      (mem_diagonalBlockUpperPairs_iff p 0 u).2 ⟨rfl, rfl⟩
    let q : diagonalBlockUpperPairs p 0 := ⟨u, hu⟩
    have htest := h 0 (1 : Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ) q
    have hsqrtC : ((Real.sqrt p.c : ℝ) : ℂ) = 1 := by
      simpa [physicalSingletonUpperCoordinates, normalizedSingletonUpperCoordinates,
        q, u, x, a] using htest
    have hsqrtR : Real.sqrt p.c = 1 := by
      exact_mod_cast hsqrtC
    exact (sqrt_c_eq_one_iff p).1 hsqrtR
  · intro hc j G q
    have hsqrt : Real.sqrt p.c = 1 := (sqrt_c_eq_one_iff p).2 hc
    simp [physicalSingletonUpperCoordinates, hsqrt]

/-- For the paper's parameter range `b > 0`, the physical coefficient mismatch is
not merely possible: it always occurs. -/
theorem not_forall_physicalSingletonUpperCoordinates_eq_normalized (p : Params) :
    ¬ (∀ (j : ZMod p.n)
      (G : Matrix (BlockGUE.Index (singletonBlockSize p.W))
        (BlockGUE.Index (singletonBlockSize p.W)) ℂ)
      (q : diagonalBlockUpperPairs p j),
      physicalSingletonUpperCoordinates p j G q =
        normalizedSingletonUpperCoordinates p j G q) := by
  rw [physicalSingletonUpperCoordinates_eq_normalized_iff]
  exact ne_of_lt p.c_lt_one

end GaussianRing
end CoareaNative.BlockBand
