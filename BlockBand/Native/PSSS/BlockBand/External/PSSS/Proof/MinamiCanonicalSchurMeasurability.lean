module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCanonicalSchurData
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerPerronPassage

/-!
# Joint measurability of canonical PSSS Schur data

The canonical Schur complement, its Hermitian background and its positive absorber depend
measurably on the blocks, the energy and the regulator. Consequently the canonical background and
absorber of the selected block, as functions of the exterior sample, the energy and the regulator,
are measurable.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- A measurable block/energy/regulator family has a measurable totalized
canonical Schur complement.  No invertibility hypothesis is needed for this
measurability statement. -/
theorem measurable_canonicalFrozenSchur
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Ω → Matrix m m ℂ) (B : Ω → Matrix m n ℂ)
    (C : Ω → Matrix n m ℂ) (D : Ω → Matrix n n ℂ)
    (e eta : Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hD : Measurable D)
    (he : Measurable e) (heta : Measurable eta) :
    Measurable (fun ω => canonicalFrozenSchur
      (A ω) (B ω) (C ω) (D ω) (e ω) (eta ω)) := by
  let Ar : Ω → Matrix m m ℂ := fun ω =>
    A ω - (e ω : ℂ) • (1 : Matrix m m ℂ) +
      Complex.I • (eta ω • (1 : Matrix m m ℂ))
  let Dr : Ω → Matrix n n ℂ := fun ω =>
    frozenExteriorRegulated (D ω) (e ω) (eta ω)
  have hAr : Measurable Ar := by
    rw [Matrix.measurable_iff]
    intro i j
    simp only [Ar, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have hDr : Measurable Dr := by
    rw [Matrix.measurable_iff]
    intro i j
    simp only [Dr, frozenExteriorRegulated, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have hBD : Measurable (fun ω => B ω * (Dr ω)⁻¹) :=
    Measurable.matrixMul hB (Measurable.matrixNonsingInv hDr)
  have hBDC : Measurable (fun ω => B ω * (Dr ω)⁻¹ * C ω) :=
    Measurable.matrixMul hBD hC
  have hout : Measurable (fun ω => Ar ω - B ω * (Dr ω)⁻¹ * C ω) := by
    rw [Matrix.measurable_iff]
    intro i j
    exact (Matrix.measurable_iff.mp hAr i j).sub
      (Matrix.measurable_iff.mp hBDC i j)
  simpa only [canonicalFrozenSchur, Ar, Dr] using hout

/-- Joint measurability of the canonical Hermitian background. -/
theorem measurable_canonicalFrozenBackground
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Ω → Matrix m m ℂ) (B : Ω → Matrix m n ℂ)
    (C : Ω → Matrix n m ℂ) (D : Ω → Matrix n n ℂ)
    (e eta : Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hD : Measurable D)
    (he : Measurable e) (heta : Measurable eta) :
    Measurable (fun ω => canonicalFrozenBackground
      (A ω) (B ω) (C ω) (D ω) (e ω) (eta ω)) := by
  have hS := measurable_canonicalFrozenSchur A B C D e eta
    hA hB hC hD he heta
  rw [Matrix.measurable_iff]
  intro i j
  simp only [canonicalFrozenBackground, matrixHermitianPart,
    Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
  exact measurable_const.mul
    ((Matrix.measurable_iff.mp hS i j).add
      (Complex.continuous_conj.measurable.comp
        (Matrix.measurable_iff.mp hS j i)))

/-- Joint measurability of the canonical absorber, including a varying
regulator. -/
theorem measurable_canonicalFrozenAbsorber
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Ω → Matrix m m ℂ) (B : Ω → Matrix m n ℂ)
    (C : Ω → Matrix n m ℂ) (D : Ω → Matrix n n ℂ)
    (e eta : Ω → ℝ)
    (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hD : Measurable D)
    (he : Measurable e) (heta : Measurable eta) :
    Measurable (fun ω => canonicalFrozenAbsorber
      (A ω) (B ω) (C ω) (D ω) (e ω) (eta ω)) := by
  have hS := measurable_canonicalFrozenSchur A B C D e eta
    hA hB hC hD he heta
  rw [Matrix.measurable_iff]
  intro i j
  simp only [canonicalFrozenAbsorber, matrixImaginaryPart,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.conjTranspose_apply]
  fun_prop

/-- Recombining an exterior sample with the zero selected sample is measurable. -/
theorem measurable_frozenExteriorPublicSample {k : ℕ}
    (dims : Fin k → ℕ) (j : Fin k) :
    Measurable (frozenExteriorPublicSample dims j) := by
  unfold frozenExteriorPublicSample
  exact (BlockProductDisintegration.split dims j).symm.measurable.comp
    (measurable_id.prodMk measurable_const)

/-- The reindexed public deformation is measurable in the exterior sample. -/
theorem measurable_frozenExteriorReindexed {k : ℕ}
    (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k) :
    Measurable (frozenExteriorReindexed A₀ j) := by
  have hraw : Measurable (fun G =>
      (publicBlockDeformation A₀
        (frozenExteriorPublicSample dims j G)).1) :=
    measurable_subtype_coe.comp
      ((measurable_publicBlockDeformation dims A₀).comp
        (measurable_frozenExteriorPublicSample dims j))
  rw [Matrix.measurable_iff]
  intro x y
  exact (Matrix.measurable_iff.mp hraw
    (selectedBlockSplitEquiv dims j x)
    (selectedBlockSplitEquiv dims j y))

/-- The canonical background of the selected block, as a function of the exterior sample,
the energy and the regulator. -/
def publicFrozenCanonicalBackground {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (p : (BlockProductDisintegration.ExteriorSample dims j × ℝ) × ℝ) :
    Matrix (Fin (dims j)) (Fin (dims j)) ℂ :=
  canonicalFrozenBackground
    (frozenSelectedA A₀ j p.1.1) (frozenSelectedB A₀ j p.1.1)
    (frozenSelectedC A₀ j p.1.1) (frozenSelectedD A₀ j p.1.1)
    p.1.2 p.2

/-- The canonical absorber of the selected block, with the same joint parameters. -/
def publicFrozenCanonicalAbsorber {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (p : (BlockProductDisintegration.ExteriorSample dims j × ℝ) × ℝ) :
    Matrix (Fin (dims j)) (Fin (dims j)) ℂ :=
  canonicalFrozenAbsorber
    (frozenSelectedA A₀ j p.1.1) (frozenSelectedB A₀ j p.1.1)
    (frozenSelectedC A₀ j p.1.1) (frozenSelectedD A₀ j p.1.1)
    p.1.2 p.2

/-- `publicFrozenCanonicalBackground` is jointly measurable in the exterior sample, the
energy and the regulator. -/
theorem measurable_publicFrozenCanonicalBackground {k : ℕ}
    (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k) :
    Measurable (publicFrozenCanonicalBackground A₀ j) := by
  let M := fun p : (BlockProductDisintegration.ExteriorSample dims j × ℝ) × ℝ =>
    frozenExteriorReindexed A₀ j p.1.1
  have hM : Measurable M :=
    (measurable_frozenExteriorReindexed dims A₀ j).comp
      (measurable_fst.comp measurable_fst)
  have hA : Measurable (fun p => (M p).submatrix
      (Sum.inl : Fin (dims j) → Fin (dims j) ⊕
        {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inl) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inl x) (Sum.inl y)
  have hB : Measurable (fun p => (M p).submatrix
      (Sum.inl : Fin (dims j) → Fin (dims j) ⊕
        {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inr) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inl x) (Sum.inr y)
  have hC : Measurable (fun p => (M p).submatrix
      (Sum.inr : {x : BlockGUE.Index dims // x.1 ≠ j} →
        Fin (dims j) ⊕ {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inl) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inr x) (Sum.inl y)
  have hD : Measurable (fun p => (M p).submatrix
      (Sum.inr : {x : BlockGUE.Index dims // x.1 ≠ j} →
        Fin (dims j) ⊕ {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inr) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inr x) (Sum.inr y)
  change Measurable (fun p => canonicalFrozenBackground
    ((M p).submatrix Sum.inl Sum.inl)
    ((M p).submatrix Sum.inl Sum.inr)
    ((M p).submatrix Sum.inr Sum.inl)
    ((M p).submatrix Sum.inr Sum.inr) p.1.2 p.2)
  exact measurable_canonicalFrozenBackground
    (fun p => (M p).submatrix Sum.inl Sum.inl)
    (fun p => (M p).submatrix Sum.inl Sum.inr)
    (fun p => (M p).submatrix Sum.inr Sum.inl)
    (fun p => (M p).submatrix Sum.inr Sum.inr)
    (fun p => p.1.2) (fun p => p.2)
    hA hB hC hD
    (measurable_snd.comp measurable_fst) measurable_snd

/-- `publicFrozenCanonicalAbsorber` is jointly measurable in the exterior sample, the energy
and the regulator. -/
theorem measurable_publicFrozenCanonicalAbsorber {k : ℕ}
    (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k) :
    Measurable (publicFrozenCanonicalAbsorber A₀ j) := by
  let M := fun p : (BlockProductDisintegration.ExteriorSample dims j × ℝ) × ℝ =>
    frozenExteriorReindexed A₀ j p.1.1
  have hM : Measurable M :=
    (measurable_frozenExteriorReindexed dims A₀ j).comp
      (measurable_fst.comp measurable_fst)
  have hA : Measurable (fun p => (M p).submatrix
      (Sum.inl : Fin (dims j) → Fin (dims j) ⊕
        {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inl) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inl x) (Sum.inl y)
  have hB : Measurable (fun p => (M p).submatrix
      (Sum.inl : Fin (dims j) → Fin (dims j) ⊕
        {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inr) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inl x) (Sum.inr y)
  have hC : Measurable (fun p => (M p).submatrix
      (Sum.inr : {x : BlockGUE.Index dims // x.1 ≠ j} →
        Fin (dims j) ⊕ {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inl) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inr x) (Sum.inl y)
  have hD : Measurable (fun p => (M p).submatrix
      (Sum.inr : {x : BlockGUE.Index dims // x.1 ≠ j} →
        Fin (dims j) ⊕ {x : BlockGUE.Index dims // x.1 ≠ j}) Sum.inr) := by
    rw [Matrix.measurable_iff]
    intro x y
    exact Matrix.measurable_iff.mp hM (Sum.inr x) (Sum.inr y)
  change Measurable (fun p => canonicalFrozenAbsorber
    ((M p).submatrix Sum.inl Sum.inl)
    ((M p).submatrix Sum.inl Sum.inr)
    ((M p).submatrix Sum.inr Sum.inl)
    ((M p).submatrix Sum.inr Sum.inr) p.1.2 p.2)
  exact measurable_canonicalFrozenAbsorber
    (fun p => (M p).submatrix Sum.inl Sum.inl)
    (fun p => (M p).submatrix Sum.inl Sum.inr)
    (fun p => (M p).submatrix Sum.inr Sum.inl)
    (fun p => (M p).submatrix Sum.inr Sum.inr)
    (fun p => p.1.2) (fun p => p.2)
    hA hB hC hD
    (measurable_snd.comp measurable_fst) measurable_snd

end PSSSNative.BlockBand.PSSS
