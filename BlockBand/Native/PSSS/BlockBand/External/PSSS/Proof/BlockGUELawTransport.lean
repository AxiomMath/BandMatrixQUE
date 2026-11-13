module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Interface
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.PublicGUE
public import Mathlib.Probability.HasLaw

/-!
# Exact transport from the BlockGUE input contract

The `BlockGUE.Law` interface is not an opaque matrix measure: it supplies all
upper-entry marginal laws and their joint independence.  This module packages
those data as one canonical finite coordinate product and proves equality of
the complete matrix law, and of every deterministic Hermitian deformation.

The coordinate convention is the one fixed by `BlockGUE.indexLE`.  A
coordinate is the pair `(re, im)`.  Diagonal coordinates have law
`N(0,1/d_j)` with identically-zero imaginary part; strict upper coordinates
inside block `j` have two independent `N(0,1/(2 d_j))` components; coordinates
between different blocks are identically zero.  Thus this is an executable
canonical normalized block-GUE product.  The public single-block `GUE` law is
built from the equivalent `Fin d` strict-upper ordering.  Equality with that
presentation additionally requires transporting between those two arbitrary
finite orderings; the exact all-block law needed by `BlockGUE.deformed` does
not depend on choosing such an ordering adapter.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BlockGUE

local instance upperPairFintype {k : ℕ} (d : Fin k → ℕ) :
    Fintype (UpperPair d) := by
  unfold UpperPair
  infer_instance

/-- The real and imaginary components used for every canonical upper entry. -/
abbrev UpperRealPair := ℝ × ℝ

/-- The component law of one upper entry in the exact PSSS normalization. -/
def canonicalUpperPairMeasure {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) (q : UpperPair d) : Measure UpperRealPair :=
  if hdiag : q.1.1 = q.1.2 then
    Measure.map (fun x : ℝ => (x, 0))
      (gaussianReal 0 ⟨entryVariance d q.1.1 q.1.1,
        entryVariance_nonneg hd q.1.1 q.1.1⟩)
  else if hblock : q.1.1.1 = q.1.2.1 then
    (gaussianReal 0 ⟨entryVariance d q.1.1 q.1.2 / 2,
      div_nonneg (entryVariance_nonneg hd q.1.1 q.1.2) (by norm_num)⟩).prod
    (gaussianReal 0 ⟨entryVariance d q.1.1 q.1.2 / 2,
      div_nonneg (entryVariance_nonneg hd q.1.1 q.1.2) (by norm_num)⟩)
  else
    Measure.dirac (0, 0)

/-- The finite product of all normalized block-GUE upper coordinates. -/
def canonicalUpperCoordinateMeasure {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) : Measure (UpperPair d → UpperRealPair) :=
  Measure.pi (canonicalUpperPairMeasure d hd)

/-- Turn a real component pair into its complex upper entry. -/
def complexOfUpperRealPair (z : UpperRealPair) : ℂ :=
  (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- Forming the complex upper entry from its two real components is measurable. -/
theorem measurable_complexOfUpperRealPair :
    Measurable complexOfUpperRealPair := by
  unfold complexOfUpperRealPair
  fun_prop

/-- The raw matrix reconstructed from upper-entry real coordinates. -/
def matrixOfUpperCoordinatesRaw {k : ℕ} (d : Fin k → ℕ)
    (z : UpperPair d → UpperRealPair) : Matrix (Index d) (Index d) ℂ :=
  fun x y =>
      if hxy : x = y then (z ⟨(x, y), by
        show ((Fintype.equivFin (Index d)) x).val ≤
          ((Fintype.equivFin (Index d)) y).val
        simp [hxy]⟩).1
      else if hle : indexLE d x y then
        complexOfUpperRealPair (z ⟨(x, y), hle⟩)
      else
        star (complexOfUpperRealPair
          (z ⟨(y, x), by
            unfold indexLE at hle ⊢
            exact Nat.le_of_lt (lt_of_not_ge hle)⟩))

/-- The raw upper-coordinate reconstruction is Hermitian. -/
theorem matrixOfUpperCoordinatesRaw_isHermitian {k : ℕ} (d : Fin k → ℕ)
    (z : UpperPair d → UpperRealPair) :
    (matrixOfUpperCoordinatesRaw d z).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Matrix.conjTranspose_apply, matrixOfUpperCoordinatesRaw]
  · by_cases hle : indexLE d x y
    · have hnot : ¬ indexLE d y x := by
        intro hyx
        apply hxy
        apply (Fintype.equivFin (Index d)).injective
        apply Fin.ext
        exact Nat.le_antisymm hle hyx
      have hyx_ne : y ≠ x := Ne.symm hxy
      simp [Matrix.conjTranspose_apply, matrixOfUpperCoordinatesRaw,
        hxy, hyx_ne, hle, hnot]
    · have hyx : indexLE d y x := by
        unfold indexLE at hle ⊢
        exact Nat.le_of_lt (lt_of_not_ge hle)
      have hyx_ne : y ≠ x := Ne.symm hxy
      simp [Matrix.conjTranspose_apply, matrixOfUpperCoordinatesRaw,
        hxy, hyx_ne, hle, hyx]

/-- Reconstruct a Hermitian matrix from the upper-entry real coordinates.
The imaginary part of a diagonal coordinate is deliberately ignored. -/
def matrixOfUpperCoordinates {k : ℕ} (d : Fin k → ℕ)
    (z : UpperPair d → UpperRealPair) : HermitianMatrix (Index d) :=
  ⟨matrixOfUpperCoordinatesRaw d z,
    matrixOfUpperCoordinatesRaw_isHermitian d z⟩

/-- Hermitian upper-coordinate reconstruction is Borel measurable. -/
theorem measurable_matrixOfUpperCoordinates {k : ℕ} (d : Fin k → ℕ) :
    Measurable (matrixOfUpperCoordinates d) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  unfold matrixOfUpperCoordinatesRaw
  split_ifs
  · fun_prop
  · exact measurable_complexOfUpperRealPair.comp (measurable_pi_apply _)
  · exact Complex.continuous_conj.measurable.comp
      (measurable_complexOfUpperRealPair.comp (measurable_pi_apply _))

/-- The executable canonical normalized block-GUE matrix law. -/
def canonicalMatrixMeasure {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) : Measure (HermitianMatrix (Index d)) :=
  Measure.map (matrixOfUpperCoordinates d)
    (canonicalUpperCoordinateMeasure d hd)

/-- Upper real-coordinate extraction from a supplied law. -/
def Law.upperRealCoordinates {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd) (ω : M.Ω)
    (q : UpperPair d) : UpperRealPair :=
  ((M.G ω q.1.1 q.1.2).re, (M.G ω q.1.1 q.1.2).im)

/-- Extracted upper real-coordinate pairs are jointly independent. -/
theorem Law.upperRealCoordinates_iIndep {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd) :
    iIndepFun (fun q ω => M.upperRealCoordinates ω q) M.P := by
  exact M.upper_independent.comp
    (fun _ => fun z : ℂ => (z.re, z.im)) (fun _ => by fun_prop)

/-- One extracted upper pair has exactly its canonical normalized component
law, including the diagonal and cross-block degeneracies. -/
theorem Law.upperRealCoordinates_hasLaw {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd) (q : UpperPair d) :
    HasLaw (fun ω => M.upperRealCoordinates ω q)
      (canonicalUpperPairMeasure d hd q) M.P := by
  rcases q with ⟨⟨x, y⟩, hxy⟩
  by_cases hdiag : x = y
  · subst y
    rw [show canonicalUpperPairMeasure d hd ⟨(x, x), hxy⟩ =
        Measure.map (fun r : ℝ => (r, (0 : ℝ)))
          (gaussianReal 0 ⟨entryVariance d x x,
            entryVariance_nonneg hd x x⟩) by
      simp [canonicalUpperPairMeasure]]
    have hbase := M.diagonal_re_law x
    have hmap : HasLaw (fun ω => ((M.G ω x x).re, (0 : ℝ)))
        (Measure.map (fun r : ℝ => (r, (0 : ℝ)))
          (gaussianReal 0 ⟨entryVariance d x x,
            entryVariance_nonneg hd x x⟩)) M.P := by
      exact (hasLaw_map (by fun_prop : AEMeasurable
        (fun r : ℝ => (r, (0 : ℝ)))
        (gaussianReal 0 ⟨entryVariance d x x,
          entryVariance_nonneg hd x x⟩))).fun_comp hbase
    refine HasLaw.congr
      (X := fun ω => ((M.G ω x x).re, (0 : ℝ)))
      (Y := fun ω => M.upperRealCoordinates ω ⟨(x, x), hxy⟩)
      hmap ?_
    filter_upwards [M.diagonal_im_zero x] with ω hω
    simp [Law.upperRealCoordinates, hω]
  · by_cases hblock : x.1 = y.1
    · rw [show canonicalUpperPairMeasure d hd ⟨(x, y), hxy⟩ =
          (gaussianReal 0 ⟨entryVariance d x y / 2,
            div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩).prod
          (gaussianReal 0 ⟨entryVariance d x y / 2,
            div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩) by
        simp [canonicalUpperPairMeasure, hdiag, hblock]]
      simpa [Law.upperRealCoordinates] using
        (indepFun_iff_hasLaw_prodMk_prod
        (M.offdiag_re_law x y hxy hdiag hblock)
        (M.offdiag_im_law x y hxy hdiag hblock)).mp
          (M.offdiag_components_independent x y hxy hdiag hblock)
    · rw [show canonicalUpperPairMeasure d hd ⟨(x, y), hxy⟩ =
          Measure.dirac (0, 0) by
        simp [canonicalUpperPairMeasure, hdiag, hblock]]
      have hzero : (fun ω => M.upperRealCoordinates ω ⟨(x, y), hxy⟩) =ᵐ[M.P]
          (fun _ => (0, 0)) := by
        filter_upwards [M.block_diagonal x y hblock] with ω hω
        simp [Law.upperRealCoordinates, hω]
      have hc : HasLaw (fun _ : M.Ω => ((0, 0) : UpperRealPair))
          (Measure.dirac (0, 0)) M.P := by
        refine ⟨measurable_const.aemeasurable, ?_⟩
        simp
      exact hc.congr hzero

/-- The whole extracted upper-coordinate vector has the canonical finite
product law. -/
theorem Law.hasLaw_upperRealCoordinates {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd) :
    HasLaw (fun ω q => M.upperRealCoordinates ω q)
      (canonicalUpperCoordinateMeasure d hd) M.P := by
  unfold canonicalUpperCoordinateMeasure
  exact (M.upperRealCoordinates_iIndep).hasLaw_pi M.upperRealCoordinates_hasLaw

/-- Reconstruction from all upper real coordinates recovers every supplied
Hermitian matrix pointwise. -/
theorem Law.matrixOfUpperCoordinates_upperRealCoordinates {k : ℕ}
    {d : Fin k → ℕ} {hd : ∀ j, 0 < d j} (M : Law d hd) (ω : M.Ω) :
    matrixOfUpperCoordinates d (M.upperRealCoordinates ω) =
      ⟨M.G ω, M.hermitian ω⟩ := by
  apply Subtype.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    change matrixOfUpperCoordinatesRaw d (M.upperRealCoordinates ω) x x =
      M.G ω x x
    rw [show matrixOfUpperCoordinatesRaw d (M.upperRealCoordinates ω) x x =
        ((M.G ω x x).re : ℂ) by
      simp [matrixOfUpperCoordinatesRaw, Law.upperRealCoordinates]]
    exact (M.hermitian ω).coe_re_apply_self x
  · by_cases hle : indexLE d x y
    · change matrixOfUpperCoordinatesRaw d (M.upperRealCoordinates ω) x y =
        M.G ω x y
      simp [matrixOfUpperCoordinatesRaw, hxy, hle,
        complexOfUpperRealPair, Law.upperRealCoordinates]
    · have hherm := congrFun (congrFun (M.hermitian ω) y) x
      simp only [Matrix.conjTranspose_apply] at hherm
      change matrixOfUpperCoordinatesRaw d (M.upperRealCoordinates ω) x y =
        M.G ω x y
      simp [matrixOfUpperCoordinatesRaw, hxy, hle,
        complexOfUpperRealPair, Law.upperRealCoordinates, ← hherm]

/-- Every supplied executable `BlockGUE.Law` has exactly the canonical
independent normalized block-GUE matrix law. -/
theorem Law.hasLaw_matrix_canonical {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd) :
    HasLaw (fun ω => (⟨M.G ω, M.hermitian ω⟩ : HermitianMatrix (Index d)))
      (canonicalMatrixMeasure d hd) M.P := by
  have hrec : HasLaw
      (fun ω => matrixOfUpperCoordinates d (M.upperRealCoordinates ω))
      (canonicalMatrixMeasure d hd) M.P := by
    exact (hasLaw_map (measurable_matrixOfUpperCoordinates d).aemeasurable).fun_comp
      M.hasLaw_upperRealCoordinates
  apply hrec.congr
  filter_upwards with ω
  exact (M.matrixOfUpperCoordinates_upperRealCoordinates ω).symm

/-- Adding an arbitrary deterministic Hermitian deformation preserves the
exact transport; this is the law used by the PSSS interval-count interface. -/
theorem Law.hasLaw_deformed_canonical {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd)
    (A₀ : HermitianMatrix (Index d)) :
    HasLaw (BlockGUE.deformed M A₀)
      (Measure.map (fun H : HermitianMatrix (Index d) =>
        (⟨A₀.1 + H.1, A₀.2.add H.2⟩ : HermitianMatrix (Index d)))
        (canonicalMatrixMeasure d hd)) M.P := by
  have hmap := hasLaw_map (by fun_prop : AEMeasurable
    (fun H : HermitianMatrix (Index d) =>
      (⟨A₀.1 + H.1, A₀.2.add H.2⟩ : HermitianMatrix (Index d)))
    (canonicalMatrixMeasure d hd))
  have h := hmap.fun_comp M.hasLaw_matrix_canonical
  apply h.congr
  filter_upwards with ω
  rfl

end BlockGUE
end PSSSNative.BlockBand
