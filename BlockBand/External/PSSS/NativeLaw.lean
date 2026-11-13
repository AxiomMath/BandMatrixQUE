module

public import Mathlib
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Concrete independent normalized block-GUE law

The finite domain is `Σ j : Fin k, Fin (d j)`, with all `d j > 0` and `k = 0`
allowed. The concrete measure is the finite product of real Gaussian upper
coordinates followed by Hermitian reconstruction. Diagonal variance is `1/d j`;
strict upper real and imaginary variances are `1/(2*d j)`; cross-block entries
vanish. Supplied law fields assert exactly these distributions and joint
independence, without any spectral or moment bound.

Exact matrix and arbitrary deterministic Hermitian deformation law transport
is proved. No physical ring characteristic-law bridge, counting estimate,
asymptotic regime, or analytic constructor is included. The cited native
all-order theorem is checked separately; importing this module does not import
its historical dependency closure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.External.PSSS

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Finite complex Hermitian matrices with inherited topology and measurable space. -/
abbrev HermitianMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  {A : Matrix ι ι ℂ // A.IsHermitian}

namespace BlockGUE

/-- The coordinate space for a family of blocks. -/
abbrev Index {k : ℕ} (d : Fin k → ℕ) := Σ j, Fin (d j)

/-- The canonical finite ordering used to select upper-triangular entries. -/
def indexLE {k : ℕ} (d : Fin k → ℕ) (x y : Index d) : Prop :=
  (Fintype.equivFin (Index d) x).val ≤ (Fintype.equivFin (Index d) y).val

instance {k : ℕ} (d : Fin k → ℕ) (x y : Index d) : Decidable (indexLE d x y) :=
  by unfold indexLE; infer_instance

/-- Upper-triangular coordinates of the full block-diagonal noise matrix. -/
def UpperPair {k : ℕ} (d : Fin k → ℕ) :=
  {q : Index d × Index d // indexLE d q.1 q.2}

/-- Total variance of one within-block complex entry in the PSSS normalization. -/
def entryVariance {k : ℕ} (d : Fin k → ℕ) (x y : Index d) : ℝ :=
  if x.1 = y.1 then 1 / (d x.1 : ℝ) else 0

/-- Nonnegativity of the PSSS variance when all blocks are nonempty. -/
theorem entryVariance_nonneg {k : ℕ} {d : Fin k → ℕ}
    (hd : ∀ j, 0 < d j) (x y : Index d) : 0 ≤ entryVariance d x y := by
  unfold entryVariance
  split_ifs
  · exact one_div_nonneg.mpr (by exact_mod_cast (hd x.1).le)
  · exact le_rfl

/-- The PSSS block-GUE law at variance `1 / d_j` in block `j`.

The contract records the source normalization and all independence assertions
used downstream.  It is deliberately separate from the ring law: conditioning
on the ring bonds produces a deterministic deformation plus a law of this
shape for its diagonal blocks. -/
structure Law {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) where
  Ω : Type*
  mΩ : MeasurableSpace Ω
  P : Measure Ω
  probability : IsProbabilityMeasure P
  G : Ω → Matrix (Index d) (Index d) ℂ
  hermitian : ∀ ω, (G ω).IsHermitian
  measurable_entry : ∀ x y, Measurable (fun ω => G ω x y)
  block_diagonal : ∀ x y, x.1 ≠ y.1 → ∀ᵐ ω ∂P, G ω x y = 0
  upper_independent :
    @iIndepFun Ω (UpperPair d) mΩ
      (fun _ => ℂ) (fun _ => Complex.measurableSpace)
      (fun q ω => G ω q.1.1 q.1.2) P
  diagonal_im_zero : ∀ x, ∀ᵐ ω ∂P, (G ω x x).im = 0
  diagonal_re_law : ∀ x,
    HasLaw (fun ω => (G ω x x).re)
      (gaussianReal 0 ⟨entryVariance d x x, entryVariance_nonneg hd x x⟩) P
  offdiag_components_independent : ∀ x y, indexLE d x y → x ≠ y → x.1 = y.1 →
    IndepFun (fun ω => (G ω x y).re) (fun ω => (G ω x y).im) P
  offdiag_re_law : ∀ x y, indexLE d x y → x ≠ y → x.1 = y.1 →
    HasLaw (fun ω => (G ω x y).re)
      (gaussianReal 0 ⟨entryVariance d x y / 2,
        div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩) P
  offdiag_im_law : ∀ x y, indexLE d x y → x ≠ y → x.1 = y.1 →
    HasLaw (fun ω => (G ω x y).im)
      (gaussianReal 0 ⟨entryVariance d x y / 2,
        div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩) P

attribute [instance] Law.mΩ Law.probability

/-- A sample of block-GUE noise is Hermitian. -/
theorem Law.isHermitian {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : Law d hd) (ω : M.Ω) : (M.G ω).IsHermitian := M.hermitian ω

end BlockGUE

end BlockBand.External.PSSS

namespace BlockBand.External.PSSS

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

/-- Add an arbitrary deterministic Hermitian deformation, with no norm bound. -/
def deformed {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : Law d hd) (A₀ : HermitianMatrix (Index d)) (ω : M.Ω) :
    HermitianMatrix (Index d) :=
  ⟨A₀.1 + M.G ω, A₀.2.add (M.hermitian ω)⟩

/-- Every concrete normalized upper-entry component law is a probability
measure, including the zero cross-block law. No estimate is assumed. -/
theorem canonicalUpperPairMeasure_probability {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) (q : UpperPair d) :
    IsProbabilityMeasure (canonicalUpperPairMeasure d hd q) := by
  unfold canonicalUpperPairMeasure
  split_ifs
  · constructor
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]
    exact (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _).measure_univ
  · have : IsProbabilityMeasure (gaussianReal 0
        ⟨entryVariance d q.1.1 q.1.2 / 2,
          div_nonneg (entryVariance_nonneg hd _ _) (by norm_num)⟩) :=
      ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
    infer_instance
  · infer_instance

/-- The finite independent normalized Gaussian coordinate product is a
probability measure, including the empty family. -/
theorem canonicalUpperCoordinateMeasure_probability {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) :
    IsProbabilityMeasure (canonicalUpperCoordinateMeasure d hd) := by
  have : ∀ q : UpperPair d, IsProbabilityMeasure (canonicalUpperPairMeasure d hd q) :=
    canonicalUpperPairMeasure_probability d hd
  unfold canonicalUpperCoordinateMeasure
  infer_instance

/-- The reconstructed normalized block-GUE matrix measure is a probability
measure. -/
theorem canonicalMatrixMeasure_probability {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) : IsProbabilityMeasure (canonicalMatrixMeasure d hd) := by
  have := canonicalUpperCoordinateMeasure_probability d hd
  constructor
  rw [canonicalMatrixMeasure, Measure.map_apply
    (measurable_matrixOfUpperCoordinates d) MeasurableSet.univ]
  simp

/-- Concrete Gaussian coordinates give the declared matrix law by measurable
reconstruction. This is a named finite source-law constructor with no analytic
PSSS bound or physical-ring premise. -/
theorem hasLaw_canonicalReconstruction {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) :
    HasLaw (matrixOfUpperCoordinates d) (canonicalMatrixMeasure d hd)
      (canonicalUpperCoordinateMeasure d hd) :=
  hasLaw_map (measurable_matrixOfUpperCoordinates d).aemeasurable

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

/-- Measure-map form of the exact canonical law transport. -/
theorem Law.map_matrix_eq_canonical {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd) :
    Measure.map (fun ω => (⟨M.G ω, M.hermitian ω⟩ :
      HermitianMatrix (Index d))) M.P = canonicalMatrixMeasure d hd :=
  M.hasLaw_matrix_canonical.map_eq

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

/-- Measure-map adapter for the deformed law. -/
theorem Law.map_deformed_eq_canonical {k : ℕ} {d : Fin k → ℕ}
    {hd : ∀ j, 0 < d j} (M : Law d hd)
    (A₀ : HermitianMatrix (Index d)) :
    Measure.map (BlockGUE.deformed M A₀) M.P =
      Measure.map (fun H : HermitianMatrix (Index d) =>
        (⟨A₀.1 + H.1, A₀.2.add H.2⟩ : HermitianMatrix (Index d)))
        (canonicalMatrixMeasure d hd) :=
  (M.hasLaw_deformed_canonical A₀).map_eq

end BlockGUE
end BlockBand.External.PSSS
