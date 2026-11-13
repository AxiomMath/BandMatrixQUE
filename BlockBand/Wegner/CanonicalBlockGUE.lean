module

public import Mathlib
public import BlockBand.External.PSSS.SourceStatement

/-!
# The canonical normalized block-GUE law as a `BlockGUE.Law`

The canonical coordinate measure `canonicalUpperCoordinateMeasure` on upper-triangular real
coordinate pairs (independent Gaussian entries within blocks, zero across blocks) is packaged as
`canonicalLaw : Law d hd`, with every field of `BlockGUE.Law` proved.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory
open BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE

variable {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j)

/-- The finite-type instance on upper pairs used to define `canonicalUpperCoordinateMeasure`. -/
local instance upperPairFintype : Fintype (UpperPair d) := by
  unfold UpperPair
  infer_instance

/-- The scalar upper entry carried by one real coordinate pair. -/
def upperEntryOf (q : UpperPair d) (w : UpperRealPair) : ℂ :=
  if q.1.1 = q.1.2 then (w.1 : ℂ) else complexOfUpperRealPair w

theorem measurable_upperEntryOf (q : UpperPair d) : Measurable (upperEntryOf d q) := by
  unfold upperEntryOf complexOfUpperRealPair
  split_ifs <;> fun_prop

/-- At an upper pair the reconstructed entry depends only on that coordinate. -/
theorem matrixOfUpperCoordinatesRaw_upper (z : UpperPair d → UpperRealPair)
    (q : UpperPair d) :
    matrixOfUpperCoordinatesRaw d z q.1.1 q.1.2 = upperEntryOf d q (z q) := by
  rcases q with ⟨⟨x, y⟩, hxy⟩
  by_cases h : x = y
  · subst h
    simp [matrixOfUpperCoordinatesRaw, upperEntryOf]
  · simp [matrixOfUpperCoordinatesRaw, upperEntryOf, h, hxy]

instance canonicalUpperPairMeasure_isProbability (q : UpperPair d) :
    IsProbabilityMeasure (canonicalUpperPairMeasure d hd q) :=
  canonicalUpperPairMeasure_probability d hd q

instance canonicalUpperCoordinateMeasure_isProbability :
    IsProbabilityMeasure (canonicalUpperCoordinateMeasure d hd) :=
  canonicalUpperCoordinateMeasure_probability d hd

/-- One canonical coordinate has its own component law. -/
theorem hasLaw_canonical_eval (q : UpperPair d) :
    HasLaw (fun z : UpperPair d → UpperRealPair => z q) (canonicalUpperPairMeasure d hd q)
      (canonicalUpperCoordinateMeasure d hd) :=
  (measurePreserving_eval (canonicalUpperPairMeasure d hd) q).hasLaw

/-- The canonical upper pair of a site with itself. -/
def diagonalPair (x : Index d) : UpperPair d := ⟨(x, x), le_rfl⟩

theorem canonicalUpperPairMeasure_diagonal (x : Index d) :
    canonicalUpperPairMeasure d hd (diagonalPair d x) =
      Measure.map (fun r : ℝ => (r, (0 : ℝ)))
        (gaussianReal 0 ⟨entryVariance d x x, entryVariance_nonneg hd x x⟩) := by
  simp [canonicalUpperPairMeasure, diagonalPair]

theorem canonicalUpperPairMeasure_offdiag (x y : Index d) (hxy : indexLE d x y)
    (hne : x ≠ y) (hb : x.1 = y.1) :
    canonicalUpperPairMeasure d hd ⟨(x, y), hxy⟩ =
      (gaussianReal 0 ⟨entryVariance d x y / 2,
          div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩).prod
        (gaussianReal 0 ⟨entryVariance d x y / 2,
          div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩) := by
  simp [canonicalUpperPairMeasure, hne, hb]

theorem canonicalUpperPairMeasure_cross (x y : Index d) (hxy : indexLE d x y)
    (hb : x.1 ≠ y.1) :
    canonicalUpperPairMeasure d hd ⟨(x, y), hxy⟩ = Measure.dirac (0, 0) := by
  have hne : x ≠ y := fun h => hb (by rw [h])
  simp [canonicalUpperPairMeasure, hne, hb]

/-- A cross-block canonical coordinate vanishes almost surely. -/
theorem canonical_eval_ae_zero (x y : Index d) (hxy : indexLE d x y) (hb : x.1 ≠ y.1) :
    ∀ᵐ z ∂(canonicalUpperCoordinateMeasure d hd), z ⟨(x, y), hxy⟩ = (0, 0) := by
  have hdirac : ∀ᵐ w ∂(canonicalUpperPairMeasure d hd ⟨(x, y), hxy⟩),
      w = ((0, 0) : UpperRealPair) := by
    rw [canonicalUpperPairMeasure_cross d hd x y hxy hb]
    exact (ae_dirac_iff (p := fun w : UpperRealPair => w = (0, 0))
      (measurableSet_singleton _)).mpr rfl
  exact (measurePreserving_eval (canonicalUpperPairMeasure d hd)
    ⟨(x, y), hxy⟩).quasiMeasurePreserving.ae hdirac

local instance gaussianReal_isProbability (μ : ℝ) (v : NNReal) :
    IsProbabilityMeasure (gaussianReal μ v) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal μ v

/-- Abbreviation for the canonical coordinate law. -/
abbrev canonicalP : Measure (UpperPair d → UpperRealPair) := canonicalUpperCoordinateMeasure d hd

theorem canonical_measurable_entry (x y : Index d) :
    Measurable (fun z : UpperPair d → UpperRealPair => matrixOfUpperCoordinatesRaw d z x y) := by
  have h := measurable_subtype_coe.comp (measurable_matrixOfUpperCoordinates d)
  exact (Matrix.measurable_iff.mp h) x y

theorem canonical_block_diagonal (x y : Index d) (hb : x.1 ≠ y.1) :
    ∀ᵐ z ∂(canonicalP d hd), matrixOfUpperCoordinatesRaw d z x y = 0 := by
  have hne : x ≠ y := fun h => hb (by rw [h])
  by_cases hle : indexLE d x y
  · filter_upwards [canonical_eval_ae_zero d hd x y hle hb] with z hz
    have h := matrixOfUpperCoordinatesRaw_upper d z ⟨(x, y), hle⟩
    simp only at h
    rw [h, hz]
    simp [upperEntryOf, hne, complexOfUpperRealPair]
  · have hle' : indexLE d y x := by
      unfold indexLE at hle ⊢
      exact Nat.le_of_lt (lt_of_not_ge hle)
    filter_upwards [canonical_eval_ae_zero d hd y x hle' (fun h => hb h.symm)] with z hz
    simp [matrixOfUpperCoordinatesRaw, hne, hle, hz, complexOfUpperRealPair]

theorem canonical_upper_independent :
    iIndepFun (fun (q : UpperPair d) (z : UpperPair d → UpperRealPair) =>
      matrixOfUpperCoordinatesRaw d z q.1.1 q.1.2) (canonicalP d hd) := by
  have h := iIndepFun_pi (μ := canonicalUpperPairMeasure d hd)
    (X := fun q w => upperEntryOf d q w)
    (fun q => (measurable_upperEntryOf d q).aemeasurable)
  have he : (fun (q : UpperPair d) (z : UpperPair d → UpperRealPair) =>
      matrixOfUpperCoordinatesRaw d z q.1.1 q.1.2) =
      (fun q z => upperEntryOf d q (z q)) := by
    funext q z
    exact matrixOfUpperCoordinatesRaw_upper d z q
  rw [he]
  exact h

theorem canonical_diagonal_im_zero (x : Index d) :
    ∀ᵐ z ∂(canonicalP d hd), (matrixOfUpperCoordinatesRaw d z x x).im = 0 := by
  filter_upwards with z
  simp [matrixOfUpperCoordinatesRaw]

theorem canonical_diagonal_re_law (x : Index d) :
    HasLaw (fun z : UpperPair d → UpperRealPair => (matrixOfUpperCoordinatesRaw d z x x).re)
      (gaussianReal 0 ⟨entryVariance d x x, entryVariance_nonneg hd x x⟩) (canonicalP d hd) := by
  have h0 := hasLaw_canonical_eval d hd (diagonalPair d x)
  rw [canonicalUpperPairMeasure_diagonal d hd x] at h0
  have h1 := (hasLaw_map (measurable_fst.aemeasurable)).fun_comp h0
  rw [Measure.map_map measurable_fst (by fun_prop)] at h1
  have hid : (Prod.fst ∘ fun r : ℝ => (r, (0 : ℝ))) = id := rfl
  rw [hid, Measure.map_id] at h1
  have he : (fun z : UpperPair d → UpperRealPair => (matrixOfUpperCoordinatesRaw d z x x).re) =
      (fun z => (z (diagonalPair d x)).1) := by
    funext z
    simp [matrixOfUpperCoordinatesRaw, diagonalPair]
  rw [he]
  exact h1

/-- The variance law of one real component of an off-diagonal within-block entry. -/
abbrev halfLaw (x y : Index d) : Measure ℝ :=
  gaussianReal 0 ⟨entryVariance d x y / 2,
    div_nonneg (entryVariance_nonneg hd x y) (by norm_num)⟩

theorem canonical_offdiag_fst_law (x y : Index d) (hxy : indexLE d x y) (hne : x ≠ y)
    (hb : x.1 = y.1) :
    HasLaw (fun z : UpperPair d → UpperRealPair => (z ⟨(x, y), hxy⟩).1) (halfLaw d hd x y)
      (canonicalP d hd) := by
  have h0 := hasLaw_canonical_eval d hd ⟨(x, y), hxy⟩
  rw [canonicalUpperPairMeasure_offdiag d hd x y hxy hne hb] at h0
  have h1 := (hasLaw_map measurable_fst.aemeasurable).fun_comp h0
  have hP : IsProbabilityMeasure (halfLaw d hd x y) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  have hm : Measure.map Prod.fst ((halfLaw d hd x y).prod (halfLaw d hd x y)) =
      halfLaw d hd x y := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [hm] at h1
  exact h1

theorem canonical_offdiag_snd_law (x y : Index d) (hxy : indexLE d x y) (hne : x ≠ y)
    (hb : x.1 = y.1) :
    HasLaw (fun z : UpperPair d → UpperRealPair => (z ⟨(x, y), hxy⟩).2) (halfLaw d hd x y)
      (canonicalP d hd) := by
  have h0 := hasLaw_canonical_eval d hd ⟨(x, y), hxy⟩
  rw [canonicalUpperPairMeasure_offdiag d hd x y hxy hne hb] at h0
  have h1 := (hasLaw_map measurable_snd.aemeasurable).fun_comp h0
  have hP : IsProbabilityMeasure (halfLaw d hd x y) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  have hm : Measure.map Prod.snd ((halfLaw d hd x y).prod (halfLaw d hd x y)) =
      halfLaw d hd x y := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  rw [hm] at h1
  exact h1

theorem canonical_offdiag_entry (x y : Index d) (hxy : indexLE d x y) (hne : x ≠ y)
    (z : UpperPair d → UpperRealPair) :
    matrixOfUpperCoordinatesRaw d z x y = complexOfUpperRealPair (z ⟨(x, y), hxy⟩) := by
  simp [matrixOfUpperCoordinatesRaw, hne, hxy]

theorem canonical_offdiag_re_law (x y : Index d) (hxy : indexLE d x y) (hne : x ≠ y)
    (hb : x.1 = y.1) :
    HasLaw (fun z : UpperPair d → UpperRealPair => (matrixOfUpperCoordinatesRaw d z x y).re)
      (halfLaw d hd x y) (canonicalP d hd) := by
  have he : (fun z : UpperPair d → UpperRealPair => (matrixOfUpperCoordinatesRaw d z x y).re) =
      (fun z => (z ⟨(x, y), hxy⟩).1) := by
    funext z
    rw [canonical_offdiag_entry d x y hxy hne z]
    simp [complexOfUpperRealPair]
  rw [he]
  exact canonical_offdiag_fst_law d hd x y hxy hne hb

theorem canonical_offdiag_im_law (x y : Index d) (hxy : indexLE d x y) (hne : x ≠ y)
    (hb : x.1 = y.1) :
    HasLaw (fun z : UpperPair d → UpperRealPair => (matrixOfUpperCoordinatesRaw d z x y).im)
      (halfLaw d hd x y) (canonicalP d hd) := by
  have he : (fun z : UpperPair d → UpperRealPair => (matrixOfUpperCoordinatesRaw d z x y).im) =
      (fun z => (z ⟨(x, y), hxy⟩).2) := by
    funext z
    rw [canonical_offdiag_entry d x y hxy hne z]
    simp [complexOfUpperRealPair]
  rw [he]
  exact canonical_offdiag_snd_law d hd x y hxy hne hb

theorem canonical_offdiag_components_independent (x y : Index d) (hxy : indexLE d x y)
    (hne : x ≠ y) (hb : x.1 = y.1) :
    IndepFun (fun z : UpperPair d → UpperRealPair => (matrixOfUpperCoordinatesRaw d z x y).re)
      (fun z => (matrixOfUpperCoordinatesRaw d z x y).im) (canonicalP d hd) := by
  have h0 := hasLaw_canonical_eval d hd ⟨(x, y), hxy⟩
  rw [canonicalUpperPairMeasure_offdiag d hd x y hxy hne hb] at h0
  have hre := canonical_offdiag_re_law d hd x y hxy hne hb
  have him := canonical_offdiag_im_law d hd x y hxy hne hb
  refine (indepFun_iff_hasLaw_prodMk_prod hre him).mpr ?_
  have he : (fun z : UpperPair d → UpperRealPair =>
      ((matrixOfUpperCoordinatesRaw d z x y).re, (matrixOfUpperCoordinatesRaw d z x y).im)) =
      (fun z => z ⟨(x, y), hxy⟩) := by
    funext z
    rw [canonical_offdiag_entry d x y hxy hne z]
    simp [complexOfUpperRealPair]
  simpa only [he] using h0

/-- The canonical normalized block-GUE law, with every `BlockGUE.Law` field proved. -/
def canonicalLaw : Law.{0} d hd where
  Ω := UpperPair d → UpperRealPair
  mΩ := inferInstance
  P := canonicalP d hd
  probability := canonicalUpperCoordinateMeasure_probability d hd
  G := matrixOfUpperCoordinatesRaw d
  hermitian := matrixOfUpperCoordinatesRaw_isHermitian d
  measurable_entry := canonical_measurable_entry d
  block_diagonal := canonical_block_diagonal d hd
  upper_independent := canonical_upper_independent d hd
  diagonal_im_zero := canonical_diagonal_im_zero d hd
  diagonal_re_law := canonical_diagonal_re_law d hd
  offdiag_components_independent := canonical_offdiag_components_independent d hd
  offdiag_re_law := canonical_offdiag_re_law d hd
  offdiag_im_law := canonical_offdiag_im_law d hd

end BlockBand.Wegner
