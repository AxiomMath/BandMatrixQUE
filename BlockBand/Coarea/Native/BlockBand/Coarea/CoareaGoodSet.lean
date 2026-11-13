module

public import BlockBand.Coarea.Native.BlockBand.Coarea.HermitianSimpleSpectrum
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairJacobianLocal
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.MeasurableMatrixInverse
public import BlockBand.Coarea.Native.BlockBand.Spectral.Measurable.Counts

/-!
# Measurable good sets for eigenpair coarea

The exceptional-set and measurability facts used by the coarea theorem, in explicit
finite-dimensional Hermitian coordinates.  The simple-spectrum discriminant is null, and for
every fixed Hermitian matrix Lebesgue-almost every energy avoids its finite ordered spectrum.
Consequently the corresponding pole and complementary-collision sets are null for
product Lebesgue measure, and for every measure absolutely continuous with respect to
that product measure.

The core density below records exactly the squared complementary gap determinant and
the additive inertia sector; no random-matrix law is involved.

Normalization: ordered ranks are zero-based in Lean, so the rank condition of the complete
coarea formula is written without truncated subtraction as `N_R(E) + N_-(M) + 1 = r.val + 1`.
There are no asymptotic parameters or limit orders in this file.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal

/-- Shift a Hermitian matrix by a real energy, retaining the Hermitian subtype. -/
def shiftedHermitianFinCoordinates (d : ℕ)
    (x : HermitianCoordinateSpace d) (E : ℝ) : HermitianMatrix (Fin d) :=
  ⟨(hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ) - (E : ℂ) • 1, by
    change (((hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ) -
      (E : ℂ) • 1)ᴴ) = _
    rw [Matrix.conjTranspose_sub, (hermitianOfFinCoordinates d x).property.eq]
    simp⟩

/-- The shifted Hermitian coordinate family is Borel measurable jointly in the
matrix coordinates and the real energy. -/
theorem measurable_shiftedHermitianFinCoordinates (d : ℕ) :
    Measurable (fun z : HermitianCoordinateSpace d × ℝ =>
      shiftedHermitianFinCoordinates d z.1 z.2) := by
  apply Measurable.subtype_mk
  have hA : Measurable (fun z : HermitianCoordinateSpace d × ℝ =>
      ((hermitianOfFinCoordinates d z.1 : HermitianMatrix (Fin d)) :
        Matrix (Fin d) (Fin d) ℂ)) :=
    measurable_subtype_coe.comp
      ((measurable_hermitianOfFinCoordinates d).comp measurable_fst)
  rw [Matrix.measurable_iff]
  intro i j
  change Measurable (fun z : HermitianCoordinateSpace d × ℝ =>
    (hermitianOfFinCoordinates d z.1 : Matrix (Fin d) (Fin d) ℂ) i j -
      ((z.2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) i j)
  exact (hA.eval_matrix (i := i) (j := j)).sub
    (measurable_snd.complex_ofReal.smul measurable_const |>.eval_matrix)

/-- Strict negative inertia of the shifted matrix, `N_-(H-E)`. -/
def shiftedInertia (d : ℕ)
    (x : HermitianCoordinateSpace d) (E : ℝ) : ℕ :=
  inertia (shiftedHermitianFinCoordinates d x E)

/-- Shifted inertia is jointly Borel measurable. -/
theorem measurable_shiftedInertia (d : ℕ) :
    Measurable (fun z : HermitianCoordinateSpace d × ℝ =>
      shiftedInertia d z.1 z.2) :=
  measurable_inertia.comp (measurable_shiftedHermitianFinCoordinates d)

/-- The pole-free locus for an exterior Hermitian matrix and an energy.  It is
expressed through the complete increasing ordered spectrum, so it is total and
requires no inverse or simplicity hypothesis. -/
def coareaExteriorPoleFree (d : ℕ) :
    Set (HermitianCoordinateSpace d × ℝ) :=
  {z | ∀ r : Fin (Fintype.card (Fin d)),
    orderedEigenvalue (hermitianOfFinCoordinates d z.1) r ≠ z.2}

/-- The exterior pole-free locus is Borel measurable. -/
theorem measurableSet_coareaExteriorPoleFree (d : ℕ) :
    MeasurableSet (coareaExteriorPoleFree d) := by
  simp only [coareaExteriorPoleFree, ofPred_forall]
  apply MeasurableSet.iInter
  intro r
  have h := ((measurableSet_singleton 0).preimage
    (((measurable_orderedEigenvalue_hermitianOfFinCoordinates d r).comp
      measurable_fst).sub measurable_snd)).compl
  convert h using 1
  ext z
  simp [sub_eq_zero]

/-- For a fixed exterior matrix, Lebesgue-almost every energy avoids every one
of its ordered eigenvalues. -/
theorem ae_coareaExteriorPoleFree_energy (d : ℕ)
    (x : HermitianCoordinateSpace d) :
    ∀ᵐ E ∂(volume : Measure ℝ), (x, E) ∈ coareaExteriorPoleFree d := by
  change ∀ᵐ E ∂(volume : Measure ℝ), ∀ r,
    orderedEigenvalue (hermitianOfFinCoordinates d x) r ≠ E
  rw [ae_all_iff]
  intro r
  rw [ae_iff]
  have hset : {E : ℝ |
      ¬orderedEigenvalue (hermitianOfFinCoordinates d x) r ≠ E} =
      {orderedEigenvalue (hermitianOfFinCoordinates d x) r} := by
    ext E
    simp [eq_comm]
  rw [hset]
  exact Real.volume_singleton

/-- Exterior poles form a null set for product Lebesgue measure. -/
theorem volume_coareaExteriorPoleFree_compl (d : ℕ) :
    (volume.prod volume) (coareaExteriorPoleFree d)ᶜ = 0 := by
  rw [Measure.measure_prod_null (measurableSet_coareaExteriorPoleFree d).compl]
  apply Filter.Eventually.of_forall
  intro x
  change volume (Prod.mk x ⁻¹' (coareaExteriorPoleFree d)ᶜ) = (0 : ℝ≥0∞)
  have hset : Prod.mk x ⁻¹' (coareaExteriorPoleFree d)ᶜ =
      {E : ℝ | (x, E) ∉ coareaExteriorPoleFree d} := by
    ext E
    simp
  rw [hset]
  exact ae_iff.mp (ae_coareaExteriorPoleFree_energy d x)

/-- Any law with a joint density in exterior coordinates and energy inherits
pole avoidance.  In particular this is the exact transfer lemma for a concrete
Gaussian density once that density has been constructed. -/
theorem ae_coareaExteriorPoleFree_of_absolutelyContinuous (d : ℕ)
    {μ : Measure (HermitianCoordinateSpace d × ℝ)}
    (hμ : μ ≪ (volume.prod volume)) :
    ∀ᵐ z ∂μ, z ∈ coareaExteriorPoleFree d := by
  rw [ae_iff]
  exact hμ (volume_coareaExteriorPoleFree_compl d)

/-- The squared complementary spectral-gap determinant in explicit Hermitian
coordinates.  This is the nonnegative `det(M)^2` factor in
the complete coarea formula. -/
def coareaGapWeight (d : ℕ)
    (E : ℝ) (x : HermitianCoordinateSpace d) : ℝ :=
  eigenpairLocalRealJacobianDensity E
    (hermitianOfFinCoordinates d x : Matrix (Fin d) (Fin d) ℂ)

/-- The complementary gap weight is jointly Borel measurable. -/
theorem measurable_coareaGapWeight (d : ℕ) :
    Measurable (fun z : ℝ × HermitianCoordinateSpace d =>
      coareaGapWeight d z.1 z.2) := by
  rw [show (fun z : ℝ × HermitianCoordinateSpace d => coareaGapWeight d z.1 z.2) =
      fun z => Complex.normSq
        (eigenpairGapMatrix z.1
          (hermitianOfFinCoordinates d z.2 : Matrix (Fin d) (Fin d) ℂ)).det by
    funext z
    exact eigenpairLocalRealJacobianDensity_eq_normSq_det _ _]
  apply Complex.continuous_normSq.measurable.comp
  apply Measurable.matrixDet
  have hB : Measurable (fun z : ℝ × HermitianCoordinateSpace d =>
      ((hermitianOfFinCoordinates d z.2 : HermitianMatrix (Fin d)) :
        Matrix (Fin d) (Fin d) ℂ)) :=
    measurable_subtype_coe.comp
      ((measurable_hermitianOfFinCoordinates d).comp measurable_snd)
  rw [Matrix.measurable_iff]
  intro i j
  simp only [eigenpairGapMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (measurable_fst.complex_ofReal.mul measurable_const).sub
    (hB.eval_matrix (i := i) (j := j))

/-- The complementary collision-free locus, expressed by avoidance of the
complete ordered spectrum. -/
def coareaComplementCollisionFree (d : ℕ) :
    Set (HermitianCoordinateSpace d × ℝ) :=
  coareaExteriorPoleFree d

/-- The complementary collision-free locus is Borel measurable. -/
theorem measurableSet_coareaComplementCollisionFree (d : ℕ) :
    MeasurableSet (coareaComplementCollisionFree d) :=
  measurableSet_coareaExteriorPoleFree d

/-- For each fixed complementary Hermitian matrix, almost every energy avoids
its ordered spectrum.  This is the collision exclusion required before using the
nonzero-gap form of the local chart. -/
theorem ae_coareaComplementCollisionFree_energy (d : ℕ)
    (x : HermitianCoordinateSpace d) :
    ∀ᵐ E ∂(volume : Measure ℝ),
      (x, E) ∈ coareaComplementCollisionFree d := by
  exact ae_coareaExteriorPoleFree_energy d x

/-- Complementary spectral collisions form a product-Lebesgue-null set. -/
theorem volume_coareaComplementCollisionFree_compl (d : ℕ) :
    (volume.prod volume) (coareaComplementCollisionFree d)ᶜ = 0 := by
  exact volume_coareaExteriorPoleFree_compl d

/-- Coordinates entering the additive inertia sector: exterior matrix, energy,
and Hermitian complementary block. -/
abbrev CoareaSectorCoordinates (dR dM : ℕ) :=
  HermitianCoordinateSpace dR × (ℝ × HermitianCoordinateSpace dM)

/-- The additive one-based rank represented by exterior and complementary
inertias at a fixed energy. -/
def coareaRankIndex (dR dM : ℕ)
    (z : CoareaSectorCoordinates dR dM) : ℕ :=
  shiftedInertia dR z.1 z.2.1 + shiftedInertia dM z.2.2 z.2.1 + 1

/-- The additive coarea rank is Borel measurable. -/
theorem measurable_coareaRankIndex (dR dM : ℕ) :
    Measurable (coareaRankIndex dR dM) := by
  exact (((measurable_shiftedInertia dR).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      ((measurable_shiftedInertia dM).comp
        ((measurable_snd.comp measurable_snd).prodMk
          (measurable_fst.comp measurable_snd)))).add_const 1

/-- The total, subtraction-free fixed-rank sector. -/
def coareaRankSector (dR dM : ℕ) (α : ℕ) :
    Set (CoareaSectorCoordinates dR dM) :=
  {z | coareaRankIndex dR dM z = α + 1}

/-- The fixed-rank inertia sector is Borel measurable. -/
theorem measurableSet_coareaRankSector (dR dM : ℕ) (α : ℕ) :
    MeasurableSet (coareaRankSector dR dM α) := by
  exact (measurableSet_singleton (α + 1)).preimage
    (measurable_coareaRankIndex dR dM)

/-- The analytic good set before selecting an inertia sector: the exterior
matrix has simple spectrum, the physical energy is not an exterior pole, and
the complementary block has no eigenvalue at that energy. -/
def coareaAnalyticGoodSet (dR dM : ℕ) :
    Set (CoareaSectorCoordinates dR dM) :=
  {z | z.1 ∈ hermitianSimpleSpectrumCoordinates dR ∧
    (z.1, z.2.1) ∈ coareaExteriorPoleFree dR ∧
    (z.2.2, z.2.1) ∈ coareaComplementCollisionFree dM}

/-- The analytic coarea good set is Borel measurable. -/
theorem measurableSet_coareaAnalyticGoodSet (dR dM : ℕ) :
    MeasurableSet (coareaAnalyticGoodSet dR dM) := by
  apply MeasurableSet.inter
  · exact (measurableSet_hermitianSimpleSpectrumCoordinates dR).preimage
      measurable_fst
  · apply MeasurableSet.inter
    · exact (measurableSet_coareaExteriorPoleFree dR).preimage
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact (measurableSet_coareaComplementCollisionFree dM).preimage
        ((measurable_snd.comp measurable_snd).prodMk
          (measurable_fst.comp measurable_snd))

/-- The good set at a fixed one-based rank `α + 1`. -/
def coareaFixedRankGoodSet (dR dM : ℕ) (α : ℕ) :
    Set (CoareaSectorCoordinates dR dM) :=
  coareaAnalyticGoodSet dR dM ∩ coareaRankSector dR dM α

/-- The fixed-rank good set is Borel measurable. -/
theorem measurableSet_coareaFixedRankGoodSet (dR dM : ℕ) (α : ℕ) :
    MeasurableSet (coareaFixedRankGoodSet dR dM α) :=
  (measurableSet_coareaAnalyticGoodSet dR dM).inter
    (measurableSet_coareaRankSector dR dM α)

/-- The squared gap determinant is nonnegative pointwise. -/
theorem coareaGapWeight_nonneg (d : ℕ) (E : ℝ)
    (x : HermitianCoordinateSpace d) :
    0 ≤ coareaGapWeight d E x := by
  rw [coareaGapWeight, eigenpairLocalRealJacobianDensity_eq_normSq_det]
  exact Complex.normSq_nonneg _

/-- The determinant-and-inertia core of the coarea density, without the regression and
crossing factors. -/
def coareaCoreDensity (dR dM : ℕ) (α : ℕ)
    (z : CoareaSectorCoordinates dR dM) : ℝ≥0∞ := by
  classical
  exact if z ∈ coareaRankSector dR dM α then
    ENNReal.ofReal (coareaGapWeight dM z.2.1 z.2.2)
  else 0

/-- The determinant-and-inertia core density is Borel measurable. -/
theorem measurable_coareaCoreDensity (dR dM : ℕ) (α : ℕ) :
    Measurable (coareaCoreDensity dR dM α) := by
  unfold coareaCoreDensity
  apply Measurable.ite (measurableSet_coareaRankSector dR dM α)
  · exact ENNReal.measurable_ofReal.comp
      ((measurable_coareaGapWeight dM).comp
        ((measurable_fst.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_snd)))
  · exact measurable_const

/-- The explicit simple-spectrum good set is measurable and has full volume. -/
theorem ae_hermitianSimpleSpectrumCoordinates (d : ℕ) :
    ∀ᵐ x ∂(volume : Measure (HermitianCoordinateSpace d)),
      x ∈ hermitianSimpleSpectrumCoordinates d := by
  rw [ae_iff]
  exact volume_hermitianSimpleSpectrumCoordinates_compl d

/-- Absolute continuity transfers the unconditional discriminant exclusion to
any concrete Hermitian coordinate law with a density. -/
theorem ae_hermitianSimpleSpectrumCoordinates_of_absolutelyContinuous
    (d : ℕ) {μ : Measure (HermitianCoordinateSpace d)} (hμ : μ ≪ volume) :
    ∀ᵐ x ∂μ, x ∈ hermitianSimpleSpectrumCoordinates d := by
  rw [ae_iff]
  exact hμ (volume_hermitianSimpleSpectrumCoordinates_compl d)

end CoareaNative.BlockBand
