module

public import BlockBand.Coarea.Native.BlockBand.Coarea.HermitianSimpleSpectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Phase-fixed affine charts for complex projective eigenvectors

A nonzero complex eigenvector is defined only up to multiplication by a nonzero
complex scalar.  This module constructs the elementary finite affine atlas used
to remove that ambiguity.  On the chart where coordinate `k` is nonzero, all
coordinates are divided by the `k`-th coordinate, so the resulting
representative has `k`-th coordinate exactly `1`.  Its norm-normalization is
therefore a canonical phase-fixed unit representative whose `k`-th coordinate
is positive real.

These results are purely finite-dimensional and do not choose eigenvectors as a
function of a Hermitian matrix.  They supply chart coverage, scalar invariance,
injectivity, and continuous reconstruction for the future measurable
eigenpair atlas, without asserting the unavailable measurable dependence of
Mathlib's chosen eigenbasis or a global coarea theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

set_option linter.unusedSectionVars false

open scoped ComplexConjugate

section Charts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The affine coordinates complementary to a distinguished coordinate `k`. -/
abbrev ProjectiveChartCoordinate (k : ι) := {j : ι // j ≠ k}

/-- Domain of the projective affine chart whose distinguished coordinate is
`k`. -/
def projectiveEigenvectorChartDomain (k : ι) :
    Set (EuclideanSpace ℂ ι) :=
  {v | v k ≠ 0}

/-- Affine projective coordinates obtained by dividing all complementary
coordinates by the nonzero distinguished coordinate. -/
def projectiveEigenvectorChart (k : ι) (v : EuclideanSpace ℂ ι) :
    ProjectiveChartCoordinate k → ℂ :=
  fun j => v j.1 / v k

/-- Each affine chart domain is open (and hence Borel measurable). -/
theorem isOpen_projectiveEigenvectorChartDomain (k : ι) :
    IsOpen (projectiveEigenvectorChartDomain k) := by
  have hcont : Continuous (fun v : EuclideanSpace ℂ ι => v k) :=
    PiLp.continuous_apply 2 (fun _ : ι => ℂ) k
  have hclosed : IsClosed {v : EuclideanSpace ℂ ι | v k = 0} :=
    isClosed_singleton.preimage hcont
  simpa only [projectiveEigenvectorChartDomain, Set.compl_ofPred,
    Classical.not_not] using hclosed.isOpen_compl

/-- Each affine chart domain is Borel measurable. -/
theorem measurableSet_projectiveEigenvectorChartDomain (k : ι) :
    MeasurableSet (projectiveEigenvectorChartDomain k) :=
  (isOpen_projectiveEigenvectorChartDomain k).measurableSet

/-- Affine coordinate extraction is continuous on its chart domain. -/
theorem continuous_projectiveEigenvectorChart_onDomain (k : ι) :
    Continuous (fun v : projectiveEigenvectorChartDomain k =>
      projectiveEigenvectorChart k v.1) := by
  rw [continuous_pi_iff]
  intro j
  apply Continuous.div₀
  · exact (PiLp.continuous_apply 2 (fun _ : ι => ℂ) j.1).comp
      continuous_subtype_val
  · exact (PiLp.continuous_apply 2 (fun _ : ι => ℂ) k).comp
      continuous_subtype_val
  · intro v
    exact v.property

/-- The affine representative of a vector: scalar multiplication makes its
`k`-th coordinate equal to one whenever `v k ≠ 0`. -/
def projectiveAffineRepresentative (k : ι) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  (v k)⁻¹ • v

/-- Reconstruct the affine representative from complementary coordinates by
inserting `1` at the distinguished coordinate. -/
def projectiveEigenvectorReconstruction (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => if h : i = k then 1 else z ⟨i, h⟩

/-- The reconstructed vector has distinguished coordinate one. -/
@[simp] theorem projectiveEigenvectorReconstruction_apply_self (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    projectiveEigenvectorReconstruction k z k = 1 := by
  simp [projectiveEigenvectorReconstruction]

/-- A reconstructed affine representative is nonzero. -/
theorem projectiveEigenvectorReconstruction_ne_zero (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    projectiveEigenvectorReconstruction k z ≠ 0 := by
  intro hz
  have hk : projectiveEigenvectorReconstruction k z k = 0 := by
    rw [hz]
    rfl
  simp at hk

/-- Reconstruction recovers each complementary affine coordinate. -/
@[simp] theorem projectiveEigenvectorReconstruction_apply (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) (j : ProjectiveChartCoordinate k) :
    projectiveEigenvectorReconstruction k z j.1 = z j := by
  simp [projectiveEigenvectorReconstruction, j.property]

/-- The chart is a left inverse to affine reconstruction. -/
@[simp] theorem projectiveEigenvectorChart_reconstruction (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    projectiveEigenvectorChart k (projectiveEigenvectorReconstruction k z) = z := by
  funext j
  simp [projectiveEigenvectorChart]

/-- Affine reconstruction is injective. -/
theorem projectiveEigenvectorReconstruction_injective (k : ι) :
    Function.Injective (projectiveEigenvectorReconstruction k) :=
  Function.LeftInverse.injective (projectiveEigenvectorChart_reconstruction k)

/-- On its domain, the affine representative has distinguished coordinate
exactly one. -/
@[simp] theorem projectiveAffineRepresentative_apply_self (k : ι)
    (v : EuclideanSpace ℂ ι) (hv : v k ≠ 0) :
    projectiveAffineRepresentative k v k = 1 := by
  simp [projectiveAffineRepresentative, hv]

/-- Reconstructing the chart of a vector gives its canonical affine
representative. -/
theorem projectiveEigenvectorReconstruction_chart (k : ι)
    (v : EuclideanSpace ℂ ι) (hv : v k ≠ 0) :
    projectiveEigenvectorReconstruction k (projectiveEigenvectorChart k v) =
      projectiveAffineRepresentative k v := by
  apply PiLp.ext
  intro i
  by_cases hi : i = k
  · subst i
    simp [projectiveAffineRepresentative, hv]
  · simp [projectiveEigenvectorReconstruction, projectiveEigenvectorChart,
      projectiveAffineRepresentative, hi, div_eq_inv_mul]

/-- Affine coordinates are unchanged by multiplication by a nonzero complex
scalar, which is the required projective invariance. -/
theorem projectiveEigenvectorChart_smul (k : ι) (a : ℂ)
    (ha : a ≠ 0) (v : EuclideanSpace ℂ ι) :
    projectiveEigenvectorChart k (a • v) = projectiveEigenvectorChart k v := by
  funext j
  simp only [projectiveEigenvectorChart, PiLp.smul_apply, smul_eq_mul]
  field_simp

/-- Two vectors in the same chart with identical affine coordinates differ by
an explicit nonzero scalar. -/
theorem projectiveEigenvectorChart_eq_iff_smul
    (k : ι) (v w : EuclideanSpace ℂ ι) (hv : v k ≠ 0) (hw : w k ≠ 0) :
    projectiveEigenvectorChart k v = projectiveEigenvectorChart k w ↔
      v = (v k / w k) • w := by
  constructor
  · intro h
    apply PiLp.ext
    intro i
    by_cases hi : i = k
    · subst i
      simp [hw]
    · have hc := congrFun h ⟨i, hi⟩
      simp only [projectiveEigenvectorChart] at hc
      simp only [PiLp.smul_apply, smul_eq_mul]
      calc
        v i = (v i / v k) * v k := by field_simp
        _ = (w i / w k) * v k := by rw [hc]
        _ = (v k / w k) * w i := by field_simp
  · intro heq
    calc
      projectiveEigenvectorChart k v =
          projectiveEigenvectorChart k ((v k / w k) • w) :=
        congrArg (projectiveEigenvectorChart k) heq
      _ = projectiveEigenvectorChart k w :=
        projectiveEigenvectorChart_smul k (v k / w k)
          (div_ne_zero hv hw) w

/-- Every nonzero finite complex vector lies in at least one affine chart. -/
theorem exists_mem_projectiveEigenvectorChartDomain
    (v : EuclideanSpace ℂ ι) (hv : v ≠ 0) :
    ∃ k : ι, v ∈ projectiveEigenvectorChartDomain k := by
  by_contra h
  push Not at h
  apply hv
  apply PiLp.ext
  intro k
  have hk : v k = 0 := by
    simpa [projectiveEigenvectorChartDomain] using h k
  simpa using hk

/-- Unit, phase-fixed reconstruction of affine coordinates.  The norm is the
Euclidean (`ℓ²`) norm inherited by `EuclideanSpace`. -/
def projectiveUnitReconstruction (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) : EuclideanSpace ℂ ι :=
  (‖projectiveEigenvectorReconstruction k z‖⁻¹ : ℝ) •
    projectiveEigenvectorReconstruction k z

/-- The phase-fixed reconstruction is normalized in the paper's
Euclidean norm. -/
@[simp] theorem norm_projectiveUnitReconstruction (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    ‖projectiveUnitReconstruction k z‖ = 1 := by
  exact norm_smul_inv_norm (projectiveEigenvectorReconstruction_ne_zero k z)

/-- The distinguished coordinate of the unit reconstruction is the positive
real inverse norm; this fixes the complex phase. -/
theorem projectiveUnitReconstruction_apply_self (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    projectiveUnitReconstruction k z k =
      ((‖projectiveEigenvectorReconstruction k z‖⁻¹ : ℝ) : ℂ) := by
  simp [projectiveUnitReconstruction]

/-- The distinguished coordinate is strictly positive real, making the phase
choice unique inside this affine chart. -/
theorem projectiveUnitReconstruction_self_re_pos (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    0 < (projectiveUnitReconstruction k z k).re := by
  rw [projectiveUnitReconstruction_apply_self]
  simp only [Complex.ofReal_re]
  exact inv_pos.mpr (norm_pos_iff.mpr
    (projectiveEigenvectorReconstruction_ne_zero k z))

/-- Taking affine coordinates of the unit phase-fixed reconstruction recovers
the original chart coordinate. -/
@[simp] theorem projectiveEigenvectorChart_unitReconstruction (k : ι)
    (z : ProjectiveChartCoordinate k → ℂ) :
    projectiveEigenvectorChart k (projectiveUnitReconstruction k z) = z := by
  have hnorm : ‖projectiveEigenvectorReconstruction k z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (projectiveEigenvectorReconstruction_ne_zero k z)
  have hnormC : ((‖projectiveEigenvectorReconstruction k z‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnorm
  funext j
  simp [projectiveEigenvectorChart, projectiveUnitReconstruction]
  field_simp

/-- The normalized phase-fixed reconstruction is injective. -/
theorem projectiveUnitReconstruction_injective (k : ι) :
    Function.Injective (projectiveUnitReconstruction k) :=
  Function.LeftInverse.injective
    (projectiveEigenvectorChart_unitReconstruction k)

/-- Affine reconstruction is continuous. -/
theorem continuous_projectiveEigenvectorReconstruction (k : ι) :
    Continuous (projectiveEigenvectorReconstruction k) := by
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).comp
  rw [continuous_pi_iff]
  intro i
  by_cases hi : i = k
  · simp only [hi, ↓reduceDIte]
    exact continuous_const
  · simp only [hi, ↓reduceDIte]
    fun_prop

/-- Unit phase-fixed reconstruction is continuous on the entire affine chart. -/
theorem continuous_projectiveUnitReconstruction (k : ι) :
    Continuous (projectiveUnitReconstruction k) := by
  have hrec : Continuous (projectiveEigenvectorReconstruction k) :=
    continuous_projectiveEigenvectorReconstruction k
  have hnorm : Continuous (fun z : ProjectiveChartCoordinate k → ℂ =>
      ‖projectiveEigenvectorReconstruction k z‖) := hrec.norm
  have hne : ∀ z : ProjectiveChartCoordinate k → ℂ,
      ‖projectiveEigenvectorReconstruction k z‖ ≠ 0 := fun z => by
    simp [projectiveEigenvectorReconstruction_ne_zero k z]
  change Continuous (fun z : ProjectiveChartCoordinate k → ℂ =>
    (‖projectiveEigenvectorReconstruction k z‖⁻¹ : ℝ) •
      projectiveEigenvectorReconstruction k z)
  exact (hnorm.inv₀ hne).smul hrec

/-- Consequently the phase-fixed reconstruction is Borel measurable. -/
theorem measurable_projectiveUnitReconstruction (k : ι) :
    Measurable (projectiveUnitReconstruction k) :=
  (continuous_projectiveUnitReconstruction k).measurable

end Charts

end CoareaNative.BlockBand
