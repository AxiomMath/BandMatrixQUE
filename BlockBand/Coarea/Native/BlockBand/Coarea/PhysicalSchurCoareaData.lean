module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalFixedRankCoareaFormula

/-!
# Physical Schur data in eigenpair coarea coordinates

This file instantiates the deterministic Schur data of the coarea formula from
fixed exterior data `(H_R,C,V)`.  The sign convention is exactly
`(H_R-E)⁻¹`: `F(E)=V-Cᴴ(H_R-E)⁻¹C`, `T(E)=(H_R-E)⁻¹C`, and
`𝒟(E)=I+T(E)ᴴT(E)`.  The phase-fixed Householder frame of the normalized
affine representative supplies `f(E,v)`, `q(E,v)`, and `F_v(E,v)`.

Matrix inversion is Mathlib's totalized inverse, so the definitions and their
Borel measurability are global.  The pole-free set is where these total
formulas coincide with the ordinary resolvent.  All
claims are finite-dimensional and pointwise; no limiting or uniformity
assertion is made.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ComplexOrder ENNReal

variable {r d : ℕ}

/-- Rectangular finite matrix multiplication preserves measurability. -/
theorem measurable_matrix_mul_rect
    {α : Type*} [MeasurableSpace α]
    {m n p : Type*} [Fintype n]
    {A : α → Matrix m n ℂ} {B : α → Matrix n p ℂ}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x => A x * B x) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  fun_prop

/-- Conjugate transpose preserves measurability of finite matrix families. -/
theorem Measurable.matrix_conjTranspose
    {α : Type*} [MeasurableSpace α] {m n : Type*}
    {A : α → Matrix m n ℂ} (hA : Measurable A) :
    Measurable (fun x => (A x)ᴴ) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.continuous_conj.measurable.comp
    ((Matrix.measurable_apply.comp hA).comp measurable_id)

/-- Totalized physical resolvent `(H_R-E)⁻¹`. -/
def physicalCoareaResolvent
    (H_R : Matrix (Fin r) (Fin r) ℂ) (E : ℝ) :
    Matrix (Fin r) (Fin r) ℂ :=
  (H_R - (E : ℂ) • 1)⁻¹

/-- Pole-free energies for the physical exterior resolvent. -/
def physicalCoareaPoleFreeSet
    (H_R : Matrix (Fin r) (Fin r) ℂ) : Set ℝ :=
  {E | (H_R - (E : ℂ) • 1).det ≠ 0}

/-- The concrete pole-free predicate is exactly invertibility of the exterior
pencil. -/
theorem mem_physicalCoareaPoleFreeSet_iff_isUnit
    (H_R : Matrix (Fin r) (Fin r) ℂ) (E : ℝ) :
    E ∈ physicalCoareaPoleFreeSet H_R ↔
      IsUnit (H_R - (E : ℂ) • 1).det := by
  exact isUnit_iff_ne_zero.symm

/-- The physical Schur transfer `T(E)=(H_R-E)⁻¹C`. -/
def physicalCoareaT
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) (E : ℝ) :
    Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ :=
  physicalCoareaResolvent H_R E * C

/-- The deterministic physical compression
`F(E)=V-Cᴴ(H_R-E)⁻¹C`. -/
def physicalCoareaF
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  V - Cᴴ * physicalCoareaResolvent H_R E * C

/-- The positive Schur clock `𝒟(E)=I+T(E)ᴴT(E)`. -/
def physicalCoareaD
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) (E : ℝ) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  schurClock (physicalCoareaT H_R C E)

/-- Phase-fixed frame whose first column is the normalized affine vector `v`. -/
def physicalCoareaFrame (z : Fin (d - 1) → ℂ) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  phaseFixedHouseholderFrame (Sum.inl Unit.unit)
    (canonicalProjectiveUnitVector z)

/-- The compression `F(E)` in the phase-fixed eigenvector frame. -/
def physicalCoareaFrameCompression
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (z : Fin (d - 1) → ℂ) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  (physicalCoareaFrame z)ᴴ * physicalCoareaF H_R C V E *
    physicalCoareaFrame z

/-- Scalar compression `f(E,v)=vᴴF(E)v`. -/
def physicalCoarea_f
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (z : Fin (d - 1) → ℂ) : ℝ :=
  (physicalCoareaFrameCompression H_R C V E z
    (Sum.inl Unit.unit) (Sum.inl Unit.unit)).re

/-- Perpendicular column `q(E,v)=(I-vvᴴ)F(E)v` in the chosen frame. -/
def physicalCoarea_q
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (z : Fin (d - 1) → ℂ) : Fin (d - 1) → ℂ :=
  fun j => physicalCoareaFrameCompression H_R C V E z
    (Sum.inr j) (Sum.inl Unit.unit)

/-- Complementary compression `F_v(E,v)=U_vᴴF(E)U_v`. -/
def physicalCoareaFv
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (z : Fin (d - 1) → ℂ) :
    Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ :=
  (physicalCoareaFrameCompression H_R C V E z).submatrix Sum.inr Sum.inr

/-- The physical Schur compression is Hermitian. -/
theorem physicalCoareaF_isHermitian
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hR : H_R.IsHermitian) (hV : V.IsHermitian) (E : ℝ) :
    (physicalCoareaF H_R C V E).IsHermitian := by
  have hshift : (H_R - (E : ℂ) • 1).IsHermitian :=
    hR.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  have hterm : (Cᴴ * physicalCoareaResolvent H_R E * C).IsHermitian := by
    simpa [physicalCoareaResolvent, Matrix.mul_assoc] using
      Matrix.isHermitian_mul_mul_conjTranspose Cᴴ hshift.inv
  exact hV.sub hterm

/-- Subtracting `E I` from `F(E)` gives exactly the physical moving
Schur complement of the full block pencil with coupling `Cᴴ`. -/
theorem physicalCoareaF_sub_energy_eq_physicalSchurMatrix
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) :
    physicalCoareaF H_R C V E - (E : ℂ) • 1 =
      physicalSchurMatrix V Cᴴ H_R E := by
  simp only [physicalCoareaF, physicalCoareaResolvent,
    physicalSchurMatrix, physicalRetainedPencil, physicalExteriorPencil,
    Matrix.conjTranspose_conjTranspose]
  abel

/-- The framed physical compression remains Hermitian. -/
theorem physicalCoareaFrameCompression_isHermitian
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hR : H_R.IsHermitian) (hV : V.IsHermitian) (E : ℝ)
    (z : Fin (d - 1) → ℂ) :
    (physicalCoareaFrameCompression H_R C V E z).IsHermitian := by
  simpa [physicalCoareaFrameCompression, Matrix.mul_assoc] using
    Matrix.isHermitian_mul_mul_conjTranspose (physicalCoareaFrame z)ᴴ
      (physicalCoareaF_isHermitian H_R C V hR hV E)

/-- The complementary compression `F_v` is Hermitian. -/
theorem physicalCoareaFv_isHermitian
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hR : H_R.IsHermitian) (hV : V.IsHermitian) (E : ℝ)
    (z : Fin (d - 1) → ℂ) :
    (physicalCoareaFv H_R C V E z).IsHermitian :=
  isHermitian_submatrix_inr
    ⟨physicalCoareaFrameCompression H_R C V E z,
      physicalCoareaFrameCompression_isHermitian H_R C V hR hV E z⟩

/-- The physical clock is positive definite. -/
theorem physicalCoareaD_posDef
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) (E : ℝ) :
    (physicalCoareaD H_R C E).PosDef :=
  schurClock_posDef (physicalCoareaT H_R C E)

/-- The physical clock is positive semidefinite. -/
theorem physicalCoareaD_posSemidef
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) (E : ℝ) :
    (physicalCoareaD H_R C E).PosSemidef :=
  schurClock_posSemidef (physicalCoareaT H_R C E)

/-- Borel measurability of the totalized physical resolvent. -/
theorem measurable_physicalCoareaResolvent
    (H_R : Matrix (Fin r) (Fin r) ℂ) :
    Measurable (physicalCoareaResolvent H_R) := by
  unfold physicalCoareaResolvent
  apply Measurable.matrixNonsingInv
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  fun_prop

/-- The physical pole-free energy set is Borel measurable. -/
theorem measurableSet_physicalCoareaPoleFreeSet
    (H_R : Matrix (Fin r) (Fin r) ℂ) :
    MeasurableSet (physicalCoareaPoleFreeSet H_R) := by
  have hshift : Measurable (fun E : ℝ => H_R - (E : ℂ) •
      (1 : Matrix (Fin r) (Fin r) ℂ)) := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    fun_prop
  change MeasurableSet ((fun E : ℝ =>
    (H_R - (E : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).det) ⁻¹' ({0}ᶜ))
  exact (measurable_matrixDet.comp hshift) (measurableSet_singleton 0).compl

/-- Borel measurability of `T(E)`. -/
theorem measurable_physicalCoareaT
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (physicalCoareaT H_R C) := by
  unfold physicalCoareaT
  exact measurable_matrix_mul_rect
    (measurable_physicalCoareaResolvent H_R) measurable_const

/-- Borel measurability of `F(E)`. -/
theorem measurable_physicalCoareaF
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (physicalCoareaF H_R C V) := by
  unfold physicalCoareaF
  have hterm : Measurable (fun E : ℝ =>
      Cᴴ * physicalCoareaResolvent H_R E * C) :=
    measurable_matrix_mul_rect
      (measurable_matrix_mul_rect measurable_const
        (measurable_physicalCoareaResolvent H_R)) measurable_const
  apply Measurable.of_eval_matrix
  intro i j
  exact measurable_const.sub
    ((Matrix.measurable_iff.mp hterm) i j)

/-- Borel measurability of the positive clock `𝒟(E)`. -/
theorem measurable_physicalCoareaD
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (physicalCoareaD H_R C) := by
  unfold physicalCoareaD schurClock
  have hT := measurable_physicalCoareaT H_R C
  have hprod : Measurable (fun E : ℝ =>
      (physicalCoareaT H_R C E)ᴴ * physicalCoareaT H_R C E) :=
    measurable_matrix_mul_rect (Measurable.matrix_conjTranspose hT) hT
  apply Measurable.of_eval_matrix
  intro i j
  exact measurable_const.add ((Matrix.measurable_iff.mp hprod) i j)

/-- The phase-fixed physical frame is continuous, hence Borel measurable. -/
theorem continuous_physicalCoareaFrame :
    Continuous (physicalCoareaFrame (d := d)) := by
  rw [continuous_iff_continuousAt]
  intro z
  apply (continuousAt_phaseFixedHouseholderFrame
    (Sum.inl Unit.unit) (canonicalProjectiveUnitVector z) ?_).comp
  · exact (continuous_projectiveUnitReconstruction
      (Sum.inl Unit.unit)).continuousAt.comp
      ((canonicalProjectiveChartCoordinatesLinearMap
        (n := Fin (d - 1))).toContinuousLinearMap.continuous.continuousAt)
  · have hp := canonicalProjectiveUnitVector_selected_re_pos z
    linarith

/-- Joint Borel measurability of the framed compression `(E,z) ↦ U_vᴴF(E)U_v`. -/
theorem measurable_physicalCoareaFrameCompression
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (fun p : ℝ × (Fin (d - 1) → ℂ) =>
      physicalCoareaFrameCompression H_R C V p.1 p.2) := by
  unfold physicalCoareaFrameCompression
  exact measurable_matrix_mul_rect
    (measurable_matrix_mul_rect
      (Measurable.matrix_conjTranspose
        ((continuous_physicalCoareaFrame (d := d)).measurable.comp measurable_snd))
      ((measurable_physicalCoareaF H_R C V).comp measurable_fst))
    ((continuous_physicalCoareaFrame (d := d)).measurable.comp measurable_snd)

/-- Joint Borel measurability of `f(E,v)`. -/
theorem measurable_physicalCoarea_f
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (fun p : ℝ × (Fin (d - 1) → ℂ) =>
      physicalCoarea_f H_R C V p.1 p.2) := by
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply.comp
      (measurable_physicalCoareaFrameCompression H_R C V)).comp measurable_id)

/-- Joint Borel measurability of `q(E,v)`. -/
theorem measurable_physicalCoarea_q
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (fun p : ℝ × (Fin (d - 1) → ℂ) =>
      physicalCoarea_q H_R C V p.1 p.2) := by
  rw [measurable_pi_iff]
  intro j
  exact (Matrix.measurable_apply.comp
    (measurable_physicalCoareaFrameCompression H_R C V)).comp measurable_id

/-- Joint Borel measurability of the complementary compression `F_v(E,v)`. -/
theorem measurable_physicalCoareaFv
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (fun p : ℝ × (Fin (d - 1) → ℂ) =>
      physicalCoareaFv H_R C V p.1 p.2) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact (Matrix.measurable_apply.comp
    (measurable_physicalCoareaFrameCompression H_R C V)).comp measurable_id

/-- The generic crossing factor is exactly `vᴴ𝒟(E)v` for the physical data. -/
theorem physicalEigenpairCrossingQuadratic_physicalCoareaT
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (z : Fin (d - 1) → ℂ) :
    physicalEigenpairCrossingQuadratic (physicalCoareaT H_R C E) z =
      (star (canonicalProjectiveUnitVector z) ⬝ᵥ
        (physicalCoareaD H_R C E *ᵥ
          canonicalProjectiveUnitVector z)).re := by
  rfl

/-- The physical crossing factor is strictly positive for every
affine projective coordinate. -/
theorem physicalEigenpairCrossingQuadratic_physicalCoareaT_pos
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (z : Fin (d - 1) → ℂ) :
    0 < physicalEigenpairCrossingQuadratic
      (physicalCoareaT H_R C E) z := by
  have hv : canonicalProjectiveUnitVector z ≠ 0 := by
    intro hzero
    have hn := norm_canonicalProjectiveUnitVector z
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hv' : (fun j => canonicalProjectiveUnitVector z j) ≠ 0 := by
    intro h
    apply hv
    ext j
    exact congrFun h j
  have hpos := schurClock_quadratic_pos (physicalCoareaT H_R C E) hv'
  exact (Complex.pos_iff.mp hpos).1

/-- The physical specialization of the generic fixed-rank coarea density.
Every parameter is computed from `(H_R,C,V)` and the incidence coordinates;
no compression data is taken as a hypothesis. -/
def physicalSchurCoareaDensity
    (α : ℕ) (R : HermitianCoordinateSpace r) (i : Fin d) (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) : ℝ≥0∞ :=
  let y := eigenpairIncidenceCoordinates i x
  physicalEigenpairCoareaDensity α R i t
    (physicalCoarea_f H_R C V y.1 y.2.1)
    (physicalCoarea_q H_R C V y.1 y.2.1)
    (physicalCoareaFv H_R C V y.1 y.2.1)
    (physicalCoareaT H_R C y.1) x

/-- Unfolding the specialization recovers the generic density evaluated at the
energy- and projective-dependent physical Schur data. -/
theorem physicalSchurCoareaDensity_eq
    (α : ℕ) (R : HermitianCoordinateSpace r) (i : Fin d) (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) :
    physicalSchurCoareaDensity α R i t H_R C V x =
      physicalEigenpairCoareaDensity α R i t
        (physicalCoarea_f H_R C V
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1)
        (physicalCoarea_q H_R C V
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1)
        (physicalCoareaFv H_R C V
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1)
        (physicalCoareaT H_R C (eigenpairIncidenceCoordinates i x).1) x := by
  rfl

/-- On the fixed-rank collision-free locus, the specialized
density is the exact product with the physical dependent data and
crossing form `vᴴ𝒟(E)v`.  The projective correction defect is retained. -/
theorem physicalSchurCoareaDensity_eq_explicit
    (α : ℕ) (R : HermitianCoordinateSpace r) (i : Fin d) (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d)
    (hrank : physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2)
    (hgap : (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2.1).det ≠ 0) :
    physicalSchurCoareaDensity α R i t H_R C V x =
      ENNReal.ofReal (coareaGaussianDensityConstant d t) *
      ENNReal.ofReal (canonicalGaussianRegressionFactor
        (eigenpairIncidenceCoordinates i x).1
        (physicalCoarea_f H_R C V
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1) t
        (physicalCoarea_q H_R C V
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1)) *
      ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
        ((eigenpairIncidenceCoordinates i x).2.2.1 -
          physicalCoareaFv H_R C V
            (eigenpairIncidenceCoordinates i x).1
            (eigenpairIncidenceCoordinates i x).2.1) / (2 * t))) *
      ENNReal.ofReal ((star (canonicalProjectiveUnitVector
          (eigenpairIncidenceCoordinates i x).2.1) ⬝ᵥ
        (physicalCoareaD H_R C
            (eigenpairIncidenceCoordinates i x).1 *ᵥ
          canonicalProjectiveUnitVector
            (eigenpairIncidenceCoordinates i x).2.1)).re) *
      ENNReal.ofReal (canonicalProjectiveAffineDensity
        (eigenpairIncidenceCoordinates i x).2.1 *
        Complex.normSq (eigenpairGapMatrix
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.2.1).det *
        coherentEigenpairProjectiveJacobianDefect i
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1
          (eigenpairIncidenceCoordinates i x).2.2 hgap) := by
  rw [physicalSchurCoareaDensity_eq]
  rw [physicalEigenpairCoareaDensity_eq_explicit α R i t
    (physicalCoarea_f H_R C V
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.1)
    (physicalCoarea_q H_R C V
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.1)
    (physicalCoareaFv H_R C V
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.1)
    (physicalCoareaT H_R C (eigenpairIncidenceCoordinates i x).1)
    x hrank hgap]
  rw [physicalEigenpairCrossingQuadratic_physicalCoareaT]

end CoareaNative.BlockBand
