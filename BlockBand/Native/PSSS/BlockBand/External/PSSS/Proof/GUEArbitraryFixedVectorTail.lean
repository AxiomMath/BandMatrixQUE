module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalFixedVectorTail

/-!
# Canonical GUE inverse tails for arbitrary unit vectors

This module transports the canonical-coordinate fixed-vector inverse tail through an
explicit unitary completion of an arbitrary deterministic unit vector.  The source is
the APSSS/PSSS fixed-vector estimate, in the canonical `GUE_N(1/N)` normalization.
The constant is uniform in the dimension, deterministic Hermitian deformation, unit
vector and threshold.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- A unitary matrix preserves the Euclidean norm of coordinate vectors. -/
theorem norm_conjTranspose_mulVec_of_unitary {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) (x : Fin N → ℂ) :
    ‖(WithLp.toLp 2 (Uᴴ *ᵥ x) : EuclideanSpace ℂ (Fin N))‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin N))‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  calc
    ‖(WithLp.toLp 2 (Uᴴ *ᵥ x) : EuclideanSpace ℂ (Fin N))‖ ^ 2 =
        RCLike.re (inner ℂ
          (WithLp.toLp 2 (Uᴴ *ᵥ x) : EuclideanSpace ℂ (Fin N))
          (WithLp.toLp 2 (Uᴴ *ᵥ x) : EuclideanSpace ℂ (Fin N))) :=
      (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (inner ℂ
          (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin N))
          (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin N))) := by
      congr 1
      rw [PiLp.inner_apply, PiLp.inner_apply]
      simp only [RCLike.inner_apply]
      change (Uᴴ *ᵥ x) ⬝ᵥ star (Uᴴ *ᵥ x) = x ⬝ᵥ star x
      calc
        (Uᴴ *ᵥ x) ⬝ᵥ star (Uᴴ *ᵥ x) =
            star (Uᴴ *ᵥ x) ⬝ᵥ (Uᴴ *ᵥ x) := dotProduct_comm _ _
        _ = star x ⬝ᵥ x := by
          rw [star_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul,
            conjTranspose_conjTranspose, mul_eq_one_comm.mp hU, Matrix.vecMul_one]
        _ = x ⬝ᵥ star x := dotProduct_comm _ _
    _ = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin N))‖ ^ 2 :=
      inner_self_eq_norm_sq _

/-- Unitary conjugation distributes over addition of Hermitian matrices. -/
theorem conjugateHermitian_add_apply {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ)
    (A V : HermitianMatrix (Fin N)) :
    Uᴴ * (A.1 + V.1) * U =
      (conjugateHermitian U A).1 + (conjugateHermitian U V).1 := by
  simp only [conjugateHermitian, Matrix.mul_add, Matrix.add_mul]

/-- Exact inverse-vector transport under a unitary whose zeroth column is `φ`. -/
theorem conjugateHermitian_add_inv_mulVec_firstCoordinate {N : ℕ} (hN : 0 < N)
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (φ : Fin N → ℂ)
    (hUφ : U *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩ = φ)
    (A V : HermitianMatrix (Fin N)) :
    ((conjugateHermitian U A).1 + (conjugateHermitian U V).1)⁻¹ *ᵥ
        phaseFixedCoordinateVector ⟨0, hN⟩ =
      Uᴴ *ᵥ ((A.1 + V.1)⁻¹ *ᵥ φ) := by
  rw [← conjugateHermitian_add_apply U A V]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.inv_eq_left_inv hU, Matrix.inv_eq_right_inv hU]
  rw [← Matrix.mul_assoc]
  calc
    ((Uᴴ * (A.1 + V.1)⁻¹) * U) *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩ =
        (Uᴴ * (A.1 + V.1)⁻¹) *ᵥ
          (U *ᵥ phaseFixedCoordinateVector ⟨0, hN⟩) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = (Uᴴ * (A.1 + V.1)⁻¹) *ᵥ φ := by rw [hUφ]
    _ = Uᴴ *ᵥ ((A.1 + V.1)⁻¹ *ᵥ φ) :=
      (Matrix.mulVec_mulVec _ _ _).symm

/-- The arbitrary-vector inverse event is Borel measurable. -/
theorem measurableSet_arbitraryVector_inverse_event {N : ℕ}
    (A : HermitianMatrix (Fin N)) (φ : Fin N → ℂ) (s : ℝ) :
    MeasurableSet {V : HermitianMatrix (Fin N) |
      s ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ φ) :
        EuclideanSpace ℂ (Fin N))‖} := by
  have hm : Measurable fun V : HermitianMatrix (Fin N) =>
      (A.1 + V.1)⁻¹ :=
    PSSSNative.BlockBand.Measurable.matrixNonsingInv
      ((continuous_const.add continuous_subtype_val).measurable)
  have hv : Measurable fun V : HermitianMatrix (Fin N) =>
      (A.1 + V.1)⁻¹ *ᵥ φ := by
    rw [measurable_pi_iff]
    intro i
    unfold Matrix.mulVec dotProduct
    fun_prop
  apply measurableSet_le measurable_const
  fun_prop

/-- **Arbitrary-unit-vector canonical GUE inverse tail.**  Source: APSSS/PSSS
fixed-vector estimate.  In canonical `GUE_N(1/N)` normalization there is one
absolute constant, chosen before `N`, the Hermitian deformation `A`, the unit
vector `φ`, and `t`, such that the inverse-vector event has probability at most
`C/t`. -/
theorem canonicalGUE_arbitraryUnitVector_inverse_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ) (_hN : 0 < N), ∀ (A : HermitianMatrix (Fin N))
      (φ : Fin N → ℂ), ‖complexEuclideanVector φ‖ = 1 →
      ∀ (t : ℝ), 1 ≤ t →
      canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
        (canonicalGUEVariance_nonneg N)
        {V | t * Real.sqrt N ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ φ) :
            EuclideanSpace ℂ (Fin N))‖} ≤ ENNReal.ofReal (C / t) := by
  obtain ⟨C, hC, htail⟩ := canonicalGUE_fixedVector_inverse_tail
  refine ⟨C, hC, ?_⟩
  intro N hN A φ hφ t ht
  obtain ⟨U, hU, hUφ, hmap, _⟩ :=
    exists_arbitraryUnitVector_GUE_disintegration hN φ hφ
      (canonicalGUEVariance N) (canonicalGUEVariance_nonneg N)
  let P := canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
    (canonicalGUEVariance_nonneg N)
  let A' := conjugateHermitian U A
  let E := {V : HermitianMatrix (Fin N) | t * Real.sqrt N ≤
    ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ φ) : EuclideanSpace ℂ (Fin N))‖}
  let E' := {V : HermitianMatrix (Fin N) | t * Real.sqrt N ≤
    ‖(WithLp.toLp 2 ((A'.1 + V.1)⁻¹ *ᵥ
      phaseFixedCoordinateVector ⟨0, hN⟩) : EuclideanSpace ℂ (Fin N))‖}
  have hpre : (conjugateHermitian U) ⁻¹' E' = E := by
    ext V
    change (t * Real.sqrt N ≤ ‖(WithLp.toLp 2
      (((conjugateHermitian U A).1 + (conjugateHermitian U V).1)⁻¹ *ᵥ
        phaseFixedCoordinateVector ⟨0, hN⟩) : EuclideanSpace ℂ (Fin N))‖) ↔
      (t * Real.sqrt N ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ φ) :
        EuclideanSpace ℂ (Fin N))‖)
    rw [conjugateHermitian_add_inv_mulVec_firstCoordinate hN U hU φ hUφ A V,
      norm_conjTranspose_mulVec_of_unitary U hU]
  have hE' : MeasurableSet E' :=
    measurableSet_arbitraryVector_inverse_event A'
      (phaseFixedCoordinateVector ⟨0, hN⟩) (t * Real.sqrt N)
  have hmeasure : P E = P E' := by
    rw [← hpre, ← Measure.map_apply (measurable_conjugateHermitian U) hE']
    exact congrArg (fun μ : Measure (HermitianMatrix (Fin N)) => μ E') hmap
  rw [hmeasure]
  exact htail N hN A' t ht

end PSSSNative.BlockBand.PSSS
