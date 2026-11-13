module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEUniformSphereConditioning
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEBlockPoissonRepresentation
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.PublicGUE

/-!
# Canonical GUE operator-inverse tail

This module completes the APSSS Frobenius-to-operator assembly for the repository's
canonical normalized GUE pushforward.  It uses an independent uniform complex direction,
the exact factor-ten spherical amplification, and the fixed-vector inverse tail.  No
eigenvector law or Haar-selection certificate is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

open scoped Matrix.Norms.L2Operator in
/-- **Canonical operator-inverse tail.**  There is one absolute constant, chosen before
the positive dimension, deterministic Hermitian deformation and threshold, such that the
canonical `GUE_N(1/N)` inverse has `L²` operator-norm tail `C/t` at scale `tN`.

The public `BlockBand.GUE` alias is deliberately not mentioned: this theorem concerns the
already constructed and identified canonical Hermitian pushforward law. -/
theorem canonicalGUE_operator_inverse_tail :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (N : ℕ) (_hN : 0 < N), ∀ (A : HermitianMatrix (Fin N))
      (t : ℝ), 1 ≤ t →
      canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
        (canonicalGUEVariance_nonneg N)
        {V | t * N ≤ ‖(A.1 + V.1)⁻¹‖} ≤ ENNReal.ofReal (K / t) := by
  obtain ⟨C, hC, hjoint⟩ := canonicalGUE_uniformSphere_joint_inverse_tail
  refine ⟨20 * C, by nlinarith, ?_⟩
  intro N hN A t ht
  let μ := canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
    (canonicalGUEVariance_nonneg N)
  let ν := uniformSphere N
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ, canonicalHermitianGUEPushforward]
    infer_instance
  let E : Set (HermitianMatrix (Fin N)) := {V | t * N ≤ ‖(A.1 + V.1)⁻¹‖}
  have hE : MeasurableSet E := by
    unfold E
    apply measurableSet_le measurable_const
    have hinv : Measurable fun V : HermitianMatrix (Fin N) => (A.1 + V.1)⁻¹ :=
      PSSSNative.BlockBand.Measurable.matrixNonsingInv
        ((continuous_const.add continuous_subtype_val).measurable)
    fun_prop
  change μ E ≤ ENNReal.ofReal (20 * C / t)
  by_cases hlarge : 10 ≤ t
  · let s : ℝ := t / 10
    let T : Set (HermitianMatrix (Fin N) × EuclideanSpace ℂ (Fin N)) :=
        {p | s * Real.sqrt N ≤
          ‖(WithLp.toLp 2 ((A.1 + p.1.1)⁻¹ *ᵥ WithLp.ofLp p.2) :
            EuclideanSpace ℂ (Fin N))‖}
    have hs : 1 ≤ s := by dsimp [s]; linarith
    have hT : MeasurableSet T := by
      unfold T
      apply measurableSet_le measurable_const
      have hinv : Measurable fun p : HermitianMatrix (Fin N) ×
          EuclideanSpace ℂ (Fin N) => (A.1 + p.1.1)⁻¹ :=
        PSSSNative.BlockBand.Measurable.matrixNonsingInv
          ((continuous_const.add continuous_fst.subtype_val).measurable)
      have hmul : Measurable fun p : HermitianMatrix (Fin N) ×
          EuclideanSpace ℂ (Fin N) =>
          (A.1 + p.1.1)⁻¹ *ᵥ WithLp.ofLp p.2 := by
        rw [measurable_pi_iff]
        intro i
        unfold Matrix.mulVec dotProduct
        fun_prop
      fun_prop
    have hfiber : ∀ V ∈ E,
        1 ≤ 2 * ν ((fun φ => (V, φ)) ⁻¹' T) := by
      intro V hV
      have hamp := operatorInverseEvent_sphericalFiber hN A V
        (t := t) (by linarith) hV
      simpa only [ν, T, s, Set.preimage_ofPred_eq, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc] using hamp
    have hmeasFiber : Measurable fun V => ν ((fun φ => (V, φ)) ⁻¹' T) :=
      measurable_measure_prodMk_left_finite hT
    have hprod := hjoint N hN A s hs
    change μ.prod ν T ≤ ENNReal.ofReal (C / s) at hprod
    calc
      μ E ≤ ∫⁻ V, 2 * ν ((fun φ => (V, φ)) ⁻¹' T) ∂μ := by
        apply meas_le_lintegral₀ (hmeasFiber.const_mul 2).aemeasurable
        exact hfiber
      _ = 2 * μ.prod ν T := by
        rw [Measure.prod_apply hT, lintegral_const_mul _ hmeasFiber]
      _ ≤ 2 * ENNReal.ofReal (C / s) := by gcongr
      _ = ENNReal.ofReal (20 * C / t) := by
        rw [← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        dsimp [s]
        field_simp
        ring
  · have hμ : μ E ≤ 1 := prob_le_one
    refine hμ.trans ?_
    rw [ENNReal.one_le_ofReal]
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    apply (le_div_iff₀ htpos).2
    nlinarith

open scoped Matrix.Norms.L2Operator in

/-- **Public operator-inverse tail (APSSS (1.7)).**  The public `GUE` law at
variance `1/N` is definitionally identified by the nonnegative-variance
adapter with the canonical pushforward used above.  A real energy is absorbed into
the deterministic Hermitian deformation. -/
theorem opNorm_inv_tail :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (N : ℕ), 0 < N → ∀ (A : HermitianMatrix (Fin N))
      (x : ℝ) (t : ℝ), 1 ≤ t →
      (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))
        {V | t * N ≤
          ‖(A.1 + V.1 - (x : ℂ) •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖} ≤
        ENNReal.ofReal (K / t) := by
  obtain ⟨K, hK, htail⟩ := canonicalGUE_operator_inverse_tail
  refine ⟨K, hK, ?_⟩
  intro N hN A x t ht
  have hvar : 0 ≤ (1 / (N : ℝ)) := by positivity
  rw [PSSSNative.BlockBand.GUE_toMeasure_eq_canonicalHermitianGUEPushforward
    N (1 / (N : ℝ)) hvar]
  have h := htail N hN (energyShiftHermitian A x) t ht
  have hset :
      {V : HermitianMatrix (Fin N) | t * N ≤
        ‖(A.1 + V.1 - (x : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖} =
      {V : HermitianMatrix (Fin N) | t * N ≤
        ‖((energyShiftHermitian A x).1 + V.1)⁻¹‖} := by
    ext V
    simp only [Set.mem_ofPred_eq]
    rw [show A.1 + V.1 - (x : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ) =
        (energyShiftHermitian A x).1 + V.1 by
      ext i j
      simp [energyShiftHermitian]
      ring]
  rw [hset]
  simpa only [canonicalGUEVariance] using h

end PSSSNative.BlockBand.PSSS
