module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorOperatorCorollary
public import Mathlib.Probability.Independence.Basic

/-!
# Canonical GUE and an independent uniform complex direction

The APSSS Frobenius-to-operator argument does not require choosing an eigenvector of the
GUE matrix, nor any Haar-eigenvector theorem.  Its auxiliary direction is sampled
independently from `uniformSphere`.  This module records that product coupling
and integrates the already proved fixed-direction inverse tail over its spherical
coordinate.  Multiplicities play no role at this conditioning layer.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

open scoped Matrix.Norms.L2Operator in
/-- On the operator-inverse tail event, the independent spherical direction has
probability at least one half of witnessing the fixed-vector threshold with the exact
APSSS factor `10`.  This is deterministic in the matrix sample. -/
theorem operatorInverseEvent_sphericalFiber
    {N : ℕ} (hN : 0 < N) (A V : HermitianMatrix (Fin N))
    {t : ℝ} (ht : 0 ≤ t)
    (hV : t * N ≤ ‖(A.1 + V.1)⁻¹‖) :
    1 ≤ 2 * uniformSphere N
      {φ | t * Real.sqrt N / 10 ≤
        ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ WithLp.ofLp φ) :
          EuclideanSpace ℂ (Fin N))‖} := by
  let Q := (A.1 + V.1)⁻¹
  have hsqrt : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsqrtSq : Real.sqrt (N : ℝ) * Real.sqrt N = N := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  have hthreshold : t * Real.sqrt N / 10 ≤ ‖Q‖ / (10 * Real.sqrt N) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 10)
      (mul_pos (by norm_num) hsqrt)]
    dsimp [Q] at hV ⊢
    nlinarith [hV]
  have hbase := one_le_two_mul_uniformSphere_large hN Q
  refine hbase.trans ?_
  gcongr

/-- The product-coupled canonical GUE and independent uniform direction satisfy the
same fixed-vector inverse tail.  The constant is chosen before the dimension,
deformation and threshold.  This is the conditional-law statement needed before
applying `one_le_two_mul_uniformSphere_large` pointwise in the matrix sample. -/
theorem canonicalGUE_uniformSphere_joint_inverse_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ) (_hN : 0 < N), ∀ (A : HermitianMatrix (Fin N))
      (t : ℝ), 1 ≤ t →
      ((canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
          (canonicalGUEVariance_nonneg N)).prod (uniformSphere N))
        {p | t * Real.sqrt N ≤
          ‖(WithLp.toLp 2 ((A.1 + p.1.1)⁻¹ *ᵥ WithLp.ofLp p.2) :
            EuclideanSpace ℂ (Fin N))‖} ≤ ENNReal.ofReal (C / t) := by
  obtain ⟨C, hC, htail⟩ := uniformSphere_ae_canonicalGUE_inverse_tail
  refine ⟨C, hC, ?_⟩
  intro N hN A t ht
  let μ := canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
    (canonicalGUEVariance_nonneg N)
  let ν := uniformSphere N
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ, canonicalHermitianGUEPushforward]
    infer_instance
  let E : Set (HermitianMatrix (Fin N) × EuclideanSpace ℂ (Fin N)) :=
    {p | t * Real.sqrt N ≤
      ‖(WithLp.toLp 2 ((A.1 + p.1.1)⁻¹ *ᵥ WithLp.ofLp p.2) :
        EuclideanSpace ℂ (Fin N))‖}
  have hE : MeasurableSet E := by
    unfold E
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
  change μ.prod ν E ≤ ENNReal.ofReal (C / t)
  rw [Measure.prod_apply_symm hE]
  calc
    (∫⁻ φ, μ ((fun V => (V, φ)) ⁻¹' E) ∂ν) ≤
        ∫⁻ _φ, ENNReal.ofReal (C / t) ∂ν := by
      apply lintegral_mono_ae
      have h := htail N hN A t ht
      filter_upwards [h] with φ hφ
      simpa only [μ, ν, E, Set.preimage_ofPred_eq] using hφ
    _ = ENNReal.ofReal (C / t) := by simp

end PSSSNative.BlockBand.PSSS
