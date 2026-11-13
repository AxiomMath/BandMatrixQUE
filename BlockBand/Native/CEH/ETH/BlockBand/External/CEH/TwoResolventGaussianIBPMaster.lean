module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPLoop

/-!
# The normalized GUE two-resolvent master loop equation

Gaussian integration by parts in every coordinate, after left multiplication by the coordinate
direction, and the covariance contraction of the normalized GUE law give the master loop
equation for the two-resolvent word, with exactly two normalized trace terms.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ComplexOrder

/-- The matrix-valued finite sum is the entrywise covariance contraction. -/
theorem normalizedGUECovarianceContraction_eq_sum_smul
    (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate N)),
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℂ) •
        (gueCoordinateDirection N k * X * gueCoordinateDirection N k)) =
      normalizedGUECovarianceContraction N X := by
  apply Matrix.ext
  intro p q
  let ev : Matrix (Fin N) (Fin N) ℂ →+ ℂ :=
    { toFun := fun M => M p q
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ k : Fin (Fintype.card (HermitianCoordinate N)),
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℂ) •
        (gueCoordinateDirection N k * X * gueCoordinateDirection N k)) = _
  rw [map_sum]
  unfold normalizedGUECovarianceContraction ev
  rfl

/-- Evaluate a finite weighted sum of left matrix products entrywise. -/
theorem sum_smul_mul_apply
    {N : ℕ} {κ : Type*} [Fintype κ]
    (w : κ → ℂ) (D X : κ → Matrix (Fin N) (Fin N) ℂ)
    (p q : Fin N) :
    (∑ k, w k • (D k * X k)) p q =
      ∑ k, ∑ a : Fin N, w k * D k p a * X k a q := by
  let ev : Matrix (Fin N) (Fin N) ℂ →+ ℂ :=
    { toFun := fun M => M p q
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ k, w k • (D k * X k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [ev]
  change w k * (D k * X k) p q = _
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Pull a fixed right matrix factor through a finite weighted sum,
including the sign produced by differentiating an inverse. -/
theorem sum_smul_neg_mul_right
    {N : ℕ} {κ : Type*} [Fintype κ]
    (w : κ → ℂ) (C : κ → Matrix (Fin N) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    (∑ k, w k • (-(C k * B))) =
      -((∑ k, w k • C k) * B) := by
  simp_rw [smul_neg, ← smul_mul_assoc]
  change Finset.univ.sum (fun k => -(w k • C k * B)) = _
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- The pointwise noncommutative algebra behind the two-resolvent loop equation.
After left multiplication by the coordinate direction, the two product-rule
terms are exactly the two normalized GUE covariance contractions, with the
order of every resolvent factor retained. -/
theorem normalizedGUE_leftDerivativeContraction
    {N : ℕ} (hN : 0 < N)
    (G₁ G₂ A : Matrix (Fin N) (Fin N) ℂ) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate N)),
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℂ) •
        (gueCoordinateDirection N k *
          ((-(G₁ * gueCoordinateDirection N k * G₁)) * A * G₂ +
            G₁ * A * (-(G₂ * gueCoordinateDirection N k * G₂))))) =
      -(((((N : ℂ)⁻¹ * G₁.trace) •
            (1 : Matrix (Fin N) (Fin N) ℂ)) * G₁ * A * G₂) +
        ((((N : ℂ)⁻¹ * (G₁ * A * G₂).trace) •
            (1 : Matrix (Fin N) (Fin N) ℂ)) * G₂)) := by
  rw [← normalizedGUECovarianceContraction_eq hN G₁]
  rw [← normalizedGUECovarianceContraction_eq hN (G₁ * A * G₂)]
  rw [← normalizedGUECovarianceContraction_eq_sum_smul,
    ← normalizedGUECovarianceContraction_eq_sum_smul]
  have hfirst (k : Fin (Fintype.card (HermitianCoordinate N))) :
      gueCoordinateDirection N k *
          ((-(G₁ * gueCoordinateDirection N k * G₁)) * A * G₂) =
        -((gueCoordinateDirection N k * G₁ *
            gueCoordinateDirection N k) * (G₁ * A * G₂)) := by
    noncomm_ring
  have hsecond (k : Fin (Fintype.card (HermitianCoordinate N))) :
      gueCoordinateDirection N k *
          (G₁ * A * (-(G₂ * gueCoordinateDirection N k * G₂))) =
        -((gueCoordinateDirection N k * (G₁ * A * G₂) *
            gueCoordinateDirection N k) * G₂) := by
    noncomm_ring
  simp_rw [Matrix.mul_add, hfirst, hsecond, smul_add,
    Finset.sum_add_distrib]
  rw [sum_smul_neg_mul_right, sum_smul_neg_mul_right]
  noncomm_ring

/-- Coordinate IBP after left multiplication by the corresponding Hermitian
direction.  This is the entrywise-to-matrix bridge used by the master loop. -/
theorem normalizedGUEFullTwoResolvent_leftWeightedCoordinate_IBP
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℂ) *
      ∫ y : HermitianCoordinateSpace N,
        ∑ a : Fin N, gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ k a q y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity) := by
  let μ := hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)
  have hleft (a : Fin N) : Integrable (fun y : HermitianCoordinateSpace N =>
      (y k : ℂ) * gueCoordinateDirection N k p a *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y) μ := by
    convert (integrable_coordinate_mul_fullGUEPlainTwoResolventEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k a q).mul_const
        (gueCoordinateDirection N k p a) using 1
    funext y
    ring
  have hright (a : Fin N) : Integrable (fun y : HermitianCoordinateSpace N =>
      gueCoordinateDirection N k p a *
        fullGUEPlainTwoResolventDerivativeEntry
          H₁ H₂ A z₁ z₂ k a q y) μ :=
    (integrable_fullGUEPlainTwoResolventDerivativeEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k a q).const_mul _
  rw [integral_finsetSum Finset.univ (fun a ha => hleft a)]
  rw [integral_finsetSum Finset.univ (fun a ha => hright a)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∫ y, (y k : ℂ) * gueCoordinateDirection N k p a *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y ∂μ) =
      gueCoordinateDirection N k p a *
        ∫ y, (y k : ℂ) *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        ring
    _ = gueCoordinateDirection N k p a *
        ((hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          ∫ y, fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ k a q y ∂μ) := by
        rw [normalizedGUEFullTwoResolvent_coordinate_IBP_arbitrary
          hN H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k a q]
    _ = (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
        ∫ y, gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ k a q y ∂μ := by
        rw [integral_const_mul]
        ring

/-- **Source-shaped normalized GUE two-resolvent loop equation.** The random coordinate field
left-multiplies the two-resolvent word. Gaussian integration by parts and the complete
diagonal/paired-real/paired-imaginary covariance contraction give exactly the two trace terms. -/
theorem normalizedGUEFullTwoResolvent_masterLoop
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      -∫ y : HermitianCoordinateSpace N,
        (((((N : ℂ)⁻¹ * (fullGUEResolvent H₁ z₁ y).trace) •
              (1 : Matrix (Fin N) (Fin N) ℂ)) *
            fullGUEResolvent H₁ z₁ y * A * fullGUEResolvent H₂ z₂ y) +
          ((((N : ℂ)⁻¹ *
              (fullGUEResolvent H₁ z₁ y * A *
                fullGUEResolvent H₂ z₂ y).trace) •
              (1 : Matrix (Fin N) (Fin N) ℂ)) *
            fullGUEResolvent H₂ z₂ y)) p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity) := by
  let μ := hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)
  have hleft (k : Fin (Fintype.card (HermitianCoordinate N))) :
      Integrable (fun y : HermitianCoordinateSpace N =>
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y) μ := by
    apply integrable_finsetSum Finset.univ
    intro a ha
    convert (integrable_coordinate_mul_fullGUEPlainTwoResolventEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k a q).mul_const
        (gueCoordinateDirection N k p a) using 1
    funext y
    ring
  have hright (k : Fin (Fintype.card (HermitianCoordinate N))) :
      Integrable (fun y : HermitianCoordinateSpace N =>
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          ∑ a : Fin N, gueCoordinateDirection N k p a *
            fullGUEPlainTwoResolventDerivativeEntry
              H₁ H₂ A z₁ z₂ k a q y) μ := by
    apply Integrable.const_mul
    apply integrable_finsetSum Finset.univ
    intro a ha
    exact (integrable_fullGUEPlainTwoResolventDerivativeEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k a q).const_mul _
  calc
    (∫ y, ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y ∂μ) =
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∫ y, ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y ∂μ := by
        rw [integral_finsetSum Finset.univ (fun k hk => hleft k)]
    _ = ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          ∫ y, ∑ a : Fin N, gueCoordinateDirection N k p a *
            fullGUEPlainTwoResolventDerivativeEntry
              H₁ H₂ A z₁ z₂ k a q y ∂μ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact normalizedGUEFullTwoResolvent_leftWeightedCoordinate_IBP
          hN H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k p q
    _ = ∫ y, ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          ∑ a : Fin N, gueCoordinateDirection N k p a *
            fullGUEPlainTwoResolventDerivativeEntry
              H₁ H₂ A z₁ z₂ k a q y ∂μ := by
        rw [integral_finsetSum Finset.univ (fun k hk => hright k)]
        simp_rw [integral_const_mul]
    _ = -∫ y,
        (((((N : ℂ)⁻¹ * (fullGUEResolvent H₁ z₁ y).trace) •
              (1 : Matrix (Fin N) (Fin N) ℂ)) *
            fullGUEResolvent H₁ z₁ y * A * fullGUEResolvent H₂ z₂ y) +
          ((((N : ℂ)⁻¹ *
              (fullGUEResolvent H₁ z₁ y * A *
                fullGUEResolvent H₂ z₂ y).trace) •
              (1 : Matrix (Fin N) (Fin N) ℂ)) *
            fullGUEResolvent H₂ z₂ y)) p q ∂μ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with y
        have halg := congrFun (congrFun
          (normalizedGUE_leftDerivativeContraction hN
            (fullGUEResolvent H₁ z₁ y)
            (fullGUEResolvent H₂ z₂ y) A) p) q
        rw [sum_smul_mul_apply] at halg
        change _ = -_
        convert halg using 1
        · apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          unfold fullGUEPlainTwoResolventDerivativeEntry
          ring
        · rfl

/-- Scalar-coefficient form of the master loop, exposing exactly the two
quantities used in the two-resolvent bootstrap: the normalized trace of the
first resolvent and the normalized trace of the two-resolvent word. -/
theorem normalizedGUEFullTwoResolvent_masterLoop_scalar
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      -∫ y : HermitianCoordinateSpace N,
        ((N : ℂ)⁻¹ * (fullGUEResolvent H₁ z₁ y).trace) *
            (fullGUEResolvent H₁ z₁ y * A *
              fullGUEResolvent H₂ z₂ y) p q +
          ((N : ℂ)⁻¹ *
            (fullGUEResolvent H₁ z₁ y * A *
              fullGUEResolvent H₂ z₂ y).trace) *
            fullGUEResolvent H₂ z₂ y p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity) := by
  rw [normalizedGUEFullTwoResolvent_masterLoop
    hN H₁ H₂ A hH₁ hH₂ hz₁ hz₂ p q]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

/-- Pointwise remainder split used before applying Hölder/Cauchy–Schwarz in the two-resolvent
bootstrap. The two summands are precisely the normalized one-resolvent trace contribution and the
normalized two-resolvent-trace contribution. -/
theorem norm_normalizedGUE_masterIntegrand_le
    {N : ℕ} (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (y : HermitianCoordinateSpace N) (p q : Fin N) :
    ‖((N : ℂ)⁻¹ * (fullGUEResolvent H₁ z₁ y).trace) *
          (fullGUEResolvent H₁ z₁ y * A *
            fullGUEResolvent H₂ z₂ y) p q +
        ((N : ℂ)⁻¹ *
          (fullGUEResolvent H₁ z₁ y * A *
            fullGUEResolvent H₂ z₂ y).trace) *
          fullGUEResolvent H₂ z₂ y p q‖ ≤
      ‖(N : ℂ)⁻¹ * (fullGUEResolvent H₁ z₁ y).trace‖ *
        ‖(fullGUEResolvent H₁ z₁ y * A *
          fullGUEResolvent H₂ z₂ y) p q‖ +
      ‖(N : ℂ)⁻¹ *
        (fullGUEResolvent H₁ z₁ y * A *
          fullGUEResolvent H₂ z₂ y).trace‖ *
        ‖fullGUEResolvent H₂ z₂ y p q‖ := by
  refine (norm_add_le _ _).trans_eq ?_
  simp only [norm_mul]

end CEHNative.BlockBand.External.CEH
