module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.OneResolventTraceConcentration
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPMaster
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPScaled

/-!
# One-resolvent Gaussian master equation

This module derives the finite-dimensional one-resolvent loop equation directly
from the concrete normalized GUE coordinate product.  It is an exact Gaussian
integration-by-parts identity, before MDE stability, spectral-domain
uniformity, or any limiting argument.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

/-- Full-product scalar Gaussian IBP for one resolvent entry in an arbitrary
normalized GUE coordinate.  All conditioning and integrability premises are
discharged by the concrete product law and nonreal resolvent bound. -/
theorem normalizedGUEFullResolvent_coordinate_IBP_arbitrary
    {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) :
    (∫ y : HermitianCoordinateSpace N, (y k : ℂ) *
        fullGUECoordinateResolventEntry H z i j y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℝ) *
        ∫ y : HermitianCoordinateSpace N,
          fullGUECoordinateDerivativeEntry H z k i j y
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity) := by
  let c := Fintype.card (HermitianCoordinate N)
  have hc : 1 ≤ c := by
    exact (Nat.one_le_iff_ne_zero).2 (by
      intro h
      have : IsEmpty (Fin c) := Fin.isEmpty_iff.mpr h
      exact this.false k)
  have hcEq : c - 1 + 1 = c := Nat.sub_add_cancel hc
  let e : Fin (c - 1 + 1) ≃ Fin c := Equiv.cast (congrArg Fin hcEq)
  let k₀ : Fin (c - 1 + 1) := e.symm k
  let μ := hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)
  let ν :=
    (gaussianReal 0
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) (e k₀))).prod
      (Measure.pi fun l : Fin (c - 1) =>
        gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) (e (k₀.succAbove l))))
  let S := normalizedGUESplitMap e k₀
  have hek : e k₀ = k := by simp [k₀]
  have hmp : MeasurePreserving S μ ν :=
    measurePreserving_normalizedGUESplitMap hN e k₀
  have hleftFull : Integrable (fun y : HermitianCoordinateSpace N =>
      (y (e k₀) : ℂ) * fullGUECoordinateResolventEntry H z i j y) μ :=
    integrable_coordinate_mul_fullGUEResolventEntry H hH hz (e k₀) i j
  have hrightFull : Integrable
      (fullGUECoordinateDerivativeEntry H z (e k₀) i j) μ :=
    integrable_fullGUECoordinateDerivativeEntry H hH hz (e k₀) i j
  have hleftSplit : Integrable (fun p : ℝ × (Fin (c - 1) → ℝ) =>
      (((S.symm p) (e k₀) : ℝ) : ℂ) *
        fullGUECoordinateResolventEntry H z i j (S.symm p)) ν := by
    change Integrable ((fun y : HermitianCoordinateSpace N =>
      (y (e k₀) : ℂ) * fullGUECoordinateResolventEntry H z i j y) ∘ S.symm) ν
    exact hmp.symm.integrable_comp_of_integrable hleftFull
  have hrightSplit : Integrable (fun p : ℝ × (Fin (c - 1) → ℝ) =>
      fullGUECoordinateDerivativeEntry H z (e k₀) i j (S.symm p)) ν := by
    change Integrable
      (fullGUECoordinateDerivativeEntry H z (e k₀) i j ∘ S.symm) ν
    exact hmp.symm.integrable_comp_of_integrable hrightFull
  rw [← hek]
  rw [integral_normalizedGUE_eq_split hN e k₀]
  rw [integral_normalizedGUE_eq_split hN e k₀]
  change (∫ p : ℝ × (Fin (c - 1) → ℝ),
      (((S.symm p) (e k₀) : ℝ) : ℂ) *
        fullGUECoordinateResolventEntry H z i j (S.symm p) ∂ν) =
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
      (by positivity) (e k₀) : ℝ) *
      ∫ p : ℝ × (Fin (c - 1) → ℝ),
        fullGUECoordinateDerivativeEntry H z (e k₀) i j (S.symm p) ∂ν
  rw [integral_prod_symm _ hleftSplit, integral_prod_symm _ hrightSplit]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with b
  have hcond := normalizedGUEFullResolvent_conditionalCoordinate_IBP
    hN H hH hz (e k₀) i j (S.symm (0, b))
  convert hcond using 1
  · apply integral_congr_ae
    filter_upwards with x
    rw [show S.symm (x, b) =
      Function.update (S.symm (0, b)) (e k₀) x by
        exact normalizedGUESplitMap_symm_eq_update e k₀ x b]
    simp
  · apply congrArg
    apply integral_congr_ae
    filter_upwards with x
    rw [show S.symm (x, b) =
      Function.update (S.symm (0, b)) (e k₀) x by
        exact normalizedGUESplitMap_symm_eq_update e k₀ x b]

/-- Covariance contraction of the derivative of a single inverse pencil. -/
theorem normalizedGUE_leftResolventDerivativeContraction
    {N : ℕ} (hN : 0 < N) (G : Matrix (Fin N) (Fin N) ℂ) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate N)),
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℂ) •
        (gueCoordinateDirection N k *
          (-(G * gueCoordinateDirection N k * G)))) =
      -((NTrace G) • G) := by
  have hk (k : Fin (Fintype.card (HermitianCoordinate N))) :
      gueCoordinateDirection N k *
          (-(G * gueCoordinateDirection N k * G)) =
        -((gueCoordinateDirection N k * G *
          gueCoordinateDirection N k) * G) := by
    noncomm_ring
  simp_rw [hk]
  rw [sum_smul_neg_mul_right]
  rw [normalizedGUECovarianceContraction_eq_sum_smul,
    normalizedGUECovarianceContraction_eq hN]
  simp [NTrace, CEHNative.BlockBand.Conventions.normalizedTrace]

/-- Exact one-resolvent normalized-GUE loop cancellation.  The random source
and normalized-trace feedback have a single common expectation and cancel
entrywise. -/
theorem normalizedGUEFullResolvent_masterCancellation
    {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      ((hermitianGUEBlock N y).1 * fullGUEResolvent H z y) p q
      ∂normalizedGUEMeasure N) +
    (∫ y : HermitianCoordinateSpace N,
      NTrace (fullGUEResolvent H z y) * (fullGUEResolvent H z y) p q
      ∂normalizedGUEMeasure N) = 0 := by
  let μ := normalizedGUEMeasure N
  have hleft (k : Fin (Fintype.card (HermitianCoordinate N))) :
      Integrable (fun y : HermitianCoordinateSpace N =>
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUECoordinateResolventEntry H z a q y) μ := by
    apply integrable_finsetSum Finset.univ
    intro a ha
    convert (integrable_coordinate_mul_fullGUEResolventEntry
      H hH hz k a q).mul_const (gueCoordinateDirection N k p a) using 1
    funext y
    ring
  have hright (k : Fin (Fintype.card (HermitianCoordinate N))) :
      Integrable (fun y : HermitianCoordinateSpace N =>
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          ∑ a : Fin N, gueCoordinateDirection N k p a *
            fullGUECoordinateDerivativeEntry H z k a q y) μ := by
    apply Integrable.const_mul
    apply integrable_finsetSum Finset.univ
    intro a ha
    exact (integrable_fullGUECoordinateDerivativeEntry H hH hz k a q).const_mul _
  rw [show (fun y : HermitianCoordinateSpace N =>
      ((hermitianGUEBlock N y).1 * fullGUEResolvent H z y) p q) =
      (fun y => ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUECoordinateResolventEntry H z a q y) by
    funext y
    exact hermitianGUEBlock_mul_twoResolvent_apply y _ p q]
  rw [integral_finsetSum Finset.univ (fun k hk => hleft k)]
  have hibp (k : Fin (Fintype.card (HermitianCoordinate N))) :
      (∫ y, ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUECoordinateResolventEntry H z a q y ∂μ) =
      ∫ y, (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
        ∑ a : Fin N, gueCoordinateDirection N k p a *
          fullGUECoordinateDerivativeEntry H z k a q y ∂μ := by
    have hleftA (a : Fin N) : Integrable (fun y : HermitianCoordinateSpace N =>
        (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUECoordinateResolventEntry H z a q y) μ := by
      convert (integrable_coordinate_mul_fullGUEResolventEntry
        H hH hz k a q).mul_const (gueCoordinateDirection N k p a) using 1
      funext y
      ring
    rw [integral_finsetSum Finset.univ (fun a ha => hleftA a)]
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ (fun a ha =>
      (integrable_fullGUECoordinateDerivativeEntry H hH hz k a q).const_mul _)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    calc
      (∫ y, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUECoordinateResolventEntry H z a q y ∂μ) =
        gueCoordinateDirection N k p a *
          ∫ y, (y k : ℂ) *
            fullGUECoordinateResolventEntry H z a q y ∂μ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          ring
      _ = gueCoordinateDirection N k p a *
          ((hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k : ℂ) *
            ∫ y, fullGUECoordinateDerivativeEntry H z k a q y ∂μ) := by
          rw [normalizedGUEFullResolvent_coordinate_IBP_arbitrary
            hN H hH hz k a q]
      _ = (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k : ℂ) *
          ∫ y, gueCoordinateDirection N k p a *
            fullGUECoordinateDerivativeEntry H z k a q y ∂μ := by
          rw [integral_const_mul]
          ring
  simp_rw [hibp]
  rw [← integral_finsetSum Finset.univ (fun k hk => hright k)]
  have hderivSum : Integrable (fun y : HermitianCoordinateSpace N =>
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          ∑ a : Fin N, gueCoordinateDirection N k p a *
            fullGUECoordinateDerivativeEntry H z k a q y) μ :=
    integrable_finsetSum Finset.univ (fun k hk => hright k)
  have hfeedback : Integrable (fun y : HermitianCoordinateSpace N =>
      NTrace (fullGUEResolvent H z y) * (fullGUEResolvent H z y) p q) μ := by
    have hi (i : Fin N) : Integrable (fun y : HermitianCoordinateSpace N =>
        (fullGUEResolvent H z y) i i * (fullGUEResolvent H z y) p q) μ :=
      (integrable_fullGUECoordinateResolventEntry H hH hz i i).mul_bdd
        (measurable_fullGUECoordinateResolventEntry H z p q).aestronglyMeasurable
        (ae_of_all _ (norm_fullGUECoordinateResolventEntry_le H hH hz p q))
    have hs := integrable_finsetSum Finset.univ (fun i hi_mem => hi i)
    convert hs.const_mul (((N : ℕ) : ℂ)⁻¹) using 1
    funext y
    unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
      Matrix.trace
    rw [mul_assoc, Finset.sum_mul]
    congr 1
  rw [← integral_add hderivSum hfeedback]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  have halg := congrFun (congrFun
    (normalizedGUE_leftResolventDerivativeContraction hN
      (fullGUEResolvent H z y)) p) q
  rw [sum_smul_mul_apply] at halg
  change _ + _ = 0
  convert congrArg (fun w : ℂ => w +
      NTrace (fullGUEResolvent H z y) * (fullGUEResolvent H z y) p q) halg using 1
  · apply congrArg (fun w : ℂ => w +
      NTrace (fullGUEResolvent H z y) * (fullGUEResolvent H z y) p q)
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    unfold fullGUECoordinateDerivativeEntry
    simp only [Matrix.neg_apply]
    ring
  · simp

/-- Coupling-scaled one-resolvent master cancellation.  Gaussian covariance
produces the exact factor `lambda ^ 2` in the trace feedback. -/
theorem scaledNormalizedGUE_oneResolvent_masterCancellation
    {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      (((lambda : ℂ) • (hermitianGUEBlock N y).1) *
        scaledFullGUEResolvent H lambda z y) p q ∂normalizedGUEMeasure N) +
    (∫ y : HermitianCoordinateSpace N,
      (lambda : ℂ) ^ 2 * NTrace (scaledFullGUEResolvent H lambda z y) *
        (scaledFullGUEResolvent H lambda z y) p q ∂normalizedGUEMeasure N) = 0 := by
  by_cases hlambda : lambda = 0
  · subst lambda
    simp
  · let c : ℂ := (lambda : ℂ)
    let H' : Matrix (Fin N) (Fin N) ℂ := c⁻¹ • H
    let z' : ℂ := c⁻¹ * z
    have hc : c ≠ 0 := by
      simpa [c] using Complex.ofReal_ne_zero.mpr hlambda
    have hH' : H'.IsHermitian := by
      change (c⁻¹ • H).IsHermitian
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH]
      congr 1
      simp [c]
    have hz' : z'.im ≠ 0 := by
      simp [z', c, Complex.mul_im, hlambda, hz]
    have hG (y : HermitianCoordinateSpace N) :
        fullGUEResolvent H' z' y =
          c • scaledFullGUEResolvent H lambda z y := by
      rw [scaledFullGUEResolvent_eq_inv_smul_fullGUEResolvent
        H hH lambda hlambda hz y]
      simp [H', z', c, smul_smul, hc]
    have hmaster := normalizedGUEFullResolvent_masterCancellation
      hN H' hH' hz' p q
    have hleft :
        (∫ y : HermitianCoordinateSpace N,
          (((lambda : ℂ) • (hermitianGUEBlock N y).1) *
            scaledFullGUEResolvent H lambda z y) p q ∂normalizedGUEMeasure N) =
        ∫ y : HermitianCoordinateSpace N,
          ((hermitianGUEBlock N y).1 * fullGUEResolvent H' z' y) p q
          ∂normalizedGUEMeasure N := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hG]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
      rfl
    have hfeedback :
        (∫ y : HermitianCoordinateSpace N,
          (lambda : ℂ) ^ 2 * NTrace (scaledFullGUEResolvent H lambda z y) *
            (scaledFullGUEResolvent H lambda z y) p q ∂normalizedGUEMeasure N) =
        ∫ y : HermitianCoordinateSpace N,
          NTrace (fullGUEResolvent H' z' y) * (fullGUEResolvent H' z' y) p q
          ∂normalizedGUEMeasure N := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hG]
      simp only [NTrace_smul, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hleft, hfeedback]
    exact hmaster

end CEHNative.BlockBand.External.CEH
