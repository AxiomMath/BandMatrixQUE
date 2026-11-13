module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.OneResolventGaussianIBPMaster
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# First one-resolvent expectation-bias checkpoint

The exact Gaussian master equation is centered around the finite-dimensional
mean trace.  Its only stochastic defect is a covariance between the centered
normalized trace and one resolvent entry.  This module bounds that covariance
by the sharp Poincaré second moment.  The result is pointwise in the spectral
parameter and is not an identification with the CEH MDE branch.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ENNReal
open PencilAdapter

namespace ReplicatedGUEEuclidean

/-- Transport of the Euclidean centered second moment back to the concrete
replicated normalized-GUE product law. -/
theorem integral_norm_sq_centeredReplicatedOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ y, ‖centeredReplicatedOneResolventTrace d f lambda z y‖ ^ 2
      ∂replicatedNormalizedGUEMeasure N d) ≤
      (Real.pi ^ 2 / 2) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4 := by
  have hmean :
      (∫ x, oneResolventTrace d f lambda z x ∂measure N d) =
      ∫ y, replicatedOneResolventTrace d f lambda z y
        ∂replicatedNormalizedGUEMeasure N d := by
    rw [measure]
    rw [integral_map_of_stronglyMeasurable (measurable_coordinatesEquiv N d)
      (measurable_oneResolventTrace f lambda hz).stronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with y
    exact oneResolventTrace_coordinatesEquiv f lambda z y
  have htransport (y : ReplicatedGUECoordinateSpace N d) :
      centeredOneResolventTrace d f lambda z (coordinatesEquiv N d y) =
        centeredReplicatedOneResolventTrace d f lambda z y := by
    simp only [centeredOneResolventTrace, centeredReplicatedOneResolventTrace,
      oneResolventTrace_coordinatesEquiv, hmean]
  have hmeas : StronglyMeasurable (fun x : CoordinateEuclideanSpace N d =>
      ‖centeredOneResolventTrace d f lambda z x‖ ^ 2) :=
    ((measurable_centeredOneResolventTrace f lambda hz).norm.pow_const 2).stronglyMeasurable
  have hmoment :=
    integral_norm_sq_centeredOneResolventTrace_le hN hd f lambda hz
  rw [measure] at hmoment
  rw [integral_map_of_stronglyMeasurable
    (measurable_coordinatesEquiv N d) hmeas] at hmoment
  simpa only [htransport] using hmoment

/-- `L¹` control of the centered trace obtained from its `L²` Poincaré bound
on the probability space.  The right side is deliberately left as the exact
real half-power of the proved second-moment constant. -/
theorem integral_norm_centeredReplicatedOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ y, ‖centeredReplicatedOneResolventTrace d f lambda z y‖
      ∂replicatedNormalizedGUEMeasure N d) ≤
      ((Real.pi ^ 2 / 2) * lambda ^ 2 *
        (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)) := by
  let c := fun y : ReplicatedGUECoordinateSpace N d =>
    ‖centeredReplicatedOneResolventTrace d f lambda z y‖
  have hcmeas : AEStronglyMeasurable c (replicatedNormalizedGUEMeasure N d) := by
    have htrace := (integrable_replicatedOneResolventTrace (d := d)
      f lambda hz).aestronglyMeasurable
    exact (htrace.sub aestronglyMeasurable_const).norm
  have hcsq : Integrable (fun y => c y ^ 2)
      (replicatedNormalizedGUEMeasure N d) := by
    apply Integrable.of_bound (hcmeas.pow 2)
      (4 * |z.im|⁻¹ ^ 2)
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := norm_centeredReplicatedOneResolventTrace_le
      hN hd f lambda hz y
    calc
      c y ^ 2 ≤ (2 * |z.im|⁻¹) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (by norm_num) (inv_nonneg.mpr (abs_nonneg _)))).2 h
      _ = 4 * |z.im|⁻¹ ^ 2 := by ring
  have hcLpNat : MemLp c 2 (replicatedNormalizedGUEMeasure N d) :=
    (memLp_two_iff_integrable_sq hcmeas).2 hcsq
  have hcLp : MemLp c (ENNReal.ofReal (2 : ℝ))
      (replicatedNormalizedGUEMeasure N d) := by
    simpa using hcLpNat
  have honeLp :
      MemLp (fun _ : ReplicatedGUECoordinateSpace N d => (1 : ℝ))
        (ENNReal.ofReal (2 : ℝ))
        (replicatedNormalizedGUEMeasure N d) := by
    simpa using
      (memLp_const (μ := replicatedNormalizedGUEMeasure N d) (1 : ℝ))
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (ae_of_all _ fun y => norm_nonneg _)
    (ae_of_all _ fun _ => zero_le_one) hcLp honeLp
  have hholder' :
      (∫ y, c y ∂replicatedNormalizedGUEMeasure N d) ≤
        (∫ y, c y ^ (2 : ℝ) ∂replicatedNormalizedGUEMeasure N d) ^
          (1 / (2 : ℝ)) := by
    simpa using hholder
  calc
    _ ≤ (∫ y, c y ^ (2 : ℝ) ∂replicatedNormalizedGUEMeasure N d) ^
        (1 / (2 : ℝ)) := hholder'
    _ = (∫ y, c y ^ 2 ∂replicatedNormalizedGUEMeasure N d) ^
        (1 / (2 : ℝ)) := by norm_num
    _ ≤ _ := Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
      (integral_norm_sq_centeredReplicatedOneResolventTrace_le
        hN hd f lambda hz) (by positivity)

end ReplicatedGUEEuclidean

/-- The covariance defect in the centered one-resolvent master equation. -/
def replicatedOneResolventCovarianceRemainder {N : ℕ} (d : ℕ)
    (f : Spectrum N) (lambda : ℝ) (z : ℂ) (p q : Fin (N * d)) : ℂ :=
  ∫ y, centeredReplicatedOneResolventTrace d f lambda z y *
    scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
      lambda z y p q ∂replicatedNormalizedGUEMeasure N d

/-- The first quantitative expectation-bias input: every covariance entry in
the exact master equation is `O((N*d)⁻¹)` with its explicit fixed-parameter
constant. -/
theorem norm_replicatedOneResolventCovarianceRemainder_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (p q : Fin (N * d)) :
    ‖replicatedOneResolventCovarianceRemainder d f lambda z p q‖ ≤
      |z.im|⁻¹ *
        ((Real.pi ^ 2 / 2) * lambda ^ 2 *
          (((N * d : ℕ) : ℝ)⁻¹) ^ 2 * |z.im|⁻¹ ^ 4) ^ (1 / (2 : ℝ)) := by
  unfold replicatedOneResolventCovarianceRemainder
  have hcint : Integrable (centeredReplicatedOneResolventTrace d f lambda z)
      (replicatedNormalizedGUEMeasure N d) :=
    (integrable_replicatedOneResolventTrace (d := d) f lambda hz).sub
      (integrable_const _)
  have hg : Integrable (fun y : ReplicatedGUECoordinateSpace N d =>
      |z.im|⁻¹ * ‖centeredReplicatedOneResolventTrace d f lambda z y‖)
      (replicatedNormalizedGUEMeasure N d) := hcint.norm.const_mul _
  calc
    _ ≤ ∫ y, |z.im|⁻¹ *
        ‖centeredReplicatedOneResolventTrace d f lambda z y‖
        ∂replicatedNormalizedGUEMeasure N d := by
      apply norm_integral_le_of_norm_le hg
      filter_upwards with y
      rw [norm_mul]
      have hG := norm_replicated_resolvent_entry_le f lambda hz y p q
      exact (mul_le_mul_of_nonneg_left hG (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = |z.im|⁻¹ *
        ∫ y, ‖centeredReplicatedOneResolventTrace d f lambda z y‖
          ∂replicatedNormalizedGUEMeasure N d := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ReplicatedGUEEuclidean.integral_norm_centeredReplicatedOneResolventTrace_le
        hN hd f lambda hz) (inv_nonneg.mpr (abs_nonneg _))

/-- Exact centered form of the coupling-scaled master cancellation.  It
identifies the covariance remainder above as the complete stochastic defect
before deterministic MDE stability is invoked. -/
theorem replicated_oneResolvent_centered_masterCancellation
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (p q : Fin (N * d)) :
    (∫ y : ReplicatedGUECoordinateSpace N d,
      (((lambda : ℂ) • (hermitianGUEBlock (N * d) y).1) *
        scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
          lambda z y) p q ∂replicatedNormalizedGUEMeasure N d) +
      (lambda : ℂ) ^ 2 *
        (∫ y, replicatedOneResolventTrace d f lambda z y
          ∂replicatedNormalizedGUEMeasure N d) *
        (∫ y, scaledFullGUEResolvent
          (deformationMatrix (replicatedSpectrum d f)) lambda z y p q
          ∂replicatedNormalizedGUEMeasure N d) +
      (lambda : ℂ) ^ 2 *
        replicatedOneResolventCovarianceRemainder d f lambda z p q = 0 := by
  let G := fun y : ReplicatedGUECoordinateSpace N d =>
    scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
      lambda z y p q
  let m := fun y : ReplicatedGUECoordinateSpace N d =>
    replicatedOneResolventTrace d f lambda z y
  let em := ∫ y, m y ∂replicatedNormalizedGUEMeasure N d
  have hmaster := scaledNormalizedGUE_oneResolvent_masterCancellation
    (Nat.mul_pos hN hd) (deformationMatrix (replicatedSpectrum d f))
    (deformationMatrix_isHermitian (replicatedSpectrum d f))
    lambda hz p q
  rw [show normalizedGUEMeasure (N * d) =
    replicatedNormalizedGUEMeasure N d by rfl] at hmaster
  have hsplit : (fun y : ReplicatedGUECoordinateSpace N d =>
      (lambda : ℂ) ^ 2 * NTrace
        (scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
          lambda z y) *
        scaledFullGUEResolvent (deformationMatrix (replicatedSpectrum d f))
          lambda z y p q) = (fun y =>
      ((lambda : ℂ) ^ 2 * em) * G y +
        (lambda : ℂ) ^ 2 *
          (centeredReplicatedOneResolventTrace d f lambda z y * G y)) := by
    funext y
    unfold centeredReplicatedOneResolventTrace
    simp only [replicatedOneResolventTrace, m, em, G]
    ring
  have hG : Integrable G (replicatedNormalizedGUEMeasure N d) := by
    exact integrable_scaledFullGUEResolvent_entry
      (deformationMatrix (replicatedSpectrum d f))
      (deformationMatrix_isHermitian (replicatedSpectrum d f))
      lambda hz p q
  have hc : Integrable
      (centeredReplicatedOneResolventTrace d f lambda z)
      (replicatedNormalizedGUEMeasure N d) :=
    (integrable_replicatedOneResolventTrace (d := d) f lambda hz).sub
      (integrable_const _)
  have hcov : Integrable (fun y =>
      centeredReplicatedOneResolventTrace d f lambda z y * G y)
      (replicatedNormalizedGUEMeasure N d) := by
    apply hc.mul_bdd hG.aestronglyMeasurable
    exact ae_of_all _ fun y => norm_replicated_resolvent_entry_le
      f lambda hz y p q
  rw [hsplit, integral_add (hG.const_mul _) (hcov.const_mul _),
    integral_const_mul, integral_const_mul] at hmaster
  simpa [G, m, em, replicatedOneResolventCovarianceRemainder,
    add_assoc] using hmaster

end CEHNative.BlockBand.External.CEH
