module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedMDE
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPFubini

/-!
# First unconditional fluctuation bounds for the replicated GUE resolvent

This module works under the concrete full normalized GUE coordinate product
law in dimension `N*d`.  It proves a uniform bound, integrability, and a direct
centered second-moment estimate for the normalized one-resolvent trace.  It
also records the exact coordinate derivative, including its `1/(N*d)` trace
normalization, which is the input required by a sharp Gaussian Poincaré step.

Mathlib has scalar Gaussian integration by parts but no
finite-product Gaussian Poincaré inequality.  Consequently the unconditional
second-moment estimate proved here is the maximal direct bound from the
Hermitian resolvent estimate; it does not claim the additional `1/(N*d)^2`
fluctuation gain that a Poincaré theorem would provide.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal
open PencilAdapter

/-- The normalized trace of the full-GUE resolvent at replicated
dimension. -/
def replicatedOneResolventTrace {N : ℕ} (d : ℕ) (f : Spectrum N)
    (lambda : ℝ) (z : ℂ) (y : ReplicatedGUECoordinateSpace N d) : ℂ :=
  NTrace (scaledFullGUEResolvent
    (deformationMatrix (replicatedSpectrum d f)) lambda z y)

/-- The preceding observable is the normalized trace of the paper-facing
resolvent with the full `N*d` GUE sample. -/
theorem replicatedOneResolventTrace_eq_resolvent
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) (z : ℂ)
    (y : ReplicatedGUECoordinateSpace N d) :
    replicatedOneResolventTrace d f lambda z y =
      NTrace (resolvent (replicatedSpectrum d f) lambda
        (hermitianGUEBlock (N * d) y).1 z) := by
  rfl

/-- Every entry of the replicated random resolvent obeys the nonreal
Hermitian resolvent bound. -/
theorem norm_replicated_resolvent_entry_le
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (y : ReplicatedGUECoordinateSpace N d)
    (i j : Fin (N * d)) :
    ‖resolvent (replicatedSpectrum d f) lambda
      (hermitianGUEBlock (N * d) y).1 z i j‖ ≤ |z.im|⁻¹ := by
  let H := deformedMatrix (replicatedSpectrum d f) lambda
    (hermitianGUEBlock (N * d) y).1
  have hH : H.IsHermitian := deformedMatrix_isHermitian _ _ _
    (hermitianGUEBlock_isHermitian (N * d) y)
  change ‖(deformedMatrix (replicatedSpectrum d f) lambda
      (hermitianGUEBlock (N * d) y).1 -
        z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ))⁻¹ i j‖ ≤ |z.im|⁻¹
  simpa [coordinateResolvent, coordinatePencil] using
    (norm_coordinateHermitianResolvent_entry_le H 0 hH
      Matrix.isHermitian_zero hz i j 0)

/-- The normalized trace has the dimension-free bound `|Im z|⁻¹`; the
normalization explicitly uses the full dimension `N*d`. -/
theorem norm_replicatedOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (y : ReplicatedGUECoordinateSpace N d) :
    ‖replicatedOneResolventTrace d f lambda z y‖ ≤ |z.im|⁻¹ := by
  have hn : 0 < N * d := Nat.mul_pos hN hd
  unfold replicatedOneResolventTrace NTrace
    CEHNative.BlockBand.Conventions.normalizedTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    ((N * d : ℕ) : ℝ)⁻¹ * ‖Matrix.trace
        (scaledFullGUEResolvent
          (deformationMatrix (replicatedSpectrum d f)) lambda z y)‖
      ≤ ((N * d : ℕ) : ℝ)⁻¹ *
          (((N * d : ℕ) : ℝ) * |z.im|⁻¹) := by
        gcongr
        rw [Matrix.trace]
        calc
          ‖∑ i : Fin (N * d), scaledFullGUEResolvent
              (deformationMatrix (replicatedSpectrum d f)) lambda z y i i‖
            ≤ ∑ i : Fin (N * d), ‖scaledFullGUEResolvent
              (deformationMatrix (replicatedSpectrum d f)) lambda z y i i‖ :=
                norm_sum_le _ _
          _ ≤ ∑ _i : Fin (N * d), |z.im|⁻¹ := by
                apply Finset.sum_le_sum
                intro i hi
                simpa only [scaledFullGUEResolvent_deformationMatrix] using
                  norm_replicated_resolvent_entry_le f lambda hz y i i
          _ = (((N * d : ℕ) : ℝ) * |z.im|⁻¹) := by simp
    _ = |z.im|⁻¹ := by
      field_simp [show (((N * d : ℕ) : ℝ)) ≠ 0 by exact_mod_cast hn.ne']

/-- The normalized replicated trace is Bochner integrable under the concrete
full-GUE product law. -/
theorem integrable_replicatedOneResolventTrace
    {N d : ℕ}
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (replicatedOneResolventTrace d f lambda z)
      (replicatedNormalizedGUEMeasure N d) := by
  unfold replicatedOneResolventTrace NTrace
    CEHNative.BlockBand.Conventions.normalizedTrace
  change Integrable (fun y =>
    (((N * d : ℕ) : ℂ)⁻¹ * ∑ i : Fin (N * d),
      scaledFullGUEResolvent
        (deformationMatrix (replicatedSpectrum d f)) lambda z y i i))
    (normalizedGUEMeasure (N * d))
  apply Integrable.const_mul
  apply integrable_finsetSum Finset.univ
  intro i hi
  simpa [replicatedNormalizedGUEMeasure] using
    integrable_scaledFullGUEResolvent_entry
      (deformationMatrix (replicatedSpectrum d f))
      (deformationMatrix_isHermitian (replicatedSpectrum d f))
      lambda hz i i

/-- Replacing one real GUE coordinate exhibits the coupled replicated
resolvent as an affine one-coordinate pencil. -/
theorem scaledReplicatedResolvent_update_eq_coordinateResolvent
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) (z : ℂ)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d))))
    (y : ReplicatedGUECoordinateSpace N d) (x : ℝ) :
    scaledFullGUEResolvent
        (deformationMatrix (replicatedSpectrum d f)) lambda z
        (Function.update y k x) =
      coordinateResolvent
        (deformationMatrix (replicatedSpectrum d f) +
          (lambda : ℂ) • complementaryGUEBackground (N * d) k y -
          z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ))
        ((lambda : ℂ) • gueCoordinateDirection (N * d) k) x := by
  unfold scaledFullGUEResolvent coordinateResolvent coordinatePencil
  rw [hermitianGUEBlock_update_eq_coordinatePencil]
  congr 1
  module

/-- Exact derivative of the normalized replicated one-resolvent trace along
one real GUE coordinate.  In particular, the derivative retains the explicit
full-dimensional normalization `1/(N*d)` needed by Gaussian Poincaré. -/
theorem hasDerivAt_replicatedOneResolventTrace_update
    {N d : ℕ} (f : Spectrum N) (lambda : ℝ) {z : ℂ}
    (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate (N * d))))
    (y : ReplicatedGUECoordinateSpace N d) (x : ℝ) :
    let B := deformationMatrix (replicatedSpectrum d f) +
      (lambda : ℂ) • complementaryGUEBackground (N * d) k y -
      z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ)
    let D := (lambda : ℂ) • gueCoordinateDirection (N * d) k
    let G := coordinateResolvent B D x
    HasDerivAt
      (fun u => replicatedOneResolventTrace d f lambda z
        (Function.update y k u))
      ((((N * d : ℕ) : ℂ)⁻¹ *
        ∑ i : Fin (N * d), -(G * D * G) i i)) x := by
  dsimp only
  let H := deformationMatrix (replicatedSpectrum d f) +
    (lambda : ℂ) • complementaryGUEBackground (N * d) k y
  let B := H - z • (1 : Matrix (Fin (N * d)) (Fin (N * d)) ℂ)
  let D := (lambda : ℂ) • gueCoordinateDirection (N * d) k
  let G := coordinateResolvent B D
  have hH : H.IsHermitian :=
    (deformationMatrix_isHermitian (replicatedSpectrum d f)).add
      ((complementaryGUEBackground_isHermitian (N * d) k y).smul
        (RCLike.conj_ofReal lambda))
  have hD : D.IsHermitian :=
    (gueCoordinateDirection_isHermitian (N * d) k).smul
      (RCLike.conj_ofReal lambda)
  have hinv (u : ℝ) : IsUnit (coordinatePencil B D u).det := by
    exact isUnit_det_coordinateHermitianPencil H D hH hD hz u
  have hentry (i : Fin (N * d)) :
      HasDerivAt (fun u => G u i i) (-(G x * D * G x) i i) x :=
    hasDerivAt_coordinateResolvent_entry B D i i x (hinv x)
  have hsum : HasDerivAt (fun u => ∑ i : Fin (N * d), G u i i)
      (∑ i : Fin (N * d), -(G x * D * G x) i i) x :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hentry i)
  have hfun : (fun u => replicatedOneResolventTrace d f lambda z
      (Function.update y k u)) =
      (fun u => (((N * d : ℕ) : ℂ)⁻¹) * ∑ i : Fin (N * d), G u i i) := by
    funext u
    unfold replicatedOneResolventTrace NTrace
      CEHNative.BlockBand.Conventions.normalizedTrace Matrix.trace
    rw [scaledReplicatedResolvent_update_eq_coordinateResolvent]
    rfl
  rw [hfun]
  exact hsum.const_mul (((N * d : ℕ) : ℂ)⁻¹)

/-- Centering of the normalized trace by its full-GUE expectation. -/
def centeredReplicatedOneResolventTrace {N : ℕ} (d : ℕ)
    (f : Spectrum N) (lambda : ℝ) (z : ℂ)
    (y : ReplicatedGUECoordinateSpace N d) : ℂ :=
  replicatedOneResolventTrace d f lambda z y -
    ∫ x, replicatedOneResolventTrace d f lambda z x
      ∂replicatedNormalizedGUEMeasure N d

/-- The expectation has the same resolvent bound. -/
theorem norm_integral_replicatedOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖∫ y, replicatedOneResolventTrace d f lambda z y
      ∂replicatedNormalizedGUEMeasure N d‖ ≤ |z.im|⁻¹ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := replicatedNormalizedGUEMeasure N d)
    (ae_of_all _ (norm_replicatedOneResolventTrace_le hN hd f lambda hz))

/-- Direct pointwise control of the centered trace. -/
theorem norm_centeredReplicatedOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (y : ReplicatedGUECoordinateSpace N d) :
    ‖centeredReplicatedOneResolventTrace d f lambda z y‖ ≤
      2 * |z.im|⁻¹ := by
  unfold centeredReplicatedOneResolventTrace
  calc
    ‖replicatedOneResolventTrace d f lambda z y -
      ∫ x, replicatedOneResolventTrace d f lambda z x
        ∂replicatedNormalizedGUEMeasure N d‖
      ≤ ‖replicatedOneResolventTrace d f lambda z y‖ +
        ‖∫ x, replicatedOneResolventTrace d f lambda z x
          ∂replicatedNormalizedGUEMeasure N d‖ := norm_sub_le _ _
    _ ≤ |z.im|⁻¹ + |z.im|⁻¹ := add_le_add
      (norm_replicatedOneResolventTrace_le hN hd f lambda hz y)
      (norm_integral_replicatedOneResolventTrace_le hN hd f lambda hz)
    _ = 2 * |z.im|⁻¹ := by ring

/-- Unconditional centered second-moment estimate under the concrete
replicated full-GUE product law.  This is the direct resolvent-scale bound
available before Gaussian Poincaré. -/
theorem integral_normSq_centeredReplicatedOneResolventTrace_le
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (lambda : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ y, ‖centeredReplicatedOneResolventTrace d f lambda z y‖ ^ 2
      ∂replicatedNormalizedGUEMeasure N d) ≤
      4 * |z.im|⁻¹ ^ 2 := by
  have hmeas : AEStronglyMeasurable
      (fun y : ReplicatedGUECoordinateSpace N d =>
        ‖centeredReplicatedOneResolventTrace d f lambda z y‖ ^ 2)
      (replicatedNormalizedGUEMeasure N d) := by
    have htrace := (integrable_replicatedOneResolventTrace (d := d)
      f lambda hz).aestronglyMeasurable
    exact ((htrace.sub aestronglyMeasurable_const).norm.pow 2)
  have hbound : ∀ y : ReplicatedGUECoordinateSpace N d,
      ‖centeredReplicatedOneResolventTrace d f lambda z y‖ ^ 2 ≤
        4 * |z.im|⁻¹ ^ 2 := by
    intro y
    have h := norm_centeredReplicatedOneResolventTrace_le
      hN hd f lambda hz y
    have ha : 0 ≤ |z.im|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
    calc
      ‖centeredReplicatedOneResolventTrace d f lambda z y‖ ^ 2 ≤
          (2 * |z.im|⁻¹) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (by norm_num) ha)).2 h
      _ = 4 * |z.im|⁻¹ ^ 2 := by ring
  have hint : Integrable
      (fun y : ReplicatedGUECoordinateSpace N d =>
        ‖centeredReplicatedOneResolventTrace d f lambda z y‖ ^ 2)
      (replicatedNormalizedGUEMeasure N d) :=
    Integrable.of_bound hmeas _ (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound y)
  calc
    _ ≤ ∫ _y : ReplicatedGUECoordinateSpace N d,
        4 * |z.im|⁻¹ ^ 2 ∂replicatedNormalizedGUEMeasure N d := by
      apply integral_mono hint (integrable_const _) hbound
    _ = 4 * |z.im|⁻¹ ^ 2 := by simp

end CEHNative.BlockBand.External.CEH
