module

public import BlockBand.Palm.CoarseRelativeFluctuation

/-!
# Coarse relative local law: Gaussian integration by parts for resolvent entries

* `hasWeakCoordPartial_of_contDiff`: a `C¹` function has its classical partial as the
  Lebesgue weak partial used by `MultivariateGaussianIBP` (Mathlib integration by parts against
  smooth compactly supported tests).
* `gaussian_ibp_of_bounded`: from the Gaussian input `MultivariateGaussianIBP`, for a
  bounded `C¹` complex function with bounded partial `j`, `E[y_j f] = E[∂_j f]` under
  `gaussianProduct 1`.
* `linInv_hasFDerivAt`, `linInv_contDiff`: any real-linear functional of the inverse of an
  everywhere invertible affine matrix family is `C¹` with derivative `-ℓ(R (L v) R)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal ContDiff

theorem coordPartial_eq_fderiv {ι : Type} [Fintype ι] [DecidableEq ι] {φ : (ι → ℝ) → ℝ}
    (hφ : Differentiable ℝ φ) (j : ι) (x : ι → ℝ) :
    coordPartial φ j x = fderiv ℝ φ x (Pi.single j 1) := by
  unfold coordPartial
  have hu := hasDerivAt_update x j (x j)
  have h := (hφ (Function.update x j (x j))).hasFDerivAt.comp_hasDerivAt (x j) hu
  rw [Function.update_eq_self] at h
  exact h.deriv

theorem hasWeakCoordPartial_of_contDiff {ι : Type} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (j : ι) :
    HasWeakCoordPartial j f (fun x => fderiv ℝ f x (Pi.single j 1)) := by
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (fun x => fderiv ℝ f x (Pi.single j 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨hfc.locallyIntegrable, hdc.locallyIntegrable, ?_⟩
  intro φ hφ hφc
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ1 : Continuous (fun x => fderiv ℝ φ x (Pi.single j 1)) :=
    ((hφ.of_le (by exact_mod_cast le_top)).continuous_fderiv (n := 1) (by simp)).clm_apply
      continuous_const
  simp_rw [coordPartial_eq_fderiv hφd j]
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (𝕜 := ℝ)
    (f := φ) (g := f) (v := Pi.single j 1)
    ((hφ1.smul hfc).integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) _ |>.smul_right))
    ((hφ.continuous.smul hdc).integrable_of_hasCompactSupport hφc.smul_right)
    ((hφ.continuous.smul hfc).integrable_of_hasCompactSupport hφc.smul_right)
    (fun x _ => hφd x) (fun x _ => hf.differentiable (by simp) x)
  rw [h, neg_neg]

/-- Coordinates are integrable under the standard Gaussian product law. -/
theorem coord_integrable {ι : Type} [Fintype ι] (j : ι) :
    Integrable (fun y : ι → ℝ => y j) (gaussianProduct (fun _ : ι => (1 : ℝ≥0))) := by
  unfold gaussianProduct
  have hmp := measurePreserving_eval (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) j
  have hid : Integrable id (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) :=
    (ProbabilityTheory.memLp_id_gaussianReal 1).integrable le_rfl
  exact (hmp.integrable_comp measurable_id.aestronglyMeasurable).mpr hid

/-- **Gaussian IBP** (from `MultivariateGaussianIBP`) for bounded `C¹` functions with a
bounded partial: `E[y_j f] = E[∂_j f]` under `gaussianProduct 1`. -/
theorem gaussian_ibp_of_bounded (hIBP : MultivariateGaussianIBP) {ι : Type} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (j : ι) {C C' : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (hC' : ∀ y, ‖fderiv ℝ f y (Pi.single j 1)‖ ≤ C') :
    ∫ y, (y j : ℂ) * f y ∂gaussianProduct (fun _ : ι => (1 : ℝ≥0)) =
      ∫ y, fderiv ℝ f y (Pi.single j 1) ∂gaussianProduct (fun _ : ι => (1 : ℝ≥0)) := by
  have hprob : IsProbabilityMeasure (gaussianProduct (fun _ : ι => (1 : ℝ≥0))) := by
    unfold gaussianProduct; infer_instance
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (fun x => fderiv ℝ f x (Pi.single j 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfi : Integrable f (gaussianProduct (fun _ : ι => (1 : ℝ≥0))) :=
    Integrable.of_bound hfc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hgi : Integrable (fun x => fderiv ℝ f x (Pi.single j 1))
      (gaussianProduct (fun _ : ι => (1 : ℝ≥0))) :=
    Integrable.of_bound hdc.aestronglyMeasurable C' (Filter.Eventually.of_forall hC')
  have hxi : Integrable (fun x : ι → ℝ => x j • f x) (gaussianProduct (fun _ : ι => (1 : ℝ≥0))) := by
    have hc : Integrable (fun x : ι → ℝ => ((x j : ℝ) : ℂ))
        (gaussianProduct (fun _ : ι => (1 : ℝ≥0))) := (coord_integrable j).ofReal
    have := hc.bdd_mul (f := f) hfc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Complex.real_smul]
    ring
  have h := hIBP ι (fun _ => (1 : ℝ≥0)) ℂ j f (fun x => fderiv ℝ f x (Pi.single j 1))
    (fun _ _ => one_pos) (hasWeakCoordPartial_of_contDiff hf j) hfi hgi hxi
  simp only [NNReal.coe_one, one_smul, Complex.real_smul] at h
  exact h

section Calc

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Derivative of `y ↦ ℓ((A₀ + L y)⁻¹)` for a real-linear functional `ℓ`. -/
theorem linInv_hasFDerivAt (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (ℓ : Matrix ι ι ℂ →ₗ[ℝ] ℂ) (hU : ∀ y, IsUnit (A₀ + L y).det) (y : V) :
    ∃ D : V →L[ℝ] ℂ, HasFDerivAt (fun y => ℓ ((A₀ + L y)⁻¹)) D y ∧
      ∀ v, D v = -ℓ ((A₀ + L y)⁻¹ * L v * (A₀ + L y)⁻¹) := by
  set L' := LinearMap.toContinuousLinearMap L
  set T := LinearMap.toContinuousLinearMap ℓ
  have hA : HasFDerivAt (fun y => A₀ + L y) L' y :=
    (L'.hasFDerivAt (x := y)).const_add A₀
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (hU y)
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinv
  have hc := T.hasFDerivAt.comp y (hinv.comp y hA)
  have hfun : (fun y => ℓ ((A₀ + L y)⁻¹)) = (T ∘ Ring.inverse ∘ fun y => A₀ + L y) := by
    funext w
    simp [T, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  refine ⟨_, hc, ?_⟩
  intro v
  rw [← Ring.inverse_unit u, hu, ← Matrix.nonsing_inv_eq_ringInverse]
  change ℓ (-((A₀ + L y)⁻¹ * L v * (A₀ + L y)⁻¹)) = _
  rw [map_neg]

theorem linInv_contDiff (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (ℓ : Matrix ι ι ℂ →ₗ[ℝ] ℂ) (hU : ∀ y, IsUnit (A₀ + L y).det) :
    ContDiff ℝ 1 (fun y => ℓ ((A₀ + L y)⁻¹)) := by
  set T := LinearMap.toContinuousLinearMap ℓ
  have hL : ContDiff ℝ 1 (fun y => A₀ + L y) :=
    contDiff_const.add ((LinearMap.toContinuousLinearMap L).contDiff (n := 1))
  have hI : ContDiff ℝ 1 (fun y => (A₀ + L y)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (hU y)
    have h := contDiffAt_ringInverse ℝ (n := 1) u
    rw [hu] at h
    exact h.comp y hL.contDiffAt
  exact (T.contDiff (n := 1)).comp hI

end Calc

end BlockBand.Palm.CoarseRelative
