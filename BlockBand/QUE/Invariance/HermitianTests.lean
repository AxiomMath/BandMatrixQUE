module

public import BlockBand.QUE.Invariance.BlockUnitary
public import BlockBand.QUE.Invariance.Frobenius

/-!
# Hermitian trace tests for the characteristic law

The characteristic function of a physical model at a Hermitian trace test `tr(AH)` is Gaussian,
with covariance the ordered-entry variance `hermitianTestVariance`
(`GaussianRingModel.hermitianTrace_characteristic`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open Matrix MeasureTheory ProbabilityTheory

/-- Diagonal/strict-upper decomposition of a symmetric finite array. -/
theorem sum_symmetric_upper (p : BlockBand.Parameters) (f : p.Site → p.Site → ℝ)
    (hsym : ∀ x y, f y x = f x y) :
    (∑ x, ∑ y, f x y) = (∑ x, f x x) +
      2 * ∑ x, ∑ y with p.siteIndex x < p.siteIndex y, f x y := by
  have hpoint (x y : p.Site) : f x y =
      (if x = y then f x x else 0) +
      (if p.siteIndex x < p.siteIndex y then f x y else 0) +
      (if p.siteIndex y < p.siteIndex x then f y x else 0) := by
    by_cases he : x = y
    · subst y; simp
    · have hi : p.siteIndex x ≠ p.siteIndex y := fun h => he (p.siteIndex_injective h)
      by_cases hlt : p.siteIndex x < p.siteIndex y
      · have hn : ¬p.siteIndex y < p.siteIndex x := by omega
        simp [he, hlt, hn]
      · have hylt : p.siteIndex y < p.siteIndex x := by omega
        simp [he, hlt, hylt, hsym]
  have hsum : (∑ x, ∑ y, f x y) = ∑ x, ∑ y,
      ((if x = y then f x x else 0) +
      (if p.siteIndex x < p.siteIndex y then f x y else 0) +
      (if p.siteIndex y < p.siteIndex x then f y x else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact hpoint x y
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hdiag : (∑ x : p.Site, ∑ y : p.Site, if x = y then f x x else 0) =
      ∑ x, f x x := by simp
  rw [hdiag]
  have hlo : (∑ x : p.Site, ∑ y : p.Site,
      if p.siteIndex y < p.siteIndex x then f y x else 0) =
      ∑ x : p.Site, ∑ y : p.Site,
        if p.siteIndex x < p.siteIndex y then f x y else 0 := Finset.sum_comm
  rw [hlo]
  simp_rw [← Finset.sum_filter]
  ring

/-- Full ordered-entry covariance of a Hermitian trace test. -/
def hermitianTestVariance (p : BlockBand.Parameters) (A : p.SiteMatrix) : ℝ :=
  ∑ x, ∑ y, p.entryVariance x y * Complex.normSq (A x y)

/-- Reduction of the covariance to the diagonal and strict-upper coefficients. -/
theorem hermitianTestVariance_eq_coordinateVariance (p : BlockBand.Parameters)
    (A : p.SiteMatrix) (hA : A.IsHermitian) :
    p.hermitianTestVariance A =
      p.coordinateVariance (fun x => (A x x).re)
        (fun x y => 2 * (A x y).re) (fun x y => 2 * (A x y).im) := by
  have hs : ∀ x y, p.entryVariance y x * Complex.normSq (A y x) =
      p.entryVariance x y * Complex.normSq (A x y) := by
    intro x y
    have h : starRingEnd ℂ (A y x) = A x y := hA.apply x y
    have hn := congrArg Complex.normSq h
    simp only [Complex.normSq_conj] at hn
    rw [p.entryVariance_symm, hn]
  rw [hermitianTestVariance, p.sum_symmetric_upper _ hs]
  unfold coordinateVariance
  have hdiag (x : p.Site) : (A x x).im = 0 := by
    have hd : starRingEnd ℂ (A x x) = A x x := hA.apply x x
    have h := congrArg Complex.im hd
    simp only [Complex.conj_im] at h
    linarith
  simp_rw [Complex.normSq_apply]
  simp_rw [hdiag, mul_zero, add_zero, ← pow_two]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- A Hermitian trace pairing equals its real-coordinate pairing. -/
theorem hermitianTrace_eq_coordinatePairing (p : BlockBand.Parameters)
    (A H : p.SiteMatrix) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    (Matrix.trace (A * H)).re =
      p.coordinatePairing (fun x => (A x x).re)
        (fun x y => 2 * (A x y).re) (fun x y => 2 * (A x y).im) H := by
  have hconj (x y : p.Site) : starRingEnd ℂ (H x y) = H y x := hH.apply y x
  have hconjA (x y : p.Site) : starRingEnd ℂ (A x y) = A y x := hA.apply y x
  have hs : ∀ x y, (A y x * H x y).re = (A x y * H y x).re := by
    intro x y
    rw [← hconjA, ← hconj]
    simp [Complex.mul_re]
  have hdiag (x : p.Site) : (A x x).im = 0 := by
    have hd : starRingEnd ℂ (A x x) = A x x := hA.apply x x
    have h := congrArg Complex.im hd
    simp only [Complex.conj_im] at h
    linarith
  have ht : (Matrix.trace (A * H)).re = ∑ x, ∑ y, (A x y * H y x).re := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [ht, p.sum_symmetric_upper _ hs]
  unfold coordinatePairing
  simp_rw [Complex.mul_re]
  simp_rw [hdiag, zero_mul, sub_zero]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← hconj]
  simp only [Complex.conj_im, Complex.conj_re]
  ring

/-- Every physical model has the full Hermitian trace characteristic
function with the unnormalized ordered-entry covariance. -/
theorem GaussianRingModel.hermitianTrace_characteristic
    {p : BlockBand.Parameters} (model : p.GaussianRingModel)
    (A : p.SiteMatrix) (hA : A.IsHermitian) :
    (∫ H, Complex.exp (Complex.I * ((Matrix.trace (A * H)).re : ℂ))
      ∂(model.law : Measure p.SiteMatrix)) =
    Complex.exp (-(p.hermitianTestVariance A : ℂ) / 2) := by
  have hae : (fun H : p.SiteMatrix =>
      Complex.exp (Complex.I * ((Matrix.trace (A * H)).re : ℂ))) =ᵐ[
        (model.law : Measure p.SiteMatrix)]
      (fun H => Complex.exp (Complex.I * (p.coordinatePairing
        (fun x => (A x x).re) (fun x y => 2 * (A x y).re)
        (fun x y => 2 * (A x y).im) H : ℂ))) := by
    filter_upwards [model.isPhysical.1] with H hH
    rw [p.hermitianTrace_eq_coordinatePairing A H hA hH]
  rw [integral_congr_ae hae, model.isPhysical.2,
    p.hermitianTestVariance_eq_coordinateVariance A hA]

end BlockBand.Parameters
