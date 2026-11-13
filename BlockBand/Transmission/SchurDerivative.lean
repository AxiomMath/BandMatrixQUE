module

public import BlockBand.Transmission.SchurPassivity
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Constructed absorbed-pencil source derivatives

The first deterministic inverse/source differential component of the differentiated covariance
lemma. Finite complex matrices use the Euclidean `L²` operator norm, not an entrywise or
normalized Schatten norm. The complex inverse differential is local around an
invertible base point. Its physical real-line specialization constructs that inverse from
Hermitian `A`, `Q`, PSD absorption `Γ` and `η > 0`; neither the inverse nor the derivative is
assumed.

The real source-response derivative is not asserted to be holomorphic: the
adjoint differentiates along the real line. Noncommutative factor orders are
preserved. There is no measure, Gaussian conditional covariance/Poincaré estimate,
width-uniform bound or process convergence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex local inverse derivative for an arbitrary matrix direction.
Invertibility is required only at a, not assumed on a whole complex line. -/
theorem affineInverse_hasDerivAt (K Q : Matrix ι ι ℂ) (a : ℂ)
    (hK : IsUnit (K + a • Q)) :
    HasDerivAt (fun t : ℂ => (K + t • Q)⁻¹)
      (-((K + a • Q)⁻¹ * Q * (K + a • Q)⁻¹)) a := by
  have hp : HasDerivAt (fun t : ℂ => K + t • Q) Q a := by
    simpa using ((hasDerivAt_id a).smul_const Q).const_add K
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℂ) hK.unit).comp_hasDerivAt a hp
  have huinv : (↑(hK.unit⁻¹) : Matrix ι ι ℂ) = (K + a • Q)⁻¹ := by
    rw [← Ring.inverse_of_isUnit hK, Matrix.nonsing_inv_eq_ringInverse]
  simpa only [Function.comp_apply, huinv, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, Matrix.nonsing_inv_eq_ringInverse] using! hi

/-- Eliminated two-port near inverse derivative at zero source.
The arbitrary complex source direction may be non-Hermitian; its local inverse
is constructed from Hermitian near/far blocks and Im z>0, not supplied. -/
theorem passiveSchurInverse_source_hasDerivAt {κ : Type*} [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ ℂ) (hA : A.IsHermitian)
    (B : Matrix ι κ ℂ) (D : Matrix ι ι ℂ) (hD : D.IsHermitian)
    (Q : Matrix κ κ ℂ) {z : ℂ} (hz : 0 < z.im) :
    let K := portPencil (passiveSchurInput A B D z) z
    HasDerivAt (fun h : ℂ => (K + h • Q)⁻¹) (-(K⁻¹ * Q * K⁻¹)) 0 := by
  dsimp only
  have hu := passiveSchur_near_isUnit A hA B D hD hz
  simpa using affineInverse_hasDerivAt
    (portPencil (passiveSchurInput A B D z) z) Q 0 (by simpa using hu)

/-- Hermitian real part with positive-regulated PSD absorption. -/
def regulatedAbsorbedPencil (A Γ : Matrix ι ι ℂ) (η : ℝ) : Matrix ι ι ℂ :=
  A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ))

/-- Every real Hermitian source perturbation is invertible, constructed from
strict positive absorption; the source need not commute with A or Γ. -/
theorem regulatedAbsorbedPencil_realLine_isUnit (A Q Γ : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian) (hΓ : Γ.PosSemidef)
    {η : ℝ} (hη : 0 < η) (r : ℝ) :
    IsUnit (regulatedAbsorbedPencil A Γ η + (r : ℂ) • Q) := by
  have hAQ : (A + r • Q).IsHermitian :=
    hA.add (hQ.smul (RCLike.conj_ofReal r))
  have hd := isUnit_det_add_I_smul_add_pos_regulator hAQ hΓ hη
  have he : regulatedAbsorbedPencil A Γ η + (r : ℂ) • Q =
      (A + r • Q) + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ)) := by
    ext i j
    simp only [regulatedAbsorbedPencil, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul]
    ring
  rw [he]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr hd

/-- Real inverse derivative -RQR, with inverse construction included.
The regulator η remains fixed while the real source strength varies. -/
theorem regulatedAbsorbedInverse_hasDerivAt (A Q Γ : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian) (hΓ : Γ.PosSemidef)
    {η : ℝ} (hη : 0 < η) (r : ℝ) :
    HasDerivAt (fun t : ℝ =>
      (regulatedAbsorbedPencil A Γ η + (t : ℂ) • Q)⁻¹)
      (-((regulatedAbsorbedPencil A Γ η + (r : ℂ) • Q)⁻¹ * Q *
        (regulatedAbsorbedPencil A Γ η + (r : ℂ) • Q)⁻¹)) r := by
  have hc := affineInverse_hasDerivAt (regulatedAbsorbedPencil A Γ η) Q (r : ℂ)
    (regulatedAbsorbedPencil_realLine_isUnit A Q Γ hA hQ hΓ hη r)
  have hr := (hc.hasFDerivAt.restrictScalars ℝ).comp r Complex.ofRealCLM.hasFDerivAt
  simpa using! hr.hasDerivAt

/-- Real-line differentiated response, retaining the two distinct outside
orders R* Q* R* S R and R* S R Q R. S is arbitrary and need not commute. -/
theorem regulatedAbsorbedResponse_hasDerivAt (A Q Γ S : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hQ : Q.IsHermitian) (hΓ : Γ.PosSemidef)
    {η : ℝ} (hη : 0 < η) (r : ℝ) :
    let R := (regulatedAbsorbedPencil A Γ η + (r : ℂ) • Q)⁻¹
    HasDerivAt (fun t : ℝ =>
      star ((regulatedAbsorbedPencil A Γ η + (t : ℂ) • Q)⁻¹) * S *
        (regulatedAbsorbedPencil A Γ η + (t : ℂ) • Q)⁻¹)
      (-(star R * star Q * star R * S * R) -
        star R * S * R * Q * R) r := by
  dsimp only
  have hR := regulatedAbsorbedInverse_hasDerivAt A Q Γ hA hQ hΓ hη r
  have hd := (hR.star.mul_const S).mul hR
  convert hd using 1
  simp only [star_neg, star_mul]
  noncomm_ring

end BlockBand.Transmission
