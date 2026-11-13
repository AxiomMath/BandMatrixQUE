module

public import Mathlib
public import BlockBand.Wegner.PoissonRepresentation
public import BlockBand.Wegner.ProjectedWegnerBasic

/-!
# Poisson representation of matrix resolvent traces

For `B` Hermitian, `Y ⪰ 0`, `η > 0` and any `Q`, the resolvent trace
`f(ζ) = Tr[Q (B + ζY + iη)⁻¹]` is bounded and holomorphic on the closed upper half-plane, so
`∫ (1+t²)⁻¹ f(t) dt = π f(i)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open Matrix Complex MeasureTheory
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The absorbed pencil `B + ζY + iη`. -/
def absorbedPencil (B Y : Matrix n n ℂ) (η : ℝ) (ζ : ℂ) : Matrix n n ℂ :=
  B + ζ • Y + ((η : ℂ) * I) • (1 : Matrix n n ℂ)

/-- The resolvent trace `ζ ↦ Tr[Q (B + ζY + iη)⁻¹]`. -/
def resolventTrace (Q B Y : Matrix n n ℂ) (η : ℝ) (ζ : ℂ) : ℂ :=
  (Q * (absorbedPencil B Y η ζ)⁻¹).trace

/-- On the closed upper half-plane the pencil has imaginary margin `η`. -/
theorem hasImMargin_absorbedPencil {B Y : Matrix n n ℂ} (hB : B.IsHermitian)
    (hY : Y.PosSemidef) (η : ℝ) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    HasImMargin η (absorbedPencil B Y η ζ) := by
  intro v
  have hq : star v ⬝ᵥ (absorbedPencil B Y η ζ *ᵥ v) = star v ⬝ᵥ (B *ᵥ v) +
      ζ * (star v ⬝ᵥ (Y *ᵥ v)) + ((η : ℂ) * I) * (star v ⬝ᵥ v) := by
    simp [absorbedPencil, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul]
  rw [hq]
  have h1 := im_star_dotProduct_mulVec_hermitian hB v
  have hY0 := hY.dotProduct_mulVec_nonneg v
  have hYre : 0 ≤ (star v ⬝ᵥ (Y *ᵥ v)).re := (Complex.nonneg_iff.mp hY0).1
  have hYim : (star v ⬝ᵥ (Y *ᵥ v)).im = 0 := (Complex.nonneg_iff.mp hY0).2.symm
  have hs : (star v ⬝ᵥ v).im = 0 := by
    have := im_star_dotProduct_mulVec_hermitian (Matrix.isHermitian_one (α := ℂ) (n := n)) v
    simpa using this
  simp only [add_im, mul_im, h1, hYim, hs, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    add_zero, mul_one, zero_add]
  nlinarith [mul_nonneg hζ hYre]

section

open scoped Matrix.Norms.L2Operator

/-- The resolvent trace is complex-differentiable wherever the pencil is invertible. -/
theorem differentiableAt_resolventTrace (Q B Y : Matrix n n ℂ) (η : ℝ) {ζ : ℂ}
    (hunit : IsUnit (absorbedPencil B Y η ζ)) :
    DifferentiableAt ℂ (resolventTrace Q B Y η) ζ := by
  have h1 : DifferentiableAt ℂ (absorbedPencil B Y η) ζ := by
    unfold absorbedPencil
    exact ((differentiableAt_const B).add (differentiableAt_id.smul_const Y)).add
      (differentiableAt_const _)
  have h2 : DifferentiableAt ℂ (fun ζ => (absorbedPencil B Y η ζ)⁻¹) ζ := by
    simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    exact (differentiableAt_inverse hunit).comp ζ h1
  have h3 : DifferentiableAt ℂ (fun ζ => Q * (absorbedPencil B Y η ζ)⁻¹) ζ := h2.const_mul Q
  let T : Matrix n n ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℂ ℂ)
  have hT : ∀ A : Matrix n n ℂ, T A = A.trace := fun A => rfl
  have h4 := T.differentiableAt.comp ζ h3
  have he : (T ∘ fun ζ => Q * (absorbedPencil B Y η ζ)⁻¹) = resolventTrace Q B Y η := by
    funext ζ
    simp [hT, resolventTrace]
  rwa [he] at h4

end

/-- The matrix Poisson representation. For `B` Hermitian, `Y ⪰ 0`, `η > 0` and any `Q`, with
`f(ζ) = Tr[Q (B + ζY + iη)⁻¹]`: `t ↦ (1+t²)⁻¹ f(t)` is integrable on `ℝ` and
`∫ (1+t²)⁻¹ f(t) dt = π f(i)`. -/
theorem resolventTrace_poisson {B Y : Matrix n n ℂ} (hB : B.IsHermitian) (hY : Y.PosSemidef)
    {η : ℝ} (hη : 0 < η) (Q : Matrix n n ℂ) :
    Integrable (fun t : ℝ => ((1 + t ^ 2)⁻¹ : ℝ) • resolventTrace Q B Y η t) ∧
      ∫ t : ℝ, ((1 + t ^ 2)⁻¹ : ℝ) • resolventTrace Q B Y η t =
        (Real.pi : ℂ) * resolventTrace Q B Y η I :=
  poisson_upperHalfPlane
    (fun _ hz => differentiableAt_resolventTrace Q B Y η
      ((hasImMargin_absorbedPencil hB hY η hz).isUnit hη))
    (fun _ hz => (hasImMargin_absorbedPencil hB hY η hz).norm_trace_mul_inv_le hη Q)

/-- Imaginary-part form of `resolventTrace_poisson`. -/
theorem resolventTrace_poisson_im {B Y : Matrix n n ℂ} (hB : B.IsHermitian)
    (hY : Y.PosSemidef) {η : ℝ} (hη : 0 < η) (Q : Matrix n n ℂ) :
    Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹ * (resolventTrace Q B Y η t).im) ∧
      ∫ t : ℝ, (1 + t ^ 2)⁻¹ * (resolventTrace Q B Y η t).im =
        Real.pi * (resolventTrace Q B Y η I).im :=
  poisson_upperHalfPlane_im
    (fun _ hz => differentiableAt_resolventTrace Q B Y η
      ((hasImMargin_absorbedPencil hB hY η hz).isUnit hη))
    (fun _ hz => (hasImMargin_absorbedPencil hB hY η hz).norm_trace_mul_inv_le hη Q)

end BlockBand.Wegner
