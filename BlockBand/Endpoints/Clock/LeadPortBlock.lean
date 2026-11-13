module

public import BlockBand.Internal.Contracts.ClocksCommonPort

/-!
# The matched-lead self-energy is the port block of the full inverse

The old self-energy fed into the common-port law, `X = leadSchur e W r ω = C*(H_path - e)⁻¹C`
(`Layers.pathSchur` of `pathAt W r ω`, `C = pathPortCoupling`), with
`K = matchedLeadK b e X = z_b I - X`, has inverse `K⁻¹` equal to the port block
`boundaryResolvent b e W r ω` of `fullInverse = 𝓜⁻¹`,
`𝓜 = fullPathMatrix = [[H_path - e, C],[C*, z_b I]]`, the matrix whose port columns are
`Clocks.leadResponse`. This is the Schur-complement formula for the `(2,2)` block of the inverse of
a `2 × 2` block matrix.

The hypotheses are `det(H_path - e) ≠ 0` (off the null pole set of the path; `leadSchur` uses
Mathlib's `⁻¹`, which is `0` on singular matrices, so the identity needs it) and `det K ≠ 0`. The
hypothesis `det K ≠ 0` is not needed: with Mathlib's totalized inverse the identity holds from
`det(H_path - e) ≠ 0` alone (`Layers.pg_toBlocks22_inv`); it is kept in these statements, which are
therefore slightly weaker than possible. It also follows from Hermitian `X` and `Im z_b ≠ 0`
(`det_matchedLeadK_ne_zero_of_isHermitian`); `X` is Hermitian when the path matrix is
(`leadSchur_isHermitian`). The path blocks are Hermitian only almost surely, so the Hermitian
hypothesis is explicit in `boundaryResolvent_eq_inv_matchedLeadK_of_isHermitian`.

Main results:
* `toBlocks22_inv_fromBlocks` (generic Schur complement, any field-valued square blocks over `ℂ`);
* `boundaryResolvent_eq_inv_matchedLeadK`;
* `leadResponse_ports` (port rows of `Clocks.leadResponse` are `boundaryResolvent`);
* `leadSchur_isHermitian`, `det_matchedLeadK_ne_zero_of_isHermitian`,
  `boundaryResolvent_eq_inv_matchedLeadK_of_isHermitian`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped Matrix ComplexOrder

/-- Schur complement: if `A` and `S = D - C A⁻¹ B` are invertible, the `(2,2)` block of
`[[A, B],[C, D]]⁻¹` is `S⁻¹`. -/
theorem toBlocks22_inv_fromBlocks {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hA : A.det ≠ 0) (hS : (D - C * A⁻¹ * B).det ≠ 0) :
    (fromBlocks A B C D)⁻¹.toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let _ : Invertible A := A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)
  have hS' : IsUnit (D - C * ⅟A * B).det := by
    rw [invOf_eq_nonsing_inv]; exact isUnit_iff_ne_zero.mpr hS
  let _ : Invertible (D - C * ⅟A * B) := (D - C * ⅟A * B).invertibleOfIsUnitDet hS'
  let _ : Invertible (fromBlocks A B C D) := fromBlocks₁₁Invertible A B C D
  rw [← invOf_eq_nonsing_inv (fromBlocks A B C D), invOf_fromBlocks₁₁_eq, toBlocks_fromBlocks₂₂,
    invOf_eq_nonsing_inv, invOf_eq_nonsing_inv]

/-- **The port block of the full inverse.** Off the pole set of the path (`det(H_path - e) ≠ 0`)
and when `K = z_b - X` is invertible, the port block of the full inverse `fullInverse b e W r ω`
equals `K⁻¹ = (matchedLeadK b e (leadSchur e W r ω))⁻¹`.
-/
theorem boundaryResolvent_eq_inv_matchedLeadK (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (hH : (pathMatrix (pathAt W r ω) - (e : ℂ) • 1).det ≠ 0)
    (hK : (matchedLeadK b e (leadSchur e W r ω)).det ≠ 0) :
    boundaryResolvent b e W r ω = (matchedLeadK b e (leadSchur e W r ω))⁻¹ := by
  have hK' : matchedLeadK b e (leadSchur e W r ω) =
      boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        (pathPortCoupling (pathAt W r ω))ᴴ * (pathMatrix (pathAt W r ω) - (e : ℂ) • 1)⁻¹ *
          pathPortCoupling (pathAt W r ω) := rfl
  rw [hK'] at hK ⊢
  exact toBlocks22_inv_fromBlocks _ _ _ _ hH hK

/-- The port rows of `Clocks.leadResponse` are the port block `boundaryResolvent` (definitional:
`leadResponse x y = fullInverse x (Sum.inr y)`). -/
theorem leadResponse_ports (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (x y : Fin 2 × Fin W) :
    leadResponse b e W r ω (Sum.inr x) y = boundaryResolvent b e W r ω x y := rfl

/-- If the path matrix is Hermitian, so is the self-energy `X = C*(H_path - e)⁻¹C` (`e` real). -/
theorem leadSchur_isHermitian (e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (hH : (pathMatrix (pathAt W r ω)).IsHermitian) : (leadSchur e W r ω).IsHermitian := by
  have h1 : (pathMatrix (pathAt W r ω) - (e : ℂ) • 1).IsHermitian := by
    refine hH.sub ?_
    simp [IsHermitian, conjTranspose_smul]
  exact isHermitian_conjTranspose_mul_mul _ h1.inv

/-- For Hermitian `X` and `Im z_b ≠ 0` (e.g. `etaZ b e > 0` in the bulk), `K = z_b - X` is
invertible. -/
theorem det_matchedLeadK_ne_zero_of_isHermitian (b e : ℝ) {W : ℕ}
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (hη : etaZ b e ≠ 0) :
    (matchedLeadK b e X).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff (M := matchedLeadK b e X)).mpr h
  have hXv : X *ᵥ v = boundaryZ b e • v := by
    have : boundaryZ b e • v - X *ᵥ v = 0 := by
      simpa [matchedLeadK, sub_mulVec, smul_mulVec, one_mulVec] using hv
    exact (sub_eq_zero.mp this).symm
  have hq : star v ⬝ᵥ X *ᵥ v = boundaryZ b e * (star v ⬝ᵥ v) := by
    rw [hXv, dotProduct_smul, smul_eq_mul]
  have him := hX.im_star_dotProduct_mulVec_self v
  have hpos := Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hv0)
  rw [hq] at him
  have : (boundaryZ b e).im * (star v ⬝ᵥ v).re = 0 := by
    simpa [Complex.mul_im, ← hpos.2] using him
  rcases mul_eq_zero.mp this with h' | h'
  · exact hη h'
  · exact hpos.1.ne' h'

/-- The matched-lead identification with `det K ≠ 0` derived from a Hermitian path matrix and
`Im z_b ≠ 0`. -/
theorem boundaryResolvent_eq_inv_matchedLeadK_of_isHermitian (b e : ℝ) (W r : ℕ)
    (ω : GrowthPath W) (hHerm : (pathMatrix (pathAt W r ω)).IsHermitian) (hη : etaZ b e ≠ 0)
    (hH : (pathMatrix (pathAt W r ω) - (e : ℂ) • 1).det ≠ 0) :
    boundaryResolvent b e W r ω = (matchedLeadK b e (leadSchur e W r ω))⁻¹ :=
  boundaryResolvent_eq_inv_matchedLeadK b e W r ω hH
    (det_matchedLeadK_ne_zero_of_isHermitian b e (leadSchur_isHermitian e W r ω hHerm) hη)

end BlockBand.Endpoints.Clock
