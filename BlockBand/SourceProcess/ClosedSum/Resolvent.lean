module

public import BlockBand.SourceProcess.ClosingAux.Reflection
public import BlockBand.SourceProcess.ClosedPath.Iterate

/-!
# `1 - zN_j` is invertible at every length, almost surely

The contraction `N^n → 0` was first proved only at the final length `⌊WT⌋`, but the argument is
length-free: `phys_hinj` already takes a closing length `nS` and a scattering length `nT ≥ 1`.
Here:

* `isUnit_one_sub_smul_of_eigen` (algebra): if `N` has no eigenvalue of modulus `≥ 1`, then
  `det(1 - zN) ≠ 0` for every `‖z‖ ≤ 1`.
* **`ae_isUnit_closingResolvent`** (`0 < b < 1/2`, `-2 < E < 2`, `W ≥ 1`, `h² < 1`, any closing
  length `nS`): almost surely, for every length `j ≥ 1` and every `‖z‖ ≤ 1`,
  `IsUnit (1 - z • closingN 𝕊_j A Π).det`, with `A = farEmbed A_-(nS)`, `Π = farEmbed Π(nS)`.

This discharges the invertibility hypotheses of `ae_closedCol_transport` and
`ae_closedCurrent_iterate` for all phases in the closed unit disc (`ae_closedCol_transport_disc`,
`ae_closedCurrent_iterate_disc`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No eigenvalue of modulus `≥ 1` makes `1 - zN` invertible on the closed unit disc. -/
theorem isUnit_one_sub_smul_of_eigen {N : Matrix ι ι ℂ}
    (hN : ∀ (k : ℂ) (v : ι → ℂ), N *ᵥ v = k • v → 1 ≤ ‖k‖ → v = 0) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    IsUnit (1 - z • N).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_zero] at hker
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hker
    exact hv hker
  have hNv : N *ᵥ v = z⁻¹ • v := by
    conv_rhs => rw [hker]
    rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
  have hk : 1 ≤ ‖z⁻¹‖ := by
    rw [norm_inv]
    exact one_le_inv₀ (norm_pos_iff.2 hz0) |>.2 hz
  exact hv (hN _ v hNv hk)

variable {W : ℕ}

/-- **`1 - zN_j` is invertible at every length `j ≥ 1` and every `‖z‖ ≤ 1`, almost surely.** -/
theorem ae_isUnit_closingResolvent {b E h : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (hh : h ^ 2 < 1) (nS : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      IsUnit (1 - z • closingN (scatteringMatrix b E W j ω)
        (farEmbed (omittedProj b E h W nS ω)) (farEmbed (closingPairing b E h W nS ω))).det := by
  have hη : 0 < (boundaryZ b E).im := boundaryZ_im_pos (by linarith) hE1 hE2
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW, ae_growth_isHermitian W b,
    ae_isUnit_pathPencil_growth hb hW E, ae_isUnit_growth_bond hb0 hW] with ω hU hA hF hB
    j hj z hz
  have hM := isUnit_fullPathMatrix b E j ω hA hη (hF j)
  refine isUnit_one_sub_smul_of_eigen (fun k v hv hk => ?_) hz
  refine eigen_closingN ?_ ?_ ?_ (hU j).1 (phys_hinj hη h hj ω hM hB) k v hv hk
  · rw [farEmbed_mul, omittedProj_mul_self]
  · rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  · rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]

end BlockBand.SourceProcess.ClosedSum
