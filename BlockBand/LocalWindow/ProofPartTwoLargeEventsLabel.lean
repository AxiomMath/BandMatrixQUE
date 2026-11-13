module

public import BlockBand.LocalWindow.ProofPartTwoLargeEventsNorm
public import BlockBand.LocalWindow.ProofPartTwoFinal

/-!
# The pole label at a given energy, large `ρ`

At a given energy `E` (not a pole) with no crowding at radius `ε₀ = W^{-A₀}` and
`LargePoleAt A₀ H` (`σ(E) > W^H`), a simple exterior eigenvalue lies within `ε₀` of `E`.

## Main results

* `truncInv_eq_inv_of_lt`, **`near_of_largePoleAt`**: the label `j₀` separated at `ε₀` from `E`
  (`exists_poleSeparated_of_crowding`) is within `ε₀` of `E` (otherwise `ρ̂ = ρ`, `σ = 0`).
* **`largeRho_label`**: for a smaller radius `ε₁` and a grid energy `e` with `ε₁ + |E - e| ≤ ε₀`,
  `j₀` is simple, separated at `ε₁` from both `E` and `e` (`poleSeparated_shift`), and
  `|ρ(E)| > W^H - ‖C*φ‖²/ε₀` (`abs_poleRho_gt_of_largePoleAt`). In the assembly `ε₁ = W^{-A₀-1}`
  is the truncation radius of the certificates and of the compressed bad set (a second exterior
  event, at `A₀ + 1`), and `ε₀` the crowding radius (the exterior event at `A₀`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

theorem truncInv_eq_inv_of_lt {ε x : ℝ} (h : ε < |x|) : truncInv ε x = x⁻¹ := by
  simp only [truncInv, not_le.mpr h, ↓reduceIte]

/-- **A large singular part forces the label near `E`**: if `j₀` is separated at `ε₀ = W^{-A₀}`
from the nonpole energy `E` and `σ(E) > W^H`, then `|λ_{j₀} - E| ≤ ε₀`. -/
theorem near_of_largePoleAt {om : SplitState p i} (hH : om.1.IsHermitian) {j₀ : ExteriorSite p i}
    {A₀ H E : ℝ} (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hsep : PoleSeparated ((p.W : ℝ) ^ (-A₀)) hH j₀ E) (hl : LargePoleAt p i A₀ H om E) :
    |hH.eigenvalues j₀ - E| ≤ (p.W : ℝ) ^ (-A₀) := by
  by_contra hfar
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hσ := opNorm_physicalCoareaF_sub_truncF_eq om hH j₀ hdet hsep
  have he : poleRhoHat ((p.W : ℝ) ^ (-A₀)) hH j₀ om.2.1 E = poleRho hH j₀ om.2.1 E := by
    unfold poleRhoHat poleRho
    rw [truncInv_eq_inv_of_lt (not_le.mp hfar)]
  unfold LargePoleAt at hl
  rw [hσ, he, sub_self, abs_zero] at hl
  exact absurd hl (not_lt.mpr (Real.rpow_nonneg hW.le H))

/-- **The pole label at a given energy and its grid energy**: no crowding at `ε₀ = W^{-A₀}` around the nonpole energy `E`, `σ(E) > W^H`,
`0 ≤ ε₁` and `ε₁ + |E - e| ≤ ε₀`. Then some label `j₀` is simple, separated at `ε₀` and at `ε₁`
from `E`, separated at `ε₁` from `e`, and `|ρ(E)| > W^H - ‖C*φ‖²/ε₀`. -/
theorem largeRho_label {om : SplitState p i} (hH : om.1.IsHermitian) {A₀ H E e ε₁ : ℝ}
    (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hcr : spectralSum om.1 (ProofCrowding.iccInd (E - (p.W : ℝ) ^ (-A₀))
      (E + (p.W : ℝ) ^ (-A₀))) < 2)
    (hl : LargePoleAt p i A₀ H om E) (hε₁ : ε₁ + |E - e| ≤ (p.W : ℝ) ^ (-A₀)) :
    ∃ j₀ : ExteriorSite p i, PoleSimple hH j₀ ∧ PoleSeparated ((p.W : ℝ) ^ (-A₀)) hH j₀ E ∧
      PoleSeparated ε₁ hH j₀ E ∧ PoleSeparated ε₁ hH j₀ e ∧
      (p.W : ℝ) ^ H - sqNorm (poleCoupling hH j₀ om.2.1) / (p.W : ℝ) ^ (-A₀) <
        |poleRho hH j₀ om.2.1 E| := by
  obtain ⟨j₀, hsep⟩ := exists_poleSeparated_of_crowding hH hcr
  have hnear := near_of_largePoleAt hH hdet hsep hl
  have hs : PoleSimple hH j₀ := poleSimple_of_poleSeparated hH hsep hnear
  have hEe0 := abs_nonneg (E - e)
  have hsep' : PoleSeparated (ε₁ + |E - e|) hH j₀ E := poleSeparated_mono hH hε₁ hsep
  refine ⟨j₀, hs, hsep, poleSeparated_mono hH (by linarith) hsep,
    poleSeparated_shift hH hsep' le_rfl, abs_poleRho_gt_of_largePoleAt om hH j₀ hdet hsep hl⟩

end BlockBand.LocalWindow.ProofPartTwo
