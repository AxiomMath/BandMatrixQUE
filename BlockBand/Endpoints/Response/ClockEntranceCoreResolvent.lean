module

public import BlockBand.Endpoints.Response.ClockEntranceStepDefs
public import BlockBand.Endpoints.Response.ResponseVariancePath
public import BlockBand.Endpoints.Response.PassDerivativeLimitBridge
public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateAlgebra

/-!
# The propagation step, part 1: the port resolvent of the path at one length

Part of the clock fractional-entrance lemma (the propagation `A₊ = L*AL`). Deterministic linear
algebra at a fixed path length `r`, on the good event `cec_good` (Hermitian GUE blocks,
invertible interior block `H_r - E`), plus the almost-sure statement of the good event.

* `cec_ae_good` — the good event holds `growthPathLaw`-a.s. (from `ConditionalBlockGUECount`,
  through `path_ae_isUnit`, and `guelawBridge_holds`).
* `cec_nearResolvent` — on the good event, the near-near block of the port resolvent
  `ℝ_r = G_{ports}` is `passiveResolvent (pathX r) = (z - X_r)⁻¹`, and `z - X_r` is invertible
  (Schur complement of the path block, then of the far port; `X_r` is
  `pathX = nearSchur z 𝕏_r`).
* `cec_column_eqs` — for an invertible full matrix, the boundary columns `𝒰_r = G_{int,ports}`,
  `ℝ_r = G_{ports}` solve `(H - E)𝒰 + Cℝ = 0` and `C*𝒰 + zℝ = I`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs

variable {b E : ℝ} {W : ℕ}

/-- The unabsorbed path carries zero absorption. -/
theorem cec_absorptionDiag_zero (W r : ℕ) :
    absorptionDiag W (layerAbsorption W (fun _ => 0) r) = 0 := by
  ext x y
  simp [absorptionDiag, layerAbsorption, Matrix.diagonal_apply]

/-- `X_r = nearSchur z (C*(H_r - E)⁻¹C)` for the unabsorbed path. -/
theorem cec_pathX_eq (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    pathX b E W r ω = nearSchur (boundaryZ b E)
      ((pfiCoup W r ω.2)ᴴ * (pfiInt E W r ω)⁻¹ * pfiCoup W r ω.2) := by
  simp only [pathX, pathNearSchur, absorbedPathSchur, cec_absorptionDiag_zero, add_zero]
  rfl

/-- The good event at length `r`: all GUE blocks Hermitian and `H_r - E` invertible. -/
def cec_good (E : ℝ) (W r : ℕ) (ω : GrowthPath W) : Prop :=
  (∀ k, (ω.1 k).IsHermitian) ∧ IsUnit (pfiInt E W r ω).det

/-- **The good event is almost sure** (from `ConditionalBlockGUECount`, through the Wegner-count
consequence `path_ae_isUnit`). -/
theorem cec_ae_good (hCount : ConditionalBlockGUECount) (hb : b < 1 / 2) (hW : 0 < W)
    (r : ℕ) : ∀ᵐ ω ∂growthPathLaw W b, cec_good E W r ω := by
  have hD : Measurable fun B : ℕ → Matrix (Fin W) (Fin W) ℂ =>
      pathBondPart W r B - (E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ) :=
    (measurable_pathBondPart W r).sub_const _
  have hH : ∀ B : ℕ → Matrix (Fin W) (Fin W) ℂ,
      (pathBondPart W r B - (E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)).IsHermitian :=
    fun B => (pathBondPart_isHermitian W r B).sub (pfi_isHermitian_real_smul_one E)
  filter_upwards [ae_growthPath_isHermitian W b,
    path_ae_isUnit hCount guelawBridge_holds hW hb _ hD hH] with ω h1 h2
  refine ⟨h1, ?_⟩
  have : pfiInt E W r ω =
      pathBondPart W r ω.2 - (E : ℂ) • 1 + blockSumOf (pathBlocks W r ω) := by
    rw [pfiInt_eq]; abel
  rw [this]; exact h2

/-- The two-port Schur matrix `𝕏_r = C*(H_r - E)⁻¹C` is Hermitian for Hermitian blocks. -/
theorem cec_portSchur_isHermitian {r : ℕ} {ω : GrowthPath W} (hω : ∀ k, (ω.1 k).IsHermitian) :
    ((pfiCoup W r ω.2)ᴴ * (pfiInt E W r ω)⁻¹ * pfiCoup W r ω.2).IsHermitian :=
  isHermitian_conjTranspose_mul_mul _ (pfiInt_isHermitian E W r hω).inv

/-- On the good event, `ℝ_r = (z - 𝕏_r)⁻¹`. -/
theorem cec_boundaryResolvent_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {r : ℕ}
    {ω : GrowthPath W} (hω : cec_good E W r ω) :
    boundaryResolvent b E W r ω = (boundaryZ b E • 1 -
      (pfiCoup W r ω.2)ᴴ * (pfiInt E W r ω)⁻¹ * pfiCoup W r ω.2)⁻¹ := by
  have hz := pfi_boundaryZ_im_pos hb hE1 hE2
  have hX := cec_portSchur_isHermitian (E := E) (r := r) hω.1
  unfold boundaryResolvent fullInverse
  rw [fullPathMatrix_eq]
  exact toBlocks₂₂_inv_fromBlocks _ _ _ _ ((isUnit_iff_isUnit_det _).2 hω.2)
    ((isUnit_iff_isUnit_det _).2 (isUnit_det_sub_hermitian hX hz))

/-- **Near resolvent.** On the good event, the near-near block of `ℝ_r` is
`passiveResolvent (pathX r) = (z - X_r)⁻¹`, and `z - X_r` is invertible. -/
theorem cec_nearResolvent (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {r : ℕ}
    {ω : GrowthPath W} (hω : cec_good E W r ω) :
    portBlock (boundaryResolvent b E W r ω) 0 0 = passiveResolvent b E (pathX b E W r ω) ∧
      IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - pathX b E W r ω).det := by
  have hX := cec_portSchur_isHermitian (E := E) (r := r) hω.1
  obtain ⟨h2, h3⟩ := portBlock_inv_zero hX (pfi_boundaryZ_im_pos hb hE1 hE2)
  rw [cec_boundaryResolvent_eq hb hE1 hE2 hω, h2, cec_pathX_eq]
  exact ⟨rfl, h3⟩

/-- **Boundary columns.** For an invertible full matrix, `(H - E)𝒰 + Cℝ = 0` and
`C*𝒰 + zℝ = I`. -/
theorem cec_column_eqs {r : ℕ} {ω : GrowthPath W} (hM : IsUnit (fullPathMatrix b E W r ω).det) :
    pfiInt E W r ω * boundaryToInterior b E W r ω +
        pfiCoup W r ω.2 * boundaryResolvent b E W r ω = 0 ∧
      (pfiCoup W r ω.2)ᴴ * boundaryToInterior b E W r ω +
        boundaryZ b E • boundaryResolvent b E W r ω = 1 := by
  have h : fullPathMatrix b E W r ω * fullInverse b E W r ω = 1 := mul_nonsing_inv _ hM
  have e := fromBlocks_toBlocks (fullInverse b E W r ω)
  rw [← e, fullPathMatrix_eq, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  refine ⟨h.2.1, ?_⟩
  have h4 := h.2.2.2
  rw [Matrix.smul_mul, Matrix.one_mul] at h4
  exact h4

end BlockBand.Endpoints
