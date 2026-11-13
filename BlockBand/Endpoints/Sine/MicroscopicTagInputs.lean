module

public import BlockBand.Endpoints.Sine.MicroscopicTagDefs

/-!
# Two inputs of the lead comparison: field identification and covariance closeness

This file states, as propositions, two inputs used in the proof of the lead comparison
`MicroscopicTagLeadComparison`: the identification of the Gaussian field with the ported field,
and the relative Loewner closeness of the stationary and fresh one-block covariances.

* `MicroscopicTagFieldIdentity` (the field identification, as in the proof of the physical lead
  profile theorem): the Gaussian field of covariance
  `Γ₀ = c|z₀ - Σ|⁻²` (`z₀ = commonZ b e`, `Σ = C*(H_R - e)⁻¹C = -F(e)`), lifted to the ring by
  `Lv = (v, -T(e)v)`, has, jointly in all `n` block clocks and after integrating the exterior
  prior, the law of `c` times the clocks of `(J𝒢₁₂ g, H g) = (U L g, H g)`, `U = JR` the
  matched-lead response of the old path of `r = n - 3` blocks (`leadResponse`), `L` the
  common-port transport (`commonPortL`, `X` = the old self-energy `leadSchur`), `H = 𝒢₂₂`
  (`commonPortH`) at the removed block, `g ~ CN(0, I_W)`. Ring positions: block `k` (the
  exposed block) carries `‖Hg‖²`, block `k + leadRingBlock y` carries the lead mass of `y`.
* `MicroscopicTagCovarianceCloseness` (covariance closeness): for `W` large, with probability at
  least `1 - ε` under the block prior, `(1 - ω₀)Γ₀ ≤ Γ_fresh ≤ (1 + ω₀)Γ₀` in the Loewner order,
  uniformly in `n ≤ TW`, the block `k` and `e ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.ClocksCommonPort BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder

/-!
## Vocabulary
-/

/-- The stationary one-block covariance `Γ₀ = c |z₀ - Σ(e)|⁻² = c ((z₀ - Σ)*(z₀ - Σ))⁻¹`,
`z₀ = commonZ b e = -e - ca` (`Im z₀ = cπρ(e)`), `Σ(e) = C*(H_R - e)⁻¹C = -F(e)`. -/
def mts_blockGamma0 (p : Parameters) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ) :
    Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  let X := commonZ p.b e • (1 : Matrix (BlockSite p k) (BlockSite p k) ℂ) + blockF p k ω e
  (p.c : ℂ) • (Xᴴ * X)⁻¹

/-- The ported law: the old path (`growthPathLaw`, read at length `r` by `pathAt`), the fresh
common-port layer and an independent `g ~ CN(0, I_W)` (all independent). -/
def mts_portLaw (W : ℕ) (b : ℝ) :
    Measure (GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ))) :=
  (growthPathLaw W b).prod (commonPortProbeLaw W b)

/-- The block clocks of the ported field `(ULg, Hg)` on the ring of `n` blocks, relative to the
removed block `0`: block `0` carries `‖Hg‖²`, block `leadRingBlock y` carries
`‖P_y U L g‖² = leadPositionMass … (Lg) y` (path of `r = n - 3` blocks, old self-energy
`X = leadSchur e W r ω`). -/
def mts_portBlockClock (b e : ℝ) (n W : ℕ)
    (y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ))) (j : ZMod n) : ℝ :=
  (if j.val = 0 then
      ∑ a : Fin W, ‖(commonPortH b e (leadSchur e W (n - 3) y.1) y.2.1 *ᵥ y.2.2) (0, a)‖ ^ 2
    else 0) +
    ∑ x : Fin (n - 3) ⊕ Fin 2, if leadRingBlock (n - 3) x = j.val then
      leadPositionMass b e W (n - 3) y.1 (commonPortProbe b e (leadSchur e W (n - 3) y.1) y.2) x
    else 0

/-!
## The Gaussian-field identification
-/

/-- **Gaussian-field identification** (from the proof of the physical lead profile theorem: the
absorbed-density identity identifies the Gaussian field with `(J𝒢₁₂g, Hg) = (JRLg, Hg)` up to
the common factor `√c`; proved from `LeadFieldIdentificationContract` as
`microscopicTagFieldIdentity_of_contract`). For every `p`, model, exposed block `k`, one-block
exterior law `Pω`, bulk energy `e ∈ (-2,2)`, every measurable `M₀` with `M₀M₀* = Γ₀` (all give
`M₀g ~ CN(0, Γ₀)`) and every bounded measurable `Ψ` of the `n` block clocks:
`E_{Pω} E_g Ψ((‖P_j L(e) M₀ g‖²)_j) = E_{ported} Ψ((c · clock_{j-k})_j)`.
-/
def MicroscopicTagFieldIdentity : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ e : ℝ, -2 < e → e < 2 →
    ∀ M₀ : BlockState p k → Matrix (BlockSite p k) (BlockSite p k) ℂ, Measurable M₀ →
      (∀ ω, M₀ ω * (M₀ ω)ᴴ = mts_blockGamma0 p k ω e) →
    ∀ Ψ : (ZMod p.n → ℝ) → ℝ, Measurable Ψ → (∃ C : ℝ, ∀ x, |Ψ x| ≤ C) →
      (∫ ω, ∫ g, Ψ (fun j => ∑ a : Fin p.W, ‖blockLift p k ω e (M₀ ω *ᵥ g) (j, a)‖ ^ 2)
          ∂circularVectorLaw (BlockSite p k) ∂Pω) =
        ∫ y, Ψ (fun j => p.c * mts_portBlockClock p.b e p.n p.W y (j - k))
          ∂mts_portLaw p.W p.b

/-!
## Relative Loewner closeness of the covariances
-/

/-- **Relative Loewner closeness of the covariances** (from the proof of the physical lead
profile theorem: the stationary scalar approximation changes the covariance to `c|z₀-Σ|⁻²` with
relative Loewner error `o(1)`; proved from `BlockRegularEventContract` as
`microscopicTagCovarianceStability_holds`). Fixed first `b`, the bulk range `bulkInterval κ`, `T`, the relative error `ω₀ > 0` and the
probability `ε > 0`; then for `W ≥ W₀`, `n ≤ TW`, every model, block, exterior law, reindexing
`σ` and `e ∈ bulkInterval κ`, outside (outer) `Pω`-probability `ε`:
`(1-ω₀)Γ₀ ⪯ Γ ⪯ (1+ω₀)Γ₀`, `Γ = freshGamma(blockDeformation σ ω e) c e`, `Γ₀` reindexed by `σ`
(the hypothesis form of `ClockCovarianceStabilityContract`).
-/
def MicroscopicTagCovarianceCloseness : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ ω₀ : ℝ, 0 < ω₀ → ∀ ε : ℝ, 0 < ε →
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))), ∀ e ∈ bulkInterval κ,
      Pω {ω | ¬ ((((1 + ω₀ : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockGamma0 p k ω e) -
            freshGamma (blockDeformation p k σ ω e) p.c e).PosSemidef ∧
          (freshGamma (blockDeformation p k σ ω e) p.c e -
            ((1 - ω₀ : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockGamma0 p k ω e)).PosSemidef)} ≤
        ENNReal.ofReal ε

end BlockBand.Endpoints
