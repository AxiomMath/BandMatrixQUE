module

public import BlockBand.Transmission.LawForced.RatioBrL
public import BlockBand.Transmission.Generator.StepLayer

/-!
# The `κ ≡ 0` one-layer `F_z` drift at a deterministic passive input

**`ratio_layer_point`**: one fresh layer at a deterministic passive `X`, all inputs explicit
(the analogue of `layer_point` for `F_z`). With `T = T(X)`, `g = Re Tr T`,
`a = D₀/(2W)`, `f = passiveF`, `τ = layerTau`, `hs = hs(T,f)`, given
* entry integrability of `U = LL*` and `‖U‖² ∈ L¹`,
* `M³ + M⁹ ∈ L¹` (`M = ratioMf`),
* a covariance bound of exactly the `PassiveCovarianceBulk` shape (jet value `σ₋`, error `ε`),
* `‖Ū − c‖ ≤ U_a` and `‖Tr(GŪ) − c·Tr G‖ ≤ L_w` at `G = gW hT Λ` (`ubarMean_bulk`),
`|E F_z(T(X₊)) − F_z(T) − ratioDrift D₀ E 0 u z μ_T / W| ≤
  441(1+quadK+cubK)³E(M³+M⁹) + ratioBrBd z g (ag) L_w U_a ε (2|σ₋|/W) τ hs`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {p W : ℕ}

theorem ratioBrBd_mono_Lw (z : DualCoord p) (hz : IsRatioRange z.1 z.2) {g y Lw Lw' : ℝ}
    (hg : 0 ≤ g) (hy : 0 ≤ y) (h0 : 0 ≤ Lw') (h : Lw' ≤ Lw) (Ua ε S τ hs : ℝ) :
    ratioBrBd z g y Lw' Ua ε S τ hs ≤ ratioBrBd z g y Lw Ua ε S τ hs := by
  have := lamHat_nonneg hz
  unfold ratioBrBd
  gcongr

/-- **The `κ ≡ 0` one-layer `F_z` drift** (all inputs explicit). -/
theorem ratio_layer_point {z : DualCoord p} (hz : z ∈ dualChamber p) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hW : 1 ≤ W) (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) (hT : (passiveTransmission b E X).PosSemidef)
    (hUi : ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b))
    (hU2 : Integrable (fun ω => ‖freshU b E X ω‖ ^ 2) (freshLaw W b))
    (hM : Integrable (fun ω => ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 3 +
      ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 9) (freshLaw W b))
    (σm : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance (freshLaw W b) (freshU b E X)
        v₁ v₂ v₃ v₄ - ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
          (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X) +
            crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1) +
          σm / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X) +
          conj σm / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ)‖ ≤
        ε * fourNorm v₁ v₂ v₃ v₄)
    {Ua Lw : ℝ} (hUa : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      ((meanC b E X : ℝ) : ℂ) • 1‖ ≤ Ua)
    (hLw : ‖((gW hT fun k => dualLam z (ts_lam hT k)) *
        matrixExpect (freshLaw W b) (freshU b E X)).trace -
      ((meanC b E X : ℝ) : ℂ) * (gW hT fun k => dualLam z (ts_lam hT k)).trace‖ ≤ Lw)
    (u : ℝ) :
    |∫ ω, transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E (freshSchur E X ω)))
        ∂freshLaw W b - transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) -
        ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E X)) / W| ≤
      441 * (1 + quadK z + cubK z) ^ 3 *
          ∫ ω, (ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 3 +
            ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 9) ∂freshLaw W b +
        ratioBrBd z (passiveTransmission b E X).trace.re
          (transportD0 b E / (2 * W) * (passiveTransmission b E X).trace.re) Lw Ua ε
          (‖σm / W‖ + ‖conj σm / W‖) (layerTau b E X)
          (hsSandwich (passiveTransmission b E X) (passiveF b E X)) := by
  have hzr : IsRatioRange z.1 z.2 := IsRatioParameter.isRatioRange hz
  have h1T := one_sub_passiveTransmission_posSemidef b E X
  have ht1 := ts_lam_le_one hT h1T
  have hD0 : 0 ≤ transportD0 b E := by
    have : 0 < 4 - E ^ 2 := by nlinarith
    unfold transportD0; positivity
  have ha : 0 ≤ transportD0 b E / (2 * W) := by positivity
  have hg0 : 0 ≤ (passiveTransmission b E X).trace.re := by
    rw [← ts_sum_lam hT]; exact Finset.sum_nonneg fun k _ => ts_lam_nonneg hT k
  have hc : meanC b E X = (1 + transportD0 b E / (2 * W) *
      (passiveTransmission b E X).trace.re)⁻¹ := by
    rw [meanC_eq hb0 hb h1 h2]; ring_nf
  have hsplit := ratio_layer_split hz hb0 hb hW h1 h2 hX hT hUi hU2 hM u
  rw [hc] at hUa hLw
  have hbr := ratioBr_le hzr hT ht1 (freshU b E X) (passiveF b E X) ha (σm / W) (conj σm / W)
    hcov hUa
  have hmono := ratioBrBd_mono_Lw z hzr hg0 (mul_nonneg ha hg0) (norm_nonneg _) hLw Ua ε
    (‖σm / W‖ + ‖conj σm / W‖) (layerTau b E X)
    (hsSandwich (passiveTransmission b E X) (passiveF b E X))
  have e : layerTau b E X = ‖(passiveTransmission b E X * passiveF b E X).trace‖ +
      Real.sqrt (passiveTransmission b E X).trace.re *
        hsSandwich (passiveTransmission b E X) (passiveF b E X) := rfl
  rw [e] at hmono ⊢
  linarith

end BlockBand.Transmission.LawForced
