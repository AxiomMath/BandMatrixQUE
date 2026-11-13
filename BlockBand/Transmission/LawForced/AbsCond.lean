module

public import BlockBand.Transmission.LawForced.RatioCond
public import BlockBand.Transmission.Absorbed.ModulusCond

/-!
# The absorbed ratio drift error as a one-layer bracket at `X − iε`, a.s.

Conditionally on the past, the drift error of the ratio `F_z` along the absorbed path is almost
surely the one-layer bracket of a fresh layer at the absorbed input `X_r − iε_r`
(`ratioDriftError_abs_ae`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar BlockBand.Transmission.LawFinite
open scoped ComplexOrder

variable {p W : ℕ}

/-- `F_z` of the clamped trace measure after one fresh layer at the absorbed input. -/
def freshRatioAbs (b E ε : ℝ) (z : DualCoord p)
    (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) : ℝ :=
  freshRatio b E z (absorbedInput x.1 ε, x.2)

theorem measurable_freshRatioAbs {z : DualCoord p} (hz : z ∈ dualChamber p) (b E ε : ℝ) :
    Measurable (freshRatioAbs (W := W) b E ε z) := by
  have hc : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => absorbedInput X ε :=
    continuous_id.sub continuous_const
  exact (measurable_freshRatio hz b E).comp ((hc.measurable.comp measurable_fst).prodMk
    measurable_snd)

/-- **The absorbed ratio drift error is the one-layer bracket at `X_r − iε_r`**, a.s. -/
theorem ratioDriftError_abs_ae {z : DualCoord p} (hz : z ∈ dualChamber p) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) {r : ℕ} (hr : 1 ≤ r) :
    ratioDriftError b E κ W z r =ᵐ[growthPathLaw W b] fun ω =>
      ∫ y, transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E
          (freshSchur E (absorbedInput (pathNearSchur b E κ W r ω)
            (layerAbsorption W κ (r + 1) 0)) y))) ∂freshLaw W b -
        transmissionRatio z.1 z.2
          (traceMeasure (passiveTransmission b E (pathNearSchur b E κ W r ω))) -
        ratioDrift (transportD0 b E) E κ ((r : ℝ) / W) z
          (traceMeasure (passiveTransmission b E (pathNearSchur b E κ W r ω))) / W := by
  set μ := growthPathLaw W b
  set ε := layerAbsorption W κ (r + 1) 0
  have hε : 0 ≤ ε := div_nonneg (hκ.2.1 _) (sq_nonneg _)
  have hb1 : b < 1 := by linarith
  have hzr := IsRatioParameter.isRatioRange hz
  have hI1 := integrable_ratioAt hκ hb1 h1 h2 hz (W := W) (r + 1)
  have hI0 := integrable_ratioAt hκ hb1 h1 h2 hz (W := W) r
  have hsub := condExp_sub hI1 hI0 (growthSigma W r) (μ := μ)
  have hm0 : Measurable[growthSigma W r] fun ω =>
      transmissionRatio z.1 z.2 (stateAt b E κ W r ω) :=
    (continuous_ratio_nu hz).measurable.comp (measurable_stateAt b E _ r)
  have hc0 : μ[ratioAt b E κ W r z | growthSigma W r] =ᵐ[μ] ratioAt b E κ W r z := by
    refine (condExp_congr_ae (ratioAt_ae_eq hκ hb1 h1 h2 r)).trans ?_
    rw [condExp_of_stronglyMeasurable (growthSigma_le W r) hm0.stronglyMeasurable
      (hI0.congr (ratioAt_ae_eq hκ hb1 h1 h2 r))]
    exact (ratioAt_ae_eq hκ hb1 h1 h2 r).symm
  have hae : ratioAt b E κ W (r + 1) z =ᵐ[μ]
      fun ω => freshRatioAbs b E ε z (pastX b E κ W r (pastCoords W r ω), freshSample W r ω) := by
    filter_upwards [ae_pathNearSchur_succ_abs (W := W) (b := b) hb h1 h2 hW hκ.2.1,
      ae_stateAt_eq hκ.2.1 hb1 h1 h2] with ω hω hst
    have e1 := hst (r + 1)
    rw [ratioAt, ← e1, stateAt, freshRatioAbs, freshRatio, ← pathNearSchur_eq_past]
    show transmissionRatio z.1 z.2 (clampedTraceMeasure
      (passiveTransmission b E (pathNearSchur b E κ W (r + 1) ω))) = _
    rw [hω r hr]
    rfl
  have hc1 : μ[ratioAt b E κ W (r + 1) z | growthSigma W r] =ᵐ[μ]
      fun ω => ∫ y, freshRatioAbs b E ε z (pastX b E κ W r (pastCoords W r ω), y)
        ∂freshLaw W b :=
    (condExp_congr_ae hae).trans (Absorbed.condExp_fresh_past b (measurable_pastX b E κ r)
      (measurable_freshRatioAbs hz b E ε) (M := 1) (fun x => by
        have h := transmissionRatio_mem_vec hzr (clampedTraceMeasure
          (passiveTransmission b E (freshSchur E (absorbedInput x.1 ε) x.2)))
        rw [freshRatioAbs, freshRatio, abs_of_pos h.1]; exact h.2))
  filter_upwards [hsub, hc0, hc1, ae_passiveSample W hκ.2.1 hb1 h1 h2] with ω e1 e2 e3 hP
  have hX := pathNearSchur_passive hP r
  show (μ[fun ω => ratioAt b E κ W (r + 1) z ω - ratioAt b E κ W r z ω |
    growthSigma W r] - fun ω => ratioDriftAt b E κ W r z ω / W) ω = _
  rw [Pi.sub_apply]
  have e1' : μ[fun ω => ratioAt b E κ W (r + 1) z ω - ratioAt b E κ W r z ω |
      growthSigma W r] ω = (μ[ratioAt b E κ W (r + 1) z | growthSigma W r] -
        μ[ratioAt b E κ W r z | growthSigma W r]) ω := e1
  rw [e1', Pi.sub_apply, e2, e3, ← pathNearSchur_eq_past]
  have hint : ∫ y, freshRatioAbs b E ε z (pathNearSchur b E κ W r ω, y) ∂freshLaw W b =
      ∫ y, transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E
        (freshSchur E (absorbedInput (pathNearSchur b E κ W r ω) ε) y))) ∂freshLaw W b := by
    refine integral_congr_ae ?_
    filter_upwards [PassiveLayer.ae_good W hb0 hW] with y hy
    rw [freshRatioAbs, freshRatio, clamped_passive hb1 h1 h2
      (PathScalar.passiveY_freshSchur E (passiveY_absorbedInput hX hε) y hy.1)]
  rw [hint]
  rfl

end BlockBand.Transmission.LawForced
