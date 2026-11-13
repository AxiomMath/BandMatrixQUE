module

public import BlockBand.Transmission.LawForced.Discrete
public import BlockBand.Transmission.LawForced.RatioBulk
public import BlockBand.Transmission.Generator.DriftCond
public import BlockBand.Transmission.Bridge.TransportFull

/-!
# The `κ ≡ 0` ratio drift error as a one-layer bracket, a.s.

* `freshRatio` (`F_z` of the clamped trace measure after one fresh layer; measurable, in `(0,1]`,
  so `condExp_fresh` needs no further clamp);
* **`ratioDriftError_zero_ae`**: for `r ≥ 1`, a.s.
  `ratioDriftError b E 0 W z r = ∫F_z(T(freshSchur X_r y)) dy − F_z(T(X_r)) −
  ratioDrift D₀ E 0 (r/W) z μ_{T(X_r)}/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory ProbabilityTheory Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.Bridge
open scoped ComplexOrder

variable {p W : ℕ}

theorem isAbsorptionProfile_zero' : IsAbsorptionProfile (fun _ => (0 : ℝ)) :=
  ⟨continuous_const, fun _ => le_rfl, 0, fun _ => le_rfl⟩

/-- `F_z` of the clamped trace measure after one fresh layer. -/
def freshRatio (b E : ℝ) (z : DualCoord p)
    (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) : ℝ :=
  transmissionRatio z.1 z.2
    (clampedTraceMeasure (passiveTransmission b E (freshSchur E x.1 x.2)))

theorem measurable_passiveTransmission (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveTransmission b E X := by
  have hc : Continuous fun Q : Matrix (Fin W) (Fin W) ℂ => (((4 * etaZ b E : ℝ)) : ℂ) • Q :=
    continuous_const_smul _
  exact hc.measurable.comp (SourceMixing.mu_measurable_passiveQ b E)

theorem measurable_freshRatio {z : DualCoord p} (hz : z ∈ dualChamber p) (b E : ℝ) :
    Measurable (freshRatio (W := W) b E z) :=
  (continuous_ratio_nu hz).measurable.comp (measurable_clampedTraceMeasure.comp
    ((measurable_passiveTransmission b E).comp (SourceMixing.measurable_freshSchur_prod E)))

theorem clamped_passive {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    clampedTraceMeasure (passiveTransmission b E X) = traceMeasure (passiveTransmission b E X) := by
  rw [clampedTraceMeasure, ite_eq_left ⟨passiveTransmission_posSemidef hb h1 h2 hX,
    one_sub_passiveTransmission_posSemidef b E X⟩]

/-- **The `κ ≡ 0` ratio drift error is the one-layer bracket at `X_r`**, a.s. (`r ≥ 1`). -/
theorem ratioDriftError_zero_ae {z : DualCoord p} (hz : z ∈ dualChamber p) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W) {r : ℕ}
    (hr : 1 ≤ r) :
    ratioDriftError b E (fun _ => 0) W z r =ᵐ[growthPathLaw W b] fun ω =>
      ∫ y, transmissionRatio z.1 z.2
          (traceMeasure (passiveTransmission b E (freshSchur E (pathX b E W r ω) y)))
          ∂freshLaw W b -
        transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E (pathX b E W r ω))) -
        ratioDrift (transportD0 b E) E (fun _ => 0) ((r : ℝ) / W) z
          (traceMeasure (passiveTransmission b E (pathX b E W r ω))) / W := by
  set μ := growthPathLaw W b
  have hκ := isAbsorptionProfile_zero'
  have hb1 : b < 1 := by linarith
  have hzr := IsRatioParameter.isRatioRange hz
  have hI1 := integrable_ratioAt hκ hb1 h1 h2 hz (W := W) (r + 1)
  have hI0 := integrable_ratioAt hκ hb1 h1 h2 hz (W := W) r
  have hsub := condExp_sub hI1 hI0 (growthSigma W r) (μ := μ)
  -- the `𝓕_r`-measurable term
  have hm0 : Measurable[growthSigma W r] fun ω =>
      transmissionRatio z.1 z.2 (stateAt b E (fun _ => 0) W r ω) :=
    (continuous_ratio_nu hz).measurable.comp (measurable_stateAt b E _ r)
  have hc0 : μ[ratioAt b E (fun _ => 0) W r z | growthSigma W r] =ᵐ[μ]
      ratioAt b E (fun _ => 0) W r z := by
    refine (condExp_congr_ae (ratioAt_ae_eq hκ hb1 h1 h2 r)).trans ?_
    rw [condExp_of_stronglyMeasurable (growthSigma_le W r) hm0.stronglyMeasurable
      (hI0.congr (ratioAt_ae_eq hκ hb1 h1 h2 r))]
    exact (ratioAt_ae_eq hκ hb1 h1 h2 r).symm
  -- the fresh layer
  have hae : ratioAt b E (fun _ => 0) W (r + 1) z =ᵐ[μ]
      fun ω => freshRatio b E z (pathX b E W r ω, freshSample W r ω) := by
    filter_upwards [Bridge.ae_pathX_succ hb h1 h2 hW, ae_stateAt_eq hκ.2.1 hb1 h1 h2]
      with ω hω hst
    have e1 := hst (r + 1)
    rw [ratioAt, ← e1, stateAt, freshRatio]
    show transmissionRatio z.1 z.2 (clampedTraceMeasure
      (passiveTransmission b E (pathX b E W (r + 1) ω))) = _
    rw [hω r hr]
  have hc1 : μ[ratioAt b E (fun _ => 0) W (r + 1) z | growthSigma W r] =ᵐ[μ]
      fun ω => ∫ y, freshRatio b E z (pathX b E W r ω, y) ∂freshLaw W b :=
    (condExp_congr_ae hae).trans (condExp_fresh b E (measurable_freshRatio hz b E) (M := 1)
      (fun x => by
        have h := transmissionRatio_mem_vec hzr
          (clampedTraceMeasure (passiveTransmission b E (freshSchur E x.1 x.2)))
        rw [freshRatio, abs_of_pos h.1]; exact h.2) r)
  filter_upwards [hsub, hc0, hc1, SourceMixing.mm_ae_passive (W := W) hb1 h1 h2 r]
    with ω e1 e2 e3 hX
  show (μ[fun ω => ratioAt b E (fun _ => 0) W (r + 1) z ω - ratioAt b E (fun _ => 0) W r z ω |
    growthSigma W r] - fun ω => ratioDriftAt b E (fun _ => 0) W r z ω / W) ω = _
  rw [Pi.sub_apply]
  have e1' : μ[fun ω => ratioAt b E (fun _ => 0) W (r + 1) z ω - ratioAt b E (fun _ => 0) W r z ω |
      growthSigma W r] ω = (μ[ratioAt b E (fun _ => 0) W (r + 1) z | growthSigma W r] -
        μ[ratioAt b E (fun _ => 0) W r z | growthSigma W r]) ω := e1
  rw [e1', Pi.sub_apply, e2, e3]
  have hint : ∫ y, freshRatio b E z (pathX b E W r ω, y) ∂freshLaw W b =
      ∫ y, transmissionRatio z.1 z.2
        (traceMeasure (passiveTransmission b E (freshSchur E (pathX b E W r ω) y)))
        ∂freshLaw W b := by
    refine integral_congr_ae ?_
    filter_upwards [PassiveLayer.ae_good W hb0 hW] with y hy
    rw [freshRatio, clamped_passive hb1 h1 h2 (PathScalar.passiveY_freshSchur E hX y hy.1)]
  rw [hint]
  rfl

end BlockBand.Transmission.LawForced
