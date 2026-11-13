module

public import BlockBand.SourceProcess.PhysApprox.B3JetFrac
public import BlockBand.SourceProcess.PhysApprox.B3Jet1Shift

/-!
# The common closing-shift estimate `ClosedJetShiftNbhdLp`

`ClosedJetShiftNbhdLp` asks that the closing-time shift of `W⁻¹Tr(w - X)⁻¹` be `O(1/W)` in every
`L^p`, uniformly for `|w - z_∂| ≤ r`. It is proved here from `ClosedShiftDiscTrace` and
`FarFracTraceMoments`, with `r = η/2`:

* **`closedJetShiftNbhdLp_of_frac`**: `ClosedShiftDiscTrace + FarFracTraceMoments ⇒
  ClosedJetShiftNbhdLp` (the dominating function of `closedShiftDisc_dominated` is uniform in
  `w`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Topology Matrix Set Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.Jet1
open scoped ENNReal

theorem nearTraceAt_eq_stieltjes (W : ℕ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    nearTraceAt W w X = stieltjes X w := rfl

/-- **`ClosedJetShiftNbhdLp`** (the common shift estimate) from the cavity-kernel bound on the
boundary disc and the fractional transmission moments, with radius `η/2`. -/
theorem closedJetShiftNbhdLp_of_frac (hA : ClosedShiftDiscTrace) (hB : FarFracTraceMoments) :
    ClosedJetShiftNbhdLp := by
  intro b E np τ m T s h K Vs hF p hp
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -⟩ := id hF
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  have hη : 0 < etaZ b E := lt_of_lt_of_le (etaLow_pos (by linarith : b < 1) hκ)
    (etaLow_le (by linarith : b < 1) hκ hEb)
  obtain ⟨C, hC0, hC⟩ := closedShiftDisc_dominated hA hB b E np τ m T s h K Vs hF p hp
  have hp0 : 0 < p := by linarith
  refine ⟨etaZ b E / 2, C, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 w hw
  obtain ⟨B, hB0, hdom, hint⟩ := hW
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW1
  set n := closeLen s W
  set f : ProbedPath W np × ℝ → ℝ := fun y =>
    ‖stieltjes (b3ClosedX b E s h τ m W n y) w - stieltjes (pathX b E W n y.1.1) w‖ with hfdef
  have hfm : Measurable f :=
    ((measurable_stieltjes_joint.comp ((measurable_b3ClosedX b E s h τ m n).prodMk
      measurable_const)).sub (measurable_stieltjes_joint.comp
        (((measurable_pathX b E n).comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_const))).norm
  have hw' : ‖w - boundaryZ b E‖ ≤ etaZ b E / 2 := by
    rwa [mem_closedBall, dist_eq_norm] at hw
  have hle : ∀ᵐ y ∂closedLaw b W np, ‖f y‖ₑ ^ p ≤ ENNReal.ofReal (B y ^ p) := by
    filter_upwards [hdom] with y hy
    have h1 : f y ≤ B y := hy w hw'
    rw [Real.enorm_eq_ofReal (norm_nonneg _), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      hp0.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    hfm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ y, ‖f y‖ₑ ^ p ∂closedLaw b W np) ^ (1 / p)
      ≤ (ENNReal.ofReal ((C / W) ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow ((lintegral_mono_ae hle).trans hint) (by positivity)
    _ = ENNReal.ofReal (C / W) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
          Real.rpow_rpow_inv (by positivity) hp0.ne']

end BlockBand.SourceProcess.PhysApprox.B3.Jet
