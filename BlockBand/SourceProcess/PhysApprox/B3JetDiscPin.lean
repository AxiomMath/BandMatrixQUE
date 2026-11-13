module

public import BlockBand.SourceProcess.PhysApprox.B3JetWood
public import BlockBand.SourceProcess.PhysApprox.B3JetOrder

/-!
# `ClosedShiftDiscTrace` and the closed jets from the fractional moments

* **`closedShiftDiscTrace_holds`**: a.e. under `closedLaw`, at the closing time, for every
  `|w - z_∂| ≤ η/2`, `|W⁻¹Tr(w - X_cl)⁻¹ - W⁻¹Tr(w - X_open)⁻¹| ≤ 2(ηW)⁻¹ Σ_k κ(t_k, z)`
  (`closedShift_factor` and `stieltjes_sub_le_of_factor`; the a.s. invertibilities of
  the closed path; the phase `z = e^{iθ}`, `θ ∈ (0, 2π)`);
* consequences with the single further hypothesis `FarFracTraceMoments`:
  `closedJetShiftNbhdLp_of_fracMoments`, `closedJet0Fam_of_fracMoments`,
  `closedJetL4Fam_b3ClosedX_of_fracMomentsAt` (order `p = 4` only).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open scoped ComplexOrder

/-- **`ClosedShiftDiscTrace` holds.** -/
theorem closedShiftDiscTrace_holds : ClosedShiftDiscTrace := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, -, -, hh0, hh1, -⟩ := id hF
  have hh : h ^ 2 < 1 := by nlinarith
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [eventually_ge_atTop 1] with W hW1
  set n := closeLen s W
  have hph : ∀ᵐ y ∂closedLaw b W np, y.2 ∈ Ioo 0 (2 * Real.pi) := by
    rw [ae_iff]
    have : {y : ProbedPath W np × ℝ | ¬ y.2 ∈ Ioo 0 (2 * Real.pi)} =
        Set.univ ×ˢ {θ | ¬ θ ∈ Ioo 0 (2 * Real.pi)} := by ext y; simp
    rw [this, Measure.prod_prod, ← ae_iff.1 ae_phaseLaw_mem_Ioo, mul_comm]
    simp
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW1,
    ae_closedPhase_good (W := W) (np := np) b E s h n,
    ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW1 n, hph]
    with y hP hQ hX hθ w hw
  obtain ⟨hA, hFp, -, hS⟩ := hP
  obtain ⟨hU, -, -, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s n y.1.1 hA hη (hFp n)).ne_zero
  obtain ⟨P, Q, d, hD, hk⟩ := closedShift_factor b E s h hh y.1.1 (norm_phase y.2)
    (phase_ne_one hθ) hA hη (hFp n) (hS n) (isUnit_iff_ne_zero.2 hU) (isUnit_iff_ne_zero.2 hR)
  have ho : (passiveY (pathX b E W n y.1.1)).PosSemidef :=
    pathNearSchur_passive (κ := fun _ => 0) ⟨hA, fun _ => le_rfl, hη⟩ n
  have hmain := stieltjes_sub_le_of_factor hb0 hb hE1 hE2 hX ho hw hD hk
  rw [nearTraceAt_eq_stieltjes, nearTraceAt_eq_stieltjes]
  refine hmain.trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  have hη' : etaZ b E ≠ 0 := hη.ne'
  field_simp
  ring

/-- **`ClosedJetShiftNbhdLp`** from the fractional moments. -/
theorem closedJetShiftNbhdLp_of_fracMoments (hB : FarFracTraceMoments) :
    BlockBand.SourceProcess.PhysApprox.B3.Jet1.ClosedJetShiftNbhdLp :=
  closedJetShiftNbhdLp_of_frac closedShiftDiscTrace_holds hB

/-- **`ClosedJet0Fam`** from the contract hypotheses and the fractional moments. -/
theorem closedJet0Fam_of_fracMoments (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hB : FarFracTraceMoments) :
    ClosedJet0Fam :=
  closedJet0Fam_of_disc hMT hGA hLp closedShiftDiscTrace_holds hB

/-- **`ClosedJetL4Fam b3ClosedX`** from the contract hypotheses and the fractional moments at
`p = 4`. -/
theorem closedJetL4Fam_b3ClosedX_of_fracMomentsAt (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hB : FarFracTraceMomentsAt 4) : ClosedJetL4Fam b3ClosedX :=
  closedJetL4Fam_b3ClosedX_of_fracAt hMT hGA hLp closedShiftDiscTrace_holds hB

end BlockBand.SourceProcess.PhysApprox.B3.Jet
