module

public import BlockBand.SourceProcess.ComplexCoupled.Ext
public import BlockBand.SourceProcess.ComplexCoupled.Frame
public import BlockBand.SourceProcess.ComplexConstruct.Model
public import BlockBand.SourceProcess.ComplexConstruct.KAmbHolds
public import BlockBand.SourceProcess.ComplexCutoff.Pin

/-!
# One born frame carries a complex finite source model

`frame_complex`: under `FrameHyp` (one frame of the coupled-frames construction, deterministic
births), with the entrance law of the transmission sequence `tq` given, there is an Itô
process `𝒴ᵇ` with zero drift and diffusion `kNoise(X)` (`X` the born frame) such that
`(gramPair P X, kProc … 𝒴ᵇ)` is a complex finite source model at cutoff `h`. The ambient integral
`𝒴` is `ambientKIntegral_holds` at the ambient solution `Y` (it applies to every solution on one
driver space, hence to each frame of the coupling); `𝒴ᵇ = kBorn θ λ 𝒴`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.ComplexUnique BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.CoupledFrames
open BlockBand.SourceProcess.ComplexCutoff
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {K R np : ℕ}
  {b E s h : ℝ} {τ m : Fin np → ℝ} {tq : Dr S K R → ℕ → ℝ}
  {Y : ℝ≥0 → Dr S K R → Matrix (Amb K R) (ExtCol K R) ℂ}
  {pv : Fin np → Dr S K R → ExtCol K R → ℂ} {w : Fin np → Dr S K R → Amb K R → ℂ}

/-- **One born frame carries a complex finite source model.** -/
theorem frame_complex (H : FrameHyp b E s h τ m μ tq Y pv w) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hm : ∀ j, 0 ≤ m j) (hsτ : ∀ j, s < τ j)
    {entrance : Measure (Measure unitInterval)}
    (hlaw : (driverLaw (κ := SourceNoise (Amb K R)) μ).map (fun x => seqTraceMeasure (tq x)) =
      entrance) :
    ∃ Yb : ℝ≥0 → Dr S K R → Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ,
      IsNativeItoProcess μ Yb (fun _ _ => 0)
        (fun a t x => kNoise (transportD0 b E) (etaZ b E) (ambP K R) (srcSignature K (Fin np)) a
          (bFr s τ Y pv w t x)) ∧
      IsFiniteComplexSourceModel b E s τ m h K entrance
        (driverAugmented (κ := SourceNoise (Amb K R)) μ) (driverLaw (κ := SourceNoise (Amb K R)) μ)
        tq (fun t x => gramPair (ambP K R) (bFr s τ Y pv w t x)) (kProc E s τ m Yb) := by
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hξm := stronglyMeasurable_extFrame (R := R) H.tq_meas h
  have hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      TwoProjection (ambP K R) (extSig K R) (extFrame K R (tq x) h) :=
    H.tq_seq.mono fun x hx => twoProjection_extFrame K R (fun k => hx.2.1 k) h
  obtain ⟨𝒴, h𝒴, -⟩ := ambientKIntegral_holds b E hb0 hb1 hE1 hE2 S μ (Amb K R) (ExtCol K R)
    (K + R) (ambP K R) (extSig K R) (isNearProjection_ambP K R) (isSignature_extSig K R) _ hξm
    hξc Y H.sol
  obtain ⟨hG, heq, h0⟩ := gram_model H hb0 hb1 hE1 hE2 hm hsτ
  have hXp := isStronglyProgressive_bornFrame (Equiv.refl (Fin np)) H.sol (measurable_sigD s τ)
    H.pv_meas H.w_meas
  have hj : ∀ f, 0 ≤ ((probeJump (K := K) (fun j => dStar b * m j) f).1.trace).re := fun f => by
    simp [probeJump, mul_nonneg (dStar_pos hb1).le (hm f)]
  have hc𝒢 : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      Continuous fun t => gramPair (ambP K R) (Y t x) :=
    H.sol.1.continuous.mono fun x hx => (continuous_gramPair _).comp hx
  have hrep : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ e t,
      bornCompensated (transportD0 b E) (srcSignature K (Fin np))
        (fun t x => gramPair (ambP K R) (bFr s τ Y pv w t x))
        (bJ (probeJump (K := K) fun j => dStar b * m j) (sigD s τ)) e t x =
      bornRep (mθ K (sigD s τ)) (glam K R pv) (gramCompensated (transportD0 b E) (extSig K R)
        (fun t x => gramPair (ambP K R) (Y t x))) e t x := by
    filter_upwards [heq, H.rep, hc𝒢] with x he hr hc e t
    rw [bornCompensated_congr he]
    exact bornCompensated_eq_bornRep (fun t x => bornL_sig_probe t x) hr hc e t
  have hext := complexExt_born hb0 hE1 hE2 (isNearProjection_ambP K R) (isSignature_extSig K R)
    hξm hξc H.sol h𝒴 H.theta_meas H.glam_meas (fun t x => bornL_sig_probe t x) hXp H.eq_mul hj
    (measurable_sigD s τ) hG hrep (fun t => kBirthJump E (fun j => τ j - s) m (t : ℝ))
  refine ⟨kBorn (mθ K (sigD s τ)) (glam K R pv) 𝒴,
    isNativeItoProcess_kBorn h𝒴 H.theta_meas H.glam_meas (fun t x => bornL_sig_probe t x) hXp
      H.eq_mul, ?_⟩
  exact
    { prob := inferInstance
      entrance_measurable := H.tq_meas
      entrance_sequence := H.tq_seq
      entrance_law := hlaw
      initial := h0.mono fun x hx => ⟨hx, by
        simp only [kProc, sub_self]
        rw [kBirthJump_zero hsτ]
        ext i k; simp [probeBlock]⟩
      solution := hG
      complex := hext }

end BlockBand.SourceProcess.ComplexCoupled
