module

public import BlockBand.SourceProcess.ClosingLeak.Samples

/-!
# The expected leaked mass of one injection: `E leakTerm_{il} = (2/M) E Tr(A_- Q(q_i))`

Fix `0 < h < 1`. For all large `W`, Tonelli over `(path, samples, phase)`, the phase average
(`lintegral_phase_leak`, on the almost sure set of `closedReflection_holds` and
`ae_phaseAvg_physClosingDefect`) and the sample average (`lintegral_sample_leak`) give

`∫⁻ leakTerm_{il} = ∫⁻_ω (2/M) Re Tr(farEmbed(A_-(s)) Q(q_i)(T))` (`eventually_lintegral_leakTerm`).

This is the Gaussian closing error combined with `E_samples \widehat Q = Q(q)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.Sampling BlockBand.SourceProcess.ClosingAux
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open scoped ComplexOrder

variable {W : ℕ}

theorem measurable_sampVec (b E : ℝ) (n : ℕ) {p M : ℕ} (il : Fin p × Fin M) :
    Measurable fun x : SampledPath W p M => sampVec b E n x il := by
  have hU : Measurable fun x : SampledPath W p M => boundaryToInterior b E W n x.1 :=
    (Measurable.of_eval_matrix _ fun _ _ => (measurable_fullInverse b E n).eval_matrix).comp
      measurable_fst
  have hg : Measurable fun x : SampledPath W p M => (x.2.1 il, x.2.2 il) :=
    ((measurable_pi_apply il).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply il).comp (measurable_snd.comp measurable_snd))
  have ht : Measurable fun x : SampledPath W p M => tagVector W n (x.2.1 il) (x.2.2 il) :=
    (measurable_tagVector_pair W n).comp hg
  refine Measurable.of_eval fun c => ?_
  simp only [sampVec, mulVec, dotProduct, conjTranspose_apply, Complex.star_def]
  exact Finset.measurable_sum _ fun z _ =>
    (Complex.continuous_conj.measurable.comp hU.eval_matrix).mul (ht.eval)

theorem measurable_rankOne_sample (b E : ℝ) (n : ℕ) {p M : ℕ} (κ : ℝ) (il : Fin p × Fin M) :
    Measurable fun x : SampledPath W p M =>
      rankOne (boundaryToInterior b E W n x.1) κ (x.2.1 il, x.2.2 il) := by
  have hv := measurable_sampVec (W := W) b E n il
  refine Measurable.of_eval_matrix _ fun c d => ?_
  simp only [rankOne, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, Complex.star_def,
    smul_eq_mul]
  exact measurable_const.mul ((hv.eval (a := c)).mul
    (Complex.continuous_conj.measurable.comp (hv.eval (a := d))))

theorem measurable_leakTerm (b E s T h : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (M W : ℕ)
    (il : Fin p × Fin M) : Measurable (leakTerm b E s T h q M W il) := by
  have hC : Measurable fun y : SampledPath W p M × ℝ =>
      physClosingMap b E s T h W y.1.1 (phase y.2) :=
    measurable_physClosingMap_comp b E s T h (measurable_fst.comp measurable_fst) measurable_snd
  have hD : Measurable fun y : SampledPath W p M × ℝ => closeDefect b E s T h y :=
    measurable_matrix_sub hC measurable_const
  exact measurable_trace_re (measurable_matrix_mul' (measurable_matrix_mul' hD
    (measurable_matrix_conjTranspose' hD))
    ((measurable_rankOne_sample b E _ _ il).comp measurable_fst))

/-- `farEmbed(A_-)` is an orthogonal projection, hence positive semidefinite. -/
theorem farEmbed_omittedProj_eq (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    (farEmbed (omittedProj b E h W n ω))ᴴ * farEmbed (omittedProj b E h W n ω) =
      farEmbed (omittedProj b E h W n ω) := by
  rw [farEmbed_conjTranspose, omittedProj_conjTranspose, farEmbed_mul, omittedProj_mul_self]

theorem farEmbed_omittedProj_psd (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    (farEmbed (omittedProj b E h W n ω)).PosSemidef := by
  rw [← farEmbed_omittedProj_eq]; exact posSemidef_conjTranspose_mul_self _

/-- The phase-and-sample average on one good path. -/
theorem lintegral_leak_path {b E s T h : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {M : ℕ} (hM : 0 < M) (hW0 : 0 < W) (il : Fin p × Fin M)
    {ω : GrowthPath W}
    (hN : Tendsto (fun n => closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
        (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
        (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) ^ n) atTop (𝓝 0))
    (hD : phaseAvg (fun θ => (physClosingMap b E s T h W ω (phase θ) - 1) *
          (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω)) :
    ∫⁻ z, ∫⁻ θ, ENNReal.ofReal (leakTerm b E s T h q M W il ((ω, z), θ)) ∂phaseLaw
        ∂((Measure.pi fun i : Fin p × Fin M => tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q i.1)).prod
          (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))) =
      ENNReal.ofReal (2 / M * (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
          intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q il.1) ω).trace.re) := by
  have hκ : 0 ≤ gridMass W ⌊(W : ℝ) * T⌋₊ (q il.1) / (M * W) :=
    div_nonneg (gridMass_nonneg W _ (hq il.1)) (by positivity)
  have hK : ((2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω)).PosSemidef :=
    (farEmbed_omittedProj_psd b E h ⌊(W : ℝ) * s⌋₊ ω).smul (by norm_num)
  have h1 : ∀ z : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ),
      ∫⁻ θ, ENNReal.ofReal (leakTerm b E s T h q M W il ((ω, z), θ)) ∂phaseLaw =
      ENNReal.ofReal (((2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
        rankOne (boundaryToInterior b E W ⌊(W : ℝ) * T⌋₊ ω)
          (gridMass W ⌊(W : ℝ) * T⌋₊ (q il.1) / (M * W)) (z.1 il, z.2 il)).trace.re) := by
    intro z
    have e : ∀ θ, leakTerm b E s T h q M W il ((ω, z), θ) =
        ((physClosingMap b E s T h W ω (phase θ) - 1) *
          (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ *
          rankOne (boundaryToInterior b E W ⌊(W : ℝ) * T⌋₊ ω)
            (gridMass W ⌊(W : ℝ) * T⌋₊ (q il.1) / (M * W)) (z.1 il, z.2 il)).trace.re :=
      fun θ => rfl
    simp only [e]
    exact lintegral_phase_leak hN hD (rankOne_psd _ hκ _)
  rw [lintegral_congr h1, lintegral_sample_leak _ hq hW0 hM hK il, sampleMean_eq,
    Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, show (2 : ℂ) * (((M : ℝ)⁻¹ : ℝ) : ℂ) = ((2 / M : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- **The expected leaked mass of one injection.** -/
theorem eventually_lintegral_leakTerm {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) {s T h : ℝ} (hs : 0 < s) (hsT : s < T) (hh0 : 0 < h) (hh1 : h < 1) {p : ℕ}
    {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) {M : ℕ} (hM : 0 < M) :
    ∀ᶠ W in atTop, ∀ il : Fin p × Fin M,
      ∫⁻ y, ENNReal.ofReal (leakTerm b E s T h q M W il y)
          ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) =
        ∫⁻ ω, ENNReal.ofReal (2 / M * (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
          intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q il.1) ω).trace.re) ∂growthPathLaw W b := by
  have hh2 : h ^ 2 < 1 := by nlinarith
  filter_upwards [closedReflection_holds b hb0 hb E hE1 hE2 s T h hs hsT hh0 hh1,
    eventually_ge_atTop 1] with W hW hW1 il
  have hm := (measurable_leakTerm b E s T h q M W il).ennreal_ofReal
  have hm2 := hm.lintegral_prod_right' (ν := phaseLaw)
  rw [lintegral_prod _ hm.aemeasurable]
  unfold sampledPathLaw
  rw [lintegral_prod _ hm2.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hW, ae_phaseAvg_physClosingDefect hb hE1 hE2 hW1 s T h hh2] with ω hN hD
  exact lintegral_leak_path hq hM (by omega) il hN (hD hN)

end BlockBand.SourceProcess.ClosingLeak
