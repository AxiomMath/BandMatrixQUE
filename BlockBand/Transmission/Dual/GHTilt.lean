module

public import BlockBand.Transmission.Dual.GLemma1

/-!
# The local Doob identity for a general h-transform: hypotheses, density, pathwise identity

`IsHTransform D₀ q U h b̃`: on an open `U ⊆ 𝒞_q`, `h` is `C²` and positive, `𝓛⁰h = 0`, and
`𝓛⁰(hφ) = h 𝓛̃φ` for every `C²` `φ`, where `𝓛⁰` is the flat base generator and `𝓛̃` the
generator of `(b̃, flatDiff)`; `b̃` is locally Lipschitz on `U`. Examples: `(𝒞_q, H_q, flatDrift)`
(`isHTransform_cauchyH`), and the product transforms `G_j`. This file generalizes `exists_tilt`
and `testMart_mul_densM` from `H_q` to `h`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ}

/-- The hypotheses of a (local) h-transform of the flat base process. -/
structure IsHTransform (D0 : ℝ) (q : ℕ) (U : Set (Fin (q + q) → ℝ)) (h : (Fin (q + q) → ℝ) → ℝ)
    (bt : (Fin (q + q) → ℝ) → Fin (q + q) → ℝ) : Prop where
  isOpen : IsOpen U
  sub : U ⊆ flatChamber q
  smooth : ContDiffOn ℝ 2 h U
  pos : ∀ w ∈ U, 0 < h w
  harm : ∀ w ∈ U, mpGenerator (flatBaseDrift D0 q) (flatDiff D0 q) h w = 0
  lip : LocallyLipschitzOn U bt
  transform : ∀ φ : (Fin (q + q) → ℝ) → ℝ, ContDiff ℝ 2 φ → ∀ w ∈ U,
    mpGenerator (flatBaseDrift D0 q) (flatDiff D0 q) (fun w => h w * φ w) w =
      h w * mpGenerator bt (flatDiff D0 q) φ w

/-- The Cauchy determinant is an h-transform with target the flat dual. -/
theorem isHTransform_cauchyH (D0 : ℝ) :
    IsHTransform D0 q (flatChamber q) (flatH q) (flatDrift D0 q) where
  isOpen := isOpen_flatChamber q
  sub := subset_rfl
  smooth := contDiffOn_cauchyH_flat
  pos := fun _ hw => cauchyH_pos hw
  harm := fun _ hw => mpGenerator_flatBase_cauchyH D0 hw
  lip := locallyLipschitzOn_flatDrift D0
  transform := fun φ hφ w hw => by
    have hf : ContDiff ℝ 2 (φ ∘ flatHomeo q) := hφ.comp (contDiff_flatHomeo.of_le (by simp))
    have e : (fun w => flatH q w * φ w) = (fun z => cauchyH q z * (φ ∘ flatHomeo q) z) ∘ ofFlat q :=
      funext fun w => by
        simp only [Function.comp_apply, flatH]
        rw [show flatHomeo q (ofFlat q w) = w from (flatHomeo q).apply_symm_apply w]
    rw [e, mpGenerator_flatBase_cauchyH_mul D0 hf hw, ← mpGenerator_flat D0 hf w, comp_flatHomeo]
    rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}
  {z : Fin (q + q) → ℝ} {W U : Set (Fin (q + q) → ℝ)} {h : (Fin (q + q) → ℝ) → ℝ}
  {bt : (Fin (q + q) → ℝ) → Fin (q + q) → ℝ}

theorem IsHTransform.continuousOn_bt (hh : IsHTransform D0 q U h bt) : ContinuousOn bt U :=
  hh.lip.continuousOn

/-- The density `h(Z^τ_t)/h(z)`. -/
def densH (h : (Fin (q + q) → ℝ) → ℝ) (W : Set (Fin (q + q) → ℝ))
    (Z : ℝ≥0 → Ω → Fin (q + q) → ℝ) (z : Fin (q + q) → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  h (stopZ W Z t ω) / h z

/-- The target generator vanishes off the support of the test function. -/
theorem mpGenerator_eq_zero_of_notMem {d : ℕ} {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {φ : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ}
    (hw : w ∉ tsupport φ) : mpGenerator b a φ w = 0 := by
  rw [mpGenerator_congr (notMem_tsupport_iff_eventuallyEq.1 hw)]
  simp [mpGenerator]

variable [IsProbabilityMeasure P]

/-- Itô's formula for the base solution on `U`: the stopped test process has a martingale
modification. -/
theorem hasMM_stop_base (hZ : IsBaseSol D0 q P 𝓖 Z z) (hU : IsOpen U)
    {φ : (Fin (q + q) → ℝ) → ℝ} (hφ : ContDiffOn ℝ 2 φ U) {L : (Fin (q + q) → ℝ) → ℝ}
    (hL : ∀ w ∈ U, mpGenerator (flatBaseDrift D0 q) (flatDiff D0 q) φ w = L w)
    (hW : IsInteriorDomain W U) :
    HasMartingaleModification P 𝓖 (stoppedProcess (fun t ω => φ (Z t ω) - φ (Z 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, L (Z s.toNNReal ω)) (exitTimeFrom W Z)) := by
  obtain ⟨M, hM, hMe⟩ := Semimartingale.martingaleProblemIto_holds (q + q) Ω P 𝓖
    (flatBaseDrift D0 q) (flatDiff D0 q) U hU (continuous_flatBaseDrift D0).continuousOn
    (contDiff_flatDiff D0).continuous.continuousOn Z (isMPSolutionOn_mono hZ.sol (subset_univ U))
    φ hφ W hW
  refine ⟨M, hM, fun t => (hMe t).trans (Eventually.of_forall fun ω => ?_)⟩
  simp only [stoppedProcess_eq_stopTime]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => hL _ (hW.2.2 ?_)
  exact (Bridges.stopped_path_mem_closure hW.1 (hZ.cont ω) t).1 s hs

theorem exists_bound_h (hh : IsHTransform D0 q U h bt) (hW : IsInteriorDomain W U) :
    ∃ C, ∀ w ∈ closure W, 0 < h w ∧ h w ≤ C := by
  obtain ⟨C, hC⟩ := hW.2.1.exists_bound_of_continuousOn (hh.smooth.continuousOn.mono hW.2.2)
  exact ⟨C, fun w hw => ⟨hh.pos _ (hW.2.2 hw), (le_abs_self _).trans
    (Real.norm_eq_abs _ ▸ hC w hw)⟩⟩

/-- **The tilted measure of the h-transform.** -/
theorem exists_tiltH (hh : IsHTransform D0 q U h bt) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W U) (hzW : z ∈ W) : ∃ (M : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0),
      IsDensity P 𝓖 M g ∧ (∀ t, M t =ᵐ[P] densH h W Z z t) ∧ IsProbabilityMeasure (tilt P g) := by
  obtain ⟨C, hC⟩ := exists_bound_h hh hW
  have hz0 : 0 < h z := (hC z (subset_closure hzW)).1
  obtain ⟨N, hN, hNe⟩ := hasMM_stop_base hZ hh.isOpen hh.smooth hh.harm hW
  set M : ℝ≥0 → Ω → ℝ := fun t => (h z)⁻¹ • (N t + fun _ => h z)
  have hM : Martingale M 𝓖 P := (hN.add (martingale_const 𝓖 P (h z))).smul _
  have hMe : ∀ t, M t =ᵐ[P] densH h W Z z t := fun t => by
    filter_upwards [hNe t] with ω hω
    simp only [M, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hω, densH, stoppedProcess_eq_stopTime,
      hZ.start, stopZ, integral_zero, sub_zero]
    field_simp
    ring
  have hbd : ∀ t, ∀ᵐ ω ∂P, 0 ≤ M t ω ∧ M t ω ≤ C / h z := fun t => by
    filter_upwards [hMe t] with ω hω
    rw [hω, densH]
    have h' := hC _ (stopZ_mem_closure hZ hW.1 hzW t ω)
    exact ⟨div_nonneg h'.1.le hz0.le, div_le_div_of_nonneg_right h'.2 hz0.le⟩
  obtain ⟨g, hg⟩ := exists_isDensity hM hbd
  refine ⟨M, g, hg, hMe, hg.isProbabilityMeasure_tilt ?_⟩
  filter_upwards [hMe 0] with ω hω
  rw [hω, densH, stopZ, stoppedProcess_eq_stopTime, Semimartingale.stopTime_zero, hZ.start,
    div_self hz0.ne']

omit [IsProbabilityMeasure P] in
/-- **The pathwise identity** `h(z) X_t M_t = I1 − φ(z) I2 − I3` for the target generator. -/
theorem testMart_mul_densH (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W)
    {φ : (Fin (q + q) → ℝ) → ℝ} (hφs : tsupport φ ⊆ W) (t : ℝ≥0) (ω : Ω) :
    testMart bt (flatDiff D0 q) φ (stopZ W Z) t ω * densH h W Z z t ω =
      (h z)⁻¹ * (stoppedProcess (fun t ω => h (Z t ω) * φ (Z t ω) - h (Z 0 ω) * φ (Z 0 ω) -
        ∫ s in Ioc (0 : ℝ) t, h (Z s.toNNReal ω) * mpGenerator bt (flatDiff D0 q) φ
          (Z s.toNNReal ω)) (exitTimeFrom W Z) t ω -
        φ z * stoppedProcess (fun t ω => h (Z t ω) - h (Z 0 ω)) (exitTimeFrom W Z) t ω -
        ((∫ s in Ioc (0 : ℝ) t, mpGenerator bt (flatDiff D0 q) φ (stopZ W Z s.toNNReal ω)) *
            h (stopZ W Z t ω) -
          ∫ s in Ioc (0 : ℝ) t, mpGenerator bt (flatDiff D0 q) φ (stopZ W Z s.toNNReal ω) *
            h (stopZ W Z s.toNNReal ω))) := by
  have hvan : ∀ w ∉ W, h w * mpGenerator bt (flatDiff D0 q) φ w = 0 := fun w hw => by
    rw [mpGenerator_eq_zero_of_notMem (fun hm => hw (hφs hm)), mul_zero]
  have hI := integral_stopZ hZ hW hvan t ω
  simp only [stoppedProcess_eq_stopTime, hZ.start]
  rw [← hI]
  have e0 : stopZ W Z 0 ω = z := by
    rw [stopZ, stoppedProcess_eq_stopTime, Semimartingale.stopTime_zero, hZ.start]
  have e1 : ∫ s in Ioc (0 : ℝ) t, mpGenerator bt (flatDiff D0 q) φ (stopZ W Z s.toNNReal ω) *
      h (stopZ W Z s.toNNReal ω) = ∫ s in Ioc (0 : ℝ) t,
      h (stopZ W Z s.toNNReal ω) * mpGenerator bt (flatDiff D0 q) φ (stopZ W Z s.toNNReal ω) :=
    setIntegral_congr_fun measurableSet_Ioc fun s _ => mul_comm _ _
  rw [e1]
  unfold testMart densH
  rw [e0]
  simp only [stopZ, stoppedProcess_eq_stopTime]
  by_cases hz : h z = 0
  · simp [hz]
  · field_simp
    ring

end BlockBand.Transmission.Dual.G
