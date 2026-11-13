module

public import BlockBand.SourceProcess.ContractingWords.LiftDriftMain

/-!
# `OrdinaryDriftStepAll` from the one-layer `LayerDrift`

`ordinaryDriftStepAll_of`: the one-layer drift bound `LayerDrift`, applied along the growth path at
the step `j → j+1` on the survival event, gives the first conditional increment bound
`OrdinaryDriftStepAll`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped ENNReal

variable {W nT nI : ℕ}

/-- The fresh integral of the increment, on the survival event. -/
theorem integral_incΨ_eq (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (w : TraceWord nT nI) (ω : GrowthPath W)
    (hi : Integrable (fun y => newProd (letterMatrix b E k q W j ω) (injCoef q W j)
      (freshTransport b E (pathXX E W j ω) y) (freshD b E (pathXX E W j ω) y)
      (sepOf b E (freshTwoPortSchur E (pathXX E W j ω) y)) [w]) (freshLaw W b))
    (hcore : productValue b E k q W j ω [w] =
      coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) [w]) :
    ∫ y, incΨ b E k q W j w (pastCoords W j ω, y) ∂freshLaw W b =
      ∫ y, layerNew b E (letterMatrix b E k q W j ω) (injCoef q W j) (pathXX E W j ω) w y
          ∂freshLaw W b -
        coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) [w] := by
  have e : ∀ y, incΨ b E k q W j w (pastCoords W j ω, y) =
      layerNew b E (letterMatrix b E k q W j ω) (injCoef q W j) (pathXX E W j ω) w y -
        coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) [w] := fun y => by
    rw [incΨ_past, hcore]
    simp [stateZ, newProd, layerNew]
  have hi' : Integrable (fun y => layerNew b E (letterMatrix b E k q W j ω) (injCoef q W j)
      (pathXX E W j ω) w y) (freshLaw W b) := hi.congr (Eventually.of_forall fun y => by
        simp [newProd, layerNew])
  simp_rw [e]
  rw [integral_sub hi' (integrable_const _), integral_const, probReal_univ, one_smul]

/-- **`OrdinaryDriftStepAll`** from the input hypotheses and the one-layer `LayerDrift`. -/
theorem ordinaryDriftStepAll_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hLD : LayerDrift) :
    OrdinaryDriftStepAll := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K hε hεT
  obtain ⟨c₀, hc₀, hqc⟩ := intervalTests_bounded hq
  obtain ⟨C1, W1, hC1, hL⟩ := hLD b hb0 hb κI hκ d (max K 0) c₀ (le_max_right _ _) hc₀
  obtain ⟨CF, WF, -, hFr⟩ := layerFreshBound_holds hGA hLp b hb0 hb κI hκ d 1 (max K 0) c₀
    le_rfl (le_max_right _ _) hc₀
  obtain ⟨Cd, ρ, Wd, hCd, hρ0, hρ1, hdec⟩ := decay_restart hMT hGA hLp hSR b hb0 hb κI hκ nT nI
    q hq d ε T K 4 hε hεT (by norm_num)
  obtain ⟨C4, W4, hC4, h4⟩ := errMoments hMT hGA hLp hb0 hb hκ (T := T) hε (p := 4)
    (by norm_num)
  obtain ⟨C2, W2, hC2, h2⟩ := pathErr_pow_le hMT hGA hLp hb0 hb hκ (T := T) hε (n := 2)
    (by norm_num)
  obtain ⟨CN, WN, hCN, hN⟩ := pathErr_pow_le hMT hGA hLp hb0 hb hκ (T := T) hε
    (n := 2 * d + 4) (by omega)
  obtain ⟨WI, hInt⟩ := productValue_integrable hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T
    hε hεT
  refine ⟨C1 * ((20 * d ^ 2 : ℕ) : ℝ) * C4 * Cd + C1 * (1 + C2 ^ 2 + CN ^ (2 * d + 4)), ρ,
    max (max (max W1 WF) (max Wd W4)) (max (max W2 WN) (max WI 1)), by positivity, hρ0, hρ1,
    fun W hW E hE k j hj hjk hjT w hw hlen => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW1, hWF⟩, hWd, hW4⟩, ⟨hW2, hWN⟩, hWI, hW1'⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  obtain ⟨s, hs⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hj1 : 1 ≤ j := by
    have : (0 : ℝ) < j := lt_of_lt_of_le (mul_pos hε hW0) hj
    exact_mod_cast this
  have hjT' : (j : ℝ) ≤ T * W := le_trans (by push_cast; linarith) hjT
  have hj' : ε * W ≤ ((j + 1 : ℕ) : ℝ) := hj.trans (by push_cast; linarith)
  have hZ : IsAdmittedProduct [w] := fun v hv => by
    simp only [List.mem_singleton] at hv; rw [hv]; exact hw.1
  have hd : productDegree [w] ≤ d := by simpa [productDegree] using hlen
  set μ := growthPathLaw W b
  set A := alive b E k q K ε W j
  have hm : growthSigma W j ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
    growthSigma_le j
  have hAm : MeasurableSet A := hm _ (measurableSet_alive b E k q K ε j)
  have hf : Integrable (wordInc b E k q W j w) μ :=
    ((hInt W hWI E hE k (j + 1) hj' hjT [w] hZ hd).sub
      (hInt W hWI E hE k j hj hjT' [w] hZ hd)).congr
      (Eventually.of_forall fun ω => by simp [productValue, wordInc])
  have hce := condExp_alive_eq b E k q K ε j hf (measurable_incΨ b E k q j w) (by
    filter_upwards [ae_wordInc_eq hb0 hb hE1 hE2 hW1' k q hj1 hjk] with ω h; exact h w)
  set L := contrDrift w
  have hpt : ∀ᵐ ω ∂μ, ‖A.indicator (fun ω => μ[A.indicator (wordInc b E k q W j w) |
      growthSigma W j] ω - (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordDrift (transportD0 b E) w +
        MvPolynomial.C (wordInjection b q (stepTime W j) w))) ω‖ ≤
      driftMaj b E s k q K ε W j d C1 L ω := by
    filter_upwards [hce, ae_step_state' hb0 hb hE1 hE2 hW1' k q, ae_growth_isHermitian W b,
      ae_isUnit_pathPencil_growth hb hW1' E] with ω hω1 hω2 hω3 hω4
    by_cases hA : ω ∈ A
    · rw [Set.indicator_of_mem hA, hω1, Set.indicator_of_mem hA]
      have hcore : ∀ Zs, productValue b E k q W j ω Zs = coreProd (letterMatrix b E k q W j ω)
          (sepOf b E (pathXX E W j ω)) Zs := fun Zs => (hω2 j hj1 hjk Zs).2
      have hXX := pathSchur_isHermitian E j ω hω3
      have hlet := letterMatrix_isHermitian b E k q hq j ω
      have hnuc : ∀ ℓ, nuclearNorm (letterMatrix b E k q W j ω ℓ) ≤ max K 0 := fun ℓ =>
        (nuclearNorm_letter_le b E k q hq hj hA ℓ).trans (le_max_left K 0)
      have hb' := hL W hW1 E hE s hs (pathXX E W j ω) hXX nT nI (letterMatrix b E k q W j ω) q j
        hlet hnuc (pathCurrent_eq b E j ω (hω4 j)) hqc w hw hlen
      have hiF := (hFr W hWF E hE s hs (pathXX E W j ω) hXX nT nI (letterMatrix b E k q W j ω)
        (injCoef q W j) hlet hnuc (injCoef_le hc₀ hqc j) [w] hZ hd).1
      rw [integral_incΨ_eq b E k q j w ω hiF (hcore [w]), polyValue_eq_core hcore]
      exact driftMaj_ge hC1 L hA hcore hb'
    · rw [Set.indicator_of_notMem hA, norm_zero]
      exact driftMaj_nonneg b E s k q K ε W j d hC1 L ω
  have hLHSm : AEStronglyMeasurable (A.indicator fun ω => μ[A.indicator (wordInc b E k q W j w) |
      growthSigma W j] ω - (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordDrift (transportD0 b E) w +
        MvPolynomial.C (wordInjection b q (stepTime W j) w))) μ :=
    ((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.sub
      ((measurable_polyValue b E k q j _).aestronglyMeasurable.const_mul _)).indicator hAm
  refine (eLpNorm_mono_ae_real hLHSm hpt).trans ?_
  have h4' : eLpNorm (pathErr b E s W j) 4 μ ≤ ENNReal.ofReal (C4 / W) := by
    have := h4 W hW4 E hE s hs j hj hjT'
    rwa [show ENNReal.ofReal 4 = 4 by norm_num] at this
  have h2' := (h2 W hW2 E hE s hs j hj hjT').2
  have hN' := (hN W hWN E hE s hs j hj hjT').2
  have hZ' : ∀ Zs ∈ L, eLpNorm (A.indicator fun ω => productValue b E k q W j ω Zs) 4 μ ≤
      ENNReal.ofReal (Cd * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)) := by
    intro Zs hZs
    obtain ⟨h1, h2, h3⟩ := contrDrift_facts w Zs hZs
    have := hdec W hWd E hE k Zs h1 (by rw [h2]; exact hlen) h3 j hj hjT'
    rwa [show ENNReal.ofReal 4 = 4 by norm_num] at this
  have hG := eLpNorm_lifted_le (μ := μ) L (fun Zs ω => productValue b E k q W j ω Zs) A hAm
    (pathErr b E s W j) (h2 W hW2 E hE s hs j hj hjT').1
    (fun Zs => (measurable_productValue b E k q j Zs).aestronglyMeasurable) (2 * d + 4)
    (c := (W : ℝ)⁻¹ / Real.sqrt W) hC1
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) h4' h2' hN' hZ'
  unfold driftMaj
  refine hG.trans (ENNReal.ofReal_le_ofReal ?_)
  have hLl : (L.length : ℝ) ≤ ((20 * d ^ 2 : ℕ) : ℝ) := by
    have h1 := contrDrift_length_le w
    have h2 : w.length ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hlen 2
    exact_mod_cast h1.trans (by omega)
  have hX : 0 ≤ C4 / W * (Cd * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)) := by
    positivity
  have hstep := stepErr_of_parts (W := W) (by omega) (C₁ := C1) (Cz := Cd) (Ce := C4)
    (M := ((20 * d ^ 2 : ℕ) : ℝ)) (ρ := ρ ^ (j - restartIndex ε W k j))
    (m := ρ ^ (j - restartIndex ε W k j)) (c₂ := C2) (cN := CN) (N := 2 * d + 4) (by omega) hC1
    (by positivity) (by positivity) hCN rfl
  refine le_trans ?_ (hstep.trans (le_of_eq ?_))
  · have := mul_le_mul_of_nonneg_right hLl hX
    nlinarith [mul_le_mul_of_nonneg_left this hC1]
  · simp only [stepErr]

end BlockBand.SourceProcess.ContractingWords
