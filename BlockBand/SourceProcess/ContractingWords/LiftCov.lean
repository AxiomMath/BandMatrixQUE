module

public import BlockBand.SourceProcess.ContractingWords.LiftDriftHolds

/-!
# `OrdinaryCovStepAll` from the one-layer `LayerCov`

`ordinaryCovStepAll_of`: the one-layer covariance bound `LayerCov`, applied along the growth path
at the step `j → j+1` and combined with the decay of contracting products from the last restart,
gives the second conditional increment bound `OrdinaryCovStepAll`. The word increments are in
`L²` (`memLp_wordInc`).
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

theorem integral_incΨ_mul_eq (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (w v : TraceWord nT nI) (ω : GrowthPath W)
    (hcore : ∀ Zs, productValue b E k q W j ω Zs =
      coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs) :
    ∫ y, incΨ b E k q W j w (pastCoords W j ω, y) * incΨ b E k q W j v (pastCoords W j ω, y)
        ∂freshLaw W b =
      ∫ y, (layerNew b E (letterMatrix b E k q W j ω) (injCoef q W j) (pathXX E W j ω) w y -
          coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) [w]) *
        (layerNew b E (letterMatrix b E k q W j ω) (injCoef q W j) (pathXX E W j ω) v y -
          coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) [v]) ∂freshLaw W b := by
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [incΨ_past, incΨ_past, hcore, hcore]
  simp [stateZ, newProd, layerNew]

theorem memLp_wordInc (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κI : ℝ} (hκ : 0 < κI) {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q)
    (d : ℕ) {ε T : ℝ} (hε : 0 < ε) (hεT : ε < T) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ (k : Fin nT → ℕ) (j : ℕ),
      ε * W ≤ j → ((j + 1 : ℕ) : ℝ) ≤ T * W → ∀ w : TraceWord nT nI, w ≠ [] → w.length ≤ d →
        MemLp (wordInc b E k q W j w) 2 (growthPathLaw W b) := by
  obtain ⟨C, W₀, h⟩ := productValue_eLpNorm_le hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T 2
    hε hεT (by norm_num)
  refine ⟨W₀, fun W hW E hE k j hj hjT w hw hlen => ?_⟩
  have hZ : IsAdmittedProduct [w] := fun u hu => by
    simp only [List.mem_singleton] at hu; rw [hu]; exact hw
  have hd : productDegree [w] ≤ d := by simpa [productDegree] using hlen
  have hjT' : (j : ℝ) ≤ T * W := le_trans (by push_cast; linarith) hjT
  have hj' : ε * W ≤ ((j + 1 : ℕ) : ℝ) := hj.trans (by push_cast; linarith)
  have m1 : MemLp (fun ω => productValue b E k q W (j + 1) ω [w]) 2 (growthPathLaw W b) := by
    have := h W hW E hE k (j + 1) hj' hjT [w] hZ hd
    rw [show ENNReal.ofReal 2 = 2 by norm_num] at this
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  have m0 : MemLp (fun ω => productValue b E k q W j ω [w]) 2 (growthPathLaw W b) := by
    have := h W hW E hE k j hj hjT' [w] hZ hd
    rw [show ENNReal.ofReal 2 = 2 by norm_num] at this
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  refine (m1.sub m0).ae_eq (Eventually.of_forall fun ω => ?_)
  simp [productValue, wordInc]

/-- **`OrdinaryCovStepAll`** from the input hypotheses and the one-layer `LayerCov`. -/
theorem ordinaryCovStepAll_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hLC : LayerCov) :
    OrdinaryCovStepAll := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K hε hεT
  obtain ⟨c₀, hc₀, hqc⟩ := intervalTests_bounded hq
  obtain ⟨C1, W1, hC1, hL⟩ := hLC b hb0 hb κI hκ d (max K 0) c₀ (le_max_right _ _) hc₀
  obtain ⟨WF, hFr⟩ := memLp_wordInc hMT hGA hLp hSR hb0 hb hκ hq (nT := nT) d hε hεT
  obtain ⟨Cd, ρ, Wd, hCd, hρ0, hρ1, hdec⟩ := decay_restart hMT hGA hLp hSR b hb0 hb κI hκ nT nI
    q hq (2 * d) ε T K 4 hε hεT (by norm_num)
  obtain ⟨C4, W4, hC4, h4⟩ := errMoments hMT hGA hLp hb0 hb hκ (T := T) hε (p := 4)
    (by norm_num)
  obtain ⟨C2, W2, hC2, h2⟩ := pathErr_pow_le hMT hGA hLp hb0 hb hκ (T := T) hε (n := 2)
    (by norm_num)
  obtain ⟨CN, WN, hCN, hN⟩ := pathErr_pow_le hMT hGA hLp hb0 hb hκ (T := T) hε
    (n := 2 * d + 4) (by omega)
  refine ⟨C1 * ((16 * d ^ 2 : ℕ) : ℝ) * C4 * Cd + C1 * (1 + C2 ^ 2 + CN ^ (2 * d + 4)), ρ,
    max (max (max W1 WF) (max Wd W4)) (max (max W2 WN) 1), by positivity, hρ0, hρ1,
    fun W hW E hE k j hj hjk hjT w v hw hv hlen hlenv => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW1, hWF⟩, hWd, hW4⟩, ⟨hW2, hWN⟩, hW1'⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  obtain ⟨s, hs⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hj1 : 1 ≤ j := by
    have : (0 : ℝ) < j := lt_of_lt_of_le (mul_pos hε hW0) hj
    exact_mod_cast this
  have hjT' : (j : ℝ) ≤ T * W := le_trans (by push_cast; linarith) hjT
  have hj' : ε * W ≤ ((j + 1 : ℕ) : ℝ) := hj.trans (by push_cast; linarith)
  set μ := growthPathLaw W b
  set A := alive b E k q K ε W j
  have hm : growthSigma W j ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
    growthSigma_le j
  have hAm : MeasurableSet A := hm _ (measurableSet_alive b E k q K ε j)
  have hf : Integrable (fun ω => wordInc b E k q W j w ω * wordInc b E k q W j v ω) μ :=
    (hFr W hWF E hE k j hj hjT w hw.1 hlen).integrable_mul (hFr W hWF E hE k j hj hjT v hv.1 hlenv)
  have hce := condExp_alive_eq b E k q K ε j hf
    (Ψ := fun z => incΨ b E k q W j w z * incΨ b E k q W j v z)
    ((measurable_incΨ b E k q j w).mul (measurable_incΨ b E k q j v)) (by
    filter_upwards [ae_wordInc_eq hb0 hb hE1 hE2 hW1' k q hj1 hjk] with ω h; rw [h w, h v])
  set L := contrCov w v
  have hpt : ∀ᵐ ω ∂μ, ‖A.indicator (fun ω => μ[A.indicator
      (fun ω => wordInc b E k q W j w ω * wordInc b E k q W j v ω) |
      growthSigma W j] ω - (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) w v))
        ω‖ ≤
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
        hlet hnuc (pathCurrent_eq b E j ω (hω4 j)) hqc w v hw hv hlen hlenv
      rw [integral_incΨ_mul_eq b E k q j w v ω hcore, polyValue_eq_core hcore]
      exact driftMaj_ge hC1 L hA hcore hb'
    · rw [Set.indicator_of_notMem hA, norm_zero]
      exact driftMaj_nonneg b E s k q K ε W j d hC1 L ω
  have hLHSm : AEStronglyMeasurable (A.indicator fun ω => μ[A.indicator
      (fun ω => wordInc b E k q W j w ω * wordInc b E k q W j v ω) |
      growthSigma W j] ω - (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) w v)) μ :=
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
    obtain ⟨h1, h2, h3⟩ := contrCov_facts w v hw.1 Zs hZs
    have := hdec W hWd E hE k Zs h1 (by rw [h2]; omega) h3 j hj hjT'
    rwa [show ENNReal.ofReal 4 = 4 by norm_num] at this
  have hG := eLpNorm_lifted_le (μ := μ) L (fun Zs ω => productValue b E k q W j ω Zs) A hAm
    (pathErr b E s W j) (h2 W hW2 E hE s hs j hj hjT').1
    (fun Zs => (measurable_productValue b E k q j Zs).aestronglyMeasurable) (2 * d + 4)
    (c := (W : ℝ)⁻¹ / Real.sqrt W) hC1
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) h4' h2' hN' hZ'
  unfold driftMaj
  refine hG.trans (ENNReal.ofReal_le_ofReal ?_)
  have hLl : (L.length : ℝ) ≤ ((16 * d ^ 2 : ℕ) : ℝ) := by
    have h1 := contrCov_length_le w v
    have h2 : w.length * v.length ≤ d * d := Nat.mul_le_mul hlen hlenv
    have h3 : w.length * (v.length * 16) = 16 * (w.length * v.length) := by ring
    have h4 : d ^ 2 = d * d := by ring
    exact_mod_cast h1.trans (by omega)
  have hX : 0 ≤ C4 / W * (Cd * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)) := by
    positivity
  have hstep := stepErr_of_parts (W := W) (by omega) (C₁ := C1) (Cz := Cd) (Ce := C4)
    (M := ((16 * d ^ 2 : ℕ) : ℝ)) (ρ := ρ ^ (j - restartIndex ε W k j))
    (m := ρ ^ (j - restartIndex ε W k j)) (c₂ := C2) (cN := CN) (N := 2 * d + 4) (by omega) hC1
    (by positivity) (by positivity) hCN rfl
  refine le_trans ?_ (hstep.trans (le_of_eq ?_))
  · have := mul_le_mul_of_nonneg_right hLl hX
    nlinarith [mul_le_mul_of_nonneg_left this hC1]
  · simp only [stepErr]

end BlockBand.SourceProcess.ContractingWords
