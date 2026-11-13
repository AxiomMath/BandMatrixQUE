module

public import BlockBand.SourceProcess.ContractingWords.StepFluctMain
public import BlockBand.SourceProcess.ContractingWords.PathStepAll

/-!
# The centered step for every admitted product, with unborn tags

`stepFluct_noBirth`: at an index `j ≥ εW` that is not a tag birth, the centered step
`Z_{j+1} - E[Z_{j+1} | 𝓕_j]` of an admitted product, on the survival event `{j < σ_K}`, has
`L^p` norm at most `C/√W`, uniformly in `W ≥ W₀` and `E` in the bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W : ℕ}

theorem stepFluct_noBirth (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hL : LayerFreshBound) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ,
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            productValue b E k q W (j + 1) ω Zs -
              (growthPathLaw W b)[fun ω' => productValue b E k q W (j + 1) ω' Zs |
                growthSigma W j] ω)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (C / Real.sqrt W) := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨c₀, hc₀, hqc⟩ := intervalTests_bounded hq
  obtain ⟨C, W₀, hC0, hL'⟩ := hL b hb0 hb κI hκ d p (max K 0) c₀ hp (le_max_right _ _) hc₀
  obtain ⟨Ce, We, hCe0, hErr⟩ := errMoments hMT hGA hLp hb0 hb hκ (T := T) hε hp
  obtain ⟨Wi, hInt⟩ := productValue_integrable hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T
    hε hεT
  refine ⟨C * (1 + Ce), max (max W₀ We) (max Wi 1),
    fun W hW E hE k Zs hZ hd j hj hkj hjT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₀, hWe⟩, hWi, hW1⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hj1 : 1 ≤ j := by
    have : (0 : ℝ) < j := lt_of_lt_of_le (mul_pos hε hW0) hj
    exact_mod_cast this
  have hjT' : (j : ℝ) ≤ T * W := le_trans (by push_cast; linarith) hjT
  set μ := growthPathLaw W b
  have hj' : ε * W ≤ ((j + 1 : ℕ) : ℝ) := hj.trans (by push_cast; linarith)
  have hint := hInt W hWi E hE k (j + 1) hj' hjT Zs hZ hd
  have hce := condExp_step' hb0 hb hE1 hE2 hW1 k q hj1 hkj Zs hint
  have hst := ae_step_state' hb0 hb hE1 hE2 hW1 k q
  have hH := ae_growth_isHermitian W b
  obtain ⟨s, hs⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  set A := alive b E k q K ε W j
  obtain ⟨A', hA'm, hA'eq0⟩ := measurableSet_alive b E k q K ε j (W := W)
  have hA'eq : pastCoords W j ⁻¹' A' = A := hA'eq0
  set H := {x : PastSample W j | ∀ k : Fin j, (x.1 k).IsHermitian}
  set B : PastSample W j → ℝ := fun x =>
    C * (1 / Real.sqrt W + jetDistance0 b E (pathX b E W j (extPast W j x)))
  have hBm : Measurable B := measurable_const.mul (measurable_const.add
    ((measurable_jetDistance0 b E).comp
      ((BlockBand.Transmission.PathJet.measurable_pathX b E j).comp (measurable_extPast j))))
  have hB0 : ∀ x, 0 ≤ B x := fun x => by simp only [B, jetDistance0]; positivity
  have hBb : ∀ x ∈ A' ∩ H, eLpNorm (fun y => stateΨ b E k q W j Zs (x, y) -
      ∫ y', stateΨ b E k q W j Zs (x, y') ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (B x) := by
    rintro x ⟨hxA, hxH⟩
    have hω : extPast W j x ∈ A := by
      rw [← hA'eq]; simpa only [Set.mem_preimage, pastCoords_extPast] using hxA
    have hXX := pathSchur_isHermitian E j (extPast W j x) (extPast_isHermitian hxH)
    have hb := (hL' W hW₀ E hE s hs (pathXX E W j (extPast W j x)) hXX nT nI
      (letterMatrix b E k q W j (extPast W j x)) (injCoef q W j)
      (letterMatrix_isHermitian b E k q hq j _)
      (fun ℓ => (nuclearNorm_letter_le b E k q hq hj hω ℓ).trans (le_max_left _ _))
      (injCoef_le hc₀ hqc j) Zs hZ hd).2.2
    simp only [← pathX_eq] at hb
    exact hb
  have hF := eLpNorm_indicator_fresh_le b j (measurable_stateΨ b E k q j Zs)
    (hA'm.inter (measurableSet_pastHerm j)) hp hBm hB0 hBb
  have hLHS : A.indicator (fun ω => productValue b E k q W (j + 1) ω Zs -
      μ[fun ω' => productValue b E k q W (j + 1) ω' Zs | growthSigma W j] ω) =ᵐ[μ]
      (pastCoords W j ⁻¹' (A' ∩ H)).indicator (fun ω =>
        stateΨ b E k q W j Zs (pastCoords W j ω, freshSample W j ω) -
          ∫ y, stateΨ b E k q W j Zs (pastCoords W j ω, y) ∂freshLaw W b) := by
    filter_upwards [hce, hst, hH] with ω hω1 hω2 hω3
    have hpcH : pastCoords W j ω ∈ H := fun k => hω3 k
    have hmem : ω ∈ A ↔ ω ∈ pastCoords W j ⁻¹' (A' ∩ H) := by
      rw [← hA'eq]; simp only [Set.mem_preimage, Set.mem_inter_iff, hpcH, and_true]
    by_cases hωA : ω ∈ A
    · rw [Set.indicator_of_mem hωA, Set.indicator_of_mem (hmem.mp hωA), hω1,
        (hω2 j hj1 hkj Zs).1]
      simp only [stateΨ, stateZ_extPast]
    · rw [Set.indicator_of_notMem hωA, Set.indicator_of_notMem (fun h => hωA (hmem.mpr h))]
  rw [eLpNorm_congr_ae hLHS]
  refine hF.trans ?_
  set err : GrowthPath W → ℝ := fun ω => jetDistance0 b E (pathX b E W j ω) +
    jetDistance1 b E s (pathX b E W j ω) + |pathConductance b E W j ω| / W + (W : ℝ)⁻¹
  have hR : ∀ ω, ‖(pastCoords W j ⁻¹' (A' ∩ H)).indicator (fun ω => B (pastCoords W j ω)) ω‖ ≤
      C * (1 / Real.sqrt W + err ω) := fun ω => by
    have h1 : 0 ≤ jetDistance1 b E s (pathX b E W j ω) := by simp only [jetDistance1]; positivity
    have h2 : 0 ≤ |pathConductance b E W j ω| / W := by positivity
    have h3 : 0 ≤ (W : ℝ)⁻¹ := by positivity
    have hB' : B (pastCoords W j ω) ≤ C * (1 / Real.sqrt W + err ω) := by
      simp only [B, pathX_extPast, err]
      exact mul_le_mul_of_nonneg_left (by linarith) hC0
    by_cases hω : ω ∈ pastCoords W j ⁻¹' (A' ∩ H)
    · rw [Set.indicator_of_mem hω, Real.norm_of_nonneg (hB0 _)]; exact hB'
    · rw [Set.indicator_of_notMem hω, norm_zero]; exact (hB0 _).trans hB'
  have hm2 : AEStronglyMeasurable ((pastCoords W j ⁻¹' (A' ∩ H)).indicator
      fun ω => B (pastCoords W j ω)) μ :=
    ((hBm.comp (measurable_pastCoords W j)).indicator
      ((measurable_pastCoords W j) (hA'm.inter (measurableSet_pastHerm j)))).aestronglyMeasurable
  refine (eLpNorm_mono_real hm2 hR).trans ?_
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using hp
  have e : (fun ω => C * (1 / Real.sqrt W + err ω)) = C • ((fun _ => 1 / Real.sqrt W) + err) := by
    funext ω; simp [smul_eq_mul]
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hC0]
  have hc : eLpNorm (fun _ : GrowthPath W => 1 / Real.sqrt W) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (1 / Real.sqrt W) := by
    have : IsProbabilityMeasure μ := by simp only [μ, growthPathLaw]; infer_instance
    refine (eLpNorm_le_of_ae_bound aestronglyMeasurable_const (C := 1 / Real.sqrt W)
      (Eventually.of_forall fun _ => by rw [Real.norm_of_nonneg (by positivity)])).trans ?_
    simp
  have hsq : 1 / (W : ℝ) ≤ 1 / Real.sqrt W := by
    have h1 : Real.sqrt W ≤ W := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [(by exact_mod_cast hW1 : (1 : ℝ) ≤ W)]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hW0) h1
  calc ENNReal.ofReal C * eLpNorm ((fun _ => 1 / Real.sqrt W) + err) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * (ENNReal.ofReal (1 / Real.sqrt W) + ENNReal.ofReal (Ce / W)) := by
        gcongr
        exact (eLpNorm_add_le hp1).trans (add_le_add hc (hErr W hWe E hE s hs j hj hjT'))
    _ ≤ ENNReal.ofReal (C * (1 + Ce) / Real.sqrt W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC0]
        refine ENNReal.ofReal_le_ofReal ?_
        have : Ce / W ≤ Ce / Real.sqrt W := by
          rw [div_eq_mul_one_div, div_eq_mul_one_div Ce]
          exact mul_le_mul_of_nonneg_left hsq hCe0
        have e2 : C * (1 + Ce) / Real.sqrt W = C * (1 / Real.sqrt W + Ce / Real.sqrt W) := by ring
        rw [e2]
        exact mul_le_mul_of_nonneg_left (by linarith) hC0

end BlockBand.SourceProcess.ContractingWords
