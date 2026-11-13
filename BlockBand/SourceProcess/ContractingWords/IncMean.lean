module

public import BlockBand.SourceProcess.ContractingWords.StepMean
public import BlockBand.SourceProcess.ContractingWords.PathStepAll

/-!
# The step mean for every admitted product, with unborn tags

`stepMean_noBirth`: at an index `j ≥ εW` that is not a tag birth, the conditional mean of an
admitted product satisfies `E[Z_{j+1} | 𝓕_j] = m(Z) Z_j + O(1/W)` in `L^p` on the survival
event `{j < σ_K}`, with `m = meanFactor` at a stationary jet.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge
open scoped ENNReal

theorem stepMean_noBirth (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hL : LayerFreshBound) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ k : Fin nT → ℕ,
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            (growthPathLaw W b)[fun ω' => productValue b E k q W (j + 1) ω' Zs |
              growthSigma W j] ω - meanFactor b E s Zs * productValue b E k q W j ω Zs)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (C / W) := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨c₀, hc₀, hqc⟩ := intervalTests_bounded hq
  obtain ⟨C, W₀, hC0, hL'⟩ := hL b hb0 hb κI hκ d p (max K 0) c₀ hp (le_max_right _ _) hc₀
  obtain ⟨Ce, We, hCe0, hErr⟩ := errMoments hMT hGA hLp hb0 hb hκ (T := T) hε hp
  obtain ⟨Wi, hInt⟩ := productValue_integrable hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T
    hε hεT
  refine ⟨C * Ce, max (max W₀ We) (max Wi 1), fun W hW E hE s hs k Zs hZ hd j hj hkj hjT => ?_⟩
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
  set A := alive b E k q K ε W j
  set err : GrowthPath W → ℝ := fun ω => jetDistance0 b E (pathX b E W j ω) +
    jetDistance1 b E s (pathX b E W j ω) + |pathConductance b E W j ω| / W + (W : ℝ)⁻¹
  have herr0 : ∀ ω, 0 ≤ err ω := fun ω => by
    simp only [err, jetDistance0, jetDistance1]; positivity
  have hm : growthSigma W j ≤ (inferInstance : MeasurableSpace (GrowthPath W)) := by
    rw [growthSigma_eq_comap]; exact (measurable_pastCoords W j).comap_le
  have hAm : MeasurableSet A := hm _ (measurableSet_alive b E k q K ε j)
  have hLHSm : AEStronglyMeasurable (A.indicator fun ω =>
      μ[fun ω' => productValue b E k q W (j + 1) ω' Zs | growthSigma W j] ω -
        meanFactor b E s Zs * productValue b E k q W j ω Zs) μ :=
    ((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.sub
      ((measurable_productValue b E k q j Zs).aestronglyMeasurable.const_mul _)).indicator hAm
  have hpt : ∀ᵐ ω ∂μ, ‖A.indicator (fun ω =>
      μ[fun ω' => productValue b E k q W (j + 1) ω' Zs | growthSigma W j] ω -
        meanFactor b E s Zs * productValue b E k q W j ω Zs) ω‖ ≤ C * err ω := by
    filter_upwards [hce, hst, hH] with ω hω1 hω2 hω3
    by_cases hωA : ω ∈ A
    · rw [Set.indicator_of_mem hωA, hω1, (hω2 j hj1 hkj Zs).2]
      have hXX := pathSchur_isHermitian E j ω hω3
      have hb := (hL' W hW₀ E hE s hs (pathXX E W j ω) hXX nT nI (letterMatrix b E k q W j ω)
        (injCoef q W j) (letterMatrix_isHermitian b E k q hq j ω)
        (fun ℓ => (nuclearNorm_letter_le b E k q hq hj hωA ℓ).trans (le_max_left _ _))
        (injCoef_le hc₀ hqc j) Zs hZ hd).2.1
      simp only [← pathX_eq] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      have : conductanceOf (passiveTransmission b E (pathX b E W j ω)) / W ≤
          |pathConductance b E W j ω| / W :=
        div_le_div_of_nonneg_right (le_abs_self _) hW0.le
      simp only [err]; linarith
    · rw [Set.indicator_of_notMem hωA, norm_zero]
      exact mul_nonneg hC0 (herr0 ω)
  refine (eLpNorm_mono_ae_real hLHSm hpt).trans ?_
  have e : (fun ω => C * err ω) = C • err := by funext ω; simp [smul_eq_mul]
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hC0]
  calc ENNReal.ofReal C * eLpNorm err (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * ENNReal.ofReal (Ce / W) := by
        gcongr; exact hErr W hWe E hE s hs j hj hjT'
    _ = ENNReal.ofReal (C * Ce / W) := by rw [← ENNReal.ofReal_mul hC0, mul_div_assoc]

end BlockBand.SourceProcess.ContractingWords
