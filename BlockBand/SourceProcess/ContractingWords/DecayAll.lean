module

public import BlockBand.SourceProcess.ContractingWords.EarlyIncrement
public import BlockBand.SourceProcess.ContractingWords.RecursionField
public import BlockBand.SourceProcess.ContractingWords.Summed

/-!
# Decay of contracting products with any births, restarted at the last birth

Admitted products containing a contracting letter decay geometrically in `L^p` along any window
without tag births, up to an error `W^{-1/2}`.

* **`decay_all`**: for an admitted product with a contracting letter, of degree `≤ d`, and a window
  `εW ≤ j₀ ≤ j ≤ TW` **without births** (`i ≠ k_a` for `j₀ ≤ i < j`; tags may be born anywhere
  else, before `εW` or after `j`):
  `‖1_{j<σ_K} Z_j‖_p ≤ C(ρ^{j-j₀} + W^{-1/2})`. The decay argument (`recursion_of`) with the
  one-step inputs `stepMean_noBirth`, `stepFluct_noBirth`, which need only `i ≠ k_a`.
* **`decay_restart`**: the same at `j₀ = restartIndex ε W k j`, which has no birth in `[j₀, j)`.

Measure `growthPathLaw W b`, `L^p` norm (`p ≥ 1`); constants depend on `b, κI`, the sources,
`d, ε, T, K, p`, uniformly in `W ≥ W₀`, `E ∈ bulkInterval κI`, the stationary jet, the births and
the window. Hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract`,
`ScalarRecursionContract` and `GaussianLpGradient`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open scoped ENNReal ComplexConjugate

/-- The one step `a_{i+1} ≤ ρ a_i + c` of the decay, along `1_{A_i}`. -/
theorem decay_step {W i : ℕ} {μ : Measure (GrowthPath W)} {A : ℕ → Set (GrowthPath W)}
    {Z : ℕ → GrowthPath W → ℂ} {lam : ℂ} {ρ e f p : ℝ} (hp : 1 ≤ p) (hlam : ‖lam‖ ≤ ρ)
    (hAm : MeasurableSet (A (i + 1))) (hZm : Measurable (Z (i + 1)))
    (hsub : A (i + 1) ⊆ A i) (Y : GrowthPath W → ℂ)
    (he : eLpNorm ((A i).indicator fun ω => Y ω - lam * Z i ω) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal e)
    (hξ : eLpNorm ((A i).indicator fun ω => Z (i + 1) ω - Y ω) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal f) (he0 : 0 ≤ e) (hf0 : 0 ≤ f) :
    eLpNorm ((A (i + 1)).indicator (Z (i + 1))) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ρ * eLpNorm ((A i).indicator (Z i)) (ENNReal.ofReal p) μ +
        ENNReal.ofReal (e + f) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hmono : eLpNorm ((A (i + 1)).indicator (Z (i + 1))) (ENNReal.ofReal p) μ ≤
      eLpNorm ((A i).indicator (Z (i + 1))) (ENNReal.ofReal p) μ := by
    refine eLpNorm_mono ((hZm.indicator hAm).aestronglyMeasurable) fun ω => ?_
    by_cases h : ω ∈ A (i + 1)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hsub h)]
    · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
  have hsplit : (A i).indicator (Z (i + 1)) = lam • (A i).indicator (Z i) +
      (A i).indicator (fun ω => Y ω - lam * Z i ω) +
        (A i).indicator (fun ω => Z (i + 1) ω - Y ω) := by
    funext ω
    by_cases h : ω ∈ A i
    · simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem h, smul_eq_mul]; ring
    · simp [Set.indicator_of_notMem h]
  refine hmono.trans ?_
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans ?_
  refine (add_le_add_left (eLpNorm_add_le hp1) _).trans ?_
  rw [eLpNorm_const_smul, ENNReal.ofReal_add he0 hf0, ← add_assoc]
  refine add_le_add (add_le_add ?_ he) hξ
  refine mul_le_mul_left ?_ _
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hlam

/-- **Decay along a window without births.** -/
theorem decay_all (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ k : Fin nT → ℕ, ∀ j₀ : ℕ, ε * W ≤ j₀ →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      ∀ j : ℕ, j₀ ≤ j → (j : ℝ) ≤ T * W → (∀ a i, j₀ ≤ i → i < j → i ≠ k a) →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω => productValue b E k q W j ω Zs)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C * (ρ ^ (j - j₀) + 1 / Real.sqrt W)) := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  have hL := layerFreshBound_holds hGA hLp
  obtain ⟨CM, WM, hCM⟩ :=
    stepMean_noBirth hMT hGA hLp hSR hL b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨CF, WF, hCF⟩ :=
    stepFluct_noBirth hMT hGA hLp hSR hL b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨C0, W0, hC0⟩ := productValue_eLpNorm_le hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T
    p hε hεT hp
  obtain ⟨hρ0, hρ1, -⟩ := thetaStar_bulk_bound hb0 hb hκ
  set ρ := thetaBound b κI
  set Cm := max CM 0
  set Cf := max CF 0
  set C0' := max C0 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  have hCf : 0 ≤ Cf := le_max_right _ _
  have hC0' : 0 ≤ C0' := le_max_right _ _
  have h1ρ : 0 < 1 - ρ := by linarith
  have hD : 0 ≤ (Cm + Cf) / (1 - ρ) := div_nonneg (by linarith) h1ρ.le
  refine ⟨C0' + (Cm + Cf) / (1 - ρ) + Cm + Cf, ρ, max (max WM WF) (max W0 1), by positivity,
    hρ0, hρ1, ?_⟩
  intro W hW E hE s hs k j₀ hj₀ Zs hZ hd hr j hj hjT hnb
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWM, hWF⟩, hW0, hW1⟩ := hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hlam : ‖meanFactor b E s Zs‖ ≤ ρ := norm_meanFactor_le hb0 hb hκ hE hs Zs hr
  set c : ℝ := Cm / W + Cf / Real.sqrt W
  have hc : 0 ≤ c := by positivity
  set a : ℕ → ℝ≥0∞ := fun i => eLpNorm ((alive b E k q K ε W i).indicator fun ω =>
    productValue b E k q W i ω Zs) (ENNReal.ofReal p) (growthPathLaw W b)
  have h0 : a j₀ ≤ ENNReal.ofReal C0' := by
    refine (eLpNorm_indicator_le _ ((measurable_pastCoords W j₀).comap_le _
      (measurableSet_alive b E k q K ε j₀)).nullMeasurableSet).trans ?_
    exact (hC0 W hW0 E hE k j₀ hj₀ (le_trans (by exact_mod_cast hj) hjT) Zs hZ hd).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hstep : ∀ i, j₀ ≤ i → i < j →
      a (i + 1) ≤ ENNReal.ofReal ρ * a i + ENNReal.ofReal c := by
    intro i hi hij
    have hi1 : ((i + 1 : ℕ) : ℝ) ≤ T * W := le_trans (by exact_mod_cast hij) hjT
    have hεi : ε * W ≤ i := le_trans hj₀ (by exact_mod_cast hi)
    have hki : ∀ a, i ≠ k a := fun a => hnb a i hi hij
    have he := (hCM W hWM E hE s hs k Zs hZ hd i hεi hki hi1).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left CM 0) hWpos.le))
    have hξ := (hCF W hWF E hE k Zs hZ hd i hεi hki hi1).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left CF 0) hsW.le))
    exact decay_step (A := alive b E k q K ε W)
      (Z := fun i ω => productValue b E k q W i ω Zs) hp hlam ((measurable_pastCoords W (i + 1)).comap_le _
      (measurableSet_alive b E k q K ε (i + 1))) (measurable_productValue b E k q (i + 1) Zs)
      (alive_succ_subset b E k q K ε i) _ he hξ (by positivity) (by positivity)
  have hfin := geometric_iterate hρ0 hρ1 hc hC0' h0 hstep (j - j₀) (by omega)
  rw [show j₀ + (j - j₀) = j by omega] at hfin
  refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc' : c ≤ (Cm + Cf) * (1 / Real.sqrt W) := by
    have h1 := one_div_le_one_div_sqrt hW1
    have e1 : Cm / W = Cm * (1 / W) := by ring
    have e2 : Cf / Real.sqrt W = Cf * (1 / Real.sqrt W) := by ring
    simp only [c, e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left h1 hCm]
  have hρn : 0 ≤ ρ ^ (j - j₀) := pow_nonneg hρ0 _
  have hs' : 0 ≤ 1 / Real.sqrt W := by positivity
  have hcd : c / (1 - ρ) ≤ (Cm + Cf) / (1 - ρ) * (1 / Real.sqrt W) := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hc' h1ρ.le
  nlinarith [mul_nonneg hD hρn, mul_nonneg hCm hρn, mul_nonneg hCf hρn, mul_nonneg hC0' hs',
    mul_nonneg hCm hs', mul_nonneg hCf hs']

/-- No birth in `[r_j, j)`, `r_j = restartIndex ε W k j`. -/
theorem restart_noBirth (ε : ℝ) (W : ℕ) {nT : ℕ} (k : Fin nT → ℕ) (j : ℕ) :
    ∀ a i, restartIndex ε W k j ≤ i → i < j → i ≠ k a := by
  intro a i hi hij hia
  have hka : k a < j := hia ▸ hij
  have hmem : a ∈ Finset.univ.filter fun a => k a < j := Finset.mem_filter.mpr ⟨by simp, hka⟩
  have h1 : k a + 1 ≤ (Finset.univ.filter fun a => k a < j).sup fun a => k a + 1 :=
    Finset.le_sup (f := fun a => k a + 1) hmem
  have h2 : k a + 1 ≤ restartIndex ε W k j := h1.trans (le_max_right _ _)
  omega

/-- **Decay restarted at the last birth.** -/
theorem decay_restart (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ k : Fin nT → ℕ,
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      ∀ j : ℕ, ε * W ≤ j → (j : ℝ) ≤ T * W →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω => productValue b E k q W j ω Zs)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)) := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨C, ρ, W₀, hC, hρ0, hρ1, h⟩ := decay_all hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T K
    p hε hεT hp
  refine ⟨C, ρ, W₀, hC, hρ0, hρ1, fun W hW E hE k Zs hZ hd hr j hj hjT => ?_⟩
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  obtain ⟨s, hs⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  have hceil : ⌈ε * W⌉₊ ≤ j := Nat.ceil_le.mpr hj
  have hr0 : ε * W ≤ restartIndex ε W k j :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
  exact h W hW E hE s hs k _ hr0 Zs hZ hd hr j (restartIndex_mem_le ε W k hceil).2 hjT
    (restart_noBirth ε W k j)

end BlockBand.SourceProcess.ContractingWords
