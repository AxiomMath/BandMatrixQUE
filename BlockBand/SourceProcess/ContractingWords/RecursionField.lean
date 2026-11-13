module

public import BlockBand.SourceProcess.ContractingWords.Recursion

/-!
# Assembly of the field `recursion`

`recursion_of` has exactly the type of the
field `ContractingWordsEnergyUniformContract.recursion`.

Constants: `ρ = thetaBound b κI` (`|λ| ≤ ρ`), `C_m = max C_mean 0`, `C_f = max C_fluct 0`,
`C₀ = max C_init 0`, `C = C₀ + (C_m + C_f)/(1-ρ) + C_m + C_f`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open scoped ENNReal ComplexConjugate

theorem one_div_le_one_div_sqrt {W : ℕ} (hW : 1 ≤ W) : 1 / (W : ℝ) ≤ 1 / Real.sqrt W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hs1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.mpr hW1
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ W by linarith)
  exact one_div_le_one_div_of_le (by linarith) (by nlinarith)

/-- **The field `recursion`**, from the one-step hypotheses and the Gaussian inputs. -/
theorem recursion_of (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract)
    (hM : WordStepMean) (hF : WordStepFluct) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) → ∀ j₀ : ℕ, ε * W ≤ j₀ → (∀ a, k a < j₀) →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      let μ := growthPathLaw W b
      let lam : ℂ := thetaStar b E s ^ unconjCount Zs * conj (thetaStar b E s) ^ conjCount Zs
      let Z : ℕ → GrowthPath W → ℂ := fun j ω => productValue b E k q W j ω Zs
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      (∀ j : ℕ, j₀ ≤ j → ((j + 1 : ℕ) : ℝ) ≤ T * W → ∃ ξ : GrowthPath W → ℂ,
        Integrable ((A j).indicator ξ) μ ∧
        μ[(A j).indicator ξ | growthSigma W j] =ᵐ[μ] 0 ∧
        eLpNorm ((A j).indicator fun ω => Z (j + 1) ω - lam * Z j ω - ξ ω)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / W) ∧
        eLpNorm ((A j).indicator ξ) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / Real.sqrt W)) ∧
      ∀ j : ℕ, j₀ ≤ j → (j : ℝ) ≤ T * W →
        eLpNorm ((A j).indicator (Z j)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * (ρ ^ (j - j₀) + 1 / Real.sqrt W)) := by
  intro b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨CM, WM, hCM⟩ := hM b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨CF, WF, hCF⟩ := hF b hb0 hb κI hκ nT nI q hq d ε T K p hε hεT hp
  obtain ⟨C0, W0, hC0⟩ := productValue_eLpNorm_le hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T
    p hε hεT hp
  obtain ⟨WI, hWI⟩ := productValue_integrable hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq d ε T
    hε hεT
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
  set C := C0' + (Cm + Cf) / (1 - ρ) + Cm + Cf
  refine ⟨C, ρ, max (max WM WF) (max (max W0 WI) 1), hρ0, hρ1, ?_⟩
  intro W hW E hE s hs k hk j₀ hj₀ hkj₀ Zs hZ hd hr μ lam Z A
  have hWM : WM ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWF : WF ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW0 : W0 ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hW
  have hWI' : WI ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hlam : ‖lam‖ ≤ ρ := norm_meanFactor_le hb0 hb hκ hE hs Zs hr
  have hA : ∀ j, MeasurableSet (A j) := fun j =>
    (measurable_pastCoords W j).comap_le _ (measurableSet_alive b E k q K ε j)
  have hZm : ∀ j, Measurable (Z j) := fun j => measurable_productValue b E k q j Zs
  -- the one-step part, with the Doob centered part
  have hone : ∀ j : ℕ, j₀ ≤ j → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      let ξ : GrowthPath W → ℂ := fun ω => Z (j + 1) ω - μ[Z (j + 1) | growthSigma W j] ω
      Integrable ((A j).indicator ξ) μ ∧
      μ[(A j).indicator ξ | growthSigma W j] =ᵐ[μ] 0 ∧
      eLpNorm ((A j).indicator fun ω => Z (j + 1) ω - lam * Z j ω - ξ ω)
        (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cm / W) ∧
      eLpNorm ((A j).indicator ξ) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cf / Real.sqrt W) := by
    intro j hj hj1 ξ
    have hεj : ε * W ≤ j := le_trans hj₀ (by exact_mod_cast hj)
    have hkj : ∀ a, k a < j := fun a => lt_of_lt_of_le (hkj₀ a) hj
    have hZ1 : Integrable (Z (j + 1)) μ := hWI W hWI' E hE k (j + 1)
      (le_trans hεj (by exact_mod_cast Nat.le_succ j)) hj1 Zs hZ hd
    obtain ⟨hI, hCE⟩ := doob_split ((measurable_pastCoords W j).comap_le)
      (measurableSet_alive b E k q K ε j) hZ1
    refine ⟨hI, hCE, ?_, ?_⟩
    · have e : ((A j).indicator fun ω => Z (j + 1) ω - lam * Z j ω - ξ ω) =
          (alive b E k q K ε W j).indicator fun ω =>
            (growthPathLaw W b)[fun ω' => productValue b E k q W (j + 1) ω' Zs |
              growthSigma W j] ω - meanFactor b E s Zs * productValue b E k q W j ω Zs := by
        congr 1; funext ω; simp only [ξ, Z, lam, meanFactor, μ]; ring
      rw [e]
      exact (hCM W hWM E hE s hs k hk Zs hZ hd hr j hεj hkj hj1).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le))
    · exact (hCF W hWF E hE k hk Zs hZ hd hr j hεj hkj hj1).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hsW.le))
  have hCmC : Cm ≤ C := by simp only [C]; linarith
  have hCfC : Cf ≤ C := by simp only [C]; linarith
  refine ⟨fun j hj hj1 => ?_, fun j hj hjT => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hone j hj hj1
    exact ⟨_, h1, h2, h3.trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right hCmC hWpos.le)),
      h4.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCfC hsW.le))⟩
  -- the decay
  set c : ℝ := Cm / W + Cf / Real.sqrt W
  have hc : 0 ≤ c := by positivity
  set a : ℕ → ℝ≥0∞ := fun i => eLpNorm ((A i).indicator (Z i)) (ENNReal.ofReal p) μ
  have h0 : a j₀ ≤ ENNReal.ofReal C0' := by
    refine (eLpNorm_indicator_le _ (hA j₀).nullMeasurableSet).trans ?_
    exact (hC0 W hW0 E hE k j₀ hj₀ (le_trans (by exact_mod_cast hj) hjT) Zs hZ hd).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hstep : ∀ i, j₀ ≤ i → i < j →
      a (i + 1) ≤ ENNReal.ofReal ρ * a i + ENNReal.ofReal c := by
    intro i hi hij
    have hi1 : ((i + 1 : ℕ) : ℝ) ≤ T * W := le_trans (by exact_mod_cast hij) hjT
    obtain ⟨-, -, he, hξ⟩ := hone i hi hi1
    set ξ : GrowthPath W → ℂ := fun ω => Z (i + 1) ω - μ[Z (i + 1) | growthSigma W i] ω
    have hmono : a (i + 1) ≤ eLpNorm ((A i).indicator (Z (i + 1))) (ENNReal.ofReal p) μ := by
      refine eLpNorm_mono (((hZm (i + 1)).indicator (hA (i + 1))).aestronglyMeasurable)
        fun ω => ?_
      by_cases h : ω ∈ A (i + 1)
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem
          (alive_succ_subset b E k q K ε i h)]
      · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
    have hsplit : (A i).indicator (Z (i + 1)) = lam • (A i).indicator (Z i) +
        (A i).indicator (fun ω => Z (i + 1) ω - lam * Z i ω - ξ ω) + (A i).indicator ξ := by
      funext ω
      by_cases h : ω ∈ A i
      · simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem h, smul_eq_mul]; ring
      · simp [Set.indicator_of_notMem h]
    refine hmono.trans ?_
    rw [hsplit]
    refine (eLpNorm_add_le hp1).trans ?_
    refine (add_le_add_left (eLpNorm_add_le hp1) _).trans ?_
    rw [eLpNorm_const_smul]
    change _ ≤ ENNReal.ofReal ρ * a i + ENNReal.ofReal (Cm / W + Cf / Real.sqrt W)
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ← add_assoc]
    refine add_le_add (add_le_add ?_ he) hξ
    refine mul_le_mul_left ?_ _
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hlam
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
  simp only [C]
  nlinarith [mul_nonneg hD hρn, mul_nonneg hCm hρn, mul_nonneg hCf hρn, mul_nonneg hC0' hs',
    mul_nonneg hCm hs', mul_nonneg hCf hs']

end BlockBand.SourceProcess.ContractingWords
