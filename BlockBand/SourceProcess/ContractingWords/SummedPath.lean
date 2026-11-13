module

public import BlockBand.SourceProcess.ContractingWords.StepSecond
public import BlockBand.SourceProcess.ContractingWords.SummedPins
public import BlockBand.SourceProcess.ContractingWords.AliveLetters
public import BlockBand.SourceProcess.ContractingWords.Moments

/-!
# The summed step on the path: past measurability and the dominating load

* `wordValue_congr`, `measurable_wordValue_past`: `Tr w(j)` is `growthSigma W j`-measurable;
* `domM` `= 1 + Σ_{w∈S}(|Tr w(j)| + |Tr w(j+1)|)` dominates both evaluation points everywhere
  (`dominated_domM`);
* `lintegral_pow_le_of_eLpNorm`: an `L^n` bound `B` gives `E f^n ≤ Bⁿ`. With it,
  `domM_moments` gives `E domM^n ≤ (1 + 2|S|C_n)^n` uniformly (`W ≥ W₀`, `E ∈ bulkInterval κI`,
  `k`, `εW ≤ j`, `j + 1 ≤ TW`, nonempty words of length `≤ d`), from
  `productValue_eLpNorm_le` (under `MatchedTracesContract`, `GaussianAbsorptionContract`,
  `ScalarRecursionContract` and `GaussianLpGradient`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge
open scoped ENNReal

variable {W nT nI : ℕ}

theorem separatorMatrix_congr (b E : ℝ) (j : ℕ) {ω ω' : GrowthPath W}
    (h : pathAt W j ω = pathAt W j ω') (σ : Separator) :
    separatorMatrix b E W j ω σ = separatorMatrix b E W j ω' σ := by
  cases σ <;> simp only [separatorMatrix, scatteringMatrix, boundaryResolvent, fullInverse,
    fullPathMatrix, h]

theorem wordValue_congr (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    {ω ω' : GrowthPath W} (h : pathAt W j ω = pathAt W j ω') (w : TraceWord nT nI) :
    wordValue b E k q W j ω w = wordValue b E k q W j ω' w := by
  simp only [wordValue, letterMatrix_congr b E k q j h, separatorMatrix_congr b E j h]

/-- **Old word values are past-measurable.** -/
theorem measurable_wordValue_past (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (w : TraceWord nT nI) :
    Measurable[growthSigma W j] fun ω : GrowthPath W => wordValue b E k q W j ω w := by
  have e : (fun ω : GrowthPath W => wordValue b E k q W j ω w) =
      (fun ω => wordValue b E k q W j ω w) ∘ extPast W j ∘ pastCoords W j := by
    funext ω
    exact (wordValue_congr b E k q j (pathAt_extPast_le le_rfl ω) w).symm
  rw [e]
  exact ((measurable_wordValue b E k q j w).comp (measurable_extPast j)).comp
    (comap_measurable (pastCoords W j))

theorem growthSigma_le (j : ℕ) :
    growthSigma W j ≤ (inferInstance : MeasurableSpace (GrowthPath W)) := by
  rw [growthSigma_eq_comap]; exact (measurable_pastCoords W j).comap_le

/-- The dominating variable `1 + Σ_{w∈S}(|Tr w(j)| + |Tr w(j+1)|)`. -/
def domM (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ) (S : Finset (TraceWord nT nI))
    (ω : GrowthPath W) : ℝ :=
  1 + ∑ w ∈ S, (‖wordValue b E k q W j ω w‖ + ‖wordValue b E k q W (j + 1) ω w‖)

theorem one_le_domM (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (S : Finset (TraceWord nT nI)) (ω : GrowthPath W) : 1 ≤ domM b E k q j S ω := by
  unfold domM
  have : 0 ≤ ∑ w ∈ S, (‖wordValue b E k q W j ω w‖ + ‖wordValue b E k q W (j + 1) ω w‖) :=
    Finset.sum_nonneg fun _ _ => by positivity
  linarith

theorem measurable_domM (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (S : Finset (TraceWord nT nI)) : Measurable (domM (W := W) b E k q j S) :=
  measurable_const.add (Finset.measurable_sum _ fun w _ =>
    (measurable_wordValue b E k q j w).norm.add (measurable_wordValue b E k q (j + 1) w).norm)

theorem dominated_domM (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (S : Finset (TraceWord nT nI)) :
    Dominated (growthPathLaw W b) S (fun ω => wordValue b E k q W j ω)
      (fun ω => wordValue b E k q W (j + 1) ω) (domM b E k q j S) :=
  Eventually.of_forall fun ω w hw => by
    unfold domM
    have := Finset.single_le_sum (f := fun w => ‖wordValue b E k q W j ω w‖ +
      ‖wordValue b E k q W (j + 1) ω w‖) (fun _ _ => by positivity) hw
    linarith

theorem lintegral_pow_le_of_eLpNorm {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (hfm : AEStronglyMeasurable f μ) {n : ℕ} (hn : 1 ≤ n)
    {B : ℝ≥0∞} (h : eLpNorm f (n : ℝ≥0∞) μ ≤ B) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ^ n ∂μ ≤ B ^ n := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by simp; omega
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hn0 (ENNReal.natCast_ne_top n) hfm] at h
  have hnr : ((n : ℝ≥0∞)).toReal = n := by simp
  rw [hnr] at h
  have e : ∫⁻ ω, ‖f ω‖ₑ ^ (n : ℝ) ∂μ = ∫⁻ ω, ENNReal.ofReal (f ω) ^ n ∂μ :=
    lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal (hf ω), ENNReal.rpow_natCast]
  rw [e] at h
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc ∫⁻ ω, ENNReal.ofReal (f ω) ^ n ∂μ =
      ((∫⁻ ω, ENNReal.ofReal (f ω) ^ n ∂μ) ^ (1 / (n : ℝ))) ^ (n : ℝ) := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hpos.ne', ENNReal.rpow_one]
    _ ≤ B ^ (n : ℝ) := ENNReal.rpow_le_rpow h hpos.le
    _ = B ^ n := ENNReal.rpow_natCast _ _

end BlockBand.SourceProcess.ContractingWords
