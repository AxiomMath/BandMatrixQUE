module

public import BlockBand.SourceProcess.PhysApprox.B3BoundJet1
public import BlockBand.SourceProcess.PhysApprox.B3BridgesJet
public import BlockBand.SourceProcess.PhysApprox.B3DecayStep
public import BlockBand.SourceProcess.PhysApprox.B3CovRepDecay
public import BlockBand.SourceProcess.PhysApprox.B3DecayDrift

/-!
# The closed layer error and the contracting decay at bounded order

* `ClosedErrLpLe P e`, `B3DecayIn.B3ClosedJetLpLe P`, `B3ClosedContrStepMeanLe P`,
  `B3ClosedContrStepFluctLe P`, `B3ClosedContrDecayLe P`: the original statements with `p ≤ P`;
* `closedErrLpLe_of_jets`, `b3ClosedJetLpLe_of_closedErrLp`, **`b3ClosedJetLpLe_of_jets`**;
* `B3DecayIn.b3ClosedContrStepMeanLe_of_layer`, `…StepFluctLe_of_layer`,
  `b3ClosedContrDecayLe_of_steps`, **`B3DecayIn.b3ClosedContrDecayLe_of_gaussianInputs`**;
* the consumers, with their original conclusions: **`covDecayHyp_b3CovZ_of_le`**
  (`CovDecayHyp b3CovZ`), **`kDriftSummed_of_decayLe`** (`KDriftSummed`),
  **`genReqGramDrift_of_decayLe`** (`GenReqGramDrift`), and the step forms `kStepDrift_of_decayLe`,
  `gramSumStepDrift_of_decayLe`;
* **`b3ClosedContrDecayLe_of_frac4`**: `B3ClosedContrDecayLe 4` from the contract hypotheses,
  `B3ClosedContrLayerForm`, `ClosedShiftDiscTrace`, `FarFracTraceMoments4` and the conductance
  `ClosedCondLpLe 4`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## Bounded restatements
-/

/-- **`ClosedErrLp e` at the orders `1 ≤ p ≤ P`.** -/
def ClosedErrLpLe (P : ℝ) (e : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (e b E np τ m s h K W (Vs W) j))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **The contracting step mean `B3ClosedContrStepMean` at the orders `1 ≤ p ≤ P`.** -/
def B3ClosedContrStepMeanLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P →
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
      ∃ lam : ℂ, ‖lam‖ ≤ ρ ∧
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          (closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y -
            lam * b3ContrCoord b E s h τ m W j (Vs W) σ k l y))
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **The contracting step fluctuation `B3ClosedContrStepFluct` at the orders `1 ≤ p ≤ P`.** -/
def B3ClosedContrStepFluctLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P →
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
          b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l y -
            (closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y))
        (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / Real.sqrt W)

/-- **`B3ClosedContrDecay` at the orders `1 ≤ p ≤ P`.** -/
def B3ClosedContrDecayLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P →
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
    ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3ContrCoord b E s h τ m W j (Vs W) σ k l)) (ENNReal.ofReal p) (closedLaw b W np) ≤
        ENNReal.ofReal (C * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

theorem closedErrLpLe_of {e : CovField} (h : ClosedErrLp e) (P : ℝ) : ClosedErrLpLe P e :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

theorem b3ClosedContrDecayLe_of (h : B3ClosedContrDecay) (P : ℝ) : B3ClosedContrDecayLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

/-!
## The closed layer error
-/

/-- **`ClosedErrLpLe P b3CovErr` from the three closed jet estimates at the same orders** (Minkowski;
adapted from `closedErrLp_of_jets`). -/
theorem closedErrLpLe_of_jets {P : ℝ} (h0 : ClosedJet0LpLe P) (h1 : ClosedJet1LpLe P)
    (hg : ClosedCondLpLe P) : ClosedErrLpLe P b3CovErr := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨C0, hC0, hev0⟩ := h0 b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨C1, hC1, hev1⟩ := h1 b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨Cg, hCg, hevg⟩ := hg b E np τ m T s h K Vs hFD R p hp hpP
  refine ⟨C0 + C1 + Cg + 1, by positivity, ?_⟩
  filter_upwards [hev0, hev1, hevg, hFD.2.2.2.2.2] with W hW0 hW1 hWg hVW j hj
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j (Vs W)
  have hsplit := indicator_b3CovErr_split b E np τ m s h K W (Vs W) j A
  have hconst : eLpNorm (A.indicator (fun _ => (W : ℝ)⁻¹)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (W : ℝ)⁻¹ := by
    refine (eLpNorm_indicator_le _
      (nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j hV)).trans (le_of_eq ?_)
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr (by linarith)).ne' (NeZero.ne μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg (by positivity)]
  have hg' : eLpNorm ((W : ℝ)⁻¹ • A.indicator (fun y => conductanceOf
      (passiveTransmission b E (b3ClosedX b E s h τ m W j y))))
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (W : ℝ)⁻¹ * ENNReal.ofReal Cg := by
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity)]
    gcongr
    exact hWg j hj
  rw [hsplit]
  refine (eLpNorm_add4_le hp1 _ _ _ _).trans ?_
  calc _ ≤ ENNReal.ofReal (C0 / W) + ENNReal.ofReal (C1 / W) +
        ENNReal.ofReal (W : ℝ)⁻¹ * ENNReal.ofReal Cg + ENNReal.ofReal (W : ℝ)⁻¹ :=
        add_le_add (add_le_add (add_le_add (hW0 j hj) (hW1 j hj)) hg') hconst
    _ = ENNReal.ofReal ((C0 + C1 + Cg + 1) / W) := cov_err_arith hC0 hC1 hCg

end BlockBand.SourceProcess.PhysApprox.B3

namespace BlockBand.SourceProcess.PhysApprox.B3DecayIn

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.PhysApprox.B3
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.FullSourceStops
open scoped NNReal ENNReal

/-- **`B3ClosedJetLp` at the orders `1 ≤ p ≤ P`.** -/
def B3ClosedJetLpLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ Cj : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ sj : ℂ, IsStationaryJet b E sj →
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator fun y =>
          b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)) (ENNReal.ofReal p)
        (closedLaw b W np) ≤ ENNReal.ofReal (Cj / W)

theorem b3ClosedJetLpLe_of (h : B3ClosedJetLp) (P : ℝ) : B3ClosedJetLpLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

end BlockBand.SourceProcess.PhysApprox.B3DecayIn

namespace BlockBand.SourceProcess.PhysApprox.B3

section BridgeJet

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder

/-- **The jet bridge at bounded order** (adapted from `b3ClosedJetLp_of_closedErrLp`). -/
theorem b3ClosedJetLpLe_of_closedErrLp {P : ℝ} (hE : ClosedErrLpLe P b3CovErr)
    (hP : B3ClosedXPassive) : B3DecayIn.B3ClosedJetLpLe P := by
  intro b E np τ m T s h K Vs hD R p hp hpP
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hD.1
  have hη : 0 ≤ etaZ b E :=
    (Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2).le
  obtain ⟨C, -, hev⟩ := hE b E np τ m T s h K Vs hD R p hp hpP
  refine ⟨C, ?_⟩
  filter_upwards [hev, hP b E np τ m T s h K Vs hD] with W hW hPW j hj sj hsj
  refine le_of_eq_of_le (eLpNorm_congr_ae ?_) (hW j hj)
  filter_upwards [hPW j (Finset.mem_filter.1 hj).1] with y hy
  by_cases hA : y ∈ b3Alive b E s h τ m R W j (Vs W)
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    simp only [b3CovErr, B3DecayIn.b3LayerErr, b3LayerErrX, b3Jet_eq hb0 hb hE1 hE2 hsj,
      abs_of_nonneg (FullSourceCovariance.conductance_nonneg b E hη hy)]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]

/-- **`B3ClosedJetLpLe P` from the three closed jet estimates at the same orders** and the step-form
hypothesis. -/
theorem b3ClosedJetLpLe_of_jets {P : ℝ} (h0 : ClosedJet0LpLe P) (h1 : ClosedJet1LpLe P)
    (hg : ClosedCondLpLe P) (hF : ClosedKStepForm b3ClosedX) : B3DecayIn.B3ClosedJetLpLe P :=
  b3ClosedJetLpLe_of_closedErrLp (closedErrLpLe_of_jets h0 h1 hg)
    (b3ClosedXPassive_of_stepForm hF)

end BridgeJet

end BlockBand.SourceProcess.PhysApprox.B3

namespace BlockBand.SourceProcess.PhysApprox.B3DecayIn

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.PhysApprox.B3
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.FullSourceStops
open scoped NNReal ENNReal

variable {W np : ℕ}

/-!
## The contracting step mean and fluctuation at bounded order
-/

/-- **The contracting step mean at bounded order** (adapted from
`b3ClosedContrStepMean_of_layer`). -/
theorem b3ClosedContrStepMeanLe_of_layer {P : ℝ} (hL : LayerFreshBound)
    (hI : B3ClosedContrLayerForm) (hJ : B3ClosedJetLpLe P) : B3ClosedContrStepMeanLe P := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, -, -, hVs⟩ := id hFD
  have hb1 : b < 1 := by linarith
  obtain ⟨Kl, c₀, hKl, hc₀, hev⟩ := hI b E np τ m T s h K Vs hFD R
  obtain ⟨Cj, hevJ⟩ := hJ b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨hκ, hEb⟩ := bulk_of_lt hE1 hE2
  set κ := min (2 + E) (2 - E) / 2
  obtain ⟨sj, hsj⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  obtain ⟨hρ0, hρ1, -⟩ := thetaStar_bulk_bound hb0 hb hκ
  obtain ⟨CL, WL, hCL, hLb⟩ := hL b hb0 hb κ hκ 1 p Kl c₀ hp hKl hc₀
  refine ⟨2 * CL * max Cj 0, thetaBound b κ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hev, hevJ, hVs, eventually_ge_atTop WL, eventually_ge_atTop 1]
    with W hW hWJ hVW hWL hW1 j hj σ k l
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hVσ : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVσ.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  obtain ⟨nT, nI, XX, A, c, Zs, wt, hF⟩ := hW j hj σ k l
  obtain ⟨h1, h2⟩ := closedLayer_ae hb1 hE1 hE2 hjc hVσ hF
  obtain ⟨-, -, -, -, hXXh, hAh, hAn, hc, hZ, hd, hr, hu, hcc, hwt, -, hform⟩ := hF
  set lam := meanFactor b E sj (Zs 0)
  have hlam1 : meanFactor b E sj (Zs 1) = lam := by simp only [lam, meanFactor, hu, hcc]
  refine ⟨lam, norm_meanFactor_le hb0 hb hκ hEb hsj (Zs 0) hr, ?_⟩
  set μ := closedLaw b W np
  set Al := b3Alive b E s h τ m R W j (Vs W)
  have hAlM := b3Alive_ae_eq (np := np) hb1 hE1 hE2 s h τ m R W j (Vs W)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  set err : ProbedPath W np × ℝ → ℝ := Al.indicator fun y =>
    b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
  have herr0 : ∀ y, 0 ≤ err y := fun y => Set.indicator_nonneg
    (fun y _ => b3LayerErr_nonneg b E sj W _) y
  have hLHSm : AEStronglyMeasurable (Al.indicator fun y =>
      μ[Al.indicator (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y -
        lam * b3ContrCoord b E s h τ m W j (Vs W) σ k l y) μ :=
    genMem_aesm_indicator hb1 hE1 hE2 s h τ m R W j hmV
      ((stronglyMeasurable_condExp.mono (b3Sigma_le j)).measurable.sub
        ((measurable_b3ContrCoord b E s h τ m W j hmV σ k l).const_mul _))
  have hpt : ∀ᵐ y ∂μ, ‖Al.indicator (fun y =>
      μ[Al.indicator (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y -
        lam * b3ContrCoord b E s h τ m W j (Vs W) σ k l y) y‖ ≤ 2 * CL * err y := by
    filter_upwards [h2, hAlM.mem_iff, hform] with y hy2 hy hf
    by_cases hya : y ∈ Al
    · obtain ⟨hX, -, hQ⟩ := hf hya
      rw [Set.indicator_of_mem hya, hy2, aliveWt, Set.indicator_of_mem (hy.1 hya), one_mul, hQ]
      have hb' : ∀ t, Integrable (fun F => b3LayerVal b E (A y) c (XX y) F (Zs t))
          (freshLaw W b) ∧
          ‖∫ F, b3LayerVal b E (A y) c (XX y) F (Zs t) ∂freshLaw W b -
              meanFactor b E sj (Zs t) * coreProd (A y) (sepOf b E (XX y)) (Zs t)‖ ≤
            CL * b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y) := by
        intro t
        have hl := hLb W hWL E hEb sj hsj (XX y) (hXXh y) nT nI (A y) c (hAh y) (hAn y) hc
          (Zs t) (hZ t) (hd t)
        refine ⟨hl.1, hl.2.1.trans (mul_le_mul_of_nonneg_left ?_ hCL)⟩
        rw [← hX]
        have hg : conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) (XX y))) /
            W ≤ |conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) (XX y)))| /
              W := div_le_div_of_nonneg_right (le_abs_self _) hWpos.le
        simp only [b3LayerErr]; linarith
      obtain ⟨hi0, hm0⟩ := hb' 0
      obtain ⟨hi1, hm1⟩ := hb' 1
      rw [hlam1] at hm1
      have hsum : ∫ F, layerSum b E XX A c Zs wt y F ∂freshLaw W b =
          wt 0 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b +
            wt 1 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b := by
        simp only [layerSum, Fin.sum_univ_two]
        rw [integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul,
          integral_const_mul]
      rw [hsum, Fin.sum_univ_two, show err y = b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
        from Set.indicator_of_mem hya _]
      have e : wt 0 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b +
            wt 1 * ∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b -
          lam * (wt 0 * coreProd (A y) (sepOf b E (XX y)) (Zs 0) +
            wt 1 * coreProd (A y) (sepOf b E (XX y)) (Zs 1)) =
          wt 0 * (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b -
              lam * coreProd (A y) (sepOf b E (XX y)) (Zs 0)) +
            wt 1 * (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b -
              lam * coreProd (A y) (sepOf b E (XX y)) (Zs 1)) := by ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have hn0 := norm_nonneg (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 0) ∂freshLaw W b -
        lam * coreProd (A y) (sepOf b E (XX y)) (Zs 0))
      have hn1 := norm_nonneg (∫ F, b3LayerVal b E (A y) c (XX y) F (Zs 1) ∂freshLaw W b -
        lam * coreProd (A y) (sepOf b E (XX y)) (Zs 1))
      have hw0 := hwt 0
      have hw1 := hwt 1
      have := norm_nonneg (wt 0)
      have := norm_nonneg (wt 1)
      nlinarith
    · rw [Set.indicator_of_notMem hya, norm_zero]
      exact mul_nonneg (by positivity) (herr0 y)
  refine (eLpNorm_mono_ae_real hLHSm hpt).trans ?_
  have e : (fun y => 2 * CL * err y) = (2 * CL) • err := by funext y; simp [smul_eq_mul]
  have hC2 : 0 ≤ 2 * CL := by positivity
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hC2]
  calc ENNReal.ofReal (2 * CL) * eLpNorm err (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * CL) * ENNReal.ofReal (max Cj 0 / W) := by
        gcongr
        exact (hWJ j hj sj hsj).trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le))
    _ = ENNReal.ofReal (2 * CL * max Cj 0 / W) := by
        rw [← ENNReal.ofReal_mul hC2, mul_div_assoc]

/-- **The contracting step fluctuation at bounded order** (adapted from
`b3ClosedContrStepFluct_of_layer`). -/
theorem b3ClosedContrStepFluctLe_of_layer {P : ℝ} (hL : LayerFreshBound)
    (hI : B3ClosedContrLayerForm) (hJ : B3ClosedJetLpLe P) : B3ClosedContrStepFluctLe P := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, -, -, hVs⟩ := id hFD
  have hb1 : b < 1 := by linarith
  obtain ⟨Kl, c₀, hKl, hc₀, hev⟩ := hI b E np τ m T s h K Vs hFD R
  obtain ⟨Cj, hevJ⟩ := hJ b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨hκ, hEb⟩ := bulk_of_lt hE1 hE2
  set κ := min (2 + E) (2 - E) / 2
  obtain ⟨sj, hsj⟩ := BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb hE1 hE2
  obtain ⟨CL, WL, hCL, hLb⟩ := hL b hb0 hb κ hκ 1 p Kl c₀ hp hKl hc₀
  refine ⟨2 * CL * (1 + max Cj 0), by positivity, ?_⟩
  filter_upwards [hev, hevJ, hVs, eventually_ge_atTop WL, eventually_ge_atTop 1]
    with W hW hWJ hVW hWL hW1 j hj σ k l
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hVσ : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVσ.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun ω => growth_fun_extPast hjc hVσ ω
  obtain ⟨nT, nI, XX, A, c, Zs, wt, hF⟩ := hW j hj σ k l
  obtain ⟨h1, h2⟩ := closedLayer_ae hb1 hE1 hE2 hjc hVσ hF
  obtain ⟨hXXm, hAm, hXXi, hAi, hXXh, hAh, hAn, hc, hZ, hd, -, -, -, hwt, -, hform⟩ := hF
  set μ := closedLaw b W np
  set Al := b3Alive b E s h τ m R W j (Vs W)
  set AM := b3AliveM b E s h τ m R W j (Vs W)
  have hAMm : MeasurableSet AM := measurableSet_b3AliveM b E s h τ m R W j hmV
  have hAlM := b3Alive_ae_eq (np := np) hb1 hE1 hE2 s h τ m R W j (Vs W)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  set wA := aliveWt b E s h τ m R W j (Vs W)
  set S := layerSum b E XX A c Zs wt
  have hwA : ∀ y, wA (b3Ext W j y) = wA y := aliveWt_b3Ext hjc hVinv
  have hSi : ∀ y, S (b3Ext W j y) = S y := layerSum_b3Ext b E hXXi hAi
  -- the centred function
  set Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => wA (b3Rebuild W j z.1) *
      (S (b3Rebuild W j z.1) z.2 - ∫ F, S (b3Rebuild W j z.1) F ∂freshLaw W b) with hΦdef
  have hSm := measurable_layerSum_rebuild (j := j) (Zs := Zs) (wt := wt) (c := c) b E hXXm hAm
  have hΦ : Measurable Φ :=
    ((measurable_aliveWt b E s h τ m R j hmV).comp
      ((measurable_b3Rebuild (np := np) W j).comp measurable_fst)).mul
      (hSm.sub ((hSm.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable.comp
        measurable_fst))
  have hgΦ : (Al.indicator fun y => b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l y -
      μ[Al.indicator (b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l) | b3Sigma W j np] y)
      =ᵐ[μ] fun y => Φ (b3Past W j y, freshSample W j y.1.1) := by
    filter_upwards [h1, h2, hAlM.mem_iff] with y hy1 hy2 hy
    simp only [hΦdef, b3Rebuild_b3Past, hwA, hSi]
    by_cases hya : y ∈ Al
    · have hyM := hy.1 hya
      have hw : wA y = 1 := Set.indicator_of_mem hyM _
      rw [Set.indicator_of_mem hya] at hy1 ⊢
      rw [hy2, hy1, hw, one_mul, one_mul, one_mul]
    · have hyM : y ∉ AM := fun h' => hya (hy.2 h')
      have hw : wA y = 0 := Set.indicator_of_notMem hyM _
      rw [Set.indicator_of_notMem hya, hw, zero_mul]
  -- the fresh bound
  set H : ProbedPath W np × ℝ → ℝ := AM.indicator fun y =>
    2 * CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) with hHdef
  have hH0 : ∀ y, 0 ≤ H y := fun y => Set.indicator_nonneg (fun y _ => by
    have : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)) := by
      simp only [jetDistance0]; positivity
    positivity) y
  have hb' : ∀ x, eLpNorm (fun F => Φ (x, F)) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (H (b3Rebuild W j x)) := by
    intro x
    set y := b3Rebuild W j x
    by_cases hyM : y ∈ AM
    · have hw : wA y = 1 := Set.indicator_of_mem hyM _
      have hl : ∀ t, Integrable (fun F => b3LayerVal b E (A y) c (XX y) F (Zs t))
          (freshLaw W b) ∧
          eLpNorm (fun F => b3LayerVal b E (A y) c (XX y) F (Zs t) -
              ∫ F', b3LayerVal b E (A y) c (XX y) F' (Zs t) ∂freshLaw W b)
            (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal (CL * (1 / Real.sqrt W +
              jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)))) := fun t => by
        have hl := hLb W hWL E hEb sj hsj (XX y) (hXXh y) nT nI (A y) c (hAh y) (hAn y) hc
          (Zs t) (hZ t) (hd t)
        exact ⟨hl.1, hl.2.2⟩
      obtain ⟨hi0, hf0⟩ := hl 0
      obtain ⟨hi1, hf1⟩ := hl 1
      have hfun : (fun F => Φ (x, F)) =
          wt 0 • (fun F => b3LayerVal b E (A y) c (XX y) F (Zs 0) -
              ∫ F', b3LayerVal b E (A y) c (XX y) F' (Zs 0) ∂freshLaw W b) +
            wt 1 • (fun F => b3LayerVal b E (A y) c (XX y) F (Zs 1) -
              ∫ F', b3LayerVal b E (A y) c (XX y) F' (Zs 1) ∂freshLaw W b) := by
        funext F
        simp only [hΦdef, S, layerSum, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        rw [hw, integral_add (hi0.const_mul _) (hi1.const_mul _), integral_const_mul,
          integral_const_mul]
        ring
      rw [hfun]
      refine (eLpNorm_add_le hp1).trans ?_
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
      have hw0 : ‖wt 0‖ₑ ≤ 1 := by rw [← ofReal_norm, ← ENNReal.ofReal_one];
                                    exact ENNReal.ofReal_le_ofReal (hwt 0)
      have hw1 : ‖wt 1‖ₑ ≤ 1 := by rw [← ofReal_norm, ← ENNReal.ofReal_one];
                                    exact ENNReal.ofReal_le_ofReal (hwt 1)
      have hHy : H y = 2 * CL * (1 / Real.sqrt W +
          jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) := Set.indicator_of_mem hyM _
      have hj0 : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)) := by
        simp only [jetDistance0]; positivity
      have hD0 : 0 ≤ CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) :=
        by positivity
      rw [hHy, show 2 * CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y)))
        = CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) +
          CL * (1 / Real.sqrt W + jetDistance0 b E (nearSchur (boundaryZ b E) (XX y))) by ring,
        ENNReal.ofReal_add hD0 hD0]
      gcongr
      · exact (mul_le_mul' hw0 hf0).trans (by rw [one_mul])
      · exact (mul_le_mul' hw1 hf1).trans (by rw [one_mul])
    · have hw : wA y = 0 := Set.indicator_of_notMem hyM _
      have hfun : (fun F => Φ (x, F)) = 0 := by
        funext F; simp only [hΦdef, Pi.zero_apply]; rw [hw, zero_mul]
      rw [hfun, eLpNorm_zero]
      exact zero_le
  have hfr := eLpNorm_fresh_le b j hp hΦ hH0 hb'
  have hHinv : (fun y => H (b3Ext W j y)) = H := by
    funext y
    have hiff := mem_b3AliveM_b3Ext b E s h τ m R hjc le_rfl hVinv y
    by_cases hyM : y ∈ AM
    · rw [hHdef, Set.indicator_of_mem hyM, Set.indicator_of_mem (show b3Ext W j y ∈ AM from
        hiff.2 hyM), hXXi]
    · have hyM' : b3Ext W j y ∉ AM := fun h' => hyM (hiff.1 h')
      rw [hHdef, Set.indicator_of_notMem hyM, Set.indicator_of_notMem hyM']
  rw [hHinv] at hfr
  rw [eLpNorm_congr_ae hgΦ]
  refine hfr.trans ?_
  -- `H ≤ 2CL/√W + 2CL·1_{A}err`
  set err : ProbedPath W np × ℝ → ℝ := Al.indicator fun y =>
    b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
  have herr0 : ∀ y, 0 ≤ err y := fun y => Set.indicator_nonneg
    (fun y _ => b3LayerErr_nonneg b E sj W _) y
  have hHm : AEStronglyMeasurable H μ :=
    (Measurable.indicator (measurable_const.mul (measurable_const.add
      ((BlockBand.Transmission.PathScalar.measurable_jetDistance0 b E).comp
        (FullSource.measurable_nearSchur_comp _ hXXm)))) hAMm).aestronglyMeasurable
  have hpt : ∀ᵐ y ∂μ, ‖H y‖ ≤ 2 * CL * (1 / Real.sqrt W) + 2 * CL * err y := by
    filter_upwards [hAlM.mem_iff, hform] with y hy hf
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 y)]
    by_cases hya : y ∈ Al
    · have hyM := hy.1 hya
      rw [hHdef, Set.indicator_of_mem hyM, show err y = b3LayerErr b E sj W
        (b3ClosedX b E s h τ m W j y) from Set.indicator_of_mem hya _, (hf hya).1]
      have := jetDistance0_le_b3LayerErr b E sj W (b3ClosedX b E s h τ m W j y)
      nlinarith
    · have hyM : y ∉ AM := fun h' => hya (hy.2 h')
      rw [hHdef, Set.indicator_of_notMem hyM]
      have := herr0 y
      positivity
  refine (eLpNorm_mono_ae_real hHm hpt).trans ?_
  have hC2 : 0 ≤ 2 * CL := by positivity
  have hsplit : (fun y => 2 * CL * (1 / Real.sqrt W) + 2 * CL * err y) =
      (fun _ => 2 * CL * (1 / Real.sqrt W)) + (2 * CL) • err := by
    funext y; simp [smul_eq_mul]
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC2, eLpNorm_const _ (by positivity)
    (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow, mul_one,
    Real.enorm_eq_ofReal (by positivity)]
  have hjet := hWJ j hj sj hsj
  have hWs : (1 : ℝ) / W ≤ 1 / Real.sqrt W := by
    have h1 : Real.sqrt W ≤ W := by
      have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      have := Real.sqrt_le_sqrt (show (W : ℝ) ≤ W * W by nlinarith)
      rwa [Real.sqrt_mul_self hWpos.le] at this
    exact one_div_le_one_div_of_le hsq h1
  calc ENNReal.ofReal (2 * CL * (1 / Real.sqrt W)) +
        ENNReal.ofReal (2 * CL) * eLpNorm err (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * CL * (1 / Real.sqrt W)) +
          ENNReal.ofReal (2 * CL) * ENNReal.ofReal (max Cj 0 / W) := by
        gcongr
        exact hjet.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le))
    _ = ENNReal.ofReal (2 * CL * (1 / Real.sqrt W) + 2 * CL * (max Cj 0 / W)) := by
        rw [← ENNReal.ofReal_mul hC2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (2 * CL * (1 + max Cj 0) / Real.sqrt W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hm0 : 0 ≤ max Cj 0 := le_max_right _ _
        have e1 : max Cj 0 / W = max Cj 0 * (1 / W) := by ring
        have e2 : 2 * CL * (1 + max Cj 0) / Real.sqrt W =
            2 * CL * (1 / Real.sqrt W) + 2 * CL * (max Cj 0 * (1 / Real.sqrt W)) := by ring
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_left hWs hm0
        nlinarith

end BlockBand.SourceProcess.PhysApprox.B3DecayIn

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## The decay at bounded order
-/

/-- **The decay at bounded order** from the one-step estimates and the bound
`B3ClosedContrBound` (adapted from
`b3ClosedContrDecay_of_steps`). -/
theorem b3ClosedContrDecayLe_of_steps {P : ℝ} (hM : B3ClosedContrStepMeanLe P)
    (hF : B3ClosedContrStepFluctLe P) (hB : B3ClosedContrBound) : B3ClosedContrDecayLe P := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevM⟩ := hM b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨C₂, hC₂, hevF⟩ := hF b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨C₀, hC₀, hevB⟩ := hB b E np τ m T s h K Vs hFD R
  obtain ⟨hD, -, -, -, -, hVs⟩ := id hFD
  have hb1 : b < 1 := by linarith [hD.2.1]
  have h1ρ : 0 < 1 - ρ := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  refine ⟨C₀ + (C₁ + C₂) / (1 - ρ), ρ, add_nonneg hC₀ (div_nonneg (add_nonneg hC₁ hC₂) h1ρ.le),
    hρ0, hρ1, ?_⟩
  filter_upwards [hevM, hevF, hevB, hVs, eventually_ge_atTop 1]
    with W hWM hWF hWB hVW hW1 j hj hjT σ k l
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
  set μ := closedLaw b W np
  set a : ℕ → ℝ≥0∞ := fun i => eLpNorm ((b3Alive b E s h τ m R W i (Vs W)).indicator
    (b3ContrCoord b E s h τ m W i (Vs W) σ k l)) (ENNReal.ofReal p) μ
  set c : ℝ := C₁ / W + C₂ / Real.sqrt W
  have hc1 : 0 ≤ C₁ / W := div_nonneg hC₁ hWpos.le
  have hc2 : 0 ≤ C₂ / Real.sqrt W := div_nonneg hC₂ hsq.le
  have hc : 0 ≤ c := add_nonneg hc1 hc2
  obtain ⟨hrR, hrj, hsr⟩ := lastRestart_spec s τ hj
  set r := lastRestart s τ W j
  have h0 : a r ≤ ENNReal.ofReal C₀ := by
    refine (eLpNorm_le_of_ae_bound (aestronglyMeasurable_contr hb1 hD.2.2.1 hD.2.2.2.1 s h τ m
      R W r hmV r σ k l) (hWB r hsr (hrj.trans hjT) σ k l)).trans (le_of_eq ?_)
    rw [measure_univ, ENNReal.one_rpow, one_mul]
  have hstep : ∀ i, r ≤ i → i < j → a (i + 1) ≤ ENNReal.ofReal ρ * a i + ENNReal.ofReal c := by
    intro i hri hij
    have hiS : i ∈ genNoBirthSteps s T τ W := by
      simp only [genNoBirthSteps, mem_filter, mem_Ico]
      exact ⟨⟨hsr.trans hri, by omega⟩, not_birth_of_lastRestart s τ hri hij⟩
    obtain ⟨lam, hlam, hmean⟩ := hWM i hiS σ k l
    have hfl := hWF i hiS σ k l
    refine (decay_minkowski_step hp1 (genMem_b3Alive_succ_subset b E s h τ m R W i (Vs W))
      (Z := b3ContrCoord b E s h τ m W i (Vs W) σ k l)
      (Y := fun y => μ[(b3Alive b E s h τ m R W i (Vs W)).indicator
        (b3ContrCoord b E s h τ m W (i + 1) (Vs W) σ k l) | b3Sigma W i np] y) lam
      (aestronglyMeasurable_contr hb1 hD.2.2.1 hD.2.2.2.1 s h τ m R W (i + 1) hmV (i + 1)
        σ k l)).trans ?_
    rw [show ENNReal.ofReal c = ENNReal.ofReal (C₁ / W) + ENNReal.ofReal (C₂ / Real.sqrt W) from
      ENNReal.ofReal_add hc1 hc2, ← add_assoc]
    refine add_le_add (add_le_add ?_ hmean) hfl
    refine mul_le_mul' ?_ le_rfl
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hlam
  have hfin := ContractingWords.geometric_iterate hρ0 hρ1 hc hC₀ h0 hstep (j - r) (by omega)
  rw [show r + (j - r) = j by omega] at hfin
  refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
  have hrate : ρ ^ (j - r) ≤ genStepRate ρ s τ W j := pow_le_genStepRate hρ0 s τ W hrR hrj
  have hw : (1 : ℝ) / W ≤ 1 / Real.sqrt W := by
    have h1 : Real.sqrt W ≤ W := by
      have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
      have := Real.sqrt_le_sqrt (show (W : ℝ) ≤ W * W by nlinarith)
      rwa [Real.sqrt_mul_self hWpos.le] at this
    exact one_div_le_one_div_of_le hsq h1
  have hc' : c ≤ (C₁ + C₂) * (1 / Real.sqrt W) := by
    have e1 : C₁ / W = C₁ * (1 / W) := by ring
    have e2 : C₂ / Real.sqrt W = C₂ * (1 / Real.sqrt W) := by ring
    simp only [c, e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hw hC₁]
  have hcd : c / (1 - ρ) ≤ (C₁ + C₂) / (1 - ρ) * (1 / Real.sqrt W) := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hc' h1ρ.le
  have hD' : 0 ≤ (C₁ + C₂) / (1 - ρ) := div_nonneg (add_nonneg hC₁ hC₂) h1ρ.le
  have hs' : 0 ≤ 1 / Real.sqrt W := by positivity
  have hr0 : 0 ≤ genStepRate ρ s τ W j := genStepRate_nonneg hρ0 s τ W j
  nlinarith [mul_le_mul_of_nonneg_left hrate hC₀, mul_nonneg hD' hr0, mul_nonneg hC₀ hs', hcd]

/-!
## The consumers of the decay
-/

/-- **The decay of the contracting sum at the orders `1 ≤ p ≤ P`** (adapted from
`covDecayHypP_b3CovZ`). -/
theorem covDecayHypPLe_b3CovZ {P : ℝ} (hD : B3ClosedContrDecayLe P) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P →
      ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
        eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
            (b3CovZ b E np τ m s h K W (Vs W) j)) (ENNReal.ofReal p) (closedLaw b W np) ≤
          ENNReal.ofReal (C * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hD b E np τ m T s h K Vs hFD R p hp hpP
  set N : ℝ := (Fintype.card (Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np)) : ℝ) with hNdef
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨N * C, ρ, mul_nonneg hN hC, hρ0, hρ1, ?_⟩
  filter_upwards [hev] with W hW j hj1 hj2
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set r : ℝ := genStepRate ρ s τ W j + 1 / Real.sqrt W
  have hr : 0 ≤ r := add_nonneg (genStepRate_nonneg hρ0 s τ W j) (by positivity)
  rw [indicator_b3CovZ]
  refine (eLpNorm_sum_le hp1).trans ?_
  have hterm : ∀ x : Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np),
      eLpNorm (fun y => ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3ContrCoord b E s h τ m W j (Vs W) x.1 x.2.1 x.2.2) y‖) (ENNReal.ofReal p)
          (closedLaw b W np) ≤ ENNReal.ofReal (C * r) := by
    intro x
    have hx := hW j hj1 hj2 x.1 x.2.1 x.2.2
    have hm := aestronglyMeasurable_of_eLpNorm_ne_top (hx.trans_lt ENNReal.ofReal_lt_top).ne
    rw [eLpNorm_norm _ hm]
    exact hx
  refine (Finset.sum_le_sum fun x _ => hterm x).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc,
    ENNReal.ofReal_mul hN, hNdef, ENNReal.ofReal_natCast]

/-- **`CovDecayHyp b3CovZ` (an `L⁴` statement) from the decay at the orders `≤ 4`.** -/
theorem covDecayHyp_b3CovZ_of_le (hD : B3ClosedContrDecayLe 4) : CovDecayHyp b3CovZ := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := covDecayHypPLe_b3CovZ hD b E np τ m T s h K Vs hFD R 4
    (by norm_num) le_rfl
  refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
  filter_upwards [hev] with W hW j hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj
  have := hW j hj.1.1 hj.1.2.le
  rwa [ENNReal.ofReal_ofNat] at this

/-- The per-step `SummedStep` bound from the layer structure and the decay at `p = 2` (adapted
from `b3_stepBound_of_layer_decay`; the decay is used only at `p = 2 ≤ 4`). -/
theorem b3_stepBound_of_layer_decayLe (hD : B3ClosedContrDecayLe 4) {b E : ℝ} {np : ℕ}
    {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ) (P : CIdx K np → Prop)
    (hL : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      B3LayerMeanAt b E s h τ m R W j (Vs W) C c) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      genDriftStep b E s h τ m R W j (Vs W) c ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by
  obtain ⟨CL, hCL, hevL⟩ := hL
  obtain ⟨C₂, ρ, hC₂, hρ0, hρ1, hevD⟩ := hD b E np τ m T s h K Vs hF R 2 (by norm_num) (by norm_num)
  set N : ℝ := (Fintype.card (ContrIdx K np) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨CL * (CL * N * C₂ + CL ^ 2 + CL ^ 6 + 1), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hevD, eventually_ge_atTop 1] with W hWL hWD hW1 j hj c hc
  have hj' := hj
  simp only [genNoBirthSteps, mem_filter, mem_Ico] at hj'
  have hr : 0 ≤ genStepRate ρ s τ W j := genStepRate_nonneg hρ0 s τ W j
  have hQ : ∀ x : ContrIdx K np, eLpNorm (b3ContrAlive b E s h τ m R W j (Vs W) x) 2
      (closedLaw b W np) ≤ ENNReal.ofReal (C₂ * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) :=
    fun x => by
      have := hWD j hj'.1.1 hj'.1.2.le x.1 x.2.1 x.2.2
      rwa [ENNReal.ofReal_ofNat] at this
  refine (b3_driftStep_le_of_layer b E s h τ m R j hCL (by positivity) (hWL j hj c hc)
    hQ).trans (ENNReal.ofReal_le_ofReal ?_)
  exact decay_step_arith hCL hr hW1

/-!
## The two drift estimates
-/

/-- **`KStepDrift` from the closed decay and the closed `𝒦` mean structure.** -/
theorem kStepDrift_of_decayLe (hD : B3ClosedContrDecayLe 4) (hK : B3ClosedKLayerMean) :
    KStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decayLe hD hF R
    (fun c => ∃ ij : Fin np × Fin np, c = Sum.inr ij)
    (by
      obtain ⟨C, hC, hev⟩ := hK b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨ij, hij⟩ => hij ▸ hW j hj ij⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj ij => hW j hj _ ⟨ij, rfl⟩⟩

/-- **`GramSumStepDrift` from the closed decay and the closed Gram mean structure.** -/
theorem gramSumStepDrift_of_decayLe (hD : B3ClosedContrDecayLe 4) (hG : B3ClosedGramLayerMean) :
    GramSumStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decayLe hD hF R
    (fun c => ∃ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np), c = Sum.inl e)
    (by
      obtain ⟨C, hC, hev⟩ := hG b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨e, he⟩ => he ▸ hW j hj e⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj e => hW j hj _ ⟨e, rfl⟩⟩

/-- The summed drifts follow (by the summation lemmas of the generator and Gram sums). -/
theorem kDriftSummed_of_decayLe (hD : B3ClosedContrDecayLe 4) (hK : B3ClosedKLayerMean) :
    KDriftSummed :=
  kDriftSummed_of_step (kStepDrift_of_decayLe hD hK)

theorem genReqGramDrift_of_decayLe (hD : B3ClosedContrDecayLe 4) (hG : B3ClosedGramLayerMean) :
    GenReqGramDrift :=
  genReqGramDrift_of_step (gramSumStepDrift_of_decayLe hD hG)

end BlockBand.SourceProcess.PhysApprox.B3

namespace BlockBand.SourceProcess.PhysApprox.B3DecayIn

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.PhysApprox.B3
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.FullSourceStops
open scoped NNReal ENNReal

/-!
## From the contract hypotheses
-/

/-- **The decay at bounded order from the input hypotheses**, the closed layer form and the closed
jets at the same orders (with (D0), `b3ClosedContrBound_holds`).
-/
theorem b3ClosedContrDecayLe_of_gaussianInputs (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hI : B3ClosedContrLayerForm) {P : ℝ} (hJ : B3ClosedJetLpLe P) :
    B3ClosedContrDecayLe P :=
  b3ClosedContrDecayLe_of_steps
    (b3ClosedContrStepMeanLe_of_layer (layerFreshBound_holds hGA hLp) hI hJ)
    (b3ClosedContrStepFluctLe_of_layer (layerFreshBound_holds hGA hLp) hI hJ)
    b3ClosedContrBound_holds

end BlockBand.SourceProcess.PhysApprox.B3DecayIn

namespace BlockBand.SourceProcess.PhysApprox.B3

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs

/-!
## Assembly from the order-4 hypothesis
-/

/-- **`B3ClosedJetLpLe 4`** from the contract hypotheses, `ClosedShiftDiscTrace`,
`FarFracTraceMoments4` and the
conductance at the orders `≤ 4` (`ClosedKStepForm` is proved). -/
theorem b3ClosedJetLpLe_of_frac4 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hA : Jet.ClosedShiftDiscTrace) (hB : FarFracTraceMoments4)
    (hg : ClosedCondLpLe 4) : B3DecayIn.B3ClosedJetLpLe 4 :=
  b3ClosedJetLpLe_of_jets (closedJet0LpLe_of_frac4 hMT hGA hLp hA hB)
    (Jet1.closedJet1LpLe_of_frac4 hMT hGA hLp hA hB) hg closedKStepForm_holds

/-- **`B3ClosedContrDecayLe 4`** from the contract hypotheses, the closed layer form,
`ClosedShiftDiscTrace`, `FarFracTraceMoments4` and the conductance at the orders `≤ 4`. -/
theorem b3ClosedContrDecayLe_of_frac4 (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hI : B3DecayIn.B3ClosedContrLayerForm) (hA : Jet.ClosedShiftDiscTrace)
    (hB : FarFracTraceMoments4) (hg : ClosedCondLpLe 4) : B3ClosedContrDecayLe 4 :=
  B3DecayIn.b3ClosedContrDecayLe_of_gaussianInputs hGA hLp hI (b3ClosedJetLpLe_of_frac4 hMT hGA hLp hA hB hg)

end BlockBand.SourceProcess.PhysApprox.B3
