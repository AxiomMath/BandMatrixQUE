module

public import BlockBand.SourceProcess.PhysApprox.B3JetOrder
public import BlockBand.SourceProcess.PhysApprox.B3Jet1Bridge
public import BlockBand.SourceProcess.PhysApprox.B3GramStepSmall
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm

/-!
# The closed `δ₀` jet at bounded moment order

**The analytic hypothesis at one order.** `FarFracTraceMoments4 := Jet.FarFracTraceMomentsAt 4`: for
every admissible `b, E, s` there is `α > 0` with `4α < 1` and `E(Σ_k t_k^α)^4 ≤ C` at the closing
length, eventually in `W`. It is implied by the original `FarFracTraceMoments` (at `p = 4`;
`farFracTraceMoments4_of`), and it gives the same statement at every `1 ≤ p ≤ 4` with the same `α`
(`farFracTraceMomentsAt_of_four`, from `x^p ≤ 1 + x^4` and a probability law).

**Bounded restatements** (the original statement with `p ≤ P` added after `1 ≤ p`; each is
implied by its `∀ p` form, `*_le_of`):

* `ClosedJet0FamLe P`, `ClosedJet0LpLe P`, `ClosedJet0LpStepsLe P`, `ClosedJet1LpLe P`,
  `ClosedCondLpLe P`;
* **`closedJet0FamLe_of_frac4`**: `MatchedTracesContract`, `GaussianAbsorptionContract`,
  `GaussianLpGradient`, `ClosedShiftDiscTrace` and `FarFracTraceMoments4` give
  `ClosedJet0FamLe 4` (through `Jet.closedJetLpAt_b3ClosedX`, start Markov at order `p`);
* the `δ₀` consumers at `p = 4`, all with their original conclusions:
  `closedJetL4Fam_of_famLe` (`ClosedJetL4Fam b3ClosedX`), `closedKMeanInput_of_famLe`,
  `closedJetHalf_of_famLe`, the jet bridges `closedJetStopHalf_of_famLe` and
  `closedJetStopSmall_of_famLe`, and the same consequences of `closedJet0FamLe_of_frac4`
  (`closedJetL4Fam_of_frac4`, …, `closedJet0LpLe_of_frac4`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

/-!
## The analytic hypothesis at `p = 4`
-/

/-- **`FarFracTraceMoments4`**: `FarFracTraceMoments` at the single order `p = 4`
(so `0 < α < 1/4`). -/
def FarFracTraceMoments4 : Prop := Jet.FarFracTraceMomentsAt 4

/-- The original `∀ p` hypothesis implies the order-4 hypothesis. -/
theorem farFracTraceMoments4_of (hB : Jet.FarFracTraceMoments) : FarFracTraceMoments4 :=
  Jet.farFracTraceMomentsAt_of hB (by norm_num)

/-- `x^p ≤ 1 + x^4` for `x ≥ 0`, `0 ≤ p ≤ 4`. -/
theorem rpow_le_one_add_pow_four {x p : ℝ} (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hp4 : p ≤ 4) :
    x ^ p ≤ 1 + x ^ (4 : ℝ) := by
  have h4 : 0 ≤ x ^ (4 : ℝ) := Real.rpow_nonneg hx _
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx h hp0
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hp4
    linarith

/-- **The order-4 hypothesis gives every order `1 ≤ p ≤ 4`** (same `α`; `E F^p ≤ 1 + E F^4`). -/
theorem farFracTraceMomentsAt_of_four (hB : FarFracTraceMoments4) {p : ℝ} (hp : 1 ≤ p)
    (hp4 : p ≤ 4) : Jet.FarFracTraceMomentsAt p := by
  intro b E h0 h1 h2 h3 s hs
  obtain ⟨α, hα0, hα4, C, hC⟩ := hB b E h0 h1 h2 h3 s hs
  refine ⟨α, hα0, by nlinarith, 1 + max C 0, ?_⟩
  filter_upwards [hC] with W hW
  set F : GrowthPath W → ℝ := fun ω => Jet.farFracTrace b E α W (closeLen s W) ω
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg fun k _ => by positivity
  calc ∫⁻ ω, ENNReal.ofReal (F ω ^ p) ∂growthPathLaw W b
      ≤ ∫⁻ ω, (1 + ENNReal.ofReal (F ω ^ (4 : ℝ))) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg (hF0 ω) _)]
        exact ENNReal.ofReal_le_ofReal
          (rpow_le_one_add_pow_four (hF0 ω) (by linarith) hp4)
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (F ω ^ (4 : ℝ)) ∂growthPathLaw W b := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal (max C 0) := by
        gcongr
        exact hW.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (1 + max C 0) := by
        rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one]

/-!
## Bounded restatements
-/

/-- **`ClosedJet0Fam` at the orders `1 ≤ p ≤ P`.** -/
def ClosedJet0FamLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)) (ENNReal.ofReal p)
          (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedJet0Lp` at the orders `1 ≤ p ≤ P`.** -/
def ClosedJet0LpLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`Jet1.ClosedJet0LpSteps` at the orders `1 ≤ p ≤ P`.** -/
def ClosedJet0LpStepsLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedJet1Lp` at the orders `1 ≤ p ≤ P`.** -/
def ClosedJet1LpLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W j y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedCondLp` at the orders `1 ≤ p ≤ P`.** -/
def ClosedCondLpLe (P : ℝ) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → p ≤ P → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => conductanceOf
            (passiveTransmission b E (b3ClosedX b E s h τ m W j y))))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal C

/-!
## The original `∀ p` forms imply the bounded ones
-/

theorem closedJet0FamLe_of (h : ClosedJet0Fam) (P : ℝ) : ClosedJet0FamLe P :=
  fun b E np τ m T s h' K Vs hF p hp _ => h b E np τ m T s h' K Vs hF p hp

theorem closedJet0LpLe_of (h : ClosedJet0Lp) (P : ℝ) : ClosedJet0LpLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

theorem closedJet0LpStepsLe_of (h : Jet1.ClosedJet0LpSteps) (P : ℝ) : ClosedJet0LpStepsLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

theorem closedJet1LpLe_of (h : ClosedJet1Lp) (P : ℝ) : ClosedJet1LpLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

theorem closedCondLpLe_of (h : ClosedCondLp) (P : ℝ) : ClosedCondLpLe P :=
  fun b E np τ m T s h' K Vs hF R p hp _ => h b E np τ m T s h' K Vs hF R p hp

/-- Monotonicity in the order bound. -/
theorem ClosedJet0FamLe.mono {P Q : ℝ} (h : ClosedJet0FamLe P) (hQ : Q ≤ P) :
    ClosedJet0FamLe Q :=
  fun b E np τ m T s h' K Vs hF p hp hpQ => h b E np τ m T s h' K Vs hF p hp (hpQ.trans hQ)

/-!
## `ClosedJet0FamLe 4` from the order-4 hypothesis
-/

/-- **`ClosedJet0FamLe P` from the fractional moments at every order `1 ≤ p ≤ P`.** -/
theorem closedJet0FamLe_of_fracAt (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hA : Jet.ClosedShiftDiscTrace)
    {P : ℝ} (hB : ∀ p : ℝ, 1 ≤ p → p ≤ P → Jet.FarFracTraceMomentsAt p) :
    ClosedJet0FamLe P := by
  intro b E np τ m T s h K Vs hF p hp hpP
  obtain ⟨C, -, hC⟩ := Jet.closedJetLpAt_b3ClosedX hMT hGA hLp hA hp (hB p hp hpP)
    b E np τ m T s h K Vs hF
  exact ⟨C, hC⟩

/-- **`ClosedJet0FamLe 4` from `FarFracTraceMoments4`.** -/
theorem closedJet0FamLe_of_frac4 (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hA : Jet.ClosedShiftDiscTrace)
    (hB : FarFracTraceMoments4) : ClosedJet0FamLe 4 :=
  closedJet0FamLe_of_fracAt hMT hGA hLp hA fun _ hp hp4 => farFracTraceMomentsAt_of_four hB hp hp4

/-!
## Restrictions to the alive set
-/

/-- **`ClosedJet0FamLe P ⇒ ClosedJet0LpStepsLe P`** (`‖1_A f‖_p ≤ ‖f‖_p`). -/
theorem closedJet0LpStepsLe_of_famLe {P : ℝ} (hJ : ClosedJet0FamLe P) : ClosedJet0LpStepsLe P := by
  intro b E np τ m T s h K Vs hFD R p hp hpP
  obtain ⟨⟨-, -, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hFD
  have hb : b < 1 := by linarith [hFD.1.2.1]
  obtain ⟨C, hC⟩ := hJ b E np τ m T s h K Vs hFD p hp hpP
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC, hFD.2.2.2.2.2] with W hW hVW j hj
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  exact (eLpNorm_indicator_le _ (nullMeasurableSet_b3Alive hb hE1 hE2 s h τ m R W j hV)).trans
    ((hW j hj).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))))

/-- **`ClosedJet0LpStepsLe P ⇒ ClosedJet0LpLe P`** (no-birth steps are steps). -/
theorem closedJet0LpLe_of_stepsLe {P : ℝ} (h : ClosedJet0LpStepsLe P) : ClosedJet0LpLe P := by
  intro b E np τ m T s h' K Vs hFD R p hp hpP
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R p hp hpP
  exact ⟨C, hC, hev.mono fun W hW j hj => hW j (Finset.mem_filter.1 hj).1⟩

/-- **`ClosedJet0FamLe P ⇒ ClosedJet0LpLe P`.** -/
theorem closedJet0LpLe_of_famLe {P : ℝ} (hJ : ClosedJet0FamLe P) : ClosedJet0LpLe P :=
  closedJet0LpLe_of_stepsLe (closedJet0LpStepsLe_of_famLe hJ)

/-!
## The `δ₀` consumers at `p = 4`
-/

/-- **`ClosedJetL4Fam b3ClosedX` from `ClosedJet0FamLe 4`** (`p = 4`, fourth power). -/
theorem closedJetL4Fam_of_famLe (hJ : ClosedJet0FamLe 4) : ClosedJetL4Fam b3ClosedX := by
  intro b E np τ m T s h K Vs hD
  obtain ⟨C, hev⟩ := hJ b E np τ m T s h K Vs hD 4 (by norm_num) le_rfl
  refine ⟨max C 0 ^ 4, ?_⟩
  filter_upwards [hev] with W hW j hj _
  have hb : eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y))
      (ENNReal.ofReal 4) (closedLaw b W np) ≤ ENNReal.ofReal (max C 0 / W) :=
    (hW j hj).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg W)))
  refine (jetFam_lintegral_four_le _ (fun y => norm_nonneg _)
    (div_nonneg (le_max_right _ _) (Nat.cast_nonneg W)) hb).trans (le_of_eq ?_)
  rw [div_pow]

/-- **`ClosedKMeanInput` from `ClosedJet0FamLe 4`** (with the proved `ClosedKStepForm`). -/
theorem closedKMeanInput_of_famLe (hJ : ClosedJet0FamLe 4) : ClosedKMeanInput :=
  closedKMeanInput_of_b3ClosedX closedKStepForm_holds (closedJetL4Fam_of_famLe hJ)

/-- **`ClosedJetHalf b3ClosedX` from `ClosedJet0FamLe 4`.** -/
theorem closedJetHalf_of_famLe (hJ : ClosedJet0FamLe 4) : ClosedJetHalf b3ClosedX :=
  closedJetHalf_of_b3ClosedX (closedJetL4Fam_of_famLe hJ)

/-- **The jet bridge `ClosedJet0FamLe 4 ⇒ ClosedJetStopHalf`**
(`E[1_Aδ₀⁴] ≤ Eδ₀⁴ ≤ (C⁺/W)⁴ ≤ C⁺⁴/W²`). -/
theorem closedJetStopHalf_of_famLe (hJ : ClosedJet0FamLe 4) : ClosedJetStopHalf := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC⟩ := hJ b E np τ m T s h K Vs hD 4 (by norm_num) le_rfl
  refine ⟨(max C 0) ^ 4, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 j hj
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hle : eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y))
      (ENNReal.ofReal 4) (closedLaw b W np) ≤ ENNReal.ofReal (max C 0 / W) :=
    (hW j hj).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
  have h4 := jetFam_lintegral_four_le (closedLaw b W np) (fun y => norm_nonneg _)
    (div_nonneg (le_max_right _ _) hW0.le) hle
  refine (lintegral_mono fun y => Set.indicator_le_self _ _ y).trans
    (h4.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [div_pow]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ hW1r (by norm_num))

/-- **The jet bridge `ClosedJet0FamLe 4 ⇒ ClosedJetStopSmall`.** -/
theorem closedJetStopSmall_of_famLe (hJ : ClosedJet0FamLe 4) : ClosedJetStopSmall :=
  closedJetStopSmall_of_half (closedJetStopHalf_of_famLe hJ)

/-!
## The same from the order-4 hypothesis
-/

section Frac4

variable (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
  (hLp : GaussianLpGradient) (hA : Jet.ClosedShiftDiscTrace) (hB : FarFracTraceMoments4)
include hMT hGA hLp hA hB

theorem closedJetL4Fam_of_frac4 : ClosedJetL4Fam b3ClosedX :=
  closedJetL4Fam_of_famLe (closedJet0FamLe_of_frac4 hMT hGA hLp hA hB)

theorem closedKMeanInput_of_frac4 : ClosedKMeanInput :=
  closedKMeanInput_of_famLe (closedJet0FamLe_of_frac4 hMT hGA hLp hA hB)

theorem closedJetHalf_of_frac4 : ClosedJetHalf b3ClosedX :=
  closedJetHalf_of_famLe (closedJet0FamLe_of_frac4 hMT hGA hLp hA hB)

theorem closedJetStopHalf_of_frac4 : ClosedJetStopHalf :=
  closedJetStopHalf_of_famLe (closedJet0FamLe_of_frac4 hMT hGA hLp hA hB)

theorem closedJetStopSmall_of_frac4 : ClosedJetStopSmall :=
  closedJetStopSmall_of_famLe (closedJet0FamLe_of_frac4 hMT hGA hLp hA hB)

theorem closedJet0LpLe_of_frac4 : ClosedJet0LpLe 4 :=
  closedJet0LpLe_of_famLe (closedJet0FamLe_of_frac4 hMT hGA hLp hA hB)

end Frac4

end BlockBand.SourceProcess.PhysApprox.B3
