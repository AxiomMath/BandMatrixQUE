module

public import BlockBand.SourceProcess.PhysApprox.B3FourBirth

/-!
# The Gram consequences of the per-step closed Gram bound

The frame estimate `ClosedFrameStepEight` is false (the closed frame moves by the `O(1)` transport
`V_pr,+ = N*V_pr`), so the theorems that assume it are vacuous. This file states the per-step
bound on the Gram coordinates themselves and re-derives the same consequences.

* **`ClosedGramStepFourAt`**, stated as a hypothesis: `E[1_{A_j}|ΔG_e|⁴] ≤ C/W²`, eventually in
  `W`, at every step `n_s ≤ j < ⌊WT⌋` and for every old Gram coordinate `e` (no newborn column at
  `j`). It is the conclusion of `lintegral_gramStep_at`, stated directly.
* `closedGramStepFourAt_of_frame`: the frame estimate implies it (so it asks no more).
* **`gramStopStepFour_of_gramStep`**: `ClosedGramStepFourAt ⇒ GramStopStepFour`, hence
  **`complexGramLindeberg_of_gramStep`** and, with `KCorrStepFourAt`,
  **`complexClosedLindeberg_of_gramStep`**.
* **`gramBirthOldL2_of_gramStep`**: the Gram rows of `ComplexBirthOldL2`; with `KCorrStepFourAt`
  and the contract hypotheses, **`complexBirthOldL2_of_gramStep`** gives `ComplexBirthOldL2`. The
  generic step is `birthOldL2_of_stepFour` (`x² ≤ Wx⁴ + 1/W`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

variable {np K : ℕ}

/-- **`ClosedGramStepFourAt`** (the Gram step `V*(NN* − I)V = V*(𝒜 + 𝒜*)V` of an old
coordinate has conditional `L⁴` size `C_R W^{-1/2}` on the trace stop): eventually in `W`, at every
step `n_s ≤ j < ⌊WT⌋` and for every Gram coordinate with no newborn column at `j`,
`E[1_{A_j}|dX_e|⁴] ≤ C/W²`. -/
def ClosedGramStepFourAt : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
          ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np) →
          ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^ 4
            ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ 2)

/-- The frame estimate implies the Gram estimate (`lintegral_gramStep_at`). -/
theorem closedGramStepFourAt_of_frame (hF : ClosedFrameStepEight) : ClosedGramStepFourAt := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, -, hC⟩ := lintegral_gramStep_at hF b E np τ m T s h K Vs hD R
  exact ⟨C, hC⟩

/-- The per-step Gram bound with a nonnegative constant. -/
theorem lintegral_gramStep_of_at (hG : ClosedGramStepFourAt) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
            ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np) →
            ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
                (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^ 4
              ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC⟩ := hG b E np τ m T s h K Vs hD R
  refine ⟨max C 0, le_max_right _ _, hC.mono fun W hW j hj e he => (hW j hj e he).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))

/-- **`GramStopStepFour` from the per-step Gram estimate.** -/
theorem gramStopStepFour_of_gramStep (hG : ClosedGramStepFourAt) : GramStopStepFour := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC0, hC⟩ := lintegral_gramStep_of_at hG b E np τ m T s h K Vs hD R
  refine ⟨8 * (C * max T 0 + max 0 0), ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 e
  refine rate_sum_le hC0 hW1 (card_filter_Ico_le s T τ W)
    (fun j => ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np) y‖ₑ ^ 4) y
        ∂closedLaw b W np) (fun _ => 0) (fun j hj => ?_) (by simp)
  obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
  rw [add_zero]
  simp_rw [indicator_enorm_pow_four]
  exact (hW j hj1 e (not_isNewCoord_of_not_birth hj2 _)).trans
    (le_mul_of_one_le_left' (by norm_num))

/-- **`ComplexGramLindeberg` from the per-step Gram estimate.** -/
theorem complexGramLindeberg_of_gramStep (hG : ClosedGramStepFourAt) : ComplexGramLindeberg :=
  complexGramLindeberg_of_stepFour (gramStopStepFour_of_gramStep hG)

/-- **`ComplexClosedLindeberg` from the two per-step estimates and the input hypotheses.** -/
theorem complexClosedLindeberg_of_gramStep (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : KCorrStepFourAt) (hG : ClosedGramStepFourAt) : ComplexClosedLindeberg :=
  complexClosedLindeberg_of_pins hGA hLp hSR hMT (kCorrStepFour_of_at hC)
    (gramStopStepFour_of_gramStep hG)

/-!
## The one-step `L²` bound at the birth steps
-/

/-- **From the per-step fourth moment to the birth-step second moment** (`x² ≤ Wx⁴ + 1/W`): a
per-step bound `C/W²` on `E[1_{A_j}|dX_c|⁴]` gives `E[1_{A_j}|dX_c|²] ≤ (C + 1)/W`. -/
theorem birthOldL2_of_stepFour {b E s h T : ℝ} {τ m : Fin np → ℝ} {R : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {c : CIdx K np}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hev : ∀ᶠ W in atTop, ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
      ¬ IsNewCoord τ W j c →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
            (b3dX b E s h τ m W j (Vs W) c) y‖ₑ ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal (C / (W : ℝ) ^ 2)) :
    ∀ᶠ W : ℕ in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j →
      ¬ IsNewCoord τ W j c →
      ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3dX b E s h τ m W j (Vs W) c) y‖ₑ ^ 2 ∂closedLaw b W np ≤
        ENNReal.ofReal ((C + 1) / W) := by
  filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1 j hj1 hj2 _ hn
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  set f : ProbedPath W np × ℝ → ℝ≥0∞ := fun y => ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
    (b3dX b E s h τ m W j (Vs W) c) y‖ₑ
  calc ∫⁻ y, f y ^ 2 ∂closedLaw b W np
      ≤ ∫⁻ y, ((W : ℝ≥0∞) * f y ^ 4 + ENNReal.ofReal (1 / W)) ∂closedLaw b W np :=
        lintegral_mono fun y => sq_le_mul_pow_four_add (f y) hW1
    _ = (W : ℝ≥0∞) * ∫⁻ y, f y ^ 4 ∂closedLaw b W np + ENNReal.ofReal (1 / W) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top W), lintegral_const, measure_univ,
          mul_one]
    _ ≤ (W : ℝ≥0∞) * ENNReal.ofReal (C / (W : ℝ) ^ 2) + ENNReal.ofReal (1 / W) := by
        gcongr
        exact hW j (Finset.mem_Ico.2 ⟨hj1, hj2⟩) hn
    _ = ENNReal.ofReal ((C + 1) / W) := by
        rw [← ENNReal.ofReal_natCast W, ← ENNReal.ofReal_mul hWr.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp

/-- **The Gram rows of `ComplexBirthOldL2`** from the per-step Gram estimate. -/
theorem gramBirthOldL2_of_gramStep (hG : ClosedGramStepFourAt) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs →
      ∀ (R : ℝ) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)), ∃ C : ℝ,
        ∀ᶠ W : ℕ in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j →
          ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np) →
          ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^ 2
            ∂closedLaw b W np ≤ ENNReal.ofReal (C / W) := by
  intro b E np τ m T s h K Vs hD R e
  obtain ⟨C, hC0, hC⟩ := lintegral_gramStep_of_at hG b E np τ m T s h K Vs hD R
  exact ⟨C + 1, birthOldL2_of_stepFour hC0 (hC.mono fun W hW j hj hn => hW j hj e hn)⟩

/-- **`ComplexBirthOldL2` from the two per-step estimates** `KCorrStepFourAt`,
`ClosedGramStepFourAt` and the input hypotheses; the `𝒦` rows use `lintegral_kStopStep_at`. -/
theorem complexBirthOldL2_of_gramStep (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : KCorrStepFourAt) (hG : ClosedGramStepFourAt) : ComplexBirthOldL2 := by
  intro b E np τ m T s h K Vs hD R c
  cases c with
  | inl e => exact gramBirthOldL2_of_gramStep hG b E np τ m T s h K Vs hD R e
  | inr ij =>
      obtain ⟨C, hC0, hev⟩ :=
        lintegral_kStopStep_at hGA hLp hSR hMT hC b E np τ m T s h K Vs hD R
      refine ⟨C + 1, birthOldL2_of_stepFour hC0 (hev.mono fun W hW j hj hn => ?_)⟩
      simp_rw [indicator_b3dX_inr]
      exact hW j hj ij hn

end BlockBand.SourceProcess.PhysApprox.B3
