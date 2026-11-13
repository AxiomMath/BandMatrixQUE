module

public import BlockBand.SourceProcess.PhysApprox.B3GramStepClosed

/-!
# The Gram consumers at a weaker per-step rate `o(1/W)`

* **`ClosedGramStepFourSmall`** (an intermediate statement): per-step
  `E[1_{A_j}|dX_e|⁴] ≤ r_W`, `r_W ≥ 0`, `W r_W → 0`. `closedGramStepFourSmall_of_at`:
  `ClosedGramStepFourAt` implies it.
* **`ClosedJetStopSmall`** (a hypothesis): the stopped closed jet `E[1_{A_j}δ₀⁴] ≤ r_W` at the
  same rate (`ClosedJetStopHalf` implies it, `closedJetStopSmall_of_half`).
* **`closedGramStepFourSmall_of_closed`**: the closed-update argument at the weak rate, from
  `lintegral_gramStep_le_jet`.
* Consumers: **`complexGramLindeberg_of_small`** (`Σ_j ≤ ⌊WT⌋r_W → 0`),
  **`complexClosedLindeberg_of_small`** (with `KCorrStepFourAt` and the contract hypotheses),
  **`complexBirthOld_of_small`** (`ComplexBirthOld`, the `L¹` estimate that `ComplexBirthOldL2` was
  used for: `E|x| ≤ (Wx⁴ + 1/W)/(2θ) + θ/2`).
* **Not** recovered at the weak rate: the rate statements `GramStopStepFour` (`W·Σ_j` bounded)
  and the Gram rows of `ComplexBirthOldL2` (`C/W` at birth steps).
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

/-- **`ClosedGramStepFourSmall`**: as `ClosedGramStepFourAt` at a rate
`r_W ≥ 0` with `W·r_W → 0` in place of `C/W²`. -/
def ClosedGramStepFourSmall : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ r : ℕ → ℝ, (∀ W, 0 ≤ r W) ∧
      Tendsto (fun W : ℕ => (W : ℝ) * r W) atTop (𝓝 0) ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
            ¬ IsNewCoord τ W j (Sum.inl e : CIdx K np) →
            ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
                (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np)) y‖ₑ ^ 4
              ∂closedLaw b W np ≤ ENNReal.ofReal (r W)

/-- **`ClosedJetStopSmall`**: the stopped closed jet at a rate `r_W ≥ 0` with
`W·r_W → 0` (i.e. `δ₀ = o(W^{-1/4})` in stopped `L⁴`). -/
def ClosedJetStopSmall : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ r : ℕ → ℝ, (∀ W, 0 ≤ r W) ∧
      Tendsto (fun W : ℕ => (W : ℝ) * r W) atTop (𝓝 0) ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
              ENNReal.ofReal (jetDistance0 b E (b3ClosedX b E s h τ m W j y) ^ 4)) y
            ∂closedLaw b W np ≤ ENNReal.ofReal (r W)

theorem tendsto_mul_div_sq (C : ℝ) :
    Tendsto (fun W : ℕ => (W : ℝ) * (C / (W : ℝ) ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun W : ℕ => C / (W : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with W hW
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  field_simp

/-- `ClosedGramStepFourAt ⇒ ClosedGramStepFourSmall` (`r_W = C⁺/W²`). -/
theorem closedGramStepFourSmall_of_at (h : ClosedGramStepFourAt) : ClosedGramStepFourSmall := by
  intro b E np τ m T s h' K Vs hD R
  obtain ⟨C, hC0, hC⟩ := lintegral_gramStep_of_at h b E np τ m T s h' K Vs hD R
  exact ⟨fun W => C / (W : ℝ) ^ 2, fun W => by positivity, tendsto_mul_div_sq C, hC⟩

/-- `ClosedJetStopHalf ⇒ ClosedJetStopSmall`. -/
theorem closedJetStopSmall_of_half (h : ClosedJetStopHalf) : ClosedJetStopSmall := by
  intro b E np τ m T s h' K Vs hD R
  obtain ⟨C, hC⟩ := h b E np τ m T s h' K Vs hD R
  refine ⟨fun W => max C 0 / (W : ℝ) ^ 2, fun W => by positivity, tendsto_mul_div_sq _, ?_⟩
  filter_upwards [hC] with W hW j hj
  exact (hW j hj).trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))

/-- **The closed-update argument at the weak rate**: the closed update, the frame and leak bounds and
the stopped jet at rate `o(1/W)` give `ClosedGramStepFourSmall`. -/
theorem closedGramStepFourSmall_of_closed (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hU : ClosedGramUpdate) (hV : ClosedNearVBound)
    (hT : ClosedLeakBound) (hJ : ClosedJetStopSmall) : ClosedGramStepFourSmall := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC0, hC⟩ := lintegral_gramStep_le_jet hGA hLp hU hV hT b E np τ m T s h K Vs hD R
  obtain ⟨r, hr0, hr, hJev⟩ := hJ b E np τ m T s h K Vs hD R
  refine ⟨fun W => C * r W + C / (W : ℝ) ^ 2, fun W => by have := hr0 W; positivity, ?_, ?_⟩
  · have h1 : Tendsto (fun W : ℕ => C * ((W : ℝ) * r W)) atTop (𝓝 (C * 0)) := hr.const_mul C
    rw [mul_zero] at h1
    have h2 := h1.add (tendsto_mul_div_sq C)
    rw [add_zero] at h2
    exact h2.congr fun W => by ring
  · filter_upwards [hC, hJev] with W hW hJW j hj e he
    refine (hW j hj e he).trans ?_
    have hrW := hr0 W
    calc ENNReal.ofReal C * ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            ENNReal.ofReal (jetDistance0 b E (b3ClosedX b E s h τ m W j y) ^ 4)) y
              ∂closedLaw b W np + ENNReal.ofReal (C / (W : ℝ) ^ 2)
        ≤ ENNReal.ofReal C * ENNReal.ofReal (r W) + ENNReal.ofReal (C / (W : ℝ) ^ 2) :=
          add_le_add (mul_le_mul' le_rfl (hJW j hj)) le_rfl
      _ = ENNReal.ofReal (C * r W + C / (W : ℝ) ^ 2) := by
          rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-!
## The consumers
-/

/-- **`ComplexGramLindeberg` from the weak per-step estimate**: `Σ_j ≤ ⌊WT⌋·r_W ≤ T⁺·W r_W → 0`. -/
theorem complexGramLindeberg_of_small (hG : ClosedGramStepFourSmall) : ComplexGramLindeberg := by
  intro b E np τ m T s h K Vs hD R e
  obtain ⟨r, hr0, hr, hev⟩ := hG b E np τ m T s h K Vs hD R
  have hlim : Tendsto (fun W : ℕ => ENNReal.ofReal (max T 0 * ((W : ℝ) * r W))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hr.const_mul (max T 0))
    rwa [mul_zero, ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev] with W hW
  have hcard := card_filter_Ico_le s T τ W
  have hfl := gen_floor_mul_le T W
  calc b3LindebergErr b E s T h τ m R W (Vs W) (Sum.inl e : CIdx K np)
      ≤ ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j),
          ENNReal.ofReal (r W) := by
        refine Finset.sum_le_sum fun j hj => ?_
        obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
        simp_rw [indicator_enorm_pow_four]
        exact hW j hj1 e (not_isNewCoord_of_not_birth hj2 _)
    _ = ENNReal.ofReal (((Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun j => ¬ IsBirthStep τ W j)).card * r W) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (max T 0 * ((W : ℝ) * r W)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc : (((Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
            (fun j => ¬ IsBirthStep τ W j)).card : ℝ) ≤ W * max T 0 :=
          le_trans (by exact_mod_cast hcard) hfl
        nlinarith [hr0 W]

/-- **`ComplexClosedLindeberg` from the weak Gram estimate, `KCorrStepFourAt` and the contract
hypotheses.** -/
theorem complexClosedLindeberg_of_small (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : KCorrStepFourAt) (hG : ClosedGramStepFourSmall) : ComplexClosedLindeberg :=
  complexClosedLindeberg_of_parts (complexGramLindeberg_of_small hG)
    (complexKLindeberg_of_corr hGA hLp hSR hMT (kCorrStepFour_of_at hC))

/-- **The `L¹` birth-step bound from a per-step fourth moment `r_W` with `W r_W → 0`**:
`E|x| ≤ (W E x⁴ + 1/W)/(2θ) + θ/2 ≤ θ` eventually. -/
theorem birthOld_of_rate {b E s h T : ℝ} {τ m : Fin np → ℝ} {R : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {c : CIdx K np}
    {r : ℕ → ℝ} (hr0 : ∀ W, 0 ≤ r W) (hr : Tendsto (fun W : ℕ => (W : ℝ) * r W) atTop (𝓝 0))
    (hev : ∀ᶠ W in atTop, ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
      ¬ IsNewCoord τ W j c →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
            (b3dX b E s h τ m W j (Vs W) c) y‖ₑ ^ 4 ∂closedLaw b W np ≤ ENNReal.ofReal (r W))
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ W : ℕ in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j →
      ¬ IsNewCoord τ W j c →
      ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3dX b E s h τ m W j (Vs W) c) y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ := by
  have hsum : Tendsto (fun W : ℕ => (W : ℝ) * r W + 1 / (W : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun W : ℕ => 1 / (W : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have := hr.add h1
    rwa [add_zero] at this
  have hsmall : ∀ᶠ W : ℕ in atTop, (W : ℝ) * r W + 1 / (W : ℝ) ≤ θ ^ 2 :=
    hsum.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hev, hsmall, eventually_ge_atTop 1] with W hW hWs hW1 j hj1 hj2 _ hn
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  set f : ProbedPath W np × ℝ → ℝ≥0∞ := fun y => ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
    (b3dX b E s h τ m W j (Vs W) c) y‖ₑ
  have h2 : ∫⁻ y, f y ^ 2 ∂closedLaw b W np ≤ ENNReal.ofReal (θ ^ 2) := by
    calc ∫⁻ y, f y ^ 2 ∂closedLaw b W np
        ≤ ∫⁻ y, ((W : ℝ≥0∞) * f y ^ 4 + ENNReal.ofReal (1 / W)) ∂closedLaw b W np :=
          lintegral_mono fun y => sq_le_mul_pow_four_add (f y) hW1
      _ = (W : ℝ≥0∞) * ∫⁻ y, f y ^ 4 ∂closedLaw b W np + ENNReal.ofReal (1 / W) := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ (ENNReal.natCast_ne_top W), lintegral_const, measure_univ,
            mul_one]
      _ ≤ (W : ℝ≥0∞) * ENNReal.ofReal (r W) + ENNReal.ofReal (1 / W) := by
          gcongr
          exact hW j (Finset.mem_Ico.2 ⟨hj1, hj2⟩) hn
      _ = ENNReal.ofReal ((W : ℝ) * r W + 1 / (W : ℝ)) := by
          rw [← ENNReal.ofReal_natCast W, ← ENNReal.ofReal_mul hWr.le,
            ← ENNReal.ofReal_add (mul_nonneg hWr.le (hr0 W)) (by positivity)]
      _ ≤ ENNReal.ofReal (θ ^ 2) := ENNReal.ofReal_le_ofReal hWs
  calc ∫⁻ y, f y ∂closedLaw b W np
      ≤ ∫⁻ y, (ENNReal.ofReal (1 / (2 * θ)) * f y ^ 2 + ENNReal.ofReal (θ / 2))
          ∂closedLaw b W np := lintegral_mono fun y => Birth.le_sq_div_add hθ (f y)
    _ = ENNReal.ofReal (1 / (2 * θ)) * ∫⁻ y, f y ^ 2 ∂closedLaw b W np +
          ENNReal.ofReal (θ / 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (1 / (2 * θ)) * ENNReal.ofReal (θ ^ 2) + ENNReal.ofReal (θ / 2) := by
        gcongr
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        field_simp
        ring

/-- **`ComplexBirthOld` from the weak Gram estimate, `KCorrStepFourAt` and the contract
hypotheses.** -/
theorem complexBirthOld_of_small (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFourAt)
    (hG : ClosedGramStepFourSmall) : ComplexBirthOld := by
  intro b E np τ m T s h K Vs hD R θ hθ c
  cases c with
  | inl e =>
      obtain ⟨r, hr0, hr, hev⟩ := hG b E np τ m T s h K Vs hD R
      exact birthOld_of_rate hr0 hr (hev.mono fun W hW j hj hn => hW j hj e hn) hθ
  | inr ij =>
      obtain ⟨C, hC0, hev⟩ :=
        lintegral_kStopStep_at hGA hLp hSR hMT hC b E np τ m T s h K Vs hD R
      refine birthOld_of_rate (r := fun W => C / (W : ℝ) ^ 2) (fun W => by positivity)
        (tendsto_mul_div_sq C) (hev.mono fun W hW j hj hn => ?_) hθ
      simp_rw [indicator_b3dX_inr]
      exact hW j hj ij hn

end BlockBand.SourceProcess.PhysApprox.B3
