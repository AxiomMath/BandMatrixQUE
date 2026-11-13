module

public import BlockBand.SourceProcess.PhysApprox.B3FourGram
public import BlockBand.SourceProcess.PhysApprox.B3BirthOld

/-!
# `ComplexBirthOldL2` from the per-step fourth moments

* **`lintegral_closedStep_at`**: the shared per-step lemma, for
  every coordinate `c` (Gram and `𝒦`) and every step `n_s ≤ j < ⌊WT⌋` at which `c` has no newborn
  index: `E[1_{A_j}|dX_c|⁴] ≤ C/W²`. It rests on the contract hypotheses and the two
  per-step estimates `KCorrStepFourAt` and `ClosedFrameStepEight`.
* **`complexBirthOldL2_of_pins`**: `ComplexBirthOldL2`, by `x² ≤ Wx⁴ + 1/W`, so
  `E[1_A|dX|²] ≤ (C + 1)/W`. No measurability is used.
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

variable {W np K : ℕ}

theorem indicator_b3dX_inr (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (y : ProbedPath W np × ℝ) :
    (b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs (Sum.inr ij : CIdx K np))
      y = kStopStep b E s h τ m R W j Vs ij y :=
  rfl

/-- **The shared per-step fourth moment**: for every coordinate and every step
`n_s ≤ j < ⌊WT⌋` at which it has no newborn index, `E[1_{A_j}|dX_c|⁴] ≤ C/W²`. -/
theorem lintegral_closedStep_at (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFourAt)
    (hF : ClosedFrameStepEight) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : CIdx K np), ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ W in atTop, ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ¬ IsNewCoord τ W j c →
            ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
                (b3dX b E s h τ m W j (Vs W) c) y‖ₑ ^ 4 ∂closedLaw b W np ≤
              ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
  intro b E np τ m T s h K Vs hD R c
  cases c with
  | inl e =>
      obtain ⟨C, hC0, hev⟩ := lintegral_gramStep_at hF b E np τ m T s h K Vs hD R
      exact ⟨C, hC0, hev.mono fun W hW j hj hn => hW j hj e hn⟩
  | inr ij =>
      obtain ⟨C, hC0, hev⟩ := lintegral_kStopStep_at hGA hLp hSR hMT hC b E np τ m T s h K Vs hD R
      refine ⟨C, hC0, hev.mono fun W hW j hj hn => ?_⟩
      simp_rw [indicator_b3dX_inr]
      exact hW j hj ij hn

/-- `x² ≤ Wx⁴ + 1/W` on `ℝ≥0∞`, `W ≥ 1`. -/
theorem sq_le_mul_pow_four_add (x : ℝ≥0∞) (hW : 1 ≤ W) :
    x ^ 2 ≤ (W : ℝ≥0∞) * x ^ 4 + ENNReal.ofReal (1 / W) := by
  have hW0 : (W : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  by_cases hx : x = ⊤
  · subst hx
    rw [ENNReal.top_pow (by norm_num), ENNReal.top_pow (by norm_num), ENNReal.mul_top hW0,
      top_add]
  · rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_natCast W]
    set r := x.toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
    rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul hWr.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    refine le_of_mul_le_mul_right ?_ hWr
    have e : ((W : ℝ) * r ^ 4 + 1 / W) * W = ((W : ℝ) * r ^ 2) ^ 2 + 1 := by field_simp
    rw [e]
    nlinarith [sq_nonneg ((W : ℝ) * r ^ 2 - 1), sq_nonneg r]

/-- **`ComplexBirthOldL2` from the per-step estimates** `KCorrStepFourAt`, `ClosedFrameStepEight`
and the input hypotheses. -/
theorem complexBirthOldL2_of_pins (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFourAt)
    (hF : ClosedFrameStepEight) : ComplexBirthOldL2 := by
  intro b E np τ m T s h K Vs hD R c
  obtain ⟨C, hC0, hev⟩ := lintegral_closedStep_at hGA hLp hSR hMT hC hF b E np τ m T s h K Vs
    hD R c
  refine ⟨C + 1, ?_⟩
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

end BlockBand.SourceProcess.PhysApprox.B3
