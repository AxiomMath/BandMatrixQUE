module

public import BlockBand.SourceProcess.PhysApprox.B3BirthReduce

/-!
# Old coordinates at a birth step from a one-step `L²` bound

`ComplexBirthOld` (an `L¹` statement) follows from the one-step `L²` estimate `ComplexBirthOldL2`:
`E[1_{A_j}|dX_c|²] ≤ C/W` at the birth steps, for old coordinates (`complexBirthOld_of_L2`). The
proof uses `x ≤ x²/(2θ) + θ/2` pointwise (`le_sq_div_add`), so it needs **no measurability** of
the alive set or of the closed coordinates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal

/-- `x ≤ x²/(2θ) + θ/2` on `ℝ≥0∞`. -/
theorem Birth.le_sq_div_add {θ : ℝ} (hθ : 0 < θ) (x : ℝ≥0∞) :
    x ≤ ENNReal.ofReal (1 / (2 * θ)) * x ^ 2 + ENNReal.ofReal (θ / 2) := by
  by_cases hx : x = ⊤
  · subst hx
    have h0 : ENNReal.ofReal (1 / (2 * θ)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    refine le_of_eq ?_
    rw [ENNReal.top_pow two_ne_zero, ENNReal.mul_top h0, top_add]
  · rw [← ENNReal.ofReal_toReal hx]
    set r := x.toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : 1 / (2 * θ) * r ^ 2 + θ / 2 - r = (r - θ) ^ 2 / (2 * θ) := by
      field_simp
      ring
    have : 0 ≤ (r - θ) ^ 2 / (2 * θ) := by positivity
    linarith

/-- **One-step `L²` size of old coordinates at a birth step**: for every old coordinate
(no newborn index) the increment at a birth step has `E[1_{A_j}|dX_c|²] ≤ C/W`, uniformly over
the birth steps in `[n_s, ⌊WT⌋)`. It is the conditional second moment `E_j|dX_c|² = O(Tr M/W)`
of the regular half of the generator estimates, evaluated at the birth steps; for `𝒦` the
old entries follow `RawTag.RawUpdate`, which holds at every step. -/
def ComplexBirthOldL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : CIdx K np), ∃ C : ℝ, ∀ᶠ W : ℕ in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j →
        ¬ IsNewCoord τ W j c →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
            (b3dX b E s h τ m W j (Vs W) c) y‖ₑ ^ 2 ∂closedLaw b W np ≤
          ENNReal.ofReal (C / W)

/-- **`ComplexBirthOld` from the one-step `L²` estimate.** -/
theorem complexBirthOld_of_L2 (hL : ComplexBirthOldL2) : ComplexBirthOld := by
  intro b E np τ m T s h K Vs hD R θ hθ c
  obtain ⟨C, hC⟩ := hL b E np τ m T s h K Vs hD R c
  have hev : ∀ᶠ W : ℕ in atTop, C / W ≤ θ ^ 2 := by
    have ht : Tendsto (fun W : ℕ => C / (W : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    exact ht.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hC, hev] with W hCW hW
  intro j hj1 hj2 hjB hc
  set f : ProbedPath W np × ℝ → ℝ≥0∞ := fun y => ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
    (b3dX b E s h τ m W j (Vs W) c) y‖ₑ
  calc ∫⁻ y, f y ∂closedLaw b W np
      ≤ ∫⁻ y, (ENNReal.ofReal (1 / (2 * θ)) * f y ^ 2 + ENNReal.ofReal (θ / 2))
          ∂closedLaw b W np := lintegral_mono fun y => Birth.le_sq_div_add hθ (f y)
    _ = ENNReal.ofReal (1 / (2 * θ)) * ∫⁻ y, f y ^ 2 ∂closedLaw b W np +
          ENNReal.ofReal (θ / 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (1 / (2 * θ)) * ENNReal.ofReal (θ ^ 2) + ENNReal.ofReal (θ / 2) := by
        gcongr
        exact (hCW j hj1 hj2 hjB hc).trans (ENNReal.ofReal_le_ofReal hW)
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        field_simp
        ring

end BlockBand.SourceProcess.PhysApprox.B3
