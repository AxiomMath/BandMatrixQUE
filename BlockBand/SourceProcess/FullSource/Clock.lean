module

public import BlockBand.SourceProcess.FullSource.TagBulk

/-!
# The clock is the sum of the tags

The clock `W⁻¹Tr Y_j^1` is the sum of the tag masses, so the bulk moment bound for the clock follows
from the one for the tags.

* `superexpExit_of`: `SuperexpExit` from `ScalarRecursionContract`;
* `sum_tagProjection`: `Σ_{k<j} P_k = I` on the `j` physical blocks;
* `clock_trace_eq`: `W⁻¹Tr Y_j^1 = Σ_{k<j} W⁻¹Tr Y_{j;k}`;
* `clock_of_tag`: the bulk `clock` field from the bulk `tag` field (Minkowski; `C(j+1)`);
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal

/-- **Superexponential exit** `SuperexpExit`, from `ScalarRecursionContract`. -/
theorem superexpExit_of (hSR : ScalarRecursionContract) : SuperexpExit :=
  passiveInitialScalar_superexp_of_scalarRecursion hSR

variable {W : ℕ}

theorem sum_tagProjection (j : ℕ) : ∑ k ∈ Finset.range j, tagProjection W j k = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [tagProjection, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    have hx := x.1.isLt
    rw [Finset.sum_eq_single (j - 1 - x.1.val)]
    · have h : j - 1 - x.1.val < j ∧ x.1.val = j - 1 - (j - 1 - x.1.val) := ⟨by omega, by omega⟩
      split_ifs <;> rfl
    · intro k hk hne
      have hk' := Finset.mem_range.1 hk
      have h : ¬ (k < j ∧ x.1.val = j - 1 - k) := fun h => hne (by omega)
      split_ifs <;> rfl
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · simp [hxy]

theorem clock_trace_eq (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    (W : ℂ)⁻¹ * ((boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω).trace =
      ∑ k ∈ Finset.range j, (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace := by
  rw [← Finset.mul_sum, ← Matrix.trace_sum]
  congr 2
  rw [show (boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω =
      (boundaryToInterior b E W j ω)ᴴ * (∑ k ∈ Finset.range j, tagProjection W j k) *
        boundaryToInterior b E W j ω by rw [sum_tagProjection, Matrix.mul_one],
    Matrix.mul_sum, Matrix.sum_mul]
  rfl

/-- **`clock` from `tag`** (`Y_j^1 = Σ_k Y_{j;k}` and Minkowski). -/
theorem clock_of_tag
    (htag : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j : ℕ, (j : ℝ) ≤ T * W →
        ∀ k : ℕ, k < j →
          eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) (ENNReal.ofReal p)
            (growthPathLaw W b) ≤ ENNReal.ofReal C) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j : ℕ, (j : ℝ) ≤ T * W →
      eLpNorm (fun ω => (W : ℂ)⁻¹ * ((boundaryToInterior b E W j ω)ᴴ *
          boundaryToInterior b E W j ω).trace) (ENNReal.ofReal p) (growthPathLaw W b) ≤
        ENNReal.ofReal (C * ((j : ℝ) + 1)) := by
  intro b hb hb' κ T p hκ hp
  obtain ⟨C, W₀, hC⟩ := htag b hb hb' κ T p hκ hp
  refine ⟨max C 0, W₀, fun W hW E hE j hj => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have e : (fun ω => (W : ℂ)⁻¹ * ((boundaryToInterior b E W j ω)ᴴ *
      boundaryToInterior b E W j ω).trace) =
      ∑ k ∈ Finset.range j, fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace := by
    funext ω; rw [clock_trace_eq, Finset.sum_apply]
  rw [e]
  refine (eLpNorm_sum_le hp1).trans ?_
  calc ∑ k ∈ Finset.range j, eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace)
        (ENNReal.ofReal p) (growthPathLaw W b)
      ≤ ∑ _k ∈ Finset.range j, ENNReal.ofReal (max C 0) :=
        Finset.sum_le_sum fun k hk => (hC W hW E hE j hj k (Finset.mem_range.1 hk)).trans
          (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (max C 0 * j) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm,
          ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (max C 0 * ((j : ℝ) + 1)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _))

end BlockBand.SourceProcess.FullSource
