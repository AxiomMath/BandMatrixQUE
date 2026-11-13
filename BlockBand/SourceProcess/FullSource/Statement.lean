module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The full-source moments, uniformly on compact bulk sets

`FullSourceMomentsBulk` bounds the clock, the clock square and the tags uniformly for `E` in a bulk
interval; it implies the fixed-energy statement `FullSourceMomentsContract`
(`fullSourceMoments_of_bulk`).

* `TagPropagationBulk`: the tag bound with a constant that depends on the *propagation length*
  `j - k ≤ RW + 1` only (`b, κ, R, p` first, then `C`; then `T`, then `W₀`). This is the form the
  stopped recursion gives; it implies `tag` (with `R = T`) and `EdgeClockMomentsContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- **The full-source moments, uniformly on compact bulk sets**. -/
structure FullSourceMomentsBulk : Prop where
  clock : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j : ℕ, (j : ℝ) ≤ T * W →
      eLpNorm (fun ω => (W : ℂ)⁻¹ * ((boundaryToInterior b E W j ω)ᴴ *
          boundaryToInterior b E W j ω).trace) (ENNReal.ofReal p) (growthPathLaw W b) ≤
        ENNReal.ofReal (C * ((j : ℝ) + 1))
  clockSquare : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j : ℕ, (j : ℝ) ≤ T * W →
      ∫⁻ ω, ‖(((boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω) ^ 2).trace‖ₑ
          ∂growthPathLaw W b ≤ ENNReal.ofReal (C * W * ((j : ℝ) + 1) ^ 3)
  tag : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j : ℕ, (j : ℝ) ≤ T * W →
      ∀ k : ℕ, k < j →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal C

/-- **The tag bound in terms of the propagation length** (the form proved by the stopped
recursion): `C` depends on `b, κ, R, p` only, `W₀` also on the total length `T`. -/
def TagPropagationBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ R p : ℝ, 0 < κ → 1 ≤ p → ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ,
    ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j k : ℕ, k < j → (j : ℝ) ≤ T * W →
      (j : ℝ) ≤ k + R * W + 1 →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal C

theorem mem_bulkInterval_min {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- **`FullSourceMomentsContract` from the bulk-uniform form** `FullSourceMomentsBulk`. -/
theorem fullSourceMoments_of_bulk (h : FullSourceMomentsBulk) : FullSourceMomentsContract where
  clock b hb hb' E hE1 hE2 T p hp := by
    obtain ⟨hκ, hE⟩ := mem_bulkInterval_min hE1 hE2
    obtain ⟨C, W₀, hC⟩ := h.clock b hb hb' _ T p hκ hp
    exact ⟨C, W₀, fun W hW j hj => hC W hW E hE j hj⟩
  clockSquare b hb hb' E hE1 hE2 T := by
    obtain ⟨hκ, hE⟩ := mem_bulkInterval_min hE1 hE2
    obtain ⟨C, W₀, hC⟩ := h.clockSquare b hb hb' _ T hκ
    exact ⟨C, W₀, fun W hW j hj => hC W hW E hE j hj⟩
  tag b hb hb' E hE1 hE2 T p hp := by
    obtain ⟨hκ, hE⟩ := mem_bulkInterval_min hE1 hE2
    obtain ⟨C, W₀, hC⟩ := h.tag b hb hb' _ T p hκ hp
    exact ⟨C, W₀, fun W hW j hj k hk => hC W hW E hE j hj k hk⟩

/-- `tag` from the propagation form, with `R = max T 0` (`j - k ≤ j ≤ TW`). -/
theorem tag_of_propagation (h : TagPropagationBulk) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ j : ℕ, (j : ℝ) ≤ T * W →
      ∀ k : ℕ, k < j →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal C := by
  intro b hb hb' κ T p hκ hp
  obtain ⟨C, hC⟩ := h b hb hb' κ (max T 0) p hκ hp
  obtain ⟨W₀, hW₀⟩ := hC T
  refine ⟨C, W₀, fun W hW E hE j hj k hk => hW₀ W hW E hE j k hk hj ?_⟩
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have : T * W ≤ max T 0 * W := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0
  linarith

end BlockBand.SourceProcess.FullSource
