module

public import BlockBand.Critical.BoundaryMean.Statement

/-!
# Exact boundary mean: removing the radial regulator

At fixed width `W`, the strict clause `StrictBoundaryMeanClause` (for `Y = -Im X ≻ 0`, with
explicit constants) implies the full `ExactBoundaryMeanContract`, by removing a radial
regulator at fixed width.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ComplexOrder

/-- **Radial reduction.** The strict clause (constants `ε ≥ 0`, `C ≥ 0`, `d₂ > 0`, `W₀`) implies the
`ExactBoundaryMeanContract` (with `d₁ = d₂/2`, the same `ε`, `C`, `W₀`).
-/
theorem exactBoundaryMean_of_strict
    (h : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (ε : ℕ → ℝ) (C d₂ : ℝ) (W₀ : ℕ), Tendsto ε atTop (𝓝 0) ∧ 0 < d₂ ∧ 0 ≤ C ∧
        (∀ W, 0 ≤ ε W) ∧ StrictBoundaryMeanClause b κ ε C d₂ W₀) :
    ExactBoundaryMeanContract := by
  intro b hb0 hb κ hκ
  obtain ⟨ε, C, d₂, W₀, hε, hd₂, hC, hε0, hS⟩ := h b hb0 hb κ hκ
  refine ⟨ε, C, d₂ / 2, W₀, hε, by linarith, ?_⟩
  intro W hW hW₀ e he X hdX
  obtain ⟨hηmin, hηe⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
    (by linarith) hκ he
  have hη : 0 < (boundaryZ b e).im := hηmin.trans_le hηe
  refine ⟨fun hY => hS W hW hW₀ e he X hY (by linarith), fun hY δ hδ => ?_⟩
  set η := (boundaryZ b e).im with hηdef
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set w4 : ℝ := (W : ℝ) ^ (-(1 : ℝ) / 4)
  have hw4 : 0 ≤ w4 := Real.rpow_nonneg hWr.le _
  set A : ℝ := C * (1 / (2 * η) + 4 * W * w4)
  have hA : 0 ≤ A := by positivity
  set u : ℝ := min (d₂ * η) (δ / (A + 1))
  have hu : 0 < u := lt_min (by positivity) (by positivity)
  refine ⟨max (1 - u) 0, max_lt (by linarith) one_pos, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht.1.le
  have htu : 1 - t < u := by
    have := (le_max_left (1 - u) 0).trans_lt ht.1
    linarith
  have ht1 := ht.2
  set X' := Collar.Kernel.radialOld b e t X
  have hY' := Collar.Kernel.posDef_neg_imPart_radialOld b e hη hY ht0 ht1
  have hd' := Collar.Kernel.matchedDistance_radialOld_le b e hη hW hY ht0 ht1
  have h1t : (1 - t) / (2 * η) ≤ d₂ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : u ≤ d₂ * η := min_le_left _ _
    nlinarith
  have hd'' : matchedDistance b e X' ≤ d₂ := by linarith
  obtain ⟨hint, hnorm⟩ := hS W hW hW₀ e he X' hY' hd''
  refine ⟨(Collar.Kernel.collarKernelIntegrable_radial b e 0 0 hη hY ht0 ht1).2 hint, ?_⟩
  rw [Collar.Kernel.expectedCollarKernel_radial b e 0 0 hη hY ht0 ht1]
  refine hnorm.trans ?_
  have hg := Collar.Kernel.conductance_oldScattering_nonneg b e hη hY
  have hg' : conductance (oldScattering b e X') ≤
      conductance (oldScattering b e X) + 2 * W * (1 - t ^ 2) := by
    rw [Collar.Kernel.oldScattering_radialOld b e hη hY ht0 ht1]
    exact Collar.Kernel.conductance_radial_le _ (by nlinarith) hg
  have hAu : A * (1 - t) ≤ δ := by
    have h1 : A * (1 - t) ≤ A * u := mul_le_mul_of_nonneg_left htu.le hA
    have h2 : u ≤ δ / (A + 1) := min_le_right _ _
    have h3 : A * u ≤ A * (δ / (A + 1)) := mul_le_mul_of_nonneg_left h2 hA
    have h4 : A * (δ / (A + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hsq : 1 - t ^ 2 ≤ 2 * (1 - t) := by nlinarith
  unfold meanError
  have key : matchedDistance b e X' + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
      conductance (oldScattering b e X') * w4 ≤
      (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X) * w4) +
        (1 - t) * (1 / (2 * η) + 4 * W * w4) := by
    have e1 : conductance (oldScattering b e X') * w4 ≤
        (conductance (oldScattering b e X) + 2 * W * (1 - t ^ 2)) * w4 :=
      mul_le_mul_of_nonneg_right hg' hw4
    have e2 : 2 * W * (1 - t ^ 2) * w4 ≤ 2 * W * (2 * (1 - t)) * w4 := by
      have : 0 ≤ 2 * (W : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq this) hw4
    have e3 : (1 - t) / (2 * η) = (1 - t) * (1 / (2 * η)) := by ring
    nlinarith
  calc C * (matchedDistance b e X' + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X') * w4)
      ≤ C * ((matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X) * w4) + (1 - t) * (1 / (2 * η) + 4 * W * w4)) :=
        mul_le_mul_of_nonneg_left key hC
    _ = C * (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X) * w4) + A * (1 - t) := by ring
    _ ≤ _ := by linarith

end BlockBand.Critical.BoundaryMean
