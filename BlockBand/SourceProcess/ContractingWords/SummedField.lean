module

public import BlockBand.SourceProcess.ContractingWords.Summed

/-!
# Assembly of the field `summed`

`summed_of`: summing the per-step bound `SummedStep` over the steps `εW ≤ j < TW` gives the field
`summed` of the contracting-words statement; the geometric terms are summed per restart
(`sum_err_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- The arithmetic of the summation: `Σ_{j∈S} C/W(ρ^{j-r_j} + W^{-1/2}) ≤ C'(W^{-1/2} + W⁻¹)`. -/
theorem sum_err_le {C ρ ε T : ℝ} (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hT : 0 < T)
    {W : ℕ} (hW : 1 ≤ W) {nT : ℕ} (k : Fin nT → ℕ) (S : Finset ℕ)
    (hS : ∀ j ∈ S, ⌈ε * W⌉₊ ≤ j) (hcard : (S.card : ℝ) ≤ T * W) :
    ∑ j ∈ S, C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W) ≤
      (C * (nT + 1) / (1 - ρ) + C * T) * (1 / Real.sqrt W + 1 / W) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hsq := Real.sq_sqrt hWpos.le
  have h1ρ : 0 < 1 - ρ := by linarith
  have hgeo := sum_pow_restart_le hρ0 hρ1 ε W k S hS
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hA : C / W * (∑ j ∈ S, ρ ^ (j - restartIndex ε W k j)) ≤
      C * (nT + 1) / (1 - ρ) * (1 / W) := by
    calc C / W * (∑ j ∈ S, ρ ^ (j - restartIndex ε W k j))
        ≤ C / W * ((nT + 1) / (1 - ρ)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = C * (nT + 1) / (1 - ρ) * (1 / W) := by ring
  have hB : C / W * ((S.card : ℝ) * (1 / Real.sqrt W)) ≤ C * T * (1 / Real.sqrt W) := by
    have : C / W * ((S.card : ℝ) * (1 / Real.sqrt W)) =
        C * ((S.card : ℝ) / W) * (1 / Real.sqrt W) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (by positivity)
    rw [div_le_iff₀ hWpos]; exact hcard
  have hpos1 : 0 ≤ C * (nT + 1) / (1 - ρ) := by positivity
  have hpos2 : 0 ≤ C * T := mul_nonneg hC hT.le
  rw [mul_add]
  nlinarith [mul_nonneg hpos1 (show (0 : ℝ) ≤ 1 / Real.sqrt W by positivity),
    mul_nonneg hpos2 (show (0 : ℝ) ≤ 1 / (W : ℝ) by positivity)]

/-- **The field `summed`**, from the per-step bound `SummedStep`. -/
theorem summed_of (hS : SummedStep) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T K : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      let μ := growthPathLaw W b
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      let F : ℕ → GrowthPath W → ℂ := fun j ω => polyValue b E k q W j ω Φ
      let steps := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => ε * W ≤ (j : ℝ) ∧ ∀ a, j ≠ k a
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => F (j + 1) ω - F j ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω
              (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W)) ∧
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => (F (j + 1) ω - F j ω) ^ 2) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W)) := by
  intro b hb0 hb κI hκ nT nI q hq Φ hΦ ε T K hε hεT
  obtain ⟨C, ρ, W₀, hC, hρ0, hρ1, hstep⟩ := hS b hb0 hb κI hκ nT nI q hq Φ hΦ ε T K hε hεT
  have hT : 0 < T := lt_trans hε hεT
  refine ⟨C * (nT + 1) / (1 - ρ) + C * T, max W₀ 1, fun W hW E hE k hk => ?_⟩
  intro μ A F steps
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hTW : 0 ≤ T * W := by positivity
  have hmem : ∀ j ∈ steps, ε * W ≤ (j : ℝ) ∧ (∀ a, j ≠ k a) ∧ ((j + 1 : ℕ) : ℝ) ≤ T * W := by
    intro j hj
    obtain ⟨hjr, h1, h2⟩ := Finset.mem_filter.mp hj
    refine ⟨h1, h2, le_trans ?_ (Nat.floor_le hTW)⟩
    exact_mod_cast Finset.mem_range.mp hjr
  have hceil : ∀ j ∈ steps, ⌈ε * W⌉₊ ≤ j := fun j hj => Nat.ceil_le.mpr (hmem j hj).1
  have hcard : (steps.card : ℝ) ≤ T * W := by
    have h1 : steps.card ≤ ⌊T * W⌋₊ :=
      (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hTW)
  have hsum := sum_err_le hC hρ0 hρ1 hT hW1 k steps hceil hcard
  have herr0 : ∀ j ∈ steps, 0 ≤ C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W) :=
    fun j _ => by positivity
  have hfin : ∑ j ∈ steps,
      ENNReal.ofReal (C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)) ≤
        ENNReal.ofReal ((C * (nT + 1) / (1 - ρ) + C * T) * (1 / Real.sqrt W + 1 / W)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg herr0]; exact ENNReal.ofReal_le_ofReal hsum
  refine ⟨le_trans (Finset.sum_le_sum fun j hj => ?_) hfin,
    le_trans (Finset.sum_le_sum fun j hj => ?_) hfin⟩
  · obtain ⟨h1, h2, h3⟩ := hmem j hj
    exact (hstep W (le_of_max_le_left hW) E hE k hk j h1 h2 h3).1
  · obtain ⟨h1, h2, h3⟩ := hmem j hj
    exact (hstep W (le_of_max_le_left hW) E hE k hk j h1 h2 h3).2

end BlockBand.SourceProcess.ContractingWords
