module

public import BlockBand.LocalWindow.ProofPartOneGrid
public import BlockBand.LocalWindow.Proof
public import BlockBand.LocalWindow.ProofTruncationBounds

/-!
# The deterministic conclusion of part (i) at one selected energy

Off the exceptional events, the two clauses of part (i) of the physical local-window lemma hold
at a single selected energy.

## Main results

* `spectralSum_ind_mono`: window counts are monotone in the radius.
* **`partOne_point`**: off the crowding, pole and Poisson-bad events, with the grid and
  absorption inequalities, the two clauses of part (i) hold at `E` with `c = v₀/2` and any
  `C₁ ≥ max(L + 1, 2/v₀ + 1)`; `L = 4/v₀²` makes `c, C₁` depend on `v₀` only (not on `γ, ε, D`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartOne

open Matrix
open BlockBand.LocalWindow.ProofCount BlockBand.Coarea

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Window counts are monotone in the window radius. -/
theorem spectralSum_ind_mono {A : Matrix β β ℂ} (hA : A.IsHermitian) {a b : ℝ} (hab : a ≤ b) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A (fun l => if |l| ≤ a then 1 else 0) ≤
      BlockBand.Internal.Contracts.Inputs.spectralSum A (fun l => if |l| ≤ b then 1 else 0) := by
  rw [spectralSum_eq_sum hA, spectralSum_eq_sum hA]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : |hA.eigenvalues j| ≤ a
  · simp [h, h.trans hab]
  · simp only [h, ite_false]; split_ifs <;> norm_num

/-- **Deterministic conclusion of part (i) of the physical local window at one selected
energy.** Let `H_R, V, G` be Hermitian, `‖C‖, ‖C*‖ ≤ c`, `ε₀ > 0`, `E` a nonpole
energy with at most one eigenvalue of `H_R` within `ε₀`, `e` a grid energy with
`|E - e| ≤ h`, and `Â = F̂(e) + G - e` not Poisson-bad (`PoissonBad (2W) δ v₀ η L`). If
`L ≥ 1`, `L v₀² ≥ 4`, `C₁ ≥ max(L + 1, 2/v₀ + 1)`, `(c²/ε₀² + 1) h ≤ η`, `|β| = 2W` and the two
absorption inequalities `3(2W)^δ + 2 ≤ (v₀/2) W η`, `(2W)^δ + 2W (c²/ε₀² + 1) h/η + 2 ≤ W η`
hold, then `A = F(E) - E + G` satisfies `(v₀/2) W η ≤ N_A([-C₁η, C₁η])` and
`Σ η²/(λ² + η²) ≤ C₁ W η` (the clauses of part (i) with `c = v₀/2`). Proof:
`isPerturbation_grid`, `isPerturbation_actual`, `partOne_core`, monotonicity of the window. -/
theorem partOne_point {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ)
    {V G : Matrix β β ℂ} (hV : V.IsHermitian) (hG : G.IsHermitian)
    {ε₀ c E e h δ v₀ η L C₁ Wr : ℝ} (hε₀ : 0 < ε₀) (hc : 0 ≤ c)
    (hC : ∀ y, ‖T C y‖ ≤ c * ‖y‖) (hC' : ∀ w, ‖T Cᴴ w‖ ≤ c * ‖w‖)
    (hdet : (H_R - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0)
    (hnear : (nearSet ε₀ hH E).card ≤ 1) (hEe : |E - e| ≤ h)
    (hη : 0 < η) (hL : 1 ≤ L) (hv₀ : 0 < v₀) (hLv : 4 ≤ L * v₀ ^ 2)
    (hd : (Fintype.card β : ℝ) = 2 * Wr)
    (hgood : ¬ PoissonBad (2 * Wr) δ v₀ η L (truncF ε₀ H_R C V e + G - (e : ℂ) • 1))
    (hr : (c ^ 2 / ε₀ ^ 2 + 1) * h ≤ η) (hC₁ : L + 1 ≤ C₁) (hC₁' : 2 / v₀ + 1 ≤ C₁)
    (hW1 : 3 * (2 * Wr) ^ δ + 2 ≤ v₀ / 2 * Wr * η)
    (hW2 : (2 * Wr) ^ δ + 2 * Wr * ((c ^ 2 / ε₀ ^ 2 + 1) * h) / η + 2 ≤ Wr * η) :
    v₀ / 2 * Wr * η ≤ BlockBand.Internal.Contracts.Inputs.spectralSum
        (physicalCoareaF H_R C V E - (E : ℂ) • 1 + G)
        (fun l => if |l| ≤ C₁ * η then 1 else 0) ∧
      BlockBand.Internal.Contracts.Inputs.spectralSum
        (physicalCoareaF H_R C V E - (E : ℂ) • 1 + G) (fun l => η ^ 2 / (l ^ 2 + η ^ 2)) ≤
        C₁ * Wr * η := by
  set r := (c ^ 2 / ε₀ ^ 2 + 1) * |E - e| with hr_def
  have hr0 : 0 ≤ r := mul_nonneg (by positivity) (abs_nonneg _)
  have hrh : r ≤ (c ^ 2 / ε₀ ^ 2 + 1) * h := mul_le_mul_of_nonneg_left hEe (by positivity)
  have hWr : 0 ≤ Wr := by
    have : (0 : ℝ) ≤ Fintype.card β := Nat.cast_nonneg _
    linarith
  have hAeq : physicalCoareaF H_R C V E - (E : ℂ) • 1 + G =
      physicalCoareaF H_R C V E + G - (E : ℂ) • 1 := by abel
  rw [hAeq]
  have hpert := isPerturbation_actual hH C V G hdet hnear
    (isPerturbation_grid hH C V G hε₀ hc hC hC' E e)
  have hA := ProofCertificate.isHermitian_physicalCoareaF hH C hV E
  have hAh := isHermitian_add_sub_smul hA hG E
  have hTr := ProofCertificate.isHermitian_truncF ε₀ H_R C hV e
  have hAhat := isHermitian_add_sub_smul hTr hG e
  obtain ⟨hcore1, hcore2⟩ := partOne_core hAh hAhat hr0 hpert hη (by linarith : (0 : ℝ) < L)
  simp only [PoissonBad, not_or, not_lt] at hgood
  obtain ⟨g1, g2, g3⟩ := hgood
  rw [← spectralSum_eq_count hAhat] at g1 g2
  rw [← spectralSum_eq_count hAhat] at g3
  set P1 := BlockBand.Internal.Contracts.Inputs.spectralSum
    (truncF ε₀ H_R C V e + G - (e : ℂ) • 1) (poissonWeight η)
  set P2 := BlockBand.Internal.Contracts.Inputs.spectralSum
    (truncF ε₀ H_R C V e + G - (e : ℂ) • 1) (poissonWeight (L * η))
  have hdδ : 0 ≤ (2 * Wr) ^ δ := Real.rpow_nonneg (by linarith) _
  have hL0 : 0 < L := by linarith
  constructor
  · have k1 : 2 / L ^ 2 * P2 ≤ 2 / L ^ 2 * (2 * Wr * (L * η) / v₀ + (2 * Wr) ^ δ) :=
      mul_le_mul_of_nonneg_left g3 (by positivity)
    have k2 : 2 / L ^ 2 * (2 * Wr * (L * η) / v₀ + (2 * Wr) ^ δ) =
        4 * (Wr * η) / (L * v₀) + 2 / L ^ 2 * (2 * Wr) ^ δ := by
      field_simp; ring
    have k3 : 4 * (Wr * η) / (L * v₀) ≤ Wr * η * v₀ := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_nonneg hWr hη.le
      nlinarith
    have k4 : 2 / L ^ 2 * (2 * Wr) ^ δ ≤ 2 * (2 * Wr) ^ δ := by
      refine mul_le_mul_of_nonneg_right ?_ hdδ
      exact div_le_self (by norm_num) (one_le_pow₀ hL)
    have hwin : L * η + r ≤ C₁ * η := by nlinarith
    have hmono := spectralSum_ind_mono hAh hwin
    have : 2 * Wr * η * v₀ = 2 * (Wr * η * v₀) := by ring
    push_cast at hcore1
    nlinarith
  · have k1 : (Fintype.card β : ℝ) * (r / η) ≤ 2 * Wr * ((c ^ 2 / ε₀ ^ 2 + 1) * h) / η := by
      have h1 : r / η ≤ (c ^ 2 / ε₀ ^ 2 + 1) * h / η := div_le_div_of_nonneg_right hrh hη.le
      calc (Fintype.card β : ℝ) * (r / η) = 2 * Wr * (r / η) := by rw [hd]
        _ ≤ 2 * Wr * ((c ^ 2 / ε₀ ^ 2 + 1) * h / η) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = 2 * Wr * ((c ^ 2 / ε₀ ^ 2 + 1) * h) / η := by ring
    have k2 : 2 * Wr * η / v₀ ≤ (C₁ - 1) * (Wr * η) := by
      rw [div_le_iff₀ hv₀]
      have h2' : 2 / v₀ ≤ C₁ - 1 := by linarith
      have h2 : 2 ≤ (C₁ - 1) * v₀ := (div_le_iff₀ hv₀).mp h2'
      have := mul_nonneg hWr hη.le
      nlinarith
    push_cast at hcore2
    have : C₁ * Wr * η = (C₁ - 1) * (Wr * η) + Wr * η := by ring
    have hpw : (fun l : ℝ => η ^ 2 / (l ^ 2 + η ^ 2)) = poissonWeight η := rfl
    rw [hpw]
    linarith
