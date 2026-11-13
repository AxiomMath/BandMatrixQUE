module

public import BlockBand.Palm.MomentFlow.MultiAsymp

/-!
# `MultiShortFiniteSpeed` holds

The finite-speed statement `MultiShortFiniteSpeed` for `r ≥ 2` particles, from the hypotheses
`SemimartingaleItoFormula`, `StoppedSemimartingale`, `DysonBrownianMotion` and the Gaussian inputs
`GaussianLpGradient`, `MultivariateGaussianIBP` (through `GoodEvent.spectralGoodEvent_s8`).

* `0 < ε ≤ 1/300`: `multi_fixed` at the scales of `multi_scales`, with the bad event of `GoodEvent.spectralGoodEvent_s8` at
  exponent `D + 1`, `c' = min(1/C, r₀/64)/2` (`C` the upper-count constant of the good event);
* `ε > 1/300`: eventually `r R ≥ r N > occDist`, the initial data vanish on the sector and so does
  every solution (`IsMomentFlowSolution.eq_of_initial_eq`), with `c' = 1`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- `occDist ξ ζ ≤ r (N - 1)` on the sector. -/
theorem occDist_le_sector {N r : ℕ} {ξ ζ : Occ N} (hξ : ξ ∈ sector N r) (hζ : ζ ∈ sector N r) :
    occDist ξ ζ ≤ r * (N - 1) := by
  obtain ⟨x, hx⟩ := exists_occOf r ξ hξ
  obtain ⟨y, hy⟩ := exists_occOf r ζ hζ
  refine occDist_le_of_labs (mem_labs.2 hx) (mem_labs.2 hy) fun m => ?_
  have := BlockBand.Palm.RelativeLocalization.labelDist_lt (x m) (y m)
  omega

/-- **`MultiShortFiniteSpeed` holds.** -/
theorem multiShortFiniteSpeed_holds (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) : MultiShortFiniteSpeed := by
  intro A c r₀ s₀ v₀ hK r hr ε hε
  obtain ⟨c₁, C₁, C, b₀, hc₁, hC₁, hC, hb₀, hD⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  obtain ⟨hc0, -, hr₀, -, -, -⟩ := hK
  by_cases hε3 : ε ≤ 1 / 300
  · set c₂ : ℝ := min (1 / C) (r₀ / 64) with hc₂def
    have hc₂ : 0 < c₂ := lt_min (by positivity) (by positivity)
    refine ⟨c₂ / 2, by positivity, fun D => ?_⟩
    obtain ⟨N₁, hN₁⟩ := hD (D + 1)
    obtain ⟨N₂, hN₂⟩ := multi_scales r (D := D) (C₁ := C₁) hε hε3 hC hc₁ hr₀ hc0 hc₂
    refine ⟨max (max N₁ N₂) 3, fun N hN F E hFC => ?_⟩
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
    have hNpos : 0 < N := by omega
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    obtain ⟨-, ha, hℓ, P2, P3, P4, P5, P6, P7⟩ := hN₂ N hN2
    have hbad0 := hN₁ N hN1 F E hFC
    have hbad : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 3 := by
      have hNp : (0 : ℝ) < N := by linarith
      rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hNp, Real.rpow_neg_one]
      have hND : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num) hNr) hND.le
    intro a ℓ R s u has hsu huc ξ hξ
    exact multi_fixed r (hIto _) hStop (hDBM N) hNpos hFC.1 (E := E) (c := c)
      (τ := (N : ℝ) ^ (-(1 / 100 : ℝ))) (r₀ := r₀) (c₁ := c₁) (C₁ := C₁) (C := C) (b₀ := b₀)
      (ε := ε) (D := D) (c₂ := c₂) (h := (N : ℝ) ^ (-(1 / 100 : ℝ))) (ℓ := ℓ)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) ha hr₀ hc₁ hC₁ hC (min_le_left _ _)
      (min_le_right _ _) hℓ P2 P3 P4 P5 P6 P7
      (hbad0.trans (ENNReal.ofReal_le_ofReal hbad)) s u has hsu huc ξ hξ
  · push Not at hε3
    refine ⟨1, one_pos, fun D => ?_⟩
    obtain ⟨N₂, hN₂⟩ := multi_scales_large hε3
    refine ⟨max N₂ 1, fun N hN F E hFC => ?_⟩
    intro a ℓ R s u has hsu huc ξ hξ
    have hNR : (N : ℝ) ≤ R := hN₂ N (le_trans (le_max_left _ _) hN)
    have hempty : {ω : FlowSample N | (∀ k : Fin N, 0 < ξ k →
          |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = if (r : ℝ) * R < (occDist ξ ζ : ℝ) then 1 else 0) ∧
          Real.exp (-(1 * (N : ℝ) ^ ε)) < Φ u ξ} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, Φ, hΦ, hΦ0, hΦu⟩
      have h0 : ∀ ζ ∈ sector N r, Φ s ζ = (fun _ _ => (0 : ℝ)) s ζ := by
        intro ζ hζ
        rw [hΦ0 ζ hζ, ite_eq_right]
        intro hlt
        have h1 : (occDist ξ ζ : ℝ) ≤ r * ((N : ℝ) - 1) := by
          have := occDist_le_sector hξ hζ
          have h1N : 1 ≤ N := le_trans (le_max_right _ _) hN
          have : ((occDist ξ ζ : ℕ) : ℝ) ≤ ((r * (N - 1) : ℕ) : ℝ) := by exact_mod_cast this
          rw [Nat.cast_mul, Nat.cast_sub h1N, Nat.cast_one] at this
          exact this
        have h2 : (r : ℝ) * ((N : ℝ) - 1) < (r : ℝ) * R := by
          have hr' : (0 : ℝ) < r := by exact_mod_cast hr
          nlinarith
        linarith
      have heq := hΦ.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j)
        (isMomentFlowSolution_const _ r s u 0) h0 u ⟨hsu, le_rfl⟩ ξ hξ
      rw [heq] at hΦu
      exact absurd hΦu (not_lt.mpr (Real.exp_pos _).le)
    rw [hempty, measure_empty]
    exact bot_le

end BlockBand.Palm.MomentFlow
