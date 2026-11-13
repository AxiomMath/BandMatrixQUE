module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepDefs

/-!
# `CovDecayHyp` from the contracting decay

The hypothesis `CovDecayHyp Z` asks `‖1_{A_j}Z_j‖₄ ≤ C(genStepRate ρ j + W^{-1/2})` at
the no-birth steps. For the concrete `Z = b3CovZ = Σ_{σ,k,l}|Q^σ_{kl}|` this is
`B3ClosedContrDecay` at `p = 4`, summed over the `4|SrcCol|²` coordinates by Minkowski:

* **`covDecayHyp_b3CovZ : B3ClosedContrDecay → CovDecayHyp b3CovZ`**, with constant
  `4|SrcCol|²·C₄`, the same `ρ`, uniformly in `W`, `j` and the columns;
* `covDecayHypP_b3CovZ`: the same at every exponent `p ≥ 1` (used for products of contracting
  coordinates through Hölder).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-- The alive contracting sum is the sum of the norms of the alive coordinates. -/
theorem indicator_b3CovZ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (s h : ℝ) (K W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ)
    (A : Set (ProbedPath W np × ℝ)) :
    A.indicator (b3CovZ b E np τ m s h K W Vs j) =
      ∑ x : Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np),
        fun y => ‖A.indicator (b3ContrCoord b E s h τ m W j Vs x.1 x.2.1 x.2.2) y‖ := by
  funext y
  rw [Finset.sum_apply]
  by_cases hy : y ∈ A
  · simp only [Set.indicator_of_mem hy, b3CovZ]
  · simp [Set.indicator_of_notMem hy]

/-- **The decay of the contracting sum in every `L^p`, `p ≥ 1`.** -/
theorem covDecayHypP_b3CovZ (hD : B3ClosedContrDecay) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p →
      ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
        eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
            (b3CovZ b E np τ m s h K W (Vs W) j)) (ENNReal.ofReal p) (closedLaw b W np) ≤
          ENNReal.ofReal (C * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hD b E np τ m T s h K Vs hFD R p hp
  set N : ℝ := (Fintype.card (Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np)) : ℝ) with hNdef
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨N * C, ρ, mul_nonneg hN hC, hρ0, hρ1, ?_⟩
  filter_upwards [hev] with W hW j hj1 hj2
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set r : ℝ := genStepRate ρ s τ W j + 1 / Real.sqrt W
  have hr : 0 ≤ r := add_nonneg (genStepRate_nonneg hρ0 s τ W j) (by positivity)
  rw [indicator_b3CovZ]
  refine (eLpNorm_sum_le hp1).trans ?_
  have hterm : ∀ x : Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np),
      eLpNorm (fun y => ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3ContrCoord b E s h τ m W j (Vs W) x.1 x.2.1 x.2.2) y‖) (ENNReal.ofReal p)
          (closedLaw b W np) ≤ ENNReal.ofReal (C * r) := by
    intro x
    have hx := hW j hj1 hj2 x.1 x.2.1 x.2.2
    have hm := aestronglyMeasurable_of_eLpNorm_ne_top (hx.trans_lt ENNReal.ofReal_lt_top).ne
    rw [eLpNorm_norm _ hm]
    exact hx
  refine (Finset.sum_le_sum fun x _ => hterm x).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc,
    ENNReal.ofReal_mul hN, hNdef, ENNReal.ofReal_natCast]

/-- **`CovDecayHyp` for the concrete contracting sum, from the contracting decay
`B3ClosedContrDecay`.** -/
theorem covDecayHyp_b3CovZ (hD : B3ClosedContrDecay) : CovDecayHyp b3CovZ := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := covDecayHypP_b3CovZ hD b E np τ m T s h K Vs hFD R 4
    (by norm_num)
  refine ⟨C, ρ, hC, hρ0, hρ1, ?_⟩
  filter_upwards [hev] with W hW j hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj
  have := hW j hj.1.1 hj.1.2.le
  rwa [ENNReal.ofReal_ofNat] at this

end BlockBand.SourceProcess.PhysApprox.B3
