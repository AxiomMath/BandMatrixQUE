module

public import BlockBand.SourceProcess.PhysApprox.B3GenDoob

/-!
# Per-step Gram estimates and their summation

The summed Gram errors are reduced, as for `𝒦`, to **per-step** bounds in the shape of
`ContractingWords.SummedStep`: each per-step error is at most `C W⁻¹(genStepRate ρ j + W^{-1/2})`.
Summation is `gen_tendsto_sum_of_stepBound`, and the Doob split is `genBrStep_le`.

* `GramSumStepDrift ⇒ GenReqGramDrift` (`genReqGramDrift_of_step`);
* `GramSumStepBracket ⇒ GenReqGramBracket` (`genReqGramBracket_of_step`);
* `GramSumStepMemL2 + GramSumStepMeanL2 + GramSumStepCov ⇒ GramSumStepBracket`
  (`gramSumStepBracket_of_cov`). The Gram-only `L²` estimates follow from `GenStepMemL2`,
  `GenStepMeanL2` (`gramSumStepMemL2_of_gen`, `gramSumStepMeanL2_of_gen`);
* the statement `ComplexClosedSummed` (defined in another module) from the per-step estimates of
  both halves (`complexClosedSummed_of_gramSteps`, `complexClosedSummed_of_allCov`).
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

/-!
## The per-step Gram estimates
-/

/-- **One-step Gram drift** (the closed-system Gram generator). There are `C ≥ 0` and
`0 ≤ ρ < 1` such that, eventually in `W`, at every step `n_s ≤ j < ⌊WT⌋` without a birth and for
every Gram coordinate `e`,
`E|1_{A_j}(E_j[1_{A_j} dG_e] - W⁻¹ gramDriftEntry_e(G_j))| ≤ C W⁻¹(genStepRate + W^{-1/2})`.
The geometric part is `E[1_{A_j} e_j Σ_Σ |(V_jᴴΣV_j)_{ab}|]`, with `Σ ∈ {P𝕊, 𝕊*P, P𝕊P, P𝕊*P}`
for the closed frame `V_j`: the contracting Gram coordinates, which must decay after each
restart. -/
def GramSumStepDrift : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
    ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      genDriftStep b E s h τ m R W j (Vs W) (Sum.inl e : CIdx K np) ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **One-step Gram–Gram bracket** (the Gram covariance): the conditional
`E_j[1_{A_j} dG_e dG_e']` matches `W⁻¹ gramCovEntry_{e,e'}(G_j)` up to
`C W⁻¹(genStepRate + W^{-1/2})` in `L¹` on the alive set. This is the raw second-moment form
of `ContractingWords.LayerCov`; `gramSumStepBracket_of_cov` derives it from the centred form. -/
def GramSumStepBracket : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
    ∀ e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      genBrStep b E s h τ m R W j (Vs W) (Sum.inl e : CIdx K np) (Sum.inl e') ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **One-step centred Gram–Gram covariance**:
`E|1_{A_j}(E_j[(F - E_jF)(F' - E_jF')] - W⁻¹ gramCovEntry_{e,e'}(G_j))|`, with
`F = 1_{A_j} dG_e` and `F' = 1_{A_j} dG_e'`, is at most `C W⁻¹(genStepRate + W^{-1/2})`. The
geometric part carries the products of two contracting Gram coordinates (`contrCov_one`). -/
def GramSumStepCov : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
    ∀ e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      genCovStep b E s h τ m R W j (Vs W) (Sum.inl e : CIdx K np) (Sum.inl e') ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **Square integrability of the alive Gram increments** (the Gram coordinates of
 `GenStepMemL2`). -/
def GramSumStepMemL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
    ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator
        (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np))) 2 (closedLaw b W np)

/-- **The Gram mean size, in `L²`** (the Gram coordinates of `GenStepMeanL2`:
the `O(R/W)` Gram drift on the alive set): `∫‖E_j[1_{A_j} dG_e]‖² ≤ C/W²`. -/
def GramSumStepMeanL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
    ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      genMeanSq b E s h τ m R W j (Vs W) (Sum.inl e : CIdx K np) ≤
        ENNReal.ofReal (C / (W : ℝ) ^ 2)

/-!
## Summation
-/

/-- **`GramSumStepDrift ⇒ GenReqGramDrift`.** -/
theorem genReqGramDrift_of_step (hS : GramSumStepDrift) : GenReqGramDrift := by
  intro b E np τ m T s h K Vs hD R e
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hS b E np τ m T s h K Vs hD R
  exact gen_tendsto_sum_of_stepBound s T τ hρ0 hρ1 hC _ (genNoBirthSteps_subset s T τ) _
    (hev.mono fun W hW j hj => hW j hj e)

/-- **`GramSumStepBracket ⇒ GenReqGramBracket`.** -/
theorem genReqGramBracket_of_step (hS : GramSumStepBracket) : GenReqGramBracket := by
  intro b E np τ m T s h K Vs hD R e e'
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hS b E np τ m T s h K Vs hD R
  exact gen_tendsto_sum_of_stepBound s T τ hρ0 hρ1 hC _ (genNoBirthSteps_subset s T τ) _
    (hev.mono fun W hW j hj => hW j hj e e')

/-!
## The Doob split of the Gram bracket
-/

/-- `GenStepMemL2` contains the Gram estimate. -/
theorem gramSumStepMemL2_of_gen (hL : GenStepMemL2) : GramSumStepMemL2 := by
  intro b E np τ m T s h K Vs hD R
  exact (hL b E np τ m T s h K Vs hD R).mono fun W hW j hj e => hW j hj (Sum.inl e)

/-- `GenStepMeanL2` contains the Gram estimate. -/
theorem gramSumStepMeanL2_of_gen (hM : GenStepMeanL2) : GramSumStepMeanL2 := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC, hev⟩ := hM b E np τ m T s h K Vs hD R
  exact ⟨C, hC, hev.mono fun W hW j hj e => hW j hj (Sum.inl e)⟩

/-- **`GramSumStepMemL2 + GramSumStepMeanL2 + GramSumStepCov ⇒ GramSumStepBracket`.** -/
theorem gramSumStepBracket_of_cov (hL : GramSumStepMemL2) (hM : GramSumStepMeanL2)
    (hC : GramSumStepCov) : GramSumStepBracket := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C₂, hC₂, hevM⟩ := hM b E np τ m T s h K Vs hD R
  obtain ⟨C₁, ρ, hC₁, hρ0, hρ1, hevC⟩ := hC b E np τ m T s h K Vs hD R
  refine ⟨C₁ + 2 * C₂, ρ, by linarith, hρ0, hρ1, ?_⟩
  filter_upwards [hL b E np τ m T s h K Vs hD R, hevM, hevC, eventually_ge_atTop 1]
    with W hWL hWM hWC hW1 j hj e e'
  exact (genBrStep_le b E s h τ m R W j (Vs W) _ _ (hWL j hj e) (hWL j hj e')).trans
    (gen_stepBound_add_meanSq τ hρ0 hC₁ hC₂ hW1 j (hWC j hj e e') (hWM j hj e) (hWM j hj e'))

/-- **`GenReqGramBracket` from the centred Gram covariance and the Gram `L²` estimates.** -/
theorem genReqGramBracket_of_cov (hL : GramSumStepMemL2) (hM : GramSumStepMeanL2)
    (hC : GramSumStepCov) : GenReqGramBracket :=
  genReqGramBracket_of_step (gramSumStepBracket_of_cov hL hM hC)

/-!
## `ComplexClosedSummed` from the per-step estimates of both halves
-/

/-- **`ComplexClosedSummed` from the per-step Gram and `𝒦` estimates and the birth half.** -/
theorem complexClosedSummed_of_gramSteps (hGD : GramSumStepDrift) (hGB : GramSumStepBracket)
    (hB : GenReqBirth) (hKD : KStepDrift) (hKB : KStepBracket) (hKC : KStepConj) :
    ComplexClosedSummed :=
  complexClosedSummed_of_steps (genReqGramDrift_of_step hGD) (genReqGramBracket_of_step hGB) hB
    hKD hKB hKC

/-- **`ComplexClosedSummed` from the finest estimates**: the two drift estimates, the shared `L²`
estimates `GenStepMemL2`, `GenStepMeanL2` (all coordinates), the three centred-covariance estimates
and the birth half. -/
theorem complexClosedSummed_of_allCov (hGD : GramSumStepDrift) (hB : GenReqBirth)
    (hKD : KStepDrift) (hL : GenStepMemL2) (hM : GenStepMeanL2) (hGC : GramSumStepCov)
    (hKB : KStepCov) (hKC : KStepConjCov) : ComplexClosedSummed :=
  complexClosedSummed_of_cov (genReqGramDrift_of_step hGD)
    (genReqGramBracket_of_cov (gramSumStepMemL2_of_gen hL) (gramSumStepMeanL2_of_gen hM) hGC)
    hB hKD hL hM hKB hKC

end BlockBand.SourceProcess.PhysApprox.B3
