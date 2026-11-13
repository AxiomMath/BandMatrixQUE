module

public import BlockBand.SourceProcess.PhysApprox.B3GenSplit

/-!
# Per-step generator estimates for the `𝒦` half and their summation

The summed `𝒦` errors are reduced to **per-step** bounds in the shape of
`ContractingWords.SummedStep` (each per-step error at most `C W⁻¹(ρ^{j-r} + W^{-1/2})`, `r` a
restart: the closing length `n_s` or one step after a tag birth). Summing the geometric terms per
restart gives `C(n_p + 1)/((1-ρ)W) + C T₊/√W → 0` (`gen_tendsto_sum_of_stepBound`).

**Why a geometric shape.** The `𝒦`-multiplier mean has size `C(δ₀ + W⁻²) Tr M_pr`, with
`‖δ₀‖_{L^p} ≤ C_p/W` (the passive jet moments). Summed over the `≈ (T - s)W` steps this is
`C R (T - s) W · E δ₀ + O(W⁻¹)`, which is `O(1)`, not `o(1)`; the bound of
`RawTag.delta_fresh_bounds` (`Cm(δ₀ + W⁻¹)`) is weaker still. The summed drift error vanishes
only because the `O(δ₀)` part of the mean is `O(δ₀) V*P𝕊V`, whose factor `V*P𝕊V` is a
contracting word: after each restart it decays like `ρ^{j-r}` down to `O(W^{-1/2})`. That is the
content of the per-step estimates below.

* `genStepRate ρ s τ W j = Σ_{r ∈ restarts} [r ≤ j] ρ^{j-r}` (it dominates `ρ^{j - r_j}` for the
  last restart `r_j ≤ j`);
* `gen_sum_stepRate_le`: `Σ_{j < n} genStepRate ≤ (n_p + 1)/(1 - ρ)`;
* `gen_tendsto_sum_of_stepBound`: per-step bounds ⇒ the sums tend to `0`;
* the per-step estimates `KStepDrift`, `KStepBracket`, `KStepConj` and the reductions
  `kDriftSummed_of_step`, `kBracketSummed_of_step`, `kConjSummed_of_step`.
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
## Restarts and the geometric rate
-/

/-- The restarts of the closed process: the closing length `n_s` and the step after each tag
birth `⌊Wτ_i⌋ + 1`. -/
def genRestarts (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) : Finset ℕ :=
  insert (closeLen s W) (univ.image fun i => ⌊(W : ℝ) * τ i⌋₊ + 1)

/-- The geometric rate `Σ_{r ∈ restarts, r ≤ j} ρ^{j-r}`. -/
def genStepRate (ρ s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W j : ℕ) : ℝ :=
  ∑ r ∈ genRestarts s τ W, if r ≤ j then ρ ^ (j - r) else 0

theorem card_genRestarts_le (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) :
    (genRestarts s τ W).card ≤ np + 1 := by
  unfold genRestarts
  refine (card_insert_le _ _).trans ?_
  have := card_image_le (s := (univ : Finset (Fin np))) (f := fun i => ⌊(W : ℝ) * τ i⌋₊ + 1)
  simp only [card_univ, Fintype.card_fin] at this
  omega

theorem gen_stepTerm_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (r j : ℕ) :
    0 ≤ (if r ≤ j then ρ ^ (j - r) else 0) := by
  split_ifs
  · exact pow_nonneg hρ0 _
  · exact le_rfl

theorem genStepRate_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W j : ℕ) :
    0 ≤ genStepRate ρ s τ W j :=
  sum_nonneg fun r _ => gen_stepTerm_nonneg hρ0 r j

/-- One geometric tail: `Σ_{j < n} [r ≤ j] ρ^{j-r} ≤ (1 - ρ)⁻¹`. -/
theorem gen_sum_range_stepTerm_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (r n : ℕ) :
    ∑ j ∈ range n, (if r ≤ j then ρ ^ (j - r) else 0) ≤ (1 - ρ)⁻¹ := by
  have hinv : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith)
  rcases le_or_gt r n with hrn | hrn
  · rw [← sum_range_add_sum_Ico _ hrn, sum_Ico_eq_sum_range]
    have h0 : ∑ j ∈ range r, (if r ≤ j then ρ ^ (j - r) else 0) = 0 :=
      sum_eq_zero fun j hj =>
        ite_eq_right_iff.2 fun h => absurd h (by simp only [mem_range] at hj; omega)
    rw [h0, zero_add]
    simp only [le_add_iff_nonneg_right, zero_le, ↓reduceIte, add_tsub_cancel_left]
    calc ∑ k ∈ range (n - r), ρ ^ k ≤ ρ ^ 0 / (1 - ρ) := by
          rw [range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hρ0 hρ1
      _ = (1 - ρ)⁻¹ := by rw [pow_zero, one_div]
  · have h0 : ∑ j ∈ range n, (if r ≤ j then ρ ^ (j - r) else 0) = 0 :=
      sum_eq_zero fun j hj =>
        ite_eq_right_iff.2 fun h => absurd h (by simp only [mem_range] at hj; omega)
    rw [h0]; exact hinv

/-- **The summed geometric rate**: over any set of steps below `n`, `Σ genStepRate ≤
(n_p + 1)/(1 - ρ)`. -/
theorem gen_sum_stepRate_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (s : ℝ) {np : ℕ}
    (τ : Fin np → ℝ) (W n : ℕ) (S : Finset ℕ) (hS : S ⊆ range n) :
    ∑ j ∈ S, genStepRate ρ s τ W j ≤ (np + 1) * (1 - ρ)⁻¹ := by
  have hinv : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith)
  unfold genStepRate
  rw [sum_comm]
  calc ∑ r ∈ genRestarts s τ W, ∑ j ∈ S, (if r ≤ j then ρ ^ (j - r) else 0)
      ≤ ∑ r ∈ genRestarts s τ W, (1 - ρ)⁻¹ := by
        refine sum_le_sum fun r _ => ?_
        exact (sum_le_sum_of_subset_of_nonneg hS fun j _ _ => gen_stepTerm_nonneg hρ0 r j).trans
          (gen_sum_range_stepTerm_le hρ0 hρ1 r n)
    _ = (genRestarts s τ W).card * (1 - ρ)⁻¹ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (np + 1) * (1 - ρ)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ hinv
        exact_mod_cast card_genRestarts_le s τ W

/-!
## Summation of per-step bounds
-/

theorem gen_floor_mul_le (T : ℝ) (W : ℕ) :
    ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ W * max T 0 := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  calc ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ ((⌊(W : ℝ) * max T 0⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.floor_le_floor (mul_le_mul_of_nonneg_left (le_max_left T 0) hW)
    _ ≤ W * max T 0 := Nat.floor_le (mul_nonneg hW (le_max_right T 0))

/-- **Per-step bounds in the `SummedStep` shape sum to `o(1)`.** If, eventually, every step
`j ∈ S W ⊆ [n_s, ⌊WT⌋)` has `f W j ≤ C/W · (genStepRate ρ j + W^{-1/2})`, then
`Σ_{j ∈ S W} f W j → 0`. -/
theorem gen_tendsto_sum_of_stepBound (s T : ℝ) {np : ℕ} (τ : Fin np → ℝ) {ρ C : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (S : ℕ → Finset ℕ)
    (hS : ∀ W, S W ⊆ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊) (f : ℕ → ℕ → ℝ≥0∞)
    (hf : ∀ᶠ W in atTop, ∀ j ∈ S W,
      f W j ≤ ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))) :
    Tendsto (fun W => ∑ j ∈ S W, f W j) atTop (𝓝 0) := by
  set A : ℝ := C * ((np + 1) * (1 - ρ)⁻¹)
  set B : ℝ := C * max T 0
  have hA : 0 ≤ A := mul_nonneg hC (mul_nonneg (by positivity) (inv_nonneg.2 (by linarith)))
  have hB : 0 ≤ B := mul_nonneg hC (le_max_right T 0)
  have hu : Tendsto (fun W : ℕ => A * (W : ℝ)⁻¹ + B * (Real.sqrt W)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun W : ℕ => (W : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using (h1.const_mul A).add (h2.const_mul B)
  have hup : Tendsto (fun W : ℕ => ENNReal.ofReal (A * (W : ℝ)⁻¹ + B * (Real.sqrt W)⁻¹))
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hu
    rw [ENNReal.ofReal_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hf, eventually_ge_atTop 1] with W hW hW1
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.2 hWpos
  have hterm : ∀ j ∈ S W, 0 ≤ C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W) := fun j _ =>
    mul_nonneg (div_nonneg hC hWpos.le) (add_nonneg (genStepRate_nonneg hρ0 s τ W j)
      (one_div_nonneg.2 hsq.le))
  calc ∑ j ∈ S W, f W j
      ≤ ∑ j ∈ S W, ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) :=
        sum_le_sum hW
    _ = ENNReal.ofReal (∑ j ∈ S W, C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) :=
        (ENNReal.ofReal_sum_of_nonneg hterm).symm
    _ ≤ ENNReal.ofReal (A * (W : ℝ)⁻¹ + B * (Real.sqrt W)⁻¹) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
        have hsub : S W ⊆ range ⌊(W : ℝ) * T⌋₊ := fun j hj => by
          have := hS W hj; simp only [mem_Ico] at this; simp only [mem_range]; omega
        have hrate := gen_sum_stepRate_le hρ0 hρ1 s τ W _ (S W) hsub
        have hcard : ((S W).card : ℝ) ≤ W * max T 0 := by
          have h1 : (S W).card ≤ ⌊(W : ℝ) * T⌋₊ := by
            simpa using card_le_card hsub
          exact (Nat.cast_le.2 h1).trans (gen_floor_mul_le T W)
        have hCW : 0 ≤ C / W := div_nonneg hC hWpos.le
        calc C / W * (∑ j ∈ S W, genStepRate ρ s τ W j + (S W).card * (1 / Real.sqrt W))
            ≤ C / W * ((np + 1) * (1 - ρ)⁻¹ + W * max T 0 * (1 / Real.sqrt W)) := by
              refine mul_le_mul_of_nonneg_left (add_le_add hrate ?_) hCW
              exact mul_le_mul_of_nonneg_right hcard (one_div_nonneg.2 hsq.le)
          _ = A * (W : ℝ)⁻¹ + B * (Real.sqrt W)⁻¹ := by
              simp only [A, B]
              field_simp

/-!
## The per-step `𝒦` estimates and their summation
-/

/-- **One-step `𝒦` drift** (the mean of the complex source update for the closed `𝒦`). There
are `C ≥ 0` and `0 ≤ ρ < 1` such that, eventually in `W`, at every step `n_s ≤ j < ⌊WT⌋` without a
birth, `E|1_{A_j} E_j[1_{A_j} d𝒦_ij]| ≤ C W⁻¹(genStepRate + W^{-1/2})`. The geometric part
carries the contracting factor `V*P𝕊V` of the `O(δ₀)` mean. -/
def KStepDrift : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      genDriftStep b E s h τ m R W j (Vs W) (Sum.inr ij : CIdx K np) ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **One-step brackets with a `𝒦` coordinate**: the conditional
`E_j[d𝒦_ij dX_c']` matches `W⁻¹ cCov` (`0` for `c' = 𝒦_kl`, `kGramCov` for a Gram `c'`) up to
`C W⁻¹(genStepRate + W^{-1/2})` in `L¹` on the alive set. The equal-sign covariance of `𝒜`
carries the contracting letters (geometric part); the opposite-sign one is `D₀P⊗P'/(2W)`. -/
def KStepBracket : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ (ij : Fin np × Fin np) (c' : CIdx K np),
      genBrStep b E s h τ m R W j (Vs W) (Sum.inr ij) c' ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **One-step conjugate bracket**: `E_j[d𝒦_ij conj d𝒦_kl]` matches
`W⁻¹ kConjCov` up to `C W⁻¹(genStepRate + W^{-1/2})` in `L¹` on the alive set. -/
def KStepConj : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij kl : Fin np × Fin np,
      genConjStep (K := K) b E s h τ m R W j (Vs W) ij kl ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

theorem genNoBirthSteps_subset (s T : ℝ) {np : ℕ} (τ : Fin np → ℝ) (W : ℕ) :
    genNoBirthSteps s T τ W ⊆ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊ :=
  filter_subset _ _

/-- **`KStepDrift ⇒ KDriftSummed`.** -/
theorem kDriftSummed_of_step (hS : KStepDrift) : KDriftSummed := by
  intro b E np τ m T s h K Vs hD R ij
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hS b E np τ m T s h K Vs hD R
  exact gen_tendsto_sum_of_stepBound s T τ hρ0 hρ1 hC _ (genNoBirthSteps_subset s T τ) _
    (hev.mono fun W hW j hj => hW j hj ij)

/-- **`KStepBracket ⇒ KBracketSummed`.** -/
theorem kBracketSummed_of_step (hS : KStepBracket) : KBracketSummed := by
  intro b E np τ m T s h K Vs hD R ij c'
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hS b E np τ m T s h K Vs hD R
  exact gen_tendsto_sum_of_stepBound s T τ hρ0 hρ1 hC _ (genNoBirthSteps_subset s T τ) _
    (hev.mono fun W hW j hj => hW j hj ij c')

/-- **`KStepConj ⇒ KConjSummed`.** -/
theorem kConjSummed_of_step (hS : KStepConj) : KConjSummed := by
  intro b E np τ m T s h K Vs hD R ij kl
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := hS b E np τ m T s h K Vs hD R
  simp only [b3ConjErr_eq_gen]
  exact gen_tendsto_sum_of_stepBound s T τ hρ0 hρ1 hC _ (genNoBirthSteps_subset s T τ) _
    (hev.mono fun W hW j hj => hW j hj ij kl)

/-- **`ComplexClosedSummed` from the per-step `𝒦` estimates and the other halves.** -/
theorem complexClosedSummed_of_steps (hGD : GenReqGramDrift) (hGB : GenReqGramBracket)
    (hB : GenReqBirth) (hKD : KStepDrift) (hKB : KStepBracket) (hKC : KStepConj) :
    ComplexClosedSummed :=
  complexClosedSummed_of_parts hGD hGB hB (kDriftSummed_of_step hKD)
    (kBracketSummed_of_step hKB) (kConjSummed_of_step hKC)

end BlockBand.SourceProcess.PhysApprox.B3
