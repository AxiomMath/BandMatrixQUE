module

public import BlockBand.SourceProcess.PhysApprox.B3BirthReduce
public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability

/-!
# The `𝒦` birth estimates through the closing correction

The closed `𝒦` is the unclosed `𝒦 = 𝒥*G𝒥` minus the closing correction
`birthKCorrAt = 2iηz V_prᴴ(1 − zN)⁻¹Π𝕊V_pr` (`Birth.closedKAt_eq_sub`, `rfl`). So the two
`𝒦` birth estimates `ComplexBirthKDiag`, `ComplexBirthCrossK` split into
* `ComplexBirthKFresh` (unclosed fresh diagonal `→ a m_i`, path and probes only),
* `ComplexBirthKFreshCross` (unclosed old/new and new/new entries `→ 0`),
* `ComplexBirthKClosing` (the closing correction of every entry with a newborn index `→ 0` on
  the alive set):
`complexBirthKDiag_of_parts`, `complexBirthCrossK_of_parts`. The cross estimate `ComplexBirthCross`
is split into its Gram and `𝒦` coordinates (`complexBirthCross_of_parts`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal ENNReal ComplexConjugate

/-- **The closing correction of `𝒦` at length `j`**: `2iηz V_jᴴ(1 − zN_j)⁻¹Π𝕊_jV_j`. -/
def birthKCorrAt (b E s h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W j : ℕ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin np) (Fin np) ℂ :=
  ((2 * etaZ b E : ℝ) * Complex.I * phase y.2) •
    ((probeFrame b E W j τ m y.1)ᴴ *
      (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1)))⁻¹ *
      farEmbed (closingPairing b E h W (closeLen s W) y.1.1) *
      scatteringMatrix b E W j y.1.1 * probeFrame b E W j τ m y.1)

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W j : ℕ}

theorem Birth.closedKAt_eq_sub (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W j y =
      complexSourceK b E W j τ m y.1 - birthKCorrAt b E s h τ m W j y := rfl

/-- A function of the path and the probes integrates over the closed law as over the probed
law. -/
theorem Birth.lintegral_closedLaw_fst {f : ProbedPath W np → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y.1 ∂closedLaw b W np = ∫⁻ x, f x ∂probedPathLaw W np b := by
  show ∫⁻ y, f y.1 ∂((probedPathLaw W np b).prod phaseLaw) = _
  rw [lintegral_prod (fun z => f z.1) (hf.comp measurable_fst).aemeasurable]
  simp

/-- The pointwise split `‖1_A((u − c) − t)‖ ≤ ‖u − t‖ + ‖1_A c‖`. -/
theorem Birth.enorm_indicator_sub_le {α : Type*} (A : Set α) (u c : α → ℂ) (t : ℂ) (y : α) :
    ‖A.indicator (fun y => u y - c y - t) y‖ₑ ≤ ‖u y - t‖ₑ + ‖A.indicator c y‖ₑ := by
  by_cases hy : y ∈ A
  · simp only [Set.indicator_of_mem hy]
    calc ‖u y - c y - t‖ₑ = ‖(u y - t) + -c y‖ₑ := by congr 1; ring
      _ ≤ ‖u y - t‖ₑ + ‖-c y‖ₑ := enorm_add_le _ _
      _ = _ := by rw [enorm_neg]
  · simp [Set.indicator_of_notMem hy]

/-- The closed-law birth error of a `𝒦` entry is at most the unclosed error plus the closing
correction. -/
theorem Birth.lintegral_closedK_le (R : ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (n : ℕ) (a a' : Fin np) (t : ℂ) :
    ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
        b3ClosedKAt b E s h τ m W n y a a' - t) y‖ₑ ∂closedLaw b W np ≤
      ∫⁻ x, ‖complexSourceK b E W n τ m x a a' - t‖ₑ ∂probedPathLaw W np b +
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
          birthKCorrAt b E s h τ m W n y a a') y‖ₑ ∂closedLaw b W np := by
  have hm : Measurable fun x : ProbedPath W np => ‖complexSourceK b E W n τ m x a a' - t‖ₑ :=
    ((measurable_complexSourceK b E W n τ m).eval_matrix.sub_const t).enorm
  have key : (fun y => b3ClosedKAt b E s h τ m W n y a a' - t) = (fun y =>
      complexSourceK b E W n τ m y.1 a a' - birthKCorrAt b E s h τ m W n y a a' - t) := rfl
  rw [key]
  have hpt : ∀ y : ProbedPath W np × ℝ, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      complexSourceK b E W n τ m y.1 a a' - birthKCorrAt b E s h τ m W n y a a' - t) y‖ₑ ≤
        ‖complexSourceK b E W n τ m y.1 a a' - t‖ₑ +
          ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
            birthKCorrAt b E s h τ m W n y a a') y‖ₑ := fun y =>
    Birth.enorm_indicator_sub_le (b3Alive b E s h τ m R W j Vs)
      (fun y => complexSourceK b E W n τ m y.1 a a')
      (fun y => birthKCorrAt b E s h τ m W n y a a') t y
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_add_left (f := fun y : ProbedPath W np × ℝ =>
    ‖complexSourceK b E W n τ m y.1 a a' - t‖ₑ) (hm.comp measurable_fst)]
  congr 1
  exact Birth.lintegral_closedLaw_fst hm

/-!
## The estimates
-/

/-- **Unclosed fresh `𝒦` diagonal**: one step after its birth, the
unclosed `𝒦_ii = 𝒥_i*G𝒥_i` of a newborn tag is `a m_i` in `L¹`, uniformly over its birth step in
`[n_s, ⌊WT⌋)`. Path and probes only (no frame, no closing). -/
def ComplexBirthKFresh : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → ∀ θ : ℝ, 0 < θ → ∀ i : Fin np, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ i⌋₊ = j →
        ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x i i - matchedA E * (m i : ℂ)‖ₑ
          ∂probedPathLaw W np b ≤ ENNReal.ofReal θ

/-- **Unclosed `𝒦` cross entries**: one step after a birth, the unclosed
entries `𝒦_{aa'}`, `a ≠ a'`, with a newborn index are `o(1)` in `L¹` ("old/new cross variances
are at most `Cm Tr M_pr/W`"; new/new entries have independent probes). -/
def ComplexBirthKFreshCross : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → ∀ θ : ℝ, 0 < θ → ∀ a a' : Fin np, a ≠ a' → ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
        (⌊(W : ℝ) * τ a⌋₊ = j ∨ ⌊(W : ℝ) * τ a'⌋₊ = j) →
        ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x a a'‖ₑ ∂probedPathLaw W np b ≤ ENNReal.ofReal θ

/-- **Closing correction of the newborn `𝒦` entries**: one step after a birth, the closing
correction `2iηz V_prᴴ(1 − zN)⁻¹Π𝕊V_pr` of every entry with a newborn index is `o(1)` in `L¹` on
the alive set. Its content is that a newborn tag has far birth mass `O(g_A^in/W)`
(`SmallLeak.birth_leak_le`), and that the phase average of the omitted-mode resolvent `(1 − zN)⁻¹`
is paid by `t(1 + |log t|) ≤ C_p t^p`. -/
def ComplexBirthKClosing : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ → ∀ a a' : Fin np, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
        (⌊(W : ℝ) * τ a⌋₊ = j ∨ ⌊(W : ℝ) * τ a'⌋₊ = j) →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            birthKCorrAt b E s h τ m W (j + 1) y a a') y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-- **Gram cross entries**: the Gram part of `ComplexBirthCross`. -/
def ComplexBirthCrossGram : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ →
    ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
        IsNewCoord τ W j (Sum.inl e : CIdx K np) → ¬ IsNewDiag τ W j (Sum.inl e : CIdx K np) →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            gramEntry e (b3ClosedGramAt b E s h τ m W (j + 1) (Vs W) y)) y‖ₑ
          ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-- **Closed `𝒦` cross entries**: the `𝒦` part of `ComplexBirthCross`. -/
def ComplexBirthCrossK : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ → ∀ a a' : Fin np,
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
        IsNewCoord τ W j (Sum.inr (a, a') : CIdx K np) →
        ¬ IsNewDiag τ W j (Sum.inr (a, a') : CIdx K np) →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            b3ClosedKAt b E s h τ m W (j + 1) y a a') y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-!
## The reductions
-/

theorem Birth.ofReal_half_add_half {θ : ℝ} (hθ : 0 < θ) :
    ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) = ENNReal.ofReal θ := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- **The closed fresh `𝒦` diagonal** from the unclosed one and the closing correction. -/
theorem complexBirthKDiag_of_parts (hF : ComplexBirthKFresh) (hC : ComplexBirthKClosing) :
    ComplexBirthKDiag := by
  intro b E np τ m T s h K Vs hD R θ hθ i
  have hCSL := hD.1
  have hs := hD.2.1
  have hsτ := hD.2.2.1
  filter_upwards [hF b E np τ m T s hCSL hs hsτ (θ / 2) (by positivity) i,
    hC b E np τ m T s h K Vs hD R (θ / 2) (by positivity) i i] with W hFW hCW
  intro j hj1 hj2 hi
  refine (Birth.lintegral_closedK_le R (Vs W) (j + 1) i i _).trans ?_
  rw [← Birth.ofReal_half_add_half hθ]
  exact add_le_add (hFW j hj1 hj2 hi) (hCW j hj1 hj2 (Or.inl hi))

/-- **The closed `𝒦` cross entries** from the unclosed ones and the closing correction. -/
theorem complexBirthCrossK_of_parts (hF : ComplexBirthKFreshCross) (hC : ComplexBirthKClosing) :
    ComplexBirthCrossK := by
  intro b E np τ m T s h K Vs hD R θ hθ a a'
  have hCSL := hD.1
  have hs := hD.2.1
  have hsτ := hD.2.2.1
  by_cases haa : a = a'
  · subst haa
    exact Eventually.of_forall fun W j _ _ hc hd => absurd (by
      rcases hc with hc | hc <;> exact ⟨a, hc, Or.inl rfl⟩) hd
  filter_upwards [hF b E np τ m T s hCSL hs hsτ (θ / 2) (by positivity) a a' haa,
    hC b E np τ m T s h K Vs hD R (θ / 2) (by positivity) a a'] with W hFW hCW
  intro j hj1 hj2 hc _
  have e := Birth.lintegral_closedK_le (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m)
    (j := j) R (Vs W) (j + 1) a a' 0
  simp only [sub_zero] at e
  refine e.trans ?_
  rw [← Birth.ofReal_half_add_half hθ]
  exact add_le_add (hFW j hj1 hj2 hc) (hCW j hj1 hj2 hc)

/-- **The cross estimate from its Gram and `𝒦` parts.** -/
theorem complexBirthCross_of_parts (hG : ComplexBirthCrossGram) (hK : ComplexBirthCrossK) :
    ComplexBirthCross := by
  intro b E np τ m T s h K Vs hD R θ hθ c
  rcases c with e | ⟨a, a'⟩
  · exact hG b E np τ m T s h K Vs hD R θ hθ e
  · exact hK b E np τ m T s h K Vs hD R θ hθ a a'

end BlockBand.SourceProcess.PhysApprox.B3
