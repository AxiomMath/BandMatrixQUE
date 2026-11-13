module

public import BlockBand.SourceProcess.ClosedSumProof.ClosedStep

/-!
# Conditional drift and variance of the closed steps

`gErr`, `fErr`: the drift and bracket integrands of `ClosedSummed` (Borel cap `aliveM`, bracket
with `(e, swapE e)`). For an admissible frame and `n_s ≤ j₁`:
* `stronglyMeasurable_dInc`: `d_k` is `closedSigma (j₁+k+1)`-measurable;
* **`dInc_drift`**: `|E[d_k | closedSigma (j₁+k)]| ≤ W⁻¹C_b(R) + g_k` a.e.;
* **`dInc_var`**: `E[d_k² | closedSigma (j₁+k)] ≤ W⁻¹C_c(R) + f_k` a.e.;
given the fourth moment of the step (from `ClosedFourth`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum

variable {W p K M : ℕ}

/-- The law of `ClosedSummed` at width `W`. -/
abbrev lawW (b T : ℝ) (q : Fin p → ℝ → ℝ) (M W : ℕ) : Measure (SampledPath W p M × ℝ) :=
  (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw

section Window

variable (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
  (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M))

/-- The drift integrand of `ClosedSummed` at step `j₁ + k` (Borel cap). -/
def gErr (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) : ℝ :=
  if k < L then ‖(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
    (lawW b T q M W)[(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) |
        closedSigma W (j₁ + k) p M] y - (((W : ℝ)⁻¹ : ℝ) : ℂ) *
      gramDriftEntry (transportD0 b E) (srcSignature K (Fin p × Fin M)) e
        (closedGramAt b E s T h q W (j₁ + k) Vs y)) y‖ else 0

/-- The bracket integrand of `ClosedSummed` with `(e, swapE e)` at step `j₁ + k`. -/
def fErr (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) : ℝ :=
  if k < L then ‖(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
    (lawW b T q M W)[(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
      (zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) *
        (zc b E s T h q W Vs (swapE e) (j₁ + k + 1) y -
          zc b E s T h q W Vs (swapE e) (j₁ + k) y)) | closedSigma W (j₁ + k) p M] y -
      (((W : ℝ)⁻¹ : ℝ) : ℂ) * gramCovEntry (transportD0 b E) (srcSignature K (Fin p × Fin M)) e
        (swapE e) (closedGramAt b E s T h q W (j₁ + k) Vs y)) y‖ else 0

theorem gErr_nonneg (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) :
    0 ≤ gErr b E s T h q R W Vs e j₁ L k y := by unfold gErr; split_ifs <;> simp

theorem fErr_nonneg (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) :
    0 ≤ fErr b E s T h q R W Vs e j₁ L k y := by unfold fErr; split_ifs <;> simp

variable {b E s T h q R W Vs}

theorem l1_closedGram_le {j : ℕ} (hj : closeLen s W ≤ j) {y : SampledPath W p M × ℝ}
    (hy : y ∈ aliveM b E s T h q R W j Vs) :
    l1 (closedGramAt b E s T h q W j Vs y).1 ≤ rhoR K p M R ∧
      l1 (closedGramAt b E s T h q W j Vs y).2 ≤ rhoR K p M R := by
  have htr := hy.2 j hj le_rfl
  have hent : ∀ e', ‖gramEntry e' (closedGramAt b E s T h q W j Vs y)‖ ≤ max R 0 := fun e' =>
    (norm_gramEntry_le (closedFrameAt b E s T h q W j Vs y) (fun z => if z.1 = 0 then 1 else 0)
      (norm_nearPortProj_entry_le W) e').trans (htr.le.trans (le_max_left _ _))
  exact ⟨l1_le_of_entry fun a c => by simpa [gramEntry] using hent (0, a, c),
    l1_le_of_entry fun a c => by simpa [gramEntry] using hent (1, a, c)⟩

theorem measurableSet_am (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j : ℕ}
    (hj : closeLen s W ≤ j) : MeasurableSet[closedSigma W j p M] (am b E s T h q R W Vs j) :=
  (measurableSet_aliveM b E s T h q R hj hVs).inter (measurableSet_noBirth j)

theorem measurable_zc (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j : ℕ}
    (hj : closeLen s W ≤ j) : Measurable[closedSigma W j p M] (zc b E s T h q W Vs e j) :=
  (measurable_gramEntry e).comp (measurable_closedGramAt_past b E s T h q hj hVs)

theorem stronglyMeasurable_step (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j : ℕ}
    (hj : closeLen s W ≤ j) :
    StronglyMeasurable[closedSigma W (j + 1) p M] ((am b E s T h q R W Vs j).indicator fun y =>
      zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) := by
  have h1 := measurable_zc (b := b) (E := E) (T := T) (h := h) (q := q) (M := M) e hVs
    (by omega : closeLen s W ≤ j + 1)
  have h0 := (measurable_zc (b := b) (E := E) (T := T) (h := h) (q := q) (M := M) e hVs hj).mono (closedSigma_mono (Nat.le_succ j)) le_rfl
  exact ((h1.sub h0).stronglyMeasurable).indicator
    (closedSigma_mono (Nat.le_succ j) _ (measurableSet_am (b := b) (E := E) (T := T) (h := h)
      (q := q) (R := R) hVs hj))

theorem stronglyMeasurable_dInc (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j₁ : ℕ}
    (hj₁ : closeLen s W ≤ j₁) (u : ℂ) (L k : ℕ) :
    StronglyMeasurable[closedSigma W (j₁ + (k + 1)) p M] (dInc b E s T h q R W Vs e u j₁ L k) := by
  unfold dInc
  split_ifs
  · have := stronglyMeasurable_step (b := b) (E := E) (T := T) (h := h) (q := q) (R := R) e hVs
      (by omega : closeLen s W ≤ j₁ + k)
    have e2 := indicator_reMul u (am b E s T h q R W Vs (j₁ + k)) (fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y)
    have e3 : (fun y => (am b E s T h q R W Vs (j₁ + k)).indicator (fun y => reMul u
        (zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y)) y) =
        (am b E s T h q R W Vs (j₁ + k)).indicator (fun y => reMul u
        (zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y)) := rfl
    rw [e3, e2, ← add_assoc]
    exact (reMul u).continuous.comp_stronglyMeasurable this
  · exact stronglyMeasurable_const

theorem aestronglyMeasurable_step (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j : ℕ}
    (hj : closeLen s W ≤ j) (μ : Measure (SampledPath W p M × ℝ)) :
    AEStronglyMeasurable ((am b E s T h q R W Vs j).indicator fun y =>
      zc b E s T h q W Vs e (j + 1) y - zc b E s T h q W Vs e j y) μ :=
  ((stronglyMeasurable_step e hVs hj).mono (closedSigma_le (j + 1))).aestronglyMeasurable

theorem norm_drift_le {j : ℕ} (hj : closeLen s W ≤ j) :
    ∀ y ∈ am b E s T h q R W Vs j, ‖gramDriftEntry (transportD0 b E)
      (srcSignature K (Fin p × Fin M)) e (closedGramAt b E s T h q W j Vs y)‖ ≤
        driftC b E K p M R := fun _y hy =>
  norm_gramDriftEntry_le_rho _ _ e _ (l1_closedGram_le hj hy.1).1 (l1_closedGram_le hj hy.1).2

theorem norm_cov_le {j : ℕ} (hj : closeLen s W ≤ j) :
    ∀ y ∈ am b E s T h q R W Vs j, ‖gramCovEntry (transportD0 b E)
      (srcSignature K (Fin p × Fin M)) e (swapE e) (closedGramAt b E s T h q W j Vs y)‖ ≤
        covC b E K p M R := fun _y hy =>
  norm_gramCovEntry_le_rho _ _ e _ _ (l1_closedGram_le hj hy.1).1 (l1_closedGram_le hj hy.1).2

/-- **The conditional drift of a closed step.** -/
theorem dInc_drift (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j₁ : ℕ}
    (hj₁ : closeLen s W ≤ j₁) {u : ℂ} (hu : ‖u‖ = 1) (L k : ℕ)
    (hΔ : k < L → Integrable ((am b E s T h q R W Vs (j₁ + k)).indicator fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) (lawW b T q M W)) :
    ∀ᵐ y ∂lawW b T q M W, |(lawW b T q M W)[dInc b E s T h q R W Vs e u j₁ L k |
      closedSigma W (j₁ + k) p M] y| ≤ (W : ℝ)⁻¹ * driftC b E K p M R +
        gErr b E s T h q R W Vs e j₁ L k y := by
  by_cases hk : k < L
  · have hd : dInc b E s T h q R W Vs e u j₁ L k = (am b E s T h q R W Vs (j₁ + k)).indicator
        (fun y => reMul u (zc b E s T h q W Vs e (j₁ + k + 1) y -
          zc b E s T h q W Vs e (j₁ + k) y)) := by
      funext y; simp only [dInc, ite_eq_left hk]
    rw [hd]
    have := stepCond_drift (μ := lawW b T q M W) (measurableSet_am hVs (by omega)) hu (hΔ hk)
      (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹) (driftC_nonneg b E K p M R)
      (norm_drift_le e (by omega : closeLen s W ≤ j₁ + k))
    simpa only [gErr, ite_eq_left hk] using this
  · have hd : dInc b E s T h q R W Vs e u j₁ L k = 0 := by
      funext y; simp only [dInc, ite_eq_right hk, Pi.zero_apply]
    rw [hd, condExp_zero]
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [Pi.zero_apply, abs_zero]
    exact add_nonneg (mul_nonneg (by positivity) (driftC_nonneg b E K p M R))
      (gErr_nonneg b E s T h q R W Vs e j₁ L k y)

/-- **The conditional variance of a closed step.** -/
theorem dInc_var [IsFiniteMeasure (lawW b T q M W)]
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j₁ : ℕ}
    (hj₁ : closeLen s W ≤ j₁) {u : ℂ} (hu : ‖u‖ = 1) (L k : ℕ)
    (h4 : k < L → Integrable (fun y => ‖(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) y‖ ^ 4)
        (lawW b T q M W)) :
    (lawW b T q M W)[fun y => dInc b E s T h q R W Vs e u j₁ L k y ^ 2 |
      closedSigma W (j₁ + k) p M] ≤ᵐ[lawW b T q M W] fun y => (W : ℝ)⁻¹ * covC b E K p M R +
        fErr b E s T h q R W Vs e j₁ L k y := by
  by_cases hk : k < L
  · have hd : (fun y => dInc b E s T h q R W Vs e u j₁ L k y ^ 2) = fun y =>
        (am b E s T h q R W Vs (j₁ + k)).indicator (fun y => reMul u
          (zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y)) y ^ 2 := by
      funext y; simp only [dInc, ite_eq_left hk]
    rw [hd]
    have hstar : ∀ y, zc b E s T h q W Vs (swapE e) (j₁ + k + 1) y -
        zc b E s T h q W Vs (swapE e) (j₁ + k) y = star (zc b E s T h q W Vs e (j₁ + k + 1) y -
          zc b E s T h q W Vs e (j₁ + k) y) := fun y => by
      simp only [zc, closedGramAt, star_sub,
        star_gramEntry _ (nearPortProj_conjTranspose (W := W))]
    have := stepCond_var (μ := lawW b T q M W) (measurableSet_am hVs (by omega)) hu hstar
      (aestronglyMeasurable_step e hVs (by omega) _) (h4 hk)
      (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹) (covC_nonneg b E K p M R)
      (norm_cov_le e (by omega : closeLen s W ≤ j₁ + k))
    filter_upwards [this] with y hy
    simpa only [fErr, ite_eq_left hk] using hy
  · have hd : (fun y => dInc b E s T h q R W Vs e u j₁ L k y ^ 2) = 0 := by
      funext y; simp [dInc, ite_eq_right hk]
    rw [hd, condExp_zero]
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [Pi.zero_apply]
    exact add_nonneg (mul_nonneg (by positivity) (covC_nonneg b E K p M R))
      (fErr_nonneg b E s T h q R W Vs e j₁ L k y)

end Window

end BlockBand.SourceProcess.ClosedSumProof
