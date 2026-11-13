module

public import BlockBand.SourceProcess.ClosedSumProof.ModAbstract
public import BlockBand.SourceProcess.ClosedSumProof.StepCond
public import BlockBand.SourceProcess.ClosedSumProof.ClosedModW

/-!
# The modulus of one real coordinate on one window (abstract)

The closed modulus estimates `closed_modulus_fixed`, `window_errs` and `closed_modulus_W` are
stated for the real Gram process (`closedGramAt`, `sampledPathLaw`). This file is their abstract
form, for any filtration `F`, events `A_j ∈ F_j`, complex increments `Δ_j` (`F_{j+1}`-measurable),
a conjugate partner `Δ'_j = Δ̄_j`, deterministic birth steps `bs` with jumps `B_j`, and
predictions `P_d, P_c` bounded on `A_j` by `C_b, C_c`:

**`window_modulus`**: if the summed drift, bracket (`ΔΔ'` against `s P_c`), birth and fourth-moment
errors over a step set containing the window are at most `ε ≤ 1`, then on `A_{j₁+L}` the
probability that the real coordinate `Re(u Z)` (`Z_{j+1} - Z_j = Δ_j - B_j`, `‖u‖ = 1`) moves by
more than `3λ + ℓ s C_b + κ + κ'` within `ℓ` steps is at most
`16 (s C_c)² (Nℓ) ℓ / λ⁴ + ε((64 + 8λ²)/λ⁴ + 1/κ + 1/κ')`.

Generic pieces used: `modulus_births` (with `modulus_tail`), `stepCond_drift`, `stepCond_var`,
`reMul`, `integrable_of_pow4`, `window_of_steps`, `modulus_arith`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Modul

open MeasureTheory Finset
open BlockBand.SourceProcess.ClosedSumProof
open scoped ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ## The window objects -/

/-- The real coordinate `Re(u Z)` along the window `[j₁, j₁ + L]`, held constant after `L`
steps. -/
def wX (Z : ℕ → Ω → ℂ) (u : ℂ) (j₁ L k : ℕ) (y : Ω) : ℝ := reMul u (Z (j₁ + min k L) y)

/-- The martingale-type step `1_{A_j} Re(uΔ_j)` at a step without birth, `j = j₁ + k`. -/
def wD (A : ℕ → Set Ω) (Δ : ℕ → Ω → ℂ) (bs : ℕ → Prop) [DecidablePred bs] (u : ℂ)
    (j₁ L k : ℕ) : Ω → ℝ :=
  if k < L ∧ ¬ bs (j₁ + k) then (A (j₁ + k)).indicator fun y => reMul u (Δ (j₁ + k) y) else 0

/-- The birth error `‖1_{A_j}(Δ_j - B_j)‖` at a birth step. -/
def wB (A : ℕ → Set Ω) (Δ : ℕ → Ω → ℂ) (Bj : ℕ → ℂ) (bs : ℕ → Prop) [DecidablePred bs]
    (j₁ L k : ℕ) : Ω → ℝ :=
  if k < L ∧ bs (j₁ + k) then fun y =>
    ‖(A (j₁ + k)).indicator (fun y => Δ (j₁ + k) y - Bj (j₁ + k)) y‖ else 0

/-- The drift error integrand at a step without birth. -/
def wG (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω) (A : ℕ → Set Ω) (Δ Pd : ℕ → Ω → ℂ)
    (bs : ℕ → Prop) [DecidablePred bs] (sc : ℝ) (j₁ L k : ℕ) : Ω → ℝ :=
  if k < L ∧ ¬ bs (j₁ + k) then fun y => ‖(A (j₁ + k)).indicator (fun y =>
    μ[(A (j₁ + k)).indicator (Δ (j₁ + k)) | F (j₁ + k)] y - (sc : ℂ) * Pd (j₁ + k) y) y‖ else 0

/-- The bracket error integrand (`ΔΔ'` against `s P_c`) at a step without birth. -/
def wF (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω) (A : ℕ → Set Ω) (Δ Δ' Pc : ℕ → Ω → ℂ)
    (bs : ℕ → Prop) [DecidablePred bs] (sc : ℝ) (j₁ L k : ℕ) : Ω → ℝ :=
  if k < L ∧ ¬ bs (j₁ + k) then fun y => ‖(A (j₁ + k)).indicator (fun y =>
    μ[(A (j₁ + k)).indicator (fun y => Δ (j₁ + k) y * Δ' (j₁ + k) y) | F (j₁ + k)] y -
      (sc : ℂ) * Pc (j₁ + k) y) y‖ else 0

/-- The fourth-moment integrand at a step without birth. -/
def w4 (A : ℕ → Set Ω) (Δ : ℕ → Ω → ℂ) (bs : ℕ → Prop) [DecidablePred bs] (j₁ L k : ℕ) :
    Ω → ℝ :=
  if k < L ∧ ¬ bs (j₁ + k) then fun y => ‖(A (j₁ + k)).indicator (Δ (j₁ + k)) y‖ ^ 4 else 0

/-! ## Auxiliary facts -/

theorem sum_lintegral_ite (μ : Measure Ω) (steps : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (V : ℕ → Ω → ℂ) :
    ∑ j ∈ steps, ∫⁻ y, ‖(if p j then V j else 0) y‖ₑ ∂μ =
      ∑ j ∈ steps.filter p, ∫⁻ y, ‖V j y‖ₑ ∂μ := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : p j <;> simp [hj]

theorem enorm_ofReal_norm_pow4 (z : ℂ) : ‖((‖z‖ ^ 4 : ℝ) : ℂ)‖ₑ = ‖z‖ₑ ^ 4 := by
  rw [← enorm_norm, Complex.norm_real, enorm_norm, enorm_pow, enorm_norm]

theorem indicator_enorm_pow4 (S : Set Ω) (f : Ω → ℂ) (y : Ω) :
    S.indicator (fun y => ‖f y‖ₑ ^ 4) y = ‖S.indicator f y‖ₑ ^ 4 := by
  by_cases hy : y ∈ S
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, enorm_zero]
    exact (zero_pow (by norm_num)).symm

theorem integrable_of_window {μ : Measure Ω} {L : ℕ} {φ : ℕ → Ω → ℝ}
    (h1 : ∀ k < L, Integrable (φ k) μ) (h2 : ∀ k, ¬ k < L → φ k = 0) (k : ℕ) :
    Integrable (φ k) μ := by
  by_cases hk : k < L
  · exact h1 k hk
  · rw [h2 k hk]; exact integrable_zero _ _ _

/-! ## The window bound -/

/-- **One real coordinate on one window** (abstract form of `closed_modulus_W`). -/
theorem window_modulus (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ i, F i ≤ m0) (hFm : Monotone F) (A : ℕ → Set Ω) (Δ Δ' Z : ℕ → Ω → ℂ)
    (Bj : ℕ → ℂ) (bs : ℕ → Prop) [DecidablePred bs] (Pd Pc : ℕ → Ω → ℂ) {sc Cb Cc : ℝ}
    (hsc : 0 ≤ sc) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) {j₁ L : ℕ} (steps : Finset ℕ)
    (hs : ∀ k < L, j₁ + k ∈ steps)
    (hA : ∀ k < L, MeasurableSet[F (j₁ + k)] (A (j₁ + k)))
    (hAL : ∀ k ≤ L, A (j₁ + L) ⊆ A (j₁ + k))
    (hΔ : ∀ k < L, StronglyMeasurable[F (j₁ + k + 1)] (Δ (j₁ + k)))
    (hstar : ∀ k < L, ∀ y, Δ' (j₁ + k) y = star (Δ (j₁ + k) y))
    (hZ : ∀ k < L, ∀ y, Z (j₁ + k + 1) y - Z (j₁ + k) y = Δ (j₁ + k) y - Bj (j₁ + k))
    (hB : ∀ j, ¬ bs j → Bj j = 0)
    (hPd : ∀ k < L, AEStronglyMeasurable (Pd (j₁ + k)) μ)
    (hPc : ∀ k < L, AEStronglyMeasurable (Pc (j₁ + k)) μ)
    (hPdb : ∀ k < L, ∀ y ∈ A (j₁ + k), ‖Pd (j₁ + k) y‖ ≤ Cb)
    (hPcb : ∀ k < L, ∀ y ∈ A (j₁ + k), ‖Pc (j₁ + k) y‖ ≤ Cc)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hEd : ∑ j ∈ steps.filter (fun j => ¬ bs j), ∫⁻ y, ‖(A j).indicator (fun y =>
      μ[(A j).indicator (Δ j) | F j] y - (sc : ℂ) * Pd j y) y‖ₑ ∂μ ≤ ENNReal.ofReal ε)
    (hEf : ∑ j ∈ steps.filter (fun j => ¬ bs j), ∫⁻ y, ‖(A j).indicator (fun y =>
      μ[(A j).indicator (fun y => Δ j y * Δ' j y) | F j] y - (sc : ℂ) * Pc j y) y‖ₑ ∂μ ≤
        ENNReal.ofReal ε)
    (hEb : ∑ j ∈ steps.filter (fun j => bs j), ∫⁻ y, ‖(A j).indicator (fun y =>
      Δ j y - Bj j) y‖ₑ ∂μ ≤ ENNReal.ofReal ε)
    (hE4 : ∑ j ∈ steps.filter (fun j => ¬ bs j), ∫⁻ y, (A j).indicator (fun y =>
      ‖Δ j y‖ₑ ^ 4) y ∂μ ≤ ENNReal.ofReal ε)
    (N ℓ : ℕ) (hℓ : 0 < ℓ) (hNL : L ≤ N * ℓ) {u : ℂ} (hu : ‖u‖ = 1) {lam κ κ' : ℝ}
    (hlam : 0 < lam) (hκ : 0 < κ) (hκ' : 0 < κ') :
    μ {y | y ∈ A (j₁ + L) ∧ ∃ x y', x ≤ y' ∧ y' ≤ N * ℓ ∧ y' ≤ x + ℓ ∧
        3 * lam + ℓ * (sc * Cb) + κ + κ' < |wX Z u j₁ L y' y - wX Z u j₁ L x y|} ≤
      ENNReal.ofReal (16 * (sc * Cc) ^ 2 * ((N : ℝ) * ℓ) * ℓ / lam ^ 4 +
        ε * ((64 + 8 * lam ^ 2) / lam ^ 4 + 1 / κ + 1 / κ')) := by
  have hAm : ∀ k < L, MeasurableSet (A (j₁ + k)) := fun k hk => hF _ _ (hA k hk)
  have hΔm : ∀ k < L, AEStronglyMeasurable ((A (j₁ + k)).indicator (Δ (j₁ + k))) μ :=
    fun k hk => (((hΔ k hk).mono (hF _)).indicator (hAm k hk)).aestronglyMeasurable
  -- the four window sums
  obtain ⟨i4, s4⟩ := window_of_steps (μ := μ) (fun j => if ¬ bs j then fun y =>
      ((‖(A j).indicator (Δ j) y‖ ^ 4 : ℝ) : ℂ) else 0) steps j₁ L N ℓ
    (fun i hi => by
      by_cases hb : bs (j₁ + i)
      · simp only [hb, not_true_eq_false, ite_false]; exact aestronglyMeasurable_const
      · simp only [hb, not_false_eq_true, ite_true]
        exact Complex.continuous_ofReal.comp_aestronglyMeasurable ((hΔm i hi).norm.pow 4))
    hs hNL (by
      rw [sum_lintegral_ite]
      refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => lintegral_congr fun y => ?_) hE4
      rw [enorm_ofReal_norm_pow4, indicator_enorm_pow4])
    (w4 A Δ bs j₁ L)
    (fun k hk => funext fun y => by
      by_cases hb : bs (j₁ + k)
      · simp [w4, hb]
      · simp only [w4, hk, hb, not_false_eq_true, and_self, ite_true, Complex.norm_real,
          Real.norm_eq_abs]
        exact (abs_of_nonneg (by positivity)).symm)
    (fun k hk => by simp [w4, hk])
  obtain ⟨ig, sg⟩ := window_of_steps (μ := μ) (fun j => if ¬ bs j then (A j).indicator (fun y =>
      μ[(A j).indicator (Δ j) | F j] y - (sc : ℂ) * Pd j y) else 0) steps j₁ L N ℓ
    (fun i hi => by
      by_cases hb : bs (j₁ + i)
      · simp only [hb, not_true_eq_false, ite_false]; exact aestronglyMeasurable_const
      · simp only [hb, not_false_eq_true, ite_true]
        exact ((stronglyMeasurable_condExp.mono (hF _)).aestronglyMeasurable.sub
          (aestronglyMeasurable_const.mul (hPd i hi))).indicator (hAm i hi))
    hs hNL (by rw [sum_lintegral_ite]; exact hEd) (wG μ F A Δ Pd bs sc j₁ L)
    (fun k hk => funext fun y => by
      by_cases hb : bs (j₁ + k)
      · simp [wG, hb]
      · simp [wG, hk, hb])
    (fun k hk => by simp [wG, hk])
  obtain ⟨if', sf⟩ := window_of_steps (μ := μ) (fun j => if ¬ bs j then (A j).indicator (fun y =>
      μ[(A j).indicator (fun y => Δ j y * Δ' j y) | F j] y - (sc : ℂ) * Pc j y) else 0)
    steps j₁ L N ℓ
    (fun i hi => by
      by_cases hb : bs (j₁ + i)
      · simp only [hb, not_true_eq_false, ite_false]; exact aestronglyMeasurable_const
      · simp only [hb, not_false_eq_true, ite_true]
        exact ((stronglyMeasurable_condExp.mono (hF _)).aestronglyMeasurable.sub
          (aestronglyMeasurable_const.mul (hPc i hi))).indicator (hAm i hi))
    hs hNL (by rw [sum_lintegral_ite]; exact hEf) (wF μ F A Δ Δ' Pc bs sc j₁ L)
    (fun k hk => funext fun y => by
      by_cases hb : bs (j₁ + k)
      · simp [wF, hb]
      · simp [wF, hk, hb])
    (fun k hk => by simp [wF, hk])
  obtain ⟨ib, sb⟩ := window_of_steps (μ := μ) (fun j => if bs j then (A j).indicator (fun y =>
      Δ j y - Bj j) else 0) steps j₁ L N ℓ
    (fun i hi => by
      by_cases hb : bs (j₁ + i)
      · simp only [hb, ite_true]
        exact (((hΔ i hi).mono (hF _)).aestronglyMeasurable.sub
          aestronglyMeasurable_const).indicator (hAm i hi)
      · simp only [hb, ite_false]; exact aestronglyMeasurable_const)
    hs hNL (by rw [sum_lintegral_ite]; exact hEb) (wB A Δ Bj bs j₁ L)
    (fun k hk => funext fun y => by
      by_cases hb : bs (j₁ + k)
      · simp [wB, hk, hb]
      · simp [wB, hb])
    (fun k hk => by simp [wB, hk])
  rw [max_eq_left hε0] at s4 sg sf sb
  -- fourth moments of the steps
  have h4 : ∀ k, (hk : k < L ∧ ¬ bs (j₁ + k)) →
      Integrable (fun y => ‖(A (j₁ + k)).indicator (Δ (j₁ + k)) y‖ ^ 4) μ := fun k hk => by
    have := i4 k hk.1
    rwa [w4, ite_eq_left hk] at this
  have hpow : ∀ k y, wD A Δ bs u j₁ L k y ^ 4 ≤ w4 A Δ bs j₁ L k y := fun k y => by
    by_cases hk : k < L ∧ ¬ bs (j₁ + k)
    · simp only [wD, w4, ite_eq_left hk]
      rw [indicator_reMul, ← Even.pow_abs (by decide)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_reMul_le hu _) 4
    · simp [wD, w4, hk]
  have hdm : ∀ k, StronglyMeasurable[F (j₁ + (k + 1))] (wD A Δ bs u j₁ L k) := fun k => by
    by_cases hk : k < L ∧ ¬ bs (j₁ + k)
    · rw [wD, ite_eq_left hk]
      exact ((reMul u).continuous.comp_stronglyMeasurable (hΔ k hk.1)).indicator
        (hFm (Nat.le_succ _) _ (hA k hk.1))
    · rw [wD, ite_eq_right hk]; exact stronglyMeasurable_const
  have hd4 : ∀ k, Integrable (fun y => wD A Δ bs u j₁ L k y ^ 4) μ := fun k => by
    refine Integrable.mono' (integrable_of_window i4 (fun k hk => by simp [w4, hk]) k)
      ((((hdm k).mono (hF _)).aestronglyMeasurable).pow 4)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (by decide) _)]
    exact hpow k y
  -- conditional drift and variance
  have hdrift : ∀ k < N * ℓ, ∀ᵐ y ∂μ, |μ[wD A Δ bs u j₁ L k | F (j₁ + k)] y| ≤
      sc * Cb + wG μ F A Δ Pd bs sc j₁ L k y := fun k _ => by
    by_cases hk : k < L ∧ ¬ bs (j₁ + k)
    · have hint := integrable_of_pow4 (hΔm k hk.1) (h4 k hk)
      have := stepCond_drift (μ := μ) (hA k hk.1) hu hint hsc hCb (hPdb k hk.1)
      rw [wD, ite_eq_left hk]
      filter_upwards [this] with y hy
      rw [wG, ite_eq_left hk]
      exact hy
    · rw [wD, ite_eq_right hk, condExp_zero]
      refine Filter.Eventually.of_forall fun y => ?_
      have : 0 ≤ wG μ F A Δ Pd bs sc j₁ L k y := by rw [wG, ite_eq_right hk]; simp
      simp only [Pi.zero_apply, abs_zero]
      positivity
  have hvar : ∀ k < N * ℓ, μ[fun y => wD A Δ bs u j₁ L k y ^ 2 | F (j₁ + k)] ≤ᵐ[μ]
      fun y => sc * Cc + wF μ F A Δ Δ' Pc bs sc j₁ L k y := fun k _ => by
    by_cases hk : k < L ∧ ¬ bs (j₁ + k)
    · have := stepCond_var (μ := μ) (hA k hk.1) hu (hstar k hk.1) (hΔm k hk.1) (h4 k hk) hsc hCc
        (hPcb k hk.1)
      have e : (fun y => wD A Δ bs u j₁ L k y ^ 2) = fun y => (A (j₁ + k)).indicator
          (fun y => reMul u (Δ (j₁ + k) y)) y ^ 2 := by
        funext y; rw [wD, ite_eq_left hk]
      rw [e]
      filter_upwards [this] with y hy
      rw [wF, ite_eq_left hk]
      exact hy
    · have e : (fun y => wD A Δ bs u j₁ L k y ^ 2) = 0 := by
        funext y; simp [wD, hk]
      rw [e, condExp_zero]
      refine Filter.Eventually.of_forall fun y => ?_
      have : 0 ≤ wF μ F A Δ Δ' Pc bs sc j₁ L k y := by rw [wF, ite_eq_right hk]; simp
      simp only [Pi.zero_apply]
      positivity
  -- one step of the coordinate
  have hstep : ∀ y ∈ A (j₁ + L), ∀ k < N * ℓ, |wX Z u j₁ L (k + 1) y - wX Z u j₁ L k y -
      wD A Δ bs u j₁ L k y| ≤ wB A Δ Bj bs j₁ L k y := fun y hy k _ => by
    by_cases hk : k < L
    · have hyk : y ∈ A (j₁ + k) := hAL k hk.le hy
      have hX : wX Z u j₁ L (k + 1) y - wX Z u j₁ L k y =
          reMul u (Δ (j₁ + k) y - Bj (j₁ + k)) := by
        have e1 : j₁ + min (k + 1) L = j₁ + k + 1 := by omega
        have e0 : j₁ + min k L = j₁ + k := by omega
        rw [wX, wX, e1, e0, ← map_sub, hZ k hk y]
      rw [hX]
      by_cases hb : bs (j₁ + k)
      · have hn : ¬ (k < L ∧ ¬ bs (j₁ + k)) := fun h => h.2 hb
        simp only [wD, wB, ite_eq_right hn, ite_eq_left (And.intro hk hb), Pi.zero_apply, sub_zero,
          Set.indicator_of_mem hyk]
        exact abs_reMul_le hu _
      · have hp : k < L ∧ ¬ bs (j₁ + k) := ⟨hk, hb⟩
        have hn : ¬ (k < L ∧ bs (j₁ + k)) := fun h => hb h.2
        simp only [wD, wB, ite_eq_left hp, ite_eq_right hn, Pi.zero_apply, Set.indicator_of_mem hyk,
          hB _ hb, sub_zero, sub_self, abs_zero, le_refl]
    · have hn1 : ¬ (k < L ∧ ¬ bs (j₁ + k)) := fun h => hk h.1
      have hn2 : ¬ (k < L ∧ bs (j₁ + k)) := fun h => hk h.1
      simp only [wX, wD, wB, ite_eq_right hn1, ite_eq_right hn2,
        min_eq_right (by omega : L ≤ k + 1),
        min_eq_right (not_lt.mp hk), Pi.zero_apply, sub_self, abs_zero, le_refl]
  -- nonnegativity
  have hf0 : ∀ k y, 0 ≤ wF μ F A Δ Δ' Pc bs sc j₁ L k y := fun k y => by
    unfold wF; split_ifs <;> simp
  have hg0 : ∀ k y, 0 ≤ wG μ F A Δ Pd bs sc j₁ L k y := fun k y => by
    unfold wG; split_ifs <;> simp
  have hb0 : ∀ k y, 0 ≤ wB A Δ Bj bs j₁ L k y := fun k y => by
    unfold wB; split_ifs <;> simp
  have hF0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, wF μ F A Δ Δ' Pc bs sc j₁ L i y ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => hf0 i y
  have hG0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, wG μ F A Δ Pd bs sc j₁ L i y ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => hg0 i y
  have hB0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, wB A Δ Bj bs j₁ L i y ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => hb0 i y
  have hD0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, wD A Δ bs u j₁ L i y ^ 4 ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => Even.pow_nonneg (by decide) _
  have hD : ∑ i ∈ range (N * ℓ), ∫ y, wD A Δ bs u j₁ L i y ^ 4 ∂μ ≤ ε :=
    le_trans (Finset.sum_le_sum fun i _ => integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => Even.pow_nonneg (by decide) _)
      (integrable_of_window i4 (fun k hk => by simp [w4, hk]) i)
      (Filter.Eventually.of_forall fun y => hpow i y)) s4
  have hmod := modulus_births (μ := μ) (fun i => F (j₁ + i)) (fun i => hF _)
    (fun i i' h => hFm (by omega)) N ℓ hℓ (wX Z u j₁ L) (A (j₁ + L)) (wD A Δ bs u j₁ L)
    (wF μ F A Δ Δ' Pc bs sc j₁ L) (wG μ F A Δ Pd bs sc j₁ L) (wB A Δ Bj bs j₁ L) (sc * Cc)
    (sc * Cb) lam κ κ' (mul_nonneg hsc hCc) (mul_nonneg hsc hCb) hlam hκ hκ' hdm
    (fun k _ => hd4 k) hf0
    (fun k _ => integrable_of_window if' (fun k hk => by simp [wF, hk]) k) hvar hg0
    (fun k _ => integrable_of_window ig (fun k hk => by simp [wG, hk]) k) hdrift hb0
    (fun k _ => integrable_of_window ib (fun k hk => by simp [wB, hk]) k) hstep
  refine hmod.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (modulus_arith hlam hκ hκ' hF0 sf hD sg sb hε1)

end BlockBand.SourceProcess.PhysApprox.B3.Modul
