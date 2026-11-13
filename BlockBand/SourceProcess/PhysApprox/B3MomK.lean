module

public import BlockBand.SourceProcess.PhysApprox.B3Pins2
public import BlockBand.SourceProcess.ComplexSourceLaw.KcMoments
public import BlockBand.SourceProcess.RawTag.Holds

/-!
# The stop for `𝒦` reduced to the closed resolvent correction

The closed `𝒦` at length `j` is `𝒦_j − corr_j` (`b3ClosedKAt_eq`), where
`corr_j = 2iηz V_jᴴ(1 − zN_j)⁻¹Π𝕊_jV_j` is the closed resolvent correction (`b3KCorrAt`).

* **`lintegral_kUnclosed_le`** (from `RawTagMoments`): the unclosed entries have uniform fourth
  moments, `E|(𝒦_n)_{ij}|⁴ ≤ C` for all `n ≤ TW`, `W ≥ W₀`, under `closedLaw`. No stop is needed.
  This is `lintegral_kc_le` with `p = 4` and the phase integrated out.
* **`ComplexKCorrMoment`** (a hypothesis): the same stopped fourth moment for the correction.
* **`complexKStoppedMoment_of_corr`**: `RawTagMoments + ComplexKCorrMoment ⇒
  ComplexKStoppedMoment` (Minkowski, `(a + b)⁴ ≤ 8(a⁴ + b⁴)`); `complexKStoppedMoment_of_baseContracts`
  with `RawTag.rawTagMoments_holds`. The converse `complexKCorrMoment_of_stopped` also holds, so
  the hypothesis is equivalent to `ComplexKStoppedMoment` given the raw moments.
* **`complexKStoppedMomentMax_of_corr`**: `KUnclosedMax + ComplexKCorrMomentMax ⇒
  ComplexKStoppedMomentMax`. Note that `RawTagMoments` does **not** give `KUnclosedMax` (it bounds
  each fixed length, not the supremum over the `~W(T − s)` lengths); that is a separate
  hypothesis.
* the alternative argument through the steps of the closed process is
  `complexKStoppedMomentMax_of_parts`.

Given `RawTagMoments`, the per-length `ComplexKStoppedMoment` is equivalent to `ComplexKCorrMoment`.
The latter is a hypothesis here; it follows from `ClosedTraceFour` and `RawTagMoments`
(`complexKCorrMoment_of_closedTrace`). It is controlled through the time-`s` representation, not
through the operator `(1 − zN_j)⁻¹` above: the final-time far amplitude has fourth phase moment
`(2 − t)/t`, while in the time-`s` canonical basis each closed omitted pair contributes the bounded
near-reflector correction `tz/(1 − √(1 − t)z)`, of modulus `≤ 2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

variable {W np : ℕ}

/-!
## The closed resolvent correction
-/

/-- **The closed resolvent correction at length `j`**: `2iηz V_jᴴ(1 − zN_j)⁻¹Π𝕊_jV_j`, with
`N_j = Π𝕊_jA`, `A, Π` the time-`s` omitted projection and pairing, `z = e^{iθ}`. -/
def b3KCorrAt (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin np) (Fin np) ℂ :=
  ((2 * etaZ b E : ℝ) * Complex.I * phase y.2) •
    ((probeFrame b E W j τ m y.1)ᴴ *
      (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1)))⁻¹ *
      farEmbed (closingPairing b E h W (closeLen s W) y.1.1) *
      scatteringMatrix b E W j y.1.1 * probeFrame b E W j τ m y.1)

/-- The closed `𝒦` is the unclosed `𝒦` minus the closed resolvent correction. -/
theorem b3ClosedKAt_eq (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W j y = complexSourceK b E W j τ m y.1 - b3KCorrAt b E s h τ m W j y :=
  rfl

/-!
## Unclosed fourth moments (no stop)
-/

theorem enorm_pow_four_eq (z : ℂ) : ‖z‖ₑ ^ 4 = ENNReal.ofReal (‖z‖ ^ (4 : ℝ)) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem add_pow_four_le (a c : ℝ≥0∞) : (a + c) ^ 4 ≤ 8 * (a ^ 4 + c ^ 4) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a c (p := 4) (by norm_num)
  have e : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ (4 : ℕ) := fun x => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [e, e, e, show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast] at h
  calc (a + c) ^ 4 ≤ 2 ^ 3 * (a ^ 4 + c ^ 4) := h
    _ = 8 * (a ^ 4 + c ^ 4) := by norm_num

/-- Integrating out the phase. -/
theorem lintegral_closedLaw_fst (b : ℝ) {f : ProbedPath W np → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y.1 ∂closedLaw b W np = ∫⁻ x, f x ∂probedPathLaw W np b := by
  rw [closedLaw, lintegral_prod (fun y : ProbedPath W np × ℝ => f y.1)
    (hf.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]

theorem measurable_enorm_complexSourceK_pow (b E : ℝ) (n : ℕ) (τ m : Fin np → ℝ) (i k : Fin np) :
    Measurable fun x : ProbedPath W np => ‖complexSourceK b E W n τ m x i k‖ₑ ^ 4 :=
  ((measurable_complexSourceK b E W n τ m).eval_matrix (i := i) (j := k)).enorm.pow_const 4

/-- **Uniform fourth moments of the unclosed `𝒦`** (at `p = 4`, `lintegral_kc_le`): on the domain,
eventually in `W`, every entry at every length `n ≤ TW` has `E|𝒦_{ij}|⁴ ≤ C` under `closedLaw`. -/
theorem lintegral_kUnclosed_le (hR : RawTagMoments) {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ}
    {T : ℝ} (hD : ComplexSourceLawDomain b E τ m T) : ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ n : ℕ, (n : ℝ) ≤ T * W → ∀ ij : Fin np × Fin np,
        ∫⁻ y, ‖complexSourceK b E W n τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal C := by
  obtain ⟨hb0, hb1, hE0, hE1, -, -, hm, -⟩ := hD
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨C, W₀, hC⟩ := hR b hb0 hb1 κ hκ T 4 (by norm_num)
  refine ⟨∑ i : Fin np, ∑ k : Fin np, |C * (m i * m k) ^ ((4 : ℝ) / 2)|, W₀,
    fun W hW n hn ij => ?_⟩
  rw [lintegral_closedLaw_fst b (measurable_enorm_complexSourceK_pow b E n τ m ij.1 ij.2)]
  simp_rw [enorm_pow_four_eq]
  refine (lintegral_kc_le b E n τ m hm (by norm_num) (hC W hW E hEκ n hn) ij.1 ij.2).trans
    (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_))
  have h1 := Finset.single_le_sum (f := fun k => |C * (m ij.1 * m k) ^ ((4 : ℝ) / 2)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ ij.2)
  have h2 := Finset.single_le_sum
    (f := fun i => ∑ k : Fin np, |C * (m i * m k) ^ ((4 : ℝ) / 2)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ ij.1)
  exact h1.trans h2

/-- The unclosed fourth moments from the input hypotheses (`RawTag.rawTagMoments_holds`). -/
theorem lintegral_kUnclosed_le_of_baseContracts (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T : ℝ} (hD : ComplexSourceLawDomain b E τ m T) :
    ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ n : ℕ, (n : ℝ) ≤ T * W → ∀ ij : Fin np × Fin np,
        ∫⁻ y, ‖complexSourceK b E W n τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal C :=
  lintegral_kUnclosed_le (RawTag.rawTagMoments_holds hGA hLp hSR hMT) hD

/-!
## The correction part of `ComplexKStoppedMoment` and the reduction
-/

/-- **`ComplexKCorrMoment`: the stopped fourth moment of the closed resolvent correction**. Same
quantifiers, alive set and lengths as `ComplexKStoppedMoment`, for `b3KCorrAt` in place of
`b3ClosedKAt`. It is a hypothesis of the results below. It is controlled through the time-`s`
representation (closed omitted pairs are unitary near reflectors with correction
`tz/(1 − √(1 − t)z)` of modulus `≤ 2`), not through `(1 − zN_j)⁻¹` (whose far amplitude has fourth
phase moment `(2 − t)/t`). -/
def ComplexKCorrMoment : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ∀ ij : Fin np × Fin np,
        ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y
            ∂closedLaw b W np ≤ ENNReal.ofReal C

theorem succ_le_mul_of_lt_floor {W j : ℕ} {T : ℝ} (hj : j < ⌊(W : ℝ) * T⌋₊) :
    ((j + 1 : ℕ) : ℝ) ≤ T * W := by
  have hpos : 0 < ⌊(W : ℝ) * T⌋₊ := Nat.zero_lt_of_lt hj
  have h1 : (1 : ℝ) ≤ (W : ℝ) * T := Nat.floor_pos.1 hpos
  have h2 : ((j + 1 : ℕ) : ℝ) ≤ (⌊(W : ℝ) * T⌋₊ : ℝ) := by exact_mod_cast hj
  rw [mul_comm]
  exact h2.trans (Nat.floor_le (by linarith))

/-- Pointwise Minkowski for the stopped integrand. -/
theorem indicator_closedK_le (S : Set (ProbedPath W np × ℝ)) (b E s h : ℝ) (τ m : Fin np → ℝ)
    (n : ℕ) (i k : Fin np) (y : ProbedPath W np × ℝ) :
    S.indicator (fun y => ‖b3ClosedKAt b E s h τ m W n y i k‖ₑ ^ 4) y ≤
      8 * S.indicator (fun y => ‖b3KCorrAt b E s h τ m W n y i k‖ₑ ^ 4) y +
        8 * ‖complexSourceK b E W n τ m y.1 i k‖ₑ ^ 4 := by
  by_cases hy : y ∈ S
  · simp only [Set.indicator_of_mem hy, b3ClosedKAt_eq, Matrix.sub_apply]
    calc ‖complexSourceK b E W n τ m y.1 i k - b3KCorrAt b E s h τ m W n y i k‖ₑ ^ 4
        ≤ (‖complexSourceK b E W n τ m y.1 i k‖ₑ + ‖b3KCorrAt b E s h τ m W n y i k‖ₑ) ^ 4 :=
          pow_le_pow_left₀ zero_le enorm_sub_le 4
      _ ≤ 8 * (‖complexSourceK b E W n τ m y.1 i k‖ₑ ^ 4 +
            ‖b3KCorrAt b E s h τ m W n y i k‖ₑ ^ 4) := add_pow_four_le _ _
      _ = _ := by ring
  · simp only [Set.indicator_of_notMem hy]
    exact zero_le

/-- **`ComplexKStoppedMoment` from the correction estimate** (Minkowski):
`RawTagMoments + ComplexKCorrMoment ⇒ ComplexKStoppedMoment`. -/
theorem complexKStoppedMoment_of_corr (hR : RawTagMoments) (hC : ComplexKCorrMoment) :
    ComplexKStoppedMoment := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, hC₁⟩ := hC b E np τ m T s h K Vs hF R
  obtain ⟨C₀, W₀, hC₀⟩ := lintegral_kUnclosed_le hR hF.1
  refine ⟨8 * max C₁ 0 + 8 * max C₀ 0, ?_⟩
  filter_upwards [hC₁, eventually_ge_atTop W₀] with W hW1 hW0 j hj1 hj2 ij
  have hn := succ_le_mul_of_lt_floor hj2
  refine (lintegral_mono fun y => indicator_closedK_le _ b E s h τ m (j + 1) ij.1 ij.2 y).trans ?_
  have hg : Measurable fun y : ProbedPath W np × ℝ =>
      8 * ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 :=
    ((measurable_enorm_complexSourceK_pow b E (j + 1) τ m ij.1 ij.2).comp
      measurable_fst).const_mul _
  rw [lintegral_add_right _ hg, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]
  have e1 := (hW1 j hj1 hj2 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₁ 0))
  have e0 := (hC₀ W hW0 (j + 1) hn ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0))
  calc 8 * ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y ∂closedLaw b W np +
        8 * ∫⁻ y, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np
      ≤ 8 * ENNReal.ofReal (max C₁ 0) + 8 * ENNReal.ofReal (max C₀ 0) := by gcongr
    _ = ENNReal.ofReal (8 * max C₁ 0 + 8 * max C₀ 0) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- Pointwise Minkowski the other way: the correction is `𝒦 − 𝒦_cl`. -/
theorem indicator_kCorr_le (S : Set (ProbedPath W np × ℝ)) (b E s h : ℝ) (τ m : Fin np → ℝ)
    (n : ℕ) (i k : Fin np) (y : ProbedPath W np × ℝ) :
    S.indicator (fun y => ‖b3KCorrAt b E s h τ m W n y i k‖ₑ ^ 4) y ≤
      8 * S.indicator (fun y => ‖b3ClosedKAt b E s h τ m W n y i k‖ₑ ^ 4) y +
        8 * ‖complexSourceK b E W n τ m y.1 i k‖ₑ ^ 4 := by
  by_cases hy : y ∈ S
  · have e : b3KCorrAt b E s h τ m W n y i k =
        complexSourceK b E W n τ m y.1 i k - b3ClosedKAt b E s h τ m W n y i k := by
      rw [b3ClosedKAt_eq, Matrix.sub_apply, sub_sub_cancel]
    simp only [Set.indicator_of_mem hy, e]
    calc ‖complexSourceK b E W n τ m y.1 i k - b3ClosedKAt b E s h τ m W n y i k‖ₑ ^ 4
        ≤ (‖complexSourceK b E W n τ m y.1 i k‖ₑ + ‖b3ClosedKAt b E s h τ m W n y i k‖ₑ) ^ 4 :=
          pow_le_pow_left₀ zero_le enorm_sub_le 4
      _ ≤ 8 * (‖complexSourceK b E W n τ m y.1 i k‖ₑ ^ 4 +
            ‖b3ClosedKAt b E s h τ m W n y i k‖ₑ ^ 4) := add_pow_four_le _ _
      _ = _ := by ring
  · simp only [Set.indicator_of_notMem hy]
    exact zero_le

/-- **The converse**: `RawTagMoments + ComplexKStoppedMoment ⇒ ComplexKCorrMoment`. With
`complexKStoppedMoment_of_corr`, the estimate `ComplexKCorrMoment` is equivalent to
`ComplexKStoppedMoment` given the raw moments: the reduction loses nothing. -/
theorem complexKCorrMoment_of_stopped (hR : RawTagMoments) (hK : ComplexKStoppedMoment) :
    ComplexKCorrMoment := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, hC₁⟩ := hK b E np τ m T s h K Vs hF R
  obtain ⟨C₀, W₀, hC₀⟩ := lintegral_kUnclosed_le hR hF.1
  refine ⟨8 * max C₁ 0 + 8 * max C₀ 0, ?_⟩
  filter_upwards [hC₁, eventually_ge_atTop W₀] with W hW1 hW0 j hj1 hj2 ij
  have hn := succ_le_mul_of_lt_floor hj2
  refine (lintegral_mono fun y => indicator_kCorr_le _ b E s h τ m (j + 1) ij.1 ij.2 y).trans ?_
  have hg : Measurable fun y : ProbedPath W np × ℝ =>
      8 * ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 :=
    ((measurable_enorm_complexSourceK_pow b E (j + 1) τ m ij.1 ij.2).comp
      measurable_fst).const_mul _
  rw [lintegral_add_right _ hg, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]
  have e1 := (hW1 j hj1 hj2 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₁ 0))
  have e0 := (hC₀ W hW0 (j + 1) hn ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0))
  calc 8 * ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y ∂closedLaw b W np +
        8 * ∫⁻ y, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np
      ≤ 8 * ENNReal.ofReal (max C₁ 0) + 8 * ENNReal.ofReal (max C₀ 0) := by gcongr
    _ = ENNReal.ofReal (8 * max C₁ 0 + 8 * max C₀ 0) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **`ComplexKStoppedMoment` from the correction hypothesis `ComplexKCorrMoment` and the input
hypotheses.** -/
theorem complexKStoppedMoment_of_baseContracts (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : ComplexKCorrMoment) : ComplexKStoppedMoment :=
  complexKStoppedMoment_of_corr (RawTag.rawTagMoments_holds hGA hLp hSR hMT) hC

/-!
## The maximal form
-/

/-- **`ComplexKCorrMomentMax`**: the maximal stopped fourth moment of the closed resolvent
correction, `E ⨆_{n_s ≤ j < ⌊WT⌋} 1_{A_j}|corr_{j+1}|⁴ ≤ C` (the body of
`ComplexKStoppedMomentMax` with `b3KCorrAt` in place of `b3ClosedKAt`). -/
def ComplexKCorrMomentMax : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ∫⁻ y, ⨆ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          (b3Alive b E s h τ m R W j (Vs W)).indicator
            (fun y => ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y
        ∂closedLaw b W np ≤ ENNReal.ofReal C

/-- **`KUnclosedMax`: the maximal fourth moment of the unclosed `𝒦`** along the path,
`E ⨆_{n_s ≤ j < ⌊WT⌋} |(𝒦_{j+1})_{ij}|⁴ ≤ C` (no stop). `RawTagMoments` gives this at each fixed
length only (`lintegral_kUnclosed_le`), **not** for the supremum; the supremum needs Doob and
Burkholder along the raw-form recursion (`RawTag.step_bound`). -/
def KUnclosedMax : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T → ∀ s : ℝ,
    ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ∫⁻ y, ⨆ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np ≤
        ENNReal.ofReal C

/-- **The maximal `ComplexKStoppedMoment` from the maximal correction estimate and the maximal
unclosed moment** (Minkowski under the supremum). -/
theorem complexKStoppedMomentMax_of_corr (hU : KUnclosedMax) (hC : ComplexKCorrMomentMax) :
    ComplexKStoppedMomentMax := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, hC₁⟩ := hC b E np τ m T s h K Vs hF R
  obtain ⟨C₀, hC₀⟩ := hU b E np τ m T hF.1 s
  refine ⟨8 * max C₁ 0 + 8 * max C₀ 0, ?_⟩
  filter_upwards [hC₁, hC₀] with W hW1 hW0 ij
  set S := Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊
  have hpt : ∀ y, (⨆ j ∈ S, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) ≤
      8 * (⨆ j ∈ S, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) +
      8 * ⨆ j ∈ S, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 := by
    intro y
    refine iSup₂_le fun j hj => (indicator_closedK_le _ b E s h τ m (j + 1) ij.1 ij.2 y).trans ?_
    gcongr
    · exact le_iSup₂ (f := fun j (_ : j ∈ S) => (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) j hj
    · exact le_iSup₂ (f := fun j (_ : j ∈ S) =>
        ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4) j hj
  have hg : Measurable fun y : ProbedPath W np × ℝ =>
      8 * ⨆ j ∈ S, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 :=
    (Measurable.iSup fun j => Measurable.iSup fun _ =>
      (measurable_enorm_complexSourceK_pow b E (j + 1) τ m ij.1 ij.2).comp
        measurable_fst).const_mul _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_right _ hg, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]
  have e1 := (hW1 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₁ 0))
  have e0 := (hW0 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0))
  calc _ ≤ 8 * ENNReal.ofReal (max C₁ 0) + 8 * ENNReal.ofReal (max C₀ 0) := by gcongr
    _ = ENNReal.ofReal (8 * max C₁ 0 + 8 * max C₀ 0) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num

end BlockBand.SourceProcess.PhysApprox.B3
