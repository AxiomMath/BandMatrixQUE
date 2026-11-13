module

public import BlockBand.SourceProcess.PhysApprox.B3FourRaw
public import BlockBand.SourceProcess.PhysApprox.B3MomMax
public import BlockBand.SourceProcess.PhysApprox.B3GenStep
public import BlockBand.SourceProcess.PhysApprox.B3BirthReduce

/-!
# `KStopStepFour` and the Lindeberg clause, reduced to the correction step

The closed `𝒦` is the unclosed `𝒦` minus the closed resolvent correction (`b3ClosedKAt_eq`), so
the stopped step `Z_i` of the maximal moment bound is `1_{A_i}(Δ𝒦_i − Δcorr_i)`.
* **`KCorrStepFourAt`** (summed form `KCorrStepFour`), stated as a
  hypothesis: the stopped fourth moment of one step of the closed resolvent correction is
  `≤ C/W²`. It is the only missing piece: **`kStopStepFour_of_corr`** gives `KStopStepFour` from
  `KCorrStepFour` and the contract hypotheses, **`kCorrStepFour_of_stop`** the converse, and
  **`lintegral_kStopStep_at`** the per-step `E|Z_j|⁴ ≤ C/W²` at every step for the entries with no
  newborn tag.
* **`complexKLindeberg_of_stepFour`**: `KStopStepFour ⇒ ComplexKLindeberg`
  (`W·Σ ≤ C ⇒ Σ → 0`); the Gram rate form `GramStopStepFour` gives
  `ComplexGramLindeberg` (`complexGramLindeberg_of_stepFour`); it is proved from the frame estimate
  `ClosedFrameStepEight`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.RawTag
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

variable {W np K : ℕ}

/-!
## Entries of the unclosed `𝒦` as raw forms
-/

theorem complexSourceK_eq_rawForm (b E : ℝ) (n : ℕ) (τ m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j)
    (x : ProbedPath W np) (i j : Fin np) (hi : ⌊(W : ℝ) * τ i⌋₊ < n)
    (hj : ⌊(W : ℝ) * τ j⌋₊ < n) :
    complexSourceK b E W n τ m x i j = ((Real.sqrt (m i) * Real.sqrt (m j) : ℝ) : ℂ) *
      rawForm b E W n ⌊(W : ℝ) * τ i⌋₊ ⌊(W : ℝ) * τ j⌋₊ x.1 (x.2 i) (x.2 j) := by
  rw [complexSourceK_apply, probeColumn_eq_tagVector n τ m _ i hi,
    probeColumn_eq_tagVector n τ m _ j hj, tagForm, tagForm_eq_rawForm b E n _ _ (hm i) (hm j)]
  have e : ∀ β : ℕ, β < n → n - 1 - (n - 1 - β) = β := fun β hβ => by omega
  simp only [e _ hi, e _ hj]

/-- A tag not born at step `l` is old at both lengths or absent at both. -/
theorem old_or_absent {τ : Fin np → ℝ} {l : ℕ} {i : Fin np} (hne : ⌊(W : ℝ) * τ i⌋₊ ≠ l) :
    ⌊(W : ℝ) * τ i⌋₊ < l ∨ (¬ ⌊(W : ℝ) * τ i⌋₊ < l + 1 ∧ ¬ ⌊(W : ℝ) * τ i⌋₊ < l) := by
  omega

/-- At a step without a birth no coordinate is new. -/
theorem not_isNewCoord_of_not_birth {τ : Fin np → ℝ} {j : ℕ} (hl : ¬ IsBirthStep τ W j)
    (c : CIdx K np) : ¬ IsNewCoord τ W j c := by
  have hc : ∀ k : SrcCol K (Fin np), ¬ IsNewCol τ W j k := by
    intro k hk
    cases k with
    | inl _ => exact hk
    | inr i => exact hl ⟨i, hk⟩
  intro h
  cases c with
  | inl e =>
      rcases (h : IsNewCol τ W j e.2.1 ∨ IsNewCol τ W j e.2.2) with h | h
      exacts [hc _ h, hc _ h]
  | inr ij =>
      rcases (h : ⌊(W : ℝ) * τ ij.1⌋₊ = j ∨ ⌊(W : ℝ) * τ ij.2⌋₊ = j) with h | h
      exacts [hl ⟨_, h⟩, hl ⟨_, h⟩]

/-- **The unclosed `𝒦` step of an old entry** (at `p = 4`), at every step `l`
where neither tag of the entry is born (in particular at every step without a birth). -/
theorem lintegral_kUnclosedStep_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) {b E : ℝ} {τ m : Fin np → ℝ}
    {T : ℝ} (hD : ComplexSourceLawDomain b E τ m T) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ l : ℕ, ((l + 1 : ℕ) : ℝ) ≤ T * W →
      ∀ ij : Fin np × Fin np, ⌊(W : ℝ) * τ ij.1⌋₊ ≠ l → ⌊(W : ℝ) * τ ij.2⌋₊ ≠ l →
        ∫⁻ y, ‖complexSourceK b E W (l + 1) τ m y.1 ij.1 ij.2 -
            complexSourceK b E W l τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
  obtain ⟨hb0, hb1, hE0, hE1, -, -, hm, -⟩ := hD
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  obtain ⟨C₀, W₀, hC₀, hstep⟩ := Four.lintegral_stepIncr_le hGA hLp
    (BlockBand.Transmission.EnergyUniform.fullSourceMomentsEnergyUniform_holds hGA hLp hSR)
    (BlockBand.Transmission.LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp) hb0 hb1 hκ T
  set Mx := ∑ i, m i
  have hMx : ∀ i, m i ≤ Mx := fun i =>
    Finset.single_le_sum (f := m) (fun j _ => hm j) (Finset.mem_univ i)
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun j _ => hm j
  refine ⟨Mx ^ 4 * C₀, max W₀ 1, by positivity, fun W hW l hlT ij hl₁ hl₂ => ?_⟩
  have hW₀ : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hlT' : (l : ℝ) ≤ T * W := le_trans (by exact_mod_cast Nat.le_succ l) hlT
  have hmeas : Measurable fun x : ProbedPath W np =>
      ‖complexSourceK b E W (l + 1) τ m x ij.1 ij.2 -
        complexSourceK b E W l τ m x ij.1 ij.2‖ₑ ^ 4 :=
    (((measurable_complexSourceK b E W (l + 1) τ m).eval_matrix (i := ij.1) (j := ij.2)).sub
      ((measurable_complexSourceK b E W l τ m).eval_matrix (i := ij.1) (j := ij.2))).enorm.pow_const
      4
  rw [lintegral_closedLaw_fst b hmeas]
  rcases old_or_absent hl₁ with hi | ⟨hi1, hi0⟩
  swap
  · have h0 : ∀ x : ProbedPath W np, ‖complexSourceK b E W (l + 1) τ m x ij.1 ij.2 -
        complexSourceK b E W l τ m x ij.1 ij.2‖ₑ ^ 4 = 0 := fun x => by
      rw [complexSourceK_apply, complexSourceK_apply, probeColumn_eq_zero _ τ m _ _ hi1,
        probeColumn_eq_zero _ τ m _ _ hi0, tagForm_zero_left, tagForm_zero_left, sub_self,
        enorm_zero]
      norm_num
    simp only [h0, lintegral_zero]
    exact zero_le
  rcases old_or_absent hl₂ with hj | ⟨hj1, hj0⟩
  swap
  · have h0 : ∀ x : ProbedPath W np, ‖complexSourceK b E W (l + 1) τ m x ij.1 ij.2 -
        complexSourceK b E W l τ m x ij.1 ij.2‖ₑ ^ 4 = 0 := fun x => by
      rw [complexSourceK_apply, complexSourceK_apply, probeColumn_eq_zero _ τ m _ _ hj1,
        probeColumn_eq_zero _ τ m _ _ hj0, tagForm_zero_right, tagForm_zero_right, sub_self,
        enorm_zero]
      norm_num
    simp only [h0, lintegral_zero]
    exact zero_le
  -- both tags old: the raw update
  set β₁ := ⌊(W : ℝ) * τ ij.1⌋₊
  set β₂ := ⌊(W : ℝ) * τ ij.2⌋₊
  have hl1 : 1 ≤ l := by omega
  set c : ℂ := ((Real.sqrt (m ij.1) * Real.sqrt (m ij.2) : ℝ) : ℂ)
  have hupd := rawUpdate_holds b E hb0 hb1 hE0 hE1 W hW1
  set ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)
  have hae : ∀ᵐ x ∂probedPathLaw W np b, complexSourceK b E W (l + 1) τ m x ij.1 ij.2 -
      complexSourceK b E W l τ m x ij.1 ij.2 =
        c * bilinear (nearL b E W l β₁ x.1 (x.2 ij.1)) (stepDelta b E W l x.1)
          (nearR b E W l β₂ x.1 (x.2 ij.2)) := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b) (ν := ν)).ae hupd
    filter_upwards [h] with x hx
    rw [complexSourceK_eq_rawForm b E (l + 1) τ m hm x _ _ (by omega) (by omega),
      complexSourceK_eq_rawForm b E l τ m hm x _ _ hi hj, ← mul_sub,
      hx l hl1 β₁ β₂ hi hj (x.2 ij.1) (x.2 ij.2)]
    ring
  have hcm : ‖c‖ₑ ^ 4 ≤ ENNReal.ofReal (Mx ^ 4) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc : ‖c‖ = Real.sqrt (m ij.1) * Real.sqrt (m ij.2) := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    rw [hc, mul_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, Real.sq_sqrt (hm _),
      Real.sq_sqrt (hm _)]
    calc (m ij.1) ^ 2 * (m ij.2) ^ 2 ≤ Mx ^ 2 * Mx ^ 2 := by
          gcongr
          · exact hm _
          · exact hMx _
          · exact hm _
          · exact hMx _
      _ = Mx ^ (2 * 2) := by ring
  have hmapi : ν.map (fun g => g ij.1) = circularVectorLaw (Fin W) :=
    (measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) ij.1).map_eq
  have hmapj : ν.map (fun g => g ij.2) = circularVectorLaw (Fin W) :=
    (measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) ij.2).map_eq
  have hs := hstep W hW₀ E hEκ (Fin np → Fin W → ℂ) ν (fun g => g ij.1) (fun g => g ij.2)
    (measurable_pi_apply _) (measurable_pi_apply _) hmapi hmapj l β₁ β₂ hl1 hi hj hlT'
  calc ∫⁻ x, ‖complexSourceK b E W (l + 1) τ m x ij.1 ij.2 -
        complexSourceK b E W l τ m x ij.1 ij.2‖ₑ ^ 4 ∂probedPathLaw W np b
      = ∫⁻ x, ‖c‖ₑ ^ 4 * ‖bilinear (nearL b E W l β₁ x.1 (x.2 ij.1)) (stepDelta b E W l x.1)
          (nearR b E W l β₂ x.1 (x.2 ij.2))‖ₑ ^ 4 ∂probedPathLaw W np b := by
        refine lintegral_congr_ae (hae.mono fun x hx => ?_)
        dsimp only
        rw [hx, enorm_mul, mul_pow]
    _ = ‖c‖ₑ ^ 4 * ∫⁻ x, ‖bilinear (nearL b E W l β₁ x.1 (x.2 ij.1)) (stepDelta b E W l x.1)
          (nearR b E W l β₂ x.1 (x.2 ij.2))‖ₑ ^ 4 ∂probedPathLaw W np b :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)
    _ ≤ ENNReal.ofReal (Mx ^ 4) * ENNReal.ofReal (C₀ / (W : ℝ) ^ 2) := by
        gcongr
        exact hs
    _ = ENNReal.ofReal (Mx ^ 4 * C₀ / (W : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_div_assoc]

/-!
## The correction step and the reduction
-/

/-- The stopped step `1_{A_i}(corr_{i+1} − corr_i)` of the entry `ij` of the closed resolvent
correction `b3KCorrAt`. -/
def kCorrStep (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (y : ProbedPath W np × ℝ) : ℂ :=
  (b3Alive b E s h τ m R W i Vs).indicator (fun y =>
    b3KCorrAt b E s h τ m W (i + 1) y ij.1 ij.2 - b3KCorrAt b E s h τ m W i y ij.1 ij.2) y

/-- **`KCorrStepFourAt`** (controlled by the
`δ₀` jets of the closed boundary): at every step `n_s ≤ j < ⌊WT⌋` and for every entry with no
tag born at `j` (all entries at a step without a birth, the old entries at a birth step), the
stopped fourth moment of one step of the closed resolvent correction is `≤ C/W²`, uniformly. -/
def KCorrStepFourAt : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∀ ij : Fin np × Fin np,
        ¬ IsNewCoord τ W j (Sum.inr ij : CIdx K np) →
          ∫⁻ y, ‖kCorrStep b E s h τ m R W j (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
            ENNReal.ofReal (C / (W : ℝ) ^ 2)

/-- **`KCorrStepFour`**: the summed (rate) form of `KCorrStepFourAt`, exactly the piece
of `KStopStepFour` carried by the correction (`kStopStepFour_of_corr`, `kCorrStepFour_of_stop`). -/
def KCorrStepFour : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ((W : ℕ) : ℝ≥0∞) * ∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun i => ¬ IsBirthStep τ W i),
        ∫⁻ y, ‖kCorrStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal C

/-- The pointwise split of the stopped closed step: `|Z|⁴ ≤ 8(|Δ𝒦|⁴ + |corr step|⁴)` and
`|corr step|⁴ ≤ 8(|Δ𝒦|⁴ + |Z|⁴)`. -/
theorem enorm_kStopStep_le (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (y : ProbedPath W np × ℝ) :
    ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ≤
        8 * (‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 -
          complexSourceK b E W i τ m y.1 ij.1 ij.2‖ₑ ^ 4 +
          ‖kCorrStep b E s h τ m R W i Vs ij y‖ₑ ^ 4) ∧
      ‖kCorrStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ≤
        8 * (‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 -
          complexSourceK b E W i τ m y.1 ij.1 ij.2‖ₑ ^ 4 +
          ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ ^ 4) := by
  unfold kStopStep kCorrStep
  by_cases hy : y ∈ b3Alive b E s h τ m R W i Vs
  · simp only [Set.indicator_of_mem hy, b3ClosedKAt_eq, Matrix.sub_apply]
    set u := complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 -
      complexSourceK b E W i τ m y.1 ij.1 ij.2
    set v := b3KCorrAt b E s h τ m W (i + 1) y ij.1 ij.2 - b3KCorrAt b E s h τ m W i y ij.1 ij.2
    have e1 : complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 -
        b3KCorrAt b E s h τ m W (i + 1) y ij.1 ij.2 -
        (complexSourceK b E W i τ m y.1 ij.1 ij.2 - b3KCorrAt b E s h τ m W i y ij.1 ij.2) =
        u - v := by simp only [u, v]; ring
    have e2 : v = u - (u - v) := by ring
    rw [e1]
    refine ⟨(pow_le_pow_left₀ zero_le (enorm_sub_le) 4).trans (add_pow_four_le _ _), ?_⟩
    calc ‖v‖ₑ ^ 4 = ‖u - (u - v)‖ₑ ^ 4 := by rw [← e2]
      _ ≤ _ := (pow_le_pow_left₀ zero_le (enorm_sub_le) 4).trans (add_pow_four_le _ _)
  · simp only [Set.indicator_of_notMem hy, enorm_zero]
    norm_num

/-- The summation arithmetic: `W·Σ_S f ≤ 8(C₁ max T 0 + max C₂ 0)` when `|S| ≤ ⌊WT⌋`,
`f ≤ 8(C₁/W² + g)` on `S` and `W·Σ_S g ≤ C₂`. -/
theorem rate_sum_le {S : Finset ℕ} {T C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hW : 1 ≤ W)
    (hS : S.card ≤ ⌊(W : ℝ) * T⌋₊) (f g : ℕ → ℝ≥0∞)
    (hfg : ∀ i ∈ S, f i ≤ 8 * (ENNReal.ofReal (C₁ / (W : ℝ) ^ 2) + g i))
    (hg : (W : ℝ≥0∞) * ∑ i ∈ S, g i ≤ ENNReal.ofReal C₂) :
    (W : ℝ≥0∞) * ∑ i ∈ S, f i ≤ ENNReal.ofReal (8 * (C₁ * max T 0 + max C₂ 0)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hcard : (S.card : ℝ) ≤ W * max T 0 :=
    le_trans (by exact_mod_cast hS) (gen_floor_mul_le T W)
  have h1 : (W : ℝ≥0∞) * ∑ i ∈ S, ENNReal.ofReal (C₁ / (W : ℝ) ^ 2) ≤
      ENNReal.ofReal (C₁ * max T 0) := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Nat.cast_mul, show (W : ℝ) * S.card * (C₁ / (W : ℝ) ^ 2) = S.card * C₁ / W by
      field_simp]
    rw [div_le_iff₀ hW0]
    nlinarith
  calc (W : ℝ≥0∞) * ∑ i ∈ S, f i
      ≤ (W : ℝ≥0∞) * ∑ i ∈ S, 8 * (ENNReal.ofReal (C₁ / (W : ℝ) ^ 2) + g i) := by
        gcongr with i hi; exact hfg i hi
    _ = 8 * ((W : ℝ≥0∞) * ∑ i ∈ S, ENNReal.ofReal (C₁ / (W : ℝ) ^ 2) +
          (W : ℝ≥0∞) * ∑ i ∈ S, g i) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]; ring
    _ ≤ 8 * (ENNReal.ofReal (C₁ * max T 0) + ENNReal.ofReal (max C₂ 0)) := by
        gcongr
        exact hg.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (8 * (C₁ * max T 0 + max C₂ 0)) := by
        rw [← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
          ENNReal.ofReal_mul (by norm_num)]
        norm_num

theorem card_filter_Ico_le (s T : ℝ) (τ : Fin np → ℝ) (W : ℕ) :
    ((Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun i => ¬ IsBirthStep τ W i)).card ≤
      ⌊(W : ℝ) * T⌋₊ :=
  (Finset.card_filter_le _ _).trans ((Nat.card_Ico _ _).le.trans (Nat.sub_le _ _))

/-- The per-step estimate gives its summed form. -/
theorem kCorrStepFour_of_at (hA : KCorrStepFourAt) : KCorrStepFour := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, hC⟩ := hA b E np τ m T s h K Vs hF R
  refine ⟨8 * (max C 0 * max T 0 + max 0 0), ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with W hW hW1 ij
  refine rate_sum_le (le_max_right _ _) hW1 (card_filter_Ico_le s T τ W) _ (fun _ => 0)
    (fun i hi => ?_) (by simp)
  rw [add_zero]
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  exact (hW i hi1 ij (not_isNewCoord_of_not_birth hi2 _)).trans ((ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))).trans
    (le_mul_of_one_le_left' (by norm_num)))

theorem measurable_kUnclosedStep (b E : ℝ) (τ m : Fin np → ℝ) (W i : ℕ) (ij : Fin np × Fin np) :
    Measurable fun y : ProbedPath W np × ℝ =>
      ‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 -
        complexSourceK b E W i τ m y.1 ij.1 ij.2‖ₑ ^ 4 :=
  ((((measurable_complexSourceK b E W (i + 1) τ m).eval_matrix (i := ij.1) (j := ij.2)).sub
    ((measurable_complexSourceK b E W i τ m).eval_matrix (i := ij.1) (j := ij.2))).enorm.pow_const
    4).comp measurable_fst

/-- The integrated split of `enorm_kStopStep_le`. -/
theorem lintegral_kStopStep_le (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np) :
    ∫⁻ y, ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
        8 * (∫⁻ y, ‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 -
          complexSourceK b E W i τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np +
          ∫⁻ y, ‖kCorrStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ∂closedLaw b W np) ∧
      ∫⁻ y, ‖kCorrStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
        8 * (∫⁻ y, ‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 -
          complexSourceK b E W i τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np +
          ∫⁻ y, ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ∂closedLaw b W np) := by
  have hU := measurable_kUnclosedStep b E τ m W i ij
  constructor
  · refine (lintegral_mono fun y => (enorm_kStopStep_le b E s h τ m R W i Vs ij y).1).trans
      (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hU]
  · refine (lintegral_mono fun y => (enorm_kStopStep_le b E s h τ m R W i Vs ij y).2).trans
      (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hU]

/-- **`KStopStepFour` from the correction hypothesis `KCorrStepFour` and the input hypotheses.** -/
theorem kStopStepFour_of_corr (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFour) :
    KStopStepFour := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, W₁, hC₁, hU⟩ := lintegral_kUnclosedStep_le hGA hLp hSR hMT hF.1
  obtain ⟨C₂, h₂⟩ := hC b E np τ m T s h K Vs hF R
  refine ⟨8 * (C₁ * max T 0 + max C₂ 0), ?_⟩
  filter_upwards [h₂, eventually_ge_atTop (max W₁ 1)] with W hW2 hW ij
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  refine rate_sum_le hC₁ hW1 (card_filter_Ico_le s T τ W)
    (fun i => ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np)
    (fun i => ∫⁻ y, ‖kCorrStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np)
    (fun i hi => ?_) (hW2 ij)
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  refine (lintegral_kStopStep_le b E s h τ m R W i (Vs W) ij).1.trans ?_
  gcongr
  exact hU W hW₁ i (succ_le_mul_of_lt_floor (Finset.mem_Ico.1 hi1).2) ij (fun h => hi2 ⟨_, h⟩)
    (fun h => hi2 ⟨_, h⟩)

/-- **The converse**: given the contract hypotheses, `KStopStepFour` implies `KCorrStepFour`; so the
correction estimate carries the whole content of `KStopStepFour` beyond the input hypotheses. -/
theorem kCorrStepFour_of_stop (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hK : KStopStepFour) :
    KCorrStepFour := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, W₁, hC₁, hU⟩ := lintegral_kUnclosedStep_le hGA hLp hSR hMT hF.1
  obtain ⟨C₂, h₂⟩ := hK b E np τ m T s h K Vs hF R
  refine ⟨8 * (C₁ * max T 0 + max C₂ 0), ?_⟩
  filter_upwards [h₂, eventually_ge_atTop (max W₁ 1)] with W hW2 hW ij
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  refine rate_sum_le hC₁ hW1 (card_filter_Ico_le s T τ W)
    (fun i => ∫⁻ y, ‖kCorrStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np)
    (fun i => ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np)
    (fun i hi => ?_) (hW2 ij)
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  refine (lintegral_kStopStep_le b E s h τ m R W i (Vs W) ij).2.trans ?_
  gcongr
  exact hU W hW₁ i (succ_le_mul_of_lt_floor (Finset.mem_Ico.1 hi1).2) ij (fun h => hi2 ⟨_, h⟩)
    (fun h => hi2 ⟨_, h⟩)

/-- `KStopStepFour` from the per-step correction estimate and the contract hypotheses. -/
theorem kStopStepFour_of_corrAt (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFourAt) :
    KStopStepFour :=
  kStopStepFour_of_corr hGA hLp hSR hMT (kCorrStepFour_of_at hC)

/-- **The per-step fourth moment of the stopped closed `𝒦` step** at every step
`n_s ≤ j < ⌊WT⌋` and every entry with no tag born at `j`: `E|Z_j|⁴ ≤ C/W²`. -/
theorem lintegral_kStopStep_at (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFourAt) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, ∀ ij : Fin np × Fin np,
          ¬ IsNewCoord τ W j (Sum.inr ij : CIdx K np) →
            ∫⁻ y, ‖kStopStep b E s h τ m R W j (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
              ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, W₁, hC₁, hU⟩ := lintegral_kUnclosedStep_le hGA hLp hSR hMT hF.1
  obtain ⟨C₂, h₂⟩ := hC b E np τ m T s h K Vs hF R
  refine ⟨8 * (C₁ + max C₂ 0), by positivity, ?_⟩
  filter_upwards [h₂, eventually_ge_atTop W₁] with W hW2 hW j hj ij hnew
  have hn₁ : ⌊(W : ℝ) * τ ij.1⌋₊ ≠ j := fun h' =>
    hnew (show IsNewCoord τ W j (Sum.inr ij : CIdx K np) from Or.inl h')
  have hn₂ : ⌊(W : ℝ) * τ ij.2⌋₊ ≠ j := fun h' =>
    hnew (show IsNewCoord τ W j (Sum.inr ij : CIdx K np) from Or.inr h')
  refine (lintegral_kStopStep_le b E s h τ m R W j (Vs W) ij).1.trans ?_
  calc 8 * (∫⁻ y, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2 -
          complexSourceK b E W j τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂closedLaw b W np +
        ∫⁻ y, ‖kCorrStep b E s h τ m R W j (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np)
      ≤ 8 * (ENNReal.ofReal (C₁ / (W : ℝ) ^ 2) + ENNReal.ofReal (max C₂ 0 / (W : ℝ) ^ 2)) := by
        gcongr
        · exact hU W hW j (succ_le_mul_of_lt_floor (Finset.mem_Ico.1 hj).2) ij hn₁ hn₂
        · exact (hW2 j hj ij hnew).trans (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
    _ = ENNReal.ofReal (8 * (C₁ + max C₂ 0) / (W : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div,
          show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          mul_div_assoc]

/-!
## The Lindeberg clause from the rate forms
-/

/-- `W·S_W ≤ C` eventually gives `S_W → 0`. -/
theorem tendsto_zero_of_rate {S : ℕ → ℝ≥0∞} {C : ℝ}
    (h : ∀ᶠ W : ℕ in atTop, (W : ℝ≥0∞) * S W ≤ ENNReal.ofReal C) : Tendsto S atTop (𝓝 0) := by
  have hle : ∀ᶠ W in atTop, S W ≤ ENNReal.ofReal C * (W : ℝ≥0∞)⁻¹ := by
    filter_upwards [h, eventually_ge_atTop 1] with W hW hW1
    have hW0 : (W : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
    calc S W = (W : ℝ≥0∞)⁻¹ * ((W : ℝ≥0∞) * S W) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hW0 (ENNReal.natCast_ne_top W), one_mul]
      _ ≤ (W : ℝ≥0∞)⁻¹ * ENNReal.ofReal C := by gcongr
      _ = _ := mul_comm _ _
  have hlim : Tendsto (fun W : ℕ => ENNReal.ofReal C * (W : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.ofReal_ne_top (r := C)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) hle

theorem indicator_enorm_pow_four {α : Type*} (S : Set α) (f : α → ℂ) (y : α) :
    S.indicator (fun y => ‖f y‖ₑ ^ 4) y = ‖S.indicator f y‖ₑ ^ 4 := by
  by_cases hy : y ∈ S
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, enorm_zero]
    norm_num

/-- The `𝒦` Lindeberg error is the sum of the stopped fourth moments of `B3MomMax`. -/
theorem b3LindebergErr_inr (b E s T h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np) :
    b3LindebergErr b E s T h τ m R W Vs (Sum.inr ij : CIdx K np) =
      ∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun i => ¬ IsBirthStep τ W i),
        ∫⁻ y, ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ ^ 4 ∂closedLaw b W np := by
  refine Finset.sum_congr rfl fun i _ => lintegral_congr fun y => ?_
  rw [indicator_enorm_pow_four]
  rfl

/-- **`ComplexKLindeberg` from `KStopStepFour`.** -/
theorem complexKLindeberg_of_stepFour (hK : KStopStepFour) : ComplexKLindeberg := by
  intro b E np τ m T s h K Vs hD R ij
  obtain ⟨C, hC⟩ := hK b E np τ m T s h K Vs hD R
  refine tendsto_zero_of_rate (C := C) (hC.mono fun W hW => ?_)
  rw [b3LindebergErr_inr]
  exact hW ij

/-- **`ComplexKLindeberg` from the correction hypothesis `KCorrStepFour` and the input
hypotheses.** -/
theorem complexKLindeberg_of_corr (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) (hC : KCorrStepFour) :
    ComplexKLindeberg :=
  complexKLindeberg_of_stepFour (kStopStepFour_of_corr hGA hLp hSR hMT hC)

/-- **`GramStopStepFour`** (the rate
`E Σ_j |ΔZ_j|⁴ ≤ C_K W⁻¹` away from births, for the closed Gram coordinates; complex copy of the
rate in `ClosedFourth`): `W` times the summed stopped fourth moments of the Gram steps at
the steps without a birth is bounded. Rate form of the Gram rows of `ComplexClosedFourth`. -/
def GramStopStepFour : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
        ((W : ℕ) : ℝ≥0∞) * b3LindebergErr b E s T h τ m R W (Vs W) (Sum.inl e : CIdx K np) ≤
          ENNReal.ofReal C

/-- **`ComplexGramLindeberg` from `GramStopStepFour`.** -/
theorem complexGramLindeberg_of_stepFour (hG : GramStopStepFour) : ComplexGramLindeberg := by
  intro b E np τ m T s h K Vs hD R e
  obtain ⟨C, hC⟩ := hG b E np τ m T s h K Vs hD R
  exact tendsto_zero_of_rate (C := C) (hC.mono fun W hW => hW e)

/-- **`ComplexClosedLindeberg` from `KCorrStepFour`, `GramStopStepFour` and the input
hypotheses.** -/
theorem complexClosedLindeberg_of_pins (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hC : KCorrStepFour) (hG : GramStopStepFour) : ComplexClosedLindeberg :=
  complexClosedLindeberg_of_parts (complexGramLindeberg_of_stepFour hG)
    (complexKLindeberg_of_corr hGA hLp hSR hMT hC)

end BlockBand.SourceProcess.PhysApprox.B3
