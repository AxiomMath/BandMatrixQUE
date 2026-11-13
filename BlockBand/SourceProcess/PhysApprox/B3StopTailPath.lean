module

public import BlockBand.SourceProcess.PhysApprox.B3MomTight
public import BlockBand.SourceProcess.PhysApprox.B3BirthReduce
public import BlockBand.SourceProcess.PhysApprox.B3Assembly2
public import BlockBand.SourceProcess.ClosedSumProof.GramBound
public import BlockBand.SourceProcess.CutoffLimit.InitFrame

/-!
# The stop tail of the closed complex path: the pathwise part

The first two steps of the full-source stop estimate, for the closed complex path, including the
tag births; the target is `ComplexClosedStopTail`.

The objects are those of `ComplexClosedSummed`: the closed law `closedLaw b W np`, the closed
Gram process `b3ClosedGramAt`, the alive set `b3Alive` (cap event, trace stop), the steps
`n_s ≤ j < ⌊WT⌋`. With `dg x = (0, x, x)` (diagonal `M`-coordinates):
* `b3Tr` (`Re Tr M_j`), `b3Tr_nonneg`; `indicator_trStep`: the stopped trace step is
  `Re Σ_x 1_{A_j} ΔX_{dg x}`;
* **`stopped_sum`** (abstract, pathwise optional stopping): for `x ≥ 0`, the stopped sum
  `x n + Σ_{n ≤ j < N} 1_{a_j}(x_{j+1} - x_j)` is `≥ 0`, and `≥ R` on the stop event (the same
  statement as `StopTail.stopped_sum`);
* `cDrift_dg`: the drift coefficient of a diagonal `M`-coordinate is `0`;
* **`sum_norm_birth_le`**: the deterministic tag births add at most
  `birthC = Σ_i |d_* m_i|` to the trace over any set of steps;
* **`trace_initialGram_le`** (`Re Tr M₀ ≤ 4K` when `t ≤ 1`) and **`ae_b3Tr_start_le`**: for an
  admissible frame, a.s. `Re Tr M_{n_s} ≤ 4K` (as in `ae_b3ClosedGramAt_start_adm`).
  The probes are born after `n_s`, so no start event is needed (unlike the real case).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.StopTail

open MeasureTheory Filter Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum
open scoped ENNReal

variable {W np K : ℕ}

/-! ## The closed trace and its steps -/

/-- The closed trace `Re Tr M_j`. -/
def b3Tr (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) : ℝ :=
  ((b3ClosedGramAt b E s h τ m W j Vs y).1.trace).re

theorem b3Tr_nonneg (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) : 0 ≤ b3Tr b E s h τ m W j Vs y := by
  unfold b3Tr b3ClosedGramAt gramPair
  rw [ClosedSumProof.re_trace_sourceGram]
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- The diagonal `M`-coordinate of column `x`. -/
def dg {c : Type*} (x : c) : Fin 2 × c × c := (0, x, x)

/-- The stopped step of the diagonal `M`-coordinate `dg x`: `1_{A_j} ΔX_{dg x}`. -/
def stepX (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : SrcCol K (Fin np))
    (j : ℕ) : ProbedPath W np × ℝ → ℂ :=
  (b3Alive b E s h τ m R W j Vs).indicator
    (b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np))

theorem b3dX_dg (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np) y =
      (b3ClosedGramAt b E s h τ m W (j + 1) Vs y).1 x x -
        (b3ClosedGramAt b E s h τ m W j Vs y).1 x x := by
  simp [b3dX, b3X, cEntry, gramEntry, dg]

/-- **The stopped trace step** is `Re Σ_x 1_{A_j} ΔX_{dg x}`. -/
theorem indicator_trStep (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) :
    (b3Alive b E s h τ m R W j Vs).indicator
        (fun y => b3Tr b E s h τ m W (j + 1) Vs y - b3Tr b E s h τ m W j Vs y) y =
      (∑ x, stepX b E s h τ m R W Vs x j y).re := by
  by_cases hy : y ∈ b3Alive b E s h τ m R W j Vs
  · simp only [Set.indicator_of_mem hy, stepX, b3dX_dg, b3Tr, Matrix.trace, Matrix.diag,
      Complex.re_sum, Complex.sub_re, sum_sub_distrib]
  · simp [Set.indicator_of_notMem hy, stepX]

/-! ## Pathwise optional stopping -/

/-- The invariant of the stopped sum at length `N`. -/
theorem stopped_sum_inv (x : ℕ → ℝ) (c : Prop) (R : ℝ) (n : ℕ) (a : ℕ → Prop)
    [DecidablePred a] (ha : ∀ j, a j ↔ c ∧ ∀ i, n ≤ i → i ≤ j → x i < R) (N : ℕ)
    (hN : n ≤ N) :
    (a N ∧ x n + ∑ j ∈ Ico n N, (if a j then x (j + 1) - x j else 0) = x N) ∨
      ∃ k, n ≤ k ∧ k ≤ N ∧ x n + ∑ j ∈ Ico n N, (if a j then x (j + 1) - x j else 0) = x k ∧
        (¬c ∨ R ≤ x k) := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Ico_self, sum_empty, add_zero]
    by_cases h : a n
    · exact Or.inl ⟨h, rfl⟩
    · refine Or.inr ⟨n, le_rfl, le_rfl, rfl, ?_⟩
      by_cases hc : c
      · refine Or.inr (not_lt.1 fun hlt => h ((ha n).2 ⟨hc, fun i h1 h2 => ?_⟩))
        rwa [le_antisymm h2 h1]
      · exact Or.inl hc
  | succ N hnN ih =>
    rw [sum_Ico_succ_top hnN, ← add_assoc]
    rcases ih with ⟨haN, hF⟩ | ⟨k, hk1, hk2, hF, hk⟩
    · rw [ite_eq_left haN, hF, add_sub_cancel]
      by_cases h : a (N + 1)
      · exact Or.inl ⟨h, rfl⟩
      · refine Or.inr ⟨N + 1, by omega, le_rfl, rfl, Or.inr ?_⟩
        obtain ⟨hc, hlt⟩ := (ha N).1 haN
        refine not_lt.1 fun hR => h ((ha (N + 1)).2 ⟨hc, fun i h1 h2 => ?_⟩)
        rcases Nat.lt_or_ge i (N + 1) with hi | hi
        · exact hlt i h1 (by omega)
        · rwa [le_antisymm h2 hi]
    · have hna : ¬a N := fun haN => by
        obtain ⟨hc, hlt⟩ := (ha N).1 haN
        rcases hk with hk | hk
        · exact hk hc
        · exact absurd (hlt k hk1 hk2) (not_lt.2 hk)
      rw [ite_eq_right hna, add_zero, hF]
      exact Or.inr ⟨k, hk1, by omega, rfl, hk⟩

/-- **The stopped sum**: nonnegative, and at least `R` on the stop event. -/
theorem stopped_sum (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (c : Prop) (R : ℝ) (n N : ℕ)
    (hnN : n ≤ N) (a : ℕ → Prop) [DecidablePred a]
    (ha : ∀ j, a j ↔ c ∧ ∀ i, n ≤ i → i ≤ j → x i < R) :
    0 ≤ x n + ∑ j ∈ Ico n N, (if a j then x (j + 1) - x j else 0) ∧
      (c → (∃ i, n ≤ i ∧ i ≤ N ∧ R ≤ x i) →
        R ≤ x n + ∑ j ∈ Ico n N, (if a j then x (j + 1) - x j else 0)) := by
  rcases stopped_sum_inv x c R n a ha N hnN with ⟨haN, hF⟩ | ⟨k, -, -, hF, hk⟩
  · refine ⟨hF ▸ hx N, fun _ ⟨i, h1, h2, hi⟩ => ?_⟩
    exact absurd (((ha N).1 haN).2 i h1 h2) (not_lt.2 hi)
  · refine ⟨hF ▸ hx k, fun hc _ => ?_⟩
    rw [hF]
    rcases hk with hk | hk
    · exact absurd hc hk
    · exact hk

/-- **The stopped closed trace** `Y = Re Tr M_{n_s} + Σ_j Re Σ_x 1_{A_j}ΔX_{dg x}` is `≥ 0`
pathwise, and `≥ R` on the stop event of `ComplexClosedStopTail`. -/
theorem stopped_trace (b E s h : ℝ) (τ m : Fin np → ℝ) (R T : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (hnN : closeLen s W ≤ ⌊(W : ℝ) * T⌋₊) (y : ProbedPath W np × ℝ) :
    0 ≤ b3Tr b E s h τ m W (closeLen s W) Vs y + ∑ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        (∑ x, stepX b E s h τ m R W Vs x j y).re ∧
      ((y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i, closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * T⌋₊ ∧
          R ≤ ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re) →
        R ≤ b3Tr b E s h τ m W (closeLen s W) Vs y +
          ∑ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, (∑ x, stepX b E s h τ m R W Vs x j y).re) := by
  classical
  have e : ∑ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, (∑ x, stepX b E s h τ m R W Vs x j y).re =
      ∑ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, (if y ∈ b3Alive b E s h τ m R W j Vs then
        b3Tr b E s h τ m W (j + 1) Vs y - b3Tr b E s h τ m W j Vs y else 0) := by
    refine sum_congr rfl fun j _ => ?_
    rw [← indicator_trStep]
    by_cases hy : y ∈ b3Alive b E s h τ m R W j Vs
    · rw [Set.indicator_of_mem hy, ite_eq_left hy]
    · rw [Set.indicator_of_notMem hy, ite_eq_right hy]
  rw [e]
  have key := stopped_sum (fun i => b3Tr b E s h τ m W i Vs y)
    (fun i => b3Tr_nonneg b E s h τ m W i Vs y) (y.1.1 ∈ physCapEventC b E s h K W) R
    (closeLen s W) ⌊(W : ℝ) * T⌋₊ hnN (fun j => y ∈ b3Alive b E s h τ m R W j Vs)
    (fun j => Iff.rfl)
  exact ⟨key.1, fun hy => key.2 hy.1 hy.2⟩

/-! ## Drift and births of the diagonal `M`-coordinates -/

/-- The drift coefficient of a diagonal `M`-coordinate vanishes. -/
theorem cDrift_dg (b E : ℝ) (x : SrcCol K (Fin np)) (G : GramState (SrcCol K (Fin np))) :
    cDrift b E (Sum.inl (dg x) : CIdx K np) G = 0 := by
  simp [cDrift, gramDriftEntry, dg]

theorem cEntry_dg_birth (b E : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) (x : SrcCol K (Fin np)) :
    cEntry (Sum.inl (dg x) : CIdx K np) (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j) =
      (b3BirthAt b τ m W j).1 x x := by
  simp [cEntry, gramEntry, dg]

/-- The birth weight bound `birthC = Σ_i |d_* m_i|`. -/
def birthC (b : ℝ) (m : Fin np → ℝ) : ℝ := ∑ i, |dStar b * m i|

theorem birthC_nonneg (b : ℝ) (m : Fin np → ℝ) : 0 ≤ birthC b m :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem sum_norm_birthAt_le (b : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) :
    ∑ x : SrcCol K (Fin np), ‖(b3BirthAt b τ m W j).1 x x‖ ≤
      ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = j then |dStar b * m i| else 0 := by
  calc ∑ x : SrcCol K (Fin np), ‖(b3BirthAt b τ m W j).1 x x‖
      ≤ ∑ x : SrcCol K (Fin np), ∑ i,
          if ⌊(W : ℝ) * τ i⌋₊ = j then (if x = Sum.inr i then |dStar b * m i| else 0) else 0 := by
        refine sum_le_sum fun x _ => ?_
        rw [(Birth.b3BirthAt_apply (b := b) (τ := τ) (m := m) (W := W) (j := j) x x).2]
        refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
        by_cases hi : ⌊(W : ℝ) * τ i⌋₊ = j
        · by_cases hx : x = Sum.inr i
          · simp [hi, hx, Complex.norm_real]
          · simp [hi, hx]
        · simp [hi]
    _ = ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = j then |dStar b * m i| else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        by_cases hi : ⌊(W : ℝ) * τ i⌋₊ = j
        · simp [hi]
        · simp [hi]

/-- **The births add at most `birthC` over any set of steps.** -/
theorem sum_norm_birth_le (b : ℝ) (τ m : Fin np → ℝ) (W : ℕ) (S : Finset ℕ) :
    ∑ j ∈ S, ∑ x : SrcCol K (Fin np), ‖(b3BirthAt b τ m W j).1 x x‖ ≤ birthC b m := by
  calc ∑ j ∈ S, ∑ x : SrcCol K (Fin np), ‖(b3BirthAt b τ m W j).1 x x‖
      ≤ ∑ j ∈ S, ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = j then |dStar b * m i| else 0 :=
        sum_le_sum fun j _ => sum_norm_birthAt_le b τ m W j
    _ = ∑ i, if ⌊(W : ℝ) * τ i⌋₊ ∈ S then |dStar b * m i| else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_ite_eq]
    _ ≤ birthC b m := sum_le_sum fun i _ => by split_ifs <;> [exact le_rfl; exact abs_nonneg _]

/-! ## The start value -/

/-- **The trace of the initial Gram state is at most `4K`** (modes `t ≤ 1`). -/
theorem trace_initialGram_le (π : Type*) [Fintype π] {t : ℕ → ℝ} (ht : ∀ k, t k ≤ 1) (h : ℝ) :
    ((initialGram K π t h).1.trace).re ≤ 4 * K := by
  have hb := CutoffLimit.hsSq_mode_le (initialFrame K π t h) (fun _ => 1)
    (fun k => h ^ 2 < t k.val) (fun x k σ => by
      simp only [initialFrame]
      split_ifs with hk
      · have h0 : 0 ≤ t k.val := (sq_nonneg h).trans hk.2.le
        exact (CutoffLimit.norm_mode_entry_sq_le h0 (ht _) σ x.2).trans
          (Real.sqrt_le_one.2 (ht _))
      · simp) (fun x j => rfl)
  have e : ((initialGram K π t h).1.trace).re = hsSq (initialFrame K π t h) := by
    change ((sourceGram (initialFrame K π t h)).trace).re = _
    rw [ClosedSumProof.re_trace_sourceGram]
    rfl
  rw [e]
  refine hb.trans ?_
  calc ∑ k : Fin K, 4 * (if h ^ 2 < t k.val then (1 : ℝ) else 0) ≤ ∑ _k : Fin K, (4 : ℝ) :=
        sum_le_sum fun k _ => by split_ifs <;> norm_num
    _ = 4 * K := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **The start bound**: for an admissible frame, a.s. `Re Tr M_{n_s} ≤ 4K`. -/
theorem ae_b3Tr_start_le {b E s h : ℝ} {τ m : Fin np → ℝ} (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (hτ : ∀ i, s < τ i)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ y ∂closedLaw b W np, b3Tr b E s h τ m W (closeLen s W) Vs y ≤ 4 * K := by
  have h1 := ae_b3ClosedGramAt_start_adm (m := m) hb hE1 hE2 hW hτ hVs
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  filter_upwards [hq.ae h1] with y hy
  unfold b3Tr
  rw [show y = ((y.1.1, y.1.2), y.2) from rfl, hy y.1.2 y.2]
  exact trace_initialGram_le _ (fun k => ClosedSum.physTseq_le_one _ k) h

end BlockBand.SourceProcess.PhysApprox.B3.StopTail
