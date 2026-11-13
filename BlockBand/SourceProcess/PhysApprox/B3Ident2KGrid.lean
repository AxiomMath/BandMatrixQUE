module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Fatou
public import BlockBand.SourceProcess.PhysApprox.B3FddMod

/-!
# The grid functional of the `𝒦` stop and its finite-`W` bound

A finite grid `r : α → ℚ` of model times with `r a₀ = 0`, a trace level `L`, a truncation `N`
and the `𝒦` entry `ij`. On the observables (`Re Tr M` at the grid times, `𝒦_ij` at the grid
times) the **grid functional** is
`fGrid(x) = max_a 1{Re Tr M(r_b) < L for all r_b ≤ r_a} · min(|𝒦(r_a) − 𝒦(0) − κ_a|², N)`,
`κ_a` the deterministic birth part. Its continuous approximations `psiFun k` replace each
indicator by `cl01(k(L − ·))`.

* `fGrid_le`, `psiFun_le_fGrid`, `tendsto_psiFun`, `continuous_psiFun`, `psiGrid` (the BCF).
* `re_trace_b3JumpAt_nonneg`, `re_trace_b3JumpAt_le`: `0 ≤ Re Tr J_j ≤ Σ_i d_* m_i`.
* **`ofReal_fGrid_le`** (pointwise, on the cap event): `fGrid(obs_W) ≤ 2 + 2C_J² + 2·Z + N·1_Bad`,
  with `Z` the integrand of `ComplexKStoppedMomentMax` (level `R`) and `Bad` the event that the
  grid sees the trace below `L` up to `r_a` while the path reaches `R` before `⌊W(s+r_a)⌋`.
* **`bad_subset`**: if `R ≥ L + Σ d_* m + 2` and the grid is `δ`-dense from the left, `Bad` lies
  in the union over the columns of the modulus events of `modulusS` (window `δ`,
  `η = 1/#cols`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- The grid observable labels: `M` diagonal entries at the grid times, `𝒦_ij` at the grid
times. -/
abbrev GLab (K np : ℕ) (α : Type) := (α × SrcCol K (Fin np)) ⊕ α

variable {K np : ℕ} {α : Type} [Fintype α] [Nonempty α]

/-- `Re Tr M` at the grid time `r_a`. -/
def trOf (x : GLab K np α → ℂ) (a : α) : ℝ := (∑ c, x (Sum.inl (a, c))).re

/-- The grid alive indicator up to `r_a`. -/
def gridInd (L : ℝ) (r : α → ℚ) (x : GLab K np α → ℂ) (a : α) : ℝ :=
  ∏ b ∈ Finset.univ.filter (fun b => r b ≤ r a), if trOf x b < L then 1 else 0

/-- Its continuous approximation. -/
def gridCl (L : ℝ) (r : α → ℚ) (k : ℕ) (x : GLab K np α → ℂ) (a : α) : ℝ :=
  ∏ b ∈ Finset.univ.filter (fun b => r b ≤ r a), cl01 ((k : ℝ) * (L - trOf x b))

/-- The truncated squared `𝒦` increment. -/
def kTerm (N : ℝ) (κ : α → ℂ) (a₀ : α) (x : GLab K np α → ℂ) (a : α) : ℝ :=
  min (‖x (Sum.inr a) - x (Sum.inr a₀) - κ a‖ ^ 2) N

/-- **The grid functional.** -/
def fGrid (L : ℝ) (r : α → ℚ) (N : ℝ) (κ : α → ℂ) (a₀ : α) (x : GLab K np α → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => gridInd L r x a * kTerm N κ a₀ x a

/-- Its continuous approximations. -/
def psiFun (L : ℝ) (r : α → ℚ) (N : ℝ) (κ : α → ℂ) (a₀ : α) (k : ℕ)
    (x : GLab K np α → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => gridCl L r k x a * kTerm N κ a₀ x a

variable {L N : ℝ} {r : α → ℚ} {κ : α → ℂ} {a₀ : α}

omit [Nonempty α] in
theorem gridInd_nonneg (x : GLab K np α → ℂ) (a : α) : 0 ≤ gridInd L r x a :=
  Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num

omit [Nonempty α] in
theorem gridInd_le_one (x : GLab K np α → ℂ) (a : α) : gridInd L r x a ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => by split_ifs <;> norm_num) fun _ _ => by split_ifs <;> norm_num

omit [Nonempty α] in
theorem gridInd_eq_zero {x : GLab K np α → ℂ} {a : α} (h : ¬ ∀ b, r b ≤ r a → trOf x b < L) :
    gridInd L r x a = 0 := by
  push Not at h
  obtain ⟨b, hb1, hb2⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ b, hb1⟩) ?_
  simp [not_lt.2 hb2]

omit [Fintype α] [Nonempty α] in
theorem kTerm_nonneg (hN : 0 ≤ N) (x : GLab K np α → ℂ) (a : α) : 0 ≤ kTerm N κ a₀ x a :=
  le_min (by positivity) hN

omit [Fintype α] [Nonempty α] in
theorem kTerm_le (x : GLab K np α → ℂ) (a : α) : kTerm N κ a₀ x a ≤ N := min_le_right _ _

omit [Nonempty α] in
theorem gridCl_le (x : GLab K np α → ℂ) (a : α) (k : ℕ) : gridCl L r k x a ≤ gridInd L r x a :=
  Finset.prod_le_prod₀ (fun _ _ => cl01_nonneg _) fun _ _ => cl01_le_ind (Nat.cast_nonneg k) _ _

omit [Nonempty α] in
theorem gridCl_nonneg (x : GLab K np α → ℂ) (a : α) (k : ℕ) : 0 ≤ gridCl L r k x a :=
  Finset.prod_nonneg fun _ _ => cl01_nonneg _

theorem fGrid_le (hN : 0 ≤ N) (x : GLab K np α → ℂ) : fGrid L r N κ a₀ x ≤ N :=
  Finset.sup'_le _ _ fun a _ => (mul_le_of_le_one_left (kTerm_nonneg hN x a)
    (gridInd_le_one x a)).trans (kTerm_le x a)

theorem psiFun_nonneg (hN : 0 ≤ N) (k : ℕ) (x : GLab K np α → ℂ) :
    0 ≤ psiFun L r N κ a₀ k x := by
  obtain ⟨a⟩ := ‹Nonempty α›
  exact (mul_nonneg (gridCl_nonneg x a k) (kTerm_nonneg hN x a)).trans
    (Finset.le_sup' (fun a => gridCl L r k x a * kTerm N κ a₀ x a) (Finset.mem_univ a))

theorem psiFun_le_fGrid (hN : 0 ≤ N) (k : ℕ) (x : GLab K np α → ℂ) :
    psiFun L r N κ a₀ k x ≤ fGrid L r N κ a₀ x :=
  Finset.sup'_le _ _ fun a _ => (mul_le_mul_of_nonneg_right (gridCl_le x a k)
    (kTerm_nonneg hN x a)).trans
    (Finset.le_sup' (fun a => gridInd L r x a * kTerm N κ a₀ x a) (Finset.mem_univ a))

theorem tendsto_psiFun (x : GLab K np α → ℂ) :
    Tendsto (fun k => psiFun L r N κ a₀ k x) atTop (𝓝 (fGrid L r N κ a₀ x)) := by
  refine Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty fun a _ => ?_
  refine Tendsto.mul ?_ tendsto_const_nhds
  exact tendsto_finsetProd _ fun b _ => tendsto_cl01_ind L (trOf x b)

omit [Fintype α] [Nonempty α] in
theorem continuous_trOf (a : α) : Continuous fun x : GLab K np α → ℂ => trOf x a :=
  Complex.continuous_re.comp (continuous_finsetSum _ fun _ _ => continuous_apply _)

theorem continuous_psiFun (k : ℕ) :
    Continuous fun x : GLab K np α → ℂ => psiFun L r N κ a₀ k x := by
  refine Continuous.finset_sup'_apply Finset.univ_nonempty fun a _ => ?_
  refine (continuous_finsetProd _ fun b _ => continuous_cl01.comp (continuous_const.mul
    (continuous_const.sub (continuous_trOf b)))).mul ?_
  exact ((continuous_norm.comp (((continuous_apply (Sum.inr a)).sub
    (continuous_apply (Sum.inr a₀))).sub continuous_const)).pow 2).min continuous_const

/-- The approximations as bounded continuous functions. -/
def psiGrid (L : ℝ) (r : α → ℚ) (N : ℝ) (hN : 0 ≤ N) (κ : α → ℂ) (a₀ : α) (k : ℕ) :
    BoundedContinuousFunction (GLab K np α → ℂ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (psiFun L r N κ a₀ k) (continuous_psiFun k) N
    fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (psiFun_nonneg hN k x)]
      exact (psiFun_le_fGrid hN k x).trans (fGrid_le hN x)

theorem psiGrid_apply (hN : 0 ≤ N) (k : ℕ) (x : GLab K np α → ℂ) :
    psiGrid L r N hN κ a₀ k x = psiFun L r N κ a₀ k x := rfl

/-!
## The Gram births are bounded
-/

theorem re_trace_b3BirthAt (b : ℝ) (τ m : Fin np → ℝ) (W l : ℕ) :
    ((b3BirthAt (K := K) b τ m W l).1.trace).re =
      ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = l then dStar b * m i else 0 := by
  simp only [b3BirthAt, Prod.fst_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem re_trace_b3JumpAt_eq (b s : ℝ) (τ m : Fin np → ℝ) (W j : ℕ) :
    ((b3JumpAt (K := K) b s τ m W j).1.trace).re =
      ∑ i, if ⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W) j then dStar b * m i else 0 := by
  simp only [b3JumpAt, Prod.fst_sum, Matrix.trace_sum, Complex.re_sum, re_trace_b3BirthAt]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_ite_eq _ _ _

theorem re_trace_b3JumpAt_nonneg {b : ℝ} (hb : b < 1) {m : Fin np → ℝ} (hm : ∀ i, 0 ≤ m i)
    (s : ℝ) (τ : Fin np → ℝ) (W j : ℕ) : 0 ≤ ((b3JumpAt (K := K) b s τ m W j).1.trace).re := by
  rw [re_trace_b3JumpAt_eq]
  have hd : 0 ≤ dStar b := div_nonneg zero_le_one (by linarith)
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> [exact mul_nonneg hd (hm i); exact le_rfl]

theorem re_trace_b3JumpAt_le {b : ℝ} (hb : b < 1) {m : Fin np → ℝ} (hm : ∀ i, 0 ≤ m i)
    (s : ℝ) (τ : Fin np → ℝ) (W j : ℕ) :
    ((b3JumpAt (K := K) b s τ m W j).1.trace).re ≤ ∑ i, dStar b * m i := by
  rw [re_trace_b3JumpAt_eq]
  have hd : 0 ≤ dStar b := div_nonneg zero_le_one (by linarith)
  exact Finset.sum_le_sum fun i _ => by
    split_ifs <;> [exact le_rfl; exact mul_nonneg hd (hm i)]

/-!
## The finite-`W` objects
-/

variable {b E s h : ℝ} {τ m : Fin np → ℝ}

/-- The grid observable labels in `complexObs`. -/
def gIdx (ij : Fin np × Fin np) : GLab K np α → LIdx K np :=
  Sum.elim (fun p => Sum.inl (0, p.2, p.2)) fun _ => Sum.inr (Sum.inr ij)

/-- Their times. -/
def gTime (r : α → ℚ) : GLab K np α → ℝ≥0 :=
  Sum.elim (fun p => ((r p.1 : ℝ)).toNNReal) fun a => ((r a : ℝ)).toNNReal

/-- The grid length at `r_a`. -/
def gLen (s : ℝ) (W : ℕ) (r : α → ℚ) (a : α) : ℕ := limLenAll s W ((r a : ℝ)).toNNReal

/-- The finite-`W` `𝒦` stop integrand of `ComplexKStoppedMomentMax`. -/
def kMaxZ (b E s h : ℝ) (τ m : Fin np → ℝ) (R T : ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (y : ProbedPath W np × ℝ) : ℝ≥0∞ :=
  ⨆ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, (b3Alive b E s h τ m R W j V).indicator
    (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y

/-- The bad event: the grid sees the trace below `L` up to `r_a`, the path reaches `R` before
`⌊W(s + r_a)⌋`. -/
def gridBad (b E s h : ℝ) (τ m : Fin np → ℝ) (L R : ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (r : α → ℚ) :
    Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ a, (∀ c, r c ≤ r a →
      ((b3ClosedGramAt b E s h τ m W (gLen s W r c) V y).1.trace).re < L) ∧
    ∃ i, closeLen s W ≤ i ∧ i < gLen s W r a ∧
      R ≤ ((b3ClosedGramAt b E s h τ m W i V y).1.trace).re}

omit [Fintype α] [Nonempty α] in
theorem trOf_obs {W : ℕ} {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (ij : Fin np × Fin np) (y : ProbedPath W np × ℝ) (a : α) :
    trOf (fun l => b3ObsAll b E s h τ m W V (gIdx ij l) (gTime r l) y) a =
      ((b3ClosedGramAt b E s h τ m W (gLen s W r a) V y).1.trace).re := by
  simp [trOf, gIdx, gTime, b3ObsAll, gLen, gramEntry, Matrix.trace]

omit [Fintype α] [Nonempty α] in
theorem gLen_eq {W : ℕ} (a : α) (hr : 0 ≤ (r a : ℝ)) :
    gLen s W r a = ⌊(W : ℝ) * (s + r a)⌋₊ := by
  rw [gLen, limLenAll, Real.coe_toNNReal _ hr]

omit [Fintype α] [Nonempty α] in
theorem gLen_a₀ {W : ℕ} (hr0 : r a₀ = 0) : gLen s W r a₀ = closeLen s W := by
  simp [gLen, limLenAll, hr0, closeLen]

/-- **The pointwise finite-`W` bound of the grid functional on the cap event.** -/
theorem ofReal_fGrid_le {W : ℕ} {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (ij : Fin np × Fin np) (hN : 0 ≤ N) (hr0 : r a₀ = 0) (hrn : ∀ a, 0 ≤ (r a : ℝ))
    {CJ : ℝ} (hκ : ∀ a, ‖κ a‖ ≤ CJ) (hτ : ∀ j, s < τ j) {R T : ℝ}
    (hrT : ∀ a, s + (r a : ℝ) ≤ T) (y : ProbedPath W np × ℝ)
    (hy : y.1.1 ∈ physCapEventC b E s h K W) :
    ENNReal.ofReal (fGrid L r N κ a₀ (fun l => b3ObsAll b E s h τ m W V (gIdx ij l)
        (gTime r l) y)) ≤
      ENNReal.ofReal (2 + 2 * CJ ^ 2) + 2 * kMaxZ b E s h τ m R T W V ij y +
        (gridBad b E s h τ m L R W V r).indicator (fun _ => ENNReal.ofReal N) y := by
  set x := fun l => b3ObsAll b E s h τ m W V (gIdx ij l) (gTime r l) y with hxdef
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => gridInd L r x a * kTerm N κ a₀ x a)
  have hf : fGrid L r N κ a₀ x = gridInd L r x a * kTerm N κ a₀ x a := ha
  rw [hf]
  have hCJ : 0 ≤ CJ := (norm_nonneg _).trans (hκ a)
  by_cases hg : ∀ c, r c ≤ r a → trOf x c < L
  swap
  · rw [gridInd_eq_zero hg, zero_mul, ENNReal.ofReal_zero]; exact bot_le
  have hle1 : gridInd L r x a * kTerm N κ a₀ x a ≤ kTerm N κ a₀ x a :=
    mul_le_of_le_one_left (kTerm_nonneg hN x a) (gridInd_le_one x a)
  by_cases hal : ∀ i, closeLen s W ≤ i → i < gLen s W r a →
      ((b3ClosedGramAt b E s h τ m W i V y).1.trace).re < R
  · -- alive: the moment bound
    have hx0 : x (Sum.inr a₀) = 0 := by
      show b3ClosedKAt b E s h τ m W (gLen s W r a₀) y ij.1 ij.2 = 0
      rw [gLen_a₀ hr0, b3ClosedKAt_start hτ y, Matrix.zero_apply]
    set Kv := b3ClosedKAt b E s h τ m W (gLen s W r a) y ij.1 ij.2
    have hxa : x (Sum.inr a) = Kv := rfl
    have hZ : ‖Kv‖ₑ ^ 4 ≤ kMaxZ b E s h τ m R T W V ij y := by
      by_cases hl : gLen s W r a ≤ closeLen s W
      · have : gLen s W r a = closeLen s W := le_antisymm hl (by
          unfold gLen limLenAll
          exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (NNReal.coe_nonneg _)) (Nat.cast_nonneg W)))
        have hK0 : Kv = 0 := by
          show b3ClosedKAt b E s h τ m W (gLen s W r a) y ij.1 ij.2 = 0
          rw [this, b3ClosedKAt_start hτ y, Matrix.zero_apply]
        rw [hK0, enorm_zero, zero_pow (by norm_num)]; exact bot_le
      · push Not at hl
        set j := gLen s W r a - 1
        have hj1 : j + 1 = gLen s W r a := by omega
        have hjT : j < ⌊(W : ℝ) * T⌋₊ := by
          have : gLen s W r a ≤ ⌊(W : ℝ) * T⌋₊ := by
            rw [gLen_eq a (hrn a)]
            exact Nat.floor_le_floor (mul_le_mul_of_nonneg_left (hrT a) (Nat.cast_nonneg W))
          omega
        have hmem : y ∈ b3Alive b E s h τ m R W j V :=
          ⟨hy, fun i hi1 hi2 => hal i hi1 (by omega)⟩
        refine le_trans ?_ (le_iSup₂ (f := fun j (_ : j ∈ Finset.Ico (closeLen s W)
          ⌊(W : ℝ) * T⌋₊) => (b3Alive b E s h τ m R W j V).indicator
            (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) j
          (Finset.mem_Ico.2 ⟨by omega, hjT⟩))
        rw [Set.indicator_of_mem hmem, hj1]
    have hkt : kTerm N κ a₀ x a ≤ (2 + 2 * CJ ^ 2) + 2 * ‖Kv‖ ^ 4 := by
      refine (min_le_left _ _).trans ?_
      rw [hxa, hx0, sub_zero]
      have h1 := norm_sub_le Kv (κ a)
      have h2 : ‖Kv‖ ^ 2 ≤ 1 + ‖Kv‖ ^ 4 := by nlinarith [sq_nonneg (‖Kv‖ ^ 2 - 1)]
      have h4 : ‖Kv - κ a‖ ^ 2 ≤ (‖Kv‖ + ‖κ a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h5 : ‖κ a‖ ^ 2 ≤ CJ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hκ a) 2
      nlinarith [sq_nonneg (‖Kv‖ - ‖κ a‖)]
    calc ENNReal.ofReal (gridInd L r x a * kTerm N κ a₀ x a)
        ≤ ENNReal.ofReal ((2 + 2 * CJ ^ 2) + 2 * ‖Kv‖ ^ 4) :=
          ENNReal.ofReal_le_ofReal (hle1.trans hkt)
      _ = ENNReal.ofReal (2 + 2 * CJ ^ 2) + 2 * ‖Kv‖ₑ ^ 4 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
          norm_num
      _ ≤ _ := by
          refine le_trans ?_ le_self_add
          gcongr
  · -- bad
    have hbad : y ∈ gridBad b E s h τ m L R W V r := by
      push Not at hal
      obtain ⟨i, hi1, hi2, hi3⟩ := hal
      refine ⟨hy, a, fun c hc => ?_, i, hi1, hi2, hi3⟩
      have := hg c hc
      rwa [hxdef, trOf_obs] at this
    rw [Set.indicator_of_mem hbad]
    refine le_trans ?_ le_add_self
    exact ENNReal.ofReal_le_ofReal (hle1.trans (kTerm_le x a))

/-- The modulus event of `modulusS` for the diagonal `M` entry of column `col`. -/
def modEvent (b E s h : ℝ) (τ m : Fin np → ℝ) (T δ η : ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (col : SrcCol K (Fin np)) :
    Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ t ∈ Set.Icc s T, ∃ t' ∈ Set.Icc s T,
    |t - t'| ≤ δ ∧ η <
      ‖b3X b E s h τ m W ⌊(W : ℝ) * t⌋₊ V (Sum.inl (0, col, col)) y -
        cEntry (Sum.inl (0, col, col) : CIdx K np) (b3JumpAt b s τ m W ⌊(W : ℝ) * t⌋₊)
          (b3KJumpAt E s τ m W ⌊(W : ℝ) * t⌋₊) -
        (b3X b E s h τ m W ⌊(W : ℝ) * t'⌋₊ V (Sum.inl (0, col, col)) y -
          cEntry (Sum.inl (0, col, col) : CIdx K np) (b3JumpAt b s τ m W ⌊(W : ℝ) * t'⌋₊)
            (b3KJumpAt E s τ m W ⌊(W : ℝ) * t'⌋₊))‖}

theorem floor_max_div {s : ℝ} {W i : ℕ} (hW : 0 < W) (hi : closeLen s W ≤ i) :
    ⌊(W : ℝ) * max s ((i : ℝ) / W)⌋₊ = i := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rcases le_total s ((i : ℝ) / W) with h1 | h1
  · rw [max_eq_right h1, mul_div_cancel₀ _ hW'.ne', Nat.floor_natCast]
  · rw [max_eq_left h1]
    have : (i : ℝ) ≤ W * s := by rw [div_le_iff₀ hW'] at h1; linarith
    have h2 : i ≤ ⌊(W : ℝ) * s⌋₊ := Nat.le_floor this
    exact (le_antisymm h2 hi).symm

omit [Fintype α] [Nonempty α] in
/-- **The bad event lies in the modulus events.** -/
theorem bad_subset {W : ℕ} {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hb : b < 1) (hm : ∀ i, 0 ≤ m i) (hs0 : 0 ≤ s) (hr0 : r a₀ = 0) (hrn : ∀ a, 0 ≤ (r a : ℝ))
    {R T δ : ℝ}
    (hR : L + ∑ i, dStar b * m i + 2 ≤ R) (hrT : ∀ a, s + (r a : ℝ) ≤ T)
    (hdense : ∀ x : ℝ, 0 ≤ x → (∃ a, x < r a) → ∃ c, (r c : ℝ) ≤ x ∧ x - δ ≤ r c)
    (hδ : 0 ≤ δ) (ij : Fin np × Fin np) :
    gridBad b E s h τ m L R W V r ⊆ ⋃ col : SrcCol K (Fin np),
      modEvent b E s h τ m T δ (1 / (Fintype.card (SrcCol K (Fin np)) : ℝ)) W V col := by
  rintro y ⟨hy, a, hg, i, hi1, hi2, hiR⟩
  have hW : 0 < W := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · subst h0; simp [gLen, limLenAll] at hi2
    · exact h0
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  -- the grid point below `i`
  have hia : (i : ℝ) / W - s < r a := by
    have h1 : i < ⌊(W : ℝ) * (s + r a)⌋₊ := by rwa [← gLen_eq a (hrn a)]
    have h2 : (i : ℝ) < W * (s + r a) :=
      lt_of_lt_of_le (by exact_mod_cast h1) (Nat.floor_le (by
        have := hrn a
        positivity))
    have : (i : ℝ) / W < s + r a := by rw [div_lt_iff₀ hW']; linarith
    linarith
  obtain ⟨c, hc1, hc2⟩ : ∃ c, (r c : ℝ) ≤ max 0 ((i : ℝ) / W - s) ∧
      max 0 ((i : ℝ) / W - s) - δ ≤ r c := by
    rcases le_total ((i : ℝ) / W - s) 0 with hx | hx
    · refine ⟨a₀, ?_, ?_⟩ <;> simp [hr0, max_eq_left hx, hδ]
    · rw [max_eq_right hx]
      exact hdense _ hx ⟨a, hia⟩
  have hca : r c ≤ r a := by
    have : (r c : ℝ) ≤ r a := hc1.trans (max_le (hrn a) hia.le)
    exact_mod_cast this
  have hLc := hg c hca
  -- the two times
  set t := max s ((i : ℝ) / W)
  set t' := s + (r c : ℝ)
  have ht : ⌊(W : ℝ) * t⌋₊ = i := floor_max_div hW hi1
  have ht' : ⌊(W : ℝ) * t'⌋₊ = gLen s W r c := (gLen_eq c (hrn c)).symm
  have htt : |t - t'| ≤ δ := by
    rw [abs_le]
    have e : t = s + max 0 ((i : ℝ) / W - s) := by
      show max s ((i : ℝ) / W) = _
      rcases le_total ((i : ℝ) / W - s) 0 with h | h
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    constructor <;> [linarith; linarith]
  have htI : t ∈ Set.Icc s T := ⟨le_max_left _ _, max_le (by linarith [hrT a, hrn a])
    (by linarith [hrT a, hia])⟩
  have htI' : t' ∈ Set.Icc s T := ⟨by linarith [hrn c], hrT c⟩
  -- the trace defect
  set Gi := b3ClosedGramAt b E s h τ m W i V y
  set Gc := b3ClosedGramAt b E s h τ m W (gLen s W r c) V y
  set Ji := b3JumpAt (K := K) b s τ m W i
  set Jc := b3JumpAt (K := K) b s τ m W (gLen s W r c)
  set d : SrcCol K (Fin np) → ℂ := fun col =>
    gramEntry (0, col, col) Gi - gramEntry (0, col, col) Ji -
      (gramEntry (0, col, col) Gc - gramEntry (0, col, col) Jc)
  have hsum : (∑ col, d col).re = (Gi.1.trace).re - (Ji.1.trace).re -
      ((Gc.1.trace).re - (Jc.1.trace).re) := by
    simp [d, gramEntry, Matrix.trace, Finset.sum_sub_distrib, Complex.re_sum]
  have hJi := re_trace_b3JumpAt_le (K := K) hb hm s τ W i
  have hJc := re_trace_b3JumpAt_nonneg (K := K) hb hm s τ W (gLen s W r c)
  have h2 : 2 ≤ ∑ col, ‖d col‖ := by
    have hre : (∑ col, d col).re ≤ ∑ col, ‖d col‖ :=
      (Complex.re_le_norm _).trans (norm_sum_le _ _)
    have : (Gc.1.trace).re < L := hLc
    linarith
  have hcard : 0 < Fintype.card (SrcCol K (Fin np)) :=
    Fintype.card_pos_iff.2 ⟨Sum.inr ij.1⟩
  obtain ⟨col, hcol⟩ : ∃ col, 1 / (Fintype.card (SrcCol K (Fin np)) : ℝ) < ‖d col‖ := by
    by_contra hne
    push Not at hne
    have := Finset.sum_le_sum fun col (_ : col ∈ Finset.univ) => hne col
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one_div_cancel (by exact_mod_cast hcard.ne')] at this
    linarith
  refine Set.mem_iUnion.2 ⟨col, hy, t, htI, t', htI', htt, ?_⟩
  rw [ht, ht']
  exact hcol

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
