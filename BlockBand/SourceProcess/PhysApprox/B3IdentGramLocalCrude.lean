module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalStep
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalClose

/-!
# The special cells and the endpoint correction, pathwise

* **`crude_pt`**: on any cell, `|Dh j| ≤ ε + K₀ eDist(ẑ(t_{j+1}), ẑ(t_j)) + C_L/W`;
  **`eDist_zHat_le`**: that distance is at most `2 Σ_c |Δ_c| + Σ_e |Δ A_e|` (the increments of
  `Ŷ` and of the cut drift);
* `alive_tele` (abstract): over decreasing alive indicators, increments of a function vanishing
  at `p`, at `q + 1` and at every first death telescope to `0`;
* **`corrF_eq_zero_of_nb`**, **`corrF_eq_zero_of_trace`**: the correction vanishes off a
  birth length, and wherever `Re Tr M ≥ R ≥ R₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal

variable {K np : ℕ}

/-!
## Abstract telescoping over decreasing alive indicators
-/

theorem alive_down {A : ℕ → Prop} (hA : ∀ j, A (j + 1) → A j) {i n : ℕ} (hin : i ≤ n)
    (hn : A n) : A i := by
  induction n, hin using Nat.le_induction with
  | base => exact hn
  | succ n _ ih => exact ih (hA n hn)

theorem alive_tele (f : ℕ → ℂ) (A : ℕ → Prop) [DecidablePred A] (hA : ∀ j, A (j + 1) → A j)
    {p q : ℕ} (hfp : f p = 0) (hfq : f (q + 1) = 0)
    (hstep : ∀ n, p < n → n ≤ q → A (n - 1) → ¬ A n → f n = 0) :
    ∑ j ∈ Finset.Ico p (q + 1), (if A j then f (j + 1) - f j else 0) = 0 := by
  classical
  have key : ∀ n, p ≤ n → n ≤ q + 1 →
      ∑ j ∈ Finset.Ico p n, (if A j then f (j + 1) - f j else 0) =
        if (∀ j, p ≤ j → j < n → A j) then f n else 0 := by
    intro n hpn hnq
    induction n, hpn using Nat.le_induction with
    | base => simp [hfp]
    | succ n hpn ih =>
      rw [Finset.sum_Ico_succ_top hpn, ih (by omega)]
      by_cases h1 : ∀ j, p ≤ j → j < n → A j
      · by_cases h2 : A n
        · have h3 : ∀ j, p ≤ j → j < n + 1 → A j := fun j hj hjn => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with h | h
            · exact h1 j hj h
            · exact h ▸ h2
          rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h3),
            ite_eq_left_of_eq_true _ _ (eq_true h2)]; ring
        · have h3 : ¬ ∀ j, p ≤ j → j < n + 1 → A j := fun h => h2 (h n hpn (Nat.lt_succ_self n))
          have hfn : f n = 0 := by
            rcases eq_or_lt_of_le hpn with h | h
            · rw [← h]; exact hfp
            · exact hstep n h (by omega) (h1 (n - 1) (by omega) (by omega)) h2
          rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h3),
            ite_eq_right_of_eq_false _ _ (eq_false h2), hfn, add_zero]
      · have h3 : ¬ ∀ j, p ≤ j → j < n + 1 → A j := fun h =>
          h1 fun j hj hjn => h j hj (hjn.trans (Nat.lt_succ_self n))
        have h2 : ¬ A n := fun hn => h1 fun j _ hjn => alive_down hA hjn.le hn
        rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h3),
          ite_eq_right_of_eq_false _ _ (eq_false h2), add_zero]
  by_cases hpq : p ≤ q + 1
  · rw [key (q + 1) hpq le_rfl]
    split_ifs <;> simp [hfq]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-!
## The crude bound on a cell
-/

section Crude

variable {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} {a t : ℝ≥0}

/-- **The crude bound on a cell.** -/
theorem crude_pt (hV : Measurable V) (hχ : Continuous χ) (hΛ : Continuous Λ) (j : ℕ)
    (y : ProbedPath W np × ℝ) {ε K₀ CL : ℝ} (hCL : 0 ≤ CL)
    (hFc : ‖F (zHat χ b E s h τ m W V (cellT s W a t (j + 1)) y) -
        F (zHat χ b E s h τ m W V (cellT s W a t j) y)‖ ≤
      ε + K₀ * eDist (zHat χ b E s h τ m W V (cellT s W a t (j + 1)) y)
        (zHat χ b E s h τ m W V (cellT s W a t j) y))
    (hL : ∀ r ∈ Ioc (cellT s W a t j : ℝ) (cellT s W a t (j + 1)),
      ‖lInt χ b E s h τ m W V Λ y r‖ ≤ CL) :
    ‖Dh χ b E s h τ m W V F Λ a t j y‖ ≤
      ε + K₀ * eDist (zHat χ b E s h τ m W V (cellT s W a t (j + 1)) y)
        (zHat χ b E s h τ m W V (cellT s W a t j) y) + CL * (W : ℝ)⁻¹ := by
  rw [Dh_eq hV hχ hΛ]
  refine (norm_sub_le _ _).trans (add_le_add hFc ?_)
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hL
  rw [Real.volume_real_Ioc] at hI
  refine hI.trans (mul_le_mul_of_nonneg_left (max_le ?_ (by positivity)) hCL)
  have := cellT_succ_sub_le s W a t j
  rwa [one_div] at this

theorem eDist_zHat_le (y : ProbedPath W np × ℝ) (u v : ℝ≥0) :
    eDist (zHat χ b E s h τ m W V v y) (zHat χ b E s h τ m W V u y) ≤
      2 * ∑ c, ‖gramEntry c (yHat b E s h τ m W (limLenAll s W v) V y) -
          gramEntry c (yHat b E s h τ m W (limLenAll s W u) V y)‖ +
        ∑ e, ‖genA χ b E s τ m (pG b E s h τ m W V) e v y -
          genA χ b E s τ m (pG b E s h τ m W V) e u y‖ := by
  unfold eDist
  simp only [zHat, sub_self, norm_zero, Finset.sum_const_zero, add_zero]
  have : ∑ e, ‖gramEntry e (yHat b E s h τ m W (limLenAll s W v) V y) -
        gramEntry e (y0P b E s h τ m W V y) - genA χ b E s τ m (pG b E s h τ m W V) e v y -
        (gramEntry e (yHat b E s h τ m W (limLenAll s W u) V y) -
          gramEntry e (y0P b E s h τ m W V y) - genA χ b E s τ m (pG b E s h τ m W V) e u y)‖ ≤
      ∑ e, (‖gramEntry e (yHat b E s h τ m W (limLenAll s W v) V y) -
          gramEntry e (yHat b E s h τ m W (limLenAll s W u) V y)‖ +
        ‖genA χ b E s τ m (pG b E s h τ m W V) e v y -
          genA χ b E s τ m (pG b E s h τ m W V) e u y‖) :=
    Finset.sum_le_sum fun e _ => by
      refine le_of_eq_of_le (by ring_nf) (norm_sub_le _ _)
  rw [Finset.sum_add_distrib] at this
  linarith

/-- The increment of the cut drift along a feasible path. -/
theorem norm_genA_sub_le (hV : Measurable V) (hχ : Continuous χ) {CA : ℝ}
    (hCA : ∀ e : GIdx K np, ∀ J ∈ jSet (K := K) b m, ∀ H : GSt K np,
      GramFeasible (srcSignature K (Fin np)) H → ‖lamA χ b E e (J, H - J)‖ ≤ CA)
    {y : ProbedPath W np × ℝ} (hy : FeasPath b E s h τ m W V y) (e : GIdx K np) {u v : ℝ≥0}
    (huv : u ≤ v) :
    ‖genA χ b E s τ m (pG b E s h τ m W V) e v y - genA χ b E s τ m (pG b E s h τ m W V) e u y‖ ≤
      CA * ((v : ℝ) - u) := by
  rw [genA_sub hV hχ e y huv]
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (u : ℝ) v)
    (f := aInt χ b E s h τ m W V e y) (C := CA) measure_Ioc_lt_top fun r _ => by
    have := hCA e _ (gramJ_mem_jSet b s τ m r.toNNReal)
      (b3ClosedGramAt b E s h τ m W (limLenAll s W r.toNNReal) V y)
      (hy _ (closeLen_le_limLenAll _))
    rw [← gY_pG] at this
    exact this
  rw [Real.volume_real_Ioc, max_eq_left (sub_nonneg.2 (NNReal.coe_le_coe.2 huv))] at hI
  exact hI

/-!
## The endpoint correction
-/

theorem corrF_eq_zero_of_nb (hτ : ∀ i, s < τ i) (hW : 1 ≤ W) {u : ℝ≥0}
    (hnb : ¬ IsBirthStep τ W (limLenAll s W u)) (y : ProbedPath W np × ℝ) :
    corrF χ b E s h τ m W V F u y = 0 := by
  rw [corrF, stZ_eq_zHat (b := b) (m := m) hτ hW hnb, sub_self]

/-- **The correction vanishes where the trace is beyond the cutoff region.** -/
theorem corrF_eq_zero_of_trace {Rχ : ℝ} (hFv : ∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ)
    {CT R : ℝ} (hCT : ∀ J ∈ jSet (K := K) b m, trRe J ≤ CT) (hR : Rχ + CT < R) (u : ℝ≥0)
    (y : ProbedPath W np × ℝ)
    (htr : R ≤ trRe (b3ClosedGramAt b E s h τ m W (limLenAll s W u) V y)) :
    corrF χ b E s h τ m W V F u y = 0 := by
  have hz : ∀ J ∈ jSet (K := K) b m, ∀ z : ZSt K np,
      z.1 = b3ClosedGramAt b E s h τ m W (limLenAll s W u) V y - J → F z = 0 := by
    intro J hJ z hz
    by_contra h0
    have h1 := (hFv z h0).1
    rw [hz, trRe_sub] at h1
    have := hCT J hJ
    have := (abs_le.1 h1).2
    linarith
  rw [corrF, hz _ (gramJ_mem_jSet b s τ m u) _ rfl,
    hz _ (b3JumpAt_mem_jSet b s τ m W _) _ rfl, sub_self]

end Crude

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
