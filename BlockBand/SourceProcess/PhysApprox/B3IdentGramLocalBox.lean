module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalMeas

/-!
# Compact boxes along feasible paths

* `jSet b m`: the finitely many jump values (`gramJ u` and `b3JumpAt n` lie in it);
  `exists_jSet_bound`: their entries and traces are bounded;
* `stateOf H H₀ J J₀ α = (H − J, (H − J) − (H₀ − J₀) − α, H₀ − J₀)`; `stZ` and `zHat` are such
  states; **`exists_bound_stateOf`**: a continuous function vanishing off the trace cutoffs is
  bounded on all of them (feasible `H, H₀`, jumps in `jSet`, `|α| ≤ B_A`);
* `exists_bound_lamA`, **`norm_genA_le`**: the cut drift integrand and the cut drift on `[0, T₁]`;
* `kBox B` (compact); **`zHat_mem_kBox`**: on the alive set at `j`, the state at a time of length
  `≤ j` lies in a box depending on `R` only.
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
## Jump values
-/

/-- A sum of the births of a subset of the probes. -/
def jSel (b : ℝ) (m : Fin np → ℝ) (x : Fin np → Bool) : GSt K np :=
  ∑ i, if x i then ((((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
      ((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1) :
        GramState (SrcCol K (Fin np))) else 0

/-- The jump values. -/
def jSet (b : ℝ) (m : Fin np → ℝ) : Set (GSt K np) := range (jSel b m)

theorem jSet_finite (b : ℝ) (m : Fin np → ℝ) : (jSet (K := K) b m).Finite := finite_range _

theorem gramJ_mem_jSet (b s : ℝ) (τ m : Fin np → ℝ) (u : ℝ≥0) :
    gramJ (K := K) b s τ m u ∈ jSet b m :=
  ⟨fun i => decide (τ i - s ≤ (u : ℝ)), (gramJ_eq_sel b s τ m u).symm⟩

theorem b3JumpAt_mem_jSet (b s : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    b3JumpAt (K := K) b s τ m W n ∈ jSet b m := by
  refine ⟨fun i => decide (⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W) n), ?_⟩
  rw [b3JumpAt_eq_sum]
  simp only [jSel, decide_eq_true_eq]

theorem exists_jSet_bound (b : ℝ) (m : Fin np → ℝ) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ J ∈ jSet (K := K) b m, (∀ e, ‖gramEntry e J‖ ≤ CJ) ∧
      |trRe J| ≤ (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ := by
  classical
  set CJ := ∑ x : Fin np → Bool, ∑ e : GIdx K np, ‖gramEntry e (jSel (K := K) b m x)‖
  have hCJ : 0 ≤ CJ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have he : ∀ J ∈ jSet (K := K) b m, ∀ e, ‖gramEntry e J‖ ≤ CJ := by
    rintro _ ⟨x, rfl⟩ e
    refine (Finset.single_le_sum (f := fun e => ‖gramEntry e (jSel (K := K) b m x)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ e)).trans ?_
    exact Finset.single_le_sum (f := fun x => ∑ e : GIdx K np, ‖gramEntry e (jSel (K := K) b m x)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x)
  refine ⟨CJ, hCJ, fun J hJ => ⟨he J hJ, ?_⟩⟩
  refine (abs_trRe_le J).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.univ : Finset (SrcCol K (Fin np)))
    (fun k => ‖gramEntry ((0 : Fin 2), k, k) J‖) CJ (fun k _ => he J hJ _)
  simpa [nsmul_eq_mul] using this

/-!
## States along feasible paths
-/

/-- The state `(H − J, (H − J) − (H₀ − J₀) − α, H₀ − J₀)`. -/
def stateOf (H H0 J J0 : GSt K np) (α : GIdx K np → ℂ) : ZSt K np :=
  (H - J, fun e => gramEntry e (H - J) - gramEntry e (H0 - J0) - α e, H0 - J0)

/-- The box of states with all coordinates of norm `≤ B`. -/
def kBox (B : ℝ) : Set (ZSt K np) :=
  {z | (∀ e, ‖gramEntry e z.1‖ ≤ B) ∧ (∀ e, ‖z.2.1 e‖ ≤ B) ∧ ∀ e, ‖gramEntry e z.2.2‖ ≤ B}

theorem kBox_eq (B : ℝ) : kBox (K := K) (np := np) B =
    {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ B} ×ˢ
      ((Set.pi univ fun _ => Metric.closedBall (0 : ℂ) B) ×ˢ
        {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ B}) := by
  ext z; simp [kBox]

theorem isCompact_kBox (B : ℝ) : IsCompact (kBox (K := K) (np := np) B) := by
  rw [kBox_eq]
  exact (isCompact_box B).prod ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod
    (isCompact_box B))

theorem kBox_mono {B B' : ℝ} (h : B ≤ B') : kBox (K := K) (np := np) B ⊆ kBox B' :=
  fun _ hz => ⟨fun e => (hz.1 e).trans h, fun e => (hz.2.1 e).trans h,
    fun e => (hz.2.2 e).trans h⟩

section Bounds

variable {b : ℝ} {m : Fin np → ℝ} {Rχ : ℝ}

/-- **A continuous function vanishing off the trace cutoffs is bounded on feasible states.** -/
theorem exists_bound_stateOf {G : GSt K np × ZSt K np → ℂ} (hG : Continuous G)
    (hGv : ∀ p, G p ≠ 0 → |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ) (BA : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J' ∈ jSet (K := K) b m, ∀ H H0 J J0 : GSt K np,
      ∀ α : GIdx K np → ℂ, GramFeasible (srcSignature K (Fin np)) H →
      GramFeasible (srcSignature K (Fin np)) H0 → J ∈ jSet b m → J0 ∈ jSet b m →
      (∀ e, ‖α e‖ ≤ BA) → ‖G (J', stateOf H H0 J J0 α)‖ ≤ C := by
  obtain ⟨CJ, -, hCJ⟩ := exists_jSet_bound (K := K) b m
  set BY := 2 * (Rχ + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ
  set BX := BY + BY + BA
  obtain ⟨C, hC⟩ := exists_bound_finite_compact hG (jSet_finite (K := K) b m)
    (isCompact_kBox (K := K) (np := np) (max BY BX))
  refine ⟨max C 0, le_max_right _ _, fun J' hJ' H H0 J J0 α hH hH0 hJ hJ0 hα => ?_⟩
  by_cases h0 : G (J', stateOf H H0 J J0 α) = 0
  · rw [h0, norm_zero]; exact le_max_right _ _
  obtain ⟨h1, h2⟩ := hGv _ h0
  have hy : ∀ e, ‖gramEntry e (H - J)‖ ≤ BY := fun e =>
    entry_sub_le_of_feasible hH (hCJ J hJ).1 (hCJ J hJ).2 h1 e
  have hy0 : ∀ e, ‖gramEntry e (H0 - J0)‖ ≤ BY := fun e =>
    entry_sub_le_of_feasible hH0 (hCJ J0 hJ0).1 (hCJ J0 hJ0).2 h2 e
  refine (hC J' hJ' _ ⟨fun e => (hy e).trans (le_max_left _ _), fun e => ?_,
    fun e => (hy0 e).trans (le_max_left _ _)⟩).trans (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (hy e) (hy0 e)))
    (hα e))

theorem exists_bound_lamA {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0) (E : ℝ) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ e : GIdx K np, ∀ J ∈ jSet (K := K) b m, ∀ H : GSt K np,
      GramFeasible (srcSignature K (Fin np)) H → ‖lamA χ b E e (J, H - J)‖ ≤ CA := by
  classical
  obtain ⟨CJ, -, hCJ⟩ := exists_jSet_bound (K := K) b m
  set BY := 2 * (Rχ + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ
  have hb : ∀ e : GIdx K np, ∃ C : ℝ, ∀ J ∈ jSet (K := K) b m,
      ∀ y ∈ {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ BY},
        ‖lamA χ b E e (J, y)‖ ≤ C := fun e =>
    exists_bound_finite_compact (continuous_lamA' hχ b E e) (jSet_finite b m) (isCompact_box BY)
  choose Cf hCf using hb
  refine ⟨∑ e, |Cf e|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun e J hJ H hH => ?_⟩
  by_cases h0 : lamA χ b E e (J, H - J) = 0
  · rw [h0, norm_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 := lamA_ne_zero hR b E e h0
  refine (hCf e J hJ _ fun e' => entry_sub_le_of_feasible hH (hCJ J hJ).1 (hCJ J hJ).2 h1 e').trans
    ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun e => |Cf e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)

end Bounds

/-!
## Along the prelimit process
-/

section Process

variable {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

/-- Feasibility at every length `≥ n_s`. -/
def FeasPath (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    Prop :=
  ∀ n, closeLen s W ≤ n →
    GramFeasible (srcSignature K (Fin np)) (b3ClosedGramAt b E s h τ m W n V y)

theorem stZ_eq_stateOf (u : ℝ≥0) (y : ProbedPath W np × ℝ) :
    stZ χ b E s τ m (pG b E s h τ m W V) u y =
      stateOf (b3ClosedGramAt b E s h τ m W (limLenAll s W u) V y)
        (b3ClosedGramAt b E s h τ m W (limLenAll s W 0) V y) (gramJ b s τ m u) (gramJ b s τ m 0)
        (fun e => genA χ b E s τ m (pG b E s h τ m W V) e u y) := rfl

theorem zHat_eq_stateOf (u : ℝ≥0) (y : ProbedPath W np × ℝ) :
    zHat χ b E s h τ m W V u y =
      stateOf (b3ClosedGramAt b E s h τ m W (limLenAll s W u) V y)
        (b3ClosedGramAt b E s h τ m W (limLenAll s W 0) V y)
        (b3JumpAt b s τ m W (limLenAll s W u)) (gramJ b s τ m 0)
        (fun e => genA χ b E s τ m (pG b E s h τ m W V) e u y) := rfl

/-- **The cut drift is bounded along a feasible path.** -/
theorem norm_genA_le {CA : ℝ} (hCA0 : 0 ≤ CA) (hCA : ∀ e : GIdx K np, ∀ J ∈ jSet (K := K) b m,
      ∀ H : GSt K np, GramFeasible (srcSignature K (Fin np)) H → ‖lamA χ b E e (J, H - J)‖ ≤ CA)
    {y : ProbedPath W np × ℝ} (hy : FeasPath b E s h τ m W V y) (e : GIdx K np) {T₁ : ℝ}
    {u : ℝ≥0} (hu : (u : ℝ) ≤ T₁) :
    ‖genA χ b E s τ m (pG b E s h τ m W V) e u y‖ ≤ CA * T₁ := by
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) u)
    (f := fun r => lamA χ b E e (gramJ b s τ m r.toNNReal,
      gY b s τ m (pG b E s h τ m W V) r.toNNReal y)) (C := CA) measure_Ioc_lt_top fun r _ => by
    have := hCA e _ (gramJ_mem_jSet b s τ m r.toNNReal)
      (b3ClosedGramAt b E s h τ m W (limLenAll s W r.toNNReal) V y)
      (hy _ (closeLen_le_limLenAll _))
    rwa [← gY_pG] at this
  rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg u)] at hI
  exact hI.trans (mul_le_mul_of_nonneg_left hu hCA0)

theorem limLenAll_zero : limLenAll s W 0 = closeLen s W := by simp [limLenAll, closeLen]

theorem gramJ_zero (hτ : ∀ i, s < τ i) : gramJ (K := K) b s τ m 0 = 0 := by
  rw [gramJ_eq_sel]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : ¬ (τ i - s ≤ ((0 : ℝ≥0) : ℝ)) := by rw [NNReal.coe_zero]; linarith [hτ i]
  simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- **On the alive set, the state with the discrete jumps lies in a box.** -/
theorem zHat_mem_kBox {R CJ BA : ℝ} (hR : 0 ≤ R) (hCJ0 : 0 ≤ CJ) (hBA : 0 ≤ BA)
    (hCJ : ∀ J ∈ jSet (K := K) b m, ∀ e, ‖gramEntry e J‖ ≤ CJ) {y : ProbedPath W np × ℝ}
    (hy : FeasPath b E s h τ m W V y) {j : ℕ} (hA : y ∈ b3Alive b E s h τ m R W j V)
    {u : ℝ≥0} (hu : limLenAll s W u ≤ j)
    (hα : ∀ e, ‖genA χ b E s τ m (pG b E s h τ m W V) e u y‖ ≤ BA) :
    zHat χ b E s h τ m W V u y ∈ kBox (2 * (2 * R + CJ) + BA) := by
  have hc := closeLen_le_limLenAll (s := s) (W := W) u
  have hG : ∀ n, closeLen s W ≤ n → n ≤ j → ∀ J ∈ jSet (K := K) b m, ∀ e,
      ‖gramEntry e (b3ClosedGramAt b E s h τ m W n V y - J)‖ ≤ 2 * R + CJ := by
    intro n h1 h2 J hJ e
    rw [gramEntry_sub']
    have a1 := ModelExist.norm_gramEntry_le_of_feasible (hy n h1) e
    have a2 := hA.2 n h1 h2
    exact (norm_sub_le _ _).trans (add_le_add (a1.trans (by linarith)) (hCJ J hJ e))
  have hRC : 0 ≤ 2 * R + CJ := by linarith
  have hy1 := hG (limLenAll s W u) hc hu (b3JumpAt b s τ m W (limLenAll s W u))
    (b3JumpAt_mem_jSet b s τ m W (limLenAll s W u))
  have hy0 := hG (limLenAll s W 0) (by rw [limLenAll_zero])
    (by rw [limLenAll_zero]; exact hc.trans hu) (gramJ b s τ m 0) (gramJ_mem_jSet b s τ m 0)
  rw [zHat_eq_stateOf]
  refine ⟨fun e => (hy1 e).trans (by linarith), fun e => ?_, fun e => (hy0 e).trans (by linarith)⟩
  simp only [stateOf]
  exact ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add (hy1 e) (hy0 e))) (hα e))).trans (by linarith)

end Process

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
