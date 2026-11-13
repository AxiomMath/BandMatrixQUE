module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalCell

/-!
# The prelimit generator process along one path

* `yHat n = G_n − J_n` (closed Gram state minus the discrete jumps `b3JumpAt`), and `zHat u`, the
  state `(Y, x, Y₀)` with the discrete jumps at the length `limLenAll s W u` and the cut drift
  `genA` of the prelimit process; **`stZ_eq_zHat`**: off a birth length, `stZ = zHat`;
* `aInt`, `lInt`: the integrands of `genA` and of the generator integral; they are integrable on
  every `Ioc 0 B` (`integrableOn_aInt`, `integrableOn_lInt`; bounded through finitely many
  lengths and jump values);
* **`genA_cell`**: on a cell without a birth, `genA(v) − genA(t_j) = (v − t_j) λ_j`;
* **`pM_sub`**: `pM v − pM u = F(stZ v) − F(stZ u) − ∫_{(u,v]} Λ`.
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

/-- `Ŷ_n = G_n − J_n` with the discrete jumps. -/
def yHat (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    GSt K np :=
  b3ClosedGramAt b E s h τ m W n V y - b3JumpAt b s τ m W n

/-- The initial state `Y₀` of the prelimit process. -/
abbrev y0P (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    GSt K np :=
  gY b s τ m (pG b E s h τ m W V) 0 y

/-- **The state with the discrete jumps** at model time `u`. -/
def zHat (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (u : ℝ≥0)
    (y : ProbedPath W np × ℝ) : ZSt K np :=
  (yHat b E s h τ m W (limLenAll s W u) V y,
    fun e => gramEntry e (yHat b E s h τ m W (limLenAll s W u) V y) -
      gramEntry e (y0P b E s h τ m W V y) - genA χ b E s τ m (pG b E s h τ m W V) e u y,
    y0P b E s h τ m W V y)

/-- The integrand of `genA`. -/
def aInt (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (e : GIdx K np)
    (y : ProbedPath W np × ℝ) (r : ℝ) : ℂ :=
  lamA χ b E e (gramJ b s τ m r.toNNReal, gY b s τ m (pG b E s h τ m W V) r.toNNReal y)

/-- The integrand of the generator integral. -/
def lInt (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Λ : GSt K np × ZSt K np → ℂ) (y : ProbedPath W np × ℝ) (r : ℝ) : ℂ :=
  Λ (gramJ b s τ m r.toNNReal, stZ χ b E s τ m (pG b E s h τ m W V) r.toNNReal y)

section Path

variable {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

theorem gY_pG (u : ℝ≥0) (y : ProbedPath W np × ℝ) :
    gY b s τ m (pG b E s h τ m W V) u y =
      b3ClosedGramAt b E s h τ m W (limLenAll s W u) V y - gramJ b s τ m u := rfl

/-- **Off a birth length, the state is the state with the discrete jumps.** -/
theorem stZ_eq_zHat (hτ : ∀ i, s < τ i) (hW : 1 ≤ W) {u : ℝ≥0}
    (hnb : ¬ IsBirthStep τ W (limLenAll s W u)) (y : ProbedPath W np × ℝ) :
    stZ χ b E s τ m (pG b E s h τ m W V) u y = zHat χ b E s h τ m W V u y := by
  have hJ := gramJ_eq_b3JumpAt (K := K) (b := b) (m := m) hτ hW hnb
  simp only [stZ, zHat, genX, gY_pG u, hJ, yHat]

/-- Integrability from a bound and measurability on `Ioc 0 B`. -/
theorem integrableOn_Ioc_of_bound {f : ℝ → ℂ} (hf : StronglyMeasurable f) (B C : ℝ)
    (hC : ∀ r ∈ Ioc (0 : ℝ) B, ‖f r‖ ≤ C) : IntegrableOn f (Ioc (0 : ℝ) B) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) B)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  exact Integrable.of_bound hf.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hC))

theorem setIntegral_Ioc_sub {f : ℝ → ℂ} {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hf : IntegrableOn f (Ioc (0 : ℝ) v)) :
    (∫ r in Ioc (0 : ℝ) v, f r) - ∫ r in Ioc (0 : ℝ) u, f r = ∫ r in Ioc u v, f r := by
  rw [← Ioc_union_Ioc_eq_Ioc hu huv, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
    measurableSet_Ioc (hf.mono_set (Ioc_subset_Ioc_right huv))
    (hf.mono_set (Ioc_subset_Ioc_left hu))]
  ring

variable (hV : Measurable V)
include hV

theorem sm_aInt (hχ : Continuous χ) (e : GIdx K np) (y : ProbedPath W np × ℝ) :
    StronglyMeasurable (aInt χ b E s h τ m W V e y) := by
  have hG : StronglyMeasurable (Function.uncurry (pG b E s h τ m W V)) := sm_pG hV
  have hY : StronglyMeasurable fun p : ℝ × (ProbedPath W np × ℝ) =>
      gY b s τ m (pG b E s h τ m W V) p.1.toNNReal p.2 := sm_gY_toNNReal hG
  have hJ : StronglyMeasurable fun p : ℝ × (ProbedPath W np × ℝ) =>
      gramJ (K := K) b s τ m p.1.toNNReal :=
    (sm_gramJ (K := K) b s τ m).comp_measurable (measurable_real_toNNReal.comp measurable_fst)
  have hj : StronglyMeasurable fun p : ℝ × (ProbedPath W np × ℝ) =>
      lamA χ b E e (gramJ b s τ m p.1.toNNReal, gY b s τ m (pG b E s h τ m W V) p.1.toNNReal p.2) :=
    (continuous_lamA' hχ b E e).comp_stronglyMeasurable (hJ.prodMk hY)
  have hc : Measurable fun r : ℝ => (r, y) := measurable_id.prodMk measurable_const
  have := hj.comp_measurable hc
  rw [Function.comp_def] at this
  unfold aInt
  exact this

theorem sm_lInt (hχ : Continuous χ) {Λ : GSt K np × ZSt K np → ℂ} (hΛ : Continuous Λ)
    (y : ProbedPath W np × ℝ) : StronglyMeasurable (lInt χ b E s h τ m W V Λ y) := by
  have hG : StronglyMeasurable (Function.uncurry (pG b E s h τ m W V)) := sm_pG hV
  have hZ : StronglyMeasurable fun p : ℝ × (ProbedPath W np × ℝ) =>
      stZ χ b E s τ m (pG b E s h τ m W V) p.1.toNNReal p.2 := by
    have := (sm_stZ (b := b) (E := E) (s := s) (τ := τ) (m := m) hG hχ).comp_measurable
      (measurable_real_toNNReal.prodMap measurable_id)
    rw [Function.comp_def] at this
    exact this
  have hJ : StronglyMeasurable fun p : ℝ × (ProbedPath W np × ℝ) =>
      gramJ (K := K) b s τ m p.1.toNNReal :=
    (sm_gramJ (K := K) b s τ m).comp_measurable (measurable_real_toNNReal.comp measurable_fst)
  have hj : StronglyMeasurable fun p : ℝ × (ProbedPath W np × ℝ) =>
      Λ (gramJ b s τ m p.1.toNNReal, stZ χ b E s τ m (pG b E s h τ m W V) p.1.toNNReal p.2) :=
    hΛ.comp_stronglyMeasurable (hJ.prodMk hZ)
  have hc : Measurable fun r : ℝ => (r, y) := measurable_id.prodMk measurable_const
  have := hj.comp_measurable hc
  rw [Function.comp_def] at this
  unfold lInt
  exact this

omit hV in
/-- The values along a path on `[0, B]` lie in a finite set of lengths and jump values. -/
theorem exists_bound_jump_len (y : ProbedPath W np × ℝ) (B : ℝ)
    (f : GSt K np × GSt K np → ℂ) :
    ∃ C : ℝ, ∀ r ∈ Ioc (0 : ℝ) B,
      ‖f (gramJ b s τ m r.toNNReal, gY b s τ m (pG b E s h τ m W V) r.toNNReal y)‖ ≤ C := by
  classical
  set S := (finite_range_gramJ (K := K) b s τ m).toFinset
  set N := limLenAll s W B.toNNReal
  refine ⟨∑ J ∈ S, ∑ n ∈ Finset.range (N + 1),
    ‖f (J, b3ClosedGramAt b E s h τ m W n V y - J)‖, fun r hr => ?_⟩
  have hJ : gramJ b s τ m r.toNNReal ∈ S := by simp [S]
  have hn : limLenAll s W r.toNNReal ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.floor_mono (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg W))
    have := Real.toNNReal_le_toNNReal hr.2
    have h2 : ((r.toNNReal : ℝ≥0) : ℝ) ≤ (B.toNNReal : ℝ) := this
    linarith
  rw [gY_pG]
  refine (Finset.single_le_sum (f := fun n => ‖f (gramJ b s τ m r.toNNReal,
      b3ClosedGramAt b E s h τ m W n V y - gramJ b s τ m r.toNNReal)‖)
    (fun _ _ => norm_nonneg _) hn).trans ?_
  exact Finset.single_le_sum (f := fun J => ∑ n ∈ Finset.range (N + 1),
      ‖f (J, b3ClosedGramAt b E s h τ m W n V y - J)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hJ

theorem integrableOn_aInt (hχ : Continuous χ) (e : GIdx K np)
    (y : ProbedPath W np × ℝ) (B : ℝ) :
    IntegrableOn (aInt χ b E s h τ m W V e y) (Ioc (0 : ℝ) B) := by
  obtain ⟨C, hC⟩ := exists_bound_jump_len (b := b) (E := E) (h := h) (τ := τ) (m := m) (V := V)
    y B (lamA χ b E e)
  exact integrableOn_Ioc_of_bound (sm_aInt hV hχ e y) B C hC

theorem genA_sub (hχ : Continuous χ) (e : GIdx K np) (y : ProbedPath W np × ℝ)
    {u v : ℝ≥0} (huv : u ≤ v) :
    genA χ b E s τ m (pG b E s h τ m W V) e v y - genA χ b E s τ m (pG b E s h τ m W V) e u y =
      ∫ r in Ioc (u : ℝ) v, aInt χ b E s h τ m W V e y r :=
  setIntegral_Ioc_sub (NNReal.coe_nonneg u) (NNReal.coe_le_coe.2 huv)
    (integrableOn_aInt (b := b) (E := E) (h := h) (τ := τ) (m := m) hV hχ e y v)

/-- **The cut drift on a cell without a birth.** -/
theorem genA_cell (hχ : Continuous χ) (hs : 0 ≤ s) (hτ : ∀ i, s < τ i) (hW : 1 ≤ W)
    {a t : ℝ≥0} {j : ℕ} (hpj : limLenAll s W a ≤ j) (hjq : j ≤ limLenAll s W t)
    (hnb : ¬ IsBirthStep τ W j) (e : GIdx K np) (y : ProbedPath W np × ℝ) {v : ℝ≥0}
    (h1 : cellT s W a t j ≤ v) (h2 : v ≤ cellT s W a t (j + 1)) :
    genA χ b E s τ m (pG b E s h τ m W V) e v y -
        genA χ b E s τ m (pG b E s h τ m W V) e (cellT s W a t j) y =
      (((v : ℝ) - cellT s W a t j : ℝ) : ℂ) *
        lamA χ b E e (b3JumpAt b s τ m W j, yHat b E s h τ m W j V y) := by
  rw [genA_sub hV hχ e y h1, integral_Ioc_eq_integral_Ioo]
  have hc : EqOn (aInt χ b E s h τ m W V e y) (fun _ => lamA χ b E e
      (b3JumpAt b s τ m W j, yHat b E s h τ m W j V y)) (Ioo (cellT s W a t j : ℝ) v) := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt (cellT s W a t j).2 hr.1
    have hcr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr0.le
    have hl1 : cellT s W a t j ≤ r.toNNReal := by
      rw [← NNReal.coe_le_coe, hcr]; exact hr.1.le
    have hl2 : r.toNNReal < cellT s W a t (j + 1) := by
      rw [← NNReal.coe_lt_coe, hcr]; exact lt_of_lt_of_le hr.2 h2
    have hL := limLenAll_of_cell hs hW hpj hjq hl1 hl2
    have hJ := gramJ_eq_b3JumpAt (K := K) (b := b) (m := m) hτ hW (hL ▸ hnb)
    simp only [aInt, gY_pG, hJ, hL, yHat]
  rw [setIntegral_congr_fun measurableSet_Ioo hc, setIntegral_const, Real.volume_real_Ioo,
    max_eq_left (sub_nonneg.2 (by exact_mod_cast h1)), Complex.real_smul]

theorem integrableOn_lInt (hχ : Continuous χ) {Λ : GSt K np × ZSt K np → ℂ}
    (hΛ : Continuous Λ) (y : ProbedPath W np × ℝ) (B : ℝ) :
    IntegrableOn (lInt χ b E s h τ m W V Λ y) (Ioc (0 : ℝ) B) := by
  classical
  -- bound of the cut drift
  have hA : ∀ e : GIdx K np, ∃ CA : ℝ, 0 ≤ CA ∧ ∀ r ∈ Ioc (0 : ℝ) B,
      ‖genA χ b E s τ m (pG b E s h τ m W V) e r.toNNReal y‖ ≤ CA := fun e => by
    obtain ⟨C, hC⟩ := exists_bound_jump_len (b := b) (E := E) (h := h) (τ := τ) (m := m)
      (V := V) y B (lamA χ b E e)
    refine ⟨max C 0 * max B 0, by positivity, fun r hr => ?_⟩
    have hI := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Ioc (0 : ℝ) (r.toNNReal : ℝ)) (f := aInt χ b E s h τ m W V e y) (C := max C 0)
      measure_Ioc_lt_top fun w hw =>
        (hC w ⟨hw.1, hw.2.trans (by rw [Real.coe_toNNReal _ hr.1.le]; exact hr.2)⟩).trans
          (le_max_left _ _)
    rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg _)] at hI
    calc ‖genA χ b E s τ m (pG b E s h τ m W V) e r.toNNReal y‖
        = ‖∫ w in Ioc (0 : ℝ) (r.toNNReal : ℝ), aInt χ b E s h τ m W V e y w‖ := rfl
      _ ≤ max C 0 * (r.toNNReal : ℝ) := hI
      _ ≤ max C 0 * max B 0 := mul_le_mul_of_nonneg_left (by
          rw [Real.coe_toNNReal _ hr.1.le]; exact hr.2.trans (le_max_left _ _)) (le_max_right _ _)
  choose CA hCA0 hCA using hA
  set BX := ∑ e, CA e
  -- the generator through the finitely many lengths and jumps, and a bounded drift
  set N := limLenAll s W B.toNNReal
  set Y0 := y0P b E s h τ m W V y
  set Φ : (GSt K np × ℕ) × (GIdx K np → ℂ) → ℂ := fun q => Λ (q.1.1,
    (b3ClosedGramAt b E s h τ m W q.1.2 V y - q.1.1,
      fun e => gramEntry e (b3ClosedGramAt b E s h τ m W q.1.2 V y - q.1.1) - gramEntry e Y0 -
        q.2 e, Y0))
  have hΦ : Continuous Φ := by
    have hg : Continuous fun n : ℕ => b3ClosedGramAt b E s h τ m W n V y :=
      continuous_of_discreteTopology
    have hgq : Continuous fun q : (GSt K np × ℕ) × (GIdx K np → ℂ) =>
        b3ClosedGramAt b E s h τ m W q.1.2 V y := hg.comp (continuous_snd.comp continuous_fst)
    refine hΛ.comp ((continuous_fst.comp continuous_fst).prodMk ((hgq.sub
      (continuous_fst.comp continuous_fst)).prodMk ((continuous_pi fun e =>
        (((ClosedLimit.continuous_gramEntry e).comp (hgq.sub
          (continuous_fst.comp continuous_fst))).sub continuous_const).sub
        ((continuous_apply e).comp continuous_snd)).prodMk continuous_const)))
  have hS : ((Set.range fun t : ℝ≥0 => gramJ (K := K) b s τ m t) ×ˢ
      (↑(Finset.range (N + 1)) : Set ℕ)).Finite :=
    (finite_range_gramJ b s τ m).prod (Finset.finite_toSet _)
  obtain ⟨C, hC⟩ := exists_bound_finite_compact hΦ hS
    (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) BX)
  refine integrableOn_Ioc_of_bound (sm_lInt hV hχ hΛ y) B C fun r hr => ?_
  have hn : limLenAll s W r.toNNReal ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.floor_mono (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg W))
    have h2 : ((r.toNNReal : ℝ≥0) : ℝ) ≤ (B.toNNReal : ℝ) := Real.toNNReal_le_toNNReal hr.2
    linarith
  have := hC (gramJ b s τ m r.toNNReal, limLenAll s W r.toNNReal) ⟨⟨_, rfl⟩, hn⟩
    (fun e => genA χ b E s τ m (pG b E s h τ m W V) e r.toNNReal y) fun e _ => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hCA e r hr).trans (Finset.single_le_sum (f := CA) (fun e _ => hCA0 e)
        (Finset.mem_univ e))
  exact this

/-- **The increment of the prelimit generator process.** -/
theorem pM_sub (hχ : Continuous χ) {F : ZSt K np → ℂ}
    {Λ : GSt K np × ZSt K np → ℂ} (hΛ : Continuous Λ) (y : ProbedPath W np × ℝ) {u v : ℝ≥0}
    (huv : u ≤ v) :
    pM χ b E s h τ m W V F Λ v y - pM χ b E s h τ m W V F Λ u y =
      F (stZ χ b E s τ m (pG b E s h τ m W V) v y) -
        F (stZ χ b E s τ m (pG b E s h τ m W V) u y) -
        ∫ r in Ioc (u : ℝ) v, lInt χ b E s h τ m W V Λ y r := by
  have key := setIntegral_Ioc_sub (NNReal.coe_nonneg u) (NNReal.coe_le_coe.2 huv)
    (integrableOn_lInt (b := b) (E := E) (s := s)
    (h := h) (τ := τ) (m := m) hV hχ hΛ y v)
  simp only [lInt] at key
  simp only [pM, genProc, lInt]
  linear_combination -key

end Path

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
