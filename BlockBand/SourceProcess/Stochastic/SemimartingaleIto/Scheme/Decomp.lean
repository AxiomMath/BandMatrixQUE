module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Scheme.Hyp
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Taylor scheme with integral bounds: decomposition and Riemann limit)

* `tendsto_riemann_int`: `Σ_k G(t_k) ∫_{t_k}^{t_{k+1}} f → ∫_a^b G f` for `G` continuous on
  `[a, b]` and `f` merely interval integrable (no pointwise bound);
* on `IGood` (fixed `s ≤ t`): the exact decomposition `schemeProc_sub_eq'`
  `X_t - X_s = T¹_n + ½ T²_n + (Riemann_n - ∫_s^t 𝓛φ) + ½ Cross_n + Rem_n`, the Riemann limit
  `tendsto_riemannSum'`, and the bounds `abs_riemannSum_le'`, `abs_integral_gen_le'` in terms of
  the control.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

/-- **Riemann sums against an integrable weight** (no bound on the weight). -/
theorem tendsto_riemann_int {a b : ℝ} (hab : a ≤ b) {G f : ℝ → ℝ} (hG : ContinuousOn G (Icc a b))
    (hf : IntervalIntegrable f volume a b) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
        G (rgrid a b n k) * ∫ u in rgrid a b n k..rgrid a b n (k + 1), f u)
      atTop (𝓝 (∫ u in a..b, G u * f u)) := by
  have hsub : ∀ n, ∀ k < n + 1, uIcc (rgrid a b n k) (rgrid a b n (k + 1)) ⊆ uIcc a b := by
    intro n k hk
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc (rgrid_mem hab n hk.le) (rgrid_mem hab n (Nat.succ_le_of_lt hk))
  have hint : ∀ n, ∀ k < n + 1, IntervalIntegrable (fun u => G u * f u) volume
      (rgrid a b n k) (rgrid a b n (k + 1)) := fun n k hk =>
    (hf.mono_set (hsub n k hk)).continuousOn_mul
      (hG.mono (by rw [← uIcc_of_le hab]; exact hsub n k hk))
  have hintA : ∀ n, ∀ k < n + 1, IntervalIntegrable (fun u => |f u|) volume
      (rgrid a b n k) (rgrid a b n (k + 1)) := fun n k hk => (hf.mono_set (hsub n k hk)).abs
  have hsplit : ∀ n, ∫ u in a..b, G u * f u = ∑ k ∈ Finset.range (n + 1),
      ∫ u in rgrid a b n k..rgrid a b n (k + 1), G u * f u := by
    intro n
    rw [intervalIntegral.sum_integral_adjacent_intervals (hint n), rgrid_zero, rgrid_last]
  have hsplitA : ∀ n, ∫ u in a..b, |f u| = ∑ k ∈ Finset.range (n + 1),
      ∫ u in rgrid a b n k..rgrid a b n (k + 1), |f u| := by
    intro n
    rw [intervalIntegral.sum_integral_adjacent_intervals (hintA n), rgrid_zero, rgrid_last]
  set F := ∫ u in a..b, |f u|
  have hF : 0 ≤ F := intervalIntegral.integral_nonneg hab fun _ _ => abs_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (2 * (F + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_mesh_le hab hG hη)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, hsplit n, ← Finset.sum_sub_distrib]
  have hcell : ∀ k ∈ Finset.range (n + 1),
      |G (rgrid a b n k) * (∫ u in rgrid a b n k..rgrid a b n (k + 1), f u) -
        ∫ u in rgrid a b n k..rgrid a b n (k + 1), G u * f u| ≤
        η * ∫ u in rgrid a b n k..rgrid a b n (k + 1), |f u| := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hfi : IntervalIntegrable f volume (rgrid a b n k) (rgrid a b n (k + 1)) :=
      hf.mono_set (hsub n k hk')
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hfi.const_mul _) (hint n k hk'), ← intervalIntegral.integral_const_mul]
    have hle : rgrid a b n k ≤ rgrid a b n (k + 1) := rgrid_mono hab n (Nat.le_succ k)
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hle (ae_of_all _ fun u hu => ?_)
      ((hintA n k hk').const_mul _)
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := hN n hn k hk' u ⟨hu.1.le, hu.2⟩
    rw [Real.dist_eq, abs_sub_comm] at h1
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans_lt ((Finset.sum_le_sum hcell).trans_lt ?_)
  rw [← Finset.mul_sum, ← hsplitA n, hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

variable {Ω : Type*} {d : ℕ} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {C : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0} {ω : Ω}

theorem IGood.ii_gen (hω : IGood K Z β α N B C s t ω) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => schemeGen φ Z β α u.toNNReal ω) volume a b := by
  unfold schemeGen
  refine IntervalIntegrable.add ?_ ?_
  · refine (intervalIntegrable_finsetSum (fun i _ => ?_))
    exact (hω.ii_β i a b).mul_continuousOn (continuous_dφ1_path hω.1 hU hKU hφ i).continuousOn
  · refine IntervalIntegrable.const_mul ?_ _
    refine intervalIntegrable_finsetSum (fun i _ => intervalIntegrable_finsetSum (fun j _ => ?_))
    exact (hω.ii_α i j a b).mul_continuousOn
      (continuous_dφ2_path hω.1 hU hKU hφ i j).continuousOn

/-- **Exact pathwise decomposition** of `X_t - X_s` along the grid. -/
theorem schemeProc_sub_eq' (hω : IGood K Z β α N B C s t ω) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) (n : ℕ) :
    schemeProc φ Z β α t ω - schemeProc φ Z β α s ω =
      transform1 φ Z N s t n ω + (1 / 2) * transform2 φ Z α N s t n ω +
      (riemannSum φ Z β α s t n ω - ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) +
      (1 / 2) * crossSum φ Z β N s t n ω + remSum φ Z s t n ω := by
  have hint := hω.ii_gen hU hKU hφ
  have hI : (∫ u in Ioc (0 : ℝ) t, schemeGen φ Z β α u.toNNReal ω) -
      ∫ u in Ioc (0 : ℝ) s, schemeGen φ Z β α u.toNNReal ω =
      ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω :=
    setIntegral_Ioc_sub hint (NNReal.coe_nonneg s) (by exact_mod_cast hst)
  have hφs : φ (Z t ω) - φ (Z s ω) = ∑ k ∈ Finset.range (n + 1),
      (φ (Z (grid s t n (k + 1)) ω) - φ (Z (grid s t n k) ω)) := by
    rw [Finset.sum_range_sub (fun k => φ (Z (grid s t n k) ω)), grid_last hst, grid_zero]
  have hstep : ∀ k ∈ Finset.range (n + 1),
      φ (Z (grid s t n (k + 1)) ω) - φ (Z (grid s t n k) ω) =
        ∑ i, dφ1 φ Z s t n i k ω * incN N s t n i k ω +
        (∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω +
          (1 / 2 : ℝ) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω) +
        (1 / 2) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω *
          (incN N s t n i k ω * incN N s t n j k ω - incJ α s t n i j k ω) +
        (1 / 2) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω *
          (incN N s t n i k ω * incI β s t n j k ω + incI β s t n i k ω * incN N s t n j k ω +
            incI β s t n i k ω * incI β s t n j k ω) +
        taylorRem φ (Z (grid s t n k) ω) (Z (grid s t n (k + 1)) ω) := by
    intro k _
    rw [taylor_split φ _ _ _ _ (incZ_eq hω.1 n k) (fun i j => incJ α s t n i j k ω)]
    simp only [dφ1, dφ2]
    ring
  have : schemeProc φ Z β α t ω - schemeProc φ Z β α s ω =
      (φ (Z t ω) - φ (Z s ω)) - ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω := by
    rw [← hI]; unfold schemeProc; ring
  rw [this, hφs, Finset.sum_congr rfl hstep]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, transform1, transform2, riemannSum,
    crossSum, remSum]
  ring

/-- **Riemann limit**: `Riemann_n → ∫_s^t 𝓛φ`. -/
theorem tendsto_riemannSum' (hω : IGood K Z β α N B C s t ω) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) :
    Tendsto (fun n => riemannSum φ Z β α s t n ω) atTop
      (𝓝 (∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω)) := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have h1 : ∀ i, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
      dφ1 φ Z s t n i k ω * incI β s t n i k ω) atTop
      (𝓝 (∫ u in (s : ℝ)..t, fderiv ℝ φ (Z u.toNNReal ω) (ev i) * β u.toNNReal ω i)) := by
    intro i
    refine (tendsto_riemann_int hst' (continuous_dφ1_path hω.1 hU hKU hφ i).continuousOn
      (hω.ii_β i _ _)).congr fun n => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hω.incI_eq' hst, dφ1, toNNReal_rgrid hst]
  have h2 : ∀ i j, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
      dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω) atTop
      (𝓝 (∫ u in (s : ℝ)..t, fderiv ℝ (fderiv ℝ φ) (Z u.toNNReal ω) (ev i) (ev j) *
        α u.toNNReal ω i j)) := by
    intro i j
    refine (tendsto_riemann_int hst' (continuous_dφ2_path hω.1 hU hKU hφ i j).continuousOn
      (hω.ii_α i j _ _)).congr fun n => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hω.incJ_eq' hst, dφ2, toNNReal_rgrid hst]
  have hlim := (tendsto_finsetSum Finset.univ (fun i _ => h1 i)).add
    ((tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ
      (fun j _ => h2 i j))).const_mul (1 / 2 : ℝ))
  have hR : ∀ n, riemannSum φ Z β α s t n ω =
      ∑ i, ∑ k ∈ Finset.range (n + 1), dφ1 φ Z s t n i k ω * incI β s t n i k ω +
      (1 / 2) * ∑ i, ∑ j, ∑ k ∈ Finset.range (n + 1),
        dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω := by
    intro n
    unfold riemannSum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hG : ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω =
      ∑ i, (∫ u in (s : ℝ)..t, fderiv ℝ φ (Z u.toNNReal ω) (ev i) * β u.toNNReal ω i) +
      (1 / 2) * ∑ i, ∑ j, ∫ u in (s : ℝ)..t,
        fderiv ℝ (fderiv ℝ φ) (Z u.toNNReal ω) (ev i) (ev j) * α u.toNNReal ω i j := by
    have i1 : ∀ i, IntervalIntegrable (fun u : ℝ => fderiv ℝ φ (Z u.toNNReal ω) (ev i) *
        β u.toNNReal ω i) volume s t := fun i =>
      (hω.ii_β i _ _).continuousOn_mul (continuous_dφ1_path hω.1 hU hKU hφ i).continuousOn
    have i2 : ∀ i j, IntervalIntegrable (fun u : ℝ =>
        fderiv ℝ (fderiv ℝ φ) (Z u.toNNReal ω) (ev i) (ev j) * α u.toNNReal ω i j)
        volume s t := fun i j =>
      (hω.ii_α i j _ _).continuousOn_mul (continuous_dφ2_path hω.1 hU hKU hφ i j).continuousOn
    unfold schemeGen
    simp_rw [mul_comm (β _ ω _), mul_comm (α _ ω _ _)]
    rw [intervalIntegral.integral_add (intervalIntegrable_finsetSum fun i _ => i1 i)
      ((intervalIntegrable_finsetSum fun i _ =>
        intervalIntegrable_finsetSum fun j _ => i2 i j).const_mul _),
      intervalIntegral.integral_finsetSum (fun i _ => i1 i), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun i _ => intervalIntegrable_finsetSum
        fun j _ => i2 i j)]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact intervalIntegral.integral_finsetSum (fun j _ => i2 i j)
  rw [hG]
  exact hlim.congr fun n => (hR n).symm

/-- Pointwise bound of the generator by the control. -/
theorem abs_schemeGen_le' {M₁ M₂ : ℝ} (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂)
    (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂)
    {u : ℝ≥0} (hZ : Z u ω ∈ K) :
    |schemeGen φ Z β α u ω| ≤ (M₁ + M₂) * ctrl β α u ω := by
  unfold schemeGen ctrl
  refine (abs_add_le _ _).trans ?_
  have s1 : |∑ i, β u ω i * fderiv ℝ φ (Z u ω) (ev i)| ≤ M₁ * ∑ i, |β u ω i| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((abs_clm_ev_le _ i).trans (hM₁ _ hZ)) (abs_nonneg _)
  have s2 : |(1 / 2 : ℝ) * ∑ i, ∑ j, α u ω i j * fderiv ℝ (fderiv ℝ φ) (Z u ω) (ev i) (ev j)| ≤
      M₂ * ∑ i, ∑ j, |α u ω i j| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : |∑ i, ∑ j, α u ω i j * fderiv ℝ (fderiv ℝ φ) (Z u ω) (ev i) (ev j)| ≤
        M₂ * ∑ i, ∑ j, |α u ω i j| := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((abs_bilin_ev_le _ i j).trans (hM₂ _ hZ)) (abs_nonneg _)
    have h0 : 0 ≤ |∑ i, ∑ j, α u ω i j * fderiv ℝ (fderiv ℝ φ) (Z u ω) (ev i) (ev j)| :=
      abs_nonneg _
    linarith
  have hb : 0 ≤ ∑ i, |β u ω i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha : 0 ≤ ∑ i, ∑ j, |α u ω i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith

/-- Pathwise bound on `∫_a^b 𝓛φ` by the control. -/
theorem IGood.abs_integral_gen_le' (hω : IGood K Z β α N B C s t ω) {a b : ℝ≥0} (hab : a ≤ b)
    {M₁ M₂ : ℝ} (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁)
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) :
    |∫ u in (a : ℝ)..b, schemeGen φ Z β α u.toNNReal ω| ≤ (M₁ + M₂) * C := by
  refine (abs_intervalIntegral_le_of_abs_le (by exact_mod_cast hab)
    ((hω.ii_ctrl _ _).const_mul (M₁ + M₂))
    fun u => abs_schemeGen_le' hM₁0 hM₂0 hM₁ hM₂ (hω.1.1 _)).trans ?_
  rw [intervalIntegral.integral_const_mul, ← hω.ctrlI_sub hab]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith [hω.2.2 b, ctrlI_nonneg (β := β) (α := α) a ω]

/-- Pathwise bound on the Riemann sums by the control. -/
theorem IGood.abs_riemannSum_le' (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) {M₁ M₂ : ℝ}
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂) (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁)
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) (n : ℕ) :
    |riemannSum φ Z β α s t n ω| ≤ (d * M₁ + d * d * M₂) * C := by
  have hcell : ∀ k, |∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω +
      (1 / 2 : ℝ) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω| ≤
      (d * M₁ + d * d * M₂) * incG β α s t n k ω := by
    intro k
    have hZ := hω.1.1 (grid s t n k)
    have hg := hω.incG_nonneg hst n k
    have b1 : ∀ i, |dφ1 φ Z s t n i k ω * incI β s t n i k ω| ≤ M₁ * incG β α s t n k ω :=
      fun i => by
        rw [abs_mul]
        exact mul_le_mul ((abs_clm_ev_le _ i).trans (hM₁ _ hZ)) (hω.abs_incI_le' hst n i k)
          (abs_nonneg _) hM₁0
    have b2 : ∀ i j, |dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω| ≤
        M₂ * incG β α s t n k ω := fun i j => by
      rw [abs_mul]
      exact mul_le_mul ((abs_bilin_ev_le _ i j).trans (hM₂ _ hZ)) (hω.abs_incJ_le' hst n i j k)
        (abs_nonneg _) hM₂0
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have s1 : |∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω| ≤ d * (M₁ * incG β α s t n k ω) :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => b1 i).trans
        (by simp))
    have s2 : |∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω| ≤
        d * (d * (M₂ * incG β α s t n k ω)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => b2 i j)).trans
          (by simp))
    have : 0 ≤ d * (d * (M₂ * incG β α s t n k ω)) := by positivity
    nlinarith
  unfold riemannSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hcell k).trans ?_)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hω.sum_incG_le hst n) (by positivity)

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
