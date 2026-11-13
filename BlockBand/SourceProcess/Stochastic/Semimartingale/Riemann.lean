module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Instances.NNReal.Lemmas
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Uniform grids, mesh moduli and Riemann sums

Deterministic. The uniform grid of `[a, b]` with `n + 1` steps is
`rgrid a b n k = a + k (b - a)/(n + 1)` (real) and `grid s t n k` (in `ℝ≥0`, same points).

* `eventually_mesh_le`: for a path continuous on `[a, b]` (values in a pseudo-metric space),
  eventually in `n` every oscillation over a grid cell is `≤ δ`.
* `tendsto_riemann`: `∑_k G(t_k) ∫_{t_k}^{t_{k+1}} f → ∫_a^b G f` for `G` continuous on
  `[a, b]` and `f` interval-integrable and bounded on `[a, b]`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open Set Filter Topology Metric MeasureTheory
open scoped NNReal

/-- Real uniform grid of `[a, b]` with `n + 1` steps. -/
def rgrid (a b : ℝ) (n k : ℕ) : ℝ := a + k * ((b - a) / (n + 1))

/-- `ℝ≥0` uniform grid of `[s, t]` with `n + 1` steps. -/
def grid (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 := s + (k : ℝ≥0) * ((t - s) / (n + 1))

theorem coe_grid {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) :
    (grid s t n k : ℝ) = rgrid s t n k := by
  simp [grid, rgrid, NNReal.coe_sub hst]

theorem rgrid_zero (a b : ℝ) (n : ℕ) : rgrid a b n 0 = a := by simp [rgrid]

theorem rgrid_last (a b : ℝ) (n : ℕ) : rgrid a b n (n + 1) = b := by
  simp only [rgrid]; push_cast; field_simp; ring

theorem rgrid_succ (a b : ℝ) (n k : ℕ) :
    rgrid a b n (k + 1) = rgrid a b n k + (b - a) / (n + 1) := by
  simp only [rgrid]; push_cast; ring

theorem rgrid_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) : Monotone (rgrid a b n) := by
  intro j k hjk
  simp only [rgrid]
  have : 0 ≤ (b - a) / (n + 1) := div_nonneg (by linarith) (by positivity)
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  nlinarith

theorem rgrid_mem {a b : ℝ} (hab : a ≤ b) (n : ℕ) {k : ℕ} (hk : k ≤ n + 1) :
    rgrid a b n k ∈ Icc a b := by
  refine ⟨?_, ?_⟩
  · simpa [rgrid_zero] using rgrid_mono hab n (Nat.zero_le k)
  · simpa [rgrid_last] using rgrid_mono hab n hk

theorem grid_zero (s t : ℝ≥0) (n : ℕ) : grid s t n 0 = s := by simp [grid]

theorem grid_last {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) : grid s t n (n + 1) = t := by
  apply NNReal.coe_injective; rw [coe_grid hst, rgrid_last]

theorem grid_mono {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) : Monotone (grid s t n) := by
  intro j k hjk
  have := rgrid_mono (a := s) (b := t) (by exact_mod_cast hst) n hjk
  rw [← coe_grid hst, ← coe_grid hst] at this
  exact_mod_cast this

theorem tendsto_mesh (a b : ℝ) : Tendsto (fun n : ℕ => (b - a) / (n + 1)) atTop (𝓝 0) := by
  have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (b - a)
  simp only [mul_zero] at this
  refine this.congr fun n => ?_
  ring

/-- Eventually every grid cell has oscillation `≤ δ`. -/
theorem eventually_mesh_le {F : Type*} [PseudoMetricSpace F] {a b : ℝ} (hab : a ≤ b)
    {z : ℝ → F} (hz : ContinuousOn z (Icc a b)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ k < n + 1, ∀ u ∈ Icc (rgrid a b n k) (rgrid a b n (k + 1)),
      dist (z u) (z (rgrid a b n k)) ≤ δ := by
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuousOn_iff_le.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hz) δ hδ
  filter_upwards [(tendsto_mesh a b).eventually (ge_mem_nhds hη)] with n hn k hk u hu'
  have hk1 := rgrid_mem hab n (Nat.succ_le_of_lt hk)
  have hk0 := rgrid_mem hab n hk.le
  refine hu u ⟨hk0.1.trans hu'.1, hu'.2.trans hk1.2⟩ _ hk0 ?_
  rw [Real.dist_eq, abs_of_nonneg (by linarith [hu'.1])]
  have := rgrid_succ a b n k
  linarith [hu'.2]

/-- **Riemann sums against an integrable weight.** -/
theorem tendsto_riemann {a b : ℝ} (hab : a ≤ b) {G f : ℝ → ℝ} (hG : ContinuousOn G (Icc a b))
    (hf : IntervalIntegrable f volume a b) {C : ℝ} (hfC : ∀ u ∈ Icc a b, |f u| ≤ C) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
        G (rgrid a b n k) * ∫ u in rgrid a b n k..rgrid a b n (k + 1), f u)
      atTop (𝓝 (∫ u in a..b, G u * f u)) := by
  have hint : ∀ n, ∀ k < n + 1, IntervalIntegrable (fun u => G u * f u) volume
      (rgrid a b n k) (rgrid a b n (k + 1)) := by
    intro n k hk
    have hsub : uIcc (rgrid a b n k) (rgrid a b n (k + 1)) ⊆ uIcc a b := by
      rw [uIcc_of_le hab]
      exact uIcc_subset_Icc (rgrid_mem hab n hk.le) (rgrid_mem hab n (Nat.succ_le_of_lt hk))
    exact (hf.mono_set hsub).continuousOn_mul (hG.mono (by rw [← uIcc_of_le hab]; exact hsub))
  have hsplit : ∀ n, ∫ u in a..b, G u * f u = ∑ k ∈ Finset.range (n + 1),
      ∫ u in rgrid a b n k..rgrid a b n (k + 1), G u * f u := by
    intro n
    rw [intervalIntegral.sum_integral_adjacent_intervals (hint n), rgrid_zero, rgrid_last]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hfC a ⟨le_rfl, hab⟩)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (2 * (C + 1) * (b - a + 1)) with hηdef
  have hη : 0 < η := by rw [hηdef]; have : 0 ≤ b - a := by linarith
                        positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_mesh_le hab hG hη)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, hsplit n, ← Finset.sum_sub_distrib]
  have hcell : ∀ k ∈ Finset.range (n + 1),
      |G (rgrid a b n k) * (∫ u in rgrid a b n k..rgrid a b n (k + 1), f u) -
        ∫ u in rgrid a b n k..rgrid a b n (k + 1), G u * f u| ≤ η * C * ((b - a) / (n + 1)) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hfi : IntervalIntegrable f volume (rgrid a b n k) (rgrid a b n (k + 1)) := by
      refine hf.mono_set ?_
      rw [uIcc_of_le hab]
      exact uIcc_subset_Icc (rgrid_mem hab n hk'.le) (rgrid_mem hab n (Nat.succ_le_of_lt hk'))
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hfi.const_mul _) (hint n k hk')]
    have hle : rgrid a b n k ≤ rgrid a b n (k + 1) := rgrid_mono hab n (Nat.le_succ k)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (E := ℝ) (C := η * C) ?_).trans ?_
    · intro u hu
      rw [uIoc_of_le hle] at hu
      have hu' : u ∈ Icc a b :=
        ⟨(rgrid_mem hab n hk'.le).1.trans hu.1.le, hu.2.trans (rgrid_mem hab n
          (Nat.succ_le_of_lt hk')).2⟩
      rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := hN n hn k hk' u ⟨hu.1.le, hu.2⟩
      rw [Real.dist_eq, abs_sub_comm] at h1
      exact mul_le_mul h1 (hfC u hu') (abs_nonneg _) hη.le
    · rw [abs_of_nonneg (by linarith), rgrid_succ]
      apply le_of_eq; ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans_lt ((Finset.sum_le_sum hcell).trans_lt ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hba : 0 ≤ b - a := by linarith
  have : ((n : ℝ) + 1) * (η * C * ((b - a) / (n + 1))) = η * C * (b - a) := by
    field_simp
  push_cast
  rw [this, hηdef]
  have hpos : 0 < 2 * (C + 1) * (b - a + 1) := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hpos]
  nlinarith [mul_nonneg hC hba]

end BlockBand.SourceProcess.Stochastic.Semimartingale
