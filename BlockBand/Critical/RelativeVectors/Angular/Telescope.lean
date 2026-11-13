module

public import BlockBand.Critical.RelativeVectors.Angular.Grid
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Riemann telescoping in time (deterministic)

A step of the space-time argument. One fixed path: `h, ht : ℝ → E → ℝ` (a test and its time
derivative), `φ : ℝ → E` (the array path, possibly discontinuous), `a v x` (the generator of
`h(v, ·)` at time `x`). For the grid of `[0, u]` with `K` cells, stopped at `t ∈ [0, u]`, the
grid sum

`S_K = Σ_k [h(p_{k+1}, φ(μ_{k+1})) - h(p_{k+1}, φ(μ_k)) - ∫_{μ_k}^{μ_{k+1}} a(p_{k+1}, x) dx]`

(the sum of the fixed-time martingale brackets of the test `h(p_{k+1}, ·)` on the cells)
converges to `h(t, φ t) - h(0, φ 0) - ∫_0^t (ht(x, φ x) + a(x, x)) dx`
(`tendsto_gridSum`), and `|S_K| ≤ 6C + t (C_t + M_a)` (`abs_gridSum_le`).

Hypotheses (`IsTelescopeData`): `h` jointly continuous on `[0,T] × E`, `∂_v h = ht` on `(0,T)`,
`ht(·, z)` continuous on `(0,T)`, `|h| ≤ C`, `|ht| ≤ C_t` on `(0, t) × B_R`, `‖φ‖ ≤ R` on
`[0, t]`, `y ↦ ht(x, φ y)` continuous at each `x ∈ (0, t)` (supplied by phase invariance),
`a(v, ·)` measurable for `v ∈ [0,T]`, `|a| ≤ M_a` on `[0,T] × (0,t)`, `v ↦ a(v, x)` continuous
within `[0,T]` at `v = x`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- The hypotheses of the telescoping lemma. -/
structure IsTelescopeData (h ht : ℝ → E → ℝ) (a : ℝ → ℝ → ℝ) (φ : ℝ → E)
    (t u T C Ct Ma R : ℝ) : Prop where
  t_nonneg : 0 ≤ t
  t_le : t ≤ u
  u_le : u ≤ T
  cont : ContinuousOn (fun p : ℝ × E => h p.1 p.2) (Icc 0 T ×ˢ univ)
  deriv : ∀ z, ∀ v ∈ Ioo 0 T, HasDerivAt (fun v' => h v' z) (ht v z) v
  ht_cont : ∀ z, ContinuousOn (fun v => ht v z) (Ioo 0 T)
  bound : ∀ v ∈ Icc 0 T, ∀ z, |h v z| ≤ C
  ht_bound : ∀ v ∈ Ioo 0 t, ∀ z, ‖z‖ ≤ R → |ht v z| ≤ Ct
  phi_bound : ∀ x ∈ Icc 0 t, ‖φ x‖ ≤ R
  phi_cont : ∀ x ∈ Ioo 0 t, ContinuousAt (fun y => ht x (φ y)) x
  a_meas : ∀ v ∈ Icc 0 T, AEStronglyMeasurable (a v) (volume.restrict (Ioc 0 t))
  a_bound : ∀ v ∈ Icc 0 T, ∀ x ∈ Ioo 0 t, |a v x| ≤ Ma
  a_cont : ∀ x ∈ Ioo 0 t, ContinuousWithinAt (fun v => a v x) (Icc 0 T) x

/-- The grid sum of the fixed-time brackets. -/
def gridSum (h : ℝ → E → ℝ) (a : ℝ → ℝ → ℝ) (φ : ℝ → E) (t u : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (h (gridPt u K (k + 1)) (φ (gridMu t u K (k + 1))) -
    h (gridPt u K (k + 1)) (φ (gridMu t u K k)) -
    ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), a (gridPt u K (k + 1)) x)

/-- The error of the fixed time on the cell `k`. -/
def partialErr (h : ℝ → E → ℝ) (φ : ℝ → E) (t u : ℝ) (K k : ℕ) : ℝ :=
  (h (gridPt u K (k + 1)) (φ (gridMu t u K (k + 1))) -
      h (gridMu t u K (k + 1)) (φ (gridMu t u K (k + 1)))) -
    (h (gridPt u K (k + 1)) (φ (gridMu t u K k)) - h (gridMu t u K (k + 1)) (φ (gridMu t u K k)))

theorem integrableOn_Ioc_of_bound {f : ℝ → ℝ} {α β M : ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict (Ioo α β)))
    (hb : ∀ x ∈ Ioo α β, |f x| ≤ M) : IntegrableOn f (Ioc α β) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  refine Integrable.of_bound hm M ((ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall fun x hx => ?_))
  rw [Real.norm_eq_abs]; exact hb x hx

theorem restrict_Ioc_eq_Ioo (α β : ℝ) :
    (volume.restrict (Ioc α β) : Measure ℝ) = volume.restrict (Ioo α β) :=
  Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm

namespace IsTelescopeData

variable {h ht : ℝ → E → ℝ} {a : ℝ → ℝ → ℝ} {φ : ℝ → E} {t u T C Ct Ma R : ℝ}

theorem u_nonneg (D : IsTelescopeData h ht a φ t u T C Ct Ma R) : 0 ≤ u := D.t_nonneg.trans D.t_le

theorem t_le_T (D : IsTelescopeData h ht a φ t u T C Ct Ma R) : t ≤ T := D.t_le.trans D.u_le

theorem mu_mem (D : IsTelescopeData h ht a φ t u T C Ct Ma R) (K k : ℕ) :
    gridMu t u K k ∈ Icc 0 t := ⟨gridMu_nonneg D.t_nonneg D.u_nonneg k, gridMu_le k⟩

theorem mu_mem_T (D : IsTelescopeData h ht a φ t u T C Ct Ma R) (K k : ℕ) :
    gridMu t u K k ∈ Icc 0 T := ⟨(D.mu_mem K k).1, (D.mu_mem K k).2.trans D.t_le_T⟩

theorem pt_mem_T (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {K k : ℕ} (hK : K ≠ 0)
    (hk : k ≤ K) : gridPt u K k ∈ Icc 0 T :=
  ⟨gridPt_nonneg D.u_nonneg k, (gridPt_le D.u_nonneg hK hk).trans D.u_le⟩

theorem ht_aesm (D : IsTelescopeData h ht a φ t u T C Ct Ma R) (z : E) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ T) :
    AEStronglyMeasurable (fun x => ht x z) (volume.restrict (Ioo α β)) :=
  ((D.ht_cont z).mono (Ioo_subset_Ioo hα hβ)).aestronglyMeasurable measurableSet_Ioo

theorem integrableOn_ht (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {z : E} (hz : ‖z‖ ≤ R)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ t) : IntegrableOn (fun x => ht x z) (Ioc α β) :=
  integrableOn_Ioc_of_bound (D.ht_aesm z hα (hβ.trans D.t_le_T))
    fun x hx => D.ht_bound x ⟨hα.trans_lt hx.1, hx.2.trans_le hβ⟩ z hz

theorem integrableOn_a (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {v : ℝ} (hv : v ∈ Icc 0 T)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ t) : IntegrableOn (a v) (Ioc α β) := by
  have hsub : Ioc α β ⊆ Ioc 0 t := Ioc_subset_Ioc hα hβ
  have hm : AEStronglyMeasurable (a v) (volume.restrict (Ioo α β)) := by
    rw [← restrict_Ioc_eq_Ioo]
    exact (D.a_meas v hv).mono_measure (Measure.restrict_mono hsub le_rfl)
  exact integrableOn_Ioc_of_bound hm fun x hx =>
    D.a_bound v hv x ⟨hα.trans_lt hx.1, hx.2.trans_le hβ⟩

theorem continuousOn_slice (D : IsTelescopeData h ht a φ t u T C Ct Ma R) (z : E) :
    ContinuousOn (fun v => h v z) (Icc 0 T) :=
  D.cont.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hv => ⟨hv, mem_univ _⟩)

/-- FTC on one cell at the fixed point `z`. -/
theorem ftc_cell (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {z : E} (hz : ‖z‖ ≤ R)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ t) :
    ∫ x in Ioc α β, ht x z = h β z - h α z := by
  rw [← intervalIntegral.integral_of_le hαβ]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun v => h v z) hαβ ?_ ?_ ?_
  · exact (D.continuousOn_slice z).mono (Icc_subset_Icc hα (hβ.trans D.t_le_T))
  · intro x hx
    exact D.deriv z x ⟨hα.trans_lt hx.1, hx.2.trans_le (hβ.trans D.t_le_T)⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ]
    exact D.integrableOn_ht hz hα hβ

/-- The glued time-derivative integrand (space point `φ(μ_k)` held fixed on the cell `k`). -/
def htCells (ht : ℝ → E → ℝ) (φ : ℝ → E) (t u : ℝ) (K : ℕ) : ℝ → ℝ :=
  cellFun t u K (fun k x => ht x (φ (gridMu t u K k)))

/-- The glued generator integrand (time `p_{k+1}` held fixed on the cell `k`). -/
def aCells (a : ℝ → ℝ → ℝ) (t u : ℝ) (K : ℕ) : ℝ → ℝ :=
  cellFun t u K (fun k x => a (gridPt u K (k + 1)) x)

/-- **Decomposition** of the grid sum. -/
theorem gridSum_eq (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {K : ℕ} (hK : K ≠ 0) :
    gridSum h a φ t u K = (h t (φ t) - h 0 (φ 0)) - (∫ x in Ioc 0 t, htCells ht φ t u K x) +
      ∑ k ∈ Finset.range K, partialErr h φ t u K k - ∫ x in Ioc 0 t, aCells a t u K x := by
  have hu := D.u_nonneg
  have hcell : ∀ k ∈ Finset.range K,
      h (gridPt u K (k + 1)) (φ (gridMu t u K (k + 1))) -
        h (gridPt u K (k + 1)) (φ (gridMu t u K k)) -
        ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), a (gridPt u K (k + 1)) x =
      (h (gridMu t u K (k + 1)) (φ (gridMu t u K (k + 1))) -
          h (gridMu t u K k) (φ (gridMu t u K k))) -
        (∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), ht x (φ (gridMu t u K k))) +
        partialErr h φ t u K k -
        ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), a (gridPt u K (k + 1)) x := by
    intro k _
    rw [D.ftc_cell (D.phi_bound _ (D.mu_mem K k)) (D.mu_mem K k).1 (gridMu_mono hu (Nat.le_succ k))
      (D.mu_mem K (k + 1)).2]
    unfold partialErr
    ring
  unfold gridSum
  rw [Finset.sum_congr rfl hcell, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => h (gridMu t u K k) (φ (gridMu t u K k))),
    gridMu_self hK D.t_le, gridMu_zero D.t_nonneg]
  have e1 : ∑ k ∈ Finset.range K,
      ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), ht x (φ (gridMu t u K k)) =
      ∫ x in Ioc 0 t, htCells ht φ t u K x :=
    sum_integral_cells D.t_nonneg D.t_le hK _ fun k _ =>
      D.integrableOn_ht (D.phi_bound _ (D.mu_mem K k)) (D.mu_mem K k).1 (D.mu_mem K (k + 1)).2
  have e2 : ∑ k ∈ Finset.range K,
      ∫ x in Ioc (gridMu t u K k) (gridMu t u K (k + 1)), a (gridPt u K (k + 1)) x =
      ∫ x in Ioc 0 t, aCells a t u K x :=
    sum_integral_cells D.t_nonneg D.t_le hK _ fun k hk =>
      D.integrableOn_a (D.pt_mem_T hK hk) (D.mu_mem K k).1 (D.mu_mem K (k + 1)).2
  rw [e1, e2]

/-!
### The partial-cell error
-/

theorem partialErr_eq_zero (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {K k : ℕ}
    (hk : ¬ (gridMu t u K k < gridMu t u K (k + 1) ∧
      gridMu t u K (k + 1) < gridPt u K (k + 1))) : partialErr h φ t u K k = 0 := by
  unfold partialErr
  rcases not_and_or.1 hk with h1 | h1
  · have e : gridMu t u K k = gridMu t u K (k + 1) :=
      le_antisymm (gridMu_mono D.u_nonneg (Nat.le_succ k)) (not_lt.1 h1)
    rw [e]; ring
  · have e : gridMu t u K (k + 1) = gridPt u K (k + 1) :=
      le_antisymm (gridMu_le_gridPt _) (not_lt.1 h1)
    rw [e]; ring

theorem sum_partialErr_eq (D : IsTelescopeData h ht a φ t u T C Ct Ma R) (K : ℕ) :
    ∑ k ∈ Finset.range K, partialErr h φ t u K k =
      ∑ k ∈ (Finset.range K).filter (fun k => gridMu t u K k < gridMu t u K (k + 1) ∧
        gridMu t u K (k + 1) < gridPt u K (k + 1)), partialErr h φ t u K k := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · rfl
  · exact D.partialErr_eq_zero hk

theorem abs_sum_le_of_card_le_one {s : Finset ℕ} (hs : s.card ≤ 1) (f : ℕ → ℝ) {M : ℝ}
    (hM : ∀ k ∈ s, |f k| ≤ M) (hM0 : 0 ≤ M) : |∑ k ∈ s, f k| ≤ M := by
  rcases Finset.card_le_one_iff_subset_singleton.1 hs with ⟨k, hk⟩
  rcases Finset.subset_singleton_iff.1 hk with e | e
  · rw [e]; simpa using hM0
  · rw [e, Finset.sum_singleton]; exact hM k (by rw [e]; exact Finset.mem_singleton_self k)

theorem abs_sum_partialErr_le (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {K : ℕ}
    (hK : K ≠ 0) : |∑ k ∈ Finset.range K, partialErr h φ t u K k| ≤ 4 * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (D.bound 0 ⟨le_rfl, D.u_nonneg.trans D.u_le⟩ (φ 0))
  rw [D.sum_partialErr_eq]
  refine abs_sum_le_of_card_le_one (card_partial_le_one D.u_nonneg) _ (fun k hk => ?_)
    (by positivity)
  have hk' := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
  have hp := D.pt_mem_T hK (show k + 1 ≤ K by omega)
  have hm := D.mu_mem_T K (k + 1)
  unfold partialErr
  have := D.bound _ hp (φ (gridMu t u K (k + 1)))
  have := D.bound _ hm (φ (gridMu t u K (k + 1)))
  have := D.bound _ hp (φ (gridMu t u K k))
  have := D.bound _ hm (φ (gridMu t u K k))
  rw [abs_le] at *
  constructor <;> linarith

theorem tendsto_sum_partialErr [ProperSpace E] (D : IsTelescopeData h ht a φ t u T C Ct Ma R) :
    Tendsto (fun K => ∑ k ∈ Finset.range K, partialErr h φ t u K k) atTop (𝓝 0) := by
  have hcpt : IsCompact (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : E) R) :=
    isCompact_Icc.prod (isCompact_closedBall 0 R)
  have huc := hcpt.uniformContinuousOn_of_continuous
    (D.cont.mono (prod_mono subset_rfl (subset_univ _)))
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := huc (ε / 3) (by positivity)
  obtain ⟨K0, hK0⟩ := exists_nat_gt (u / δ)
  refine ⟨K0 + 1, fun K hK => ?_⟩
  have hK0' : K ≠ 0 := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0'
  have hmesh : u / K < δ := by
    rw [div_lt_iff₀ hKpos]
    have : (K0 : ℝ) + 1 ≤ K := by exact_mod_cast hK
    rw [div_lt_iff₀ hδ] at hK0
    nlinarith
  rw [Real.dist_eq, sub_zero, D.sum_partialErr_eq]
  refine lt_of_le_of_lt (abs_sum_le_of_card_le_one (card_partial_le_one D.u_nonneg) _
    (M := 2 * (ε / 3)) (fun k hk => ?_) (by positivity)) (by linarith)
  have hk' := Finset.mem_filter.1 hk
  have hkK := Finset.mem_range.1 hk'.1
  have hp := D.pt_mem_T hK0' (show k + 1 ≤ K by omega)
  have hm := D.mu_mem_T K (k + 1)
  have hstart := gridMu_eq_gridPt_of_lt hk'.2.1
  have hclose : |gridPt u K (k + 1) - gridMu t u K (k + 1)| < δ := by
    rw [abs_of_nonneg (by linarith [gridMu_le_gridPt (t := t) (u := u) (K := K) (k + 1)])]
    have := gridPt_succ (u := u) (K := K) k
    linarith [hk'.2.1]
  have key : ∀ z : E, ‖z‖ ≤ R →
      |h (gridPt u K (k + 1)) z - h (gridMu t u K (k + 1)) z| < ε / 3 := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : E) R := by simpa using hz
    have := hδh (gridPt u K (k + 1), z) ⟨hp, hz'⟩ (gridMu t u K (k + 1), z) ⟨hm, hz'⟩
      (by rw [Prod.dist_eq, dist_self, Real.dist_eq]; simpa using hclose)
    rwa [Real.dist_eq] at this
  unfold partialErr
  have h1 := key _ (D.phi_bound _ (D.mu_mem K (k + 1)))
  have h2 := key _ (D.phi_bound _ (D.mu_mem K k))
  rw [abs_lt] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-!
### The glued integrands
-/

/-- The cell of a point and the distances to its grid points. -/
theorem exists_cell_close (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {K : ℕ} (hK : K ≠ 0)
    {x : ℝ} (hx : x ∈ Ioc 0 t) : ∃ k < K, x ∈ Ioc (gridMu t u K k) (gridMu t u K (k + 1)) ∧
      |gridMu t u K k - x| ≤ u / K ∧ |gridPt u K (k + 1) - x| ≤ u / K ∧
      x ≤ gridPt u K (k + 1) := by
  obtain ⟨k, hk, hxk⟩ := exists_cell D.t_nonneg D.t_le hK hx
  obtain ⟨h1, h2, _⟩ := mem_cell_bounds hxk
  have hlt : gridMu t u K k < gridMu t u K (k + 1) := lt_of_lt_of_le hxk.1 hxk.2
  have e := gridMu_eq_gridPt_of_lt hlt
  have hs := gridPt_succ (u := u) (K := K) k
  refine ⟨k, hk, hxk, ?_, ?_, h2⟩
  · rw [e, abs_of_neg (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- Dominated convergence for glued integrands, with the limit's integrability and bound. -/
theorem tendsto_integral_cells (t : ℝ) (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) {M : ℝ}
    (hFm : ∀ K, K ≠ 0 → AEStronglyMeasurable (F K) (volume.restrict (Ioc 0 t)))
    (hFb : ∀ K, K ≠ 0 → ∀ x ∈ Ioo 0 t, |F K x| ≤ M)
    (hFt : ∀ x ∈ Ioo 0 t, Tendsto (fun K => F K x) atTop (𝓝 (f x))) :
    Tendsto (fun K => ∫ x in Ioc 0 t, F K x) atTop (𝓝 (∫ x in Ioc 0 t, f x)) ∧
      IntegrableOn f (Ioc 0 t) ∧ ∀ x ∈ Ioo 0 t, |f x| ≤ M := by
  have hfb : ∀ x ∈ Ioo 0 t, |f x| ≤ M := fun x hx =>
    le_of_tendsto ((continuous_abs.tendsto _).comp (hFt x hx))
      ((eventually_ne_atTop 0).mono fun K hK => hFb K hK x hx)
  have hae : ∀ᵐ x ∂(volume.restrict (Ioc 0 t)),
      Tendsto (fun K => F (K + 1) x) atTop (𝓝 (f x)) := by
    rw [restrict_Ioc_eq_Ioo, ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun x hx => (hFt x hx).comp (tendsto_add_atTop_nat 1)
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioc 0 t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun K => hFm (K + 1) (Nat.succ_ne_zero K)) hae
  have hfi : IntegrableOn f (Ioc 0 t) := by
    refine Integrable.of_bound hfm M ?_
    rw [restrict_Ioc_eq_Ioo, ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs]; exact hfb x hx
  refine ⟨?_, hfi, hfb⟩
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  refine tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun K => hFm (K + 1) (Nat.succ_ne_zero K)) (integrable_const M) (fun K => ?_) hae
  rw [restrict_Ioc_eq_Ioo, ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun x hx => by
    rw [Real.norm_eq_abs]; exact hFb (K + 1) (Nat.succ_ne_zero K) x hx

theorem htCells_props (D : IsTelescopeData h ht a φ t u T C Ct Ma R) :
    Tendsto (fun K => ∫ x in Ioc 0 t, htCells ht φ t u K x) atTop
        (𝓝 (∫ x in Ioc 0 t, ht x (φ x))) ∧
      IntegrableOn (fun x => ht x (φ x)) (Ioc 0 t) ∧ ∀ x ∈ Ioo 0 t, |ht x (φ x)| ≤ Ct := by
  refine tendsto_integral_cells t _ _ (fun K _ => ?_) (fun K hK x hx => ?_) (fun x hx => ?_)
  · unfold htCells cellFun
    refine Finset.aestronglyMeasurable_fun_sum _ fun k _ => AEStronglyMeasurable.indicator ?_
      measurableSet_Ioc
    rw [restrict_Ioc_eq_Ioo]
    exact D.ht_aesm _ le_rfl D.t_le_T
  · obtain ⟨k, hk, hxk, -⟩ := D.exists_cell_close hK (Ioo_subset_Ioc_self hx)
    unfold htCells
    rw [cellFun_eq D.u_nonneg _ hk hxk]
    exact D.ht_bound x hx _ (D.phi_bound _ (D.mu_mem K k))
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 (D.phi_cont x hx) ε hε
    obtain ⟨K0, hK0⟩ := exists_nat_gt (u / δ)
    refine ⟨K0 + 1, fun K hK => ?_⟩
    have hK0' : K ≠ 0 := by omega
    have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0'
    have hmesh : u / K < δ := by
      rw [div_lt_iff₀ hKpos]
      have : (K0 : ℝ) + 1 ≤ K := by exact_mod_cast hK
      rw [div_lt_iff₀ hδ] at hK0
      nlinarith
    obtain ⟨k, hk, hxk, hclose, -⟩ := D.exists_cell_close hK0' (Ioo_subset_Ioc_self hx)
    unfold htCells
    rw [cellFun_eq D.u_nonneg _ hk hxk]
    exact hδc (by rw [Real.dist_eq]; linarith)

theorem aCells_props (D : IsTelescopeData h ht a φ t u T C Ct Ma R) :
    Tendsto (fun K => ∫ x in Ioc 0 t, aCells a t u K x) atTop (𝓝 (∫ x in Ioc 0 t, a x x)) ∧
      IntegrableOn (fun x => a x x) (Ioc 0 t) ∧ ∀ x ∈ Ioo 0 t, |a x x| ≤ Ma := by
  refine tendsto_integral_cells t _ _ (fun K _ => ?_) (fun K hK x hx => ?_) (fun x hx => ?_)
  · unfold aCells cellFun
    exact Finset.aestronglyMeasurable_fun_sum _ fun k hk =>
      (D.a_meas _ (D.pt_mem_T ‹K ≠ 0› (by have := Finset.mem_range.1 hk; omega))).indicator
        measurableSet_Ioc
  · obtain ⟨k, hk, hxk, -⟩ := D.exists_cell_close hK (Ioo_subset_Ioc_self hx)
    unfold aCells
    rw [cellFun_eq D.u_nonneg _ hk hxk]
    exact D.a_bound _ (D.pt_mem_T hK (by omega)) x hx
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (D.a_cont x hx) ε hε
    obtain ⟨K0, hK0⟩ := exists_nat_gt (u / δ)
    refine ⟨K0 + 1, fun K hK => ?_⟩
    have hK0' : K ≠ 0 := by omega
    have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0'
    have hmesh : u / K < δ := by
      rw [div_lt_iff₀ hKpos]
      have : (K0 : ℝ) + 1 ≤ K := by exact_mod_cast hK
      rw [div_lt_iff₀ hδ] at hK0
      nlinarith
    obtain ⟨k, hk, hxk, -, hclose, -⟩ := D.exists_cell_close hK0' (Ioo_subset_Ioc_self hx)
    unfold aCells
    rw [cellFun_eq D.u_nonneg _ hk hxk]
    exact hδc (D.pt_mem_T hK0' (by omega)) (by rw [Real.dist_eq]; linarith)

/-!
### The limit and the bound
-/

/-- **Riemann telescoping.** The grid sums converge to the space-time bracket. -/
theorem tendsto_gridSum [ProperSpace E] (D : IsTelescopeData h ht a φ t u T C Ct Ma R) :
    Tendsto (fun K => gridSum h a φ t u K) atTop
      (𝓝 (h t (φ t) - h 0 (φ 0) - ∫ x in Ioc 0 t, (ht x (φ x) + a x x))) := by
  obtain ⟨h1, h1i, -⟩ := D.htCells_props
  obtain ⟨h2, h2i, -⟩ := D.aCells_props
  have hlim := ((tendsto_const_nhds (x := h t (φ t) - h 0 (φ 0))).sub h1).add
    (D.tendsto_sum_partialErr) |>.sub h2
  rw [integral_add h1i h2i]
  have e : h t (φ t) - h 0 (φ 0) - ((∫ x in Ioc 0 t, ht x (φ x)) + ∫ x in Ioc 0 t, a x x) =
      h t (φ t) - h 0 (φ 0) - (∫ x in Ioc 0 t, ht x (φ x)) + 0 - ∫ x in Ioc 0 t, a x x := by ring
  rw [e]
  refine hlim.congr' ((eventually_ne_atTop 0).mono fun K hK => ?_)
  exact (D.gridSum_eq hK).symm

theorem abs_setIntegral_Ioc_le {f : ℝ → ℝ} {t M : ℝ} (ht : 0 ≤ t)
    (hb : ∀ x ∈ Ioo 0 t, |f x| ≤ M) : |∫ x in Ioc 0 t, f x| ≤ M * t := by
  have := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (s := Ioc 0 t) (f := f)
    (C := M) measure_Ioc_lt_top (by
      rw [restrict_Ioc_eq_Ioo, ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx)
  rwa [Real.norm_eq_abs, Real.volume_real_Ioc_of_le ht, sub_zero] at this

/-- **Uniform bound** of the grid sums. -/
theorem abs_gridSum_le (D : IsTelescopeData h ht a φ t u T C Ct Ma R) {K : ℕ} (hK : K ≠ 0) :
    |gridSum h a φ t u K| ≤ 6 * C + t * (Ct + Ma) := by
  rw [D.gridSum_eq hK]
  have e1 : |∫ x in Ioc 0 t, htCells ht φ t u K x| ≤ Ct * t := by
    refine abs_setIntegral_Ioc_le D.t_nonneg fun x hx => ?_
    obtain ⟨k, hk, hxk, -⟩ := D.exists_cell_close hK (Ioo_subset_Ioc_self hx)
    unfold htCells
    rw [cellFun_eq D.u_nonneg _ hk hxk]
    exact D.ht_bound x hx _ (D.phi_bound _ (D.mu_mem K k))
  have e2 : |∫ x in Ioc 0 t, aCells a t u K x| ≤ Ma * t := by
    refine abs_setIntegral_Ioc_le D.t_nonneg fun x hx => ?_
    obtain ⟨k, hk, hxk, -⟩ := D.exists_cell_close hK (Ioo_subset_Ioc_self hx)
    unfold aCells
    rw [cellFun_eq D.u_nonneg _ hk hxk]
    exact D.a_bound _ (D.pt_mem_T hK (by omega)) x hx
  have e3 := D.abs_sum_partialErr_le hK
  have e4 := D.bound t ⟨D.t_nonneg, D.t_le_T⟩ (φ t)
  have e5 := D.bound 0 ⟨le_rfl, D.u_nonneg.trans D.u_le⟩ (φ 0)
  rw [abs_le] at e1 e2 e3 e4 e5 ⊢
  constructor <;> nlinarith

end IsTelescopeData

end BlockBand.Critical.RelativeVectors.Angular
