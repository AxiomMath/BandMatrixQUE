module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerRep
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Version
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Gronwall
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Euler scheme: integrands at the left grid point, joint versions, increment error

Setting as in `EulerRep`: `(Ω, 𝓕, P)`, `B` a `𝓕`-Brownian motion, `ξ` `𝓕_0`-measurable,
`c : LipCoef d`, grid `t_j = j 2^{-m}`; `A` a measurable full-measure set of continuous paths of
`B` (`exists_good_set`).

* `eulDrift_eq`, `eulDiff_eq`: on `(0, t_J]` the integrands are `b(E_{j(r)})`, `σ(E_{j(r)})`.
* `eulXv`: a jointly measurable version of the scheme (`measurable_eulXv`), equal to `eulX` at
  every time on `A` (`eulXv_of_mem`).
* `eulEps m (r, ω) = |X_r - E_{j(r)}|²` (squared Euclidean, `ℝ≥0∞`), jointly measurable.

The increment bound `E eulEps(r) ≤ 2 d M² (1 + d²) 2^{-m}` for every `r ≥ 0` is proved in the
sibling module, **`lintegral_eulEps_le`**.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.Levy
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {d : ℕ}
  (c : LipCoef d) (m : ℕ) {ξ : Ω → Fin d → ℝ} {B : ℝ≥0 → Ω → Fin d → ℝ}

theorem measurable_gridIdx : Measurable fun p : ℝ × Ω => gridIdx m p.1.toNNReal :=
  (measurable_of_countable fun n : ℕ => n - 1).comp (Nat.measurable_ceil.comp
    ((measurable_id.mul_const _).comp (measurable_real_toNNReal.comp measurable_fst)))

theorem measurable_comp_gridIdx {γ : Type*} [MeasurableSpace γ] {G : ℕ → ℝ × Ω → γ}
    (hG : ∀ j, Measurable (G j)) : Measurable fun p : ℝ × Ω => G (gridIdx m p.1.toNNReal) p := by
  have h1 : Measurable fun q : (ℝ × Ω) × ℕ => G q.2 q.1 :=
    measurable_from_prod_countable_left fun j => hG j
  exact h1.comp (measurable_id.prodMk (measurable_gridIdx m))

omit mΩ in
theorem mem_grid_of_pos {r : ℝ} (hr : 0 < r) :
    (gridT m (gridIdx m r.toNNReal) : ℝ) < r ∧ r ≤ gridT m (gridIdx m r.toNNReal + 1) := by
  have h1 := gridT_idx_lt (m := m) (Real.toNNReal_pos.2 hr)
  have h2 := le_gridT_idx_succ m r.toNNReal
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.le] at h1
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.le] at h2
  exact ⟨h1, h2⟩

omit mΩ in
theorem indicator_grid_eq {r : ℝ} (hr : 0 < r) {J : ℕ} (hrJ : r ≤ gridT m J) {y : ℕ → ℝ} :
    ∑ j ∈ Finset.range J, (Ioc (gridT m j : ℝ) (gridT m (j + 1))).indicator (fun _ => y j) r =
      y (gridIdx m r.toNNReal) := by
  set j₀ := gridIdx m r.toNNReal
  have hmem := mem_grid_of_pos m hr
  have hz : ∀ j, j ≠ j₀ → (Ioc (gridT m j : ℝ) (gridT m (j + 1))).indicator (fun _ => y j) r = 0 :=
    fun j hj => indicator_of_notMem (fun h => hj (by
      refine (gridIdx_eq_of_mem ?_ ?_).symm
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.le]; exact h.1
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.le]; exact h.2)) _
  have hj₀ : j₀ ∈ Finset.range J := by
    rw [Finset.mem_range]
    by_contra hJ
    have := gridT_mono m (not_lt.1 hJ)
    have h3 : (gridT m J : ℝ) ≤ gridT m j₀ := this
    linarith [hmem.1]
  rw [Finset.sum_eq_single_of_mem j₀ hj₀ (fun j _ h => hz j h)]
  exact indicator_of_mem (show r ∈ Ioc (gridT m j₀ : ℝ) (gridT m (j₀ + 1)) from hmem) _

omit mΩ in
theorem eulDrift_eq {r : ℝ} (hr : 0 < r) {J : ℕ} (hrJ : r ≤ gridT m J) (i : Fin d) (ω : Ω) :
    eulDrift c m ξ B J i (r, ω) = c.b (eulE c m ξ B (gridIdx m r.toNNReal) ω) i :=
  indicator_grid_eq m hr hrJ (y := fun j => c.b (eulE c m ξ B j ω) i)

omit mΩ in
theorem eulDiff_eq {r : ℝ} (hr : 0 < r) {J : ℕ} (hrJ : r ≤ gridT m J) (i l : Fin d) (ω : Ω) :
    eulDiff c m ξ B J i l (r, ω) = c.σ (eulE c m ξ B (gridIdx m r.toNNReal) ω) i l := by
  have e : eulDiff c m ξ B J i l (r, ω) = ∑ j ∈ Finset.range J,
      (Ioc (gridT m j : ℝ) (gridT m (j + 1))).indicator
        (fun _ => c.σ (eulE c m ξ B j ω) i l) r := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pieceFn, ite_true, indicator_apply, mem_prod, mem_univ, and_true]
  rw [e]
  exact indicator_grid_eq m hr hrJ (y := fun j => c.σ (eulE c m ξ B j ω) i l)

/-- A jointly measurable version of the Euler scheme. -/
def eulXv (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (A : Set Ω) (p : ℝ × Ω) : Fin d → ℝ :=
  eulE c m ξ B (gridIdx m p.1.toNNReal) p.2 +
    ((p.1.toNNReal : ℝ) - gridT m (gridIdx m p.1.toNNReal)) •
      c.b (eulE c m ξ B (gridIdx m p.1.toNNReal) p.2) +
    c.σ (eulE c m ξ B (gridIdx m p.1.toNNReal) p.2) *ᵥ
      (jointVersion B A p - B (gridT m (gridIdx m p.1.toNNReal)) p.2)

omit mΩ in
theorem eulXv_of_mem {A : Set Ω} {ω : Ω} (hω : ω ∈ A) (r : ℝ) :
    eulXv c m ξ B A (r, ω) = eulX c m ξ B r.toNNReal ω := by
  simp only [eulXv, eulX, eulerX, jointVersion_of_mem hω, eulE]

theorem measurable_eulXv (hB : ∀ t, Measurable (B t)) (hE : ∀ j, Measurable (eulE c m ξ B j))
    {A : Set Ω} (hA : MeasurableSet A) (hAc : ∀ ω ∈ A, Continuous fun t => B t ω) :
    Measurable (eulXv c m ξ B A) := by
  have hJ := measurable_jointVersion hB hA hAc
  refine measurable_comp_gridIdx m (G := fun j p => eulE c m ξ B j p.2 +
    ((p.1.toNNReal : ℝ) - gridT m j) • c.b (eulE c m ξ B j p.2) +
    c.σ (eulE c m ξ B j p.2) *ᵥ (jointVersion B A p - B (gridT m j) p.2)) fun j => ?_
  have h1 : Measurable fun p : ℝ × Ω => eulE c m ξ B j p.2 := (hE j).comp measurable_snd
  exact (h1.add (((measurable_real_toNNReal.comp measurable_fst).coe_nnreal_real.sub_const
    _).smul (c.continuous_b.measurable.comp h1))).add
      ((c.continuous_σ.comp continuous_fst).matrix_mulVec continuous_snd |>.measurable.comp
        (h1.prodMk (hJ.sub ((hB _).comp measurable_snd))))

/-- The Euler discretisation error `|X_r - E_{j(r)}|²`. -/
def eulEps (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (A : Set Ω) (p : ℝ × Ω) : ℝ≥0∞ :=
  ∑ i, ‖eulXv c m ξ B A p i - eulE c m ξ B (gridIdx m p.1.toNNReal) p.2 i‖ₑ ^ 2

theorem measurable_eulEps (hB : ∀ t, Measurable (B t)) (hE : ∀ j, Measurable (eulE c m ξ B j))
    {A : Set Ω} (hA : MeasurableSet A) (hAc : ∀ ω ∈ A, Continuous fun t => B t ω) :
    Measurable (eulEps c m ξ B A) := by
  have hX := measurable_eulXv c m hB hE hA hAc
  have hEj := measurable_comp_gridIdx m (G := fun j p => eulE c m ξ B j p.2)
    fun j => (hE j).comp measurable_snd
  exact Finset.measurable_sum _ fun i _ =>
    (((measurable_pi_apply i).comp hX).sub ((measurable_pi_apply i).comp hEj)).enorm.pow_const 2

end BlockBand.SourceProcess.Stochastic.Uniqueness
