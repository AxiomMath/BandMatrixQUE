module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Euler
public import BlockBand.SourceProcess.Stochastic.Uniqueness.BrownianTools
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Euler scheme driven by a filtration Brownian motion is an Itô process

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion with
integrator `hB.isL2IntegratorVec` (general vector integral, identity density), `ξ` a
`𝓕_0`-measurable initial value, coefficients `c : LipCoef d`, grid `t_j = j 2^{-m}`, horizon `T`,
`J = ⌈T 2^m⌉` grid steps.

* `eulE`, `eulX`: the Euler grid values and the interpolated scheme driven by the paths of `B`.
* `measurable_eulE`: `E_j` is `𝓕_{t_j}`-measurable (raw filtration; no completion).
* `eulDrift`, `eulDiff`: the piecewise constant (left grid point) drift and bounded predictable
  diffusion integrands `b(E_j)`, `σ(E_j)` on `(t_j, t_{j+1}]`.
* **`eulX_rep`**: for `t ≤ T`, a.s. `X^i_t = ξ^i + ∫_{(0,t]} b_i(E_{j(r)}) dr + ∑_k ∫_0^t
  σ_{ik}(E_{j(r)}) dB^k` (general integral).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {d : ℕ}

/-- Euler grid values driven by the paths of `B`. -/
def eulE (c : LipCoef d) (m : ℕ) (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (j : ℕ)
    (ω : Ω) : Fin d → ℝ :=
  eulerE c m (ξ ω) (fun s => B s ω) j

/-- The interpolated Euler scheme driven by the paths of `B`. -/
def eulX (c : LipCoef d) (m : ℕ) (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0)
    (ω : Ω) : Fin d → ℝ :=
  eulerX c m (ξ ω) (fun s => B s ω) t

variable (c : LipCoef d) (m : ℕ) {ξ : Ω → Fin d → ℝ} {B : ℝ≥0 → Ω → Fin d → ℝ}

theorem continuous_eulStep : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
    p.1 + (1 / 2 ^ m : ℝ) • c.b p.1 + c.σ p.1 *ᵥ (p.2.1 - p.2.2) := by
  have hb := c.continuous_b
  have hσ := c.continuous_σ
  have h1 : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
      c.σ p.1 *ᵥ (p.2.1 - p.2.2) := (hσ.comp continuous_fst).matrix_mulVec (by fun_prop)
  fun_prop

/-- `E_j` is `𝓕_{t_j}`-measurable. -/
theorem measurable_eulE (hB : ∀ t, Measurable[𝓕 t] (B t)) (hξ : Measurable[𝓕 0] ξ) (j : ℕ) :
    Measurable[𝓕 (gridT m j)] (eulE c m ξ B j) := by
  induction j with
  | zero => rw [gridT_zero]; exact hξ
  | succ j ih =>
    have hle : 𝓕 (gridT m j) ≤ 𝓕 (gridT m (j + 1)) := 𝓕.mono (gridT_mono m (Nat.le_succ j))
    have h1 : Measurable[𝓕 (gridT m (j + 1))] (eulE c m ξ B j) := ih.mono hle le_rfl
    have h2 : Measurable[𝓕 (gridT m (j + 1))] (B (gridT m j)) := (hB _).mono hle le_rfl
    exact (continuous_eulStep c m).measurable.comp (h1.prodMk ((hB _).prodMk h2))

/-- The Euler drift integrand `b(E_j)` on `(t_j, t_{j+1}]`, `j < J`. -/
def eulDrift (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (J : ℕ) (i : Fin d)
    (p : ℝ × Ω) : ℝ :=
  ∑ j ∈ Finset.range J, (Ioc (gridT m j : ℝ) (gridT m (j + 1))).indicator
    (fun _ => c.b (eulE c m ξ B j p.2) i) p.1

/-- The Euler diffusion integrand `σ(E_j)` on `(t_j, t_{j+1}]`, `j < J`. -/
def eulDiff (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (J : ℕ) (i l : Fin d)
    (p : ℝ × Ω) : ℝ :=
  ∑ j ∈ Finset.range J, pieceFn (gridT m j) (gridT m (j + 1))
    (fun ω => c.σ (eulE c m ξ B j ω) i l) l l p

theorem measurable_eulDrift (hB : ∀ t, Measurable[𝓕 t] (B t)) (hξ : Measurable[𝓕 0] ξ)
    (J : ℕ) (i : Fin d) : Measurable (eulDrift c m ξ B J i) := by
  refine Finset.measurable_sum _ fun j _ => Measurable.indicator ?_
    (measurableSet_Ioc.preimage measurable_fst)
  exact (((measurable_pi_apply i).comp c.continuous_b.measurable).comp
    ((measurable_eulE c m hB hξ j).mono (𝓕.le _) le_rfl)).comp measurable_snd

omit mΩ in
theorem abs_eulDrift_le (J : ℕ) (i : Fin d) (p : ℝ × Ω) :
    |eulDrift c m ξ B J i p| ≤ c.M := by
  unfold eulDrift
  rcases le_or_gt p.1 0 with h0 | h0
  · rw [Finset.sum_eq_zero fun j _ => indicator_of_notMem (fun h => by
      have := h.1; have := (gridT m j).coe_nonneg; linarith) _]
    simp [c.M_nonneg]
  · set j₀ := gridIdx m p.1.toNNReal
    have hz : ∀ j, j ≠ j₀ → (Ioc (gridT m j : ℝ) (gridT m (j + 1))).indicator
        (fun _ => c.b (eulE c m ξ B j p.2) i) p.1 = 0 := fun j hj => by
      refine indicator_of_notMem (fun h => hj ?_) _
      have h1 : gridT m j < p.1.toNNReal := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ h0.le]; exact h.1
      have h2 : p.1.toNNReal ≤ gridT m (j + 1) := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0.le]; exact h.2
      exact (gridIdx_eq_of_mem h1 h2).symm
    by_cases hj : j₀ ∈ Finset.range J
    · rw [Finset.sum_eq_single_of_mem j₀ hj (fun j _ h => hz j h), indicator_apply]
      split_ifs
      · exact c.bd_b _ _
      · simp [c.M_nonneg]
    · rw [Finset.sum_eq_zero (fun j hjJ => hz j (fun h => hj (h ▸ hjJ)))]
      simp [c.M_nonneg]

theorem isBddPred_eulDiff (hB : ∀ t, Measurable[𝓕 t] (B t)) (hξ : Measurable[𝓕 0] ξ)
    (J : ℕ) (i l : Fin d) : IsBddPred 𝓕 (eulDiff c m ξ B J i l) :=
  IsBddPred.sum _ fun j => isBddPred_pieceFn
    ((((measurable_pi_apply l).comp (measurable_pi_apply i)).comp c.continuous_σ.measurable).comp
      (measurable_eulE c m hB hξ j)).stronglyMeasurable (fun _ => c.bd_σ _ i l) l l

omit mΩ in
theorem eulDiff_eq_sum (J : ℕ) (i l : Fin d) (p : ℝ × Ω) :
    eulDiff c m ξ B J i l p = ∑ q : Fin J × Fin d, pieceFn (gridT m q.1) (gridT m (q.1 + 1))
      (fun ω => c.σ (eulE c m ξ B q.1 ω) i q.2) q.2 l p := by
  rw [Fintype.sum_prod_type, eulDiff, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single l (fun k _ hk => by simp [pieceFn, Ne.symm hk]) (by simp)]

theorem gridT_mul_pow (n : ℕ) : gridT m (n * 2 ^ m) = n := by
  rw [gridT]; push_cast; rw [mul_div_cancel_right₀ _ (by positivity)]

theorem integral_Ioc_indicator_const {a b : ℝ≥0} (hab : a ≤ b) (t : ℝ≥0) (y : ℝ) :
    ∫ r in Ioc (0 : ℝ) t, (Ioc (a : ℝ) b).indicator (fun _ => y) r =
      (((min b t : ℝ≥0) : ℝ) - ((min a t : ℝ≥0) : ℝ)) * y := by
  rw [integral_indicator_const _ measurableSet_Ioc, measureReal_restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc, Real.volume_real_Ioc, smul_eq_mul, NNReal.coe_min, NNReal.coe_min]
  congr 1
  have ha := a.coe_nonneg
  have hab' : (a : ℝ) ≤ b := hab
  rcases le_total (t : ℝ) a with h | h
  · rw [min_eq_right (h.trans hab'), min_eq_right h, max_eq_left ha]
    simp [h]
  · rw [min_eq_left h, max_eq_left ha]
    have : (a : ℝ) ≤ min (b : ℝ) t := le_min hab' h
    rw [max_eq_left (by linarith)]

/-- **The Euler scheme is an Itô process for the general integral** (integer horizon `n`). -/
theorem eulX_rep {P : Measure Ω} [IsProbabilityMeasure P] (hB : IsFiltrationBrownian P 𝓕 B)
    (hξ : Measurable[𝓕 0] ξ) (n : ℕ) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
    ∀ t ≤ (n : ℝ≥0), ∀ i, ∀ᵐ ω ∂P, eulX c m ξ B t ω i = ξ ω i +
      ((∫ r in Ioc (0 : ℝ) t, eulDrift c m ξ B (n * 2 ^ m) i (r, ω)) +
        hB.isL2IntegratorVec.vecCont (n : ℝ≥0) (fun l => bpL2 _ (isBddPred_eulDiff c m
          (fun t => (hB.adapted t).measurable) hξ (n * 2 ^ m) i l)) t ω) := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
  intro t htT i
  set J := n * 2 ^ m
  set μ := barMeasure P (idDens d Ω) (n : ℝ≥0)
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => (hB.adapted t).measurable
  have hG : ∀ q : Fin J × Fin d, StronglyMeasurable[𝓕 (gridT m q.1)]
      (fun ω => c.σ (eulE c m ξ B q.1 ω) i q.2) := fun q => by
    have hc : Continuous fun x => c.σ x i q.2 :=
      (continuous_apply q.2).comp ((continuous_apply i).comp c.continuous_σ)
    have : Measurable[𝓕 (gridT m q.1)] (fun ω => c.σ (eulE c m ξ B q.1 ω) i q.2) :=
      hc.measurable.comp (measurable_eulE c m hBm hξ q.1)
    exact this.stronglyMeasurable
  have hpiece : ∀ (q : Fin J × Fin d) l, IsBddPred 𝓕 (pieceFn (gridT m q.1) (gridT m (q.1 + 1))
      (fun ω => c.σ (eulE c m ξ B q.1 ω) i q.2) q.2 l) := fun q l =>
    isBddPred_pieceFn (hG q) (fun _ => c.bd_σ _ i q.2) q.2 l
  have e1 : (fun l => bpL2 μ (isBddPred_eulDiff c m hBm hξ J i l)) =
      ∑ q : Fin J × Fin d, fun l => bpL2 μ (hpiece q l) := by
    funext l
    rw [Finset.sum_apply, ← bpL2_sum (fun q => hpiece q l)]
    exact bpL2_congr _ _ (Eventually.of_forall fun p => eulDiff_eq_sum c m J i l p)
  have hgrid : ∀ q : Fin J × Fin d, gridT m q.1 ≤ gridT m (q.1 + 1) := fun q =>
    gridT_mono m (Nat.le_succ _)
  have hJ : ∀ q : Fin J × Fin d, gridT m (q.1 + 1) ≤ (n : ℝ≥0) := fun q => by
    rw [← gridT_mul_pow m n]; exact gridT_mono m q.1.2
  have hpc := fun q : Fin J × Fin d => vecCont_pieceFn hB (hgrid q) (hJ q) (hG q)
    (fun _ => c.bd_σ _ i q.2) q.2 (hpiece q) t
  have hdrift : ∀ ω, ∫ r in Ioc (0 : ℝ) t, eulDrift c m ξ B J i (r, ω) =
      ∑ j ∈ Finset.range J, (((min (gridT m (j + 1)) t : ℝ≥0) : ℝ) -
        ((min (gridT m j) t : ℝ≥0) : ℝ)) * c.b (eulE c m ξ B j ω) i := fun ω => by
    show ∫ r in Ioc (0 : ℝ) t, ∑ j ∈ Finset.range J, (Ioc (gridT m j : ℝ) (gridT m (j + 1))).indicator
      (fun _ => c.b (eulE c m ξ B j ω) i) r = _
    rw [integral_finsetSum _ fun j _ => (integrable_const _).indicator measurableSet_Ioc]
    exact Finset.sum_congr rfl fun j _ =>
      integral_Ioc_indicator_const (gridT_mono m (Nat.le_succ j)) t _
  filter_upwards [vecCont_finsetSum_ae hB.isL2IntegratorVec (n : ℝ≥0) Finset.univ
    (fun q => fun l => bpL2 μ (hpiece q l)) t, ae_all_iff.2 hpc] with ω h1 h2
  rw [e1, h1, Finset.sum_congr rfl fun q _ => h2 q, hdrift ω, eulX,
    eulerX_eq_sum c m (ξ ω) _ J (htT.trans_eq (gridT_mul_pow m n).symm),
    Pi.add_apply, Finset.sum_apply, Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range
      (fun j => (((min (gridT m (j + 1)) t : ℝ≥0) : ℝ) - ((min (gridT m j) t : ℝ≥0) : ℝ)) *
        c.b (eulE c m ξ B j ω) i), ← Fin.sum_univ_eq_sum_range
      (fun j => eulerInc c m (ξ ω) (fun s => B s ω) j t i), ← Finset.sum_add_distrib]
  congr 1

end BlockBand.SourceProcess.Stochastic.Uniqueness
