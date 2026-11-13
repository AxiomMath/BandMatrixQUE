module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Zero
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Taylor scheme with integral bounds: hypotheses and pathwise facts)

Generalization of `Semimartingale.SchemeHyp` (pointwise bounds `|β| ≤ Cβ`, `|α| ≤ Cα`) to
**pathwise integral bounds**: `IHyp Q 𝓖 K Z β α N B C` asks that a.s. the paths of `β`, `α`
are integrable on every `(0, t]` and that the control
`G_t = ∫_0^t (Σ_i |β^i| + Σ_{ij} |α^{ij}|)` (`ctrlI`) is bounded by `C` for all `t`; the
other fields are those of `SchemeHyp` (arbitrary raw filtration, values a.s. in a compact `K`,
a.s. continuous paths, `𝓖_t`-a.e. measurable `Z_t`, martingales `N`, `B` equal a.s. at each
time to the compensated coordinates and products) plus a.e.-measurability of `G_t`.

Pathwise (on `IGood`, a full-measure set for fixed `s ≤ t`): increments of `∫β`, `∫α` over
a grid cell are bounded by the increment `ΔG_k` of the control (`abs_incI_le'`,
`abs_incJ_le'`); `Σ_k ΔG_k ≤ C`; `N` is bounded by `2R + C`; `Σ_k (ΔG_k)² → 0`
(`tendsto_sqG`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}

/-- The control density `Σ_i |β^i| + Σ_{ij} |α^{ij}|`. -/
def ctrl (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, |β u ω i| + ∑ i, ∑ j, |α u ω i j|

/-- The control `G_u = ∫_0^u ctrl`. -/
def ctrlI (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ v in Ioc (0 : ℝ) u, ctrl β α v.toNNReal ω

/-- Hypotheses of the Taylor scheme with integral bounds (module docstring). -/
structure IHyp (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 m₀) (K : Set (Fin d → ℝ))
    (Z β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ)
    (N : Fin d → ℝ≥0 → Ω → ℝ) (B : Fin d → Fin d → ℝ≥0 → Ω → ℝ) (C : ℝ) : Prop where
  compact : IsCompact K
  mem : ∀ᵐ ω ∂Q, ∀ t, Z t ω ∈ K
  cont : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω
  meas : ∀ t, AEStronglyMeasurable[𝓖 t] (Z t) Q
  integ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    (∀ i, IntegrableOn (fun u : ℝ => β u.toNNReal ω i) (Ioc 0 t)) ∧
    ∀ i j, IntegrableOn (fun u : ℝ => α u.toNNReal ω i j) (Ioc 0 t)
  bound : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ctrlI β α t ω ≤ C
  ctrlMeas : ∀ t, AEStronglyMeasurable (ctrlI β α t) Q
  mart : ∀ i, Martingale (N i) 𝓖 Q
  mart_eq : ∀ i t, N i t =ᵐ[Q] fun ω => Z t ω i - Z 0 ω i - drI β i t ω
  bracket : ∀ i j, Martingale (B i j) 𝓖 Q
  bracket_eq : ∀ i j t, B i j t =ᵐ[Q] fun ω => N i t ω * N j t ω - difJ α i j t ω

/-- A path integrable on every `(0, t]` (through `toNNReal`) is a.e.-strongly measurable. -/
theorem aesm_path_of_integrableOn {g : ℝ≥0 → ℝ}
    (hg : ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => g s.toNNReal) (Ioc 0 t)) :
    AEStronglyMeasurable (fun s : ℝ => g s.toNNReal) volume := by
  have h : ∀ n : ℕ, AEStronglyMeasurable (fun s : ℝ => g s.toNNReal)
      (volume.restrict (Ioc (-(n : ℝ)) n)) := fun n =>
    (intervalIntegrable_toNNReal_path hg (-(n : ℝ)) n).1.aestronglyMeasurable
  have hU : (⋃ n : ℕ, Ioc (-(n : ℝ)) n) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, by constructor <;> linarith [neg_abs_le x, le_abs_self x]⟩
  rw [← Measure.restrict_univ (μ := volume), ← hU]
  exact aestronglyMeasurable_iUnion_iff.2 h

/-- The almost-sure properties used pathwise on the grids of `[s, t]`. -/
def IGood (K : Set (Fin d → ℝ)) (Z β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (N : Fin d → ℝ≥0 → Ω → ℝ)
    (B : Fin d → Fin d → ℝ≥0 → Ω → ℝ) (C : ℝ) (s t : ℝ≥0) (ω : Ω) : Prop :=
  GoodPt K Z β α N B s t ω ∧
  (∀ u : ℝ≥0, (∀ i, IntegrableOn (fun v : ℝ => β v.toNNReal ω i) (Ioc 0 u)) ∧
    ∀ i j, IntegrableOn (fun v : ℝ => α v.toNNReal ω i j) (Ioc 0 u)) ∧
  ∀ u : ℝ≥0, ctrlI β α u ω ≤ C

variable {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀} {K : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {C : ℝ}

theorem IHyp.ae_igood (H : IHyp Q 𝓖 K Z β α N B C) (s t : ℝ≥0) :
    ∀ᵐ ω ∂Q, IGood K Z β α N B C s t ω := by
  have h1 : ∀ᵐ ω ∂Q, ∀ n k i, N i (grid s t n k) ω =
      Z (grid s t n k) ω i - Z 0 ω i - drI β i (grid s t n k) ω := by
    simp only [ae_all_iff]; exact fun n k i => H.mart_eq i _
  have h2 : ∀ᵐ ω ∂Q, ∀ n k i j, B i j (grid s t n k) ω =
      N i (grid s t n k) ω * N j (grid s t n k) ω - difJ α i j (grid s t n k) ω := by
    simp only [ae_all_iff]; exact fun n k i j => H.bracket_eq i j _
  filter_upwards [H.mem, H.cont, H.integ, H.bound, h1, h2] with ω a b c e f g
  refine ⟨⟨a, b, fun i => ?_, fun i j => ?_, f, g⟩, c, e⟩
  · exact aesm_path_of_integrableOn (g := fun u => β u ω i) fun u => (c u).1 i
  · exact aesm_path_of_integrableOn (g := fun u => α u ω i j) fun u => (c u).2 i j

theorem ctrl_nonneg (u : ℝ≥0) (ω : Ω) : 0 ≤ ctrl β α u ω :=
  add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem abs_β_le_ctrl (u : ℝ≥0) (ω : Ω) (i : Fin d) : |β u ω i| ≤ ctrl β α u ω := by
  have h1 : |β u ω i| ≤ ∑ i, |β u ω i| :=
    Finset.single_le_sum (f := fun i => |β u ω i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ i, ∑ j, |α u ω i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold ctrl; linarith

theorem abs_α_le_ctrl (u : ℝ≥0) (ω : Ω) (i j : Fin d) : |α u ω i j| ≤ ctrl β α u ω := by
  have h1 : |α u ω i j| ≤ ∑ j, |α u ω i j| :=
    Finset.single_le_sum (f := fun j => |α u ω i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j, |α u ω i j| ≤ ∑ i, ∑ j, |α u ω i j| :=
    Finset.single_le_sum (f := fun i => ∑ j, |α u ω i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i, |β u ω i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold ctrl; linarith

section Pathwise

variable {s t : ℝ≥0} {ω : Ω}

theorem IGood.ii_β (hω : IGood K Z β α N B C s t ω) (i : Fin d) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => β u.toNNReal ω i) volume a b :=
  intervalIntegrable_toNNReal_path (g := fun u => β u ω i) (fun u => (hω.2.1 u).1 i) a b

theorem IGood.ii_α (hω : IGood K Z β α N B C s t ω) (i j : Fin d) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => α u.toNNReal ω i j) volume a b :=
  intervalIntegrable_toNNReal_path (g := fun u => α u ω i j) (fun u => (hω.2.1 u).2 i j) a b

theorem IGood.integrableOn_ctrl (hω : IGood K Z β α N B C s t ω) (u : ℝ≥0) :
    IntegrableOn (fun v : ℝ => ctrl β α v.toNNReal ω) (Ioc 0 u) := by
  unfold ctrl
  refine Integrable.add (integrable_finsetSum _ fun i _ => ((hω.2.1 u).1 i).abs)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ((hω.2.1 u).2 i j).abs)

theorem IGood.ii_ctrl (hω : IGood K Z β α N B C s t ω) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => ctrl β α u.toNNReal ω) volume a b :=
  intervalIntegrable_toNNReal_path (g := fun u => ctrl β α u ω) hω.integrableOn_ctrl a b

theorem ctrlI_nonneg (u : ℝ≥0) (ω : Ω) : 0 ≤ ctrlI β α u ω :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ => ctrl_nonneg _ _

theorem IGood.C_nonneg (hω : IGood K Z β α N B C s t ω) : 0 ≤ C :=
  (ctrlI_nonneg 0 ω).trans (hω.2.2 0)

theorem IGood.ctrlI_sub (hω : IGood K Z β α N B C s t ω) {a b : ℝ≥0} (hab : a ≤ b) :
    ctrlI β α b ω - ctrlI β α a ω = ∫ v in (a : ℝ)..b, ctrl β α v.toNNReal ω :=
  setIntegral_Ioc_sub hω.ii_ctrl (NNReal.coe_nonneg a) (by exact_mod_cast hab)

theorem IGood.ctrlI_mono (hω : IGood K Z β α N B C s t ω) {a b : ℝ≥0} (hab : a ≤ b) :
    ctrlI β α a ω ≤ ctrlI β α b ω := by
  have := hω.ctrlI_sub hab
  have h0 : 0 ≤ ∫ v in (a : ℝ)..b, ctrl β α v.toNNReal ω :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hab) fun _ _ => ctrl_nonneg _ _
  linarith

theorem IGood.continuous_ctrlI (hω : IGood K Z β α N B C s t ω) :
    Continuous fun u => ctrlI β α u ω :=
  continuous_setIntegral_Ioc (g := fun u => ctrl β α u ω) hω.integrableOn_ctrl

/-- Increment of the control over the `k`-th cell. -/
def incG (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (s t : ℝ≥0) (n k : ℕ)
    (ω : Ω) : ℝ :=
  ctrlI β α (grid s t n (k + 1)) ω - ctrlI β α (grid s t n k) ω

theorem IGood.incG_eq (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n k : ℕ) :
    incG β α s t n k ω =
      ∫ v in rgrid s t n k..rgrid s t n (k + 1), ctrl β α v.toNNReal ω := by
  rw [incG, hω.ctrlI_sub (grid_mono hst n (Nat.le_succ k)), coe_grid hst, coe_grid hst]

theorem IGood.incG_nonneg (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n k : ℕ) :
    0 ≤ incG β α s t n k ω :=
  sub_nonneg.2 (hω.ctrlI_mono (grid_mono hst n (Nat.le_succ k)))

theorem IGood.sum_incG_le (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), incG β α s t n k ω ≤ C := by
  unfold incG
  rw [Finset.sum_range_sub (fun k => ctrlI β α (grid s t n k) ω), grid_last hst, grid_zero]
  linarith [hω.2.2 t, ctrlI_nonneg (β := β) (α := α) s ω]

theorem IGood.incG_le (hω : IGood K Z β α N B C s t ω) (n k : ℕ) : incG β α s t n k ω ≤ C := by
  unfold incG; linarith [hω.2.2 (grid s t n (k + 1)), ctrlI_nonneg (β := β) (α := α)
    (grid s t n k) ω]

/-- `|∫_a^b f| ≤ ∫_a^b g` for `|f| ≤ g`. -/
theorem abs_intervalIntegral_le_of_abs_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (h : ∀ u, |f u| ≤ g u) :
    |∫ u in a..b, f u| ≤ ∫ u in a..b, g u := by
  rw [← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_of_norm_le hab
    (ae_of_all _ fun u _ => by rw [Real.norm_eq_abs]; exact h u) hg

theorem IGood.incI_eq' (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ) (i : Fin d)
    (k : ℕ) :
    incI β s t n i k ω = ∫ u in rgrid s t n k..rgrid s t n (k + 1), β u.toNNReal ω i := by
  unfold incI drI
  rw [coe_grid hst, coe_grid hst]
  exact setIntegral_Ioc_sub (hω.ii_β i)
    (by rw [← coe_grid hst]; exact NNReal.coe_nonneg _)
    (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))

theorem IGood.incJ_eq' (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ) (i j : Fin d)
    (k : ℕ) :
    incJ α s t n i j k ω = ∫ u in rgrid s t n k..rgrid s t n (k + 1), α u.toNNReal ω i j := by
  unfold incJ difJ
  rw [coe_grid hst, coe_grid hst]
  exact setIntegral_Ioc_sub (hω.ii_α i j)
    (by rw [← coe_grid hst]; exact NNReal.coe_nonneg _)
    (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))

theorem IGood.abs_incI_le' (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ) (i : Fin d)
    (k : ℕ) : |incI β s t n i k ω| ≤ incG β α s t n k ω := by
  rw [hω.incI_eq' hst, hω.incG_eq hst]
  exact abs_intervalIntegral_le_of_abs_le (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))
    (hω.ii_ctrl _ _) fun u => abs_β_le_ctrl _ _ i

theorem IGood.abs_incJ_le' (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ)
    (i j : Fin d) (k : ℕ) : |incJ α s t n i j k ω| ≤ incG β α s t n k ω := by
  rw [hω.incJ_eq' hst, hω.incG_eq hst]
  exact abs_intervalIntegral_le_of_abs_le (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))
    (hω.ii_ctrl _ _) fun u => abs_α_le_ctrl _ _ i j

theorem IGood.abs_drI_le (hω : IGood K Z β α N B C s t ω) (i : Fin d) (u : ℝ≥0) :
    |drI β i u ω| ≤ C := by
  refine le_trans ?_ (hω.2.2 u)
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hω.integrableOn_ctrl u)
    (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact abs_β_le_ctrl _ _ i)

/-- Bound on `N` at grid points. -/
theorem IGood.abs_N_grid_le' (hω : IGood K Z β α N B C s t ω) {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (n k : ℕ) (i : Fin d) :
    |N i (grid s t n k) ω| ≤ 2 * R + C := by
  rw [hω.1.2.2.2.2.1]
  have hz : ∀ u, |Z u ω i| ≤ R := fun u =>
    (le_of_eq (Real.norm_eq_abs _).symm).trans ((norm_le_pi_norm _ i).trans (hR _ (hω.1.1 u)))
  have hI := hω.abs_drI_le i (grid s t n k)
  have := hz (grid s t n k); have := hz 0
  have := abs_sub (Z (grid s t n k) ω i - Z 0 ω i) (drI β i (grid s t n k) ω)
  have := abs_sub (Z (grid s t n k) ω i) (Z 0 ω i)
  linarith

theorem IGood.abs_incN_le' (hω : IGood K Z β α N B C s t ω) {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (n k : ℕ) (i : Fin d) :
    |incN N s t n i k ω| ≤ 2 * (2 * R + C) := by
  unfold incN
  have := hω.abs_N_grid_le' hR n (k + 1) i
  have := hω.abs_N_grid_le' hR n k i
  have := abs_sub (N i (grid s t n (k + 1)) ω) (N i (grid s t n k) ω)
  linarith

/-- Sum of squared control increments. -/
def sqG (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), incG β α s t n k ω ^ 2

theorem sqG_nonneg (n : ℕ) : 0 ≤ sqG β α s t n ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem IGood.sqG_le_of (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ) {η : ℝ}
    (hη : ∀ k < n + 1, incG β α s t n k ω ≤ η) : sqG β α s t n ω ≤ η * C := by
  unfold sqG
  calc ∑ k ∈ Finset.range (n + 1), incG β α s t n k ω ^ 2
      ≤ ∑ k ∈ Finset.range (n + 1), η * incG β α s t n k ω :=
        Finset.sum_le_sum fun k hk => by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hη k (Finset.mem_range.1 hk))
            (hω.incG_nonneg hst n k)
    _ = η * ∑ k ∈ Finset.range (n + 1), incG β α s t n k ω := by rw [Finset.mul_sum]
    _ ≤ η * C := by
        have h0 : 0 ≤ η := (hω.incG_nonneg hst n 0).trans (hη 0 (Nat.succ_pos n))
        exact mul_le_mul_of_nonneg_left (hω.sum_incG_le hst n) h0

theorem IGood.sqG_le (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ) :
    sqG β α s t n ω ≤ C * C :=
  hω.sqG_le_of hst n fun k _ => hω.incG_le n k

/-- `Σ_k (ΔG_k)² → 0` along every good path. -/
theorem IGood.tendsto_sqG (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) :
    Tendsto (fun n => sqG β α s t n ω) atTop (𝓝 0) := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hz : ContinuousOn (fun u : ℝ => ctrlI β α u.toNNReal ω) (Icc (s : ℝ) t) :=
    (hω.continuous_ctrlI.comp continuous_real_toNNReal).continuousOn
  have hC := hω.C_nonneg
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : 0 < ε / (2 * (C + 1)) := by positivity
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_mesh_le hst' hz hη)
  refine ⟨M, fun n hn => ?_⟩
  have hle : ∀ k < n + 1, incG β α s t n k ω ≤ ε / (2 * (C + 1)) := by
    intro k hk
    have := hM n hn k hk (rgrid s t n (k + 1)) ⟨rgrid_mono hst' n (Nat.le_succ k), le_rfl⟩
    rw [toNNReal_rgrid hst, toNNReal_rgrid hst, Real.dist_eq] at this
    exact (le_abs_self _).trans this
  have h1 := hω.sqG_le_of hst n hle
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sqG_nonneg n)]
  have : ε / (2 * (C + 1)) * C < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end Pathwise

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
