module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Path
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: exact decomposition and Riemann limit

Pathwise, on `GoodPt` (fixed `s ≤ t`), for `φ ∈ C²(U)`, `U` open, `K ⊆ U`:

* `schemeProc_sub_eq`: `X_t - X_s = T¹_n + ½ T²_n + (Riemann_n - ∫_s^t 𝓛φ) + ½ Cross_n + Rem_n`
  (exact, every `n`);
* `tendsto_riemannSum`: `Riemann_n → ∫_s^t 𝓛φ` as `n → ∞`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {Cβ Cα : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0} {ω : Ω}

theorem intervalIntegrable_finsetSum {ι : Type*} {S : Finset ι} {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun u => ∑ i ∈ S, f i u) volume a b := by
  have := IntervalIntegrable.sum S h
  convert this using 1
  funext u
  simp [Finset.sum_apply]

theorem continuous_dφ1_path (hω : GoodPt K Z β α N B s t ω) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (i : Fin d) :
    Continuous fun u : ℝ => fderiv ℝ φ (Z u.toNNReal ω) (ev i) := by
  have c1 : ContinuousOn (fderiv ℝ φ) U := hφ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have := c1.comp_continuous (hω.2.1.comp continuous_real_toNNReal) (fun u => hKU (hω.1 _))
  exact this.clm_apply continuous_const

theorem continuous_dφ2_path (hω : GoodPt K Z β α N B s t ω) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (i j : Fin d) :
    Continuous fun u : ℝ => fderiv ℝ (fderiv ℝ φ) (Z u.toNNReal ω) (ev i) (ev j) := by
  have c2 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U :=
    (hφ.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  have := c2.comp_continuous (hω.2.1.comp continuous_real_toNNReal) (fun u => hKU (hω.1 _))
  exact (this.clm_apply continuous_const).clm_apply continuous_const

theorem intervalIntegrable_gen_path (hω : GoodPt K Z β α N B s t ω)
    (hβ : ∀ t ω i, |β t ω i| ≤ Cβ) (hα : ∀ t ω i j, |α t ω i j| ≤ Cα) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => schemeGen φ Z β α u.toNNReal ω) volume a b := by
  unfold schemeGen
  refine IntervalIntegrable.add ?_ ?_
  · refine (intervalIntegrable_finsetSum (fun i _ => ?_))
    exact (hω.intervalIntegrable_β hβ i a b).mul_continuousOn
      (continuous_dφ1_path hω hU hKU hφ i).continuousOn
  · refine IntervalIntegrable.const_mul ?_ _
    refine intervalIntegrable_finsetSum (fun i _ => intervalIntegrable_finsetSum (fun j _ => ?_))
    exact (hω.intervalIntegrable_α hα i j a b).mul_continuousOn
      (continuous_dφ2_path hω hU hKU hφ i j).continuousOn

theorem toNNReal_rgrid (hst : s ≤ t) (n k : ℕ) : (rgrid s t n k).toNNReal = grid s t n k := by
  rw [← coe_grid hst, Real.toNNReal_coe]

/-- **Exact pathwise decomposition** of `X_t - X_s` along the grid. -/
theorem schemeProc_sub_eq (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    (hα : ∀ t ω i j, |α t ω i j| ≤ Cα) (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U)
    (hst : s ≤ t) (n : ℕ) :
    schemeProc φ Z β α t ω - schemeProc φ Z β α s ω =
      transform1 φ Z N s t n ω + (1 / 2) * transform2 φ Z α N s t n ω +
      (riemannSum φ Z β α s t n ω - ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) +
      (1 / 2) * crossSum φ Z β N s t n ω + remSum φ Z s t n ω := by
  have hint := intervalIntegrable_gen_path hω hβ hα hU hKU hφ
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
    rw [taylor_split φ _ _ _ _ (incZ_eq hω n k) (fun i j => incJ α s t n i j k ω)]
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
theorem tendsto_riemannSum (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    (hα : ∀ t ω i j, |α t ω i j| ≤ Cα) (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U)
    (hst : s ≤ t) :
    Tendsto (fun n => riemannSum φ Z β α s t n ω) atTop
      (𝓝 (∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω)) := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have h1 : ∀ i, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
      dφ1 φ Z s t n i k ω * incI β s t n i k ω) atTop
      (𝓝 (∫ u in (s : ℝ)..t, fderiv ℝ φ (Z u.toNNReal ω) (ev i) * β u.toNNReal ω i)) := by
    intro i
    refine (tendsto_riemann hst' (continuous_dφ1_path hω hU hKU hφ i).continuousOn
      (hω.intervalIntegrable_β hβ i _ _) (C := Cβ) (fun u _ => hβ _ _ i)).congr fun n => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [incI_eq hω hβ hst, dφ1, toNNReal_rgrid hst]
  have h2 : ∀ i j, Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
      dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω) atTop
      (𝓝 (∫ u in (s : ℝ)..t, fderiv ℝ (fderiv ℝ φ) (Z u.toNNReal ω) (ev i) (ev j) *
        α u.toNNReal ω i j)) := by
    intro i j
    refine (tendsto_riemann hst' (continuous_dφ2_path hω hU hKU hφ i j).continuousOn
      (hω.intervalIntegrable_α hα i j _ _) (C := Cα) (fun u _ => hα _ _ i j)).congr fun n => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [incJ_eq hω hα hst, dφ2, toNNReal_rgrid hst]
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
      (hω.intervalIntegrable_β hβ i _ _).continuousOn_mul
        (continuous_dφ1_path hω hU hKU hφ i).continuousOn
    have i2 : ∀ i j, IntervalIntegrable (fun u : ℝ =>
        fderiv ℝ (fderiv ℝ φ) (Z u.toNNReal ω) (ev i) (ev j) * α u.toNNReal ω i j)
        volume s t := fun i j =>
      (hω.intervalIntegrable_α hα i j _ _).continuousOn_mul
        (continuous_dφ2_path hω hU hKU hφ i j).continuousOn
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

end BlockBand.SourceProcess.Stochastic.Semimartingale
