module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeFinitePath
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeAdaptedLimit
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Almost-sure uniform convergence of the finite processes

Consecutive finite-grid approximants have geometrically small predictable energy differences, so
their paths have summable uniform-distance tails; by Borel–Cantelli the paths converge uniformly
on `[0, T]` almost surely, and the limit process has almost surely continuous paths.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)

/-- Consecutive approximants have geometrically small predictable energy differences. -/
theorem nativeApproximation_difference_bound
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (n : ℕ) :
    ‖(nativeFiniteApproximation μ T f n).val - (nativeFiniteApproximation μ T f (n+1)).val‖ ≤
      (1/8 : ℝ)^n := by
  have hn := (nativeFiniteApproximation_rate μ T f n).le
  have hs := (nativeFiniteApproximation_rate μ T f (n+1)).le
  have ht := dist_triangle (nativeFiniteApproximation μ T f n).val f
    (nativeFiniteApproximation μ T f (n+1)).val
  rw [dist_comm _ f] at ht
  rw [dist_eq_norm] at ht
  apply ht.trans
  apply (add_le_add hn hs).trans
  simp only [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/8) n]

/-- Consecutive path errors have summable geometric probability tails. -/
theorem nativeApproximation_path_tail
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (n : ℕ) :
    (driverLaw (κ := κ) μ) {x | (1/2 : ℝ)^n <
      ‖nativeFinitePath μ T (nativeFiniteApproximation μ T f n) x -
        nativeFinitePath μ T (nativeFiniteApproximation μ T f (n+1)) x‖} ≤
      ENNReal.ofReal ((1/16 : ℝ)^n) := by
  let δ : ℝ≥0 := (1/2 : ℝ≥0)^n
  have hd : (δ : ℝ) = (1/2 : ℝ)^n := by simp [δ]
  have ht := nativeFinitePath_maximal_tail μ T
    (nativeFiniteApproximation μ T f n) (nativeFiniteApproximation μ T f (n+1)) δ
  have he : ENNReal.ofReal
      (‖(nativeFiniteApproximation μ T f n).val - (nativeFiniteApproximation μ T f (n+1)).val‖^2) ≤
      (↑(δ^2) : ℝ≥0∞) * ENNReal.ofReal ((1/16 : ℝ)^n) := by
    have hp : ((1/8 : ℝ)^n)^2 = ((1/2 : ℝ)^n)^2 * (1/16 : ℝ)^n := by
      rw [pow_right_comm (1/8 : ℝ) n 2, pow_right_comm (1/2 : ℝ) n 2, ← mul_pow]
      norm_num
    calc
      _ ≤ ENNReal.ofReal (((1/8 : ℝ)^n)^2) := ENNReal.ofReal_le_ofReal
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (nativeApproximation_difference_bound μ T f n))
      _ = _ := by
        rw [hp, ← hd, ENNReal.ofReal_mul (sq_nonneg (δ : ℝ)), ← NNReal.coe_pow,
          ENNReal.ofReal_coe_nnreal]
  have hδ : (↑(δ^2) : ℝ≥0∞) ≠ 0 := by
    apply ENNReal.coe_ne_zero.mpr
    dsimp [δ]
    positivity
  have hb := (ENNReal.mul_le_mul_iff_right hδ ENNReal.coe_ne_top).1 (ht.trans he)
  simpa only [hd] using hb

/-- By Borel–Cantelli the finite paths converge uniformly almost surely. -/
theorem nativeApproximation_path_converges_ae
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∃ L : C(Set.Icc (0 : ℝ≥0) T, ℝ),
      Tendsto (fun n => nativeFinitePath μ T (nativeFiniteApproximation μ T f n) x) atTop (𝓝 L) := by
  have hg : Summable (fun n : ℕ => (1/16 : ℝ)^n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have he := ae_eventually_notMem (μ := driverLaw (κ := κ) μ)
    (s := fun n => {x | (1/2 : ℝ)^n <
      ‖nativeFinitePath μ T (nativeFiniteApproximation μ T f n) x -
        nativeFinitePath μ T (nativeFiniteApproximation μ T f (n+1)) x‖})
    (ne_top_of_le_ne_top hg.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum (fun n => nativeApproximation_path_tail μ T f n)))
  filter_upwards [he] with x hx
  rcases eventually_atTop.1 hx with ⟨N, hN⟩
  have hs : Summable (fun n : ℕ => (1/2 : ℝ)^(n+N)) :=
    (summable_nat_add_iff N).2 (summable_geometric_of_norm_lt_one (by norm_num))
  have hc : CauchySeq (fun n => nativeFinitePath μ T (nativeFiniteApproximation μ T f (n+N)) x) := by
    apply cauchySeq_of_dist_le_of_summable _ ?_ hs
    intro n
    have hb := le_of_not_gt (hN (n+N) (Nat.le_add_left N n))
    rw [dist_eq_norm]
    simpa only [Nat.succ_eq_add_one, Nat.add_right_comm n 1 N] using hb
  rcases cauchySeq_tendsto_of_complete hc with ⟨L, hL⟩
  exact ⟨L, (tendsto_add_atTop_iff_nat N).1 hL⟩

/-- The limit process agrees almost surely with the uniform path limit. -/
theorem nativeAdaptedLimit_continuous_ae
    (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ,
      Continuous (fun t : Set.Icc (0 : ℝ≥0) T => nativeAdaptedLimit μ T f t.val x) := by
  filter_upwards [nativeApproximation_path_converges_ae μ T f] with x hx
  rcases hx with ⟨L, hL⟩
  have he : (fun t : Set.Icc (0 : ℝ≥0) T => nativeAdaptedLimit μ T f t.val x) = L := by
    funext t
    have ht := ((continuous_eval_const t).tendsto L).comp hL
    exact ht.limUnder_eq
  rw [he]
  exact L.continuous

end BlockBand.SourceProcess.FiniteDriverCompletion
