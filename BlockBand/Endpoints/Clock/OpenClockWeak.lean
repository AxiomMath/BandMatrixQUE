module

public import BlockBand.Endpoints.Clock.CommonPortRatiosWeak
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Convergence in law of nonnegative random vectors from pointwise Laplace convergence

Support for the open-clock law theorem: the clock Laplace identity is the Laplace functional of
the measure `Σ_W`; tightness follows from the bounded first moments, and positive
continuous tests determine finite positive measures, so every subsequence has the same law.
One may equivalently apply the scalar Laplace limit to every positive linear combination of any
finite family of nonnegative tests.

* `eventually_uniform_of_antitone`: if `F_W` are antitone (coordinatewise) on `[0,N]^m`,
  converge pointwise to `G`, and `G` is continuous on the box, the convergence is uniform on the
  box (finite grid + monotonicity; no moment bound on `F_W` is needed).
* `tendsto_integral_of_tendsto_laplace`: if nonnegative random vectors `X_W` (on arbitrary
  probability spaces) have Laplace transforms `E e^{-⟨λ, X_W⟩} → E e^{-⟨λ, Y⟩}` for every
  `λ ≥ 0`, and the limit `Y ≥ 0` has finite first moments, then `E ψ(X_W) → E ψ(Y)` for every
  bounded continuous `ψ` (convergence in law). This uses the quantitative comparison
  `exists_laplace_comparison`; the first-moment hypothesis is only on the limit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock
namespace OpenClock

open MeasureTheory Set Filter Topology

/-- The box `[0, N]^m`. -/
def box (m : ℕ) (N : ℝ) : Set (Fin m → ℝ) := Set.pi univ fun _ => Icc 0 N

theorem isCompact_box (m : ℕ) (N : ℝ) : IsCompact (box m N) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- **Uniform convergence of antitone functions on a box.** -/
theorem eventually_uniform_of_antitone {m : ℕ} {N : ℝ} (hN : 0 < N)
    {F : ℕ → (Fin m → ℝ) → ℝ} {G : (Fin m → ℝ) → ℝ}
    (hmono : ∀ W (l l' : Fin m → ℝ), l ∈ box m N → l' ∈ box m N → (∀ i, l i ≤ l' i) →
      F W l' ≤ F W l)
    (hG : ContinuousOn G (box m N))
    (hpt : ∀ l ∈ box m N, Tendsto (fun W => F W l) atTop (𝓝 (G l))) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ W in atTop, ∀ l ∈ box m N, |F W l - G l| ≤ η := by
  have huc := (isCompact_box m N).uniformContinuousOn_of_continuous hG
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hUC⟩ := huc (η / 2) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (N / δ)
  have hM0 : (0 : ℝ) < M := lt_of_le_of_lt (div_nonneg hN.le hδ.le) hM
  have hMpos : 0 < M := by exact_mod_cast hM0
  have hNM : N / M < δ := by
    rw [div_lt_iff₀ hM0]; rw [div_lt_iff₀ hδ] at hM; linarith
  set g : (Fin m → Fin (M + 1)) → Fin m → ℝ := fun k i => (k i : ℝ) * (N / M) with hg
  have hgbox : ∀ k, g k ∈ box m N := by
    intro k i _
    have hk : ((k i : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (k i).2
    refine ⟨by positivity, ?_⟩
    calc ((k i : ℕ) : ℝ) * (N / M) ≤ M * (N / M) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = N := by field_simp
  have hgrid : ∀ᶠ W in atTop, ∀ k, |F W (g k) - G (g k)| ≤ η / 2 := by
    rw [Filter.eventually_all]
    intro k
    have := (Metric.tendsto_nhds.mp (hpt (g k) (hgbox k))) (η / 2) (by positivity)
    exact this.mono fun W hW => by rw [← Real.dist_eq]; exact hW.le
  filter_upwards [hgrid] with W hW l hl
  -- grid neighbours
  have hx : ∀ i, 0 ≤ l i * M / N ∧ l i * M / N ≤ M := by
    intro i
    obtain ⟨h0, h1⟩ := hl i (mem_univ i)
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hN]; nlinarith
  have hfl : ∀ i, ⌊l i * M / N⌋₊ < M + 1 := fun i =>
    Nat.lt_succ_iff.mpr (Nat.floor_le_of_le (hx i).2)
  have hce : ∀ i, ⌈l i * M / N⌉₊ < M + 1 := fun i =>
    Nat.lt_succ_iff.mpr (Nat.ceil_le.mpr (hx i).2)
  set kl : Fin m → Fin (M + 1) := fun i => ⟨⌊l i * M / N⌋₊, hfl i⟩
  set ku : Fin m → Fin (M + 1) := fun i => ⟨⌈l i * M / N⌉₊, hce i⟩
  have hscale : ∀ (r : ℝ) i, r * (N / M) - l i = (r - l i * M / N) * (N / M) := by
    intro r i; field_simp
  have hlow : ∀ i, g kl i ≤ l i ∧ l i - g kl i ≤ N / M := by
    intro i
    have h1 := Nat.floor_le (hx i).1
    have h2 := Nat.lt_floor_add_one (l i * M / N)
    have hNM0 : 0 < N / M := by positivity
    have e := hscale (⌊l i * M / N⌋₊ : ℝ) i
    simp only [hg, kl]
    constructor <;> nlinarith
  have hupp : ∀ i, l i ≤ g ku i ∧ g ku i - l i ≤ N / M := by
    intro i
    have h1 := Nat.le_ceil (l i * M / N)
    have h2 := Nat.ceil_lt_add_one (hx i).1
    have hNM0 : 0 < N / M := by positivity
    have e := hscale (⌈l i * M / N⌉₊ : ℝ) i
    simp only [hg, ku]
    constructor <;> nlinarith
  have hdl : dist (g kl) l < δ := by
    refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).mpr fun i => ?_) hNM
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [(hlow i).1])]
    exact (hlow i).2
  have hdu : dist (g ku) l < δ := by
    refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).mpr fun i => ?_) hNM
    rw [Real.dist_eq, abs_of_nonneg (by linarith [(hupp i).1])]
    exact (hupp i).2
  have hGl := hUC _ (hgbox kl) _ hl hdl
  have hGu := hUC _ (hgbox ku) _ hl hdu
  rw [Real.dist_eq] at hGl hGu
  have hF1 : F W l ≤ F W (g kl) := hmono W _ _ (hgbox kl) hl fun i => (hlow i).1
  have hF2 : F W (g ku) ≤ F W l := hmono W _ _ hl (hgbox ku) fun i => (hupp i).1
  have hk1 := hW kl
  have hk2 := hW ku
  rw [abs_lt] at hGl hGu
  rw [abs_le] at hk1 hk2 ⊢
  constructor <;> linarith [hk1.1, hk1.2, hk2.1, hk2.2, hGl.1, hGl.2, hGu.1, hGu.2]

/-- **Convergence in law from pointwise Laplace convergence** (nonnegative vectors). -/
theorem tendsto_integral_of_tendsto_laplace {m : ℕ} (Ω : ℕ → Type) [∀ W, MeasurableSpace (Ω W)]
    (P : ∀ W, Measure (Ω W)) [∀ W, IsProbabilityMeasure (P W)] (X : ∀ W, Ω W → Fin m → ℝ)
    (hXm : ∀ W, Measurable (X W)) (hX0 : ∀ W ω i, 0 ≤ X W ω i)
    {Ω' : Type} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (Y : Ω' → Fin m → ℝ) (hYm : Measurable Y) (hY0 : ∀ ω i, 0 ≤ Y ω i)
    (hYI : ∀ i, Integrable (fun ω => Y ω i) ν) {K : ℝ} (hYK : ∀ i, ∫ ω, Y ω i ∂ν ≤ K)
    (hlap : ∀ l : Fin m → ℝ, (∀ i, 0 ≤ l i) →
      Tendsto (fun W => ∫ ω, Real.exp (-∑ i, l i * X W ω i) ∂P W) atTop
        (𝓝 (∫ ω, Real.exp (-∑ i, l i * Y ω i) ∂ν)))
    (ψ : (Fin m → ℝ) → ℝ) (hψ : Continuous ψ) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) :
    Tendsto (fun W => ∫ ω, ψ (X W ω) ∂P W) atTop (𝓝 (∫ ω, ψ (Y ω) ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, N, hN1, hcmp⟩ := exists_laplace_comparison.{0, 0} m ψ hψ hM K (ε := ε / 2)
    (by positivity)
  have hN0 : 0 < N := by linarith
  set F : ℕ → (Fin m → ℝ) → ℝ := fun W l => ∫ ω, Real.exp (-∑ i, l i * X W ω i) ∂P W
  set G : (Fin m → ℝ) → ℝ := fun l => ∫ ω, Real.exp (-∑ i, l i * Y ω i) ∂ν
  have hexpm : ∀ {α : Type} [MeasurableSpace α] (Z : α → Fin m → ℝ), Measurable Z →
      ∀ l : Fin m → ℝ, Measurable (fun ω => Real.exp (-∑ i, l i * Z ω i)) := by
    intro α _ Z hZ l
    exact Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp hZ)).neg
  have hbX : ∀ W (l : Fin m → ℝ), (∀ i, 0 ≤ l i) →
      Integrable (fun ω => Real.exp (-∑ i, l i * X W ω i)) (P W) := by
    intro W l hl
    refine Integrable.of_bound (hexpm (X W) (hXm W) l).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (hX0 W ω i)
  have hmono : ∀ W (l l' : Fin m → ℝ), l ∈ box m N → l' ∈ box m N → (∀ i, l i ≤ l' i) →
      F W l' ≤ F W l := by
    intro W l l' hl hl' hll
    refine integral_mono (hbX W l' fun i => (hl' i (mem_univ i)).1)
      (hbX W l fun i => (hl i (mem_univ i)).1) fun ω => ?_
    refine Real.exp_le_exp.mpr (neg_le_neg (Finset.sum_le_sum fun i _ => ?_))
    exact mul_le_mul_of_nonneg_right (hll i) (hX0 W ω i)
  have hGc : ContinuousOn G (box m N) := by
    refine continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) (fun l _ =>
      (hexpm Y hYm l).aestronglyMeasurable) (fun l hl => Filter.Eventually.of_forall fun ω => ?_)
      (integrable_const 1) (Filter.Eventually.of_forall fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hl i (mem_univ i)).1 (hY0 ω i)
    · exact (Real.continuous_exp.comp (continuous_finsetSum _ fun i _ =>
        (continuous_apply i).mul continuous_const).neg).continuousOn
  have hunif := eventually_uniform_of_antitone hN0 hmono hGc
    (fun l hl => hlap l fun i => (hl i (mem_univ i)).1) hη
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hunif
  refine ⟨W₀, fun W hW => ?_⟩
  have h := hcmp (P W) ν inferInstance inferInstance (X W) Y (hXm W) hYm (hX0 W) hY0 hYI hYK
    fun l hl0 hlN => hW₀ W hW l fun i _ => ⟨hl0 i, hlN i⟩
  rw [Real.dist_eq]
  linarith

end OpenClock
end BlockBand.Endpoints.Clock
