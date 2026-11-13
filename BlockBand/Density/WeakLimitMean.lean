module

public import Mathlib

/-!
# First moments through weak convergence under a uniform second-moment bound

For probability measures `P_j → ν` weakly on a topological space with Borel sets, a continuous
`F ≥ 0` with `E_{P_j} F → L` and `sup_j E_{P_j} F² ≤ C` is `ν`-integrable with `E_ν F = L`
(truncation `min F M`, `F - min F M ≤ F²/M`, monotone convergence).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory Filter Topology
open scoped ENNReal

/-- The truncation `min F M` as a bounded continuous function (`F ≥ 0`, `M ≥ 0`). -/
def truncBCF {X : Type*} [TopologicalSpace X] {F : X → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) (M : ℝ) (hM : 0 ≤ M) : BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => min (F x) M, hF.min continuous_const⟩ M
    (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := min_le_right (F x) M
      have h2 := min_le_right (F y) M
      have h3 : 0 ≤ min (F x) M := le_min (hF0 x) hM
      have h4 : 0 ≤ min (F y) M := le_min (hF0 y) hM
      rw [abs_le]
      constructor <;> linarith)

theorem truncBCF_apply {X : Type*} [TopologicalSpace X] {F : X → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) (M : ℝ) (hM : 0 ≤ M) (x : X) :
    truncBCF hF hF0 M hM x = min (F x) M := rfl

theorem sub_min_le_sq_div {a M : ℝ} (ha : 0 ≤ a) (hM : 0 < M) : a - min a M ≤ a ^ 2 / M := by
  rcases le_total a M with h | h
  · rw [min_eq_left h, sub_self]; positivity
  · rw [min_eq_right h, le_div_iff₀ hM]
    nlinarith

/-- **Weak limits of means under a uniform second-moment bound.** -/
theorem integrable_and_integral_eq_of_tendsto {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {P : ℕ → ProbabilityMeasure X}
    {ν : ProbabilityMeasure X} (hlim : Tendsto P atTop (𝓝 ν)) {F : X → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) {L C : ℝ} (hint : ∀ j, Integrable F (P j))
    (hint2 : ∀ j, Integrable (fun x => F x ^ 2) (P j))
    (hsq : ∀ j, ∫ x, F x ^ 2 ∂(P j : Measure X) ≤ C)
    (hmean : Tendsto (fun j => ∫ x, F x ∂(P j : Measure X)) atTop (𝓝 L)) :
    Integrable F (ν : Measure X) ∧ ∫ x, F x ∂(ν : Measure X) = L := by
  have hFm : Measurable F := hF.measurable
  -- truncated means
  set M : ℕ → ℝ := fun n => (n : ℝ) + 1 with hMdef
  have hMpos : ∀ n, 0 < M n := fun n => by positivity
  set T : ℕ → BoundedContinuousFunction X ℝ := fun n => truncBCF hF hF0 (M n) (hMpos n).le
  have hTint : ∀ (Q : Measure X) [IsFiniteMeasure Q] (n : ℕ),
      Integrable (fun x => min (F x) (M n)) Q := fun Q _ n =>
    (T n).integrable Q
  set a : ℕ → ℝ := fun n => ∫ x, min (F x) (M n) ∂(ν : Measure X)
  have hTlim : ∀ n, Tendsto (fun j => ∫ x, min (F x) (M n) ∂(P j : Measure X)) atTop
      (𝓝 (a n)) := fun n =>
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (T n)
  have hup : ∀ n, a n ≤ L := fun n =>
    le_of_tendsto_of_tendsto' (hTlim n) hmean fun j =>
      integral_mono (hTint _ n) (hint j) fun x => min_le_left _ _
  have hlow : ∀ n, L - C / M n ≤ a n := by
    intro n
    have hj : ∀ j, ∫ x, F x ∂(P j : Measure X) - C / M n ≤
        ∫ x, min (F x) (M n) ∂(P j : Measure X) := by
      intro j
      have h1 : ∫ x, F x ∂(P j : Measure X) - ∫ x, min (F x) (M n) ∂(P j : Measure X) ≤
          ∫ x, F x ^ 2 / M n ∂(P j : Measure X) := by
        rw [← integral_sub (hint j) (hTint _ n)]
        exact integral_mono ((hint j).sub (hTint _ n)) ((hint2 j).div_const _)
          fun x => sub_min_le_sq_div (hF0 x) (hMpos n)
      have h2 : ∫ x, F x ^ 2 / M n ∂(P j : Measure X) ≤ C / M n := by
        rw [integral_div]
        exact div_le_div_of_nonneg_right (hsq j) (hMpos n).le
      linarith
    exact le_of_tendsto_of_tendsto' (hmean.sub_const _) (hTlim n) hj
  -- `a n → L`
  have haL : Tendsto a atTop (𝓝 L) := by
    have hC : Tendsto (fun n => L - C / M n) atTop (𝓝 L) := by
      have : Tendsto (fun n : ℕ => C / M n) atTop (𝓝 0) := by
        have hM : Tendsto M atTop atTop :=
          tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        exact hM.const_div_atTop C
      simpa using tendsto_const_nhds.sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hC tendsto_const_nhds hlow hup
  -- integrability of `F` under `ν`
  have hmono : ∀ x, Monotone fun n => min (F x) (M n) := fun x n m hnm =>
    min_le_min le_rfl (by
      simp only [hMdef]
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith)
  have hpt : ∀ x, Tendsto (fun n => min (F x) (M n)) atTop (𝓝 (F x)) := by
    intro x
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (F x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have : F x ≤ M n := by
      simp only [hMdef]
      have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact (min_eq_left this).symm
  have hlin : ∫⁻ x, ENNReal.ofReal (F x) ∂(ν : Measure X) ≤ ENNReal.ofReal L := by
    have hsup : (fun x => ENNReal.ofReal (F x)) =
        fun x => ⨆ n, ENNReal.ofReal (min (F x) (M n)) := by
      funext x
      apply le_antisymm
      · obtain ⟨n₀, hn₀⟩ := exists_nat_ge (F x)
        refine le_iSup_of_le n₀ (ENNReal.ofReal_le_ofReal ?_)
        rw [min_eq_left (by simp only [hMdef]; linarith)]
      · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    rw [hsup, lintegral_iSup (f := fun n x => ENNReal.ofReal (min (F x) (M n)))
      (fun n => ENNReal.measurable_ofReal.comp (hFm.min measurable_const))
      (fun n m hnm x => ENNReal.ofReal_le_ofReal (hmono x hnm))]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hTint _ n)
      (Eventually.of_forall fun x => le_min (hF0 x) (hMpos n).le)]
    exact ENNReal.ofReal_le_ofReal (hup n)
  have hFint : Integrable F (ν : Measure X) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF0)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hFint, ?_⟩
  have hconv := integral_tendsto_of_tendsto_of_monotone (μ := (ν : Measure X))
    (f := fun n x => min (F x) (M n)) (fun n => hTint _ n) hFint
    (Eventually.of_forall hmono) (Eventually.of_forall hpt)
  exact tendsto_nhds_unique hconv haL

end BlockBand.Density
