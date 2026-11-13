module

public import BlockBand.SourceProcess.Stochastic.Dyson.Localize
public import BlockBand.SourceProcess.Stochastic.Dyson.B2Stops
public import BlockBand.SourceProcess.Stochastic.Dyson.B2Aux

/-!
# Dyson Brownian motion: pathwise facts on non-collision samples

On a sample `ω` where `F + G_t` has simple spectrum for all `t > 0` (`NoCollision`), and for
`s > 0`: the coordinates of `F + G_{s+u}` stay in `simpleSet N`, the state, drift and covariance
paths are continuous, and up to `dysonRho n` the compensated processes `locComp`/`locSq` built from
`stateFn` are bounded by explicit constants (`state_bounds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- Non-collision sample (clause (b1) holds at `ω`). -/
def NoCollision (N : ℕ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (F : Ω → Matrix (Fin N) (Fin N) ℂ) (ω : Ω) : Prop :=
  ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)

theorem herm_add (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian) (t : ℝ≥0)
    (ω : Ω) : (F ω + G t ω).IsHermitian :=
  (hFh ω).add (hG.hermitian t ω)

theorem stateFn_hermVec (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (q : Fin N → ℂ) (k : Fin (N + N)) (t : ℝ≥0) (ω : Ω) :
    stateFn N q k (hermVec N (F ω + G t ω)) = dysonState N q (F ω + G t ω) k := by
  unfold stateFn; rw [vecHerm_hermVec (herm_add hG hFh t ω)]

theorem hermVec_mem_simpleSet (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (u : ℝ≥0) :
    hermVec N (F ω + G (s + u) ω) ∈ simpleSet N := by
  change HasSimpleSpectrum N (vecHerm N (hermVec N (F ω + G (s + u) ω)))
  rw [vecHerm_hermVec (herm_add hG hFh _ ω)]
  exact hω _ (add_pos_of_pos_of_nonneg hs zero_le)

theorem continuous_state_path (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} (hs : 0 < s)
    {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) :
    Continuous fun u => dysonState N q (F ω + G (s + u) ω) := by
  have hp : Continuous fun u => F ω + G (s + u) ω :=
    (continuous_hermBM_add hG F ω).comp (continuous_const.add continuous_id)
  refine (continuousOn_dysonState q).comp_continuous hp fun u => ?_
  exact hω _ (add_pos_of_pos_of_nonneg hs zero_le)

theorem continuous_drift_path (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} (hs : 0 < s)
    {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) :
    Continuous fun r : ℝ => dysonStateDrift N (dysonState N q (F ω + G (s + r.toNNReal) ω)) := by
  have hp : Continuous fun r : ℝ => F ω + G (s + r.toNNReal) ω :=
    (continuous_hermBM_add hG F ω).comp (continuous_const.add continuous_real_toNNReal)
  refine (continuousOn_drift_state q).comp_continuous hp fun r => ?_
  exact hω _ (add_pos_of_pos_of_nonneg hs zero_le)

theorem continuous_cov_path (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} (hs : 0 < s)
    {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) :
    Continuous fun r : ℝ => dysonStateCov N (dysonState N q (F ω + G (s + r.toNNReal) ω)) := by
  have hp : Continuous fun r : ℝ => F ω + G (s + r.toNNReal) ω :=
    (continuous_hermBM_add hG F ω).comp (continuous_const.add continuous_real_toNNReal)
  refine (continuousOn_cov_state q).comp_continuous hp fun r => ?_
  exact hω _ (add_pos_of_pos_of_nonneg hs zero_le)

theorem abs_setIntegral_Ioc_le {f : ℝ → ℝ} {C : ℝ} (v : ℝ≥0)
    (hf : ∀ r ∈ Ioc (0 : ℝ) v, |f r| ≤ C) : |∫ r in Ioc (0 : ℝ) v, f r| ≤ C * v := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) v) (f := f)
    (by simp) (fun r hr => by rw [Real.norm_eq_abs]; exact hf r hr)
  rw [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp),
    sub_zero] at h
  exact h

/-- The localization constants. -/
def kB (N : ℕ) (q : Fin N → ℂ) : ℝ := N * qNormSq q

theorem qNormSq_nonneg (q : Fin N → ℂ) : 0 ≤ qNormSq q :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem kB_nonneg (q : Fin N → ℂ) : 0 ≤ kB N q :=
  mul_nonneg (Nat.cast_nonneg N) (qNormSq_nonneg q)

/-- **State, drift and covariance bounds up to `dysonRho n`** on non-collision samples. -/
theorem state_bounds (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} (hs : 0 < s)
    (hFh : ∀ ω, (F ω).IsHermitian) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) (n : ℕ)
    {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ dysonRho G F s n ω) :
    (∀ k, |dysonState N q (F ω + G (s + v) ω) k - dysonState N q (F ω + G (s + 0) ω) k| ≤
      N * ((n : ℝ) + 1) + kB N q) ∧
    (∀ r ∈ Ioc (0 : ℝ) v, ∀ k,
      |dysonStateDrift N (dysonState N q (F ω + G (s + r.toNNReal) ω)) k| ≤
        1 / (1 / ((n : ℝ) + 1)) + kB N q / (1 / ((n : ℝ) + 1)) ^ 2) ∧
    (∀ r ∈ Ioc (0 : ℝ) v, ∀ k l,
      |dysonStateCov N (dysonState N q (F ω + G (s + r.toNNReal) ω)) k l| ≤
        1 / N + 2 * kB N q ^ 2 / (1 / ((n : ℝ) + 1)) ^ 2) := by
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hr : ∀ r ∈ Ioc (0 : ℝ) v, 0 < r.toNNReal ∧
      ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ dysonRho G F s n ω := fun r hr =>
    ⟨Real.toNNReal_pos.mpr hr.1,
      (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hr.2)).trans hv⟩
  have hgapX : ∀ w : ℝ≥0, 0 < w → (w : WithTop ℝ≥0) ≤ dysonRho G F s n ω →
      (∀ i j : Fin N, i ≠ j → 1 / ((n : ℝ) + 1) ≤
        |dysonState N q (F ω + G (s + w) ω) (finSumFinEquiv (Sum.inl i)) -
          dysonState N q (F ω + G (s + w) ω) (finSumFinEquiv (Sum.inl j))|) ∧
      (∀ i, 0 ≤ dysonState N q (F ω + G (s + w) ω) (finSumFinEquiv (Sum.inr i))) ∧
      (∀ i, dysonState N q (F ω + G (s + w) ω) (finSumFinEquiv (Sum.inr i)) ≤ kB N q) := by
    intro w hw0 hw
    obtain ⟨h1, -, h3⟩ := bounds_le_dysonRho hG hs hFh hω q n hw
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
    · rw [dysonState_inl, dysonState_inl]; exact h1 hw0 i j hij
    · rw [dysonState_inr]; exact (h3 i).1
    · rw [dysonState_inr]; exact (h3 i).2
  refine ⟨fun k => ?_, fun r hr' k => ?_, fun r hr' k l => ?_⟩
  · obtain ⟨-, h2, h3⟩ := bounds_le_dysonRho hG hs hFh hω q n hv
    obtain ⟨-, -, h3'⟩ := bounds_le_dysonRho hG hs hFh hω q n
      (v := 0) (by simp)
    obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
    rcases k with i | i
    · rw [dysonState_inl, dysonState_inl]
      exact (h2 i).trans (le_add_of_nonneg_right (kB_nonneg q))
    · rw [dysonState_inr, dysonState_inr]
      obtain ⟨a1, a2⟩ := h3 i
      obtain ⟨b1, b2⟩ := h3' i
      have hB : kB N q = N * qNormSq q := rfl
      have hpos : (0 : ℝ) ≤ N * ((n : ℝ) + 1) := by positivity
      rw [abs_le]
      constructor <;> linarith
  · obtain ⟨g1, g2, g3⟩ := hgapX _ (hr r hr').1 (hr r hr').2
    exact abs_drift_le hδ (kB_nonneg q) g1 g2 g3 k
  · obtain ⟨g1, g2, g3⟩ := hgapX _ (hr r hr').1 (hr r hr').2
    exact abs_cov_le hδ (kB_nonneg q) g1 g2 g3 k l

end BlockBand.SourceProcess.Stochastic.Dyson
