module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Euler
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Sqrt
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bounded globally Lipschitz coefficients agreeing on a compact set

**`exists_lipCoef`**: if `b : ℝ^d → ℝ^d` and `σ : ℝ^d → ℝ^{d×d}` (Frobenius norm, local
instance) are locally Lipschitz on `U` and `K ⊆ U` is compact, there are
coefficients `c : LipCoef d` (bounded, globally Lipschitz, entrywise) with `c.b = b` and
`c.σ = σ` on `K` (Lipschitz on `K` by compactness, McShane extension of each entry, clamping).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open Set Metric
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ}

theorem abs_clamp_sub_le (M x y : ℝ) :
    |max (-M) (min M x) - max (-M) (min M y)| ≤ |x - y| := by
  have h1 : |min M x - min M y| ≤ |x - y| := by
    have := abs_min_sub_min_le_max M x M y
    simpa using this
  have h2 := abs_max_sub_max_le_max (-M) (min M x) (-M) (min M y)
  simp only [sub_self, abs_zero] at h2
  exact h2.trans (max_le (abs_nonneg _) h1)

/-- A real function Lipschitz on `K` and bounded by `M` there has a bounded globally Lipschitz
extension. -/
theorem exists_clamped_extension {f : (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)} {L : ℝ≥0}
    (hf : LipschitzOnWith L f K) {M : ℝ} (hM : ∀ x ∈ K, |f x| ≤ M) :
    ∃ g : (Fin d → ℝ) → ℝ, (∀ x y, |g x - g y| ≤ L * ‖x - y‖) ∧ (∀ x, |g x| ≤ max M 0) ∧
      EqOn f g K := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  set M' := max M 0
  refine ⟨fun x => max (-M') (min M' (g x)), fun x y => ?_, fun x => ?_, fun x hx => ?_⟩
  · refine (abs_clamp_sub_le M' (g x) (g y)).trans ?_
    rw [← Real.dist_eq, ← dist_eq_norm]
    exact hg.dist_le_mul x y
  · have hM0 : 0 ≤ M' := le_max_right _ _
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · have h1 := hM x hx
    rw [hfg hx] at h1
    have h2 : g x ≤ M' := ((abs_le.1 h1).2).trans (le_max_left _ _)
    have h3 : -M' ≤ g x := by linarith [(abs_le.1 h1).1, le_max_left M 0]
    simp only [min_eq_right h2, max_eq_right h3, hfg hx]

/-- **Bounded globally Lipschitz coefficients agreeing with `b, σ` on a compact `K ⊆ U`.** -/
theorem exists_lipCoef {b : (Fin d → ℝ) → Fin d → ℝ} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {U K : Set (Fin d → ℝ)} (hb : LocallyLipschitzOn U b) (hσ : LocallyLipschitzOn U σ)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c : LipCoef d, EqOn b c.b K ∧ EqOn σ c.σ K := by
  classical
  obtain ⟨Kb, hKb⟩ := (hb.mono hKU).exists_lipschitzOnWith_of_compact hK
  obtain ⟨Kσ, hKσ⟩ := (hσ.mono hKU).exists_lipschitzOnWith_of_compact hK
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn (hb.continuousOn.mono hKU)
  obtain ⟨Cσ, hCσ⟩ := hK.exists_bound_of_continuousOn (hσ.continuousOn.mono hKU)
  set M := max Cb Cσ
  have hbi : ∀ i, LipschitzOnWith Kb (fun x => b x i) K := fun i =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
      (dist_le_pi_dist (b x) (b y) i).trans (hKb.dist_le_mul x hx y hy)
  have hσi : ∀ i k, LipschitzOnWith Kσ (fun x => σ x i k) K := fun i k =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      refine le_trans ?_ (hKσ.dist_le_mul x hx y hy)
      rw [Real.dist_eq, dist_eq_norm]
      exact abs_entry_le_norm (σ x - σ y) i k
  have hbM : ∀ i, ∀ x ∈ K, |b x i| ≤ M := fun i x hx => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (b x) i).trans ((hCb x hx).trans (le_max_left _ _))
  have hσM : ∀ i k, ∀ x ∈ K, |σ x i k| ≤ M := fun i k x hx =>
    (abs_entry_le_norm (σ x) i k).trans ((hCσ x hx).trans (le_max_right _ _))
  choose gb hgb1 hgb2 hgb3 using fun i => exists_clamped_extension (hbi i) (hbM i)
  choose gσ hgσ1 hgσ2 hgσ3 using fun i k => exists_clamped_extension (hσi i k) (hσM i k)
  refine ⟨⟨fun x i => gb i x, fun x => Matrix.of fun i k => gσ i k x, (Kb + Kσ : ℝ≥0),
    max M 0, (Kb + Kσ).coe_nonneg, le_max_right _ _, fun x y i => ?_, fun x y i k => ?_,
    fun x i => hgb2 i x, fun x i k => hgσ2 i k x⟩, fun x hx => funext fun i => hgb3 i hx,
    fun x hx => Matrix.ext fun i k => hgσ3 i k hx⟩
  · refine (hgb1 i x y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact_mod_cast le_add_of_nonneg_right Kσ.2
  · refine (hgσ1 i k x y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact_mod_cast le_add_of_nonneg_left Kb.2

end BlockBand.SourceProcess.Stochastic.Uniqueness
