module

public import BlockBand.SourceProcess.ComplexUnique.LocSol

/-!
# Bounds for the complex clauses stopped at the exit from a relatively compact domain

For an open `W` with compact closure and a continuous real path `Y`, the complex compensated
coordinates `cC`, products `cB`, `cB'` at `stopTime (exitTimeFrom W Y) u` are bounded by
constants depending only on `W`, the coefficients and `u` (`exists_bound_cC`; `exists_bound_cB`,
for both `cB` and `cB'`). Also the location facts `exitTimeFrom_eq_zero` (start outside `W`) and
`mem_closure_of_le_stop` (before the stop the path is in `closure W`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

variable {κ : Type*} [Fintype κ] {Ω : Type*}

theorem exitTimeFrom_eq_zero {d : ℕ} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (h0 : Y 0 ω ∉ W) : exitTimeFrom W Y ω = 0 :=
  le_antisymm (iInf₂_le 0 h0) bot_le

theorem stopTime_eq_self {θ : WithTop ℝ≥0} {s : ℝ≥0} (h : (s : WithTop ℝ≥0) ≤ θ) :
    stopTime θ s = s := by
  induction θ with
  | top => exact stopTime_top s
  | coe x => rw [stopTime_coe]; exact min_eq_left (WithTop.coe_le_coe.1 h)

theorem coe_stopTime_le (θ : WithTop ℝ≥0) (u : ℝ≥0) : (stopTime θ u : WithTop ℝ≥0) ≤ θ := by
  induction θ with
  | top => exact le_top
  | coe x => rw [stopTime_coe]; exact WithTop.coe_le_coe.2 (min_le_right _ _)

theorem stopTime_zero_left (u : ℝ≥0) : stopTime 0 u = 0 := by
  rw [show (0 : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) from rfl, stopTime_coe, min_eq_right zero_le]

theorem mem_closure_of_le_stop {d : ℕ} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hW : IsOpen W) (hc : Continuous fun t => Y t ω) (h0 : Y 0 ω ∈ W) {u s : ℝ≥0}
    (hs : s ≤ stopTime (exitTimeFrom W Y ω) u) : Y s ω ∈ closure W := by
  have h := stop_mem_closure hW hc h0 s
  rwa [stopTime_eq_self ((WithTop.coe_le_coe.2 hs).trans (coe_stopTime_le _ u))] at h

theorem norm_setIntegral_Ioc_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ≥0 → E} {B : ℝ} (hB : 0 ≤ B) {v u : ℝ≥0} (hvu : v ≤ u)
    (h : ∀ s ≤ v, ‖f s‖ ≤ B) : ‖∫ s in Ioc (0 : ℝ) v, f s.toNNReal‖ ≤ B * u := by
  refine (norm_setIntegral_le_of_norm_le_const (C := B) (by simp) fun s hs => ?_).trans ?_
  · refine h _ ?_
    have := Real.toNNReal_le_toNNReal hs.2
    rwa [Real.toNNReal_coe] at this
  · rw [Real.volume_real_Ioc_of_le (NNReal.coe_nonneg v), sub_zero]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hvu) hB

/-- A bound of a continuous function on the compact closure. -/
theorem exists_bound_closure {d : ℕ} {W : Set (Fin d → ℝ)} (hW : IsCompact (closure W))
    {E : Type*} [NormedAddCommGroup E] {f : (Fin d → ℝ) → E} (hf : Continuous f) :
    ∃ B, 0 ≤ B ∧ ∀ y ∈ closure W, ‖f y‖ ≤ B := by
  obtain ⟨B, hB⟩ := hW.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun y hy => (hB y hy).trans (le_max_left _ _)⟩

variable {W : Set (Fin (rDim κ) → ℝ)} {Y : ℝ≥0 → Ω → Fin (rDim κ) → ℝ}

theorem exists_bound_cC (hWo : IsOpen W) (hW : IsCompact (closure W)) {β : (κ → ℂ) → κ → ℂ}
    (hβ : Continuous β) (u : ℝ≥0) :
    ∃ C, 0 ≤ C ∧ ∀ ω, Continuous (fun t => Y t ω) → ∀ p,
      ‖cC β Y p (stopTime (exitTimeFrom W Y ω) u) ω‖ ≤ C := by
  obtain ⟨B1, hB10, hB1⟩ := exists_bound_closure hW (continuous_zOf (κ := κ))
  obtain ⟨B2, hB20, hB2⟩ := exists_bound_closure hW (hβ.comp (continuous_zOf (κ := κ)))
  refine ⟨B1 + B1 + B2 * u, by positivity, fun ω hc p => ?_⟩
  by_cases h0 : Y 0 ω ∈ W
  · set v := stopTime (exitTimeFrom W Y ω) u
    have hv : v ≤ u := stopTime_le _ u
    have hmem : ∀ s ≤ v, Y s ω ∈ closure W := fun s hs => mem_closure_of_le_stop hWo hc h0 hs
    have hz : ∀ s ≤ v, ‖zOf (Y s ω) p‖ ≤ B1 := fun s hs =>
      (norm_le_pi_norm _ p).trans (hB1 _ (hmem s hs))
    have hi := norm_setIntegral_Ioc_le (f := fun s => β (zOf (Y s ω)) p) hB20 hv
      fun s hs => (norm_le_pi_norm _ p).trans (hB2 _ (hmem s hs))
    unfold cC
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (hz v le_rfl) (hz 0 zero_le))) hi)
  · rw [exitTimeFrom_eq_zero h0, stopTime_zero_left]
    simp only [cC, sub_self, NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure,
      norm_zero]
    positivity

theorem exists_bound_cB (hWo : IsOpen W) (hW : IsCompact (closure W)) {β : (κ → ℂ) → κ → ℂ}
    (hβ : Continuous β) {Γ : (κ → ℂ) → κ → κ → ℂ} (hΓ : Continuous Γ) (u : ℝ≥0) :
    ∃ C, ∀ ω, Continuous (fun t => Y t ω) → ∀ p q,
      ‖cB β Γ Y p q (stopTime (exitTimeFrom W Y ω) u) ω‖ ≤ C ∧
      ‖cB' β Γ Y p q (stopTime (exitTimeFrom W Y ω) u) ω‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_cC (Y := Y) hWo hW hβ u
  obtain ⟨B3, hB30, hB3⟩ := exists_bound_closure hW (hΓ.comp (continuous_zOf (κ := κ)))
  refine ⟨C * C + B3 * u, fun ω hc p q => ?_⟩
  set v := stopTime (exitTimeFrom W Y ω) u
  have hv : v ≤ u := stopTime_le _ u
  have hint : ‖∫ s in Ioc (0 : ℝ) v, Γ (zOf (Y s.toNNReal ω)) p q‖ ≤ B3 * u := by
    by_cases h0 : Y 0 ω ∈ W
    · refine norm_setIntegral_Ioc_le (f := fun s => Γ (zOf (Y s ω)) p q) hB30 hv fun s hs => ?_
      exact (norm_le_pi_norm _ q).trans ((norm_le_pi_norm _ p).trans
        (hB3 _ (mem_closure_of_le_stop hWo hc h0 hs)))
    · have : v = 0 := by
        simp only [v]
        rw [exitTimeFrom_eq_zero h0, stopTime_zero_left]
      rw [this]; simp only [NNReal.coe_zero, Ioc_self, Measure.restrict_empty,
        integral_zero_measure, norm_zero]; positivity
  constructor
  · unfold cB
    refine (norm_sub_le _ _).trans (add_le_add ?_ hint)
    rw [norm_mul]; exact mul_le_mul (hC ω hc p) (hC ω hc q) (norm_nonneg _) hC0
  · unfold cB'
    refine (norm_sub_le _ _).trans (add_le_add ?_ hint)
    rw [norm_mul, norm_star]; exact mul_le_mul (hC ω hc p) (hC ω hc q) (norm_nonneg _) hC0

end BlockBand.SourceProcess.ComplexUnique
