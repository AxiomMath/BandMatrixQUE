module

public import BlockBand.SourceProcess.HorizonExt.PathStop
public import BlockBand.SourceProcess.BornRestart.Path

/-!
# Compensated coordinates of a glued path

`pC D₀ 𝖣 p e t` and `pB D₀ 𝖣 p e e' t` are the compensated coordinate and the compensated
product of one path (`gramCompensated D₀ 𝖣 G e t ω = pC D₀ 𝖣 (G · ω) e t` by `rfl`). For
continuous `g`, `y` with `y 0 = g r`:
* `integral_glue`: `∫_{(0, r+u]} φ(glue) = ∫_{(0, r]} φ(g) + ∫_{(0, u]} φ(y)`;
* up to `r` the glued path has the coordinates of `g` (`pC_glue_of_le`, `pB_glue_of_le`);
* after `r` they split: `pC (r + u) = pC^g(r) + pC^y(u)` and
  `pB (r + u) = pB^g(r) + pC^g_e(r) pC^y_{e'}(u) + pC^g_{e'}(r) pC^y_e(u) + pB^y(u)`;
* `exists_pC_bound`: if `g` is feasible on `[0, r]` and below the trace level `K` there,
  `|pC^g_e(r)|` is bounded by a constant depending only on `D₀, 𝖣, K, r, e`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open MeasureTheory Set BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal

variable {c : Type} [Fintype c] [DecidableEq c]

/-- The compensated coordinate of one path. -/
def pC (D0 : ℝ) (D : Matrix c c ℂ) (p : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ) (e : Fin 2 × c × c)
    (t : ℝ≥0) : ℂ :=
  gramEntry e (p t) - gramEntry e (p 0) - ∫ s in Ioc (0 : ℝ) t, gramDriftEntry D0 D e (p s.toNNReal)

/-- The compensated product of one path. -/
def pB (D0 : ℝ) (D : Matrix c c ℂ) (p : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ)
    (e e' : Fin 2 × c × c) (t : ℝ≥0) : ℂ :=
  pC D0 D p e t * pC D0 D p e' t - ∫ s in Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (p s.toNNReal)

variable {g y : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ} {r : ℝ≥0}

omit [Fintype c] [DecidableEq c] in
theorem integrableOn_Ioc_comp {φ : Matrix c c ℂ × Matrix c c ℂ → ℂ} (hφ : Continuous φ)
    {p : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ} (hp : Continuous p) (a b : ℝ) :
    IntegrableOn (fun s : ℝ => φ (p s.toNNReal)) (Ioc a b) :=
  ((hφ.comp (hp.comp continuous_real_toNNReal)).continuousOn.integrableOn_compact
    isCompact_Icc).mono_set Ioc_subset_Icc_self

omit [Fintype c] [DecidableEq c] in
theorem integral_glue_of_le {φ : Matrix c c ℂ × Matrix c c ℂ → ℂ} {v : ℝ≥0} (hv : v ≤ r) :
    ∫ s in Ioc (0 : ℝ) v, φ (glue r g y s.toNNReal) = ∫ s in Ioc (0 : ℝ) v, φ (g s.toNNReal) :=
  setIntegral_congr_fun measurableSet_Ioc fun s hs => by
    rw [glue_of_le ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans hv)]

omit [Fintype c] [DecidableEq c] in
theorem integral_glue (hg : Continuous g) (hy : Continuous y) (h0 : y 0 = g r)
    {φ : Matrix c c ℂ × Matrix c c ℂ → ℂ} (hφ : Continuous φ) (u : ℝ≥0) :
    ∫ s in Ioc (0 : ℝ) (r + u : ℝ≥0), φ (glue r g y s.toNNReal) =
      (∫ s in Ioc (0 : ℝ) r, φ (g s.toNNReal)) + ∫ s in Ioc (0 : ℝ) u, φ (y s.toNNReal) := by
  have hh := continuous_glue hg hy h0
  rw [NNReal.coe_add, ← Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg r) (le_add_of_nonneg_right (NNReal.coe_nonneg u)),
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (integrableOn_Ioc_comp hφ hh _ _) (integrableOn_Ioc_comp hφ hh _ _),
    integral_glue_of_le le_rfl]
  congr 1
  rw [← intervalIntegral.integral_of_le (le_add_of_nonneg_right (NNReal.coe_nonneg u)),
    ← intervalIntegral.integral_of_le (NNReal.coe_nonneg u)]
  have e := intervalIntegral.integral_comp_add_right
    (fun s : ℝ => φ (glue r g y s.toNNReal)) (a := 0) (b := (u : ℝ)) (r : ℝ)
  rw [zero_add, add_comm (u : ℝ)] at e
  rw [← e, intervalIntegral.integral_of_le (NNReal.coe_nonneg u),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg u)]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [Real.toNNReal_add hs.1.le (NNReal.coe_nonneg r), Real.toNNReal_coe, add_comm, glue_add h0]

omit [DecidableEq c] in
theorem pC_glue_of_le (D0 : ℝ) (D : Matrix c c ℂ) (e : Fin 2 × c × c) {v : ℝ≥0} (hv : v ≤ r) :
    pC D0 D (glue r g y) e v = pC D0 D g e v := by
  simp only [pC, glue_of_le hv, glue_of_le (zero_le : (0 : ℝ≥0) ≤ r), integral_glue_of_le hv]

omit [DecidableEq c] in
theorem pB_glue_of_le (D0 : ℝ) (D : Matrix c c ℂ) (e e' : Fin 2 × c × c) {v : ℝ≥0}
    (hv : v ≤ r) : pB D0 D (glue r g y) e e' v = pB D0 D g e e' v := by
  simp only [pB, pC_glue_of_le D0 D _ hv, integral_glue_of_le hv]

omit [DecidableEq c] in
theorem pC_glue_add (hg : Continuous g) (hy : Continuous y) (h0 : y 0 = g r) (D0 : ℝ)
    (D : Matrix c c ℂ) (e : Fin 2 × c × c) (u : ℝ≥0) :
    pC D0 D (glue r g y) e (r + u) = pC D0 D g e r + pC D0 D y e u := by
  simp only [pC, glue_add h0, glue_of_le (zero_le : (0 : ℝ≥0) ≤ r),
    integral_glue hg hy h0 (continuous_gramDriftEntry D0 D e) u, h0]
  ring

omit [DecidableEq c] in
theorem pB_glue_add (hg : Continuous g) (hy : Continuous y) (h0 : y 0 = g r) (D0 : ℝ)
    (D : Matrix c c ℂ) (e e' : Fin 2 × c × c) (u : ℝ≥0) :
    pB D0 D (glue r g y) e e' (r + u) = pB D0 D g e e' r + pC D0 D g e r * pC D0 D y e' u +
      pC D0 D g e' r * pC D0 D y e u + pB D0 D y e e' u := by
  simp only [pB, pC_glue_add hg hy h0, integral_glue hg hy h0 (continuous_gramCovEntry D0 D e e') u]
  ring

/-- **Bound on `pC^g_e(r)` below the trace level.** -/
theorem exists_pC_bound (D0 : ℝ) (D : Matrix c c ℂ) (K : ℝ) (r : ℝ≥0) (e : Fin 2 × c × c) :
    ∃ C, ∀ g : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ, (∀ s ≤ r, GramFeasible D (g s)) →
      (∀ s ≤ r, ¬ K ≤ ((g s).1.trace).re) → ‖pC D0 D g e r‖ ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := BornRestart.exists_bound_of_continuous (continuous_gramEntry (c := c) e)
    (max K 0)
  obtain ⟨C2, hC2, h2⟩ := BornRestart.exists_bound_of_continuous
    (continuous_gramDriftEntry (c := c) D0 D e) (max K 0)
  refine ⟨2 * C1 + C2 * r, fun g hf hK => ?_⟩
  have hR : ∀ s ≤ r, ‖toGramReal (g s)‖ ≤ max K 0 := fun s hs =>
    (norm_toGramReal_le_of_feasible (hf s hs)).trans ((not_le.1 (hK s hs)).le.trans
      (le_max_left _ _))
  have hint : ‖∫ s in Ioc (0 : ℝ) r, gramDriftEntry D0 D e (g s.toNNReal)‖ ≤
      C2 * volume.real (Ioc (0 : ℝ) r) := norm_setIntegral_le_of_norm_le_const (by simp)
    fun s hs => h2 _ (hR _ (Real.toNNReal_le_iff_le_coe.2 hs.2))
  rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg _)] at hint
  have a1 := h1 _ (hR r le_rfl)
  have a2 := h1 _ (hR 0 (zero_le))
  calc ‖pC D0 D g e r‖ ≤ ‖gramEntry e (g r)‖ + ‖gramEntry e (g 0)‖ +
        ‖∫ s in Ioc (0 : ℝ) r, gramDriftEntry D0 D e (g s.toNNReal)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 2 * C1 + C2 * r := by linarith

end BlockBand.SourceProcess.HorizonExt
