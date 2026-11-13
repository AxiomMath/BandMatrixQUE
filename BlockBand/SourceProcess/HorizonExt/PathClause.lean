module

public import BlockBand.SourceProcess.HorizonExt.PathInt

/-!
# The stopped clauses of a glued path

For continuous `g`, `y` with `y 0 = g r`, write `h = glue r g y`, `σ^h, σ^g, σ^y` for the trace
stops and `ι = 1{σ^g > r}`. Then for every `t`:
* `drift_path`: `pC^h_e(σ^h ∧ t) = pC^g_e((σ^g ∧ r) ∧ (t ∧ r)) + 1{r ≤ t} ι pC^y_e(σ^y ∧ (t - r))`;
* `bracket_path`: the same for `pB`, with the cross terms
  `pC^g_e(σ^g ∧ r) pC^y_{e'}(σ^y ∧ (t - r)) + pC^g_{e'}(σ^g ∧ r) pC^y_e(σ^y ∧ (t - r))`.
`pStop_le_iff`: for continuous `g`, `σ^g ≤ r` iff `g` reaches the level on `[0, r]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

variable {c : Type} [Fintype c]
variable {g y : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ} {r : ℝ≥0} {K : ℝ}

theorem pStop_le_iff (hg : Continuous g) :
    pStop g K ≤ r ↔ ∃ s ≤ r, K ≤ ((g s).1.trace).re := by
  constructor
  · intro h
    induction hs : pStop g K with
    | top => rw [hs] at h; exact absurd h (not_le.2 (WithTop.coe_lt_top r))
    | coe s =>
      rw [hs] at h
      exact ⟨s, WithTop.coe_le_coe.1 h, hit_of_pStop_eq hg hs⟩
  · rintro ⟨s, hs, h⟩
    exact (pStop_le h).trans (WithTop.coe_le_coe.2 hs)

/-- The indicator `1{σ^g > r}`. -/
def noHitInd (g : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ) (K : ℝ) (r : ℝ≥0) : ℂ :=
  if pStop g K ≤ r then 0 else 1

theorem stop_cases (hg : Continuous g) (hy : Continuous y) (h0 : y 0 = g r) {t : ℝ≥0} (hrt : r ≤ t) :
    (pStop g K ≤ r ∧ stopTime (pStop (glue r g y) K) t =
        stopTime (min (pStop g K) (r : WithTop ℝ≥0)) r) ∨
      (¬ pStop g K ≤ r ∧ stopTime (min (pStop g K) (r : WithTop ℝ≥0)) r = r ∧
        stopTime (pStop (glue r g y) K) t = r + stopTime (pStop y K) (t - r)) := by
  have hh := continuous_glue hg hy h0
  by_cases hE : pStop g K ≤ r
  · obtain ⟨s, hs, hK⟩ := (pStop_le_iff hg).1 hE
    exact Or.inl ⟨hE, (stopTime_glue_hit hrt hs hK).trans (stopTime_glue_of_le hh le_rfl)⟩
  · have hno : ∀ s ≤ r, ¬ K ≤ ((g s).1.trace).re := fun s hs hK =>
      hE ((pStop_le_iff hg).2 ⟨s, hs, hK⟩)
    exact Or.inr ⟨hE, le_pStop_of_noHit hno, stopTime_glue_noHit hy h0 hrt hno⟩

/-- **The stopped compensated coordinate of a glued path.** -/
theorem drift_path (hg : Continuous g) (hy : Continuous y) (h0 : y 0 = g r) (D0 : ℝ)
    (D : Matrix c c ℂ) (e : Fin 2 × c × c) (t : ℝ≥0) :
    pC D0 D (glue r g y) e (stopTime (pStop (glue r g y) K) t) =
      pC D0 D g e (stopTime (min (pStop g K) (r : WithTop ℝ≥0)) (min t r)) +
        if r ≤ t then noHitInd g K r * pC D0 D y e (stopTime (pStop y K) (t - r)) else 0 := by
  have hh := continuous_glue hg hy h0
  rcases lt_or_ge t r with htr | hrt
  · rw [ite_eq_right (not_le.2 htr), add_zero, min_eq_left htr.le, stopTime_glue_of_le hh htr.le,
      pC_glue_of_le D0 D e ((stopTime_le _ t).trans htr.le)]
  rw [ite_eq_left hrt, min_eq_right hrt]
  rcases stop_cases hg hy h0 (K := K) hrt with ⟨hE, hs⟩ | ⟨hE, hr, hs⟩
  · rw [hs, pC_glue_of_le D0 D e (stopTime_le _ r), noHitInd, ite_eq_left hE, zero_mul, add_zero]
  · rw [hs, hr, pC_glue_add hg hy h0, noHitInd, ite_eq_right hE, one_mul]

/-- **The stopped compensated product of a glued path.** -/
theorem bracket_path (hg : Continuous g) (hy : Continuous y) (h0 : y 0 = g r) (D0 : ℝ)
    (D : Matrix c c ℂ) (e e' : Fin 2 × c × c) (t : ℝ≥0) :
    pB D0 D (glue r g y) e e' (stopTime (pStop (glue r g y) K) t) =
      pB D0 D g e e' (stopTime (min (pStop g K) (r : WithTop ℝ≥0)) (min t r)) +
        if r ≤ t then noHitInd g K r *
          (pC D0 D g e (stopTime (min (pStop g K) (r : WithTop ℝ≥0)) r) *
              pC D0 D y e' (stopTime (pStop y K) (t - r)) +
            pC D0 D g e' (stopTime (min (pStop g K) (r : WithTop ℝ≥0)) r) *
              pC D0 D y e (stopTime (pStop y K) (t - r)) +
            pB D0 D y e e' (stopTime (pStop y K) (t - r))) else 0 := by
  have hh := continuous_glue hg hy h0
  rcases lt_or_ge t r with htr | hrt
  · rw [ite_eq_right (not_le.2 htr), add_zero, min_eq_left htr.le, stopTime_glue_of_le hh htr.le,
      pB_glue_of_le D0 D e e' ((stopTime_le _ t).trans htr.le)]
  rw [ite_eq_left hrt, min_eq_right hrt]
  rcases stop_cases hg hy h0 (K := K) hrt with ⟨hE, hs⟩ | ⟨hE, hr, hs⟩
  · rw [hs, pB_glue_of_le D0 D e e' (stopTime_le _ r), noHitInd, ite_eq_left hE, zero_mul, add_zero]
  · rw [hs, hr, pB_glue_add hg hy h0, noHitInd, ite_eq_right hE, one_mul]
    ring

end BlockBand.SourceProcess.HorizonExt
