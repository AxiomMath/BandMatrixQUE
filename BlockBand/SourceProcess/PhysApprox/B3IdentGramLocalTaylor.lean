module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# The second-order Taylor remainder of a cutoff

For `χ : ℝ → ℝ` of class `C³` with compact support, the remainder
`ρ(s, h) = χ(s + h) − χ(s) − χ'(s) h − χ''(s) h²/2` satisfies `|ρ| ≤ M h²` and `|ρ| ≤ M |h|³`
for one constant `M` (`taylor_cut`), by the mean value inequality applied twice. No measure.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open Set Metric

/-- The second-order Taylor remainder of `χ` at `s` with increment `h`. -/
def taylorRem (χ : ℝ → ℝ) (s h : ℝ) : ℝ :=
  χ (s + h) - χ s - deriv χ s * h - deriv (deriv χ) s * h ^ 2 / 2

theorem cut_data {χ : ℝ → ℝ} (h3 : ContDiff ℝ 3 χ) (hs : HasCompactSupport χ) :
    (∀ x, HasDerivAt χ (deriv χ x) x) ∧ (∀ x, HasDerivAt (deriv χ) (deriv (deriv χ) x) x) ∧
    (∀ x, HasDerivAt (deriv (deriv χ)) (deriv (deriv (deriv χ)) x) x) ∧
    (∃ C, ∀ x, ‖deriv (deriv χ) x‖ ≤ C) ∧ ∃ C, ∀ x, ‖deriv (deriv (deriv χ)) x‖ ≤ C := by
  have h1 : ContDiff ℝ 2 (deriv χ) := (h3.of_le (by norm_num) : ContDiff ℝ (2 + 1) χ).deriv'
  have h2 : ContDiff ℝ 1 (deriv (deriv χ)) :=
    (h1.of_le (by norm_num) : ContDiff ℝ (1 + 1) (deriv χ)).deriv'
  have h3' : ContDiff ℝ 0 (deriv (deriv (deriv χ))) :=
    (h2.of_le (by norm_num) : ContDiff ℝ (0 + 1) (deriv (deriv χ))).deriv'
  refine ⟨fun x => ((h3.differentiable (by norm_num)) x).hasDerivAt,
    fun x => ((h1.differentiable (by norm_num)) x).hasDerivAt,
    fun x => ((h2.differentiable (by norm_num)) x).hasDerivAt,
    h2.continuous.bounded_above_of_compact_support hs.deriv.deriv,
    h3'.continuous.bounded_above_of_compact_support hs.deriv.deriv.deriv⟩

/-- **The second-order Taylor remainder of a `C³` cutoff**: `|ρ| ≤ M h²` and `|ρ| ≤ M |h|³`. -/
theorem taylor_cut {χ : ℝ → ℝ} (h3 : ContDiff ℝ 3 χ) (hs : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s h : ℝ, |taylorRem χ s h| ≤ M * h ^ 2 ∧
      |taylorRem χ s h| ≤ M * |h| ^ 3 := by
  obtain ⟨d0, d1, d2, ⟨M2, hM2⟩, ⟨M3, hM3⟩⟩ := cut_data h3 hs
  set M := max (2 * M2) M3 with hM
  have hM2' : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0)
  have hM3' : 0 ≤ M3 := (norm_nonneg _).trans (hM3 0)
  refine ⟨M, le_max_of_le_right hM3', fun s h => ?_⟩
  set r := |h|
  have hr : 0 ≤ r := abs_nonneg h
  have hS : Convex ℝ (closedBall (0 : ℝ) r) := convex_closedBall 0 r
  have h0S : (0 : ℝ) ∈ closedBall (0 : ℝ) r := mem_closedBall_self hr
  have hhS : h ∈ closedBall (0 : ℝ) r := by simp [r]
  have huS : ∀ u ∈ closedBall (0 : ℝ) r, |u| ≤ r := fun u hu => by
    simpa [Real.dist_eq] using hu
  -- third derivative: `|χ''(s+u) − χ''(s)| ≤ M3 |u|` and `≤ 2 M2`
  have hd2 : ∀ u : ℝ, |deriv (deriv χ) (s + u) - deriv (deriv χ) s| ≤ M3 * |u| := fun u => by
    have := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := deriv (deriv χ)) (fun x _ => (d2 x).hasDerivWithinAt) (fun x _ => hM3 x)
      (mem_univ s) (mem_univ (s + u))
    simpa [Real.norm_eq_abs] using this
  have hd2' : ∀ u : ℝ, |deriv (deriv χ) (s + u) - deriv (deriv χ) s| ≤ 2 * M2 := fun u => by
    have a1 := hM2 (s + u); have a2 := hM2 s
    rw [Real.norm_eq_abs] at a1 a2
    calc _ ≤ |deriv (deriv χ) (s + u)| + |deriv (deriv χ) s| := abs_sub _ _
      _ ≤ _ := by linarith
  -- the first derivative of the remainder
  set g2 : ℝ → ℝ := fun u => deriv χ (s + u) - deriv χ s - deriv (deriv χ) s * u
  have hg2 : ∀ u, HasDerivAt g2 (deriv (deriv χ) (s + u) - deriv (deriv χ) s) u := fun u => by
    have a := HasDerivAt.comp_const_add s u (d1 (s + u))
    have b := ((hasDerivAt_id u).const_mul (deriv (deriv χ) s))
    convert (a.sub_const (deriv χ s)).sub b using 1 <;> first | (funext v; rfl) | simp
  have hg : ∀ u, HasDerivAt (fun u => taylorRem χ s u) (g2 u) u := fun u => by
    have a := HasDerivAt.comp_const_add s u (d0 (s + u))
    have b := (hasDerivAt_id u).const_mul (deriv χ s)
    have c := (((hasDerivAt_id u).mul (hasDerivAt_id u)).const_mul
      (deriv (deriv χ) s)).div_const 2
    have := ((a.sub_const (χ s)).sub b).sub c
    convert this using 1
    · funext v; simp only [taylorRem, Pi.sub_apply, Pi.mul_apply, id]; ring
    · simp only [g2, id]; ring
  have g20 : g2 0 = 0 := by simp [g2]
  have gt0 : taylorRem χ s 0 = 0 := by simp [taylorRem]
  have bg2a : ∀ u ∈ closedBall (0 : ℝ) r, |g2 u| ≤ M3 * r * r := fun u hu => by
    have := hS.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g2)
      (fun x _ => (hg2 x).hasDerivWithinAt) (fun x hx => (hd2 x).trans
        (mul_le_mul_of_nonneg_left (huS x hx) hM3')) h0S hu
    rw [g20, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (huS u hu) (mul_nonneg hM3' hr))
  have bg2b : ∀ u ∈ closedBall (0 : ℝ) r, |g2 u| ≤ 2 * M2 * r := fun u hu => by
    have := hS.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g2)
      (fun x _ => (hg2 x).hasDerivWithinAt) (fun x _ => hd2' x) h0S hu
    rw [g20, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (huS u hu) (by positivity))
  have ha := hS.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun u => taylorRem χ s u)
    (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by rw [Real.norm_eq_abs]; exact bg2a x hx)
    h0S hhS
  have hb := hS.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun u => taylorRem χ s u)
    (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by rw [Real.norm_eq_abs]; exact bg2b x hx)
    h0S hhS
  simp only [gt0, sub_zero, Real.norm_eq_abs] at ha hb
  have hr2 : h ^ 2 = r * r := by rw [← sq_abs h]; ring
  constructor
  · calc _ ≤ 2 * M2 * r * r := hb
      _ = 2 * M2 * h ^ 2 := by rw [hr2]; ring
      _ ≤ M * h ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg h)
  · calc _ ≤ M3 * r * r * r := ha
      _ = M3 * r ^ 3 := by ring
      _ ≤ M * r ^ 3 := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hr 3)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
