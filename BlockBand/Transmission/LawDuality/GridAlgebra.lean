module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The strip estimate, deterministic part: the strip boundary identity

Pure real analysis for the Ethier–Kurtz strip `{a₀ ≤ s, 0 ≤ v, t − η ≤ s + v ≤ t}`
(`L = t − a₀`):
* **`strip_curve_identity`**: for a bounded jointly measurable `V`,
  `∫_0^L [V(t−r, r) − V(i(r), r)] dr − ∫_{a₀}^t [V(s, t−s) − V(s, m(s))] ds
   = ∫_{t−η}^t V(s, 0) ds − ∫_{L−η}^L V(a₀, r) dr`, `i(r) = max(a₀, t−η−r)`, `m(s) = max(0, t−η−s)`
  (the two curve terms on `s + v = t` and on `s + v = t − η` cancel by `s = t − r`);
* **`abs_integral_shift_le`**: `|∫_0^L 1{T ≤ r}(g(t−r) − g(t−η−r)) dr| ≤ 2η` for `|g| ≤ 1`
  (the stopped forward steps after `τ` telescope);
* `abs_integral_left_sub_le`: `|∫_{x−η}^x f − ηf(x)| ≤ εη` for small `η` (left continuity).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set intervalIntegral

theorem intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := B)).mono_fun hf.aestronglyMeasurable
    (ae_of_all _ fun x => by
      show ‖f x‖ ≤ ‖B‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact (hB x).trans (le_abs_self _))

/-- **The strip boundary identity.** -/
theorem strip_curve_identity {V : ℝ → ℝ → ℝ} (hV : Measurable (Function.uncurry V)) {B : ℝ}
    (hB : ∀ s r, |V s r| ≤ B) {t a0 η : ℝ} (hη : 0 ≤ η) (hηL : η ≤ t - a0) :
    (∫ r in (0 : ℝ)..t - a0, (V (t - r) r - V (max a0 (t - η - r)) r)) -
        ∫ s in a0..t, (V s (t - s) - V s (max 0 (t - η - s))) =
      (∫ s in t - η..t, V s 0) - ∫ r in t - a0 - η..t - a0, V a0 r := by
  have hm : ∀ {f g : ℝ → ℝ}, Measurable f → Measurable g → Measurable fun r => V (f r) (g r) :=
    fun hf hg => hV.comp (hf.prodMk hg)
  have ii : ∀ {f g : ℝ → ℝ}, Measurable f → Measurable g → ∀ a b : ℝ,
      IntervalIntegrable (fun r => V (f r) (g r)) volume a b :=
    fun hf hg a b => intervalIntegrable_of_bdd (hm hf hg) (fun r => hB _ _) a b
  have mc : ∀ c : ℝ, Measurable fun _ : ℝ => c := fun c => measurable_const
  have mid : Measurable fun r : ℝ => r := measurable_id
  have msub : ∀ c : ℝ, Measurable fun r : ℝ => c - r := fun c => measurable_const.sub measurable_id
  have mmax : ∀ c d : ℝ, Measurable fun r : ℝ => max c (d - r) := fun c d =>
    measurable_const.max (msub d)
  -- curve `s + v = t`
  have h1 : ∫ r in (0 : ℝ)..t - a0, V (t - r) r = ∫ s in a0..t, V s (t - s) := by
    have := intervalIntegral.integral_comp_sub_left (fun s => V s (t - s)) (a := 0) (b := t - a0) t
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  -- curve `s + v = t − η`
  have h2 : ∫ r in (0 : ℝ)..t - a0 - η, V (t - η - r) r =
      ∫ s in a0..t - η, V s (t - η - s) := by
    have := intervalIntegral.integral_comp_sub_left (fun s => V s (t - η - s)) (a := 0)
      (b := t - a0 - η) (t - η)
    simp only [sub_sub_cancel, sub_zero, show t - η - (t - a0 - η) = a0 by ring] at this
    exact this
  have h3 : ∫ r in (0 : ℝ)..t - a0, V (max a0 (t - η - r)) r =
      (∫ r in (0 : ℝ)..t - a0 - η, V (t - η - r) r) + ∫ r in t - a0 - η..t - a0, V a0 r := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := t - a0 - η)
      (ii (mmax a0 (t - η)) mid _ _) (ii (mmax a0 (t - η)) mid _ _)]
    congr 1
    · refine integral_congr fun r hr => ?_
      rw [uIcc_of_le (by linarith)] at hr
      simp only [max_eq_right (show a0 ≤ t - η - r by linarith [hr.2])]
    · refine integral_congr fun r hr => ?_
      rw [uIcc_of_le (by linarith)] at hr
      simp only [max_eq_left (show t - η - r ≤ a0 by linarith [hr.1])]
  have h4 : ∫ s in a0..t, V s (max 0 (t - η - s)) =
      (∫ s in a0..t - η, V s (t - η - s)) + ∫ s in t - η..t, V s 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := t - η)
      (ii mid (mmax 0 (t - η)) _ _) (ii mid (mmax 0 (t - η)) _ _)]
    congr 1
    · refine integral_congr fun r hr => ?_
      rw [uIcc_of_le (by linarith)] at hr
      simp only [max_eq_right (show (0 : ℝ) ≤ t - η - r by linarith [hr.2])]
    · refine integral_congr fun r hr => ?_
      rw [uIcc_of_le (by linarith)] at hr
      simp only [max_eq_left (show t - η - r ≤ 0 by linarith [hr.1])]
  rw [integral_sub (ii (msub t) mid _ _) (ii (mmax a0 (t - η)) mid _ _),
    integral_sub (ii mid (msub t) _ _) (ii mid (mmax 0 (t - η)) _ _), h1, h3, h4, h2]
  ring

theorem abs_integral_le_of_abs_le {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, |f x| ≤ C) : |∫ x in a..b, f x| ≤ C * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := C)
    (f := f) fun x hx => by
      rw [uIoc_of_le hab] at hx; exact h x ⟨hx.1.le, hx.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
  exact this

/-- `∫_a^b g − ∫_{a−η}^{b−η} g = ∫_{b−η}^b g − ∫_{a−η}^a g`. -/
theorem integral_sub_shift {g : ℝ → ℝ} (hg : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (a b η : ℝ) :
    (∫ s in a..b, g s) - ∫ s in a - η..b - η, g s =
      (∫ s in b - η..b, g s) - ∫ s in a - η..a, g s := by
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hg (a - η) a) (hg a b)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hg (a - η) (b - η)) (hg (b - η) b)
  linarith

/-- **The stopped forward steps telescope.** -/
theorem abs_integral_shift_le {g : ℝ → ℝ} (hg : Measurable g) (hg1 : ∀ s, |g s| ≤ 1) {T t L η : ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hη : 0 ≤ η) :
    |∫ r in (0 : ℝ)..L, (if T ≤ r then g (t - r) - g (t - η - r) else 0)| ≤ 2 * η := by
  have ii := intervalIntegrable_of_bdd hg hg1
  set c := min T L with hc
  have hc0 : 0 ≤ c := le_min hT hL
  have hcL : c ≤ L := min_le_right _ _
  have hmG : Measurable fun r => g (t - r) - g (t - η - r) :=
    (hg.comp (measurable_const.sub measurable_id)).sub (hg.comp (measurable_const.sub measurable_id))
  have hG2 : ∀ r, |g (t - r) - g (t - η - r)| ≤ 2 := fun r => by
    have := abs_sub (g (t - r)) (g (t - η - r)); linarith [hg1 (t - r), hg1 (t - η - r)]
  have hiG : ∀ a b : ℝ, IntervalIntegrable (fun r => g (t - r) - g (t - η - r)) volume a b :=
    intervalIntegrable_of_bdd hmG hG2
  have hmI : Measurable fun r => if T ≤ r then g (t - r) - g (t - η - r) else 0 :=
    Measurable.ite measurableSet_Ici hmG measurable_const
  have hiI : ∀ a b : ℝ, IntervalIntegrable
      (fun r => if T ≤ r then g (t - r) - g (t - η - r) else 0) volume a b :=
    intervalIntegrable_of_bdd hmI (fun r => by
      split_ifs
      · exact hG2 r
      · simp)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hiI 0 c) (hiI c L)
  have hz : ∫ r in (0 : ℝ)..c, (if T ≤ r then g (t - r) - g (t - η - r) else 0) = 0 := by
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ T := by
      rw [ae_iff]; simp
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    filter_upwards [hne] with r hr hrI
    rw [uIoc_of_le hc0] at hrI
    have : r < T := lt_of_le_of_ne (hrI.2.trans (min_le_left _ _)) hr
    simp [not_le.2 this]
  have hrest : ∫ r in c..L, (if T ≤ r then g (t - r) - g (t - η - r) else 0) =
      ∫ r in c..L, (g (t - r) - g (t - η - r)) := by
    rcases le_total T L with hTL | hLT
    · refine integral_congr fun r hr => ?_
      rw [uIcc_of_le hcL] at hr
      simp only [hc, min_eq_left hTL] at hr
      simp [hr.1]
    · have : c = L := min_eq_right hLT
      rw [this, integral_same, integral_same]
  have hA : IntervalIntegrable (fun r => g (t - r)) volume c L :=
    intervalIntegrable_of_bdd (hg.comp (measurable_const.sub measurable_id)) (fun r => hg1 _) c L
  have hB : IntervalIntegrable (fun r => g (t - η - r)) volume c L :=
    intervalIntegrable_of_bdd (hg.comp (measurable_const.sub measurable_id)) (fun r => hg1 _) c L
  rw [← hsplit, hz, zero_add, hrest, intervalIntegral.integral_sub hA hB,
    intervalIntegral.integral_comp_sub_left (fun r => g r) t,
    intervalIntegral.integral_comp_sub_left (fun r => g r) (t - η)]
  have e := integral_sub_shift ii (t - L) (t - c) η
  rw [show t - η - L = t - L - η by ring, show t - η - c = t - c - η by ring, e]
  have b1 := abs_integral_le_of_abs_le (show t - c - η ≤ t - c by linarith)
    (fun s _ => hg1 s)
  have b2 := abs_integral_le_of_abs_le (show t - L - η ≤ t - L by linarith)
    (fun s _ => hg1 s)
  have := abs_sub (∫ s in t - c - η..t - c, g s) (∫ s in t - L - η..t - L, g s)
  linarith

/-- **Left averages converge** (quantitative form). -/
theorem abs_integral_left_sub_le {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ η, 0 < η → η < δ →
      IntervalIntegrable f volume (x - η) x → |(∫ s in x - η..x, f s) - η * f x| ≤ ε * η := by
  obtain ⟨δ, hδ, hfd⟩ := Metric.continuousAt_iff.1 hf ε hε
  refine ⟨δ, hδ, fun η hη hηδ hi => ?_⟩
  have e : (∫ s in x - η..x, f s) - η * f x = ∫ s in x - η..x, (f s - f x) := by
    rw [integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [e]
  have := abs_integral_le_of_abs_le (f := fun s => f s - f x) (C := ε)
    (show x - η ≤ x by linarith) fun s hs => by
      have : dist s x < δ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]; linarith [hs.1]
      exact (hfd this).le
  simpa using this

end BlockBand.Transmission.LawDuality
