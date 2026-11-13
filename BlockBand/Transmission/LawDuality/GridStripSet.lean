module

public import BlockBand.Transmission.LawDuality.GridAlgebra
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Duality strip: the strip `S_η` and its Fubini bookkeeping

The strip `S_η = {a₀ ≤ s, 0 ≤ v, t − η ≤ s + v ≤ t}`, its dual and forward fibres, and the
bound `|∫∫_{S_η} f| ≤ C(t − a₀)η` for `|f| ≤ C` on the strip.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set intervalIntegral

/-- The strip `{a₀ ≤ s, 0 ≤ v, t − η ≤ s + v ≤ t}`. -/
def stripSet (a0 t η : ℝ) : Set (ℝ × ℝ) :=
  {q | a0 ≤ q.1 ∧ 0 ≤ q.2 ∧ t - η ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ t}

theorem measurableSet_stripSet (a0 t η : ℝ) : MeasurableSet (stripSet a0 t η) := by
  have h1 : Measurable fun q : ℝ × ℝ => q.1 + q.2 := measurable_fst.add measurable_snd
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_const h1).inter (measurableSet_le h1 measurable_const)))

theorem stripSet_subset (a0 t η : ℝ) : stripSet a0 t η ⊆ Icc a0 t ×ˢ Icc 0 (t - a0) :=
  fun q hq => ⟨⟨hq.1, by linarith [hq.2.1, hq.2.2.2]⟩, ⟨hq.2.1, by linarith [hq.1, hq.2.2.2]⟩⟩

theorem mem_stripSet_dual {a0 t η s v : ℝ} (hs : a0 ≤ s) :
    (s, v) ∈ stripSet a0 t η ↔ v ∈ Icc (max 0 (t - η - s)) (t - s) := by
  simp only [stripSet, mem_ofPred_eq, mem_Icc, max_le_iff]
  constructor
  · rintro ⟨-, h1, h2, h3⟩; exact ⟨⟨h1, by linarith⟩, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨hs, h1, by linarith, by linarith⟩

theorem mem_stripSet_fwd {a0 t η u r : ℝ} (hr : 0 ≤ r) :
    (u, r) ∈ stripSet a0 t η ↔ u ∈ Icc (max a0 (t - η - r)) (t - r) := by
  simp only [stripSet, mem_ofPred_eq, mem_Icc, max_le_iff]
  constructor
  · rintro ⟨h0, -, h2, h3⟩; exact ⟨⟨h0, by linarith⟩, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, hr, by linarith, by linarith⟩

theorem notMem_stripSet_dual {a0 t η s v : ℝ} (hs : s ∉ Icc a0 t) : (s, v) ∉ stripSet a0 t η :=
  fun h => hs (stripSet_subset a0 t η h).1

theorem notMem_stripSet_fwd {a0 t η u r : ℝ} (hr : r ∉ Icc 0 (t - a0)) :
    (u, r) ∉ stripSet a0 t η :=
  fun h => hr (stripSet_subset a0 t η h).2

/-- A dual fibre integral is the integral of the strip indicator. -/
theorem integral_fiber_dual (f : ℝ × ℝ → ℝ) {a0 t η s : ℝ} (hs : a0 ≤ s) (hst : s ≤ t)
    (hη : 0 ≤ η) :
    ∫ v in max 0 (t - η - s)..t - s, f (s, v) =
      ∫ v, (stripSet a0 t η).indicator f (s, v) := by
  have hle : max 0 (t - η - s) ≤ t - s := max_le (by linarith) (by linarith)
  rw [intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  by_cases hv : v ∈ Icc (max 0 (t - η - s)) (t - s)
  · rw [indicator_of_mem hv]; exact (indicator_of_mem ((mem_stripSet_dual hs).2 hv) f).symm
  · rw [indicator_of_notMem hv]
    exact (indicator_of_notMem (fun h => hv ((mem_stripSet_dual hs).1 h)) f).symm

/-- A forward fibre integral is the integral of the strip indicator. -/
theorem integral_fiber_fwd (f : ℝ × ℝ → ℝ) {a0 t η r : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t - a0)
    (hη : 0 ≤ η) :
    ∫ u in max a0 (t - η - r)..t - r, f (u, r) =
      ∫ u, (stripSet a0 t η).indicator f (u, r) := by
  have hle : max a0 (t - η - r) ≤ t - r := max_le (by linarith) (by linarith)
  rw [intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  by_cases hu : u ∈ Icc (max a0 (t - η - r)) (t - r)
  · rw [indicator_of_mem hu]; exact (indicator_of_mem ((mem_stripSet_fwd hr).2 hu) f).symm
  · rw [indicator_of_notMem hu]
    exact (indicator_of_notMem (fun h => hu ((mem_stripSet_fwd hr).1 h)) f).symm

theorem integrable_strip {f : ℝ × ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ q, |f q| ≤ C)
    (a0 t η : ℝ) : Integrable ((stripSet a0 t η).indicator f) (volume.prod volume) := by
  refine (integrable_indicator_iff (measurableSet_stripSet a0 t η)).2 ?_
  have hfin : (volume.prod volume) (stripSet a0 t η) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (stripSet_subset a0 t η))
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
  exact Measure.integrableOn_of_bounded hfin hf.aestronglyMeasurable
    (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hC q)

/-- A bounded function supported in `[a, b]` is integrable. -/
theorem integrable_of_support_Icc {g : ℝ → ℝ} (hg : Measurable g) {C a b : ℝ}
    (hC : ∀ s, |g s| ≤ C) (hsupp : ∀ s, s ∉ Icc a b → g s = 0) : Integrable g volume := by
  have e : g = (Icc a b).indicator g := by
    funext s
    by_cases hs : s ∈ Icc a b
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs, hsupp s hs]
  rw [e]
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_
  exact Measure.integrableOn_of_bounded measure_Icc_lt_top.ne hg.aestronglyMeasurable
    (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hC q)

/-- The fibre integral over the strip is supported in `[a₀, t]` and bounded by `Cη` (the bound
is only needed off the line `v = 0`). -/
theorem norm_integral_fiber_le {a0 t η : ℝ} {f : ℝ × ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ q ∈ stripSet a0 t η, 0 < q.2 → |f q| ≤ C) (hη : 0 ≤ η) (s : ℝ) :
    ‖∫ v, (stripSet a0 t η).indicator f (s, v)‖ ≤ (Icc a0 t).indicator (fun _ => C * η) s := by
  by_cases hs : s ∈ Icc a0 t
  · rw [indicator_of_mem hs, ← integral_fiber_dual f hs.1 hs.2 hη]
    have hle : max 0 (t - η - s) ≤ t - s := max_le (by linarith [hs.2]) (by linarith)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) fun v hv => ?_).trans ?_
    · rw [uIoc_of_le hle] at hv
      rw [Real.norm_eq_abs]
      exact hC _ ((mem_stripSet_dual hs.1).2 ⟨hv.1.le, hv.2⟩)
        (lt_of_le_of_lt (le_max_left _ _) hv.1)
    · rw [abs_of_nonneg (by linarith)]
      have : t - s - max 0 (t - η - s) ≤ η := by linarith [le_max_right 0 (t - η - s)]
      nlinarith
  · rw [indicator_of_notMem hs]
    have : ∀ v, (stripSet a0 t η).indicator f (s, v) = 0 := fun v =>
      indicator_of_notMem (notMem_stripSet_dual hs) _
    simp [this]

/-- The forward fibre integral is supported in `[0, t − a₀]` and bounded by `Cη`. -/
theorem norm_integral_fiber_fwd_le {a0 t η : ℝ} {f : ℝ × ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ q ∈ stripSet a0 t η, |f q| ≤ C) (hη : 0 ≤ η) (r : ℝ) :
    ‖∫ u, (stripSet a0 t η).indicator f (u, r)‖ ≤
      (Icc 0 (t - a0)).indicator (fun _ => C * η) r := by
  by_cases hr : r ∈ Icc 0 (t - a0)
  · rw [indicator_of_mem hr, ← integral_fiber_fwd f hr.1 hr.2 hη, Real.norm_eq_abs]
    have hle : max a0 (t - η - r) ≤ t - r := max_le (by linarith [hr.2]) (by linarith)
    refine (abs_integral_le_of_abs_le hle fun u hu =>
      hC _ ((mem_stripSet_fwd hr.1).2 hu)).trans ?_
    have : t - r - max a0 (t - η - r) ≤ η := by linarith [le_max_right a0 (t - η - r)]
    nlinarith
  · rw [indicator_of_notMem hr]
    have : ∀ u, (stripSet a0 t η).indicator f (u, r) = 0 := fun u =>
      indicator_of_notMem (notMem_stripSet_fwd hr) _
    simp [this]

theorem integrable_indicator_Icc_const (a b c : ℝ) :
    Integrable ((Icc a b).indicator fun _ => c) volume :=
  (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

/-- **`|∫∫_S f| ≤ C(t − a₀)η`** when `|f| ≤ C` on `S`. -/
theorem abs_integral_strip_le {a0 t η : ℝ} {f : ℝ × ℝ → ℝ} (hf : Measurable f) {B C : ℝ}
    (hB : ∀ q, |f q| ≤ B) (hC0 : 0 ≤ C) (hC : ∀ q ∈ stripSet a0 t η, 0 < q.2 → |f q| ≤ C)
    (hat : a0 ≤ t)
    (hη : 0 ≤ η) :
    |∫ q, (stripSet a0 t η).indicator f q ∂(volume.prod volume)| ≤ C * η * (t - a0) := by
  rw [integral_prod _ (integrable_strip hf hB a0 t η)]
  calc |∫ s, ∫ v, (stripSet a0 t η).indicator f (s, v)|
      ≤ ∫ s, (Icc a0 t).indicator (fun _ => C * η) s := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (integrable_indicator_Icc_const _ _ _)
          (ae_of_all _ (norm_integral_fiber_le hC0 hC hη))
    _ = C * η * (t - a0) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
        measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring

theorem indicator_prod_univ {α : Type*} (S : Set (ℝ × ℝ)) (F : (ℝ × ℝ) × α → ℝ) (q : ℝ × ℝ)
    (a : α) : S.indicator (fun q => F (q, a)) q = (S ×ˢ (univ : Set α)).indicator F (q, a) := by
  by_cases hq : q ∈ S
  · rw [indicator_of_mem hq, indicator_of_mem (mk_mem_prod hq (mem_univ a))]
  · rw [indicator_of_notMem hq, indicator_of_notMem (fun h => hq h.1)]

end BlockBand.Transmission.LawDuality
