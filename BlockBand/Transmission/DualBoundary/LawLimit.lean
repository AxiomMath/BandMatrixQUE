module

public import BlockBand.Transmission.DualBoundary.LawRight
public import BlockBand.Transmission.DualBoundary.UniqueCouple
public import BlockBand.Transmission.DualFeller.F1
public import BlockBand.Transmission.DualFeller.F2

/-!
# `K_n(t) → K(t)` at continuity points of the law of `ζ`

Setting: the driver space `LΩ Unit` with `Q = LP (dirac ())`; `D₀ > 0`; a boundary start
`IsDualStart ![x] ![y]`, a lifted family `F₀` from `σ(x, y)`, and boundary starts
`(x_n, y_n) → (x, y)` with lifted families `F_n` from `σ(x_n, y_n)`; `K(t)`, `K_n(t)` are the
`dualTransform`s of their realizations `(N₂, X₂, Y₂)`. Norms: sup norms on `ℝ⁶`, `ℝ²`. The
absorption rate is nonnegative, and `1{ζ ≤ t}` is reduced to `ζ ∧ T`.

* `abs_dualIntegrand_sub_le` (pathwise): equal indicators and `|R − R'| ≤ c` on `[0, t]` give
  `|e^{−I} 1 − e^{−I'} 1'| ≤ H c t`, `H = rateBound E K` (`|e^{−a} − e^{−b}| ≤ |a − b|`).
* `zeta_iff_of_close`: `|ζ∧T − ζ'∧T| < η' ≤ η` and `ζ ∉ (t − η, t + η]` give
  `ζ ≤ t ↔ ζ' ≤ t` (`t + η < T`).
* **`abs_dualTransform_lift_sub_le`**: off the bad event of start continuity (`η₁`), that of
  corner absorption (`η₂`) and the window `{t − η_w < ζ₀ ≤ t + η_w}` (mass `≤ w`),
  `|K(t) − K'(t)| ≤ 2Hη₁t + η₁ + η₂ + w`.
* `zetaCdf F u = Q(ζ ≤ u)` (monotone, so its discontinuities are countable).

The sibling module proves from these **`tendsto_dualTransform_lift`**: `K_n(t) → K(t)` at every
`t > 0` where `zetaCdf F₀` is continuous (`liftStartContinuity_holds`,
`liftCornerAbsorption_holds`; the deterministic starts make the Ky Fan sets empty for large `n`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.DualLift BlockBand.Transmission.DualFeller
open scoped NNReal ENNReal

theorem continuous_absorptionRate {κ : ℝ → ℝ} (hκ : Continuous κ) (E : ℝ) :
    Continuous (absorptionRate E κ) :=
  continuous_const.mul hκ

/-- **Pathwise comparison of two integrands.** -/
theorem abs_dualIntegrand_sub_le {Ω : Type*} {N N' : ℝ≥0 → Ω → ℕ}
    {X Y X' Y' : ℝ≥0 → Ω → ℕ → ℝ} {E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {K : ℝ}
    (hK : ∀ s, κ s ≤ K) {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) {ω : Ω}
    (hR : Continuous fun s : ℝ≥0 => dualTotal (N s ω) (X s ω) (Y s ω))
    (hR' : Continuous fun s : ℝ≥0 => dualTotal (N' s ω) (X' s ω) (Y' s ω))
    (hR0 : ∀ s, 0 ≤ dualTotal (N s ω) (X s ω) (Y s ω))
    (hR0' : ∀ s, 0 ≤ dualTotal (N' s ω) (X' s ω) (Y' s ω))
    (hclose : ∀ s : ℝ≥0, s ≤ t.toNNReal →
      |dualTotal (N s ω) (X s ω) (Y s ω) - dualTotal (N' s ω) (X' s ω) (Y' s ω)| ≤ c)
    (hind : dualExtinction N ω ≤ ENNReal.ofReal t ↔ dualExtinction N' ω ≤ ENNReal.ofReal t) :
    |dualIntegrand E κ t N X Y ω - dualIntegrand E κ t N' X' Y' ω| ≤ rateBound E K * c * t := by
  unfold dualIntegrand
  by_cases hd : dualExtinction N ω ≤ ENNReal.ofReal t
  · simp only [hd, hind.1 hd, ↓reduceIte]
    refine (abs_exp_neg_sub_le (dualIntegral_nonneg hκ ht hR0)
      (dualIntegral_nonneg hκ ht hR0')).trans ?_
    unfold dualIntegral
    have hi : ∀ (M : ℝ≥0 → Ω → ℕ) (A B : ℝ≥0 → Ω → ℕ → ℝ),
        Continuous (fun s : ℝ≥0 => dualTotal (M s ω) (A s ω) (B s ω)) →
        IntervalIntegrable (fun s => absorptionRate E κ (t - s) *
          dualTotal (M s.toNNReal ω) (A s.toNNReal ω) (B s.toNNReal ω)) volume 0 t :=
      fun M A B hM => (((continuous_absorptionRate hκ.1 E).comp
        (continuous_const.sub continuous_id)).mul (hM.comp continuous_real_toNNReal)).intervalIntegrable 0 t
    rw [← intervalIntegral.integral_sub (hi N X Y hR) (hi N' X' Y' hR')]
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := rateBound E K * c) (f := fun s => absorptionRate E κ (t - s) *
          dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω) -
        absorptionRate E κ (t - s) *
          dualTotal (N' s.toNNReal ω) (X' s.toNNReal ω) (Y' s.toNNReal ω)) (fun s hs => by
        rw [Set.uIoc_of_le ht] at hs
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (absorptionRate_nonneg hκ E _)]
        exact mul_le_mul (absorptionRate_le hK E _) (hclose _ (Real.toNNReal_le_toNNReal hs.2))
          (abs_nonneg _) (rateBound_nonneg E K))
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at key
  · have hd' : ¬dualExtinction N' ω ≤ ENNReal.ofReal t := fun h => hd (hind.2 h)
    simp only [hd, hd', ↓reduceIte, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (rateBound_nonneg E K) hc) ht

/-- **`1{ζ ≤ t}` from `ζ ∧ T`** off the window `(t − η, t + η]`. -/
theorem zeta_iff_of_close {T : ℝ≥0} {z z' : WithTop ℝ≥0} {t η η' : ℝ} (hη : η' ≤ η)
    (hηt : η ≤ t) (hT : t + η < T)
    (hclose : |(((min (T : WithTop ℝ≥0) z).untopA : ℝ≥0) : ℝ) -
      (((min (T : WithTop ℝ≥0) z').untopA : ℝ≥0) : ℝ)| < η')
    (hW : ¬(z ≤ ((t + η).toNNReal : WithTop ℝ≥0) ∧ ¬z ≤ ((t - η).toNNReal : WithTop ℝ≥0))) :
    z ≤ (t.toNNReal : WithTop ℝ≥0) ↔ z' ≤ (t.toNNReal : WithTop ℝ≥0) := by
  have h0 : 0 ≤ η' := (abs_nonneg _).trans hclose.le
  rw [le_toNNReal_iff_untopA (by linarith) (by linarith),
    le_toNNReal_iff_untopA (by linarith) (by linarith)]
  rw [le_toNNReal_iff_untopA (by linarith) hT,
    le_toNNReal_iff_untopA (by linarith) (by linarith)] at hW
  rw [abs_lt] at hclose
  by_cases h1 : (((min (T : WithTop ℝ≥0) z).untopA : ℝ≥0) : ℝ) ≤ t - η
  · constructor <;> intro _ <;> linarith
  · have h2 : ¬(((min (T : WithTop ℝ≥0) z).untopA : ℝ≥0) : ℝ) ≤ t + η := fun h => hW ⟨h, h1⟩
    constructor <;> intro h <;> exfalso <;> [exact h2 (by linarith); exact h2 (by linarith)]

section Lift

variable {D0 : ℝ}

local notation "Q" => LP (Measure.dirac ())

/-- `c(u) = Q(ζ ≤ u)` for a lifted family. -/
def zetaCdf {x y : ℝ} (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y)) (u : ℝ) : ℝ :=
  (LP (Measure.dirac ())).real {ω | F.zeta ω ≤ (u.toNNReal : WithTop ℝ≥0)}

theorem measurableSet_zeta_le_amb {x y : ℝ}
    (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y)) (u : ℝ≥0) :
    MeasurableSet {ω | F.zeta ω ≤ (u : WithTop ℝ≥0)} :=
  (L𝓖 (Measure.dirac ())).le u _ (F.measurableSet_zeta_le u)

theorem monotone_zetaCdf {x y : ℝ} (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y)) :
    Monotone (zetaCdf F) := fun a b hab => by
  unfold zetaCdf
  exact measureReal_mono (fun ω (h : F.zeta ω ≤ (a.toNNReal : WithTop ℝ≥0)) =>
    h.trans (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hab))) (measure_ne_top _ _)

theorem measure_window_le {x y : ℝ} (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y))
    {t η w : ℝ} (hη : 0 ≤ η) (h : zetaCdf F (t + η) - zetaCdf F (t - η) ≤ w) :
    Q ({ω | F.zeta ω ≤ ((t + η).toNNReal : WithTop ℝ≥0)} \
      {ω | F.zeta ω ≤ ((t - η).toNNReal : WithTop ℝ≥0)}) ≤ ENNReal.ofReal w := by
  have hsub : {ω | F.zeta ω ≤ ((t - η).toNNReal : WithTop ℝ≥0)} ⊆
      {ω | F.zeta ω ≤ ((t + η).toNNReal : WithTop ℝ≥0)} :=
    fun ω (hω : F.zeta ω ≤ ((t - η).toNNReal : WithTop ℝ≥0)) =>
      hω.trans (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal (by linarith)))
  rw [← ofReal_measureReal (measure_ne_top _ _),
    measureReal_sdiff hsub (measurableSet_zeta_le_amb F _) (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

theorem isLiftStart_of_dualStart {x y : ℝ} (hxy : IsDualStart ![x] ![y]) :
    IsLiftStart (Measure.dirac ()) (sectionStart x y) :=
  isLiftStart_section (hxy.2.2.1 0) (hxy.2.2.2.1 0).1 (hxy.2.2.2.1 0).2 (hxy.2.2.2.2 0 0)

/-- **One comparison**: `|K(t) − K'(t)| ≤ 2Hη₁t + η₁ + η₂ + w`. -/
theorem abs_dualTransform_lift_sub_le (hD0 : 0 < D0) {x y x' y' : ℝ}
    (hxy : IsDualStart ![x] ![y]) (hxy' : IsDualStart ![x'] ![y'])
    (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y))
    (F' : LiftFamily (Measure.dirac ()) D0 (sectionStart x' y'))
    {E : ℝ} {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {K : ℝ} (hK : ∀ s, κ s ≤ K) {t : ℝ}
    (ht : 0 < t) {η₁ η₂ ηw w : ℝ} (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hw : 0 ≤ w)
    (hη₂w : η₂ ≤ ηw) (hηwt : ηw ≤ t) (hηw1 : ηw < 1)
    (hB₁ : Q {ω | ‖sectionStart x y ω‖ ≤ ‖liftSection x y‖ ∧ ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
      η₁ ≤ ‖liftZbar F s ω - liftZbar F' s ω‖} ≤ ENNReal.ofReal η₁)
    (hB₂ : Q {ω | ‖sectionStart x y ω‖ ≤ ‖liftSection x y‖ ∧
      η₂ ≤ |(((min ((t + 1).toNNReal : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) -
        (((min ((t + 1).toNNReal : WithTop ℝ≥0) (F'.zeta ω)).untopA : ℝ≥0) : ℝ)|} ≤
        ENNReal.ofReal η₂)
    (hW : Q ({ω | F.zeta ω ≤ ((t + ηw).toNNReal : WithTop ℝ≥0)} \
      {ω | F.zeta ω ≤ ((t - ηw).toNNReal : WithTop ℝ≥0)}) ≤ ENNReal.ofReal w) :
    |dualTransform E κ t Q F.N₂ F.X₂ F.Y₂ - dualTransform E κ t Q F'.N₂ F'.X₂ F'.Y₂| ≤
      rateBound E K * (2 * η₁) * t + η₁ + η₂ + w := by
  have hB := isBoundaryDualProcess_lift hD0 hxy F
  have hB' := isBoundaryDualProcess_lift hD0 hxy' F'
  have hx := hxy.2.2.1 0
  have hy := (hxy.2.2.2.1 0).1
  have hx' := hxy'.2.2.1 0
  have hy' := (hxy'.2.2.2.1 0).1
  simp only [Matrix.cons_val_fin_one] at hx hy hx' hy'
  set Bad := {ω | ‖sectionStart x y ω‖ ≤ ‖liftSection x y‖ ∧ ∃ s : ℝ≥0, s ≤ t.toNNReal ∧
      η₁ ≤ ‖liftZbar F s ω - liftZbar F' s ω‖} ∪
    {ω | ‖sectionStart x y ω‖ ≤ ‖liftSection x y‖ ∧
      η₂ ≤ |(((min ((t + 1).toNNReal : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) -
        (((min ((t + 1).toNNReal : WithTop ℝ≥0) (F'.zeta ω)).untopA : ℝ≥0) : ℝ)|} ∪
    ({ω | F.zeta ω ≤ ((t + ηw).toNNReal : WithTop ℝ≥0)} \
      {ω | F.zeta ω ≤ ((t - ηw).toNNReal : WithTop ℝ≥0)}) with hBad
  set C := rateBound E K * (2 * η₁) * t
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (rateBound_nonneg E K) (by linarith)) ht.le
  have hpt : ∀ᵐ ω ∂Q, ENNReal.ofReal ‖dualIntegrand E κ t F.N₂ F.X₂ F.Y₂ ω -
      dualIntegrand E κ t F'.N₂ F'.X₂ F'.Y₂ ω‖ ≤
        ENNReal.ofReal C + (toMeasurable Q Bad).indicator 1 ω := by
    filter_upwards [ae_path hB, ae_path hB', ae_dualTotal_nonneg hB hx hy,
      ae_dualTotal_nonneg hB' hx' hy', ae_dualExtinction_lift_iff hD0 (isLiftStart_of_dualStart hxy) F hB,
      ae_dualExtinction_lift_iff hD0 (isLiftStart_of_dualStart hxy') F' hB'] with
      ω hp hp' hR0 hR0' he he'
    by_cases hbad : ω ∈ toMeasurable Q Bad
    · rw [indicator_of_mem hbad, Pi.one_apply]
      have h1 := dualIntegrand_mem (E := E) hκ ht.le hR0
      have h2 := dualIntegrand_mem (E := E) hκ ht.le hR0'
      refine (ENNReal.ofReal_le_one.2 ?_).trans le_add_self
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · rw [indicator_of_notMem hbad, add_zero]
      have hnb : ω ∉ Bad := fun h => hbad (subset_toMeasurable _ _ h)
      simp only [hBad, mem_union, Set.mem_sdiff, mem_ofPred_eq, not_or] at hnb
      obtain ⟨⟨n1, n2⟩, n3⟩ := hnb
      have hle : ‖sectionStart x y ω‖ ≤ ‖liftSection x y‖ := le_rfl
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.norm_eq_abs]
      refine abs_dualIntegrand_sub_le hκ hK ht.le (by linarith) (continuous_dualTotal hp.2 hp.1)
        (continuous_dualTotal hp'.2 hp'.1) hR0 hR0' (fun s hs => ?_) ?_
      · rw [dualTotal_lift, dualTotal_lift]
        have hlt : ‖liftZbar F s ω - liftZbar F' s ω‖ < η₁ :=
          not_le.1 fun hc => n1 ⟨hle, s, hs, hc⟩
        have e0 := (norm_le_pi_norm (liftZbar F s ω - liftZbar F' s ω) 0).trans hlt.le
        have e1 := (norm_le_pi_norm (liftZbar F s ω - liftZbar F' s ω) 1).trans hlt.le
        simp only [Pi.sub_apply, Real.norm_eq_abs] at e0 e1
        rw [show liftZbar F s ω 0 + liftZbar F s ω 1 - (liftZbar F' s ω 0 + liftZbar F' s ω 1) =
          (liftZbar F s ω 0 - liftZbar F' s ω 0) + (liftZbar F s ω 1 - liftZbar F' s ω 1) by ring]
        exact (abs_add_le _ _).trans (by linarith)
      · rw [he t, he' t]
        refine zeta_iff_of_close hη₂w hηwt ?_ (not_le.1 fun hc => n2 ⟨hle, hc⟩) n3
        rw [Real.coe_toNNReal _ (by linarith)]; linarith
  have hfin : Q Bad ≤ ENNReal.ofReal η₁ + ENNReal.ofReal η₂ + ENNReal.ofReal w :=
    (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hB₁ hB₂)) hW)
  rw [dualTransform_eq_integral, dualTransform_eq_integral, ← integral_sub
    (integrable_dualIntegrand hB hx hy hκ ht.le) (integrable_dualIntegrand hB' hx' hy' hκ ht.le),
    ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal
    (by positivity) ?_)
  calc ∫⁻ ω, ENNReal.ofReal ‖dualIntegrand E κ t F.N₂ F.X₂ F.Y₂ ω -
        dualIntegrand E κ t F'.N₂ F'.X₂ F'.Y₂ ω‖ ∂Q
      ≤ ∫⁻ ω, (ENNReal.ofReal C + (toMeasurable Q Bad).indicator 1 ω) ∂Q := lintegral_mono_ae hpt
    _ = ENNReal.ofReal C + Q Bad := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
    _ ≤ ENNReal.ofReal C + (ENNReal.ofReal η₁ + ENNReal.ofReal η₂ + ENNReal.ofReal w) := by
      gcongr
    _ = ENNReal.ofReal (C + η₁ + η₂ + w) := by
      rw [ENNReal.ofReal_add (by positivity) hw, ENNReal.ofReal_add (by positivity) hη₂,
        ENNReal.ofReal_add hC hη₁]
      ring

end Lift

end BlockBand.Transmission.DualBoundary
