module

public import BlockBand.Transmission.DualBoundary.UniqueF1
public import BlockBand.Transmission.DualBoundary.Moment

/-!
# `unique` and `firstMoment` of `DualBoundaryStartContract`

No hypothesis beyond those of the contract (`D₀ > 0`, boundary start `IsDualStart ![x] ![y]`).
Exports **`dualBoundaryStart_unique`** and **`dualBoundaryStart_firstMoment`**, stated with the
exact types of the contract fields (`firstMoment` by `firstMoment_of_unique`).

Proof of `unique`:
1. `map_trunc_eq_of_tests`: it suffices that `E g(Z̄|_I)` agree for every finite
   `I ⊆ [0,∞)` and every `[0,1]`-valued Lipschitz `g`.
2. Fix `ε`, put `η = ε/(L+7)`, `σ₀ = σ(z₀)`, `R = ‖σ₀‖ + 1`, `T = max I`; start continuity of
   the lift (`LiftStartContinuity`) gives `δ`.
3. Along `s_n = 1/(n+1)`: `E g(Z̄_{s_n+·}|_I) → E g(Z̄|_I)`, `P(postSetᶜ) → 0` and
   `σ(Z̄_{s_n}) → σ₀` in probability (`tendsto_integral_shift`, `tendsto_measure_postSet_compl`,
   `tendsto_measure_shift`); pick one `n` where all the tolerances hold.
4. At `s = s_n`: `|E g(Z̄_{s+·}|_I) − E[g(Z̄_{s+·}|_I) | postSet]| ≤ η`
   (`abs_integral_sub_cond_le`), and the two conditional tests differ by `≤ Lη + 2η`
   (`abs_cond_sub_le_at`: coupling and start continuity).
5. Total `≤ (L + 6)η < ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.DualLift BlockBand.Transmission.DualFeller
open scoped NNReal ENNReal

/-- The small times `s_n = 1/(n+1)`. -/
def sSeq (n : ℕ) : ℝ≥0 := (1 / ((n : ℝ) + 1)).toNNReal

theorem sSeq_pos (n : ℕ) : 0 < sSeq n := Real.toNNReal_pos.2 Nat.one_div_pos_of_nat

theorem tendsto_sSeq : Tendsto sSeq atTop (𝓝 0) := by
  have := (continuous_real_toNNReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rwa [Real.toNNReal_zero] at this

/-- Small complement mass gives `P(A) ≥ 1/2` and `P(Aᶜ) ≤ η` (real). -/
theorem half_le_of_compl_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) {η : ℝ} (hη : 0 < η)
    (h : P Aᶜ < ENNReal.ofReal (min η 2⁻¹)) : 2⁻¹ ≤ P A ∧ P.real Aᶜ ≤ η := by
  have hle : P.real Aᶜ ≤ min η 2⁻¹ :=
    ENNReal.toReal_le_of_le_ofReal (le_min hη.le (by norm_num)) h.le
  have hpq : P.real A + P.real Aᶜ = 1 := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _), measure_add_measure_compl hA, measure_univ, ENNReal.toReal_one]
  refine ⟨?_, hle.trans (min_le_left _ _)⟩
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by simp
  rw [h2, ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  have := min_le_right η 2⁻¹
  change 2⁻¹ ≤ P.real A
  linarith

section Two

variable {D0 : ℝ} {x y : ℝ}
  {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
  {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
  {N₁ : ℝ≥0 → Ω₁ → ℕ} {X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ}
  {Ω₂ : Type} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂}
  {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
  {N₂ : ℝ≥0 → Ω₂ → ℕ} {X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ}

/-- **Two boundary realizations from the same start agree on every Lipschitz test.** -/
theorem test_eq (hD0 : 0 < D0) (hxy : 0 < x + y)
    (h₁ : IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁)
    (h₂ : IsBoundaryDualProcess P₂ 𝓖₂ D0 ![x] ![y] N₂ X₂ Y₂)
    (I : Finset ℝ≥0) {g : (I → Fin 2 → ℝ) → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (h01 : ∀ a, 0 ≤ g a ∧ g a ≤ 1) :
    ∫ ω, g (I.restrict (zbarTr N₁ X₁ Y₁ ω)) ∂P₁ = ∫ ω, g (I.restrict (zbarTr N₂ X₂ Y₂ ω)) ∂P₂ := by
  have := h₁.prob
  have := h₂.prob
  refine eq_of_forall_dist_le fun ε hε => ?_
  have hz0 : (![x, y] : Fin 2 → ℝ) 0 + (![x, y] : Fin 2 → ℝ) 1 ≠ 0 := by simp; linarith
  have hσ : ContinuousAt liftSecPt ![x, y] := continuousAt_liftSecPt hz0
  set σ₀ := liftSecPt ![x, y] with hσ₀
  have hL7 : (0 : ℝ) < L + 7 := by positivity
  set η : ℝ := ε / (L + 7) with hηdef
  have hη : 0 < η := div_pos hε hL7
  obtain ⟨δ, hδ, hF⟩ := liftStartContinuity_holds hD0 (I.sup id) (‖σ₀‖ + 1) η hη
  have hgc := hg.continuous
  have hgm := hgc.measurable
  have ev1 := Metric.tendsto_nhds.1 (tendsto_integral_shift h₁ I hgc h01 tendsto_sSeq) η hη
  have ev2 := Metric.tendsto_nhds.1 (tendsto_integral_shift h₂ I hgc h01 tendsto_sSeq) η hη
  have hc : 0 < ENNReal.ofReal (min η 2⁻¹) := ENNReal.ofReal_pos.2 (lt_min hη (by norm_num))
  have ev3 := (tendsto_order.1 (tendsto_measure_postSet_compl h₁ hxy tendsto_sSeq)).2 _ hc
  have ev4 := (tendsto_order.1 (tendsto_measure_postSet_compl h₂ hxy tendsto_sSeq)).2 _ hc
  have hδ4 : 0 < ENNReal.ofReal (δ / 4) := ENNReal.ofReal_pos.2 (by positivity)
  have hη2 : 0 < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have ev5 := (tendsto_order.1 (tendsto_measure_shift h₁ measurable_liftSecPt hσ tendsto_sSeq
    (by positivity : 0 < δ / 2))).2 _ hδ4
  have ev6 := (tendsto_order.1 (tendsto_measure_shift h₂ measurable_liftSecPt hσ tendsto_sSeq
    (by positivity : 0 < δ / 2))).2 _ hδ4
  have ev7 := (tendsto_order.1 (tendsto_measure_shift h₁ measurable_liftSecPt hσ tendsto_sSeq
    one_pos)).2 _ hη2
  obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
    (ev1.and (ev2.and (ev3.and (ev4.and (ev5.and (ev6.and ev7)))))).exists
  obtain ⟨hA₁, hq₁⟩ := half_le_of_compl_lt (measurableSet_postSet h₁ (sSeq n)) hη h3
  obtain ⟨hA₂, hq₂⟩ := half_le_of_compl_lt (measurableSet_postSet h₂ (sSeq n)) hη h4
  have hA₁0 : P₁ (postSet P₁ N₁ X₁ Y₁ (sSeq n)) ≠ 0 := (lt_of_lt_of_le (by norm_num) hA₁).ne'
  have hA₂0 : P₂ (postSet P₂ N₂ X₂ Y₂ (sSeq n)) ≠ 0 := (lt_of_lt_of_le (by norm_num) hA₂).ne'
  have hb := abs_cond_sub_le_at hD0 h₁ h₂ (sSeq_pos n) hA₁ hA₂ I hg h01 hη hδ hF h5.le h6.le
    h7.le
  have hc₁ := abs_integral_sub_cond_le (measurableSet_postSet h₁ (sSeq n)) hA₁0
    (H := fun ω => g (I.restrict (shiftZ N₁ X₁ Y₁ (sSeq n) ω)))
    (hgm.comp ((Finset.measurable_restrict I).comp (measurable_shiftZ h₁ (sSeq n))))
    (fun ω => h01 _)
  have hc₂ := abs_integral_sub_cond_le (measurableSet_postSet h₂ (sSeq n)) hA₂0
    (H := fun ω => g (I.restrict (shiftZ N₂ X₂ Y₂ (sSeq n) ω)))
    (hgm.comp ((Finset.measurable_restrict I).comp (measurable_shiftZ h₂ (sSeq n))))
    (fun ω => h01 _)
  rw [Real.dist_eq] at h1 h2 ⊢
  have hfin : ((L : ℝ) + 6) * η ≤ ε := by
    have e : ((L : ℝ) + 7) * η = ε := by rw [hηdef]; field_simp
    nlinarith
  have q1 := abs_lt.1 h1
  have q2 := abs_lt.1 h2
  have q3 := abs_le.1 hc₁
  have q4 := abs_le.1 hc₂
  have q5 := abs_le.1 hb
  rw [abs_le]
  constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2, q3.1, q3.2, q4.1, q4.2, q5.1, q5.2]

end Two

/-- **The field `unique` of the `DualBoundaryStartContract`** (unconditional). -/
theorem dualBoundaryStart_unique :
    ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓖₁ : Filtration ℝ≥0 m₁) (P₁ : Measure Ω₁)
      (N₁ : ℝ≥0 → Ω₁ → ℕ) (X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ)
      (Ω₂ : Type) (m₂ : MeasurableSpace Ω₂) (𝓖₂ : Filtration ℝ≥0 m₂) (P₂ : Measure Ω₂)
      (N₂ : ℝ≥0 → Ω₂ → ℕ) (X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ),
      IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁ →
      IsBoundaryDualProcess P₂ 𝓖₂ D0 ![x] ![y] N₂ X₂ Y₂ →
      P₁.map (truncDualState N₁ X₁ Y₁) = P₂.map (truncDualState N₂ X₂ Y₂) := by
  intro D0 hD0 x y hxy Ω₁ m₁ 𝓖₁ P₁ N₁ X₁ Y₁ Ω₂ m₂ 𝓖₂ P₂ N₂ X₂ Y₂ h₁ h₂
  have hxy' : 0 < x + y := by simpa using hxy.2.2.2.2 0 0
  exact map_trunc_eq_of_tests h₁ h₂ hxy' fun I g ⟨L, hg⟩ h01 => test_eq hD0 hxy' h₁ h₂ I hg h01

/-- **The field `firstMoment` of the `DualBoundaryStartContract`** (unconditional). -/
theorem dualBoundaryStart_firstMoment :
    ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∀ t : ℝ, 0 ≤ t →
        ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))) ∂P ≤
          ENNReal.ofReal (t * (x + y)) :=
  firstMoment_of_unique dualBoundaryStart_unique

end BlockBand.Transmission.DualBoundary
