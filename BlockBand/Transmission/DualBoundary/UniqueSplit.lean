module

public import BlockBand.Transmission.DualBoundary.UniqueReduce

/-!
# Uniqueness at a boundary start: the split at a small time `s`

Setting: one boundary realization `h : IsBoundaryDualProcess P 𝓖 D₀ ![x] ![y] N X Y` (any
filtered probability space), `x + y > 0`, a finite time set `I` and a continuous test `g` on
`I → ℝ²` with values in `[0,1]`; deterministic times `s n → 0`.
* `abs_integral_sub_cond_le` (generic): `|E H − E[H | A]| ≤ P(Aᶜ)` for `H ∈ [0,1]`.
* `ae_zbarPath_post`: a.s. the read-out of the post-`s` path is the shifted read-out
  `shiftZ s = Z̄_{s+·}`.
* **`tendsto_integral_shift`**: `E g(Z̄_{s_n+·}|_I) → E g(Z̄|_I)` (continuity of `Z̄`).
* **`tendsto_measure_shift`**: `P(ε ≤ d(φ(Z̄_{s_n}), φ(z₀))) → 0` for `φ` continuous at
  `z₀ = (x, y)`; **`tendsto_measure_postSet_compl`**: `P(postSet(s_n)ᶜ) → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- **`|E H − E[H | A]| ≤ P(Aᶜ)` for `[0,1]`-valued `H`.** -/
theorem abs_integral_sub_cond_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) (hA0 : P A ≠ 0) {H : Ω → ℝ}
    (hH : Measurable H) (h01 : ∀ ω, 0 ≤ H ω ∧ H ω ≤ 1) :
    |∫ ω, H ω ∂P - ∫ ω, H ω ∂P[|A]| ≤ P.real Aᶜ := by
  have hint : Integrable H P := Integrable.of_bound hH.aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h01 ω])
  have hsplit := integral_add_compl hA hint
  have hcond : ∫ ω, H ω ∂P[|A] = (P.real A)⁻¹ * ∫ ω in A, H ω ∂P := by
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]; rfl
  have hpq : P.real A + P.real Aᶜ = 1 := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _), measure_add_measure_compl hA, measure_univ, ENNReal.toReal_one]
  have hp : 0 < P.real A := ENNReal.toReal_pos hA0 (measure_ne_top _ _)
  have hc0 : 0 ≤ ∫ ω in A, H ω ∂P := setIntegral_nonneg hA fun ω _ => (h01 ω).1
  have hc1 : ∫ ω in A, H ω ∂P ≤ P.real A := by
    calc ∫ ω in A, H ω ∂P ≤ ∫ ω in A, (1 : ℝ) ∂P :=
          setIntegral_mono hint.integrableOn (integrable_const 1).integrableOn fun ω => (h01 ω).2
      _ = P.real A := by simp
  have hd0 : 0 ≤ ∫ ω in Aᶜ, H ω ∂P := setIntegral_nonneg hA.compl fun ω _ => (h01 ω).1
  have hd1 : ∫ ω in Aᶜ, H ω ∂P ≤ P.real Aᶜ := by
    calc ∫ ω in Aᶜ, H ω ∂P ≤ ∫ ω in Aᶜ, (1 : ℝ) ∂P :=
          setIntegral_mono hint.integrableOn (integrable_const 1).integrableOn fun ω => (h01 ω).2
      _ = P.real Aᶜ := by simp
  rw [← hsplit, hcond]
  set p := P.real A
  set q := P.real Aᶜ
  set c := ∫ ω in A, H ω ∂P
  set d := ∫ ω in Aᶜ, H ω ∂P
  set r := p⁻¹ * c with hr
  have hr0 : 0 ≤ r := mul_nonneg (inv_nonneg.2 hp.le) hc0
  have hr1 : r ≤ 1 := by rw [hr, inv_mul_le_iff₀ hp, mul_one]; exact hc1
  have hcpr : c = p * r := by rw [hr, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  have e : c + d - r = d - r * q := by linear_combination hcpr + r * hpq
  have hq0 : 0 ≤ q := measureReal_nonneg
  rw [e, abs_le]
  constructor <;> nlinarith [mul_nonneg hr0 hq0, mul_le_of_le_one_left hq0 hr1]

/-- The shifted read-out path `t ↦ Z̄_{s+t}`. -/
def shiftZ {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ≥0) (ω : Ω) :
    ℝ≥0 → Fin 2 → ℝ :=
  fun t => zbarTr N X Y ω (s + t)

section Real

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

theorem measurable_shiftZ (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (s : ℝ≥0) :
    Measurable (shiftZ N X Y s) :=
  measurable_pi_iff.2 fun t => (measurable_pi_apply (s + t)).comp (measurable_zbarTr h)

/-- A.s. the read-out of the post-`s` path is the shifted read-out. -/
theorem ae_zbarPath_post (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, zbarPath (dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω) =
      shiftZ N X Y s ω := by
  filter_upwards [ae_dualState_post h s] with ω hω
  funext u
  simp only [zbarPath, shiftZ, zbarTr, hω u]

theorem ae_continuous_zbarTr (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, Continuous (zbarTr N X Y ω) := by
  filter_upwards [ae_path h] with ω hω
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa [zbarTr_apply] using continuous_truncX hω.2 hω.1
  · simpa [zbarTr_apply] using continuous_truncY hω.2 hω.1

theorem ae_zbarTr_zero (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, zbarTr N X Y ω 0 = ![x, y] := by
  filter_upwards [h.start] with ω hs
  have h0 : N 0 ω = 1 := by simpa using hs.1
  have hX : X 0 ω 0 = x := by simpa using (hs.2 0).1
  have hY : Y 0 ω 0 = y := by simpa using (hs.2 0).2
  rw [zbarTr_apply, h0]
  funext i; fin_cases i <;> simp [truncDualCoord, hX, hY]

/-- **`E g(Z̄_{s_n+·}|_I) → E g(Z̄|_I)` as `s_n → 0`.** -/
theorem tendsto_integral_shift (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (I : Finset ℝ≥0) {g : (I → Fin 2 → ℝ) → ℝ} (hg : Continuous g)
    (h01 : ∀ a, 0 ≤ g a ∧ g a ≤ 1) {s : ℕ → ℝ≥0} (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, g (I.restrict (shiftZ N X Y (s n) ω)) ∂P) atTop
      (𝓝 (∫ ω, g (I.restrict (zbarTr N X Y ω)) ∂P)) := by
  have := h.prob
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
    (integrable_const 1) (fun n => Eventually.of_forall fun ω => ?_) ?_
  · exact (hg.measurable.comp ((Finset.measurable_restrict I).comp
      (measurable_shiftZ h (s n)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h01 (I.restrict (shiftZ N X Y (s n) ω))]
  · filter_upwards [ae_continuous_zbarTr h] with ω hω
    refine (hg.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
    have hi : Tendsto (fun n => s n + (i : ℝ≥0)) atTop (𝓝 (0 + (i : ℝ≥0))) :=
      hs.add tendsto_const_nhds
    rw [zero_add] at hi
    exact (hω.tendsto _).comp hi

/-- **Convergence in probability of `φ(Z̄_{s_n})` to `φ(z₀)`.** -/
theorem tendsto_measure_shift (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {φ : (Fin 2 → ℝ) → E} (hφm : Measurable φ) (hφ : ContinuousAt φ ![x, y])
    {s : ℕ → ℝ≥0} (hs : Tendsto s atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ dist (φ (zbarTr N X Y ω (s n))) (φ ![x, y])}) atTop (𝓝 0) := by
  have := h.prob
  have hT : TendstoInMeasure P (fun n ω => φ (zbarTr N X Y ω (s n))) atTop
      (fun _ => φ ![x, y]) := by
    refine tendstoInMeasure_of_tendsto_ae_of_measurable_edist (fun n => ?_) ?_
    · exact (continuous_id.edist continuous_const).measurable.comp
        (hφm.comp ((measurable_pi_apply (s n)).comp (measurable_zbarTr h)))
    · filter_upwards [ae_continuous_zbarTr h, ae_zbarTr_zero h] with ω hc h0
      have : Tendsto (fun n => zbarTr N X Y ω (s n)) atTop (𝓝 ![x, y]) := by
        rw [← h0]; exact (hc.tendsto 0).comp hs
      exact hφ.tendsto.comp this
  refine (hT (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)).congr fun n => ?_
  congr 1
  ext ω
  simp [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg]

/-- **`P(N_{s_n} ≠ 1 or bad) → 0`.** -/
theorem tendsto_measure_postSet_compl (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (hxy : 0 < x + y) {s : ℕ → ℝ≥0} (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => P (postSet P N X Y (s n))ᶜ) atTop (𝓝 0) := by
  have hne : (![x, y] : Fin 2 → ℝ) ≠ 0 := by
    intro he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    linarith
  have hz : 0 < dist (0 : Fin 2 → ℝ) ![x, y] := dist_pos.2 hne.symm
  have hT := tendsto_measure_shift h measurable_id continuousAt_id hs hz
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => zero_le)
    fun n => ?_
  calc P (postSet P N X Y (s n))ᶜ ≤ P (badSet P N X Y ∪
        {ω | dist (0 : Fin 2 → ℝ) ![x, y] ≤ dist (id (zbarTr N X Y ω (s n))) (id ![x, y])}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hb : ω ∈ badSet P N X Y
        · exact Or.inl hb
        · right
          obtain ⟨h0, hP⟩ := good_of_notMem_badSet hb
          have h1 : N (s n) ω ≠ 1 := fun h1 => hω ⟨hb, h1⟩
          have hN : N (s n) ω = 0 := (level_eq_one_or_zero hP h0 (s n)).resolve_left h1
          have hzb : zbarTr N X Y ω (s n) = 0 := by
            rw [zbarTr_apply, hN]; funext i; fin_cases i <;> simp [truncDualCoord]
          simp [hzb]
    _ ≤ P (badSet P N X Y) + _ := measure_union_le _ _
    _ = _ := by rw [measure_badSet h, zero_add]

end Real

end BlockBand.Transmission.DualBoundary
