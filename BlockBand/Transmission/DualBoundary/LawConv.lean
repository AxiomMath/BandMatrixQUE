module

public import BlockBand.Transmission.DualBoundary.LawLimit
public import BlockBand.Transmission.DualBoundary.LawValue

/-!
# The boundary dual identity for the lift: `K = V`

Setting: a critical limit `IsTransmissionLimit b E κ P μ` (`0 < b < 1/2`, `−2 < E < 2`,
absorption profile `κ`), `D₀ = transportD0 b E`, a boundary start `IsDualStart ![x] ![y]` with
`y < 1`, any lifted family `F` from `σ(x, y)` on `LΩ Unit`, `Q = LP (dirac ())`;
`K(t) = dualTransform E κ t Q F.N₂ F.X₂ F.Y₂`, `V(t) = E_P F_{x,y}(μ_t)`. Conditional on
`InteriorDualLawOne` (the `p = 1` interior part of `TransmissionLawContract.law`). No
atomless-lifetime lemma is used.

* `tendsto_liftSection`; **`tendsto_dualTransform_lift`**: `K_n(t) → K(t)` for any boundary
  starts `(x_n, y_n) → (x, y)` and any families `F_n`, at every `t > 0` where
  `zetaCdf F` is continuous (start continuity and corner absorption of the lift).
* `apprX`, `apprY` (`x_n = x + 1/(n+1)`, `y_n = y + ((1−y)/2)/(n+1)`), `isRatioParameter_appr`.
* **`dualTransform_lift_eq_of_continuousAt`**: `K(t) = V(t)` at those `t` (`K_n = V_n` by
  `dualLawValue_of_limit`, `V_n → V` by `tendsto_integral_ratio_param`).
* **`dualTransform_lift_eq`**: `K(t) = V(t)` at every `t > 0` (the discontinuities of the
  monotone `zetaCdf F` are countable, so their complement is dense; right-continuity of `K`
  and continuity of `V`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.DualLift BlockBand.Transmission.DualFeller
open scoped NNReal ENNReal

local notation "Q" => LP (Measure.dirac ())

theorem tendsto_liftSection {xs ys : ℕ → ℝ} {x y : ℝ} (hxs : Tendsto xs atTop (𝓝 x))
    (hys : Tendsto ys atTop (𝓝 y)) (hxy : x + y ≠ 0) :
    Tendsto (fun n => liftSection (xs n) (ys n)) atTop (𝓝 (liftSection x y)) := by
  have hv : Tendsto (fun n => ![xs n, ys n]) atTop (𝓝 ![x, y]) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · simpa using hxs
    · simpa using hys
  exact (continuousAt_liftSecPt (z := ![x, y]) (by simpa using hxy)).tendsto.comp hv

variable {D0 : ℝ}

/-- **`K_n(t) → K(t)` at continuity points of `zetaCdf F`.** -/
theorem tendsto_dualTransform_lift (hD0 : 0 < D0) {x y : ℝ} (hxy : IsDualStart ![x] ![y])
    (F : LiftFamily (Measure.dirac ()) D0 (sectionStart x y)) {E : ℝ} {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) {t : ℝ} (ht : 0 < t) (hc : ContinuousAt (zetaCdf F) t)
    {xs ys : ℕ → ℝ} (hxs : Tendsto xs atTop (𝓝 x)) (hys : Tendsto ys atTop (𝓝 y))
    (hxys : ∀ n, IsDualStart ![xs n] ![ys n])
    (Fs : ∀ n, LiftFamily (Measure.dirac ()) D0 (sectionStart (xs n) (ys n))) :
    Tendsto (fun n => dualTransform E κ t Q (Fs n).N₂ (Fs n).X₂ (Fs n).Y₂) atTop
      (𝓝 (dualTransform E κ t Q F.N₂ F.X₂ F.Y₂)) := by
  obtain ⟨K, hK⟩ := hκ.2.2
  have hH := rateBound_nonneg E K
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δw, hδw, hcw⟩ := Metric.continuousAt_iff.1 hc (ε / 8) (by positivity)
  set ηw := min (δw / 2) (min (t / 2) (1 / 2)) with hηw
  have hηw0 : 0 < ηw := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hηwδ : ηw < δw := (min_le_left _ _).trans_lt (by linarith)
  have hηwt : ηw ≤ t := (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
  have hηw1 : ηw < 1 := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  have hw : zetaCdf F (t + ηw) - zetaCdf F (t - ηw) ≤ ε / 4 := by
    have h1 := hcw (x := t + ηw) (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hηw0]; exact hηwδ)
    have h2 := hcw (x := t - ηw) (by
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hηw0]; exact hηwδ)
    rw [Real.dist_eq, abs_lt] at h1 h2
    linarith [h1.2, h2.1]
  have hden : 0 < 4 * (2 * t * rateBound E K + 1) := by positivity
  set η₁ := ε / (4 * (2 * t * rateBound E K + 1)) with hη₁
  have hη₁0 : 0 < η₁ := div_pos hε hden
  set η₂ := min (ε / 4) ηw with hη₂
  have hη₂0 : 0 < η₂ := lt_min (by positivity) hηw0
  obtain ⟨δ₁, hδ₁, hF1⟩ := liftStartContinuity_holds hD0 t.toNNReal ‖liftSection x y‖ η₁ hη₁0
  obtain ⟨δ₂, hδ₂, hF2⟩ :=
    liftCornerAbsorption_holds hD0 (t + 1).toNNReal ‖liftSection x y‖ η₂ hη₂0
  have hs : x + y ≠ 0 := (hxy.2.2.2.2 0 0).ne'
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.1 (tendsto_liftSection hxs hys hs) (min δ₁ δ₂)
    (lt_min hδ₁ hδ₂)
  refine ⟨n₀, fun n hn => ?_⟩
  have hd : ‖liftSection x y - liftSection (xs n) (ys n)‖ < min δ₁ δ₂ := by
    rw [← dist_eq_norm, dist_comm]; exact hn₀ n hn
  have hKy : ∀ δ, min δ₁ δ₂ ≤ δ →
      Q {ω | δ ≤ ‖sectionStart x y ω - sectionStart (xs n) (ys n) ω‖} ≤ ENNReal.ofReal δ := by
    intro δ hδ
    have : {ω | δ ≤ ‖sectionStart x y ω - sectionStart (xs n) (ys n) ω‖} = ∅ :=
      eq_empty_of_forall_notMem fun ω (hω : δ ≤ ‖liftSection x y - liftSection (xs n) (ys n)‖) =>
        (not_le.2 (hd.trans_le hδ)) hω
    rw [this, measure_empty]; exact zero_le
  have hξ := isLiftStart_of_dualStart hxy
  have hξn := isLiftStart_of_dualStart (hxys n)
  have hB₁ := hF1 Unit (Measure.dirac ()) _ _ hξ hξn F (Fs n) (hKy δ₁ (min_le_left _ _))
  have hB₂ := hF2 Unit (Measure.dirac ()) _ _ hξ hξn F (Fs n) (hKy δ₂ (min_le_right _ _))
  have key := abs_dualTransform_lift_sub_le (E := E) hD0 hxy (hxys n) F (Fs n) hκ hK ht hη₁0.le
    hη₂0.le
    (by positivity) (min_le_right _ _) hηwt hηw1 hB₁ hB₂ (measure_window_le F hηw0.le hw)
  rw [Real.dist_eq, abs_sub_comm]
  have e : rateBound E K * (2 * η₁) * t + η₁ = ε / 4 := by
    rw [hη₁]; field_simp
  have : η₂ ≤ ε / 4 := min_le_left _ _
  linarith

/-!
## Interior approximants
-/

/-- `x_n = x + 1/(n+1)`. -/
def apprX (x : ℝ) (n : ℕ) : ℝ := x + 1 / ((n : ℝ) + 1)

/-- `y_n = y + ((1−y)/2)·1/(n+1)`. -/
def apprY (y : ℝ) (n : ℕ) : ℝ := y + (1 - y) / 2 * (1 / ((n : ℝ) + 1))

theorem appr_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity

theorem appr_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 :=
  (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])

theorem tendsto_apprX (x : ℝ) : Tendsto (apprX x) atTop (𝓝 x) := by
  have h := (tendsto_const_nhds (x := x)).add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h
  exact h

theorem tendsto_apprY (y : ℝ) : Tendsto (apprY y) atTop (𝓝 y) := by
  have h := (tendsto_const_nhds (x := y)).add
    ((tendsto_const_nhds (x := (1 - y) / 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [mul_zero, add_zero] at h
  exact h

theorem apprY_le {y : ℝ} (hy1 : y < 1) (n : ℕ) : apprY y n ≤ (1 + y) / 2 := by
  unfold apprY
  have := mul_le_mul_of_nonneg_left (appr_le_one n) (by linarith : 0 ≤ (1 - y) / 2)
  linarith

theorem isRatioParameter_appr {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (n : ℕ) :
    IsRatioParameter ![apprX x n] ![apprY y n] := by
  have h1 := appr_pos n
  have h2 : 0 < (1 - y) / 2 * (1 / ((n : ℝ) + 1)) := mul_pos (by linarith) h1
  have h3 := apprY_le hy1 n
  refine ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun i => ?_, fun i => ?_⟩ <;>
    simp only [Matrix.cons_val_fin_one, apprX, apprY] at h3 ⊢
  · linarith
  · constructor <;> linarith

/-!
## `K = V`
-/

variable {b E : ℝ} {κ : ℝ → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {μ : ℝ → Ω → FiniteMeasure unitInterval}

theorem transportD0_pos (hb : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) : 0 < transportD0 b E := by
  unfold transportD0
  exact div_pos two_pos (mul_pos hb (by nlinarith))

/-- **`K(t) = V(t)` at continuity points of `zetaCdf F`.** -/
theorem dualTransform_lift_eq_of_continuousAt (hInt : InteriorDualLawOne) (hb : 0 < b)
    (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hκ : IsAbsorptionProfile κ)
    (hP : IsTransmissionLimit b E κ P μ) {x y : ℝ} (hxy : IsDualStart ![x] ![y]) (hy1 : y < 1)
    (F : LiftFamily (Measure.dirac ()) (transportD0 b E) (sectionStart x y)) {t : ℝ}
    (ht : 0 < t) (hc : ContinuousAt (zetaCdf F) t) :
    dualTransform E κ t Q F.N₂ F.X₂ F.Y₂ = ∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P := by
  have hD0 := transportD0_pos hb hE1 hE2
  have hx : 0 ≤ x := hxy.2.2.1 0
  have hy0 : 0 ≤ y := (hxy.2.2.2.1 0).1
  have hr := isRatioParameter_appr hx hy0 hy1
  have Fs : ∀ n, LiftFamily (Measure.dirac ()) (transportD0 b E)
      (sectionStart (apprX x n) (apprY y n)) := fun n =>
    Classical.choice (nonempty_liftFamily hD0 (isLiftStart_of_dualStart
      (isDualStart_of_ratio (hr n))))
  have h1 := tendsto_dualTransform_lift (E := E) hD0 hxy F hκ ht hc (tendsto_apprX x)
    (tendsto_apprY y) (fun n => isDualStart_of_ratio (hr n)) Fs
  have hKn : ∀ n, dualTransform E κ t Q (Fs n).N₂ (Fs n).X₂ (Fs n).Y₂ =
      ∫ ω, transmissionRatio ![apprX x n] ![apprY y n] (μ t ω) ∂P := fun n =>
    dualLawValue_of_limit hInt hb hb2 hE1 hE2 hκ hP ht (hr n) _ _ _ _ _ _ _
      (isDualDeletionProcess_lift hD0 (hr n) (Fs n))
  simp only [hKn] at h1
  have h2 := tendsto_integral_ratio_param hP ht (tendsto_apprX x) (tendsto_apprY y) hx hy0 hy1
    (fun n => (hr n).2.2.1 0 |>.le) (fun n => ((hr n).2.2.2 0).1.le) (apprY_le hy1)
    (by linarith) (X := x + 1) (fun n => by
      unfold apprX; linarith [appr_le_one n])
  exact tendsto_nhds_unique h1 h2

/-- **`K(t) = V(t)` at every `t > 0`** (density, right-continuity of `K`, continuity of
`V`). -/
theorem dualTransform_lift_eq (hInt : InteriorDualLawOne) (hb : 0 < b) (hb2 : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hκ : IsAbsorptionProfile κ)
    (hP : IsTransmissionLimit b E κ P μ) {x y : ℝ} (hxy : IsDualStart ![x] ![y]) (hy1 : y < 1)
    (F : LiftFamily (Measure.dirac ()) (transportD0 b E) (sectionStart x y)) {t : ℝ}
    (ht : 0 < t) :
    dualTransform E κ t Q F.N₂ F.X₂ F.Y₂ = ∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P := by
  have hD0 := transportD0_pos hb hE1 hE2
  have hx : 0 ≤ x := hxy.2.2.1 0
  have hy0 : 0 ≤ y := (hxy.2.2.2.1 0).1
  set S := {u | ¬ContinuousAt (zetaCdf F) u}
  have hS : S.Countable := (monotone_zetaCdf F).countable_not_continuousAt
  set A := Ioi t ∩ Sᶜ
  have hmem : t ∈ closure A := by
    have h1 := (hS.dense_compl ℝ).open_subset_closure_inter (isOpen_Ioi (a := t))
    have h2 : closure (Ioi t) ⊆ closure A := closure_minimal h1 isClosed_closure
    exact h2 (by rw [closure_Ioi]; exact Set.mem_Ici.2 le_rfl)
  have := mem_closure_iff_nhdsWithin_neBot.1 hmem
  have hK := (continuousWithinAt_dualTransform (E := E) (isBoundaryDualProcess_lift hD0 hxy F)
    hx hy0 hκ ht.le).mono (fun u (hu : u ∈ A) => le_of_lt hu.1)
  have hV := (continuousAt_integral_ratio hP ht hx hy0 hy1).continuousWithinAt (s := A)
  refine tendsto_nhds_unique (hK.tendsto.congr' ?_) hV.tendsto
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact dualTransform_lift_eq_of_continuousAt hInt hb hb2 hE1 hE2 hκ hP hxy hy1 F
    (ht.trans hu.1) (not_not.1 hu.2)

end BlockBand.Transmission.DualBoundary
