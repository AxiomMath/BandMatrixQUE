module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The removal average, abstract step: a conditional deviation bound with a nonnegative weight

**`condExp_mul_sub_le`** (any probability space, sub-σ-algebra `m ≤ m0`): `P ≥ 0`, `P ≤ B_P`,
`|Y| ≤ B_Y` measurable, `V` `m`-measurable with `|V| ≤ B_V`, `G` an `m`-measurable set, `Bad` a
measurable set; if a.e. on `G \ Bad` we have `|Y - V| ≤ e`, then a.e. on `G`
`|E[P Y | m] - V E[P | m]| ≤ e E[P | m] + B_P (B_Y + B_V) E[1_Bad | m]`.

The error is **relative** to `E[P | m]` (no rough bound on `P` on the good event is needed), and
the bad set enters only through `E[1_Bad | m]` (made small by disintegration,
`condExp_indicator_compl_small`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Filter

section Abstract

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ ω, |f ω| ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hB ω)

/-- **Conditional deviation with a nonnegative weight.** -/
theorem condExp_mul_sub_le (hm : m ≤ m0) {P Y V : Ω → ℝ} {Bp BY BV e : ℝ}
    (hP : Measurable P) (hP0 : ∀ ω, 0 ≤ P ω) (hPB : ∀ ω, P ω ≤ Bp)
    (hY : Measurable Y) (hYB : ∀ ω, |Y ω| ≤ BY)
    (hV : StronglyMeasurable[m] V) (hVB : ∀ ω, |V ω| ≤ BV)
    {G Bad : Set Ω} (hG : MeasurableSet[m] G) (hBad : MeasurableSet Bad) (he : 0 ≤ e)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ G → ω ∉ Bad → |Y ω - V ω| ≤ e) :
    ∀ᵐ ω ∂μ, ω ∈ G →
      |(μ[fun ω => P ω * Y ω | m]) ω - V ω * (μ[P | m]) ω| ≤
        e * (μ[P | m]) ω + Bp * (BY + BV) * (μ[Bad.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hVm : Measurable V := (hV.mono hm).measurable
  have hBp : 0 ≤ Bp := (hP0 Classical.ofNonempty).trans (hPB _)
  have hBY : 0 ≤ BY := (abs_nonneg _).trans (hYB Classical.ofNonempty)
  have hBV : 0 ≤ BV := (abs_nonneg _).trans (hVB Classical.ofNonempty)
  set c : ℝ := Bp * (BY + BV)
  have hc : 0 ≤ c := by positivity
  set I : Ω → ℝ := Bad.indicator (fun _ => (1 : ℝ))
  set J : Ω → ℝ := G.indicator (fun _ => (1 : ℝ))
  have hJs : StronglyMeasurable[m] J := stronglyMeasurable_const.indicator hG
  have hJm : Measurable J := (hJs.mono hm).measurable
  have hIm : Measurable I := measurable_const.indicator hBad
  have hI01 : ∀ ω, 0 ≤ I ω ∧ I ω ≤ 1 := fun ω => by
    by_cases h : ω ∈ Bad <;> simp [I, h]
  have hJ01 : ∀ ω, 0 ≤ J ω ∧ J ω ≤ 1 := fun ω => by
    by_cases h : ω ∈ G <;> simp [J, h]
  have hPabs : ∀ ω, |P ω| ≤ Bp := fun ω => by rw [abs_of_nonneg (hP0 ω)]; exact hPB ω
  have hPi : Integrable P μ := integrable_of_abs_le hP hPabs
  have hIi : Integrable I μ := integrable_of_abs_le hIm fun ω => by
    rw [abs_of_nonneg (hI01 ω).1]; exact (hI01 ω).2
  have hPYi : Integrable (fun ω => P ω * Y ω) μ :=
    integrable_of_abs_le (hP.mul hY) (B := Bp * BY) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hPabs ω) (hYB ω) (abs_nonneg _) hBp
  have hVPi : Integrable (V * P) μ :=
    integrable_of_abs_le (hVm.mul hP) (B := BV * Bp) fun ω => by
      rw [Pi.mul_apply, abs_mul]; exact mul_le_mul (hVB ω) (hPabs ω) (abs_nonneg _) hBV
  set Q : Ω → ℝ := fun ω => P ω * Y ω - (V * P) ω
  have hQm : Measurable Q := (hP.mul hY).sub (hVm.mul hP)
  have hQi : Integrable Q μ := hPYi.sub hVPi
  set D : Ω → ℝ := J * Q
  have hDi : Integrable D μ := integrable_of_abs_le (hJm.mul hQm) (B := Bp * BY + BV * Bp)
    fun ω => by
      simp only [D, Q, Pi.mul_apply]
      rw [abs_mul, abs_of_nonneg (hJ01 ω).1]
      have h1 : |P ω * Y ω - V ω * P ω| ≤ Bp * BY + BV * Bp := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (hPabs ω) (hYB ω) (abs_nonneg _) hBp)
          (mul_le_mul (hVB ω) (hPabs ω) (abs_nonneg _) hBV)
      calc J ω * |P ω * Y ω - V ω * P ω| ≤ 1 * |P ω * Y ω - V ω * P ω| :=
            mul_le_mul_of_nonneg_right (hJ01 ω).2 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h1
  set g : Ω → ℝ := fun ω => e * P ω + c * I ω
  have hgi : Integrable g μ := (hPi.const_mul e).add (hIi.const_mul c)
  -- pointwise domination
  have hdom : ∀ᵐ ω ∂μ, |D ω| ≤ g ω := by
    filter_upwards [hgood] with ω hω
    simp only [D, Q, g, Pi.mul_apply]
    have hg0 : 0 ≤ e * P ω + c * I ω :=
      add_nonneg (mul_nonneg he (hP0 ω)) (mul_nonneg hc (hI01 ω).1)
    by_cases hG' : ω ∈ G
    · have hJ1 : J ω = 1 := by simp [J, hG']
      rw [hJ1, one_mul]
      have e1 : P ω * Y ω - V ω * P ω = P ω * (Y ω - V ω) := by ring
      rw [e1, abs_mul, abs_of_nonneg (hP0 ω)]
      by_cases hB' : ω ∈ Bad
      · have hI1 : I ω = 1 := by simp [I, hB']
        rw [hI1, mul_one]
        have : |Y ω - V ω| ≤ BY + BV := (abs_sub _ _).trans (add_le_add (hYB ω) (hVB ω))
        have := mul_le_mul (hPB ω) this (abs_nonneg _) hBp
        linarith [mul_nonneg he (hP0 ω)]
      · have h := hω hG' hB'
        have := mul_le_mul_of_nonneg_left h (hP0 ω)
        linarith [mul_nonneg hc (hI01 ω).1]
    · have hJ0 : J ω = 0 := by simp [J, hG']
      rw [hJ0, zero_mul, abs_zero]; exact hg0
  have hup : D ≤ᵐ[μ] g := hdom.mono fun ω h => (le_abs_self _).trans h
  have hlo : (-D) ≤ᵐ[μ] g := hdom.mono fun ω h => by
    simp only [Pi.neg_apply]; exact (neg_le_abs _).trans h
  have h1 := condExp_mono (m := m) hDi hgi hup
  have h2 := condExp_mono (m := m) hDi.neg hgi hlo
  have h3 := condExp_neg D m (μ := μ)
  -- the right side
  have hg : μ[g | m] =ᵐ[μ] fun ω => e * (μ[P | m]) ω + c * (μ[I | m]) ω := by
    have ha := condExp_add (hPi.const_mul e) (hIi.const_mul c) m (μ := μ)
    have hb := condExp_smul (μ := μ) e P m
    have hc' := condExp_smul (μ := μ) c I m
    have e1 : g = (fun ω => e * P ω) + fun ω => c * I ω := rfl
    have e2 : (fun ω => e * P ω) = e • P := rfl
    have e3 : (fun ω => c * I ω) = c • I := rfl
    rw [e1]
    filter_upwards [ha, hb, hc'] with ω x1 x2 x3
    rw [x1, Pi.add_apply, e2, e3, x2, x3]
    simp
  -- the left side
  have hD : μ[D | m] =ᵐ[μ] fun ω =>
      J ω * ((μ[fun ω => P ω * Y ω | m]) ω - V ω * (μ[P | m]) ω) := by
    have ha := condExp_mul_of_stronglyMeasurable_left (μ := μ) hJs hDi hQi
    have hb := condExp_sub hPYi hVPi m (μ := μ)
    have hc' := condExp_mul_of_stronglyMeasurable_left (μ := μ) hV hVPi hPi
    filter_upwards [ha, hb, hc'] with ω x1 x2 x3
    rw [x1, Pi.mul_apply]
    congr 1
    have eQ : Q = (fun ω => P ω * Y ω) - V * P := rfl
    rw [eQ, x2, Pi.sub_apply, x3, Pi.mul_apply]
  filter_upwards [h1, h2, h3, hg, hD] with ω x1 x2 x3 x4 x5 hωG
  have hJ1 : J ω = 1 := by simp [J, hωG]
  rw [x4] at x1 x2
  rw [x3, Pi.neg_apply, x5, hJ1, one_mul] at x2
  rw [x5, hJ1, one_mul] at x1
  rw [abs_le]
  constructor <;> linarith
/-- Pull-out of `m`-measurable bounded weights from a conditional finite sum. -/
theorem condExp_mul_wsum (hm : m ≤ m0) {ι : Type*} [Fintype ι] {P : Ω → ℝ} (w X : ι → Ω → ℝ)
    {Bp Bw BX : ℝ} (hP : Measurable P) (hPB : ∀ ω, |P ω| ≤ Bp)
    (hw : ∀ j, StronglyMeasurable[m] (w j)) (hwB : ∀ j ω, |w j ω| ≤ Bw)
    (hX : ∀ j, Measurable (X j)) (hXB : ∀ j ω, |X j ω| ≤ BX) :
    μ[fun ω => P ω * ∑ j, w j ω * X j ω | m] =ᵐ[μ]
      fun ω => ∑ j, w j ω * (μ[fun ω => P ω * X j ω | m]) ω := by
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hPB Classical.ofNonempty)
  have hwm : ∀ j, Measurable (w j) := fun j => ((hw j).mono hm).measurable
  have hPX : ∀ j, Integrable (fun ω => P ω * X j ω) μ := fun j =>
    integrable_of_abs_le (hP.mul (hX j)) (B := Bp * BX) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hPB ω) (hXB j ω) (abs_nonneg _) hBp
  have hwPX : ∀ j, Integrable (w j * fun ω => P ω * X j ω) μ := fun j =>
    integrable_of_abs_le ((hwm j).mul (hP.mul (hX j))) (B := Bw * (Bp * BX)) fun ω => by
      rw [Pi.mul_apply, abs_mul, abs_mul]
      have hBw : 0 ≤ Bw := (abs_nonneg _).trans (hwB j ω)
      exact mul_le_mul (hwB j ω) (mul_le_mul (hPB ω) (hXB j ω) (abs_nonneg _) hBp)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hBw
  have e : (fun ω => P ω * ∑ j, w j ω * X j ω) = ∑ j, (w j * fun ω => P ω * X j ω) := by
    funext ω
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.mul_apply]; ring
  rw [e]
  have hsum := condExp_finsetSum (s := Finset.univ) (fun j _ => hwPX j) m (μ := μ)
  have hpull : ∀ᵐ ω ∂μ, ∀ j, (μ[w j * fun ω => P ω * X j ω | m]) ω =
      (w j * μ[fun ω => P ω * X j ω | m]) ω :=
    ae_all_iff.2 fun j => condExp_mul_of_stronglyMeasurable_left (hw j) (hwPX j) (hPX j)
  filter_upwards [hsum, hpull] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => h2 j

end Abstract

end BlockBand.Palm.MomentFlow
