module

public import BlockBand.Transmission.LawDecay.StepAbs

/-!
# `step_abstract`: the one-step Lyapunov inequality in expectation

For a sub-σ-algebra `m`, a current state `(x, y)` (`m`-measurable) and a next state `(x', y')`
in the domain `Dom K`, whose conditional increments are `e1 + A1`, `e2 + A2`, `e11 + B11`,
`e12 + B12`, a generator bound `coefX·A1 + coefY·A2 + coefXX·B11 + coefXY·B12 ≤
-c(Φ_ε - 2√ε)` gives
`E Φ_ε(x', y') ≤ E Φ_ε(x, y) - c(E Φ_ε(x, y) - 2√ε) + ε^{-5/2} Σ E|e| +
E[ε^{-7/2}(|x' - x|³ + (x' - x)²|y' - y|)/6]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The generator term: `E[Σ φ·A] ≤ -c(E Φ - 2√ε)`. -/
theorem gen_term_le {ε c : ℝ} {L φ1 φ2 φ3 φ4 A1 A2 B11 B12 : Ω → ℝ} {U : ℝ}
    (hL : Integrable L μ) (h1 : Integrable (fun ω => φ1 ω * A1 ω) μ)
    (h2 : Integrable (fun ω => φ2 ω * A2 ω) μ) (h3 : Integrable (fun ω => φ3 ω * B11 ω) μ)
    (h4 : Integrable (fun ω => φ4 ω * B12 ω) μ)
    (hG : ∀ᵐ ω ∂μ, φ1 ω * A1 ω + φ2 ω * A2 ω + φ3 ω * B11 ω + φ4 ω * B12 ω ≤
      -c * (L ω - 2 * Real.sqrt ε)) {e1 e2 e3 e4 : ℝ} :
    ∫ ω, φ1 ω * A1 ω ∂μ + ∫ ω, φ2 ω * A2 ω ∂μ + ∫ ω, φ3 ω * B11 ω ∂μ +
      ∫ ω, φ4 ω * B12 ω ∂μ + U * (e1 + e2 + e3 + e4) ≤
      -c * (∫ ω, L ω ∂μ - 2 * Real.sqrt ε) + U * (e1 + e2 + e3 + e4) := by
  have hR : Integrable (fun ω => -c * (L ω - 2 * Real.sqrt ε)) μ :=
    (hL.sub (integrable_const _)).const_mul _
  have i12 : Integrable (fun ω => φ1 ω * A1 ω + φ2 ω * A2 ω) μ := h1.add h2
  have i123 : Integrable (fun ω => φ1 ω * A1 ω + φ2 ω * A2 ω + φ3 ω * B11 ω) μ := i12.add h3
  have i1234 : Integrable (fun ω => φ1 ω * A1 ω + φ2 ω * A2 ω + φ3 ω * B11 ω +
    φ4 ω * B12 ω) μ := i123.add h4
  have hm := integral_mono_ae i1234 hR hG
  rw [integral_add i123 h4, integral_add i12 h3, integral_add h1 h2,
    integral_const_mul, integral_sub hL (integrable_const _), integral_const] at hm
  simp only [probReal_univ, one_smul] at hm
  linarith

/-- **The one-step Lyapunov inequality in expectation.** -/
theorem step_abstract (hm : m ≤ m₀) {ε c K : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x y x' y' A1 A2 B11 B12 e1 e2 e11 e12 : Ω → ℝ}
    (hx : Measurable[m] x) (hy : Measurable[m] y) (hx' : Measurable x') (hy' : Measurable y')
    (hd : ∀ᵐ ω ∂μ, Dom K (x ω) (y ω) ∧ Dom K (x' ω) (y' ω))
    (hA1 : Integrable A1 μ) (hA2 : Integrable A2 μ) (hB11 : Integrable B11 μ)
    (hB12 : Integrable B12 μ) (he1 : Integrable e1 μ) (he2 : Integrable e2 μ)
    (he11 : Integrable e11 μ) (he12 : Integrable e12 μ)
    (hc1 : μ[fun ω => x' ω - x ω | m] = e1 + A1) (hc2 : μ[fun ω => y' ω - y ω | m] = e2 + A2)
    (hc11 : μ[fun ω => (x' ω - x ω) * (x' ω - x ω) | m] = e11 + B11)
    (hc12 : μ[fun ω => (x' ω - x ω) * (y' ω - y ω) | m] = e12 + B12)
    (hG : ∀ᵐ ω ∂μ, coefX ε (x ω) (y ω) * A1 ω + coefY ε (x ω) * A2 ω +
      coefXX ε (x ω) (y ω) * B11 ω + coefXY ε (x ω) * B12 ω ≤
        -c * (lyap ε (x ω) (y ω) - 2 * Real.sqrt ε)) :
    ∫ ω, lyap ε (x' ω) (y' ω) ∂μ ≤ ∫ ω, lyap ε (x ω) (y ω) ∂μ -
        c * (∫ ω, lyap ε (x ω) (y ω) ∂μ - 2 * Real.sqrt ε) +
      (Real.sqrt ε)⁻¹ ^ 5 * (∫ ω, |e1 ω| ∂μ + ∫ ω, |e2 ω| ∂μ + ∫ ω, |e11 ω| ∂μ +
        ∫ ω, |e12 ω| ∂μ) +
      ∫ ω, ε ^ (-7 / 2 : ℝ) * (|x' ω - x ω| ^ 3 + (x' ω - x ω) ^ 2 * |y' ω - y ω|) / 6 ∂μ := by
  set U := (Real.sqrt ε)⁻¹ ^ 5
  have hx0 : Measurable x := hx.mono hm le_rfl
  have hy0 : Measurable y := hy.mono hm le_rfl
  -- coefficient functions
  have m1 : Measurable[m] fun ω => coefX ε (x ω) (y ω) := (measurable_coefX ε).comp (hx.prodMk hy)
  have m2 : Measurable[m] fun ω => coefY ε (x ω) := (measurable_coefY ε).comp hx
  have m3 : Measurable[m] fun ω => coefXX ε (x ω) (y ω) :=
    (measurable_coefXX ε).comp (hx.prodMk hy)
  have m4 : Measurable[m] fun ω => coefXY ε (x ω) := (measurable_coefXY ε).comp hx
  have hcb := hd.mono fun ω h => coef_bounds hε hε1 h.1.1 h.1.2.1
  have b1 : ∀ᵐ ω ∂μ, |coefX ε (x ω) (y ω)| ≤ U := hcb.mono fun ω h => h.1
  have b2 : ∀ᵐ ω ∂μ, |coefY ε (x ω)| ≤ U := hcb.mono fun ω h => h.2.1
  have b3 : ∀ᵐ ω ∂μ, |coefXX ε (x ω) (y ω)| ≤ U := hcb.mono fun ω h => h.2.2.1
  have b4 : ∀ᵐ ω ∂μ, |coefXY ε (x ω)| ≤ U := hcb.mono fun ω h => h.2.2.2
  have n1 := b1.mono fun ω h => (by simpa [Real.norm_eq_abs] using h :
    ‖coefX ε (x ω) (y ω)‖ ≤ U)
  have n2 := b2.mono fun ω h => (by simpa [Real.norm_eq_abs] using h : ‖coefY ε (x ω)‖ ≤ U)
  have n3 := b3.mono fun ω h => (by simpa [Real.norm_eq_abs] using h :
    ‖coefXX ε (x ω) (y ω)‖ ≤ U)
  have n4 := b4.mono fun ω h => (by simpa [Real.norm_eq_abs] using h : ‖coefXY ε (x ω)‖ ≤ U)
  -- increments
  have hsub := hd.mono fun ω h => abs_sub_le_of_dom h.1 h.2
  have ih : Integrable (fun ω => x' ω - x ω) μ :=
    integrable_of_abs_le (hx'.sub hx0) (hsub.mono fun ω h => h.1)
  have ik : Integrable (fun ω => y' ω - y ω) μ :=
    integrable_of_abs_le (hy'.sub hy0) (hsub.mono fun ω h => h.2)
  have ihh : Integrable (fun ω => (x' ω - x ω) * (x' ω - x ω)) μ :=
    integrable_of_abs_le ((hx'.sub hx0).mul (hx'.sub hx0)) (C := K * K) (hsub.mono fun ω h => by
      rw [abs_mul]; exact mul_le_mul h.1 h.1 (abs_nonneg _) ((abs_nonneg _).trans h.1))
  have ihk : Integrable (fun ω => (x' ω - x ω) * (y' ω - y ω)) μ :=
    integrable_of_abs_le ((hx'.sub hx0).mul (hy'.sub hy0)) (C := K * K) (hsub.mono fun ω h => by
      rw [abs_mul]; exact mul_le_mul h.1 h.2 (abs_nonneg _) ((abs_nonneg _).trans h.1))
  -- the Lyapunov values and the remainder
  have iL : Integrable (fun ω => lyap ε (x ω) (y ω)) μ :=
    integrable_of_abs_le ((measurable_lyap ε).comp (hx0.prodMk hy0)) (C := K + 2)
      (hd.mono fun ω h => (abs_lyap_le hε hε1 (h.1.1.trans h.1.2.1) h.1.1 h.1.2.2.1).trans
        (by linarith [h.1.2.2.2]))
  have iL' : Integrable (fun ω => lyap ε (x' ω) (y' ω)) μ :=
    integrable_of_abs_le ((measurable_lyap ε).comp (hx'.prodMk hy')) (C := K + 2)
      (hd.mono fun ω h => (abs_lyap_le hε hε1 (h.2.1.trans h.2.2.1) h.2.1 h.2.2.2.1).trans
        (by linarith [h.2.2.2.2]))
  have iR : Integrable (fun ω => ε ^ (-7 / 2 : ℝ) *
      (|x' ω - x ω| ^ 3 + (x' ω - x ω) ^ 2 * |y' ω - y ω|) / 6) μ := by
    have i3 : Integrable (fun ω => |x' ω - x ω| ^ 3) μ :=
      integrable_of_abs_le (by fun_prop) (C := K ^ 3) (hsub.mono fun ω h => by
        rw [abs_pow, abs_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h.1 3)
    have i2 : Integrable (fun ω => (x' ω - x ω) ^ 2 * |y' ω - y ω|) μ :=
      integrable_of_abs_le (by fun_prop) (C := K ^ 2 * K) (hsub.mono fun ω h => by
        rw [abs_mul, abs_pow, abs_abs]
        have hK : 0 ≤ K := (abs_nonneg _).trans h.1
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h.1 2) h.2 (abs_nonneg _)
          (by positivity))
    exact ((i3.add i2).const_mul _).div_const 6
  -- terms
  have t1 := integral_test_le hm m1 b1 ih hA1 he1 hc1
  have t2 := integral_test_le hm m2 b2 ik hA2 he2 hc2
  have t3 := integral_test_le hm m3 b3 ihh hB11 he11 hc11
  have t4 := integral_test_le hm m4 b4 ihk hB12 he12 hc12
  have iT1 := ih.bdd_mul (m1.mono hm le_rfl).aestronglyMeasurable n1
  have iT2 := ik.bdd_mul (m2.mono hm le_rfl).aestronglyMeasurable n2
  have iT3 := ihh.bdd_mul (m3.mono hm le_rfl).aestronglyMeasurable n3
  have iT4 := ihk.bdd_mul (m4.mono hm le_rfl).aestronglyMeasurable n4
  have gA := gen_term_le (U := U) (e1 := ∫ ω, |e1 ω| ∂μ) (e2 := ∫ ω, |e2 ω| ∂μ)
    (e3 := ∫ ω, |e11 ω| ∂μ) (e4 := ∫ ω, |e12 ω| ∂μ) iL
    (hA1.bdd_mul (m1.mono hm le_rfl).aestronglyMeasurable n1)
    (hA2.bdd_mul (m2.mono hm le_rfl).aestronglyMeasurable n2)
    (hB11.bdd_mul (m3.mono hm le_rfl).aestronglyMeasurable n3)
    (hB12.bdd_mul (m4.mono hm le_rfl).aestronglyMeasurable n4) hG
  -- integrate the pointwise bound
  have iS1 : Integrable (fun ω => coefX ε (x ω) (y ω) * (x' ω - x ω) +
      coefY ε (x ω) * (y' ω - y ω)) μ := iT1.add iT2
  have iS2 : Integrable (fun ω => coefXX ε (x ω) (y ω) * ((x' ω - x ω) * (x' ω - x ω)) +
      coefXY ε (x ω) * ((x' ω - x ω) * (y' ω - y ω))) μ := iT3.add iT4
  have iS0 : Integrable (fun ω => lyap ε (x ω) (y ω) + (coefX ε (x ω) (y ω) * (x' ω - x ω) +
      coefY ε (x ω) * (y' ω - y ω))) μ := iL.add iS1
  have iS3 : Integrable (fun ω => lyap ε (x ω) (y ω) + (coefX ε (x ω) (y ω) * (x' ω - x ω) +
      coefY ε (x ω) * (y' ω - y ω)) +
      (coefXX ε (x ω) (y ω) * ((x' ω - x ω) * (x' ω - x ω)) +
      coefXY ε (x ω) * ((x' ω - x ω) * (y' ω - y ω)))) μ := iS0.add iS2
  have iS4 : Integrable (fun ω => lyap ε (x ω) (y ω) + (coefX ε (x ω) (y ω) * (x' ω - x ω) +
      coefY ε (x ω) * (y' ω - y ω)) +
      (coefXX ε (x ω) (y ω) * ((x' ω - x ω) * (x' ω - x ω)) +
      coefXY ε (x ω) * ((x' ω - x ω) * (y' ω - y ω))) + ε ^ (-7 / 2 : ℝ) *
        (|x' ω - x ω| ^ 3 + (x' ω - x ω) ^ 2 * |y' ω - y ω|) / 6) μ := iS3.add iR
  have hpt := integral_mono_ae iL' iS4 (hd.mono fun ω h => lyap_step_dom hε hε1 h.1 h.2)
  rw [integral_add iS3 iR, integral_add iS0 iS2, integral_add iL iS1, integral_add iT1 iT2,
    integral_add iT3 iT4] at hpt
  linarith

end BlockBand.Transmission.LawDecay
