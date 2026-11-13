module

public import BlockBand.Transmission.Generator.DriftOneTools

/-!
# `L²` norm from normalised moments (measure-theoretic step of the `k = 1` drift sum)

`l2_of_moments`: on a probability space, if a.s.
`|Z| ≤ K(a+1)²(t+1)(q+1)³/s³ + 8Δ(q+1)²/s²` with `a, t, q ≥ 0` a.s. bounded, and
`∫(a+1)¹² ≤ M_A`, `∫(t+1)⁶ ≤ M_T`, `∫(q+1)¹⁸ ≤ M_Q`, then
`‖Z‖₂ ≤ √(2K²(M_A+M_T+M_Q))/s³ + √(128M_Q)Δ/s²` (`(xyz)² ≤ x¹² + y⁶ + z¹⁸` by AM–GM).
`moment_shift`: `∫(a+1)ⁿ ≤ 2ⁿ(∫aⁿ + 1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_of_bdd {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ᵐ ω ∂μ, |f ω| ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (hB.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- `∫(a+1)ⁿ ≤ 2ⁿ(∫aⁿ + 1)` for `0 ≤ a ≤ B` a.s. -/
theorem moment_shift {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ᵐ ω ∂μ, 0 ≤ a ω) {B : ℝ}
    (haB : ∀ᵐ ω ∂μ, a ω ≤ B) (n : ℕ) :
    ∫ ω, (a ω + 1) ^ n ∂μ ≤ 2 ^ n * (∫ ω, a ω ^ n ∂μ + 1) := by
  have hb : ∀ᵐ ω ∂μ, |a ω ^ n| ≤ B ^ n := by
    filter_upwards [ha0, haB] with ω h0 h1
    rw [abs_of_nonneg (pow_nonneg h0 n)]; exact pow_le_pow_left₀ h0 h1 n
  have hi : Integrable (fun ω => a ω ^ n) μ := integrable_of_bdd (ha.pow_const n) hb
  have hi1 : Integrable (fun ω => 2 ^ n * (a ω ^ n + 1)) μ :=
    (hi.add (integrable_const 1)).const_mul _
  calc ∫ ω, (a ω + 1) ^ n ∂μ ≤ ∫ ω, 2 ^ n * (a ω ^ n + 1) ∂μ := by
        refine integral_mono_of_nonneg ?_ hi1 ?_
        · filter_upwards [ha0] with ω h using pow_nonneg (by linarith) n
        · filter_upwards [ha0] with ω h using pow_add_one_le h n
    _ = 2 ^ n * (∫ ω, a ω ^ n ∂μ + 1) := by
        rw [integral_const_mul, integral_add hi (integrable_const 1)]; simp

/-- **`L²` bound from normalised moments.** -/
theorem l2_of_moments {Z a t q : Ω → ℝ} (hZ : AEStronglyMeasurable Z μ) (ha : Measurable a)
    (ht : Measurable t) (hq : Measurable q) (ha0 : ∀ᵐ ω ∂μ, 0 ≤ a ω) (ht0 : ∀ᵐ ω ∂μ, 0 ≤ t ω)
    (hq0 : ∀ᵐ ω ∂μ, 0 ≤ q ω) {Ba Bt Bq : ℝ} (haB : ∀ᵐ ω ∂μ, a ω ≤ Ba)
    (htB : ∀ᵐ ω ∂μ, t ω ≤ Bt) (hqB : ∀ᵐ ω ∂μ, q ω ≤ Bq) {s K Δ MA MT MQ : ℝ} (hs : 1 ≤ s)
    (hK : 0 ≤ K) (hΔ : 0 ≤ Δ)
    (hZb : ∀ᵐ ω ∂μ, |Z ω| ≤ K * ((a ω + 1) ^ 2 * (t ω + 1) * (q ω + 1) ^ 3) / s ^ 3 +
      8 * Δ * (q ω + 1) ^ 2 / s ^ 2)
    (hMA : ∫ ω, (a ω + 1) ^ 12 ∂μ ≤ MA) (hMT : ∫ ω, (t ω + 1) ^ 6 ∂μ ≤ MT)
    (hMQ : ∫ ω, (q ω + 1) ^ 18 ∂μ ≤ MQ) :
    eLpNorm Z 2 μ ≤ ENNReal.ofReal (Real.sqrt (2 * K ^ 2 * (MA + MT + MQ)) / s ^ 3 +
      Real.sqrt (128 * MQ) * Δ / s ^ 2) := by
  have hs0 : 0 < s := by linarith
  set F : Ω → ℝ := fun ω => K * ((a ω + 1) ^ 2 * (t ω + 1) * (q ω + 1) ^ 3) / s ^ 3 +
    8 * Δ * (q ω + 1) ^ 2 / s ^ 2
  have hFm : Measurable F := by
    simp only [F]
    exact (((ha.add_const 1).pow_const 2 |>.mul ((ht.add_const 1)) |>.mul
      ((hq.add_const 1).pow_const 3)).const_mul K |>.div_const _).add
      ((((hq.add_const 1).pow_const 2).const_mul _).div_const _)
  have hF0 : ∀ᵐ ω ∂μ, 0 ≤ F ω := by
    filter_upwards [ha0, ht0, hq0] with ω h1 h2 h3
    simp only [F]; positivity
  have hFB : ∀ᵐ ω ∂μ, F ω ≤ K * ((Ba + 1) ^ 2 * (Bt + 1) * (Bq + 1) ^ 3) / s ^ 3 +
      8 * Δ * (Bq + 1) ^ 2 / s ^ 2 := by
    filter_upwards [ha0, ht0, hq0, haB, htB, hqB] with ω h1 h2 h3 h4 h5 h6
    have : 0 ≤ Bt + 1 := by linarith
    have : 0 ≤ Bq + 1 := by linarith
    simp only [F]; gcongr
  have hZF : eLpNorm Z 2 μ ≤ eLpNorm F 2 μ := by
    refine eLpNorm_mono_ae hZ ?_
    filter_upwards [hZb, hF0] with ω h h0
    rw [Real.norm_eq_abs, Real.norm_of_nonneg h0]; exact h
  refine hZF.trans (eLpNorm_two_le_of_integral_sq hFm.aestronglyMeasurable hF0 hFB
    (A := 2 * K ^ 2 * (MA + MT + MQ) / s ^ 6 + 128 * MQ * Δ ^ 2 / s ^ 4) ?_ |>.trans ?_)
  · -- the second moment of `F`
    set G : Ω → ℝ := fun ω => 2 * K ^ 2 / s ^ 6 * ((a ω + 1) ^ 12 + (t ω + 1) ^ 6 +
      (q ω + 1) ^ 18) + 128 * Δ ^ 2 / s ^ 4 * (q ω + 1) ^ 18
    have hbd : ∀ (f : Ω → ℝ) (B : ℝ) (n : ℕ), Measurable f → (∀ᵐ ω ∂μ, 0 ≤ f ω) →
        (∀ᵐ ω ∂μ, f ω ≤ B) → Integrable (fun ω => (f ω + 1) ^ n) μ := fun f B n hf h0 hB =>
      integrable_of_bdd ((hf.add_const 1).pow_const n) (B := (B + 1) ^ n) (by
        filter_upwards [h0, hB] with ω h1 h2
        rw [abs_of_nonneg (by positivity)]; exact pow_le_pow_left₀ (by linarith) (by linarith) n)
    have iA := hbd a Ba 12 ha ha0 haB
    have iT := hbd t Bt 6 ht ht0 htB
    have iQ := hbd q Bq 18 hq hq0 hqB
    have hFG : ∀ᵐ ω ∂μ, F ω ^ 2 ≤ G ω := by
      filter_upwards [ha0, ht0, hq0] with ω h1 h2 h3
      simp only [F, G]
      set x := (a ω + 1) ^ 2 * (t ω + 1) * (q ω + 1) ^ 3
      set Q := q ω + 1
      have hQ : 1 ≤ Q := by simp only [Q]; linarith
      have hx2 : x ^ 2 ≤ (a ω + 1) ^ 12 + (t ω + 1) ^ 6 + (q ω + 1) ^ 18 := by
        have e : x ^ 2 = (a ω + 1) ^ 4 * (t ω + 1) ^ 2 * (q ω + 1) ^ 6 := by simp only [x]; ring
        have := amgm3 (x := (a ω + 1) ^ 4) (y := (t ω + 1) ^ 2) (z := (q ω + 1) ^ 6)
          (by positivity) (by positivity) (by positivity)
        rw [e]; convert this using 2 <;> ring
      have hQ4 : Q ^ 4 ≤ Q ^ 18 := pow_le_pow_right₀ hQ (by norm_num)
      have h4 : (K * x / s ^ 3 + 8 * Δ * Q ^ 2 / s ^ 2) ^ 2 ≤
          2 * (K * x / s ^ 3) ^ 2 + 2 * (8 * Δ * Q ^ 2 / s ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (K * x / s ^ 3 - 8 * Δ * Q ^ 2 / s ^ 2)]
      have h5 : 2 * (K * x / s ^ 3) ^ 2 = 2 * K ^ 2 / s ^ 6 * x ^ 2 := by field_simp
      have h6 : 2 * (8 * Δ * Q ^ 2 / s ^ 2) ^ 2 = 128 * Δ ^ 2 / s ^ 4 * Q ^ 4 := by field_simp; ring
      have h7 : 2 * K ^ 2 / s ^ 6 * x ^ 2 ≤ 2 * K ^ 2 / s ^ 6 *
          ((a ω + 1) ^ 12 + (t ω + 1) ^ 6 + (q ω + 1) ^ 18) :=
        mul_le_mul_of_nonneg_left hx2 (by positivity)
      have h8 : 128 * Δ ^ 2 / s ^ 4 * Q ^ 4 ≤ 128 * Δ ^ 2 / s ^ 4 * Q ^ 18 :=
        mul_le_mul_of_nonneg_left hQ4 (by positivity)
      linarith
    have hGi : Integrable G μ :=
      (((iA.add iT).add iQ).const_mul _).add (iQ.const_mul _)
    have hF2i : Integrable (fun ω => F ω ^ 2) μ := by
      refine Integrable.mono' hGi (hFm.pow_const 2).aestronglyMeasurable ?_
      filter_upwards [hFG] with ω h
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h
    refine (integral_mono_ae hF2i hGi hFG).trans (le_of_eq_of_le
      (b := 2 * K ^ 2 / s ^ 6 * (∫ ω, (a ω + 1) ^ 12 ∂μ + ∫ ω, (t ω + 1) ^ 6 ∂μ +
        ∫ ω, (q ω + 1) ^ 18 ∂μ) + 128 * Δ ^ 2 / s ^ 4 * ∫ ω, (q ω + 1) ^ 18 ∂μ) ?_ ?_)
    · have i2 : Integrable (fun ω => (a ω + 1) ^ 12 + (t ω + 1) ^ 6) μ := iA.add iT
      have i3 : Integrable (fun ω => (a ω + 1) ^ 12 + (t ω + 1) ^ 6 + (q ω + 1) ^ 18) μ :=
        i2.add iQ
      have i4 : Integrable (fun ω => 2 * K ^ 2 / s ^ 6 *
          ((a ω + 1) ^ 12 + (t ω + 1) ^ 6 + (q ω + 1) ^ 18)) μ := i3.const_mul _
      have i5 : Integrable (fun ω => 128 * Δ ^ 2 / s ^ 4 * (q ω + 1) ^ 18) μ := iQ.const_mul _
      simp only [G]
      rw [integral_add i4 i5, integral_const_mul, integral_const_mul, integral_add i2 iQ,
        integral_add iA iT]
    · have c1 : 0 ≤ 2 * K ^ 2 / s ^ 6 := by positivity
      have c2 : 0 ≤ 128 * Δ ^ 2 / s ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hMA hMT) hMQ) c1
      have := mul_le_mul_of_nonneg_left hMQ c2
      have e1 : 2 * K ^ 2 * (MA + MT + MQ) / s ^ 6 = 2 * K ^ 2 / s ^ 6 * (MA + MT + MQ) := by ring
      have e2 : 128 * MQ * Δ ^ 2 / s ^ 4 = 128 * Δ ^ 2 / s ^ 4 * MQ := by ring
      linarith
  · -- the square root
    refine ENNReal.ofReal_le_ofReal ?_
    have hMA0 : 0 ≤ MA := (integral_nonneg fun ω => by positivity).trans hMA
    have hMT0 : 0 ≤ MT := le_trans (integral_nonneg fun ω => by positivity) hMT
    have hMQ0 : 0 ≤ MQ := le_trans (integral_nonneg fun ω => by positivity) hMQ
    set a' := 2 * K ^ 2 * (MA + MT + MQ)
    set b' := 128 * MQ
    have ha' : 0 ≤ a' := by positivity
    have hb' : 0 ≤ b' := by positivity
    set Y := Real.sqrt a' / s ^ 3 + Real.sqrt b' * Δ / s ^ 2
    have hY : 0 ≤ Y := by positivity
    have hX : a' / s ^ 6 + 128 * MQ * Δ ^ 2 / s ^ 4 ≤ Y ^ 2 := by
      have e1 : (Real.sqrt a' / s ^ 3) ^ 2 = a' / s ^ 6 := by
        rw [div_pow, Real.sq_sqrt ha']; ring
      have e2 : (Real.sqrt b' * Δ / s ^ 2) ^ 2 = 128 * MQ * Δ ^ 2 / s ^ 4 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hb']; ring
      have h0 : 0 ≤ 2 * (Real.sqrt a' / s ^ 3) * (Real.sqrt b' * Δ / s ^ 2) := by positivity
      have : Y ^ 2 = (Real.sqrt a' / s ^ 3) ^ 2 + 2 * (Real.sqrt a' / s ^ 3) *
          (Real.sqrt b' * Δ / s ^ 2) + (Real.sqrt b' * Δ / s ^ 2) ^ 2 := by simp only [Y]; ring
      rw [this, e1, e2]; linarith
    calc Real.sqrt (a' / s ^ 6 + 128 * MQ * Δ ^ 2 / s ^ 4) ≤ Real.sqrt (Y ^ 2) :=
          Real.sqrt_le_sqrt hX
      _ = Y := Real.sqrt_sq hY

end BlockBand.Transmission.Generator
