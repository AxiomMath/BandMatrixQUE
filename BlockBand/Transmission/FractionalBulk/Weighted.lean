module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Probability.Notation

/-!
# A weighted second-moment lower bound

**`weighted_lower`**: on a probability space let `Y` be centred with `E|Y|² ≥ a`,
`E|Y|⁴ ≤ K a²` (`K ≥ 1`), and `N ≥ 1` with `E N² ≤ M`. Then for every constant `m ∈ ℂ`,
`E[|Y + m|²/N] ≥ a/(4K + M/2)`.

Proof: `E|Y+m|² = E|Y|² + |m|² =: S ≥ a + |m|²`, `E|Y+m|⁴ ≤ 8K(a + |m|²)²`, and the two
pointwise AM-GM inequalities `q ≤ (λ/2)(q/N) + qN/(2λ)`, `2qN ≤ θq²/(a+x) + (a+x)N²/θ`.
This replaces the restriction to `{‖U‖ ≤ K}` by the random weight `1/N`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory
open scoped ComplexConjugate

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem norm_add_sq_eq (z m : ℂ) : ‖z + m‖ ^ 2 = ‖z‖ ^ 2 + 2 * (z * conj m).re + ‖m‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]
  ring

theorem pow4_add_le (u v : ℝ) : (u + v) ^ 4 ≤ 8 * (u ^ 4 + v ^ 4) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg (u ^ 2 - v ^ 2),
    mul_nonneg (sq_nonneg (u + v)) (sq_nonneg (u - v))]

/-- **Weighted lower bound.** -/
theorem weighted_lower [IsProbabilityMeasure μ] {Y : Ω → ℂ} {N : Ω → ℝ} {a K M : ℝ} (m : ℂ)
    (ha : 0 < a) (hK : 1 ≤ K) (hYm : AEStronglyMeasurable Y μ)
    (hNm : AEStronglyMeasurable N μ) (hN1 : ∀ ω, 1 ≤ N ω)
    (hYi : Integrable Y μ) (hY0 : ∫ ω, Y ω ∂μ = 0)
    (hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) μ) (hY2 : a ≤ ∫ ω, ‖Y ω‖ ^ 2 ∂μ)
    (hY4i : Integrable (fun ω => ‖Y ω‖ ^ 4) μ) (hY4 : ∫ ω, ‖Y ω‖ ^ 4 ∂μ ≤ K * a ^ 2)
    (hN2i : Integrable (fun ω => N ω ^ 2) μ) (hN2 : ∫ ω, N ω ^ 2 ∂μ ≤ M) :
    a / (4 * K + M / 2) ≤ ∫ ω, ‖Y ω + m‖ ^ 2 / N ω ∂μ := by
  set x := ‖m‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun ω => by positivity) hN2
  have hN0 : ∀ ω, 0 < N ω := fun ω => by linarith [hN1 ω]
  -- integrability
  have hZm : AEStronglyMeasurable (fun ω => Y ω + m) μ := hYm.add aestronglyMeasurable_const
  have hZ2i : Integrable (fun ω => ‖Y ω + m‖ ^ 2) μ := by
    refine Integrable.mono' ((hY2i.const_mul 2).add (integrable_const (2 * x)))
      (hZm.norm.pow 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    have := norm_add_le (Y ω) m
    have h1 := pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith [norm_nonneg (Y ω), norm_nonneg m, sq_nonneg (‖Y ω‖ - ‖m‖)]
  have hZ4i : Integrable (fun ω => ‖Y ω + m‖ ^ 4) μ := by
    refine Integrable.mono' ((hY4i.const_mul 8).add (integrable_const (8 * x ^ 2)))
      (hZm.norm.pow 4) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (Y ω) m) 4
    have h2 := pow4_add_le ‖Y ω‖ ‖m‖
    have : x ^ 2 = ‖m‖ ^ 4 := by rw [hx]; ring
    rw [this]; linarith
  have hGi : Integrable (fun ω => ‖Y ω + m‖ ^ 2 / N ω) μ := by
    refine Integrable.mono' hZ2i ((hZm.norm.pow 2).div₀ hNm) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (div_nonneg (by positivity) (hN0 ω).le)]
    exact div_le_self (by positivity) (hN1 ω)
  have hHi : Integrable (fun ω => ‖Y ω + m‖ ^ 2 * N ω) μ := by
    refine Integrable.mono' (hZ4i.add hN2i) ((hZm.norm.pow 2).mul hNm)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hN0 ω).le)]
    simp only [Pi.add_apply]
    have e : ‖Y ω + m‖ ^ 4 = (‖Y ω + m‖ ^ 2) ^ 2 := by ring
    have hq : 0 ≤ ‖Y ω + m‖ ^ 2 * N ω := mul_nonneg (by positivity) (hN0 ω).le
    nlinarith [sq_nonneg (‖Y ω + m‖ ^ 2 - N ω)]
  -- the second moment
  have hS : ∫ ω, ‖Y ω + m‖ ^ 2 ∂μ = ∫ ω, ‖Y ω‖ ^ 2 ∂μ + x := by
    simp_rw [norm_add_sq_eq]
    have hc : Integrable (fun ω => 2 * (Y ω * conj m).re) μ :=
      ((hYi.mul_const (conj m)).re).const_mul 2
    rw [integral_add (f := fun ω => ‖Y ω‖ ^ 2 + 2 * (Y ω * conj m).re) (hY2i.add hc)
      (integrable_const _), integral_add hY2i hc, integral_const, integral_const_mul]
    have : ∫ ω, (Y ω * conj m).re ∂μ = 0 := by
      have h := integral_re (𝕜 := ℂ) (hYi.mul_const (conj m))
      refine h.trans ?_
      rw [integral_mul_const, hY0, zero_mul]
      rfl
    rw [this]
    simp [hx]
  -- the fourth moment
  have hF : ∫ ω, ‖Y ω + m‖ ^ 4 ∂μ ≤ 8 * K * (a + x) ^ 2 := by
    have hpt : ∀ ω, ‖Y ω + m‖ ^ 4 ≤ 8 * ‖Y ω‖ ^ 4 + 8 * x ^ 2 := fun ω => by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (Y ω) m) 4
      have h2 := pow4_add_le ‖Y ω‖ ‖m‖
      have : x ^ 2 = ‖m‖ ^ 4 := by rw [hx]; ring
      rw [this]; linarith
    calc ∫ ω, ‖Y ω + m‖ ^ 4 ∂μ ≤ ∫ ω, (8 * ‖Y ω‖ ^ 4 + 8 * x ^ 2) ∂μ :=
          integral_mono hZ4i ((hY4i.const_mul 8).add (integrable_const _)) hpt
      _ = 8 * ∫ ω, ‖Y ω‖ ^ 4 ∂μ + 8 * x ^ 2 := by
          rw [integral_add (hY4i.const_mul 8) (integrable_const _), integral_const_mul,
            integral_const]
          simp
      _ ≤ 8 * (K * a ^ 2) + 8 * x ^ 2 := by linarith
      _ ≤ 8 * K * (a + x) ^ 2 := by nlinarith [mul_nonneg ha.le hx0, sq_nonneg x]
  -- `E[|Z|²N] ≤ (a+x)(4K + M/2)`
  set b := a + x with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  set Λ := 4 * K + M / 2 with hΛ
  have hΛ0 : 0 < Λ := by rw [hΛ]; linarith
  have hH : ∫ ω, ‖Y ω + m‖ ^ 2 * N ω ∂μ ≤ b * Λ := by
    have hpt : ∀ ω, ‖Y ω + m‖ ^ 2 * N ω ≤ ‖Y ω + m‖ ^ 4 / (2 * b) + b * N ω ^ 2 / 2 := by
      intro ω
      have h := sq_nonneg (‖Y ω + m‖ ^ 2 - b * N ω)
      rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
      nlinarith
    calc ∫ ω, ‖Y ω + m‖ ^ 2 * N ω ∂μ ≤
          ∫ ω, (‖Y ω + m‖ ^ 4 / (2 * b) + b * N ω ^ 2 / 2) ∂μ :=
          integral_mono hHi ((hZ4i.div_const _).add ((hN2i.const_mul b).div_const _)) hpt
      _ = (∫ ω, ‖Y ω + m‖ ^ 4 ∂μ) / (2 * b) + b * (∫ ω, N ω ^ 2 ∂μ) / 2 := by
          rw [integral_add (hZ4i.div_const _) ((hN2i.const_mul b).div_const _), integral_div,
            integral_div, integral_const_mul]
      _ ≤ 8 * K * b ^ 2 / (2 * b) + b * M / 2 := by gcongr
      _ = b * Λ := by rw [hΛ]; field_simp; ring
  -- `S ≤ (Λ/2) G + (1/(2Λ)) E[|Z|²N]`
  have hS2 : ∫ ω, ‖Y ω + m‖ ^ 2 ∂μ ≤
      Λ / 2 * ∫ ω, ‖Y ω + m‖ ^ 2 / N ω ∂μ + (∫ ω, ‖Y ω + m‖ ^ 2 * N ω ∂μ) / (2 * Λ) := by
    have hpt : ∀ ω, ‖Y ω + m‖ ^ 2 ≤
        Λ / 2 * (‖Y ω + m‖ ^ 2 / N ω) + ‖Y ω + m‖ ^ 2 * N ω / (2 * Λ) := by
      intro ω
      have hq : 0 ≤ ‖Y ω + m‖ ^ 2 := by positivity
      have hN := hN0 ω
      have key : 2 * Λ * N ω * ‖Y ω + m‖ ^ 2 ≤
          Λ ^ 2 * ‖Y ω + m‖ ^ 2 + N ω ^ 2 * ‖Y ω + m‖ ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg (Λ - N ω)) hq]
      have e : Λ / 2 * (‖Y ω + m‖ ^ 2 / N ω) + ‖Y ω + m‖ ^ 2 * N ω / (2 * Λ) =
          (Λ ^ 2 * ‖Y ω + m‖ ^ 2 + N ω ^ 2 * ‖Y ω + m‖ ^ 2) / (2 * Λ * N ω) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      linarith
    calc ∫ ω, ‖Y ω + m‖ ^ 2 ∂μ ≤
          ∫ ω, (Λ / 2 * (‖Y ω + m‖ ^ 2 / N ω) + ‖Y ω + m‖ ^ 2 * N ω / (2 * Λ)) ∂μ :=
          integral_mono hZ2i ((hGi.const_mul _).add (hHi.div_const _)) hpt
      _ = _ := by rw [integral_add (hGi.const_mul _) (hHi.div_const _), integral_const_mul,
            integral_div]
  have hHΛ : (∫ ω, ‖Y ω + m‖ ^ 2 * N ω ∂μ) / (2 * Λ) ≤ b / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hSb : b ≤ ∫ ω, ‖Y ω + m‖ ^ 2 ∂μ := by rw [hS, hb]; linarith
  have hG : b / Λ ≤ ∫ ω, ‖Y ω + m‖ ^ 2 / N ω ∂μ := by
    rw [div_le_iff₀ hΛ0]
    nlinarith
  calc a / (4 * K + M / 2) = a / Λ := by rw [hΛ]
    _ ≤ b / Λ := by gcongr; rw [hb]; linarith
    _ ≤ _ := hG

end BlockBand.Transmission.FractionalBulk
