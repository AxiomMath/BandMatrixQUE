module

public import BlockBand.SourceProcess.FullSource.TraceAlgebra
public import BlockBand.Transmission.PassiveLayer.MomentAlgebra

/-!
# The one-layer moment step of a positive source

Abstract one-layer setting: a probability space (the fresh layer), a random matrix `𝓔`
(the Ward noise `NN* - I`) and a deterministic factor `S` of the old source `Y = S*S`.
* `trace_noise`, `momBd_of_centered`: `y = Re Tr(S*S𝓔)` has `‖y‖_q ≤ (σ + c) Re Tr(S*S)` and
  `|E y| ≤ c Re Tr(S*S)`
  when `‖E𝓔‖ ≤ c` and the centered bilinear entries of `𝓔` have `L^q` norm `≤ σ‖u‖‖v‖`;
* `integral_pow_step`: for a real `Y` with `t + Y ≥ 0`, `|EY| ≤ ct`, `‖Y‖₂ ≤ (c+σ₂)t`,
  `‖Y‖_n ≤ (c+σ_n)t`: `E(t+Y)^n ≤ t^n(1 + nc + 2^n((c+σ₂)² + (c+σ_n)^n))` (integer `n ≥ 2`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open scoped ENNReal Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- From an `L^n` bound to the `n`-th absolute moment (integer `n ≥ 1`). -/
theorem integral_abs_pow_le {f : Ω → ℝ} {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 ≤ C)
    (hf : MomBd ν f n C) :
    Integrable (fun ω => |f ω| ^ n) ν ∧ ∫ ω, |f ω| ^ n ∂ν ≤ C ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : ENNReal.ofReal n ≠ 0 := by simp; omega
  have hmem : MemLp f (ENNReal.ofReal n) ν := lt_of_le_of_lt hf.2 ENNReal.ofReal_lt_top
  have hint := hmem.integrable_norm_rpow'
  rw [ENNReal.toReal_ofReal hn0.le] at hint
  have heq : (fun ω => ‖f ω‖ ^ (n : ℝ)) = fun ω => |f ω| ^ n := by
    funext ω; rw [Real.rpow_natCast, Real.norm_eq_abs]
  rw [heq] at hint
  refine ⟨hint, ?_⟩
  have hl : ∫⁻ ω, ‖f ω‖ₑ ^ (n : ℝ) ∂ν ≤ ENNReal.ofReal C ^ (n : ℝ) := by
    have h := hf.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf.1,
      ENNReal.toReal_ofReal hn0.le] at h
    have h' := ENNReal.rpow_le_rpow h (le_of_lt hn0)
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hn0.ne', ENNReal.rpow_one] at h'
  have hl' : ENNReal.ofReal (∫ ω, |f ω| ^ n ∂ν) ≤ ENNReal.ofReal (C ^ n) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => by
      positivity)]
    refine le_of_eq_of_le (lintegral_congr fun ω => ?_) (hl.trans (le_of_eq ?_))
    · rw [← Real.norm_eq_abs, ← ofReal_norm, ENNReal.rpow_natCast,
        ENNReal.ofReal_pow (norm_nonneg _)]
    · rw [ENNReal.ofReal_rpow_of_nonneg hC hn0.le, Real.rpow_natCast]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hl'

/-- `‖Y‖_q ≤ σ + c` from `‖Y - EY‖_q ≤ σ` and `|EY| ≤ c`. -/
theorem momBd_of_centered {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y ν) {q σ c : ℝ} (hq : 1 ≤ q)
    (hσ0 : 0 ≤ σ) (hc : |∫ ω, Y ω ∂ν| ≤ c)
    (hσ : eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂ν) (ENNReal.ofReal q) ν ≤ ENNReal.ofReal σ) :
    MomBd ν Y q (σ + c) := by
  have h1 : MomBd ν (fun ω => Y ω - ∫ ω', Y ω' ∂ν) q σ :=
    ⟨hY.sub aestronglyMeasurable_const, hσ⟩
  have h2 := MomBd.const (μ := ν) (∫ ω', Y ω' ∂ν) q (by linarith)
  have h3 := (h1.add hq h2 hσ0 (abs_nonneg _)).of_le
    (show σ + |∫ ω', Y ω' ∂ν| ≤ σ + c by linarith)
  refine ⟨hY, ?_⟩
  have : (fun ω => (Y ω - ∫ ω', Y ω' ∂ν) + ∫ ω', Y ω' ∂ν) = Y := by funext ω; ring
  rw [← this]; exact h3.2

/-- **The binomial moment step.** -/
theorem integral_pow_step {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y ν) {t c σ₂ σn : ℝ}
    (ht : 0 ≤ t) (hc0 : 0 ≤ c) (hσ₂ : 0 ≤ σ₂) (hσn : 0 ≤ σn) {n : ℕ} (hn : 2 ≤ n)
    (hpos : ∀ ω, 0 ≤ t + Y ω) (hmean : ∫ ω, Y ω ∂ν ≤ c * t)
    (h2 : MomBd ν Y 2 ((c + σ₂) * t)) (hnb : MomBd ν Y n ((c + σn) * t)) :
    Integrable (fun ω => (t + Y ω) ^ n) ν ∧
      ∫ ω, (t + Y ω) ^ n ∂ν ≤ t ^ n * (1 + n * c + 2 ^ n * ((c + σ₂) ^ 2 + (c + σn) ^ n)) := by
  have hA : 0 ≤ (c + σ₂) * t := by positivity
  have hB : 0 ≤ (c + σn) * t := by positivity
  obtain ⟨hi2, hb2⟩ := integral_abs_pow_le (n := 2) (by norm_num) hA (by exact_mod_cast h2)
  obtain ⟨hin, hbn⟩ := integral_abs_pow_le (by omega) hB hnb
  have hY1 : Integrable Y ν := by
    have hmem : MemLp Y (ENNReal.ofReal n) ν := lt_of_le_of_lt hnb.2 ENNReal.ofReal_lt_top
    exact hmem.integrable (q := ENNReal.ofReal n) (by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast (show 1 ≤ n by omega)))
  have hsq : (fun ω => |Y ω| ^ 2) = fun ω => Y ω ^ 2 := by funext ω; exact sq_abs _
  rw [hsq] at hi2 hb2
  set g : Ω → ℝ := fun ω =>
    t ^ n + n * t ^ (n - 1) * Y ω + 2 ^ n * (t ^ (n - 2) * Y ω ^ 2 + |Y ω| ^ n) with hg
  have hgi : Integrable g ν :=
    ((integrable_const _).add (hY1.const_mul _)).add
      (((hi2.const_mul _).add hin).const_mul _)
  have hle : ∀ ω, (t + Y ω) ^ n ≤ g ω := fun ω => pow_add_le ht (Y ω) hn
  have hmeas : AEStronglyMeasurable (fun ω => (t + Y ω) ^ n) ν :=
    (aestronglyMeasurable_const.add hY).pow n
  have hint : Integrable (fun ω => (t + Y ω) ^ n) ν :=
    hgi.mono' hmeas (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hpos ω) n)]; exact hle ω)
  refine ⟨hint, (integral_mono hint hgi hle).trans ?_⟩
  have hgint : ∫ ω, g ω ∂ν = t ^ n + n * t ^ (n - 1) * ∫ ω, Y ω ∂ν +
      2 ^ n * (t ^ (n - 2) * ∫ ω, Y ω ^ 2 ∂ν + ∫ ω, |Y ω| ^ n ∂ν) := by
    have i3 : Integrable (fun ω => (2 ^ n * t ^ (n - 2)) * Y ω ^ 2 + 2 ^ n * |Y ω| ^ n) ν :=
      (hi2.const_mul _).add (hin.const_mul _)
    have i2 : Integrable (fun ω => (n * t ^ (n - 1)) * Y ω +
        ((2 ^ n * t ^ (n - 2)) * Y ω ^ 2 + 2 ^ n * |Y ω| ^ n)) ν := (hY1.const_mul _).add i3
    have e : ∫ ω, g ω ∂ν = ∫ ω, t ^ n + ((n * t ^ (n - 1)) * Y ω +
        ((2 ^ n * t ^ (n - 2)) * Y ω ^ 2 + 2 ^ n * |Y ω| ^ n)) ∂ν := by
      congr 1; rw [hg]; funext ω; ring
    rw [e, integral_add (integrable_const _) i2, integral_add (hY1.const_mul _) i3,
      integral_add (hi2.const_mul _) (hin.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [hgint]
  have htn1 : 0 ≤ (n : ℝ) * t ^ (n - 1) := by positivity
  have h1 : (n : ℝ) * t ^ (n - 1) * ∫ ω, Y ω ∂ν ≤ (n : ℝ) * t ^ (n - 1) * (c * t) :=
    mul_le_mul_of_nonneg_left hmean htn1
  have h2' : t ^ (n - 2) * ∫ ω, Y ω ^ 2 ∂ν ≤ t ^ (n - 2) * ((c + σ₂) * t) ^ 2 :=
    mul_le_mul_of_nonneg_left hb2 (pow_nonneg ht _)
  have e1 : (n : ℝ) * t ^ (n - 1) * (c * t) = t ^ n * (n * c) := by
    have : t ^ (n - 1) * t = t ^ n := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [← this]; ring
  have e2 : t ^ (n - 2) * ((c + σ₂) * t) ^ 2 = t ^ n * (c + σ₂) ^ 2 := by
    have : t ^ (n - 2) * t ^ 2 = t ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
    rw [← this]; ring
  have e3 : ((c + σn) * t) ^ n = t ^ n * (c + σn) ^ n := by rw [mul_pow, mul_comm]
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h2' hbn) h2n]

section Trace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [IsProbabilityMeasure ν] [DecidableEq n] in
theorem integral_bilinear (U : Ω → Matrix n n ℂ) (hU : ∀ x y, Integrable (fun ω => U ω x y) ν)
    (u v : n → ℂ) : ∫ ω, bilinear u (U ω) v ∂ν = bilinear u (matrixExpect ν U) v := by
  simp only [bilinear, dotProduct, mulVec, Pi.star_apply, matrixExpect, Matrix.of_apply]
  rw [integral_finsetSum _ fun x _ => ?_]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun y _ => (hU x y).mul_const _]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_mul_const]
  · exact (integrable_finsetSum _ fun y _ => (hU x y).mul_const _).const_mul _

omit [IsProbabilityMeasure ν] [DecidableEq n] in
theorem measurable_bilinear_comp {U : Ω → Matrix n n ℂ} (hU : Measurable U) (u v : n → ℂ) :
    Measurable fun ω => bilinear u (U ω) v := by
  simp only [bilinear, dotProduct, mulVec]
  exact Finset.measurable_sum _ fun x _ => measurable_const.mul
    (Finset.measurable_sum _ fun y _ => (measurable_pi_apply y |>.comp
      (measurable_pi_apply x |>.comp hU)).mul measurable_const)

omit [IsProbabilityMeasure ν] in
/-- **The trace of the Ward noise against a factored source**: `y = Re Tr(S*S𝓔)` has mean
`Re Tr(S*S E𝓔)` (so `|Ey| ≤ c Re Tr(S*S)`) and centered `L^q` norm `≤ σ Re Tr(S*S)`. -/
theorem trace_noise (𝓔 : Ω → Matrix n n ℂ) (h𝓔 : Measurable 𝓔)
    (hint : ∀ a b, Integrable (fun ω => 𝓔 ω a b) ν) (S : Matrix m n ℂ) {c q σ : ℝ}
    (hc : ‖matrixExpect ν 𝓔‖ ≤ c) (hq : 1 ≤ q) (hσ : 0 ≤ σ)
    (hfl : ∀ u v : n → ℂ, eLpNorm (fun ω => bilinear u (𝓔 ω - matrixExpect ν 𝓔) v)
      (ENNReal.ofReal q) ν ≤ ENNReal.ofReal (σ * vecNorm u * vecNorm v)) :
    AEStronglyMeasurable (fun ω => (Sᴴ * S * 𝓔 ω).trace.re) ν ∧
      ∫ ω, (Sᴴ * S * 𝓔 ω).trace.re ∂ν = (Sᴴ * S * matrixExpect ν 𝓔).trace.re ∧
      |∫ ω, (Sᴴ * S * 𝓔 ω).trace.re ∂ν| ≤ c * (Sᴴ * S).trace.re ∧
      eLpNorm (fun ω => (Sᴴ * S * 𝓔 ω).trace.re - ∫ ω', (Sᴴ * S * 𝓔 ω').trace.re ∂ν)
        (ENNReal.ofReal q) ν ≤ ENNReal.ofReal (σ * (Sᴴ * S).trace.re) := by
  have hT := trace_factor_re_nonneg S
  have hmeas : ∀ x, Measurable fun ω => bilinear (rowv S x) (𝓔 ω) (rowv S x) :=
    fun x => measurable_bilinear_comp h𝓔 _ _
  have htr : ∀ ω, (Sᴴ * S * 𝓔 ω).trace = ∑ x, bilinear (rowv S x) (𝓔 ω) (rowv S x) :=
    fun ω => trace_factor_mul S _
  have hm : AEStronglyMeasurable (fun ω => (Sᴴ * S * 𝓔 ω).trace.re) ν := by
    simp_rw [htr]
    exact (Complex.measurable_re.comp (Finset.measurable_sum _ fun x _ => hmeas x)).aestronglyMeasurable
  have hbi : ∀ x, Integrable (fun ω => bilinear (rowv S x) (𝓔 ω) (rowv S x)) ν := by
    intro x
    simp only [bilinear, dotProduct, mulVec]
    exact integrable_finsetSum _ fun a _ => (integrable_finsetSum _ fun b _ =>
      (hint a b).mul_const _).const_mul _
  have hmean : ∫ ω, (Sᴴ * S * 𝓔 ω).trace.re ∂ν = (Sᴴ * S * matrixExpect ν 𝓔).trace.re := by
    simp_rw [htr, Complex.re_sum]
    rw [integral_finsetSum (s := Finset.univ)
      (f := fun x ω => (bilinear (rowv S x) (𝓔 ω) (rowv S x)).re) fun x _ => by
        exact (hbi x).re, trace_factor_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h := integral_re (hbi x)
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_bilinear 𝓔 hint]
  refine ⟨hm, hmean, ?_, ?_⟩
  · rw [hmean]
    exact (Complex.abs_re_le_norm _).trans ((norm_trace_factor_le S _).trans
      (mul_le_mul_of_nonneg_right hc hT))
  · rw [hmean]
    have hc' : ∀ ω, (Sᴴ * S * 𝓔 ω).trace.re - (Sᴴ * S * matrixExpect ν 𝓔).trace.re =
        (∑ x, bilinear (rowv S x) (𝓔 ω - matrixExpect ν 𝓔) (rowv S x)).re := by
      intro ω
      rw [← trace_factor_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    simp_rw [hc']
    have hle : eLpNorm (fun ω => (∑ x, bilinear (rowv S x) (𝓔 ω - matrixExpect ν 𝓔)
        (rowv S x)).re) (ENNReal.ofReal q) ν ≤
        eLpNorm (fun ω => ∑ x, bilinear (rowv S x) (𝓔 ω - matrixExpect ν 𝓔) (rowv S x))
          (ENNReal.ofReal q) ν :=
      eLpNorm_mono (Complex.measurable_re.comp (Finset.measurable_sum _ fun x _ =>
        measurable_bilinear_comp (h𝓔.sub measurable_const) _ _)).aestronglyMeasurable
        fun ω => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
    have hsum : (fun ω => ∑ x, bilinear (rowv S x) (𝓔 ω - matrixExpect ν 𝓔) (rowv S x)) =
        ∑ x, fun ω => bilinear (rowv S x) (𝓔 ω - matrixExpect ν 𝓔) (rowv S x) := by
      funext ω; simp [Finset.sum_apply]
    rw [hsum] at hle
    refine hle.trans ((eLpNorm_sum_le (by simpa using ENNReal.ofReal_le_ofReal hq)).trans ?_)
    rw [← sum_vecNorm_rowv, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun x _ => by
      have := vecNorm_nonneg (rowv S x); positivity]
    refine Finset.sum_le_sum fun x _ => (hfl _ _).trans (le_of_eq ?_)
    ring_nf

end Trace

end BlockBand.SourceProcess.FullSource
