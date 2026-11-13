module

public import BlockBand.SourceProcess.Sampling.RankOneAlg
public import BlockBand.SourceProcess.Sampling.Mix
public import BlockBand.SourceProcess.ComplexSourceLaw.GaussianForms
public import BlockBand.SourceProcess.RawTag.KhintchineVec

/-!
# Moments of one sampled injection at a fixed tag location

* `lin_section`: `E Re Tr(K ξ) = κ Re Tr(K U*P_kU)` (via SP's `integral_quad`, `E ḡ_a g_b = δ_ab`);
* `sq_section`: **the circular fourth moment**
  `E (Re Tr ξ)² = κ² E|S g|⁴ ≤ κ² · 2M₄ · (Re Tr U*P_kU)²` (RawTag's Khintchine bound
  `lintegral_normSq_rpow_le` at `r = 2`, `M₄ = gaussMoment 4`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.RawTag
open scoped ComplexConjugate ComplexOrder ENNReal

variable {W n : ℕ}

theorem measurable_trace_re_mul {β m : Type*} [Fintype m] [MeasurableSpace β]
    (K : Matrix m m ℂ) {f : β → Matrix m m ℂ} (hf : Measurable f) :
    Measurable fun z => (K * f z).trace.re := by
  refine Complex.measurable_re.comp ?_
  simp only [trace, diag, mul_apply]
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
    measurable_const.mul hf.eval_matrix

theorem measurable_trace_re {β m : Type*} [Fintype m] [MeasurableSpace β]
    {f : β → Matrix m m ℂ} (hf : Measurable f) : Measurable fun z => (f z).trace.re := by
  refine Complex.measurable_re.comp ?_
  simp only [trace, diag]
  exact Finset.measurable_sum _ fun a _ => hf.eval_matrix

theorem measurable_rankOne_section (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ)
    (k : ℕ) : Measurable fun g : Fin W → ℂ => rankOne U κ (k, g) := by
  simp_rw [rankOne_eq]
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, mulVec, dotProduct, smul_eq_mul,
    Complex.star_def]
  have h1 : Measurable fun g : Fin W → ℂ => ∑ y, tagS U k a y * g y := by fun_prop
  have h2 : Measurable fun g : Fin W → ℂ => ∑ y, tagS U k b y * g y := by fun_prop
  exact measurable_const.mul (h1.mul (Complex.continuous_conj.measurable.comp h2))

theorem measurable_rankOne (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ) :
    Measurable (rankOne U κ) :=
  measurable_from_prod_countable_right fun k => measurable_rankOne_section U κ k

/-- **Mean at a fixed tag location.** -/
theorem lin_section (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ)
    (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : ℕ) :
    Integrable (fun g => (K * rankOne U κ (k, g)).trace.re) (circularVectorLaw (Fin W)) ∧
      ∫ g, (K * rankOne U κ (k, g)).trace.re ∂circularVectorLaw (Fin W) =
        κ * (K * (Uᴴ * tagProjection W n k * U)).trace.re := by
  set B := (tagS U k)ᴴ * K * tagS U k
  have hq := integrable_quad (ι := Fin W) (fun a b => B a b)
  simp_rw [trace_mul_rankOne]
  refine ⟨hq.re.const_mul κ, ?_⟩
  rw [integral_const_mul]
  have := integral_re hq
  simp only [RCLike.re_to_complex] at this
  have hQ : ∫ g, ∑ a, ∑ b, conj (g a) * B a b * g b ∂circularVectorLaw (Fin W) = ∑ a, B a a :=
    integral_quad (fun a b => B a b)
  rw [this, hQ, ← trace_tagS]
  rfl

/-- **The circular fourth moment at a fixed tag location.** -/
theorem sq_section (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (κ : ℝ) (k : ℕ) :
    Integrable (fun g => (rankOne U κ (k, g)).trace.re ^ 2) (circularVectorLaw (Fin W)) ∧
      ∫ g, (rankOne U κ (k, g)).trace.re ^ 2 ∂circularVectorLaw (Fin W) ≤
        κ ^ 2 * (2 * gaussMoment 4) * (Uᴴ * tagProjection W n k * U).trace.re ^ 2 := by
  set Y := Uᴴ * tagProjection W n k * U
  have e : ∀ g, ENNReal.ofReal ((rankOne U κ (k, g)).trace.re ^ 2) =
      ENNReal.ofReal (κ ^ 2) *
        ENNReal.ofReal ((∑ a, ‖(tagS U k *ᵥ g) a‖ ^ 2) ^ (2 : ℝ)) := by
    intro g
    rw [trace_rankOne, Real.rpow_two, mul_pow, ENNReal.ofReal_mul (sq_nonneg κ)]
  have hK := lintegral_normSq_rpow_le (tagS U k) (r := 2) one_le_two
  rw [show (2 : ℝ) * 2 = 4 by norm_num, sum_normSq_tagS, Real.rpow_two] at hK
  have hm : Measurable fun g => (rankOne U κ (k, g)).trace.re ^ 2 :=
    (measurable_trace_re (measurable_rankOne_section U κ k)).pow_const 2
  have hM : 0 ≤ 2 * gaussMoment 4 := mul_nonneg zero_le_two (gaussMoment_nonneg _)
  have hlint : ∫⁻ g, ENNReal.ofReal ((rankOne U κ (k, g)).trace.re ^ 2)
      ∂circularVectorLaw (Fin W) ≤ ENNReal.ofReal (κ ^ 2 * (2 * gaussMoment 4) * Y.trace.re ^ 2) := by
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc,
      ENNReal.ofReal_mul (sq_nonneg κ)]
    gcongr
  have hi : Integrable (fun g => (rankOne U κ (k, g)).trace.re ^ 2) (circularVectorLaw (Fin W)) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun g => sq_nonneg _)).2 (hlint.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => sq_nonneg _) hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (sq_nonneg _) hM) (sq_nonneg _)) hlint

end BlockBand.SourceProcess.Sampling
