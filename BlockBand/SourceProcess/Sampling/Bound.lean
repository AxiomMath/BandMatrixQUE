module

public import BlockBand.SourceProcess.Sampling.Fubini

/-!
# The sampling error at fixed width

* `abs_sub_le_integral_condErr`: Fubini over the path and `cond_lindeberg` give
  `|sourceTransform - sampledPhysTransform| ≤ E condErr` (`n = ⌊WT⌋`).
* `tag_sq_le`: `‖W⁻¹ Tr Y_{n;k}‖_2 ≤ C` gives `E(W⁻¹ Re Tr Y_{n;k})² ≤ C²`.
* `integral_condErr_le`: then `E condErr ≤ Σ_i 4M₄ (Σ_j a_{ji})² m_i² C² / M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.RawTag

variable {W : ℕ}

/-- **Fubini over the path.** -/
theorem abs_sub_le_integral_condErr (b E T : ℝ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) {M : ℕ}
    (hW : 0 < W) (hM : 0 < M)
    (hY : ∀ k ∈ Finset.range ⌊(W : ℝ) * T⌋₊, Integrable (fun ω =>
      ((tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω).trace.re / W) ^ 2) (growthPathLaw W b)) :
    |sourceTransform b E T q a W - sampledPhysTransform b E T q a M W| ≤
      ∫ ω, condErr W ⌊(W : ℝ) * T⌋₊ q a M (fun k => tagResponse b E W ⌊(W : ℝ) * T⌋₊ k ω)
        ∂growthPathLaw W b := by
  set n := ⌊(W : ℝ) * T⌋₊
  have : IsProbabilityMeasure (growthPathLaw W b) := by unfold growthPathLaw; infer_instance
  have hP : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W n (q x.1)) :=
    fun x => isProbabilityMeasure_tagSampleLaw W n (hq x.1)
  set inner := (Measure.pi fun i : Fin p × Fin M => tagSampleLaw W n (q i.1)).prod
    (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))
  have hΦ := integrable_sampledIntegrand b E W n hq ha M ((growthPathLaw W b).prod inner)
  have e1 : sampledPhysTransform b E T q a M W = ∫ ω, ∫ y, ∏ j,
      (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + ∑ i, (a j i : ℂ) •
        sampledSource b E W n (q i) M (fun l => y.1 (i, l)) (fun l => y.2 (i, l)) ω).det⁻¹).re
        ∂inner ∂growthPathLaw W b :=
    integral_prod _ hΦ
  have hin : Integrable (fun ω => ∫ y, ∏ j,
      (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + ∑ i, (a j i : ℂ) •
        sampledSource b E W n (q i) M (fun l => y.1 (i, l)) (fun l => y.2 (i, l)) ω).det⁻¹).re
        ∂inner) (growthPathLaw W b) :=
    hΦ.integral_prod_left
  have hsrc := integrable_srcIntegrand (W := W) b E n (fun i => hq i) ha
  have hcond : Integrable (fun ω => condErr W n q a M (fun k => tagResponse b E W n k ω))
      (growthPathLaw W b) :=
    integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun k hk =>
      (hY k hk).const_mul _).const_mul _
  change |∫ ω, srcIntegrand b E W n q a ω ∂growthPathLaw W b - _| ≤ _
  rw [e1, ← integral_sub hsrc hin]
  refine (abs_integral_le_integral_abs).trans (integral_mono (hsrc.sub hin).abs hcond fun ω => ?_)
  have h1 := cond_eq b E W n hq a M ω
  have h2 := srcIntegrand_eq_hyb b E hM q a ω (n := n)
  have h3 := cond_lindeberg (boundaryToInterior b E W n ω) hq ha hW hM
  simp only
  rw [abs_sub_comm, h1, h2]
  exact h3

/-- `‖W⁻¹ Tr Y‖_2 ≤ C` gives `E(W⁻¹ Re Tr Y)² ≤ C²`. -/
theorem tag_sq_le {b E : ℝ} {n k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W n k ω).trace) (ENNReal.ofReal 2)
      (growthPathLaw W b) ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ((tagResponse b E W n k ω).trace.re / W) ^ 2) (growthPathLaw W b) ∧
      ∫ ω, ((tagResponse b E W n k ω).trace.re / W) ^ 2 ∂growthPathLaw W b ≤ C ^ 2 := by
  set f := fun ω => (W : ℂ)⁻¹ * (tagResponse b E W n k ω).trace
  have hfm : Measurable f := measurable_const.mul (measurable_trace_tag b E n k)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top
    hfm.aestronglyMeasurable, ENNReal.toReal_ofReal zero_le_two] at h
  have h' := ENNReal.rpow_le_rpow h (zero_le_two : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, one_div_mul_cancel two_ne_zero, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC zero_le_two, Real.rpow_two] at h'
  have hpt : ∀ ω, ((tagResponse b E W n k ω).trace.re / W) ^ 2 ≤ ‖f ω‖ ^ 2 := by
    intro ω
    have e : (f ω).re = (tagResponse b E W n k ω).trace.re / W := by
      simp only [f]
      rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
        div_eq_inv_mul]
    rw [← e]
    have := abs_le.1 (Complex.abs_re_le_norm (f ω))
    exact sq_le_sq' this.1 this.2
  have hm : Measurable fun ω => ((tagResponse b E W n k ω).trace.re / W) ^ 2 :=
    ((Complex.measurable_re.comp (measurable_trace_tag b E n k)).div_const _).pow_const 2
  have hlint : ∫⁻ ω, ENNReal.ofReal (((tagResponse b E W n k ω).trace.re / W) ^ 2)
      ∂growthPathLaw W b ≤ ENNReal.ofReal (C ^ 2) := by
    refine (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)).trans ?_
    refine le_of_eq_of_le (lintegral_congr fun ω => ?_) h'
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
      Real.rpow_two]
  have hi : Integrable (fun ω => ((tagResponse b E W n k ω).trace.re / W) ^ 2)
      (growthPathLaw W b) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun g => sq_nonneg _)).2 (hlint.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => sq_nonneg _) hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hlint

/-- **The integrated conditional error.** -/
theorem integral_condErr_le {b E : ℝ} {n p J M : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    (a : Fin J → Fin p → ℝ) (hM : 0 < M) {C : ℝ}
    (htag : ∀ k ∈ Finset.range n, Integrable (fun ω =>
      ((tagResponse b E W n k ω).trace.re / W) ^ 2) (growthPathLaw W b) ∧
      ∫ ω, ((tagResponse b E W n k ω).trace.re / W) ^ 2 ∂growthPathLaw W b ≤ C ^ 2) :
    ∫ ω, condErr W n q a M (fun k => tagResponse b E W n k ω) ∂growthPathLaw W b ≤
      ∑ i, 4 * gaussMoment 4 * (∑ j, a j i) ^ 2 * gridMass W n (q i) ^ 2 * C ^ 2 / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM4 : 0 ≤ 4 * gaussMoment 4 := mul_nonneg (by norm_num) (gaussMoment_nonneg _)
  unfold condErr
  rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun k hk =>
    (htag k hk).1.const_mul _).const_mul _]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun k hk => (htag k hk).1.const_mul _]
  have hm := gridMass_nonneg W n (hq i)
  have hc : 0 ≤ 4 * gaussMoment 4 * (∑ j, a j i) ^ 2 * (gridMass W n (q i) / M) :=
    mul_nonneg (mul_nonneg hM4 (sq_nonneg _)) (div_nonneg hm hMr.le)
  have hs : ∑ k ∈ Finset.range n, ∫ ω, q i (((k + 1 : ℕ) : ℝ) / W) / W *
      ((tagResponse b E W n k ω).trace.re / W) ^ 2 ∂growthPathLaw W b ≤
      gridMass W n (q i) * C ^ 2 := by
    rw [gridMass, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (htag k hk).2 (div_nonneg (hq i _) (Nat.cast_nonneg _))
  refine (mul_le_mul_of_nonneg_left hs hc).trans (le_of_eq ?_)
  field_simp

end BlockBand.SourceProcess.Sampling
