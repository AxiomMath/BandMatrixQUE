module

public import BlockBand.SourceProcess.SourceProcessLaw.EarlyWeights
public import BlockBand.SourceProcess.FullSourceStops.WordValue
public import BlockBand.Transmission.Bridge.NullDet

/-!
# Measurability and tag means for the early sources

Measurability and integrability of the source transform integrand `srcIntegrand`, and the bound
`E Re Tr Y_{n;k} ≤ C W` from the first full tag clock moment (`tag_mean_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge

variable {W : ℕ}

theorem measurable_matrix_add' {α m n : Type*} [MeasurableSpace α] {f g : α → Matrix m n ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a + g a :=
  Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix.add hg.eval_matrix

theorem measurable_srcIntegrand (b E : ℝ) (n : ℕ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) : Measurable (srcIntegrand b E W n q a) := by
  unfold srcIntegrand
  refine Finset.measurable_prod _ fun j _ => Complex.measurable_re.comp (Measurable.inv ?_)
  refine measurable_det.comp (measurable_matrix_add' measurable_const ?_)
  refine measurable_matrix_sum _ fun i _ => measurable_matrix_smul _ ?_
  exact measurable_matrix_sum _ fun k _ => measurable_matrix_smul _ (measurable_tagResponse b E n k)

theorem integrable_srcIntegrand (b E : ℝ) (n : ℕ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) :
    Integrable (srcIntegrand b E W n q a) (growthPathLaw W b) := by
  have : IsProbabilityMeasure (growthPathLaw W b) := by
    unfold growthPathLaw; infer_instance
  refine Integrable.of_bound (measurable_srcIntegrand b E n q a).aestronglyMeasurable 1
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]; exact abs_srcIntegrand_le_one b E n hq ha ω

theorem measurable_trace_tag (b E : ℝ) (n k : ℕ) :
    Measurable fun ω : GrowthPath W => (tagResponse b E W n k ω).trace := by
  simp only [trace, diag]
  exact Finset.measurable_sum _ fun x _ => (measurable_tagResponse b E n k).eval_matrix

/-- From the `p = 1` tag moment: `Re Tr Y_{n;k}` is integrable with mean `≤ C W`. -/
theorem tag_mean_le {b E : ℝ} {n k : ℕ} (hW : 0 < W) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W n k ω).trace) (ENNReal.ofReal 1)
      (growthPathLaw W b) ≤ ENNReal.ofReal C) :
    Integrable (fun ω => (tagResponse b E W n k ω).trace.re) (growthPathLaw W b) ∧
      ∫ ω, (tagResponse b E W n k ω).trace.re ∂growthPathLaw W b ≤ C * W := by
  set f := fun ω => (W : ℂ)⁻¹ * (tagResponse b E W n k ω).trace
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  have hfm : AEStronglyMeasurable f (growthPathLaw W b) :=
    (measurable_const.mul (measurable_trace_tag b E n k)).aestronglyMeasurable
  rw [ENNReal.ofReal_one] at h
  have hlt : eLpNorm f 1 (growthPathLaw W b) < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hfi : Integrable f (growthPathLaw W b) := memLp_one_iff_integrable.1 hlt
  have he : (fun ω => (tagResponse b E W n k ω).trace.re) = fun ω => (W : ℝ) * (f ω).re := by
    funext ω
    have e : ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    simp only [f, e, Complex.re_ofReal_mul]
    have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
    field_simp
  have hint : Integrable (fun ω => (tagResponse b E W n k ω).trace.re) (growthPathLaw W b) := by
    rw [he]; exact hfi.re.const_mul _
  refine ⟨hint, ?_⟩
  have hnorm : ∫ ω, ‖f ω‖ ∂growthPathLaw W b ≤ C := by
    have h1 := ofReal_integral_norm_eq_lintegral_enorm hfi
    rw [eLpNorm_one_eq_lintegral_enorm hfm] at h
    rw [← h1] at h
    exact (ENNReal.ofReal_le_ofReal_iff hC).1 h
  calc ∫ ω, (tagResponse b E W n k ω).trace.re ∂growthPathLaw W b
      ≤ ∫ ω, (W : ℝ) * ‖f ω‖ ∂growthPathLaw W b := by
        refine integral_mono hint (hfi.norm.const_mul _) fun ω => ?_
        rw [show (tagResponse b E W n k ω).trace.re = (W : ℝ) * (f ω).re from congrFun he ω]
        exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (Nat.cast_nonneg _)
    _ = (W : ℝ) * ∫ ω, ‖f ω‖ ∂growthPathLaw W b := integral_const_mul _ _
    _ ≤ (W : ℝ) * C := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)
    _ = C * W := mul_comm _ _

end BlockBand.SourceProcess.SourceProcessLaw
