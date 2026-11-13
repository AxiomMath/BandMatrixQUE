module

public import BlockBand.SourceProcess.ClosedSummedProof.FramePast

/-!
# Integrability on the closed path from fresh-layer moments

* `norm_gramEntry_layerGram_le`: `|G_e(NᴴV)| ≤ ‖N‖² Re Tr VᴴV`;
* `integrable_closed_of_fresh` (Tonelli): if `∫⁻_f ‖Φ(x,f)‖ dfresh ≤ B` for every closed past `x`,
  then `Φ(cpast j, fresh j)` is `lawW`-integrable;
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ENNReal

variable {W p M : ℕ}

theorem re_trace_conj_le {ι c : Type} [Fintype ι] [DecidableEq ι] [Fintype c]
    (V : Matrix ι c ℂ) (X : Matrix ι ι ℂ) : (Vᴴ * X * V).trace.re ≤ ‖X‖ * (Vᴴ * V).trace.re := by
  have e1 : ∀ Y : Matrix ι ι ℂ, (Vᴴ * Y * V).trace = ∑ a, bilinear (colOf V a) Y (colOf V a) :=
    fun Y => by
      simp only [Matrix.trace, diag_apply]
      exact Finset.sum_congr rfl fun a _ => (bilinear_col V Y a a).symm
  have e2 : (Vᴴ * V).trace.re = ∑ a, vecNorm (colOf V a) ^ 2 := by
    rw [← Matrix.mul_one Vᴴ, e1, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [vecNorm, Real.sq_sqrt (by positivity)]
    simp only [bilinear, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum, colOf]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast rfl
  rw [e1, e2, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (Complex.re_le_norm _).trans ((norm_bilinear_le _ _ _).trans (le_of_eq ?_))
  ring

/-- `|G_e(NᴴV)| ≤ ‖N‖² Re Tr VᴴV`. -/
theorem norm_gramEntry_layerGram_le {c : Type} [Fintype c] [DecidableEq c] (b E : ℝ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (V : Matrix (Fin 2 × Fin W) c ℂ)
    (f : LayerSample W .oneBlockOnePort) (e : Fin 2 × c × c) :
    ‖gramEntry e (layerGram b E XX V f)‖ ≤ ‖freshTransport b E XX f‖ ^ 2 * (Vᴴ * V).trace.re := by
  set N := freshTransport b E XX f
  have h1 := norm_gramEntry_le (Nᴴ * V) (fun x : Fin 2 × Fin W => if x.1 = 0 then 1 else 0)
    (fun x => by split_ifs <;> simp) e
  refine h1.trans ?_
  have e1 : (gramPair (diagonal fun x : Fin 2 × Fin W => if x.1 = 0 then (1 : ℂ) else 0)
      (Nᴴ * V)).1 = Vᴴ * (N * Nᴴ) * V := by
    simp only [gramPair, sourceGram, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [e1]
  have h2 := re_trace_conj_le V (N * Nᴴ)
  have h3 := FullSource.norm_mul_conjTranspose_le N
  have h4 : 0 ≤ (Vᴴ * V).trace.re := by
    have := re_trace_conj_le V (0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    simp only [Matrix.mul_zero, Matrix.zero_mul, trace_zero, Complex.zero_re, norm_zero,
      zero_mul] at this
    rw [show (Vᴴ * V).trace.re = ∑ a, ∑ x, ‖V x a‖ ^ 2 by
      simp only [Matrix.trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast rfl]
    positivity
  exact h2.trans (mul_le_mul_of_nonneg_right h3 h4)

/-- **Tonelli on the closed past × fresh layer.** -/
theorem integrable_closed_of_fresh (b T : ℝ) {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (j : ℕ)
    {Φ : ClosedPast W j p M × LayerSample W .oneBlockOnePort → ℂ} (hΦ : Measurable Φ) (B : ℝ)
    (hB : ∀ x, ∫⁻ f, ‖Φ (x, f)‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal B) :
    Integrable (fun y => Φ (cpast j y, freshSample W j y.1.1)) (lawW b T q M W) := by
  have := isProbabilityMeasure_sampLaw (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  have : IsProbabilityMeasure (cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M) := by unfold cpLaw; infer_instance
  have hT : Measurable fun y : SampledPath W p M × ℝ => (cpast j y, freshSample W j y.1.1) :=
    (measurable_cpast j).prodMk ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  refine ⟨(hΦ.comp hT).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e : ∫⁻ y, ‖Φ (cpast j y, freshSample W j y.1.1)‖ₑ ∂lawW b T q M W =
      ∫⁻ z, ‖Φ z‖ₑ ∂((cpLaw b W j ⌊(W : ℝ) * T⌋₊ q M).prod (freshLaw W b)) := by
    rw [← lawW_map_closed_fresh b T hq j, lintegral_map hΦ.enorm hT]
  rw [e, lintegral_prod _ hΦ.enorm.aemeasurable]
  refine lt_of_le_of_lt ((lintegral_mono fun x => hB x).trans (le_of_eq (b := ENNReal.ofReal B)
    (by simp))) ENNReal.ofReal_lt_top

/-- **Bulk-uniform second and fourth moments of the fresh transport.** -/
theorem fresh_pow_bound (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) : ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ∫ y, ‖freshTransport b E XX y‖ ^ 4 ∂freshLaw W b ≤ C ∧
        Integrable (fun y => ‖freshTransport b E XX y‖ ^ 4) (freshLaw W b) := by
  obtain ⟨C, W₀, hC⟩ := FullSource.fullSourceMoments_field_holds hGA b hb0 hb κ hκ 4 (by norm_num)
  refine ⟨max C 0 ^ 4, W₀, by positivity, fun W hW E hE XX hXX => ?_⟩
  have hm : Measurable fun y => freshTransport b E XX y :=
    FullSource.measurable_freshTransport_comp b E measurable_const measurable_id
  have hmb : BlockBand.Transmission.PassiveLayer.MomBd (freshLaw W b)
      (fun y => ‖freshTransport b E XX y‖) ((4 : ℕ) : ℝ) (max C 0) :=
    ⟨hm.norm.aestronglyMeasurable, by
      simpa using (hC W hW E hE XX hXX).1.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))⟩
  have h := FullSource.integral_abs_pow_le (ν := freshLaw W b) (n := 4) (by norm_num)
    (le_max_right C 0) hmb
  simp only [abs_norm] at h
  exact ⟨h.2, h.1⟩

end BlockBand.SourceProcess.ClosedSummedProof
