module

public import BlockBand.SourceProcess.Sampling.RankOneMoments
public import BlockBand.SourceProcess.Sampling.Lindeberg
public import BlockBand.SourceProcess.SourceProcessLaw.EarlyAlg

/-!
# One sampled injection is a Lindeberg sample with mean `Q(q)/M`

The tag location `k` has law `q_k/(Wm)` (`tagSampleLaw`), `g ~ CN(0, I_W)`, and the injection is
`κ v v*`, `κ = m/(MW)`, `v = U* ι_k g`. Given the path (`U`):

* `isMatSample_rankOne`: it is an `IsMatSample` with mean
  `sampleMean U q M = M⁻¹ Σ_k (q_k/W²) U*P_kU` (`= M⁻¹ Q(q)` at `U = 𝒰_n`, so `E Q̂_M = Q(q)`);
* `integral_sq_rankOne_le`: `E(Re Tr ξ)² ≤ 2M₄ (m/M²) Σ_k (q_k/W)(W⁻¹ Re Tr U*P_kU)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.RawTag
open scoped ComplexOrder

variable {W n : ℕ}

/-- `M⁻¹ Σ_k (q_k/W²) U*P_kU`. -/
def sampleMean (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) (q : ℝ → ℝ) (M : ℕ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (((M : ℝ)⁻¹ : ℝ) : ℂ) • ∑ k ∈ Finset.range n,
    ((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) • (Uᴴ * tagProjection W n k * U)

theorem sampleMean_psd (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) (M : ℕ) : (sampleMean U q M).PosSemidef := by
  refine PosSemidef.smul (posSemidef_sum _ fun k _ => PosSemidef.smul
    ((tagProjection_posSemidef n k).conjTranspose_mul_mul_same U) ?_) ?_
  · exact Complex.zero_le_real.2 (div_nonneg (hq _) (sq_nonneg _))
  · exact Complex.zero_le_real.2 (inv_nonneg.2 (Nat.cast_nonneg M))

theorem isMatSample_zero {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    IsMatSample μ (fun _ => (0 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) 0 where
  psd _ := PosSemidef.zero
  meas := measurable_const
  lin_int _ := by simp
  lin_eq _ := by simp
  mean_psd := PosSemidef.zero
  sq_int := by simp

theorem coeff_zero_of_mass {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (hm : ¬ 0 < gridMass W n q) :
    ∀ k ∈ Finset.range n, q (((k + 1 : ℕ) : ℝ) / W) / W = 0 := by
  have h0 : gridMass W n q = 0 := le_antisymm (not_lt.1 hm) (gridMass_nonneg W n hq)
  exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => div_nonneg (hq _) (Nat.cast_nonneg _)).1 h0

theorem rankOne_zero (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) :
    rankOne U 0 = fun _ => 0 := by
  funext y; simp [rankOne]

/-- **One sampled injection is a Lindeberg sample with mean `M⁻¹ Q(q)`.** -/
theorem isMatSample_rankOne (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) (hW : 0 < W) {M : ℕ} (hM : 0 < M) :
    IsMatSample ((tagSampleLaw W n q).prod (circularVectorLaw (Fin W)))
      (rankOne U (gridMass W n q / (M * W))) (sampleMean U q M) := by
  have : IsProbabilityMeasure (tagSampleLaw W n q) := isProbabilityMeasure_tagSampleLaw W n hq
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  by_cases hm : 0 < gridMass W n q
  · set κ := gridMass W n q / (M * W)
    have hκ : 0 ≤ κ := div_nonneg hm.le (by positivity)
    have hw : ∀ k : ℕ, 0 ≤ q (((k + 1 : ℕ) : ℝ) / W) / (W * gridMass W n q) :=
      fun k => div_nonneg (hq _) (by positivity)
    rw [tagSampleLaw_eq hm]
    have hlin := fun K => mix_prod (μ := circularVectorLaw (Fin W)) (Finset.range n) hw
      (measurable_trace_re_mul K (measurable_rankOne U κ)) fun k => (lin_section U κ K k).1
    refine ⟨fun y => rankOne_psd U hκ y, measurable_rankOne U κ, fun K => (hlin K).1,
      fun K => ?_, sampleMean_psd U hq M, ?_⟩
    · rw [(hlin K).2]
      simp only [fun k => (lin_section U κ K k).2, sampleMean, Matrix.mul_smul,
        trace_smul, trace_sum, smul_eq_mul, Complex.re_ofReal_mul, Complex.re_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [κ]
      field_simp
    · exact (mix_prod (Finset.range n) hw
        ((measurable_trace_re (measurable_rankOne U κ)).pow_const 2)
        fun k => (sq_section U κ k).1).1
  · have hc := coeff_zero_of_mass hq hm
    have h0 : gridMass W n q = 0 := le_antisymm (not_lt.1 hm) (gridMass_nonneg W n hq)
    have hS : sampleMean U q M = 0 := by
      simp only [sampleMean]
      rw [Finset.sum_eq_zero fun k hk => by
        rw [sq, ← div_div, hc k hk, zero_div, Complex.ofReal_zero, zero_smul], smul_zero]
    rw [h0, zero_div, rankOne_zero, hS]
    exact isMatSample_zero _

/-- **Second moment of the trace of one sampled injection.** -/
theorem integral_sq_rankOne_le (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) (hW : 0 < W) {M : ℕ} (hM : 0 < M) :
    ∫ y, (rankOne U (gridMass W n q / (M * W)) y).trace.re ^ 2
        ∂(tagSampleLaw W n q).prod (circularVectorLaw (Fin W)) ≤
      2 * gaussMoment 4 * (gridMass W n q / (M : ℝ) ^ 2) *
        ∑ k ∈ Finset.range n, q (((k + 1 : ℕ) : ℝ) / W) / W *
          ((Uᴴ * tagProjection W n k * U).trace.re / W) ^ 2 := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM4 : 0 ≤ 2 * gaussMoment 4 := mul_nonneg zero_le_two (gaussMoment_nonneg _)
  by_cases hm : 0 < gridMass W n q
  · set κ := gridMass W n q / (M * W)
    have hw : ∀ k : ℕ, 0 ≤ q (((k + 1 : ℕ) : ℝ) / W) / (W * gridMass W n q) :=
      fun k => div_nonneg (hq _) (by positivity)
    rw [tagSampleLaw_eq hm, (mix_prod (Finset.range n) hw
      ((measurable_trace_re (measurable_rankOne U κ)).pow_const 2)
      fun k => (sq_section U κ k).1).2, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    refine (mul_le_mul_of_nonneg_left (sq_section U κ k).2 (hw k)).trans (le_of_eq ?_)
    simp only [κ]
    field_simp
  · have h0 : gridMass W n q = 0 := le_antisymm (not_lt.1 hm) (gridMass_nonneg W n hq)
    rw [h0, zero_div, rankOne_zero]
    simp

end BlockBand.SourceProcess.Sampling
