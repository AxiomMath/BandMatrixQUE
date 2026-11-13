module

public import BlockBand.SourceProcess.ClosedSummedProof.LayerAux

/-!
# Integrability of the one-layer word values

With `‖N‖ ∈ L⁴(fresh)` (from
`GaussianAbsorptionContract`, via `FullSource.fullSourceMoments_field_holds`), the new values
`Tr(NᴴLNT)` (`‖T‖ ≤ 1`) are integrable, and so are products of two centered ones, so the
integrals below are not Mathlib's junk `0` and are linear.

* `norm_trace_conj_le`: `‖Tr(NᴴLNT)‖ ≤ (Σ|L_{ij}|)‖N‖²` for `‖T‖ ≤ 1`;
* `integrable_trace_conj`, `integrable_trace_conj_mul`;
* `fresh_moments`: bulk-uniform `L²`/`L⁴` integrability of `‖N‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Σ_{ij} ‖L_{ij}‖`. -/
def entrySum (L : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖L i j‖

omit [DecidableEq ι] in
theorem entrySum_nonneg (L : Matrix ι ι ℂ) : 0 ≤ entrySum L := by unfold entrySum; positivity

theorem norm_trace_conj_le (N L T : Matrix ι ι ℂ) (hT : ‖T‖ ≤ 1) :
    ‖(Nᴴ * L * N * T).trace‖ ≤ entrySum L * ‖N‖ ^ 2 := by
  rw [trace_conj_cycle]
  refine (norm_trace_mul_le L _).trans (mul_le_mul_of_nonneg_left ?_ (entrySum_nonneg L))
  calc ‖N * T * Nᴴ‖ ≤ ‖N * T‖ * ‖Nᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖N‖ * ‖T‖) * ‖N‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ ‖N‖ ^ 2 := by nlinarith [norm_nonneg N, norm_nonneg T]

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [DecidableEq ι] in
theorem measurable_trace_conj {N : Ω → Matrix ι ι ℂ} (hN : Measurable N) (L T : Matrix ι ι ℂ) :
    Measurable fun y => ((N y)ᴴ * L * N y * T).trace := by
  have hc : Continuous fun M : Matrix ι ι ℂ => (Mᴴ * L * M * T).trace :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const |>.matrix_mul continuous_id
      |>.matrix_mul continuous_const).matrix_trace
  exact hc.measurable.comp hN

omit [IsFiniteMeasure μ] in
theorem integrable_trace_conj {N : Ω → Matrix ι ι ℂ} (hN : Measurable N)
    (h2 : Integrable (fun y => ‖N y‖ ^ 2) μ) (L T : Matrix ι ι ℂ) (hT : ‖T‖ ≤ 1) :
    Integrable (fun y => ((N y)ᴴ * L * N y * T).trace) μ :=
  (h2.const_mul (entrySum L)).mono' (measurable_trace_conj hN L T).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_trace_conj_le _ _ _ hT)

theorem integrable_trace_conj_mul {N : Ω → Matrix ι ι ℂ} (hN : Measurable N)
    (h2 : Integrable (fun y => ‖N y‖ ^ 2) μ) (h4 : Integrable (fun y => ‖N y‖ ^ 4) μ)
    (L L' T T' : Matrix ι ι ℂ) (hT : ‖T‖ ≤ 1) (hT' : ‖T'‖ ≤ 1) (a a' : ℂ) :
    Integrable (fun y => (((N y)ᴴ * L * N y * T).trace - a) *
      (((N y)ᴴ * L' * N y * T').trace - a')) μ := by
  set S := entrySum L
  set S' := entrySum L'
  have hS := entrySum_nonneg L
  have hS' := entrySum_nonneg L'
  have hdom : Integrable (fun y => S * S' * ‖N y‖ ^ 4 + (S * ‖a'‖ + S' * ‖a‖) * ‖N y‖ ^ 2 +
      ‖a‖ * ‖a'‖) μ :=
    ((h4.const_mul _).add (h2.const_mul _)).add (integrable_const _)
  refine hdom.mono' (((measurable_trace_conj hN L T).sub measurable_const).mul
    ((measurable_trace_conj hN L' T').sub measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have b1 := norm_trace_conj_le (N y) L T hT
  have b2 := norm_trace_conj_le (N y) L' T' hT'
  have c1 := norm_sub_le ((N y)ᴴ * L * N y * T).trace a
  have c2 := norm_sub_le ((N y)ᴴ * L' * N y * T').trace a'
  rw [norm_mul]
  have n2 : 0 ≤ ‖N y‖ ^ 2 := by positivity
  calc ‖((N y)ᴴ * L * N y * T).trace - a‖ * ‖((N y)ᴴ * L' * N y * T').trace - a'‖
      ≤ (S * ‖N y‖ ^ 2 + ‖a‖) * (S' * ‖N y‖ ^ 2 + ‖a'‖) :=
        mul_le_mul (c1.trans (by linarith)) (c2.trans (by linarith)) (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

end Generic

/-- **Bulk-uniform `L²`/`L⁴` integrability of the fresh transport** (from `GaussianAbsorptionContract`). -/
theorem fresh_moments (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) : ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        Integrable (fun y => ‖freshTransport b E XX y‖ ^ 2) (freshLaw W b) ∧
        Integrable (fun y => ‖freshTransport b E XX y‖ ^ 4) (freshLaw W b) := by
  obtain ⟨C, W₀, hC⟩ := FullSource.fullSourceMoments_field_holds hGA b hb0 hb κ hκ 4 (by norm_num)
  refine ⟨W₀, fun W hW E hE XX hXX => ?_⟩
  have hm : Measurable fun y => freshTransport b E XX y :=
    FullSource.measurable_freshTransport_comp b E measurable_const measurable_id
  have hmb : BlockBand.Transmission.PassiveLayer.MomBd (freshLaw W b)
      (fun y => ‖freshTransport b E XX y‖) ((4 : ℕ) : ℝ) (max C 0) :=
    ⟨hm.norm.aestronglyMeasurable, by
      simpa using (hC W hW E hE XX hXX).1.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))⟩
  have h4 := (FullSource.integral_abs_pow_le (ν := freshLaw W b) (n := 4) (by norm_num)
    (le_max_right C 0) hmb).1
  simp only [abs_norm] at h4
  refine ⟨?_, h4⟩
  refine ((h4.add (integrable_const 1))).mono' (hm.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have h0 := norm_nonneg (freshTransport b E XX y)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖freshTransport b E XX y‖ ^ 2 - 1)]

end BlockBand.SourceProcess.ClosedSummedProof
