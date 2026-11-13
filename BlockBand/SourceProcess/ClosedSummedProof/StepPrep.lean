module

public import BlockBand.SourceProcess.ClosedSummedProof.ChainPin

/-!
# Step preparation: measurability and fresh-layer bounds of the Gram increments

* `measurable_gramEntry_gramPair`, `measurable_layerGramEntry`;
* `incr x f = G_e(N(X x, f)ᴴ V(x)) - G_e(V(x))`: the one-layer increment as a function of the
  closed past `x` and the fresh layer `f`;
* `lintegral_incr_le`, `lintegral_incr_mul_le`: for `Re Tr VᴴV ≤ R'`,
  `E_f|incr| ≤ R'(C₄ + 2)` and `E_f|incr_e incr_e'| ≤ 2R'²(C₄ + 1)` (`C₄` bounds `E‖N‖⁴`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Stochastic BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosedSumProof
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ} {c : Type} [Fintype c] [DecidableEq c]

omit [Fintype c] [DecidableEq c] in
theorem measurable_gramEntry_gramPair {α : Type*} [MeasurableSpace α]
    {V : α → Matrix (Fin 2 × Fin W) c ℂ} (hV : Measurable V) (e : Fin 2 × c × c) :
    Measurable fun a => gramEntry e (gramPair (nearProjection W) (V a)) := by
  unfold gramEntry gramPair sourceGram nearGram
  split_ifs
  · exact (measurable_matrix_mul' (measurable_matrix_conjTranspose' hV) hV).eval_matrix
  · exact (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hV)
      measurable_const) hV).eval_matrix

omit [Fintype c] [DecidableEq c] in
theorem measurable_layerGramEntry (b E : ℝ) {α : Type*} [MeasurableSpace α]
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : Measurable XX)
    {V : α → Matrix (Fin 2 × Fin W) c ℂ} (hV : Measurable V)
    {f : α → LayerSample W .oneBlockOnePort} (hf : Measurable f) (e : Fin 2 × c × c) :
    Measurable fun a => gramEntry e (layerGram b E (XX a) (V a) (f a)) :=
  measurable_gramEntry_gramPair (measurable_matrix_mul' (measurable_matrix_conjTranspose'
    (FullSource.measurable_freshTransport_comp b E hXX hf)) hV) e

/-- The one-layer increment of a Gram coordinate. -/
def incr (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (V : Matrix (Fin 2 × Fin W) c ℂ)
    (e : Fin 2 × c × c) (f : LayerSample W .oneBlockOnePort) : ℂ :=
  gramEntry e (layerGram b E XX V f) - gramEntry e (gramPair (nearProjection W) V)

omit [DecidableEq c] in
theorem norm_gramEntry_old_le (V : Matrix (Fin 2 × Fin W) c ℂ) (e : Fin 2 × c × c) :
    ‖gramEntry e (gramPair (nearProjection W) V)‖ ≤ (Vᴴ * V).trace.re :=
  norm_gramEntry_le V (fun x : Fin 2 × Fin W => if x.1 = 0 then 1 else 0)
    (fun x => by split_ifs <;> simp) e

theorem norm_incr_le (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) {R' : ℝ} (hR : (Vᴴ * V).trace.re ≤ R')
    (e : Fin 2 × c × c) (f : LayerSample W .oneBlockOnePort) :
    ‖incr b E XX V e f‖ ≤ R' * (‖freshTransport b E XX f‖ ^ 2 + 1) := by
  have h1 := norm_gramEntry_layerGram_le b E XX V f e
  have h2 := norm_gramEntry_old_le V e
  have h0 : 0 ≤ (Vᴴ * V).trace.re := (norm_nonneg _).trans h2
  have hN : 0 ≤ ‖freshTransport b E XX f‖ ^ 2 := by positivity
  refine (norm_sub_le _ _).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hR hN]

theorem sq_le_pow4 (x : ℝ) : x ^ 2 ≤ x ^ 4 + 1 := by nlinarith [sq_nonneg (x ^ 2 - 1)]

/-- `E_f|incr| ≤ R'(C₄ + 2)`. -/
theorem lintegral_incr_le {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {C₄ : ℝ}
    (h4 : ∫ y, ‖freshTransport b E XX y‖ ^ 4 ∂freshLaw W b ≤ C₄)
    (h4i : Integrable (fun y => ‖freshTransport b E XX y‖ ^ 4) (freshLaw W b))
    (V : Matrix (Fin 2 × Fin W) c ℂ) {R' : ℝ} (hR' : 0 ≤ R') (hR : (Vᴴ * V).trace.re ≤ R')
    (e : Fin 2 × c × c) :
    ∫⁻ f, ‖incr b E XX V e f‖ₑ ∂freshLaw W b ≤ ENNReal.ofReal (R' * (C₄ + 2)) := by
  have hi : Integrable (fun y => R' * (‖freshTransport b E XX y‖ ^ 4 + 2)) (freshLaw W b) :=
    (h4i.add (integrable_const 2)).const_mul R'
  calc ∫⁻ f, ‖incr b E XX V e f‖ₑ ∂freshLaw W b
      ≤ ∫⁻ f, ENNReal.ofReal (R' * (‖freshTransport b E XX f‖ ^ 4 + 2)) ∂freshLaw W b := by
        refine lintegral_mono fun f => ?_
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ((norm_incr_le b E XX V hR e f).trans ?_)
        exact mul_le_mul_of_nonneg_left (by linarith [sq_le_pow4 ‖freshTransport b E XX f‖]) hR'
    _ = ENNReal.ofReal (∫ f, R' * (‖freshTransport b E XX f‖ ^ 4 + 2) ∂freshLaw W b) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun f => by positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add h4i (integrable_const 2)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        exact mul_le_mul_of_nonneg_left (by linarith) hR'

/-- `E_f|incr_e incr_e'| ≤ 2R'²(C₄ + 1)`. -/
theorem lintegral_incr_mul_le {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {C₄ : ℝ}
    (h4 : ∫ y, ‖freshTransport b E XX y‖ ^ 4 ∂freshLaw W b ≤ C₄)
    (h4i : Integrable (fun y => ‖freshTransport b E XX y‖ ^ 4) (freshLaw W b))
    (V : Matrix (Fin 2 × Fin W) c ℂ) {R' : ℝ} (hR' : 0 ≤ R') (hR : (Vᴴ * V).trace.re ≤ R')
    (e e' : Fin 2 × c × c) :
    ∫⁻ f, ‖incr b E XX V e f * incr b E XX V e' f‖ₑ ∂freshLaw W b ≤
      ENNReal.ofReal (2 * R' ^ 2 * (C₄ + 1)) := by
  have hi : Integrable (fun y => 2 * R' ^ 2 * (‖freshTransport b E XX y‖ ^ 4 + 1)) (freshLaw W b) :=
    (h4i.add (integrable_const 1)).const_mul _
  calc ∫⁻ f, ‖incr b E XX V e f * incr b E XX V e' f‖ₑ ∂freshLaw W b
      ≤ ∫⁻ f, ENNReal.ofReal (2 * R' ^ 2 * (‖freshTransport b E XX f‖ ^ 4 + 1)) ∂freshLaw W b := by
        refine lintegral_mono fun f => ?_
        rw [← ofReal_norm, norm_mul]
        refine ENNReal.ofReal_le_ofReal ?_
        have a1 := norm_incr_le b E XX V hR e f
        have a2 := norm_incr_le b E XX V hR e' f
        set t := ‖freshTransport b E XX f‖
        have ht : 0 ≤ t ^ 2 := by positivity
        calc ‖incr b E XX V e f‖ * ‖incr b E XX V e' f‖ ≤ (R' * (t ^ 2 + 1)) * (R' * (t ^ 2 + 1)) :=
              mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
          _ ≤ _ := by nlinarith [sq_nonneg (t ^ 2 - 1), sq_nonneg R']
    _ = ENNReal.ofReal (∫ f, 2 * R' ^ 2 * (‖freshTransport b E XX f‖ ^ 4 + 1) ∂freshLaw W b) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun f => by positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add h4i (integrable_const 1)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end BlockBand.SourceProcess.ClosedSummedProof
