module

public import BlockBand.SourceProcess.ComplexSourceLaw.ExtHS
public import BlockBand.SourceProcess.ComplexSourceLaw.Assembly

/-!
# The extended source moments from the raw tag moments

`extendedSourceMoments_of_raw : RawTagMoments → ExtendedSourceMoments` combines the trace term
(`lintegral_trace_le`) and the Hilbert–Schmidt term (`lintegral_hs_le`) with the bound
`S = Σ_k q_k/W ≤ max(q̄, 0) max(T, 0)`. Hence `complexSourceLawContract_of'` needs only
`ComplexFiniteUniqueness`, `ComplexSourceConstruction` and `RawTagMoments`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge

variable {W n : ℕ}

theorem measurable_extendedSourceMatrix (b E : ℝ) (q : Fin n → ℝ) :
    Measurable (extendedSourceMatrix b E W n q) :=
  measurable_matrix_smul _ (measurable_matrix_mul' (measurable_matrix_mul' measurable_const
    (measurable_interior b E n)) measurable_const)

theorem measurable_trace_rpow (b E : ℝ) (q : Fin n → ℝ) (p : ℝ) :
    Measurable fun ω : GrowthPath W =>
      ENNReal.ofReal (‖(extendedSourceMatrix b E W n q ω).trace‖ ^ p) :=
  ((Finset.measurable_sum _ fun _ _ =>
    (measurable_extendedSourceMatrix b E q).eval_matrix).norm.pow_const p).ennreal_ofReal

/-- `S = Σ_k q_k/W ≤ max(q̄, 0) max(T, 0)` for `n ≤ TW`, `W > 0`. -/
theorem sum_weights_le {T qmax : ℝ} (hW : 0 < W) (hn : (n : ℝ) ≤ T * W) (q : Fin n → ℝ)
    (hq : ∀ k, 0 ≤ q k ∧ q k ≤ qmax) :
    ∑ k, q k / W ≤ max qmax 0 * max T 0 := by
  have hWr : (0 : ℝ) < W := Nat.cast_pos.2 hW
  calc ∑ k, q k / W ≤ ∑ _k : Fin n, max qmax 0 / W :=
        Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right ((hq k).2.trans
          (le_max_left _ _)) hWr.le
    _ = max qmax 0 * ((n : ℝ) / W) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ max qmax 0 * max T 0 := by
        refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
        rw [div_le_iff₀ hWr]
        exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le)

/-- **The extended source moments from the raw tag moments.** -/
theorem extendedSourceMoments_of_raw (hR : RawTagMoments) : ExtendedSourceMoments := by
  intro b hb0 hb1 κI hκ T p qmax hp
  obtain ⟨C, W₀, hC⟩ := hR b hb0 hb1 κI hκ T p hp
  obtain ⟨C', W₀', hC'⟩ := hR b hb0 hb1 κI hκ T (max p 2) (hp.trans (le_max_left _ _))
  set Q := max qmax 0 * max T 0
  have hQ : 0 ≤ Q := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hp1 : 0 ≤ p - 1 := by linarith
  have hr1 : 0 ≤ max p 2 / 2 - 1 := by
    have := le_max_right p 2; linarith
  refine ⟨Q ^ (p - 1) * (Q * max C 0) + (1 + (Q ^ 2) ^ (max p 2 / 2 - 1) * (Q ^ 2 * max C' 0)),
    max (max W₀ W₀') 1, fun W hW E hE n hn q hq => ?_⟩
  have hW₀ : W₀ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW₀' : W₀' ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW1 : 0 < W := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hW)
  have hq0 : ∀ k, 0 ≤ q k := fun k => (hq k).1
  have hS := sum_weights_le hW1 hn q hq
  have hS0 : 0 ≤ ∑ k, q k / W := Finset.sum_nonneg fun k _ => div_nonneg (hq0 k) (Nat.cast_nonneg W)
  have htr := lintegral_trace_le b E q hq0 hp (hC W hW₀ E hE n hn)
  have hhs := lintegral_hs_le b E q hq0 hp (hC' W hW₀' E hE n hn)
  have hsplit : ∀ ω, ENNReal.ofReal (‖(extendedSourceMatrix b E W n q ω).trace‖ ^ p +
      Real.sqrt (∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2) ^ p) =
      ENNReal.ofReal (‖(extendedSourceMatrix b E W n q ω).trace‖ ^ p) +
        ENNReal.ofReal (Real.sqrt (∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2) ^ p) :=
    fun ω => ENNReal.ofReal_add (by positivity) (by positivity)
  rw [lintegral_congr hsplit, lintegral_add_left (measurable_trace_rpow b E q p)]
  refine (add_le_add htr hhs).trans ?_
  have hS2 : (∑ k, q k / W) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hS0 hS 2
  calc _ ≤ ENNReal.ofReal (Q ^ (p - 1)) * (ENNReal.ofReal Q * ENNReal.ofReal (max C 0)) +
        (1 + ENNReal.ofReal ((Q ^ 2) ^ (max p 2 / 2 - 1)) *
          (ENNReal.ofReal (Q ^ 2) * ENNReal.ofReal (max C' 0))) := by
        have h1 := Real.rpow_le_rpow hS0 hS hp1
        have h2 := Real.rpow_le_rpow (sq_nonneg _) hS2 hr1
        have h3 := le_max_left C 0
        have h4 := le_max_left C' 0
        gcongr
    _ = _ := by
        have hC0 := le_max_right C 0
        have hC0' := le_max_right C' 0
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_mul (Real.rpow_nonneg hQ _),
          ENNReal.ofReal_mul (Real.rpow_nonneg (sq_nonneg Q) _), ENNReal.ofReal_mul hQ,
          ENNReal.ofReal_mul (sq_nonneg Q)]

/-- **The complex source law theorem** `ComplexSourceLawContract` from `ComplexFiniteUniqueness`,
`ComplexSourceConstruction` and `RawTagMoments`; the field `extendedSourceMoments` is derived
from `RawTagMoments`. -/
theorem complexSourceLawContract_of' (hU : ComplexFiniteUniqueness)
    (hC : ComplexSourceConstruction) (hR : RawTagMoments) : ComplexSourceLawContract :=
  complexSourceLawContract_of hU hC hR (extendedSourceMoments_of_raw hR)

end BlockBand.SourceProcess.ComplexSourceLaw
