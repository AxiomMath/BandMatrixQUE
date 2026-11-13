module

public import BlockBand.SourceProcess.ClosingAux.Meas

/-!
# The integrand of `closedSampledTransform` is measurable, bounded and integrable

`closedIntegrand` is the function integrated in `closedSampledTransform`
(`closedSampledTransform_eq`, by `rfl`): on `(x, θ) ∈ SampledPath W p M × ℝ`,
`Π_j Re det(I + C(e^{iθ})ᴴ(Σ_i a_{ji} \widehat Q_{M,i}(x)) C(e^{iθ}))⁻¹`.

* `measurable_closedIntegrand` (every `b E s T h q a M W`): jointly Borel in the path, the tag
  locations, the Gaussians and the phase. So the Bochner integral in `closedSampledTransform`
  is an expectation, never the junk value `0` of a non-measurable integrand.
* `closedIntegrand_mem` (`q ≥ 0`, `a ≥ 0`): `0 ≤ integrand ≤ 1` everywhere (each matrix
  `Cᴴ Q̂ C` is positive semidefinite, `Re det(I+X)⁻¹ ∈ (0,1]` for `X ⪰ 0`).
* `integrable_closedIntegrand` (`q ≥ 0`, `a ≥ 0`): integrable for
  `sampledPathLaw ⊗ phaseLaw` (a probability measure), hence `0 ≤ closedSampledTransform ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingAux

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.Sampling BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped ComplexOrder

variable {W : ℕ}

/-- The integrand of `closedSampledTransform`. -/
def closedIntegrand (b E s T h : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ)
    (M W : ℕ) (y : SampledPath W p M × ℝ) : ℝ :=
  ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      (physClosingMap b E s T h W y.1.1 (phase y.2))ᴴ *
        (∑ i, (a j i : ℂ) • sampledSource b E W ⌊(W : ℝ) * T⌋₊ (q i) M
          (fun l => y.1.2.1 (i, l)) (fun l => y.1.2.2 (i, l)) y.1.1) *
        physClosingMap b E s T h W y.1.1 (phase y.2)).det⁻¹).re

theorem closedSampledTransform_eq (b E s T h : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (M W : ℕ) :
    closedSampledTransform b E s T h q a M W =
      ∫ y, closedIntegrand b E s T h q a M W y
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) := rfl

theorem closedIntegrand_eq (b E s T h : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (M W : ℕ) :
    closedIntegrand b E s T h q a M W = fun y => ∏ j, invDet
      ((physClosingMap b E s T h W y.1.1 (phase y.2))ᴴ *
        (∑ i, (a j i : ℂ) • sampledSource b E W ⌊(W : ℝ) * T⌋₊ (q i) M
          (fun l => y.1.2.1 (i, l)) (fun l => y.1.2.2 (i, l)) y.1.1) *
        physClosingMap b E s T h W y.1.1 (phase y.2)) := rfl

/-- The sampled source combination `Σ_i a_{ji} \widehat Q_{M,i}` is measurable in the sample. -/
theorem measurable_sampledSourceComb (b E : ℝ) (n : ℕ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (M : ℕ) (j : Fin J) :
    Measurable fun x : SampledPath W p M => ∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M
      (fun l => x.2.1 (i, l)) (fun l => x.2.2 (i, l)) x.1 := by
  have hU : Measurable fun x : SampledPath W p M => boundaryToInterior b E W n x.1 :=
    (Measurable.of_eval_matrix _ fun _ _ => (measurable_fullInverse b E n).eval_matrix).comp
      measurable_fst
  have hv : ∀ il : Fin p × Fin M, Measurable fun x : SampledPath W p M =>
      (boundaryToInterior b E W n x.1)ᴴ *ᵥ tagVector W n (x.2.1 il) (x.2.2 il) := by
    intro il
    have hg : Measurable fun x : SampledPath W p M => (x.2.1 il, x.2.2 il) :=
      ((measurable_pi_apply il).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply il).comp (measurable_snd.comp measurable_snd))
    have ht : Measurable fun x : SampledPath W p M => tagVector W n (x.2.1 il) (x.2.2 il) :=
      (measurable_tagVector_pair W n).comp hg
    refine Measurable.of_eval fun c => ?_
    simp only [mulVec, dotProduct, conjTranspose_apply, Complex.star_def]
    exact Finset.measurable_sum _ fun z _ =>
      (Complex.continuous_conj.measurable.comp hU.eval_matrix).mul (ht.eval)
  have hR : ∀ il : Fin p × Fin M, Measurable fun x : SampledPath W p M =>
      vecMulVec ((boundaryToInterior b E W n x.1)ᴴ *ᵥ tagVector W n (x.2.1 il) (x.2.2 il))
        (star ((boundaryToInterior b E W n x.1)ᴴ *ᵥ tagVector W n (x.2.1 il) (x.2.2 il))) := by
    intro il
    refine Measurable.of_eval_matrix _ fun c d => ?_
    simp only [vecMulVec_apply, Pi.star_apply, Complex.star_def]
    exact ((hv il).eval).mul (Complex.continuous_conj.measurable.comp (hv il).eval)
  exact meas_sum' _ fun i => meas_smul' _ (by
    unfold sampledSource; exact meas_sum' _ fun l => meas_smul' _ (hR (i, l)))

/-- **The closed integrand is measurable** (every parameter). -/
theorem measurable_closedIntegrand (b E s T h : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (M W : ℕ) : Measurable (closedIntegrand b E s T h q a M W) := by
  have hC : Measurable fun y : SampledPath W p M × ℝ =>
      physClosingMap b E s T h W y.1.1 (phase y.2) :=
    measurable_physClosingMap_comp b E s T h (measurable_fst.comp measurable_fst) measurable_snd
  rw [closedIntegrand_eq]
  exact measurable_prodInvDet fun j => measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_conjTranspose' hC)
    ((measurable_sampledSourceComb b E _ q a M j).comp measurable_fst)) hC

theorem sampledSourceComb_posSemidef (b E : ℝ) (n : ℕ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M : ℕ)
    (j : Fin J) (x : SampledPath W p M) :
    (∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M (fun l => x.2.1 (i, l))
      (fun l => x.2.2 (i, l)) x.1).PosSemidef := by
  have hS : ∀ i, (sampledSource b E W n (q i) M (fun l => x.2.1 (i, l)) (fun l => x.2.2 (i, l))
      x.1).PosSemidef := fun i => by
    have e : sampledSource b E W n (q i) M (fun l => x.2.1 (i, l)) (fun l => x.2.2 (i, l)) x.1 =
        ∑ l, rankOne (boundaryToInterior b E W n x.1) (gridMass W n (q i) / (M * W))
          (x.2.1 (i, l), x.2.2 (i, l)) := rfl
    rw [e]
    exact posSemidef_sum _ fun l _ =>
      rankOne_psd _ (div_nonneg (gridMass_nonneg W n (hq i)) (by positivity)) _
  exact posSemidef_sum _ fun i _ => (hS i).smul (by exact_mod_cast ha j i)

/-- For `q ≥ 0`, `a ≥ 0` the closed integrand takes values in `[0,1]`. -/
theorem closedIntegrand_mem (b E s T h : ℝ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M W : ℕ)
    (y : SampledPath W p M × ℝ) :
    0 ≤ closedIntegrand b E s T h q a M W y ∧ closedIntegrand b E s T h q a M W y ≤ 1 := by
  rw [closedIntegrand_eq]
  exact prodInvDet_mem fun j =>
    (sampledSourceComb_posSemidef b E ⌊(W : ℝ) * T⌋₊ hq ha M j y.1).conjTranspose_mul_mul_same
      (physClosingMap b E s T h W y.1.1 (phase y.2))

/-- **The closed integrand is integrable** for `sampledPathLaw ⊗ phaseLaw` (`q ≥ 0`, `a ≥ 0`). -/
theorem integrable_closedIntegrand (b E s T h : ℝ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M W : ℕ) :
    Integrable (closedIntegrand b E s T h q a M W)
      ((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) := by
  have : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q x.1)) :=
    fun x => isProbabilityMeasure_tagSampleLaw W _ (hq x.1)
  have : IsProbabilityMeasure (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M) := by
    unfold sampledPathLaw; infer_instance
  refine Integrable.of_bound (measurable_closedIntegrand b E s T h q a M W).aestronglyMeasurable 1
    (ae_of_all _ fun y => ?_)
  have hm := closedIntegrand_mem b E s T h hq ha M W y
  rw [Real.norm_eq_abs, abs_of_nonneg hm.1]; exact hm.2

/-- For `q ≥ 0`, `a ≥ 0`: `0 ≤ closedSampledTransform ≤ 1`. -/
theorem closedSampledTransform_mem (b E s T h : ℝ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M W : ℕ) :
    0 ≤ closedSampledTransform b E s T h q a M W ∧
      closedSampledTransform b E s T h q a M W ≤ 1 := by
  have : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W ⌊(W : ℝ) * T⌋₊ (q x.1)) :=
    fun x => isProbabilityMeasure_tagSampleLaw W _ (hq x.1)
  have : IsProbabilityMeasure (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M) := by
    unfold sampledPathLaw; infer_instance
  rw [closedSampledTransform_eq]
  refine ⟨integral_nonneg fun y => (closedIntegrand_mem b E s T h hq ha M W y).1, ?_⟩
  calc ∫ y, closedIntegrand b E s T h q a M W y
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw)
      ≤ ∫ _y, (1 : ℝ) ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) :=
        integral_mono (integrable_closedIntegrand b E s T h hq ha M W) (integrable_const _)
          fun y => (closedIntegrand_mem b E s T h hq ha M W y).2
    _ = 1 := by simp

end BlockBand.SourceProcess.ClosingAux
