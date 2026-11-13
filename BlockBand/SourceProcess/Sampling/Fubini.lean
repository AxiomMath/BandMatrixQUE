module

public import BlockBand.SourceProcess.Sampling.PathBound
public import BlockBand.SourceProcess.SourceProcessLaw.EarlyHolds

/-!
# Integrating the conditional bound over the path

* `measurable_sampledIntegrand`: the integrand of `sampledPhysTransform` is jointly
  measurable in the path, the tag locations and the Gaussians.
* `cond_eq`: given the path, the integral over `(Π tagSampleLaw) ⊗ (Π CN(0,I))` is the integral
  over `Π (tagSampleLaw ⊗ CN(0,I))` (`measurePreserving_arrowProdEquivProdArrow`).
* `abs_sub_le_integral_condErr` (proved from these in a sibling module): by Fubini and the conditional bound `cond_lindeberg`,
  `|sourceTransform - sampledPhysTransform| ≤ E condErr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.FullSourceStops
open scoped ComplexOrder

variable {W : ℕ}

theorem measurable_tagVector_pair (W n : ℕ) :
    Measurable fun y : ℕ × (Fin W → ℂ) => tagVector W n y.1 y.2 := by
  refine measurable_from_prod_countable_right fun k => ?_
  show Measurable fun g => tagVector W n k g
  simp_rw [tagVector_eq]
  exact Measurable.of_eval fun x => by simp only [mulVec, dotProduct]; fun_prop

theorem measurable_sampledIntegrand (b E : ℝ) (W n : ℕ) {p J : ℕ} (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (M : ℕ) :
    Measurable fun x : SampledPath W p M => ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      ∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M (fun l => x.2.1 (i, l))
        (fun l => x.2.2 (i, l)) x.1).det⁻¹).re := by
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
  have hF : ∀ j, Measurable fun x : SampledPath W p M => ∑ i, (a j i : ℂ) •
      sampledSource b E W n (q i) M (fun l => x.2.1 (i, l)) (fun l => x.2.2 (i, l)) x.1 :=
    fun j => meas_sum' _ fun i => meas_smul' _ (by
      unfold sampledSource; exact meas_sum' _ fun l => meas_smul' _ (hR (i, l)))
  exact measurable_prodInvDet hF

theorem integrable_sampledIntegrand (b E : ℝ) (W n : ℕ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M : ℕ)
    (μ : Measure (SampledPath W p M)) [IsFiniteMeasure μ] :
    Integrable (fun x : SampledPath W p M =>
      ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
        ∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M (fun l => x.2.1 (i, l))
          (fun l => x.2.2 (i, l)) x.1).det⁻¹).re) μ := by
  refine Integrable.of_bound (measurable_sampledIntegrand b E W n q a M).aestronglyMeasurable 1
    (ae_of_all _ fun x => ?_)
  have hS : ∀ i, (sampledSource b E W n (q i) M (fun l => x.2.1 (i, l)) (fun l => x.2.2 (i, l))
      x.1).PosSemidef := fun i => by
    have e : sampledSource b E W n (q i) M (fun l => x.2.1 (i, l)) (fun l => x.2.2 (i, l)) x.1 =
        ∑ l, rankOne (boundaryToInterior b E W n x.1) (gridMass W n (q i) / (M * W))
          (x.2.1 (i, l), x.2.2 (i, l)) := rfl
    rw [e]
    exact posSemidef_sum _ fun l _ =>
      rankOne_psd _ (div_nonneg (gridMass_nonneg W n (hq i)) (by positivity)) _
  have hpsd : ∀ j, (∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M (fun l => x.2.1 (i, l))
      (fun l => x.2.2 (i, l)) x.1).PosSemidef := fun j =>
    posSemidef_sum _ fun i _ => (hS i).smul (by exact_mod_cast ha j i)
  have h := prodInvDet_mem hpsd
  simp only [invDet] at h
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2

/-- **The conditional integral, transported to independent pairs.** -/
theorem cond_eq (b E : ℝ) (W n : ℕ) {p J : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    (a : Fin J → Fin p → ℝ) (M : ℕ) (ω : GrowthPath W) :
    ∫ y, ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
        ∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M (fun l => y.1 (i, l))
          (fun l => y.2 (i, l)) ω).det⁻¹).re
        ∂((Measure.pi fun i : Fin p × Fin M => tagSampleLaw W n (q i.1)).prod
          (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))) =
      ∫ z, hyb (fun _ => 0) (fun j (x : Fin p × Fin M) => a j x.1)
          (fun x => rankOne (boundaryToInterior b E W n ω) (gridMass W n (q x.1) / (M * W)) (z x))
        ∂Measure.pi (fun x : Fin p × Fin M => sampleLaw W n (q x.1)) := by
  have hP : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W n (q x.1)) :=
    fun x => isProbabilityMeasure_tagSampleLaw W n (hq x.1)
  have hmp := measurePreserving_arrowProdEquivProdArrow ℕ (Fin W → ℂ) (Fin p × Fin M)
    (fun x => tagSampleLaw W n (q x.1)) (fun _ => circularVectorLaw (Fin W))
  rw [← hmp.integral_comp']
  exact integral_congr_ae (ae_of_all _ fun z => sampled_eq_hyb b E q a ω z)

end BlockBand.SourceProcess.Sampling
