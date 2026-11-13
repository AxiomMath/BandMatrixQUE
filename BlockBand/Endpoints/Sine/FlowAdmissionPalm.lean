module

public import BlockBand.Endpoints.Sine.FlowAdmissionPalmShift

/-!
# The shifted mass Palm identity from the per-exterior coarea identity

`faShiftedMassPalm_holds` proves `FaShiftedMassPalm` from `CoareaContract`. Shifting the pair
residual by `a I_S` amounts, in the inner frame Gaussian integral of the coarea fiber, to the
substitution `G'' = G' + aI` in `GUE_{𝒩-1}(t)` together with a weight identity
(`fap_inner_shift`, `fap_fixed_shift`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

section Transfer

variable (p : Parameters) (i : ZMod p.n)

/-- The inner (frame Gaussian) integral of the coarea fiber at `ω_a`, for a unit `v`, equals the
one at `ω` with the observable `ρ_a(G) g(G - aI)`: substitution `G'' = G' + aI` in
`GUE_{𝒩-1}(t)` and the weight identity `fap_weight_shift`. -/
theorem fap_inner_shift (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (α : Fin p.N) (ω : SplitState p i) (a E : ℝ) (v : PairSite p i → ℂ)
    (hv : l2Norm v = 1) (hUU : (U v)ᴴ * U v = 1) (hUv : (U v)ᴴ *ᵥ v = 0)
    (g : PairMatrix p i → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ G', ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
          clockSpeed p i ω E v * Complex.normSq (frameM p i U ω E v G').det) *
        (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        (fap_gueDensity (pairTime p (pairS p)) a (reconstructedGaussian p i U ω E v G') *
          g (reconstructedGaussian p i U ω E v G' + (-a : ℂ) • 1))
      ∂(gueMeasure (FrameIndex p) (pairTime p (pairS p)))) =
    ∫⁻ G', ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) E v
            (physicalCoareaF (fa_shiftExterior p i a ω).1 (fa_shiftExterior p i a ω).2.1
              (fa_shiftExterior p i a ω).2.2 E) *
          clockSpeed p i (fa_shiftExterior p i a ω) E v *
          Complex.normSq (frameM p i U (fa_shiftExterior p i a ω) E v G').det) *
        (if negativeCount (frameM p i U (fa_shiftExterior p i a ω) E v G') +
            negativeCount ((fa_shiftExterior p i a ω).1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        g (reconstructedGaussian p i U (fa_shiftExterior p i a ω) E v G')
      ∂(gueMeasure (FrameIndex p) (pairTime p (pairS p))) := by
  have ht := fap_pairTime_ne_zero p
  have hM : Measurable fun G'' : Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      frameM p i U ω E v G'' :=
    fap_measurable_matrix_sub (fap_measurable_matrix_add measurable_const measurable_id)
      measurable_const
  have hχ : Measurable fun G'' : Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) E v
            (physicalCoareaF ω.1 ω.2.1 ω.2.2 E + (a : ℂ) • 1) *
          clockSpeed p i ω E v * Complex.normSq (frameM p i U ω E v G'').det) *
        (if negativeCount (frameM p i U ω E v G'') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        g (reconstructedGaussian p i U ω E v G'' + (-a : ℂ) • 1) := by
    refine ((ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Complex.continuous_normSq.measurable.comp
        ((continuous_id.matrix_det).measurable.comp hM)))).mul ?_).mul ?_
    · exact Measurable.ite (measurableSet_eq_fun ((fap_measurable_negativeCount.comp hM).add_const
        _) measurable_const) measurable_const measurable_const
    · exact hg.comp ((fap_measurable_recon_G p i U ω E v).add_const _)
  have hR : ∀ G' : Matrix (FrameIndex p) (FrameIndex p) ℂ,
      ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) E v
            (physicalCoareaF (fa_shiftExterior p i a ω).1 (fa_shiftExterior p i a ω).2.1
              (fa_shiftExterior p i a ω).2.2 E) *
          clockSpeed p i (fa_shiftExterior p i a ω) E v *
          Complex.normSq (frameM p i U (fa_shiftExterior p i a ω) E v G').det) *
        (if negativeCount (frameM p i U (fa_shiftExterior p i a ω) E v G') +
            negativeCount ((fa_shiftExterior p i a ω).1 - (E : ℂ) • 1) = α.val
          then 1 else 0) *
        g (reconstructedGaussian p i U (fa_shiftExterior p i a ω) E v G') =
      ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
          regressionFactor (pairTime p (pairS p)) E v
            (physicalCoareaF ω.1 ω.2.1 ω.2.2 E + (a : ℂ) • 1) *
          clockSpeed p i ω E v *
          Complex.normSq (frameM p i U ω E v (G' + (a : ℂ) • 1)).det) *
        (if negativeCount (frameM p i U ω E v (G' + (a : ℂ) • 1)) +
            negativeCount (ω.1 - (E : ℂ) • 1) = α.val then 1 else 0) *
        g (reconstructedGaussian p i U ω E v (G' + (a : ℂ) • 1) + (-a : ℂ) • 1) := by
    intro G'
    have hsp : clockSpeed p i (fa_shiftExterior p i a ω) E v = clockSpeed p i ω E v := rfl
    have hn : (fa_shiftExterior p i a ω).1 = ω.1 := rfl
    rw [fap_coareaF_shift, fap_frameM_shift p i U a ω E v hUU,
      fap_recon_shift p i U a ω E v hUU,
      sub_eq_add_neg (reconstructedGaussian p i U ω E v (G' + (a : ℂ) • 1)) ((a : ℂ) • 1),
      ← neg_smul (a : ℂ) (1 : PairMatrix p i), hsp, hn]
  rw [lintegral_congr hR, fap_lintegral_gue_shift (pairTime p (pairS p)) ht a hχ]
  refine lintegral_congr fun G'' => ?_
  have hc : 0 ≤ coareaConstant (2 * p.W) (pairTime p (pairS p)) := by
    unfold coareaConstant; positivity
  have hw := fap_weight_shift p i U a ω E v hv hUU hUv _ _ _ hc (fap_clockSpeed_nonneg p i ω E v)
    (Complex.normSq_nonneg (frameM p i U ω E v G'').det) G''
  exact fap_rearrange _ _ _ _ _ _ hw

/-- **Transfer of the fixed-`ω` coarea identity along the pair shift.** If the fixed-`ω`
identity (`FapFixedAt`, the conclusion of the `CoareaContract.formula_fixed`) holds at
`ω` for a rank `α`, it holds at `ω_a = (H_R, C, V + aI)` for the same rank, for every real `a`.
Deterministic: no law of `ω` enters.
-/
theorem fap_fixed_shift (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (hU : IsPairFrame p i U) (α : Fin p.N) (ω : SplitState p i) (a : ℝ)
    (hfix : FapFixedAt p i U α ω) : FapFixedAt p i U α (fa_shiftExterior p i a ω) := by
  intro g hg
  have ht := fap_pairTime_ne_zero p
  have hφ : Measurable fun H : PairMatrix p i => g (H + (-a : ℂ) • 1) :=
    hg.comp (measurable_id.add_const _)
  have h1 := fap_lintegral_gue_shift (pairTime p (pairS p)) ht a hφ
  have hcancel : ∀ G : PairMatrix p i, G + (a : ℂ) • 1 + (-a : ℂ) • 1 = G := fun G => by
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  simp only [hcancel] at h1
  rw [h1]
  refine (hfix (fun G => fap_gueDensity (pairTime p (pairS p)) a G * g (G + (-a : ℂ) • 1))
    ((fap_measurable_gueDensity _ a).mul hφ)).trans ?_
  unfold coareaFiber
  have := fap_nonempty_pairSite p i
  refine lintegral_congr fun E => lintegral_congr_ae ?_
  filter_upwards [fap_ae_l2Norm_projectiveHaar (PairSite p i)] with v hv
  obtain ⟨hUU, hUv⟩ := hU.2 v hv
  exact fap_inner_shift p i U α ω a E v hv hUU hUv g hg

end Transfer

/-!
## The shifted mass Palm identity
-/

/-- **The mass Palm identity under a deterministic scalar pair shift** (`FaShiftedMassPalm`),
from `CoareaContract` only. -/
theorem faShiftedMassPalm_holds (hCo : CoareaContract) : FaShiftedMassPalm := by
  intro p model i Pω hP U hU a f hf
  have hPprob := isProbabilityMeasure_of_splitting p i model _ Pω hP
  have := isProbabilityMeasure_gueMeasure (PairSite p i) (pairTime p (pairS p))
  have hA := measurable_assemble p i
  have hΨ : Measurable fun H : p.SiteMatrix => ∑ α : Fin p.N,
      ENNReal.ofReal (pairMass p i α H) *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α) :=
    Finset.measurable_sum _ fun α _ =>
      (ENNReal.measurable_ofReal.comp ((measurable_physicalOrderedBlockMass p α i).add
        (measurable_physicalOrderedBlockMass p α (i + 1)))).mul
        (hf.comp ((measurable_physicalOrderedEigenvalue p α).prodMk
          (Measurable.of_eval fun k => measurable_physicalOrderedBlockMass p α k)))
  have hΨs : Measurable fun H : p.SiteMatrix => ∑ α : Fin p.N,
      ENNReal.ofReal (pairMass p i α (H + (a : ℂ) • pairProjector p i)) *
        f (physicalOrderedEigenvalue p (H + (a : ℂ) • pairProjector p i) α)
          (blockMassVector p (H + (a : ℂ) • pairProjector p i) α) :=
    hΨ.comp (measurable_id.add_const _)
  have hcomp : Measurable fun x : SplitState p i × PairMatrix p i => ∑ α : Fin p.N,
      ENNReal.ofReal (pairMass p i α (assemble p i x.1 x.2 + (a : ℂ) • pairProjector p i)) *
        f (physicalOrderedEigenvalue p (assemble p i x.1 x.2 + (a : ℂ) • pairProjector p i) α)
          (blockMassVector p (assemble p i x.1 x.2 + (a : ℂ) • pairProjector p i) α) :=
    hΨs.comp hA
  rw [← hP, lintegral_map hΨs hA, lintegral_prod _ hcomp.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [fa_ae_isHermitianExterior p i model _ Pω hP,
    ae_all_iff.2 fun α : Fin p.N => hCo.formula_fixed p model α i (pairS p)
      (lt_min p.b_pos p.c_pos) (min_comm p.b p.c).le Pω hP U hU] with ω hω hfix
  have hfixa : ∀ α, FapFixedAt p i U α (fa_shiftExterior p i a ω) := fun α =>
    fap_fixed_shift p i U hU α ω a (hfix α)
  simp only [fap_assemble_shift]
  exact fap_mass_fiber hCo p i U hU (fa_shiftExterior p i a ω) hω.1
    (hω.2.add (isHermitian_real_smul_one a)) hfixa f hf

end BlockBand.Endpoints
