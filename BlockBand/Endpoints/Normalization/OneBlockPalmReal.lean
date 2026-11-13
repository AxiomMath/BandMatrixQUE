module

public import BlockBand.Endpoints.Normalization.OneBlockPalmMass
public import BlockBand.Endpoints.Normalization.ExactPalmReal

/-!
# One-block Palm identity: clauses `massReal` and `indexReal`

These are the signed forms of the one-block Palm identities: apply the identities to nonnegative
functions, then subtract their positive and negative parts. No contract is used.

**Proof** (as in the pair case of `ExactPalmReal`). Measures: the exact physical law on the
left; `Pω`, Lebesgue `de`, `projectiveHaar` and `GUE_{W-1}(c/W)` on the right; Bochner
integrals. Write `f = f⁺ - f⁻` and apply the `[0,∞]` clauses `oneBlockPalm_mass`,
`oneBlockPalm_index` to `ofReal ∘ f^±`. Finiteness: `|f| ≤ M` and the
block masses are `≤ 1` almost surely (they sum to one over blocks), so the left sides are at
most `NM` (`mass`) and `M` (`index`). The generic signed-integral lemmas
(`integral_integral_eq_toReal_sub`, `sum_eq_toReal_sub`, `signedParts`) are reused from the
pair case; the `ω`-measurability of the energy integral comes from its a.s. equality
with a section of a jointly measurable function (`oneBlockPalm_massFiber_ae`,
`oneBlockPalm_indexFiber_ae`). Only boundedness is used (compact energy support not needed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

section Fiber

variable (p : Parameters) (k : ZMod p.n)

/-- **Signed one-block angular fiber**: `𝒜⁰_{ℓ,e}[h⁺ - h⁻] = 𝒜⁰_{ℓ,e}[h⁺].toReal -
𝒜⁰_{ℓ,e}[h⁻].toReal` for measurable `h^± ≥ 0` with finite angular masses. -/
theorem oneBlockPalm_sectorFiberReal_eq_toReal_sub
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (e : ℝ) (ℓ : ℕ)
    (g hp hm : (BlockSite p k → ℂ) → ℝ)
    (hpm : Measurable hp) (hmm : Measurable hm) (hp0 : ∀ v, 0 ≤ hp v) (hm0 : ∀ v, 0 ≤ hm v)
    (hg : ∀ v, g v = hp v - hm v)
    (hpf : blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (hp v)) ≠ ∞)
    (hmf : blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (hm v)) ≠ ∞) :
    blockSectorFiberReal p k U ω e ℓ g =
      (blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (hp v))).toReal -
        (blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (hm v))).toReal := by
  have hmeas : ∀ h : (BlockSite p k → ℂ) → ℝ, Measurable h →
      Measurable fun q : (BlockSite p k → ℂ) × Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
        ENNReal.ofReal (coareaConstant p.W (blockTime p) *
            regressionFactor (blockTime p) e q.1 (blockF p k ω e) *
            Complex.normSq (blockFrameM p k U ω e q.1 q.2).det) *
          (if negativeCount (blockFrameM p k U ω e q.1 q.2) = ℓ then 1 else 0) *
          ENNReal.ofReal (h q.1) := by
    intro h hh
    have hg : Measurable (Function.uncurry fun (_ : ℝ) (v : BlockSite p k → ℂ) =>
        ENNReal.ofReal (h v)) := ENNReal.measurable_ofReal.comp (hh.comp measurable_snd)
    have h1 := oneBlockPalm_measurable_sectorIntegrand p k U hU ω ℓ
      (fun _ v => ENNReal.ofReal (h v)) hg
    have h2 : Measurable fun q : (BlockSite p k → ℂ) ×
        Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ =>
        ((e, q.1), q.2) := (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have h3 := h1.comp h2
    simp only [Function.comp_def] at h3
    exact h3
  unfold blockSectorFiber at hpf hmf
  unfold blockSectorFiber blockSectorFiberReal
  refine integral_integral_eq_toReal_sub _
    (fun v G' => ENNReal.ofReal (coareaConstant p.W (blockTime p) *
            regressionFactor (blockTime p) e v (blockF p k ω e) *
            Complex.normSq (blockFrameM p k U ω e v G').det) *
          (if negativeCount (blockFrameM p k U ω e v G') = ℓ then 1 else 0) *
          ENNReal.ofReal (hp v))
    (fun v G' => ENNReal.ofReal (coareaConstant p.W (blockTime p) *
            regressionFactor (blockTime p) e v (blockF p k ω e) *
            Complex.normSq (blockFrameM p k U ω e v G').det) *
          (if negativeCount (blockFrameM p k U ω e v G') = ℓ then 1 else 0) *
          ENNReal.ofReal (hm v))
    (ae_of_all _ fun v => ((hmeas hp hpm).comp measurable_prodMk_left).aemeasurable)
    (ae_of_all _ fun v => ((hmeas hm hmm).comp measurable_prodMk_left).aemeasurable)
    (hmeas hp hpm).lintegral_prod_right'.aemeasurable
    (hmeas hm hmm).lintegral_prod_right'.aemeasurable hpf hmf
    (ae_of_all _ fun v => ae_of_all _ fun G' => fun _ _ => ?_)
  have hw : 0 ≤ coareaConstant p.W (blockTime p) *
      regressionFactor (blockTime p) e v (blockF p k ω e) *
      Complex.normSq (blockFrameM p k U ω e v G').det :=
    mul_nonneg (oneBlockPalm_coareaConstant_mul_regression_nonneg p k _ e v _)
      (Complex.normSq_nonneg _)
  rw [hg v]
  split_ifs
  · simp only [mul_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hw,
      ENNReal.toReal_ofReal (hp0 v), ENNReal.toReal_ofReal (hm0 v)]
    ring
  · simp only [mul_zero, zero_mul, ENNReal.toReal_zero, sub_zero]

end Fiber

section Helpers

variable (p : Parameters) (k : ZMod p.n)

/-- Block masses are at most `1` almost surely (they sum to one over the blocks). -/
theorem oneBlockPalm_blockMass_le_one_ae (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α : Fin p.N,
      physicalOrderedBlockMass p H α k ≤ 1 := by
  filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH α
  rw [← hH α]
  exact Finset.single_le_sum (fun j _ => physicalOrderedBlockMass_nonneg p H α j)
    (Finset.mem_univ k)

/-- The one-block `mass` observable `Σ_α p_{αk} g(λ_α, p_α)` is measurable. -/
theorem oneBlockPalm_measurable_massObs (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun H : p.SiteMatrix => ∑ α : Fin p.N,
      ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) :=
  Finset.measurable_sum _ fun α _ =>
    (ENNReal.measurable_ofReal.comp (measurable_physicalOrderedBlockMass p α k)).mul
      (ENNReal.measurable_ofReal.comp (hg.comp (measurable_rankMarks p α)))

/-- Finiteness of the one-block `mass` left side for `g ≤ M`. -/
theorem oneBlockPalm_massObs_lintegral_ne_top (model : p.GaussianRingModel)
    (g : ℝ → (ZMod p.n → ℝ) → ℝ) (M : ℝ) (hgM : ∀ e x, g e x ≤ M) :
    (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
      ∂(model.law : Measure p.SiteMatrix)) ≠ ∞ := by
  have hle : (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
      ∂(model.law : Measure p.SiteMatrix)) ≤
      ∫⁻ _H, ∑ _α : Fin p.N, ENNReal.ofReal 1 * ENNReal.ofReal M
        ∂(model.law : Measure p.SiteMatrix) := by
    refine lintegral_mono_ae ?_
    filter_upwards [oneBlockPalm_blockMass_le_one_ae p k model] with H hH
    exact Finset.sum_le_sum fun α _ =>
      mul_le_mul' (ENNReal.ofReal_le_ofReal (hH α)) (ENNReal.ofReal_le_ofReal (hgM _ _))
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top

theorem oneBlockPalm_measurable_section_recon (ω : BlockState p k) (e : ℝ)
    (g : ℝ → (ZMod p.n → ℝ) → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable fun v : BlockSite p k → ℂ => g e (blockReconMass p k ω e v) := by
  have h1 := hg.comp (measurable_fst.prodMk (oneBlockPalm_measurable_reconMass_joint p k ω))
  have h2 := h1.comp (measurable_prodMk_left (x := e))
  simp only [Function.comp_def] at h2
  exact h2

theorem oneBlockPalm_measurable_ofReal_recon (ω : BlockState p k)
    (g : ℝ → (ZMod p.n → ℝ) → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry fun (e : ℝ) (v : BlockSite p k → ℂ) =>
      ENNReal.ofReal (g e (blockReconMass p k ω e v))) :=
  ENNReal.measurable_ofReal.comp
    (hg.comp (measurable_fst.prodMk (oneBlockPalm_measurable_reconMass_joint p k ω)))

theorem oneBlockPalm_measurable_massSectorSum
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun e : ℝ => ∑ ℓ ∈ Finset.range p.W,
      blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (g e (blockReconMass p k ω e v))) :=
  Finset.measurable_sum _ fun ℓ _ => oneBlockPalm_measurable_blockSectorFiber p k U hU ω ℓ _
    (oneBlockPalm_measurable_ofReal_recon p k ω g hg)

theorem oneBlockPalm_aemeasurable_massEnergy (model : p.GaussianRingModel)
    (Pω : Measure (BlockState p k)) (hP : IsBlockSplitting p k model Pω)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    AEMeasurable (fun ω => ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
      blockSectorFiber p k U ω e ℓ
        (fun v => ENNReal.ofReal (g e (blockReconMass p k ω e v)))) Pω := by
  have hae := oneBlockPalm_massFiber_ae p model k Pω hP U hU
    (fun e x => ENNReal.ofReal (g e x)) (ENNReal.measurable_ofReal.comp hg)
  beta_reduce at hae
  have h1 := ((oneBlockPalm_measurable_massObs p k g hg).comp
    (regularEvent_measurable_assembleBlock p k)).lintegral_prod_right'
    (ν := gueMeasure (BlockSite p k) (blockTime p))
  simp only [Function.comp_def] at h1
  exact h1.aemeasurable.congr hae

theorem oneBlockPalm_measurable_indexSectorSum
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : Measurable U) (ω : BlockState p k) (α : Fin p.N) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun e : ℝ => ∑ ℓ ∈ Finset.range p.W,
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
        ENNReal.ofReal (g e (blockReconMass p k ω e v))) := by
  have hNR := oneBlockPalm_measurable_offShiftCount p k ω
  have hgm : Measurable (Function.uncurry fun (e : ℝ) (v : BlockSite p k → ℂ) =>
      ENNReal.ofReal (blockClockSpeed p k ω e v) *
        ENNReal.ofReal (g e (blockReconMass p k ω e v))) :=
    (ENNReal.measurable_ofReal.comp (oneBlockPalm_measurable_clockSpeed_joint p k ω)).mul
      (oneBlockPalm_measurable_ofReal_recon p k ω g hg)
  exact Finset.measurable_sum _ fun ℓ _ =>
    (Measurable.ite (measurableSet_eq_fun (hNR.const_add ℓ) measurable_const)
      measurable_const measurable_const).mul
      (oneBlockPalm_measurable_blockSectorFiber p k U hU ω ℓ _ hgm)

theorem oneBlockPalm_aemeasurable_indexEnergy (model : p.GaussianRingModel)
    (Pω : Measure (BlockState p k)) (hP : IsBlockSplitting p k model Pω)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (α : Fin p.N) (g : ℝ → (ZMod p.n → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    AEMeasurable (fun ω => ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
        ENNReal.ofReal (g e (blockReconMass p k ω e v)))) Pω := by
  have hae := oneBlockPalm_indexFiber_ae p model k Pω hP U hU α
    (fun e x => ENNReal.ofReal (g e x)) (ENNReal.measurable_ofReal.comp hg)
  beta_reduce at hae
  have hobs : Measurable fun H : p.SiteMatrix =>
      ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) :=
    ENNReal.measurable_ofReal.comp (hg.comp (measurable_rankMarks p α))
  have h1 := (hobs.comp (regularEvent_measurable_assembleBlock p k)).lintegral_prod_right'
    (ν := gueMeasure (BlockSite p k) (blockTime p))
  simp only [Function.comp_def] at h1
  exact h1.aemeasurable.congr hae

end Helpers

/-- **`OneBlockPalmContract.massReal`** (one-block corollary of the mass Palm identity,
signed form): for bounded measurable real `f` with compact energy support,
`E Σ_α p_{αk} f(λ_α, p_α) = E_ext ∫ Σ_ℓ 𝒜⁰_{ℓ,e}[f(e, p(v,e))] de` (Bochner integrals). -/
theorem oneBlockPalm_massReal : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ, Measurable (Function.uncurry f) →
      IsBoundedCompactEnergy f →
      (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α k *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiberReal p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v))
        ∂volume ∂Pω := by
  intro p model k Pω hP U hU f hf hfb
  obtain ⟨⟨M, hM⟩, -⟩ := hfb
  obtain ⟨fp, fm, hfp0, hfm0, hfpM, hfmM, hsub, hfpm, hfmm⟩ := signedParts f hf M hM
  have hLHS : (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α k *
        f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
          ENNReal.ofReal (fp (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal -
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
          ENNReal.ofReal (fm (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal := by
    rw [← integral_toReal_sub_toReal (oneBlockPalm_measurable_massObs p k fp hfpm).aemeasurable
      (oneBlockPalm_measurable_massObs p k fm hfmm).aemeasurable
      (oneBlockPalm_massObs_lintegral_ne_top p k model fp M hfpM)
      (oneBlockPalm_massObs_lintegral_ne_top p k model fm M hfmM)]
    refine integral_congr_ae (ae_of_all _ fun H => ?_)
    have hfin : ∀ (g : ℝ → (ZMod p.n → ℝ) → ℝ), ∀ α ∈ (Finset.univ : Finset (Fin p.N)),
        ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
          ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) ≠ ∞ :=
      fun g α _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    simp only
    rw [ENNReal.toReal_sum (hfin fp), ENNReal.toReal_sum (hfin fm), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (physicalOrderedBlockMass_nonneg p H α k),
      ENNReal.toReal_ofReal (hfp0 _ _), ENNReal.toReal_ofReal (hfm0 _ _), hsub]
    ring
  have hmp := oneBlockPalm_mass p model k Pω hP U hU
    (fun e x => ENNReal.ofReal (fp e x)) (ENNReal.measurable_ofReal.comp hfpm)
  have hmm := oneBlockPalm_mass p model k Pω hP U hU
    (fun e x => ENNReal.ofReal (fm e x)) (ENNReal.measurable_ofReal.comp hfmm)
  beta_reduce at hmp hmm
  rw [hLHS, hmp, hmm]
  symm
  refine integral_integral_eq_toReal_sub _
    (fun ω e => ∑ ℓ ∈ Finset.range p.W,
      blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (fp e (blockReconMass p k ω e v))))
    (fun ω e => ∑ ℓ ∈ Finset.range p.W,
      blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (fm e (blockReconMass p k ω e v))))
    (ae_of_all _ fun ω =>
      (oneBlockPalm_measurable_massSectorSum p k U hU.1 ω fp hfpm).aemeasurable)
    (ae_of_all _ fun ω =>
      (oneBlockPalm_measurable_massSectorSum p k U hU.1 ω fm hfmm).aemeasurable)
    (oneBlockPalm_aemeasurable_massEnergy p k model Pω hP U hU fp hfpm)
    (oneBlockPalm_aemeasurable_massEnergy p k model Pω hP U hU fm hfmm)
    (by rw [← hmp]; exact oneBlockPalm_massObs_lintegral_ne_top p k model fp M hfpM)
    (by rw [← hmm]; exact oneBlockPalm_massObs_lintegral_ne_top p k model fm M hfmM)
    (ae_of_all _ fun ω => ae_of_all _ fun e => fun hAe hBe => ?_)
  refine sum_eq_toReal_sub _ _ _ _ hAe hBe fun ℓ _ ha hb => ?_
  exact oneBlockPalm_sectorFiberReal_eq_toReal_sub p k U hU.1 ω e ℓ _
    (fun v => fp e (blockReconMass p k ω e v)) (fun v => fm e (blockReconMass p k ω e v))
    (oneBlockPalm_measurable_section_recon p k ω e fp hfpm)
    (oneBlockPalm_measurable_section_recon p k ω e fm hfmm)
    (fun v => hfp0 _ _) (fun v => hfm0 _ _) (fun v => hsub _ _) ha hb

/-- **`OneBlockPalmContract.indexReal`** (one-block corollary of
the index Palm identity, signed form): for bounded measurable real `f` with compact energy support
and every rank `α`,
`E f(λ_α, p_α) = E_ext ∫ Σ_ℓ 1{ℓ + N_-(H_R - e) = α} 𝒜⁰_{ℓ,e}[(v*Dv) f(e, p(v,e))] de`. -/
theorem oneBlockPalm_indexReal : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ),
      Measurable (Function.uncurry f) → IsBoundedCompactEnergy f →
      (∫ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiberReal p k U ω e ℓ
            (fun v => blockClockSpeed p k ω e v * f e (blockReconMass p k ω e v))
        ∂volume ∂Pω := by
  intro p model k Pω hP U hU α f hf hfb
  obtain ⟨⟨M, hM⟩, -⟩ := hfb
  obtain ⟨fp, fm, hfp0, hfm0, hfpM, hfmM, hsub, hfpm, hfmm⟩ := signedParts f hf M hM
  have hobs : ∀ g : ℝ → (ZMod p.n → ℝ) → ℝ, Measurable (Function.uncurry g) →
      Measurable fun H : p.SiteMatrix =>
        ENNReal.ofReal (g (physicalOrderedEigenvalue p H α) (blockMassVector p H α)) :=
    fun g hg => ENNReal.measurable_ofReal.comp (hg.comp (measurable_rankMarks p α))
  have hLHS : (∫ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      (∫⁻ H, ENNReal.ofReal (fp (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal -
      (∫⁻ H, ENNReal.ofReal (fm (physicalOrderedEigenvalue p H α) (blockMassVector p H α))
        ∂(model.law : Measure p.SiteMatrix)).toReal := by
    rw [← integral_toReal_sub_toReal (hobs fp hfpm).aemeasurable (hobs fm hfmm).aemeasurable
      (indexObs_lintegral_ne_top p model α fp M hfpM)
      (indexObs_lintegral_ne_top p model α fm M hfmM)]
    refine integral_congr_ae (ae_of_all _ fun H => ?_)
    simp only
    rw [ENNReal.toReal_ofReal (hfp0 _ _), ENNReal.toReal_ofReal (hfm0 _ _), hsub]
  have hmp := oneBlockPalm_index p model k Pω hP U hU α
    (fun e x => ENNReal.ofReal (fp e x)) (ENNReal.measurable_ofReal.comp hfpm)
  have hmm := oneBlockPalm_index p model k Pω hP U hU α
    (fun e x => ENNReal.ofReal (fm e x)) (ENNReal.measurable_ofReal.comp hfmm)
  beta_reduce at hmp hmm
  rw [hLHS, hmp, hmm]
  symm
  refine integral_integral_eq_toReal_sub _
    (fun ω (e : ℝ) => ∑ ℓ ∈ Finset.range p.W,
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
        ENNReal.ofReal (fp e (blockReconMass p k ω e v))))
    (fun ω (e : ℝ) => ∑ ℓ ∈ Finset.range p.W,
      (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
      blockSectorFiber p k U ω e ℓ (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
        ENNReal.ofReal (fm e (blockReconMass p k ω e v))))
    (ae_of_all _ fun ω =>
      (oneBlockPalm_measurable_indexSectorSum p k U hU.1 ω α fp hfpm).aemeasurable)
    (ae_of_all _ fun ω =>
      (oneBlockPalm_measurable_indexSectorSum p k U hU.1 ω α fm hfmm).aemeasurable)
    (oneBlockPalm_aemeasurable_indexEnergy p k model Pω hP U hU α fp hfpm)
    (oneBlockPalm_aemeasurable_indexEnergy p k model Pω hP U hU α fm hfmm)
    (by rw [← hmp]; exact indexObs_lintegral_ne_top p model α fp M hfpM)
    (by rw [← hmm]; exact indexObs_lintegral_ne_top p model α fm M hfmM)
    (ae_of_all _ fun ω => ae_of_all _ fun e => fun hAe hBe => ?_)
  refine sum_eq_toReal_sub _ _ _ _ hAe hBe fun ℓ _ ha hb => ?_
  by_cases hc : ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val
  · simp only [hc, ite_true, one_mul] at ha hb ⊢
    have hcs : ∀ g : ℝ → (ZMod p.n → ℝ) → ℝ, (∀ e x, 0 ≤ g e x) →
        (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
          ENNReal.ofReal (g e (blockReconMass p k ω e v))) =
        fun v => ENNReal.ofReal (blockClockSpeed p k ω e v * g e (blockReconMass p k ω e v)) :=
      fun g _ => funext fun v =>
        (ENNReal.ofReal_mul (oneBlockPalm_clockSpeed_nonneg p k ω e v)).symm
    rw [hcs fp hfp0] at ha ⊢
    rw [hcs fm hfm0] at hb ⊢
    have hcsm : Measurable fun v : BlockSite p k → ℂ => blockClockSpeed p k ω e v := by
      have h1 := (oneBlockPalm_measurable_clockSpeed_joint p k ω).comp
        (measurable_prodMk_left (x := e))
      simp only [Function.comp_def] at h1
      exact h1
    exact oneBlockPalm_sectorFiberReal_eq_toReal_sub p k U hU.1 ω e ℓ _
      (fun v => blockClockSpeed p k ω e v * fp e (blockReconMass p k ω e v))
      (fun v => blockClockSpeed p k ω e v * fm e (blockReconMass p k ω e v))
      (hcsm.mul (oneBlockPalm_measurable_section_recon p k ω e fp hfpm))
      (hcsm.mul (oneBlockPalm_measurable_section_recon p k ω e fm hfmm))
      (fun v => mul_nonneg (oneBlockPalm_clockSpeed_nonneg p k ω e v) (hfp0 _ _))
      (fun v => mul_nonneg (oneBlockPalm_clockSpeed_nonneg p k ω e v) (hfm0 _ _))
      (fun v => by rw [hsub]; ring) ha hb
  · simp only [hc, ite_false, zero_mul, ENNReal.toReal_zero, sub_zero]

end BlockBand.Endpoints.Normalization
