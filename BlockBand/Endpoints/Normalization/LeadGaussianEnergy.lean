module

public import BlockBand.Endpoints.Normalization.LeadGaussianMeasurable
public import BlockBand.Endpoints.Normalization.LeadProfileRegularitySide

/-!
# The physical lead-profile theorem at a fixed energy (integrated over the exterior)

**Main results.**
* `energy_palm_field_comparison` (the energy-wise form; from `FreshEigenpairDensityContract`, `GaussianRatiosContract`, `BlockRegularEventContract`). Fixed
  first: `b ∈ (0,1/2)`, the bulk range `bulkInterval κ`, `T`, `m`, a continuous `ψ` on
  `[-1,1]^m` and `ε > 0`. There is `W₀` such that for every admissible `p` with this `b`,
  `W ≥ W₀`, `n ≤ TW`, every model, one-block splitting law `Pω` of block `0`, block frame `U`,
  `e ∈ bulkInterval κ`, and every family `(B_ω, d_ω)` of sandwiched forms and measurable defaults
  and bounded measurable mass-vector observable `g` (`|g| ≤ M_g`) with
  `|g(p(v,e)) - |S|⁻¹ Σ_s ψ(ratioCube B_{ω,s} D_ω d_{ω,s} v)| ≤ δ` for all `ω, v`:
  `|E_ω Σ_ℓ 𝒜⁰_{ℓ,e}[g(p)]/Z₀(e) - E_ω E_g g(p(M_ω g, e))| ≤ 2δ + 2ε + 4 M_g ε`.
  The exceptional exterior event (non-Hermitian `H_R`, failure of `IsBlockRegular` at `D = 1`,
  failure of the Loewner closeness of `BlockGammaClosenessContract`) has probability `≤ 2ε`.
* `energy_deletion` (energy-wise; no contract is used, the field law being
  `leadFieldIdentification_holds`): for every `Φ`, `ε > 0` there is `C ≥ 0` with, for every
  `p`, model, `Pω`, `|e| < 2`,
  `|E_ω E_g Ψ(p(M_ω g, e)) - gaussianLeadSide p Φ e| ≤ ε + C · E_ω E_g p_0(M_ω g, e)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal ComplexConjugate ComplexOrder BoundedContinuousFunction

section Bounds

theorem abs_palmExpect_le {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ)
    (φ : (Fin N → ℂ) → ℝ) (hφ : Measurable φ) (M : ℝ) (hM : ∀ u, |φ u| ≤ M) :
    |palmExpect F c E φ| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h := abs_palmExpect_sub_le F c E φ (fun _ => 0) hφ measurable_const M hM
    (fun _ => by simp [hM0]) M (fun u => by simpa using hM u)
  have h0 : palmExpect F c E (fun _ => 0) = 0 := by simp [palmExpect]
  rwa [h0, sub_zero] at h

variable (p : Parameters) (k : ZMod p.n)

/-- At a Hermitian exterior the normalized sector average of `|g| ≤ M` is bounded by `M`.
Consumes `FreshEigenpairDensityContract`. -/
theorem abs_blockSectorAverage_le (hD : FreshEigenpairDensityContract)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ)
    (g : (ZMod p.n → ℝ) → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ q, |g q| ≤ M) :
    |(∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p k U ω e ℓ
        (fun v => g (blockReconMass p k ω e v))) / (blockNormalizer p k U ω e).toReal| ≤ M := by
  have hobs : (fun v => g (blockReconMass p k ω e v)) =
      fun v => reconMatrixObs p k ω e g (vecMulVec v (star v)) := by
    funext v; rw [reconMatrixObs_vecMulVec]
  rw [hobs, blockSector_ratio_eq_palmExpect p k hD (blockEquiv p k) U hU ω hω e
    (reconMatrixObs p k ω e g) (measurable_reconMatrixObs p k ω e g hg) M (fun X => hM _)]
  refine abs_palmExpect_le _ _ _ _ ?_ M (fun u => hM _)
  refine (measurable_reconMatrixObs p k ω e g hg).comp ?_
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [reindex_apply, submatrix_apply, vecMulVec_apply, Pi.star_apply]
  exact (measurable_pi_apply _).mul (continuous_star.measurable.comp (measurable_pi_apply _))

end Bounds

section Energy

/-- **Palm law versus the field, energy-wise**. See the module docstring. -/
theorem energy_palm_field_comparison (hD : FreshEigenpairDensityContract)
    (hGR : GaussianRatiosContract) (hReg : BlockRegularEventContract) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (κ T : ℝ) (hκ : 0 < κ) (m : ℕ) (ψ : C(Fin m → Set.Icc (-1 : ℝ) 1, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (Pω : Measure (BlockState p 0)),
      IsBlockSplitting p 0 model Pω →
    ∀ (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ),
      IsBlockFrame p 0 U → ∀ e ∈ bulkInterval κ,
    ∀ {S : Type} [Fintype S] [Nonempty S]
      (B : BlockState p 0 → S → Fin m → Matrix (BlockSite p 0) (BlockSite p 0) ℂ),
      (∀ ω s j, IsSandwichedOn (B ω s j) (clockForm p 0 ω e)) →
    ∀ (d : BlockState p 0 → S → (BlockSite p 0 → ℂ) → Fin m → ℝ),
      (∀ ω s, Measurable (d ω s)) →
    ∀ (g : (ZMod p.n → ℝ) → ℝ), Measurable g → ∀ Mg : ℝ, (∀ q, |g q| ≤ Mg) → ∀ δ : ℝ,
      (∀ ω v, |g (blockReconMass p 0 ω e v) - (Fintype.card S : ℝ)⁻¹ *
          ∑ s, ψ (ratioCube (B ω s) (clockForm p 0 ω e) (d ω s) v)| ≤ δ) →
      |(∫ ω, (∑ ℓ ∈ Finset.range p.W,
            blockSectorFiberReal p 0 U ω e ℓ (fun v => g (blockReconMass p 0 ω e v))) /
            (blockNormalizer p 0 U ω e).toReal ∂Pω) -
        ∫ ω, ∫ g', g (blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g'))
          ∂circularVectorLaw (BlockSite p 0) ∂Pω| ≤ 2 * δ + 2 * ε + 4 * Mg * ε := by
  obtain ⟨r₀, s₀, v₀, hfc, hrest⟩ := hReg b hb hb' κ T hκ
  obtain ⟨A, hA⟩ := hrest 1 one_pos
  obtain ⟨W₁, ω₀, hω₀, hω₀', hblock⟩ :=
    block_palm_field_comparison hD hGR b A r₀ s₀ v₀ hfc m ψ ε hε
  obtain ⟨W₂, hW₂⟩ := hA 1 one_pos
  set ε' := min ω₀ ε with hε'
  have hε'0 : 0 < ε' := lt_min hω₀ hε
  obtain ⟨W₃, hW₃⟩ := blockGammaCloseness_of hReg b hb hb' κ T hκ ε' hε'0
  refine ⟨max (max W₁ W₂) (max W₃ (⌈ε⁻¹⌉₊ + 1)), ?_⟩
  intro p hpb hW hnT model Pω hsplit U hU e he S _ _ B hB d hd g hg Mg hMg δ hδ
  have hW1 : W₁ ≤ p.W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ p.W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ p.W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW4 : ⌈ε⁻¹⌉₊ + 1 ≤ p.W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  obtain ⟨he1, he2, -⟩ := mem_bulkInterval_bounds hκ he
  have he' : |e| < 2 := abs_lt.mpr ⟨he1, he2⟩
  have hprob := isProbabilityMeasure_blockSplitting p model 0 hsplit
  set σ : BlockSite p 0 ≃ Fin (Fintype.card (BlockSite p 0)) := Fintype.equivFin _
  -- the good event
  set Good : Set (BlockState p 0) := {ω | ω.1.IsHermitian ∧
    IsBlockRegular p 0 σ A r₀ s₀ v₀ 1 e ω ∧
    ((((1 + ε' : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p 0 ω e) -
          freshGamma (blockDeformation p 0 σ ω e) p.c e).PosSemidef ∧
        (freshGamma (blockDeformation p 0 σ ω e) p.c e -
          ((1 - ε' : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p 0 ω e)).PosSemidef)}
  set Ag : BlockState p 0 → ℝ := fun ω => (∑ ℓ ∈ Finset.range p.W,
      blockSectorFiberReal p 0 U ω e ℓ (fun v => g (blockReconMass p 0 ω e v))) /
      (blockNormalizer p 0 U ω e).toReal
  set Gg : BlockState p 0 → ℝ := fun ω => ∫ g', g (blockReconMass p 0 ω e
      (blockFieldFactor p 0 ω e *ᵥ g')) ∂circularVectorLaw (BlockSite p 0)
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ (Classical.arbitrary _) 0)
  -- bounds on the good event
  have hgood : ∀ ω ∈ Good, |Ag ω - Gg ω| ≤ 2 * δ + 2 * ε := by
    intro ω hω
    obtain ⟨hH, hreg, hcl⟩ := hω
    have hdet := blockShifted_det_ne_zero p 0 ω hH he'
    have hM₀ : Matrix.reindex σ σ (blockFieldFactor p 0 ω e) *
        (Matrix.reindex σ σ (blockFieldFactor p 0 ω e))ᴴ =
        Matrix.reindex σ σ (blockMatchedGamma p 0 ω e) := by
      rw [← leadField_covariance p 0 e ω hdet, LeadProfile.reindex_mul', ← conjTranspose_reindex]
    have hΓ₀ : (Matrix.reindex σ σ (blockMatchedGamma p 0 ω e)).PosSemidef :=
      hM₀ ▸ posSemidef_self_mul_conjTranspose _
    have hcl' := loewner_widen hΓ₀ (min_le_left ω₀ ε) hcl
    exact hblock p hpb hW1 0 U hU ω hH e he' σ hreg.1 hcl' (B ω) (hB ω) (d ω) (hd ω) g hg Mg hMg
      δ (hδ ω)
  -- integrability
  have hAm : Measurable Ag := by
    have h := (measurable_blockSectorAverage p 0 U hU.1 g hg).comp
      ((measurable_const (a := e)).prodMk (measurable_id (α := BlockState p 0)))
    exact h
  have hGm : Measurable Gg := measurable_fieldAverage p 0 e g hg
  have hHerm := ae_blockSplit_isHermitian p model 0 hsplit
  have hAb : ∀ᵐ ω ∂Pω, |Ag ω| ≤ Mg := by
    filter_upwards [hHerm] with ω hω
    exact abs_blockSectorAverage_le p 0 hD U hU ω hω e g hg Mg hMg
  have hGb : ∀ ω, |Gg ω| ≤ Mg := by
    intro ω
    have := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (BlockSite p 0)) (C := Mg)
      (f := fun g' => g (blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g')))
      (Filter.Eventually.of_forall fun g' => by rw [Real.norm_eq_abs]; exact hMg _)
    simpa [Real.norm_eq_abs] using this
  have hAi : Integrable Ag Pω := (integrable_const Mg).mono' hAm.aestronglyMeasurable
    (by filter_upwards [hAb] with ω hω; rwa [Real.norm_eq_abs])
  have hGi : Integrable Gg Pω := (integrable_const Mg).mono' hGm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb ω)
  -- the bad event
  set Tm := toMeasurable Pω Goodᶜ
  have hTm : MeasurableSet Tm := measurableSet_toMeasurable _ _
  have hsubT : Goodᶜ ⊆ Tm := subset_toMeasurable _ _
  have hbad : Pω Goodᶜ ≤ ENNReal.ofReal (2 * ε) := by
    have hsub : Goodᶜ ⊆ {ω : BlockState p 0 | ¬ ω.1.IsHermitian} ∪
        ({ω | ¬ IsBlockRegular p 0 σ A r₀ s₀ v₀ 1 e ω} ∪
          {ω | ¬ ((((1 + ε' : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p 0 ω e) -
              freshGamma (blockDeformation p 0 σ ω e) p.c e).PosSemidef ∧
            (freshGamma (blockDeformation p 0 σ ω e) p.c e -
              ((1 - ε' : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p 0 ω e)).PosSemidef)}) := by
      intro ω hω
      by_contra hcon
      apply hω
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
      exact ⟨hcon.1, hcon.2.1, hcon.2.2⟩
    have h0 : Pω {ω : BlockState p 0 | ¬ ω.1.IsHermitian} = 0 := by
      rw [← ae_iff]; exact hHerm
    have h1 := hW₂ p hpb hW2 hnT model 0 Pω hsplit σ e he
    have h2 := hW₃ p hpb hW3 hnT model 0 Pω hsplit σ e he
    have hWinv : (p.W : ℝ) ^ (-(1 : ℝ)) ≤ ε := by
      have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
      rw [Real.rpow_neg_one]
      have hceil : ε⁻¹ ≤ (p.W : ℝ) := by
        have := Nat.le_ceil ε⁻¹
        have h2 : ((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ) ≤ p.W := by exact_mod_cast hW4
        push_cast at h2
        linarith
      rw [inv_le_comm₀ hWpos hε]
      exact hceil
    calc Pω Goodᶜ ≤ Pω {ω : BlockState p 0 | ¬ ω.1.IsHermitian} +
          (Pω {ω | ¬ IsBlockRegular p 0 σ A r₀ s₀ v₀ 1 e ω} +
            Pω {ω | ¬ ((((1 + ε' : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p 0 ω e) -
              freshGamma (blockDeformation p 0 σ ω e) p.c e).PosSemidef ∧
            (freshGamma (blockDeformation p 0 σ ω e) p.c e -
              ((1 - ε' : ℝ) : ℂ) • Matrix.reindex σ σ (blockMatchedGamma p 0 ω e)).PosSemidef)}) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add le_rfl (measure_union_le _ _)))
      _ ≤ 0 + (ENNReal.ofReal ε + ENNReal.ofReal ε) := by
          rw [h0]
          gcongr
          · exact h1.trans (ENNReal.ofReal_le_ofReal hWinv)
          · exact h2.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = ENNReal.ofReal (2 * ε) := by
          rw [zero_add, ← ENNReal.ofReal_add hε.le hε.le, two_mul]
  have hTreal : Pω.real Tm ≤ 2 * ε := by
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
  -- the pointwise a.e. bound
  have hpt : ∀ᵐ ω ∂Pω, ‖Ag ω - Gg ω‖ ≤ (2 * δ + 2 * ε) + 2 * Mg * Tm.indicator 1 ω := by
    filter_upwards [hAb] with ω hω
    rw [Real.norm_eq_abs]
    by_cases hg : ω ∈ Good
    · have := hgood ω hg
      have : 0 ≤ 2 * Mg * Tm.indicator 1 ω :=
        mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
    · have hT : ω ∈ Tm := hsubT hg
      rw [Set.indicator_of_mem hT, Pi.one_apply, mul_one]
      have h1 := abs_sub (Ag ω) (Gg ω)
      have h2 := hGb ω
      linarith
  have hint_bd : Integrable (fun ω => (2 * δ + 2 * ε) + 2 * Mg * Tm.indicator 1 ω) Pω :=
    (integrable_const _).add ((integrable_indicator_iff hTm).mpr (integrable_const 1).integrableOn
      |>.const_mul _)
  have hmain := norm_integral_le_of_norm_le hint_bd hpt
  rw [integral_add (integrable_const _) ((integrable_indicator_iff hTm).mpr
      (integrable_const 1).integrableOn |>.const_mul _), integral_const_mul,
    integral_indicator_one hTm, integral_const, probReal_univ, one_smul] at hmain
  rw [← integral_sub hAi hGi]
  rw [Real.norm_eq_abs] at hmain
  have : 2 * Mg * Pω.real Tm ≤ 2 * Mg * (2 * ε) := mul_le_mul_of_nonneg_left hTreal (by positivity)
  linarith

end Energy

section Deletion

theorem measurable_leadExterior (p : Parameters) (k : ZMod p.n) :
    Measurable (leadExterior p k) := by
  have hr : 1 ≤ p.n - 3 := by have := p.n_ge_four; omega
  rw [LeadFieldLaw.leadExterior_eq_ofPath]
  exact (LeadFieldLaw.measurable_leadExteriorOfPath p k).comp
    ((LeadFieldLaw.mp_pathAt p.W p.b hr).measurable.prodMap measurable_id)

theorem measurable_gaussianLeadIntegrand (p : Parameters) (Φ : MassProfile →ᵇ ℝ) (e : ℝ) :
    Measurable fun y : (GrowthPath p.W × LayerSample p.W .common) × (Fin 1 × Fin p.W → ℂ) =>
      (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n, Φ (leadProfile p.b e p.n p.W y.1.1
        (commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1.1) (y.1.2, y.2)) J) := by
  have hq : Measurable fun y : (GrowthPath p.W × LayerSample p.W .common) ×
      (Fin 1 × Fin p.W → ℂ) =>
      (e, y.1.1, commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1.1) (y.1.2, y.2)) := by
    refine measurable_const.prodMk ((measurable_fst.comp measurable_fst).prodMk ?_)
    have hy : Measurable fun y : (GrowthPath p.W × LayerSample p.W .common) ×
        (Fin 1 × Fin p.W → ℂ) => (e, y) := measurable_const.prodMk measurable_id
    have h := (LeadProfileRegularity.measurable_commonPortProbe_eJoint p.b p.W (p.n - 3)).comp hy
    exact h
  refine measurable_const.mul (Finset.measurable_sum _ fun J _ => ?_)
  have h := (measurable_massProfile_bcf Φ).comp
    ((LeadProfileRegularity.measurable_leadProfile_eJoint p.b p.n p.W J).comp hq)
  exact h

/-- **Field identification and removal of block `0`, energy-wise**, integrated over the
exterior prior. Assumes no contract (the field law is
`leadFieldIdentification_holds`). -/
theorem energy_deletion (Φ : MassProfile →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Parameters) (model : p.GaussianRingModel)
      (Pω : Measure (BlockState p 0)), IsBlockSplitting p 0 model Pω → ∀ e : ℝ, |e| < 2 →
      |(∫ ω, ∫ g', leadReconObservable p Φ 0 ω e (blockFieldFactor p 0 ω e *ᵥ g')
          ∂circularVectorLaw (BlockSite p 0) ∂Pω) - gaussianLeadSide p Φ e| ≤
        ε + C * ∫ ω, ∫ g', blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g') 0
          ∂circularVectorLaw (BlockSite p 0) ∂Pω := by
  obtain ⟨C, hC, hpt⟩ := leadRecon_deletion_pointwise Φ ε hε
  refine ⟨C, hC, ?_⟩
  intro p model Pω hsplit e he
  set μ := (growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common) with hμ
  have hgp : IsProbabilityMeasure (growthPathLaw p.W p.b) := by
    unfold growthPathLaw; infer_instance
  have hlp : IsProbabilityMeasure (layerLaw p.W p.b .common) :=
    BlockBand.Layers.rng_isProbabilityMeasure_layerLaw_common p.W p.b
  have hμp : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hlaw : Pω = μ.map (leadExterior p 0) :=
    leadFieldIdentification_holds.law p model 0 Pω hsplit
  have hLm := measurable_leadExterior p 0
  set G₁ : (ZMod p.n → ℝ) → ℝ := fun q => leadProfileRotationAverage p Φ (massVectorProfile p q)
  have hG₁ : Measurable G₁ :=
    (measurable_leadProfileRotationAverage p Φ).comp (measurable_massVectorProfile p)
  have hF₁ := measurable_fieldAverage p 0 e G₁ hG₁
  have hF₀ := measurable_fieldAverage p 0 e (fun q => q 0) (measurable_pi_apply 0)
  have hdef : ∀ ω v, leadReconObservable p Φ 0 ω e v = G₁ (blockReconMass p 0 ω e v) :=
    fun ω v => rfl
  simp_rw [hdef]
  rw [hlaw, integral_map hLm.aemeasurable hF₁.aestronglyMeasurable,
    integral_map hLm.aemeasurable hF₀.aestronglyMeasurable]
  -- the Gaussian side as an iterated integral
  set H : (GrowthPath p.W × LayerSample p.W .common) × (Fin 1 × Fin p.W → ℂ) → ℝ := fun y =>
    (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n, Φ (leadProfile p.b e p.n p.W y.1.1
      (commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1.1) (y.1.2, y.2)) J)
  have hHm : Measurable H := measurable_gaussianLeadIntegrand p Φ e
  have hHb : ∀ y, |H y| ≤ ‖Φ‖ := by
    intro y
    have := abs_integral_avg_le (Measure.dirac y) p.n Φ (fun y J => leadProfile p.b e p.n p.W y.1.1
      (commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1.1) (y.1.2, y.2)) J)
    rwa [integral_dirac' _ _ hHm.stronglyMeasurable] at this
  have hHi : Integrable H (μ.prod (circularVectorLaw (Fin 1 × Fin p.W))) :=
    (integrable_const ‖Φ‖).mono' hHm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hHb y)
  have hside : gaussianLeadSide p Φ e = ∫ x, ∫ g, H (x, g) ∂circularVectorLaw (Fin 1 × Fin p.W) ∂μ := by
    unfold gaussianLeadSide leadGaussianLaw
    exact integral_prod H hHi
  rw [hside]
  set a : GrowthPath p.W × LayerSample p.W .common → ℝ := fun x =>
    ∫ g', G₁ (blockReconMass p 0 (leadExterior p 0 x) e
      (blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g')) ∂circularVectorLaw (BlockSite p 0)
  set bH : GrowthPath p.W × LayerSample p.W .common → ℝ := fun x =>
    ∫ g, H (x, g) ∂circularVectorLaw (Fin 1 × Fin p.W)
  set c : GrowthPath p.W × LayerSample p.W .common → ℝ := fun x =>
    ∫ g', blockReconMass p 0 (leadExterior p 0 x) e
      (blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g') 0 ∂circularVectorLaw (BlockSite p 0)
  have ham : Measurable a := hF₁.comp hLm
  have hbm : Measurable bH := (hHm.stronglyMeasurable.integral_prod_right'
    (ν := circularVectorLaw (Fin 1 × Fin p.W))).measurable
  have hcm : Measurable c := hF₀.comp hLm
  have hG₁b : ∀ q, |G₁ q| ≤ ‖Φ‖ := fun q => abs_leadProfileRotationAverage_le p Φ _
  have hr0 : ∀ ω v, 0 ≤ blockReconMass p 0 ω e v 0 ∧ blockReconMass p 0 ω e v 0 ≤ 1 :=
    fun ω v => blockReconMass_self_le_one p 0 ω e v
  have hint_avg : ∀ (f : (BlockSite p 0 → ℂ) → ℝ), Measurable f → ∀ M, (∀ v, |f v| ≤ M) →
      Integrable f (circularVectorLaw (BlockSite p 0)) := fun f hf M hM =>
    (integrable_const M).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hM v)
  have habs_int : ∀ (f : (BlockSite p 0 → ℂ) → ℝ) (M : ℝ), (∀ v, |f v| ≤ M) →
      |∫ v, f v ∂circularVectorLaw (BlockSite p 0)| ≤ M := fun f M hM => by
    have := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (BlockSite p 0)) (C := M)
      (f := f) (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hM v)
    simpa [Real.norm_eq_abs] using this
  have hmv : ∀ ω : BlockState p 0, Measurable fun g' : BlockSite p 0 → ℂ =>
      blockFieldFactor p 0 ω e *ᵥ g' := fun ω =>
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hrm := measurable_blockReconMass p 0
  have hne : Nonempty (BlockSite p 0) := ⟨⟨(0, ⟨0, p.W_pos⟩), rfl⟩⟩
  -- the inner bound, for a.e. lead sample
  have hinner : ∀ᵐ x ∂μ, |a x - bH x| ≤ ε + C * c x := by
    filter_upwards [leadFieldIdentification_holds.regular_ae p 0 e (abs_lt.mp he).1
      (abs_lt.mp he).2] with x hx
    set ω := leadExterior p 0 x
    have hb' : bH x = ∫ g', H (x, blockPortVector p 0 g') ∂circularVectorLaw (BlockSite p 0) :=
      (integral_circular_comp_equiv (blockPortEquiv p 0).symm (fun g => H (x, g))
        (hHm.comp (measurable_const.prodMk measurable_id))).symm
    rw [hb']
    have hm1 : Measurable fun g' => G₁ (blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g')) :=
      hG₁.comp ((hrm ω e).comp (hmv ω))
    have hm2 : Measurable fun g' : BlockSite p 0 → ℂ => H (x, blockPortVector p 0 g') :=
      hHm.comp (measurable_const.prodMk (measurable_pi_iff.mpr fun i => measurable_pi_apply _))
    have hm3 : Measurable fun g' => blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g') 0 :=
      (measurable_pi_apply 0).comp ((hrm ω e).comp (hmv ω))
    rw [← integral_sub (hint_avg _ hm1 _ fun v => hG₁b _) (hint_avg _ hm2 _ fun v => hHb _)]
    have hcx : ε + C * c x = ∫ g', (ε + C * blockReconMass p 0 ω e
        (blockFieldFactor p 0 ω e *ᵥ g') 0) ∂circularVectorLaw (BlockSite p 0) := by
      rw [integral_add (integrable_const _) ((hint_avg _ hm3 1 fun v => by
        rw [abs_of_nonneg (hr0 _ _).1]; exact (hr0 _ _).2).const_mul _), integral_const,
        probReal_univ, one_smul, integral_const_mul]
    rw [hcx]
    have := norm_integral_le_of_norm_le (((integrable_const ε).add ((hint_avg _ hm3 1 fun v => by
        rw [abs_of_nonneg (hr0 _ _).1]; exact (hr0 _ _).2).const_mul C)))
      (f := fun g' => G₁ (blockReconMass p 0 ω e (blockFieldFactor p 0 ω e *ᵥ g')) -
        H (x, blockPortVector p 0 g'))
      (by
        filter_upwards [ProjectiveHaar.circularVectorLaw_ae_ne_zero (BlockSite p 0)] with g' hg'
        rw [Real.norm_eq_abs]
        exact hpt p e he x hx g' hg')
    rwa [Real.norm_eq_abs] at this
  -- integrate
  have hai : Integrable a μ := (integrable_const ‖Φ‖).mono' ham.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact habs_int _ _ fun v => hG₁b _)
  have hbi : Integrable bH μ := (integrable_const ‖Φ‖).mono' hbm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (Fin 1 × Fin p.W))
        (C := ‖Φ‖) (f := fun g => H (x, g))
        (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hHb _)
      simpa [Real.norm_eq_abs] using this)
  have hci : Integrable c μ := (integrable_const 1).mono' hcm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact habs_int _ _ fun v => by rw [abs_of_nonneg (hr0 _ _).1]; exact (hr0 _ _).2)
  rw [← integral_sub hai hbi]
  have := norm_integral_le_of_norm_le ((integrable_const ε).add (hci.const_mul C))
    (by filter_upwards [hinner] with x hx; rw [Real.norm_eq_abs]; exact hx)
  have heq : ∫ x, (((fun _ => ε) + fun x => C * c x) :
      GrowthPath p.W × LayerSample p.W .common → ℝ) x ∂μ = ε + C * ∫ x, c x ∂μ := by
    show ∫ x, (ε + C * c x) ∂μ = _
    rw [integral_add (integrable_const _) (hci.const_mul C), integral_const, probReal_univ,
      one_smul, integral_const_mul]
  rw [heq, Real.norm_eq_abs] at this
  exact this

end Deletion

end LeadGaussian

end BlockBand.Endpoints.Normalization
