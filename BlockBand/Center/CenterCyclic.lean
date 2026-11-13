module

public import BlockBand.Center.CenterCyclicAlgebra
public import BlockBand.QUE.Fourier.PhysicalWeightedMass

/-!
# Cyclic invariance of the center second moment (`PcCenterCyclic`)

Law: the exact pair law `extendedPairMeasure p α g X.P X.Hm` of the witness extension
`ctrExtension p model g` (density `(n/2)(p_g + p_{g+1})` against the physical law).

Proof, for edges `g, g'` and `τ = ccyShift g g'` (block shift by `g - g'`):
* the shifted extension `ccyExt` (same `Ω, P`, `H' = τH`) still has the exact physical law
  (`GaussianRingModel.map_cyclicMatrix`), and carries the edge-`g'` splitting with
  `G' = G ∘ (e × e)`: `GUE` is invariant under reindexing (`ccy_gue_reindex`, characteristic
  functions) and `H' - G' = τ(H - G)` (`ccy_isCenterSplitting`);
* by `pc_pair_integral_transfer` the edge-`g'` pair integral on `ccyExt` is the one on
  `ctrExtension p model g'`;
* on `ccyExt` the pair weight at `g'` equals the weight at `g` almost surely
  (`physical_blockMass_cyclic` on the simple-spectrum locus), the ordered eigenvalue is invariant
  (`physical_eigenvalue_cyclic`) and the center is equivariant (`ccy_dysonCenter`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open scoped ENNReal NNReal

variable {p : Parameters}

/-!
## 1. `GUE` is invariant under reindexing
-/

theorem ccy_measurable_submatrix {ι ι' : Type*} (e : ι' ≃ ι) :
    Measurable (fun M : Matrix ι ι ℂ => M.submatrix e e) :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b =>
    BlockBand.Layers.pg_entry measurable_id (e a) (e b)

/-- `GUE_ι(t)` reindexed by a bijection `ι' ≃ ι` is `GUE_{ι'}(t)`. -/
theorem ccy_gue_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (t : ℝ≥0) :
    (gueMeasure ι t).map (fun M : Matrix ι ι ℂ => M.submatrix e e) = gueMeasure ι' t := by
  apply BlockBand.Layers.rsl_measure_ext
  intro α β
  rw [integral_map (ccy_measurable_submatrix e).aemeasurable
    (BlockBand.Layers.rsl_measurable_expTest α β).aestronglyMeasurable]
  have h : ∀ M : Matrix ι ι ℂ, BlockBand.Layers.rslTest α β (M.submatrix e e) =
      BlockBand.Layers.rslTest (fun u v => α (e.symm u) (e.symm v))
        (fun u v => β (e.symm u) (e.symm v)) M := by
    intro M
    have := BlockBand.Layers.rsl_test_submatrix e.symm e.symm α β M
    simpa only [Equiv.symm_symm] using this
  simp_rw [h]
  rw [BlockBand.Layers.rsl_charFun_gue, BlockBand.Layers.rsl_charFun_gue,
    BlockBand.Layers.rsl_Q_reindex e.symm α β]

/-!
## 2. The witness extension and its shift
-/

/-- The witness extension of `pairCenterFamily0` carries the edge-`g` splitting with
`G = Prod.snd` (as in `pairCenterFamily0_isDyson`). -/
theorem ccy_ctr_isCenterSplitting (model : p.GaussianRingModel) (g : ZMod p.n) :
    IsCenterSplitting (ctrExtension p model g) Prod.snd := by
  have hPω := ctr_splitLaw_isProb p model g
  refine ⟨measurable_snd, ⟨measurable_snd.aemeasurable, ?_⟩, ?_⟩
  · change ((ctrSplitLaw p g).prod (gueMeasure (PairSite p g) (pairTime p (splitS p)))).map
      Prod.snd = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  · have hfun : (fun ω : (ctrExtension p model g).Ω =>
        (ctrExtension p model g).Hm ω - embedPair p g ω.2) = fun ω => assemble p g ω.1 0 := by
      funext ω
      exact ctr_assemble_sub_embed g ω.1 ω.2
    rw [hfun]
    exact indepFun_prod (μ := ctrSplitLaw p g)
      (ν := gueMeasure (PairSite p g) (pairTime p (splitS p)))
      (X := fun ω : SplitState p g => assemble p g ω 0) (Y := id)
      (BlockBand.Layers.rsl_measurable_L g) measurable_id

theorem ccy_measurable_shift (g g' : ZMod p.n) : Measurable (ccyShift (p := p) g g') :=
  p.measurable_siteReindexMatrix _

theorem ccy_measurable_pairShift (g g' : ZMod p.n) : Measurable (ccyPairShift (p := p) g g') :=
  ccy_measurable_submatrix (ccyPairEquiv g g')

/-- The extension of edge `g` with the shifted matrix `τH` (same sample space and law). -/
def ccyExt (model : p.GaussianRingModel) (g g' : ZMod p.n) : PairExtension p model where
  Ω := (ctrExtension p model g).Ω
  P := (ctrExtension p model g).P
  Hm := fun ω => ccyShift g g' ((ctrExtension p model g).Hm ω)
  measurable_Hm := (ccy_measurable_shift g g').comp (ctrExtension p model g).measurable_Hm
  map_eq := by
    change (ctrExtension p model g).P.map (ccyShift g g' ∘ (ctrExtension p model g).Hm) = _
    rw [← Measure.map_map (ccy_measurable_shift g g') (ctrExtension p model g).measurable_Hm,
      (ctrExtension p model g).map_eq]
    exact model.map_cyclicMatrix (g - g')

theorem ccy_ext_residual (model : p.GaussianRingModel) (g g' : ZMod p.n)
    (ω : (ctrExtension p model g).Ω) :
    (ccyExt model g g').Hm ω - embedPair p g' (ccyPairShift g g' ω.2) =
      ccyShift g g' ((ctrExtension p model g).Hm ω - embedPair p g ω.2) := by
  rw [ccy_shift_sub, ccy_shift_embed]
  rfl

/-- The shifted extension carries the edge-`g'` splitting with `G' = G ∘ (e × e)`. -/
theorem ccy_isCenterSplitting (model : p.GaussianRingModel) (g g' : ZMod p.n) :
    IsCenterSplitting (ccyExt model g g') (fun ω => ccyPairShift g g' ω.2) := by
  obtain ⟨-, hlaw, hind⟩ := ccy_ctr_isCenterSplitting model g
  refine ⟨(ccy_measurable_pairShift g g').comp measurable_snd,
    ⟨((ccy_measurable_pairShift g g').comp measurable_snd).aemeasurable, ?_⟩, ?_⟩
  · have hsh : HasLaw (ccyPairShift g g') (gueMeasure (PairSite p g') (pairTime p (splitS p)))
        (gueMeasure (PairSite p g) (pairTime p (splitS p))) :=
      ⟨(ccy_measurable_pairShift g g').aemeasurable, ccy_gue_reindex (ccyPairEquiv g g') _⟩
    exact (hsh.comp hlaw).map_eq
  · have hfun : (fun ω : (ccyExt model g g').Ω =>
        (ccyExt model g g').Hm ω - embedPair p g' (ccyPairShift g g' ω.2)) =
        ccyShift g g' ∘ fun ω : (ctrExtension p model g).Ω =>
          (ctrExtension p model g).Hm ω - embedPair p g ω.2 :=
      funext (ccy_ext_residual model g g')
    rw [hfun]
    exact hind.comp (ccy_measurable_shift g g') (ccy_measurable_pairShift g g')

/-!
## 3. Transport of the pair law and of the center
-/

theorem ccy_ae_good (model : p.GaussianRingModel) (g : ZMod p.n) :
    ∀ᵐ ω ∂(ctrExtension p model g).P, ((ctrExtension p model g).Hm ω).IsHermitian ∧
      ((ctrExtension p model g).Hm ω).charpoly.Separable := by
  have h : ∀ᵐ H ∂(ctrExtension p model g).P.map (ctrExtension p model g).Hm,
      H.IsHermitian ∧ H.charpoly.Separable := by
    rw [(ctrExtension p model g).map_eq]
    filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H h1 h2
    exact ⟨h1, h2⟩
  exact ae_of_ae_map (ctrExtension p model g).measurable_Hm.aemeasurable h

/-- The pair weight at `g'` of `τH` is the pair weight at `g` of `H` (simple spectrum). -/
theorem ccy_pairWeight (α : Fin p.N) (g g' : ZMod p.n) (H : p.SiteMatrix) (hH : H.IsHermitian)
    (hsep : H.charpoly.Separable) :
    physicalPairWeight p α g' (ccyShift g g' H) = physicalPairWeight p α g H := by
  apply Subtype.ext
  change (p.n : ℝ) / 2 * (physicalOrderedBlockMass p (ccyShift g g' H) α g' +
      physicalOrderedBlockMass p (ccyShift g g' H) α (g' + 1)) =
    (p.n : ℝ) / 2 * (physicalOrderedBlockMass p H α g + physicalOrderedBlockMass p H α (g + 1))
  have h1 : g' + (g - g') = g := by abel
  have h2 : g' + 1 + (g - g') = g + 1 := by abel
  rw [physical_blockMass_cyclic p H hH hsep α (g - g') g',
    physical_blockMass_cyclic p H hH hsep α (g - g') (g' + 1), h1, h2]

/-- The edge-`g'` pair law of the shifted extension is the edge-`g` pair law of the witness. -/
theorem ccy_pairMeasure_eq (model : p.GaussianRingModel) (α : Fin p.N) (g g' : ZMod p.n) :
    extendedPairMeasure p α g' (ccyExt model g g').P (ccyExt model g g').Hm =
      extendedPairMeasure p α g (ctrExtension p model g).P (ctrExtension p model g).Hm := by
  unfold extendedPairMeasure
  apply withDensity_congr_ae
  filter_upwards [ccy_ae_good model g] with ω hω
  change ((physicalPairWeight p α g' (ccyShift g g' ((ctrExtension p model g).Hm ω)) : ℝ≥0) :
    ℝ≥0∞) = _
  rw [ccy_pairWeight α g g' _ hω.1 hω.2]

/-- The squared center at edge `h`, as a Borel function of `(H - G_h, H)` (restricted to
Hermitian residuals, where `centerDomain_measurable` gives measurability). -/
def ccyObs (α : Fin p.N) (h : ZMod p.n) (z : p.SiteMatrix × p.SiteMatrix) : ℝ :=
  ({x : p.SiteMatrix × ℝ | x.1.IsHermitian}.indicator (fun x => dysonCenter p h cst0 α x.1 x.2)
    (z.1, physicalOrderedEigenvalue p z.2 α)) ^ 2

theorem ccy_measurable_obs (α : Fin p.N) (h : ZMod p.n) : Measurable (ccyObs (p := p) α h) := by
  unfold ccyObs
  exact ((centerDomain_measurable cst0 p α h).1.comp
    (measurable_fst.prodMk ((measurable_physicalOrderedEigenvalue p α).comp measurable_snd))).pow_const 2

theorem ccy_obs_of_isHermitian (α : Fin p.N) (h : ZMod p.n) {R H : p.SiteMatrix}
    (hR : R.IsHermitian) :
    ccyObs α h (R, H) = dysonCenter p h cst0 α R (physicalOrderedEigenvalue p H α) ^ 2 := by
  unfold ccyObs
  rw [Set.indicator_of_mem (show (R, physicalOrderedEigenvalue p H α) ∈
    {x : p.SiteMatrix × ℝ | x.1.IsHermitian} from hR)]

/-- The pair-law second moment of the witness center at edge `h` is the integral of `ccyObs`. -/
theorem ccy_value_eq_obs (model : p.GaussianRingModel) (α : Fin p.N) (h : ZMod p.n) :
    (∫ ω, (pairCenterFamily0 p model α h).center ω ^ 2 ∂extendedPairMeasure p α h
        (pairCenterFamily0 p model α h).X.P (pairCenterFamily0 p model α h).X.Hm) =
      ∫ ω, ccyObs α h ((ctrExtension p model h).Hm ω - embedPair p h ω.2,
          (ctrExtension p model h).Hm ω)
        ∂extendedPairMeasure p α h (ctrExtension p model h).P (ctrExtension p model h).Hm := by
  refine integral_congr_ae ?_
  filter_upwards [ctr_ae_residual_isHermitian model α h] with ω hω
  rw [ccy_obs_of_isHermitian α h hω]
  rfl

/-- **One cyclic step**: the second moments at the edges `g` and `g'` coincide. -/
theorem ccy_value_eq (model : p.GaussianRingModel) (α : Fin p.N) (g g' : ZMod p.n) :
    (∫ ω, (pairCenterFamily0 p model α g).center ω ^ 2 ∂extendedPairMeasure p α g
        (pairCenterFamily0 p model α g).X.P (pairCenterFamily0 p model α g).X.Hm) =
      ∫ ω, (pairCenterFamily0 p model α g').center ω ^ 2 ∂extendedPairMeasure p α g'
        (pairCenterFamily0 p model α g').X.P (pairCenterFamily0 p model α g').X.Hm := by
  change (∫ ω : (ctrExtension p model g).Ω, ctrCenter p model α g ω ^ 2 ∂extendedPairMeasure p α g
    (ctrExtension p model g).P (ctrExtension p model g).Hm) = _
  rw [ccy_value_eq_obs model α g', ← pc_pair_integral_transfer α g' (ccyExt model g g')
    (ccy_isCenterSplitting model g g') (ccyObs α g') (ccy_measurable_obs α g'),
    ccy_pairMeasure_eq model α g g']
  refine integral_congr_ae ?_
  have hgood : ∀ᵐ ω ∂extendedPairMeasure p α g (ctrExtension p model g).P
      (ctrExtension p model g).Hm, ((ctrExtension p model g).Hm ω).IsHermitian := by
    unfold extendedPairMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le
      ((ccy_ae_good model g).mono fun ω hω => hω.1)
  filter_upwards [ctr_ae_residual_isHermitian model α g, hgood] with ω hR hH
  change dysonCenter p g cst0 α ((ctrExtension p model g).Hm ω - embedPair p g ω.2)
      (physicalOrderedEigenvalue p ((ctrExtension p model g).Hm ω) α) ^ 2 =
    ccyObs α g' ((ccyExt model g g').Hm ω - embedPair p g' (ccyPairShift g g' ω.2),
      (ccyExt model g g').Hm ω)
  rw [ccy_ext_residual, ccy_obs_of_isHermitian α g'
    ((ccy_shift_isHermitian_iff g g' _).mpr hR), ccy_dysonCenter]
  change _ = dysonCenter p g cst0 α _
    (physicalOrderedEigenvalue p (p.siteReindexMatrix (p.cyclicSiteEquiv (g - g'))
      ((ctrExtension p model g).Hm ω)) α) ^ 2
  rw [physical_eigenvalue_cyclic p _ hH α (g - g')]

/-- **`PcCenterCyclic`** (cyclic invariance of the center, used in
the energy primitive identity and the stationarity proposition): for every parameter set, model and
rank, the pair-law second moment of the center of `pairCenterFamily0` does not depend on the
pair. -/
theorem pcCenterCyclic_holds : PcCenterCyclic :=
  fun _ model α g g' => ccy_value_eq model α g g'

end BlockBand.Center
