module

public import BlockBand.Center.CenterMeasurable
public import BlockBand.Layers.ResidualSplitLaw
public import BlockBand.QUE.Assembly.PairResidual

/-!
# The physical center family

For every `(p, model, α, i)` the extension is `Ω = SplitState × PairMatrix` with
`P = Pω ⊗ GUE_{2W}(s/(2W))`, `s = splitS p = min(c, b)`, where `Pω` is the explicit residual
splitting law `(rpLaw W b s ⊗ pathLaw W (n-2) b).map rpSplitAssemble` (`rsl_isPairSplitting`),
`Hm = assemble`, `G = Prod.snd`, and the center is
`ω ↦ dysonCenter p i cst0 α (Hm ω - embedPair G ω) (λ_α(Hm ω))`.

* `pairCenterFamily0 : PairCenterFamily` (fields `aesm` from `centerDomain_measurable` and the
  almost-sure Hermitian property; `sq_integrable` from `|j_e| ≤ 1`);
* `pairCenterFamily0_isDyson : IsDysonCenterFamily cst0 pairCenterFamily0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.Model.Construction BlockBand.QUE.PairResidual
open scoped ENNReal NNReal ComplexConjugate

section Family

variable (p : Parameters)

theorem ctr_splitS_le_c : splitS p ≤ 2 * (1 - 2 * p.b) := by
  have h1 : splitS p ≤ 1 - 2 * p.b := min_le_left _ _
  have h2 : 0 < 1 - 2 * p.b := p.c_pos
  linarith

theorem ctr_splitS_le_b : splitS p ≤ 2 * p.b := by
  have h1 : splitS p ≤ p.b := min_le_right _ _
  linarith [p.b_pos]

/-- The explicit pair-splitting law `(rpLaw W b s ⊗ pathLaw W (n-2) b).map rpSplitAssemble` at
`s = splitS p`. -/
def ctrSplitLaw (i : ZMod p.n) : Measure (SplitState p i) :=
  ((BlockBand.Layers.rpLaw p.W p.b (splitS p)).prod (pathLaw p.W (p.n - 2) p.b)).map
    (BlockBand.Layers.rpSplitAssemble i)

theorem ctr_splitLaw_isPairSplitting (model : p.GaussianRingModel) (i : ZMod p.n) :
    IsPairSplitting p i model (splitS p) (ctrSplitLaw p i) :=
  BlockBand.Layers.rsl_isPairSplitting i model ctr_splitS_pos.le (ctr_splitS_le_c p)
    (ctr_splitS_le_b p)

theorem ctr_splitLaw_isProb (model : p.GaussianRingModel) (i : ZMod p.n) :
    IsProbabilityMeasure (ctrSplitLaw p i) :=
  BlockBand.Layers.rsl_isProb_of_splitting i (ctr_splitLaw_isPairSplitting p model i)

/-- The extension `(SplitState × PairMatrix, Pω ⊗ GUE, assemble)` carrying the edge-`i`
splitting. -/
def ctrExtension (model : p.GaussianRingModel) (i : ZMod p.n) : PairExtension p model where
  Ω := SplitState p i × PairMatrix p i
  P := (ctrSplitLaw p i).prod (gueMeasure (PairSite p i) (pairTime p (splitS p)))
  Hm := fun ω => assemble p i ω.1 ω.2
  measurable_Hm := BlockBand.Layers.rsl_measurable_assemble i
  map_eq := ctr_splitLaw_isPairSplitting p model i

/-- The center `ω ↦ j_e(λ_α(H))` built from `H - G_e` (the Dyson center). -/
def ctrCenter (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n) :
    (ctrExtension p model i).Ω → ℝ := fun ω =>
  dysonCenter p i cst0 α ((ctrExtension p model i).Hm ω - embedPair p i ω.2)
    (physicalOrderedEigenvalue p ((ctrExtension p model i).Hm ω) α)

variable {p}

theorem ctr_assemble_zero_left (i : ZMod p.n) (G : PairMatrix p i) :
    assemble p i 0 G = embedPair p i G := by
  ext x y
  unfold assemble embedPair
  split_ifs <;> simp

theorem ctr_assemble_sub_embed (i : ZMod p.n) (ω : SplitState p i) (G : PairMatrix p i) :
    assemble p i ω G - embedPair p i G = assemble p i ω 0 := by
  rw [BlockBand.Layers.rsl_assemble_add, ctr_assemble_zero_left, add_sub_cancel_right]

theorem ctr_embedPair_conjTranspose (i : ZMod p.n) (G : PairMatrix p i) :
    (embedPair p i G)ᴴ = embedPair p i Gᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply]
  unfold embedPair
  split_ifs <;> simp

theorem ctr_measurable_embedPair (i : ZMod p.n) : Measurable (embedPair p i) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold embedPair
  split_ifs
  · exact BlockBand.Layers.pg_entry measurable_id _ _
  · exact measurable_const
  · exact measurable_const

theorem ctr_ae_gue_isHermitian {ι : Type} [Fintype ι] (t : ℝ≥0) :
    ∀ᵐ A ∂gueMeasure ι t, A.IsHermitian := by
  have hS : MeasurableSet {A : Matrix ι ι ℂ | A.IsHermitian} :=
    (isClosed_eq (by fun_prop : Continuous (fun A : Matrix ι ι ℂ => Aᴴ)) continuous_id).measurableSet
  unfold gueMeasure
  rw [ae_map_iff (BlockBand.Layers.rsl_measurable_gueSample t).aemeasurable hS]
  refine Filter.Eventually.of_forall fun X => ?_
  ext a b
  simp only [Matrix.conjTranspose_apply, gueSample, Matrix.of_apply]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, map_add, Complex.conj_conj]
  ring

/-- Almost surely (under the pair law) the residual `H - G_e` is Hermitian. -/
theorem ctr_ae_residual_isHermitian (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n) :
    ∀ᵐ ω ∂extendedPairMeasure p α i (ctrExtension p model i).P (ctrExtension p model i).Hm,
      ((ctrExtension p model i).Hm ω - embedPair p i ω.2).IsHermitian := by
  have := ctr_splitLaw_isProb p model i
  have hH := ae_extendedPairMeasure p model α i (ctrExtension p model i) model.isPhysical.1
  have hG0 : ∀ᵐ ω ∂(ctrExtension p model i).P, (ω.2 : PairMatrix p i).IsHermitian :=
    (Measure.quasiMeasurePreserving_snd).ae (ctr_ae_gue_isHermitian _)
  have hG : ∀ᵐ ω ∂extendedPairMeasure p α i (ctrExtension p model i).P
      (ctrExtension p model i).Hm, (ω.2 : PairMatrix p i).IsHermitian := by
    unfold extendedPairMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le hG0
  filter_upwards [hH, hG] with ω h1 h2
  change (_ - _)ᴴ = _
  rw [Matrix.conjTranspose_sub, h1.eq, ctr_embedPair_conjTranspose, h2.eq]

theorem ctr_measurable_residualArg (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n) :
    Measurable (fun ω : (ctrExtension p model i).Ω =>
      ((ctrExtension p model i).Hm ω - embedPair p i ω.2,
        physicalOrderedEigenvalue p ((ctrExtension p model i).Hm ω) α)) := by
  have hA := (ctrExtension p model i).measurable_Hm
  have hB : Measurable (fun ω : (ctrExtension p model i).Ω => embedPair p i ω.2) :=
    (ctr_measurable_embedPair i).comp measurable_snd
  have hsub : Measurable (fun ω : (ctrExtension p model i).Ω =>
      (ctrExtension p model i).Hm ω - embedPair p i ω.2) :=
    measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      (BlockBand.Layers.pg_entry hA x y).sub (BlockBand.Layers.pg_entry hB x y)
  exact hsub.prodMk ((measurable_physicalOrderedEigenvalue p α).comp hA)

theorem ctr_center_aesm (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n) :
    AEStronglyMeasurable (ctrCenter p model α i)
      (extendedPairMeasure p α i (ctrExtension p model i).P (ctrExtension p model i).Hm) := by
  have hm := (centerDomain_measurable cst0 p α i).1
  have hcomp := Measurable.comp
    (g := {x : p.SiteMatrix × ℝ | x.1.IsHermitian}.indicator
      (fun x => dysonCenter p i cst0 α x.1 x.2))
    (f := fun ω : (ctrExtension p model i).Ω =>
      ((ctrExtension p model i).Hm ω - embedPair p i ω.2,
        physicalOrderedEigenvalue p ((ctrExtension p model i).Hm ω) α))
    hm (ctr_measurable_residualArg model α i)
  refine hcomp.aestronglyMeasurable.congr ?_
  filter_upwards [ctr_ae_residual_isHermitian model α i] with ω hω
  change Set.indicator _ _ _ = _
  rw [Set.indicator_of_mem (show _ ∈ {x : p.SiteMatrix × ℝ | x.1.IsHermitian} from hω)]
  rfl

theorem ctr_center_sq_integrable (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n) :
    Integrable (fun ω => ctrCenter p model α i ω ^ 2)
      (extendedPairMeasure p α i (ctrExtension p model i).P (ctrExtension p model i).Hm) := by
  have := extendedPairMeasure_isProbability p model α i (ctrExtension p model i)
  refine Integrable.of_bound ((ctr_center_aesm model α i).pow 2) 1
    (Filter.Eventually.of_forall fun ω => ?_)
  have h := ctr_abs_dysonCenter_le (i := i) cst0 α
    ((ctrExtension p model i).Hm ω - embedPair p i ω.2)
    (physicalOrderedEigenvalue p ((ctrExtension p model i).Hm ω) α)
  rw [Real.norm_eq_abs, abs_pow]
  change |ctrCenter p model α i ω| ^ 2 ≤ 1
  exact pow_le_one₀ (abs_nonneg _) h

/-- **The physical center family** (shared by `QUE.PhysicalCenterContract` and
`QUE.PhysicalAngularModeContract`): the edge-split extension with the Dyson center
`j_e(λ_α)` for the domain constants `cst0`. -/
def pairCenterFamily0 : PairCenterFamily := fun p model α i =>
  { X := ctrExtension p model i
    center := ctrCenter p model α i
    aesm := ctr_center_aesm model α i
    sq_integrable := ctr_center_sq_integrable model α i }

/-- **The center family is the Dyson center** (`IsDysonCenterFamily cst0`): `G = Prod.snd` has
the law `GUE_{2W}(s/(2W))`, is independent of `Hm - embed G = assemble (ω, 0)` under the
product law, and the center is `dysonCenter` at `(Hm - embed G, λ_α(Hm))` by definition. -/
theorem pairCenterFamily0_isDyson : IsDysonCenterFamily cst0 pairCenterFamily0 := by
  intro p model α i
  have hPω := ctr_splitLaw_isProb p model i
  have hγ : IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p (splitS p))) :=
    BlockBand.Layers.rsl_isProbabilityMeasure_gue _
  refine ⟨Prod.snd, ⟨measurable_snd, ?_, ?_⟩, fun ω => rfl⟩
  · refine ⟨measurable_snd.aemeasurable, ?_⟩
    change ((ctrSplitLaw p i).prod (gueMeasure (PairSite p i) (pairTime p (splitS p)))).map
      Prod.snd = _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  · have hfun : (fun ω : (pairCenterFamily0 p model α i).X.Ω =>
        (pairCenterFamily0 p model α i).X.Hm ω - embedPair p i ω.2) =
        fun ω => assemble p i ω.1 0 := by
      funext ω
      exact ctr_assemble_sub_embed i ω.1 ω.2
    rw [hfun]
    exact indepFun_prod (μ := ctrSplitLaw p i)
      (ν := gueMeasure (PairSite p i) (pairTime p (splitS p)))
      (X := fun ω : SplitState p i => assemble p i ω 0) (Y := id)
      (BlockBand.Layers.rsl_measurable_L i) measurable_id

end Family

end BlockBand.Center
