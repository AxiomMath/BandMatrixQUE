module

public import BlockBand.Angular.AssemblyGoodCenter
public import BlockBand.DeterminantScore.MinorTail

/-!
# The signed transfer to angular integrals

* `lintegral_transfer`: for a measurable line-invariant real observable `g(ω, E, u)` and a sign
  `σ ∈ ℝ`, `E♯[(σ g(splitOf(H - G_e), λ_α, ψ_α))⁺]` is the `Pω`-average of
  `∫dE ∫ν(dv) c_{d,t}(n/2)𝓡 (σ g(ω, E, L_E v))⁺ 𝔷_E(v)` (`angInt`). It applies
  `FiberAngular.lintegral_extendedPairMeasure_eq_angular` to `Ψ = (σ liftP g)⁺`.
* `measurable_angInt`: the `(ω, E)`-integrand is jointly measurable (`measurable_schurLift`,
  `measurable_detFactor`, `PhysicalColumn.measurable_angularWeight`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.AssemblyGood

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.FiberAngular
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.QUE
open BlockBand.Angular.Assembly BlockBand.Angular.ProjectiveStein BlockBand.Angular.PairCoareaBridge
open BlockBand.DeterminantScore BlockBand.DeterminantScore.PhysicalColumn BlockBand.Coarea
open BlockBand.Model.Construction BlockBand.QUE.PhysicalAngularReduction
open scoped ENNReal NNReal

variable {p : BlockBand.Parameters} {i : ZMod p.n}

/-- The fiber integral `∫ν(dv) c_{d,t}(n/2)𝓡 (σ g(ω, E, L_E v))⁺ 𝔷_E(v)`. -/
def angInt (α : Fin p.N) (U : FrameMap p i) (g : SplitState p i × ℝ → (p.Site → ℂ) → ℝ)
    (sgn : ℝ) (ω : SplitState p i) (E : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (angularWeight p i (splitS p) ω E v) *
      ENNReal.ofReal (sgn * g (ω, E) (schurLift p i ω.1 ω.2.1 E v)) *
      detFactor p i α (splitS p) U ω E v ∂projectiveHaar (PairSite p i)

theorem measurable_schurLift :
    Measurable fun θ : OuterData p i => schurLift p i θ.1.1 θ.1.2.1 θ.2.1 θ.2.2 := by
  classical
  have hT : Measurable fun θ : OuterData p i => physicalCoareaT θ.1.1 θ.1.2.1 θ.2.1 := by
    unfold physicalCoareaT physicalCoareaResolvent
    exact measurable_matMul (measurable_inv_matrix.comp (measurable_matSub measurable_fst.fst
      (measurable_smul_one measurable_snd.fst))) measurable_fst.snd.fst
  have hTv := measurable_mulVec' hT measurable_snd.snd
  refine measurable_pi_iff.2 fun x => ?_
  unfold schurLift
  by_cases hx : x.1 = i ∨ x.1 = i + 1
  · simp only [hx, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd.snd
  · simp only [hx, ↓reduceDIte]
    exact ((measurable_pi_apply _).comp hTv).neg

theorem measurable_detFactor (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U) :
    Measurable fun θ : OuterData p i => detFactor p i α s U θ.1 θ.2.1 θ.2.2 := by
  have := isProbabilityMeasure_gue (FrameIndex p) (pairTime p s)
  simp only [BlockBand.DeterminantScore.MinorTail.detFactor_eq_zNat]
  exact (measurable_secInt hU.1 α.val).lintegral_prod_right'

theorem measurable_angIntegrand (α : Fin p.N) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {g : SplitState p i × ℝ → (p.Site → ℂ) → ℝ} (hgm : Measurable (Function.uncurry g))
    (sgn : ℝ) :
    Measurable fun θ : OuterData p i => ENNReal.ofReal (angularWeight p i (splitS p) θ.1 θ.2.1 θ.2.2) *
      ENNReal.ofReal (sgn * g (θ.1, θ.2.1) (schurLift p i θ.1.1 θ.1.2.1 θ.2.1 θ.2.2)) *
      detFactor p i α (splitS p) U θ.1 θ.2.1 θ.2.2 := by
  have hg : Measurable fun θ : OuterData p i =>
      g (θ.1, θ.2.1) (schurLift p i θ.1.1 θ.1.2.1 θ.2.1 θ.2.2) :=
    hgm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_schurLift)
  exact ((ENNReal.measurable_ofReal.comp (measurable_angularWeight (splitS p))).mul
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hg))).mul
    (measurable_detFactor α (splitS p) hU)

theorem measurable_angInt (α : Fin p.N) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {g : SplitState p i × ℝ → (p.Site → ℂ) → ℝ} (hgm : Measurable (Function.uncurry g))
    (sgn : ℝ) : Measurable (Function.uncurry (angInt α U g sgn)) := by
  have := isProbabilityMeasure_projectiveHaar (ι := PairSite p i)
  exact ((measurable_angIntegrand α hU hgm sgn).comp (measurable_fst.fst.prodMk
    (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'

/-- **The signed transfer to angular integrals.** -/
theorem lintegral_transfer (hC : CoareaContract) {model : p.GaussianRingModel} (α : Fin p.N)
    (X : PairExtension p model) (G : X.Ω → PairMatrix p i) (hG : IsCenterSplitting X G)
    {U : FrameMap p i} (hU : IsPairFrame p i U) {g : SplitState p i × ℝ → (p.Site → ℂ) → ℝ}
    (hgm : Measurable (Function.uncurry g)) (hg : IsLineInvariant g) (sgn : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (sgn * g (splitOf p i (residual p i X G ω),
          physicalOrderedEigenvalue p (X.Hm ω) α) (physicalOrderedEigenvector p (X.Hm ω) α))
        ∂extendedPairMeasure p α i X.P X.Hm) =
      ∫⁻ ω', ∫⁻ E, angInt α U g sgn ω' E
        ∂volume ∂(X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)))) := by
  set Ψ : SplitState p i → ℝ → (p.Site → p.Site → ℂ) → ℝ≥0∞ :=
    fun ω' E P => ENNReal.ofReal (sgn * liftP g (ω', E) P) with hΨ
  have hΨm : Measurable (fun x : SplitState p i × ℝ × (p.Site → p.Site → ℂ) =>
      Ψ x.1 x.2.1 x.2.2) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((measurable_liftP hgm).comp
      ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)))
  have h1 := lintegral_extendedPairMeasure_eq_angular p i hC α X G hG hU Ψ hΨm
    (fun _ _ _ => ENNReal.ofReal_ne_top)
  have hL : (∫⁻ ω, ENNReal.ofReal (sgn * g (splitOf p i (residual p i X G ω),
        physicalOrderedEigenvalue p (X.Hm ω) α) (physicalOrderedEigenvector p (X.Hm ω) α))
      ∂extendedPairMeasure p α i X.P X.Hm) =
      ∫⁻ ω, (fun (ω' : SplitState p i) (G' : PairMatrix p i) =>
          Ψ ω' (physicalOrderedEigenvalue p (assemble p i ω' G') α)
            (eigenProjector (physicalOrderedEigenvector p (assemble p i ω' G') α)))
          (splitOf p i (X.Hm ω - embedPair p i (G ω))) (G ω)
        ∂extendedPairMeasure p α i X.P X.Hm := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_residual_eigen α X G hG, ae_l2Norm_eigenvector p model α i X] with ω hω hψ
    have hA : assemble p i (splitOf p i (X.Hm ω - embedPair p i (G ω))) (G ω) = X.Hm ω := by
      have hh : (X.Hm ω - embedPair p i (G ω)).IsHermitian := hω.1
      rw [assemble_splitOf p i hh, sub_add_cancel]
    simp only [hΨ, hA, liftP_eigenProjector hg _ hψ]
    rfl
  rw [hL, h1]
  refine lintegral_congr fun ω' => lintegral_congr fun E => ?_
  unfold angInt
  refine lintegral_congr_ae ?_
  filter_upwards [ae_projectiveHaar_unit (ι := PairSite p i)] with v hv
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp [normSqSum] at hv
  simp only [hΨ, liftP_lineProjector hg _ (schurLift_ne_zero p i _ _ _ hv0)]

end BlockBand.Angular.AssemblyGood
