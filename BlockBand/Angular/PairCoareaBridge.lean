module

public import BlockBand.Internal.Contracts.Layers

/-!
# Pair-law integrals on a center extension in coarea form

The center splitting `H = (H - G_e) + G_e` is an exact pair splitting, so integrals against the
extended pair measure of functions of the split residual and of `G_e` are given by the right
side `coareaRHS` of the pair coarea formula (`lintegral_extendedPairMeasure_eq_coareaRHS`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.PairCoareaBridge

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.QUE.Fourier
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

variable (p : Parameters) (i : ZMod p.n)

/-- The split state `(H_R, C, V)` of a matrix. -/
def splitOf (H : p.SiteMatrix) : SplitState p i :=
  (exteriorBlock p i H, couplingBlock p i H, pairBlock p i H)

theorem measurable_splitOf : Measurable (splitOf p i) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_) <;>
  · refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (measurable_pi_apply y.1).comp (measurable_pi_apply x.1)

/-- Reassembly: for Hermitian `A`, `assemble (splitOf A) G = A + embed G`. -/
theorem assemble_splitOf {A : p.SiteMatrix} (hA : A.IsHermitian) (G : PairMatrix p i) :
    assemble p i (splitOf p i A) G = A + embedPair p i G := by
  funext x y
  simp only [assemble, splitOf, exteriorBlock, couplingBlock, pairBlock, embedPair,
    Matrix.add_apply]
  split_ifs with hx hy hy
  · rfl
  · have := congrFun (congrFun hA x) y
    simp only [Matrix.conjTranspose_apply] at this
    rw [this, add_zero]
  · rw [add_zero]
  · rw [add_zero]

theorem embedPair_isHermitian {G : PairMatrix p i} (hG : G.IsHermitian) :
    (embedPair p i G).IsHermitian := by
  funext x y
  simp only [Matrix.conjTranspose_apply, embedPair]
  split_ifs with hx hy hy
  · exact congrFun (congrFun hG ⟨x, hy⟩) ⟨y, hx⟩
  all_goals simp

theorem measurable_embedPair : Measurable (embedPair p i) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  unfold embedPair
  split_ifs with hx hy
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  all_goals exact measurable_const

theorem measurable_assemble : Measurable (fun x : SplitState p i × PairMatrix p i =>
    assemble p i x.1 x.2) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  unfold assemble
  split_ifs with hx hy hy
  · fun_prop
  · exact continuous_star.measurable.comp (by fun_prop)
  · fun_prop
  · fun_prop

theorem gueSample_isHermitian {ι : Type*} [Fintype ι] (t : ℝ≥0) (X : ι × ι → ℂ) :
    (gueSample t X).IsHermitian := by
  funext a b
  simp only [gueSample, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_add,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem measurable_gueSample {ι : Type*} [Fintype ι] (t : ℝ≥0) :
    Measurable (gueSample (ι := ι) t) := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  simp only [gueSample, Matrix.of_apply]
  exact measurable_const.mul ((measurable_pi_apply _).add
    (Complex.continuous_conj.measurable.comp (measurable_pi_apply _)))

theorem measurableSet_isHermitian (ι : Type*) [Fintype ι] :
    MeasurableSet {G : Matrix ι ι ℂ | G.IsHermitian} := by
  have hset : {G : Matrix ι ι ℂ | G.IsHermitian} =
      ⋂ a, ⋂ b, {G : Matrix ι ι ℂ | star (G b a) = G a b} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h a b; exact congrFun (congrFun h a) b
    · intro h; funext a b; exact h a b
  rw [hset]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    measurableSet_eq_fun (continuous_star.measurable.comp
      ((measurable_pi_apply a).comp (measurable_pi_apply b)))
      ((measurable_pi_apply b).comp (measurable_pi_apply a))

/-- `GUE` samples are Hermitian almost surely. -/
theorem ae_gueMeasure_isHermitian (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    ∀ᵐ G ∂gueMeasure ι t, G.IsHermitian := by
  rw [ae_iff, gueMeasure, Measure.map_apply_of_aemeasurable
    (measurable_gueSample t).aemeasurable]
  · have : gueSample t ⁻¹' {G : Matrix ι ι ℂ | ¬ G.IsHermitian} = ∅ := by
      ext X; simp [gueSample_isHermitian t X]
    rw [this, measure_empty]
  · exact (measurableSet_isHermitian ι).compl

/-- **The center splitting is an exact pair splitting** (at
`s = min(c,b)`): the law of the split residual `(H_R, C, V)` of `H - G_e`, with the
independent `G_e ~ GUE_{2W}(s/2W)`, reassembles to the physical law. -/
theorem isPairSplitting_of_centerSplitting {model : p.GaussianRingModel}
    (X : PairExtension p model) (G : X.Ω → PairMatrix p i) (hG : IsCenterSplitting X G) :
    IsPairSplitting p i model (splitS p)
      (X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)))) := by
  obtain ⟨hGm, hlaw, hind⟩ := hG
  have hAm : Measurable (fun ω => X.Hm ω - embedPair p i (G ω)) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp X.measurable_Hm).sub
      (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
        ((measurable_embedPair p i).comp hGm))
  have hSm : Measurable (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω))) :=
    (measurable_splitOf p i).comp hAm
  have hprobmap : IsProbabilityMeasure (X.P.map X.Hm) := by rw [X.map_eq]; infer_instance
  have hprob : IsProbabilityMeasure X.P :=
    Measure.isProbabilityMeasure_of_map X.measurable_Hm.aemeasurable
  have hind' : IndepFun (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω))) G X.P :=
    hind.comp (measurable_splitOf p i) measurable_id
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hSm.aemeasurable
    hGm.aemeasurable).1 hind'
  unfold IsPairSplitting
  rw [← hlaw.map_eq, ← hprod, Measure.map_map (measurable_assemble p i) (hSm.prodMk hGm),
    ← X.map_eq]
  apply Measure.map_congr
  have hH : ∀ᵐ ω ∂X.P, (X.Hm ω).IsHermitian := by
    have h := model.isPhysical.1
    rw [← X.map_eq, ae_map_iff X.measurable_Hm.aemeasurable
      (measurableSet_isHermitian p.Site)] at h
    exact h
  have hGh : ∀ᵐ ω ∂X.P, (G ω).IsHermitian := by
    have h := ae_gueMeasure_isHermitian (PairSite p i) (pairTime p (splitS p))
    rw [← hlaw.map_eq, ae_map_iff hGm.aemeasurable
      (measurableSet_isHermitian (PairSite p i))] at h
    exact h
  filter_upwards [hH, hGh] with ω h1 h2
  simp only [Function.comp_apply]
  rw [assemble_splitOf p i (h1.sub (embedPair_isHermitian p i h2)), sub_add_cancel]

theorem splitS_pos : 0 < splitS p := lt_min p.c_pos p.b_pos

/-- **Pair-law integrals in coarea form** (Step 1 of the physical angular estimate): for a
center splitting and every measurable `Φ ≥ 0` of the split residual and the pair Gaussian,
`∫ Φ dP♯_{α,S}` on the extension equals `coareaRHS` with crossing factor `n/2`, with the exact
splitting law of the residual. -/
theorem lintegral_extendedPairMeasure_eq_coareaRHS (hC : CoareaContract)
    {model : p.GaussianRingModel} (α : Fin p.N) (X : PairExtension p model)
    (G : X.Ω → PairMatrix p i) (hG : IsCenterSplitting X G)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) (hU : IsPairFrame p i U)
    (Φ : SplitState p i → PairMatrix p i → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ)) :
    (∫⁻ ω, Φ (splitOf p i (X.Hm ω - embedPair p i (G ω))) (G ω)
        ∂extendedPairMeasure p α i X.P X.Hm) =
      coareaRHS p α i (splitS p) (X.P.map (fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω))))
        U (fun _ _ _ => (p.n : ℝ) / 2) Φ := by
  have hsplit := isPairSplitting_of_centerSplitting p i X G hG
  have hf := hC.pairLaw_formula p model α i (splitS p) (splitS_pos p) le_rfl _ hsplit U hU Φ hΦ
  rw [← hf]
  obtain ⟨hGm, hlaw, hind⟩ := hG
  have hAm : Measurable (fun ω => X.Hm ω - embedPair p i (G ω)) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp X.measurable_Hm).sub
      (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
        ((measurable_embedPair p i).comp hGm))
  set S := fun ω => splitOf p i (X.Hm ω - embedPair p i (G ω)) with hSdef
  have hSm : Measurable S := (measurable_splitOf p i).comp hAm
  have hprobmap : IsProbabilityMeasure (X.P.map X.Hm) := by rw [X.map_eq]; infer_instance
  have hprob : IsProbabilityMeasure X.P :=
    Measure.isProbabilityMeasure_of_map X.measurable_Hm.aemeasurable
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hSm.aemeasurable hGm.aemeasurable).1
    (hind.comp (measurable_splitOf p i) measurable_id)
  rw [← hlaw.map_eq, ← hprod]
  have hmass : Measurable (fun H : p.SiteMatrix => pairMass p i α H) :=
    (measurable_physicalOrderedBlockMass p α i).add (measurable_physicalOrderedBlockMass p α (i + 1))
  have hmeas : Measurable (fun x : SplitState p i × PairMatrix p i =>
      ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2)) * Φ x.1 x.2) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (hmass.comp (measurable_assemble p i)))).mul hΦ
  rw [lintegral_map hmeas (hSm.prodMk hGm)]
  have hwd : (∫⁻ ω, Φ (S ω) (G ω) ∂extendedPairMeasure p α i X.P X.Hm) =
      ∫⁻ ω, (physicalPairWeight p α i (X.Hm ω) : ℝ≥0∞) * Φ (S ω) (G ω) ∂X.P := by
    unfold extendedPairMeasure
    exact lintegral_withDensity_eq_lintegral_mul _
      (measurable_coe_nnreal_ennreal.comp ((measurable_physicalPairWeight p α i).comp
        X.measurable_Hm)) (hΦ.comp (hSm.prodMk hGm))
  rw [hwd]
  apply lintegral_congr_ae
  have hH : ∀ᵐ ω ∂X.P, (X.Hm ω).IsHermitian := by
    have h := model.isPhysical.1
    rw [← X.map_eq, ae_map_iff X.measurable_Hm.aemeasurable
      (measurableSet_isHermitian p.Site)] at h
    exact h
  have hGh : ∀ᵐ ω ∂X.P, (G ω).IsHermitian := by
    have h := ae_gueMeasure_isHermitian (PairSite p i) (pairTime p (splitS p))
    rw [← hlaw.map_eq, ae_map_iff hGm.aemeasurable
      (measurableSet_isHermitian (PairSite p i))] at h
    exact h
  filter_upwards [hH, hGh] with ω h1 h2
  rw [hSdef]
  dsimp only
  rw [assemble_splitOf p i (h1.sub (embedPair_isHermitian p i h2)), sub_add_cancel]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  rfl

end BlockBand.Angular.PairCoareaBridge
