module

public import BlockBand.DeterminantScore.ScoreMoments
public import BlockBand.DeterminantScore.GUENormTailProofMoment

/-!
# Pair-law moments of the deleted row `‖QK₀v‖`

At the selected root `QK₀v = -QG_dv`, and the pair law has every fixed Gaussian norm moment
bounded. `pairRowMoment_holds`: `ScoreMoments.PairRowMomentStatement` from `CoareaContract` alone.

Proof.
* Support identity (`reconstructedGaussian_mulVec`): for a pair frame `U` and unit `v`, the
  reconstructed Gaussian `G = E vv* + U_v(F_v + G')U_v* - F(E)` satisfies `Gv = -(F(E) - E)v`
  (`U_v*v = 0`, `v*v = 1`), so `‖QK₀v‖ ≤ 2‖K₀v‖ = 2‖Gv‖ ≤ 2‖G‖` (`Q = I - vv*`, Cauchy–Schwarz;
  the factor `2` replaces `‖Q‖ ≤ 1` and is harmless).
* Transfer: `pairExpect` of an observable of the reconstructed Gaussian is the split-space
  integral with density `(n/2)m`, `m` the pair mass of the reassembled matrix
  (`MinorTailInverse.pairExpect_reconstructed`, `CoareaContract.pairLaw_formula`).
* Uniformity: with `GUE_{2W}(t)`, `t = s/(2W)`, `s = min(c,b) < 1/2`, and the exponential tail
  `GUE{‖G‖ > C₀√(t·2W)} ≤ e^{-c₀·2W}` (`GUENormTail.gueNormTail_holds`):
  `‖G‖^q ≤ C₀^q` off the tail event, where the pair law has mass at most one
  (`pairExpect_one_le`); on the tail event `m ≤ 1` (block masses sum to one a.s.) and
  Cauchy–Schwarz with the `2q`-moment `∫‖G‖^{2q} ≤ C_{2q}(t(2W+1))^q ≤ C_{2q}`
  (`GUENormTail.gueNormMoment_le`) give `(n/2)e^{-c₀W}C_{2q}^{1/2} ≤ (T/(2c₀))C_{2q}^{1/2}`
  for `n ≤ TW` (`c₀W e^{-c₀W} ≤ 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ScoreMoments

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open BlockBand.DeterminantScore.MinorTailInverse BlockBand.DeterminantScore.GUENormTail
open scoped NNReal ENNReal Matrix.Norms.L2Operator InnerProductSpace

variable {p : Parameters} {i : ZMod p.n}

/-!
Auxiliary lemmas live in `ScoreMoments.PairRow` (no clash with sibling modules).
-/

namespace PairRow

/-!
## Finite-dimensional algebra
-/

theorem star_dotProduct_self_of_l2Norm {ι : Type} [Fintype ι] {v : ι → ℂ} (hv : l2Norm v = 1) :
    star v ⬝ᵥ v = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
  rw [EuclideanSpace.inner_eq_star_dotProduct, ← l2Norm_toLp, hv] at h
  rw [dotProduct_comm]
  simpa using h

theorem norm_star_dotProduct_le {ι : Type} [Fintype ι] (v y : ι → ℂ) :
    ‖star v ⬝ᵥ y‖ ≤ l2Norm v * l2Norm y := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 y : EuclideanSpace ℂ ι)
  rw [EuclideanSpace.inner_eq_star_dotProduct, ← l2Norm_toLp, ← l2Norm_toLp] at h
  rw [dotProduct_comm]
  simpa using h

theorem l2Norm_sub_le_add {ι : Type} [Fintype ι] (x y : ι → ℂ) :
    l2Norm (x - y) ≤ l2Norm x + l2Norm y := by
  rw [l2Norm_toLp, l2Norm_toLp, l2Norm_toLp, WithLp.toLp_sub]
  exact norm_sub_le _ _

theorem l2Norm_neg_eq {ι : Type} [Fintype ι] (x : ι → ℂ) : l2Norm (-x) = l2Norm x := by
  unfold l2Norm; simp

/-- `‖Qy‖ ≤ 2‖y‖` for `Q = I - vv*`, `v` a unit vector. -/
theorem l2Norm_orthProj_mulVec_le {v : PairSite p i → ℂ} (hv : l2Norm v = 1)
    (y : PairSite p i → ℂ) : l2Norm (orthProj v *ᵥ y) ≤ 2 * l2Norm y := by
  have e : orthProj v *ᵥ y = y - (star v ⬝ᵥ y) • v := by
    unfold orthProj
    rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  rw [e]
  have h1 := l2Norm_sub_le_add y ((star v ⬝ᵥ y) • v)
  rw [l2Norm_smul _ v, hv, mul_one] at h1
  have h2 := norm_star_dotProduct_le v y
  rw [hv, one_mul] at h2
  linarith

/-- **Support identity** `QK₀v = -QG_dv`: at the reconstructed Gaussian
`G = E vv* + U_v(F_v + G')U_v* - F(E)`, `Gv = -(F(E) - E)v` for unit `v`. -/
theorem reconstructedGaussian_mulVec {U : FrameMap p i} (hU : IsPairFrame p i U)
    (ω : SplitState p i) (E : ℝ) {v : PairSite p i → ℂ} (hv : l2Norm v = 1)
    (G' : FrameMatrix p) :
    reconstructedGaussian p i U ω E v G' *ᵥ v = -(outerK0 (ω, E, v) *ᵥ v) := by
  obtain ⟨-, hUv⟩ := hU.2 v hv
  have hvv := star_dotProduct_self_of_l2Norm hv
  unfold reconstructedGaussian outerK0
  simp only
  rw [sub_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    hvv, one_smul, ← mulVec_mulVec, hUv, mulVec_zero, add_zero, sub_mulVec, smul_mulVec,
    one_mulVec]
  abel

/-- `‖QK₀v‖ ≤ 2‖G‖` at the reconstructed Gaussian. -/
theorem l2Norm_row_le {U : FrameMap p i} (hU : IsPairFrame p i U) (θ : OuterData p i)
    (hv : l2Norm θ.2.2 = 1) (G' : FrameMatrix p) :
    l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) ≤
      2 * ‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ := by
  obtain ⟨ω, E, v⟩ := θ
  have h1 := l2Norm_orthProj_mulVec_le hv (outerK0 (ω, E, v) *ᵥ v)
  have e := reconstructedGaussian_mulVec hU ω E hv G'
  have h2 : l2Norm (outerK0 (ω, E, v) *ᵥ v) =
      l2Norm (reconstructedGaussian p i U ω E v G' *ᵥ v) := by
    rw [e, l2Norm_neg_eq]
  have h3 := l2Norm_mulVec_le (reconstructedGaussian p i U ω E v G') v
  rw [hv, mul_one] at h3
  simp only at h1 ⊢
  linarith

/-!
## Transfer to the split space
-/

/-- The split law `Pω ⊗ GUE_{2W}(t)` at `s = min(c,b)`. -/
abbrev splitProd (Pω : Measure (SplitState p i)) : Measure (SplitState p i × PairMatrix p i) :=
  Pω.prod (gueMeasure (PairSite p i) (pairTime p (splitS p)))

/-- **Transfer.** `E♯ 1{E ∈ I}‖QK₀v‖^q ≤ 2^q ∫ (n/2) m(H) ‖G‖^q d(Pω ⊗ GUE)`, `H` reassembled. -/
theorem pairExpect_row_le (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N) (κ : ℝ) {q : ℝ} (hq : 0 < q) :
    pairExpect α (splitS p) U Pω (fun θ _ =>
        (bulkInterval κ).indicator 1 θ.2.1 *
          ENNReal.ofReal (l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) ^ q)) ≤
      ENNReal.ofReal (2 ^ q) * ∫⁻ x, ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α
          (assemble p i x.1 x.2)) * ENNReal.ofReal (‖x.2‖ ^ q) ∂splitProd Pω := by
  set Φ : SplitState p i → PairMatrix p i → ℝ≥0∞ := fun _ G => ENNReal.ofReal (‖G‖ ^ q) with hΦ
  have hΦm : Measurable (Function.uncurry Φ) :=
    ((continuous_norm.measurable.pow_const q).ennreal_ofReal).comp measurable_snd
  have step : pairExpect α (splitS p) U Pω (fun θ _ =>
        (bulkInterval κ).indicator 1 θ.2.1 *
          ENNReal.ofReal (l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) ^ q)) ≤
      pairExpect α (splitS p) U Pω (fun θ G' => ENNReal.ofReal (2 ^ q) *
        Φ θ.1 (reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G')) := by
    refine pairExpect_mono_ae hPω α U fun θ _ _ hv _ => Filter.Eventually.of_forall fun G' _ => ?_
    have hind : (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) θ.2.1 ≤ 1 :=
      Set.indicator_le_self' (fun _ _ => zero_le_one) θ.2.1
    have hrow := l2Norm_row_le hU θ hv G'
    have h0 := l2Norm_nonneg' (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2))
    have hG0 := norm_nonneg (reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G')
    have hpow : l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) ^ q ≤
        2 ^ q * ‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ ^ q := by
      rw [← Real.mul_rpow (by norm_num) hG0]
      exact Real.rpow_le_rpow h0 hrow hq.le
    calc (bulkInterval κ).indicator 1 θ.2.1 *
          ENNReal.ofReal (l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) ^ q)
        ≤ 1 * ENNReal.ofReal (2 ^ q * ‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ ^ q) :=
          mul_le_mul' hind (ENNReal.ofReal_le_ofReal hpow)
      _ = _ := by
          rw [one_mul, ENNReal.ofReal_mul (by positivity)]
  refine step.trans (le_of_eq ?_)
  rw [pairExpect_const_mul α (splitS p) U Pω ENNReal.ofReal_ne_top,
    pairExpect_reconstructed α (splitS p) U Pω Φ,
    ← hC.pairLaw_formula p model α i (splitS p) (BlockBand.Angular.PairCoareaBridge.splitS_pos p)
      le_rfl Pω hPω U hU Φ hΦm]

/-!
## The split-space bound
-/

/-- Almost surely under the split law the pair mass of the reassembled matrix is in `[0, 1]`. -/
theorem ae_pairMass_le_one {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model (splitS p) Pω) (α : Fin p.N) :
    ∀ᵐ x ∂splitProd Pω, pairMass p i α (assemble p i x.1 x.2) ≤ 1 := by
  have h := physicalOrderedBlockMass_sum_ae p model
  rw [← hPω] at h
  filter_upwards [ae_of_ae_map (BlockBand.Angular.PairCoareaBridge.measurable_assemble p i).aemeasurable h] with x hx
  rw [← hx α]
  exact Finset.add_le_sum (fun k _ => physicalOrderedBlockMass_nonneg p _ α k)
    (Finset.mem_univ _) (Finset.mem_univ _) (self_ne_add_one p i)

theorem pairMass_nonneg' (α : Fin p.N) (H : p.SiteMatrix) : 0 ≤ pairMass p i α H :=
  add_nonneg (physicalOrderedBlockMass_nonneg p H α i) (physicalOrderedBlockMass_nonneg p H α _)

theorem measurable_pairDensity (α : Fin p.N) :
    Measurable fun x : SplitState p i × PairMatrix p i =>
      ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul
    (((measurable_physicalOrderedBlockMass p α i).add
      (measurable_physicalOrderedBlockMass p α (i + 1))).comp (BlockBand.Angular.PairCoareaBridge.measurable_assemble p i)))

/-- A splitting law is a probability measure. -/
theorem splitLaw_univ {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model (splitS p) Pω) : Pω Set.univ = 1 := by
  have := isProbabilityMeasure_gue (PairSite p i) (pairTime p (splitS p))
  have h := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) hPω
  rw [Measure.map_apply (BlockBand.Angular.PairCoareaBridge.measurable_assemble p i) MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod,
    measure_univ (μ := gueMeasure (PairSite p i) (pairTime p (splitS p))), mul_one,
    measure_univ (μ := (model.law : Measure p.SiteMatrix))] at h
  exact h

/-- The pair law has mass at most one, on the split space. -/
theorem lintegral_pairDensity_le_one (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N) :
    (∫⁻ x, ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2))
      ∂splitProd Pω) ≤ 1 := by
  have h := hC.pairLaw_formula p model α i (splitS p)
    (BlockBand.Angular.PairCoareaBridge.splitS_pos p) le_rfl Pω hPω U hU (fun _ _ => 1)
    measurable_const
  simp only [mul_one] at h
  rw [h, ← pairExpect_one_eq]
  exact pairExpect_one_le hC hPω hU α

/-- **Tail term.** Cauchy–Schwarz with the exponential tail and the `2q`-moment. -/
theorem lintegral_tail_norm_rpow_le {C₀ c₀ : ℝ}
    (htail : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      gueMeasure ι t {G | C₀ * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} ≤
        ENNReal.ofReal (Real.exp (-(c₀ * (Fintype.card ι : ℝ)))))
    {q : ℝ} (hq : 0 < q) :
    (∫⁻ G, {G : PairMatrix p i | C₀ * Real.sqrt ((pairTime p (splitS p) : ℝ) *
        (Fintype.card (PairSite p i) : ℝ)) < ‖G‖}.indicator 1 G * ENNReal.ofReal (‖G‖ ^ q)
      ∂gueMeasure (PairSite p i) (pairTime p (splitS p))) ≤
      ENNReal.ofReal (Real.exp (-(c₀ * p.W)) * gueMomentConst (2 * q) ^ (1 / 2 : ℝ)) := by
  set t := pairTime p (splitS p)
  set A : Set (PairMatrix p i) :=
    {G | C₀ * Real.sqrt ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ)) < ‖G‖} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const continuous_norm.measurable
  set μ := gueMeasure (PairSite p i) t
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsb : splitS p ≤ p.b := min_le_right _ _
  have hb := p.b_lt_half
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    rw [card_pairSite]; push_cast; ring
  have ht : (t : ℝ) = splitS p / (2 * p.W) := Real.coe_toNNReal _ (by positivity)
  have htd : (t : ℝ) * (Fintype.card (PairSite p i) + 1) ≤ 1 := by
    rw [ht, hcard, div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  have htd0 : 0 ≤ (t : ℝ) * (Fintype.card (PairSite p i) + 1) := by positivity
  have hf : AEMeasurable (A.indicator (1 : PairMatrix p i → ℝ≥0∞)) μ :=
    (measurable_one.indicator hAm).aemeasurable
  have hg : AEMeasurable (fun G : PairMatrix p i => ENNReal.ofReal (‖G‖ ^ q)) μ :=
    (continuous_norm.measurable.pow_const q).ennreal_ofReal.aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : (∫⁻ G, A.indicator (1 : PairMatrix p i → ℝ≥0∞) G ^ (2 : ℝ) ∂μ) = μ A := by
    rw [← lintegral_indicator_one hAm]
    refine lintegral_congr fun G => ?_
    by_cases hG : G ∈ A <;> simp [hG]
  have e2 : (∫⁻ G, ENNReal.ofReal (‖G‖ ^ q) ^ (2 : ℝ) ∂μ) =
      ∫⁻ G, ENNReal.ofReal (‖G‖ ^ (2 * q)) ∂μ := by
    refine lintegral_congr fun G => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (norm_nonneg _), mul_comm]
  have hmom := gueNormMoment_le (by positivity : 0 < 2 * q) (PairSite p i) t
  have hmom' : (∫⁻ G, ENNReal.ofReal (‖G‖ ^ (2 * q)) ∂μ) ≤
      ENNReal.ofReal (gueMomentConst (2 * q)) := by
    refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : ((t : ℝ) * (Fintype.card (PairSite p i) + 1)) ^ (2 * q / 2) ≤ 1 :=
      Real.rpow_le_one htd0 htd (by positivity)
    have h2 := gueMomentConst_nonneg (by positivity : 0 < 2 * q)
    nlinarith
  have htl : μ A ≤ ENNReal.ofReal (Real.exp (-(c₀ * (2 * p.W)))) := by
    calc μ A ≤ _ := htail (PairSite p i) t
      _ = _ := by rw [hcard]
  have hexp : Real.exp (-(c₀ * (2 * p.W))) ^ (1 / 2 : ℝ) = Real.exp (-(c₀ * p.W)) := by
    rw [← Real.exp_mul]; congr 1; ring
  calc (∫⁻ G, A.indicator 1 G * ENNReal.ofReal (‖G‖ ^ q) ∂μ)
      ≤ (∫⁻ G, A.indicator (1 : PairMatrix p i → ℝ≥0∞) G ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ G, ENNReal.ofReal (‖G‖ ^ q) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hH
    _ ≤ ENNReal.ofReal (Real.exp (-(c₀ * (2 * p.W)))) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (gueMomentConst (2 * q)) ^ (1 / 2 : ℝ) := by
        rw [e1, e2]
        exact mul_le_mul' (ENNReal.rpow_le_rpow htl (by norm_num))
          (ENNReal.rpow_le_rpow hmom' (by norm_num))
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (gueMomentConst_nonneg (by positivity)) (by norm_num),
          hexp, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Integrals of functions of `G` alone under the split law. -/
theorem lintegral_splitProd_snd {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hPω : IsPairSplitting p i model (splitS p) Pω) {g : PairMatrix p i → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ x, g x.2 ∂splitProd Pω) = ∫⁻ G, g G ∂gueMeasure (PairSite p i) (pairTime p (splitS p)) := by
  have := isProbabilityMeasure_gue (PairSite p i) (pairTime p (splitS p))
  have h := lintegral_prod_mul (μ := Pω) (ν := gueMeasure (PairSite p i) (pairTime p (splitS p)))
    (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const hg.aemeasurable
  simp only [one_mul, lintegral_one, splitLaw_univ hPω] at h
  exact h

/-- **The split-space bound.** `∫ (n/2) m ‖G‖^q ≤ C₀^q + (n/2) e^{-c₀W} C_{2q}^{1/2}`. -/
theorem lintegral_pairDensity_norm_rpow_le (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N) {C₀ c₀ : ℝ} (hC₀ : 0 < C₀)
    (htail : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      gueMeasure ι t {G | C₀ * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} ≤
        ENNReal.ofReal (Real.exp (-(c₀ * (Fintype.card ι : ℝ)))))
    {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2)) *
        ENNReal.ofReal (‖x.2‖ ^ q) ∂splitProd Pω) ≤
      ENNReal.ofReal (C₀ ^ q) + ENNReal.ofReal ((p.n : ℝ) / 2) *
        ENNReal.ofReal (Real.exp (-(c₀ * p.W)) * gueMomentConst (2 * q) ^ (1 / 2 : ℝ)) := by
  set t := pairTime p (splitS p)
  set A : Set (PairMatrix p i) :=
    {G | C₀ * Real.sqrt ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ)) < ‖G‖} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const continuous_norm.measurable
  set w : SplitState p i × PairMatrix p i → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2)) with hw
  have hwm : Measurable w := measurable_pairDensity α
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsb : splitS p ≤ p.b := min_le_right _ _
  have hb := p.b_lt_half
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    rw [card_pairSite]; push_cast; ring
  have ht : (t : ℝ) = splitS p / (2 * p.W) := Real.coe_toNNReal _ (by positivity)
  have htd : (t : ℝ) * (Fintype.card (PairSite p i) : ℝ) ≤ 1 := by
    rw [ht, hcard, div_mul_cancel₀ _ (by positivity)]
    linarith
  have hR : C₀ * Real.sqrt ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ)) ≤ C₀ := by
    have := Real.sqrt_le_one.mpr htd
    nlinarith [Real.sqrt_nonneg ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ))]
  have hn2 : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  have hpt : ∀ᵐ x ∂splitProd Pω, w x * ENNReal.ofReal (‖x.2‖ ^ q) ≤
      w x * ENNReal.ofReal (C₀ ^ q) + ENNReal.ofReal ((p.n : ℝ) / 2) *
        (A.indicator 1 x.2 * ENNReal.ofReal (‖x.2‖ ^ q)) := by
    filter_upwards [ae_pairMass_le_one hPω α] with x hx
    by_cases hG : x.2 ∈ A
    · have hwle : w x ≤ ENNReal.ofReal ((p.n : ℝ) / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := pairMass_nonneg' (i := i) α (assemble p i x.1 x.2)
        nlinarith
      simp only [Set.indicator_of_mem hG, Pi.one_apply, one_mul]
      exact le_add_left (mul_le_mul_left hwle _)
    · have hle : ‖x.2‖ ≤ C₀ := by
        have : ¬ C₀ * Real.sqrt ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ)) < ‖x.2‖ := hG
        linarith [not_lt.mp this]
      have hpow : ‖x.2‖ ^ q ≤ C₀ ^ q := Real.rpow_le_rpow (norm_nonneg _) hle hq.le
      exact le_add_right (mul_le_mul_right (ENNReal.ofReal_le_ofReal hpow) _)
  have hgm : Measurable fun G : PairMatrix p i =>
      A.indicator (1 : PairMatrix p i → ℝ≥0∞) G * ENNReal.ofReal (‖G‖ ^ q) :=
    (measurable_one.indicator hAm).mul (continuous_norm.measurable.pow_const q).ennreal_ofReal
  have hmass := lintegral_pairDensity_le_one hC hPω hU α
  have htl := lintegral_tail_norm_rpow_le (p := p) (i := i) htail hq
  calc (∫⁻ x, w x * ENNReal.ofReal (‖x.2‖ ^ q) ∂splitProd Pω)
      ≤ ∫⁻ x, (w x * ENNReal.ofReal (C₀ ^ q) + ENNReal.ofReal ((p.n : ℝ) / 2) *
          (A.indicator 1 x.2 * ENNReal.ofReal (‖x.2‖ ^ q))) ∂splitProd Pω :=
        lintegral_mono_ae hpt
    _ = (∫⁻ x, w x ∂splitProd Pω) * ENNReal.ofReal (C₀ ^ q) +
          ENNReal.ofReal ((p.n : ℝ) / 2) *
            ∫⁻ G, A.indicator 1 G * ENNReal.ofReal (‖G‖ ^ q) ∂gueMeasure (PairSite p i) t := by
        rw [lintegral_add_left (hwm.mul_const _), lintegral_mul_const _ hwm,
          lintegral_const_mul _ (f := fun x : SplitState p i × PairMatrix p i =>
            A.indicator 1 x.2 * ENNReal.ofReal (‖x.2‖ ^ q)) (hgm.comp measurable_snd),
          lintegral_splitProd_snd hPω hgm]
    _ ≤ 1 * ENNReal.ofReal (C₀ ^ q) + ENNReal.ofReal ((p.n : ℝ) / 2) *
          ENNReal.ofReal (Real.exp (-(c₀ * p.W)) * gueMomentConst (2 * q) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = _ := by rw [one_mul]

/-!
## The statement
-/

/-- `(n/2) e^{-c₀W} ≤ T/(2c₀)` for `n ≤ TW` (`c₀W ≤ e^{c₀W}`). -/
theorem half_mul_exp_le {n W T c₀ : ℝ} (hn : 0 ≤ n) (hW : 0 < W) (hc₀ : 0 < c₀)
    (hnT : n ≤ T * W) : n / 2 * Real.exp (-(c₀ * W)) ≤ T / (2 * c₀) := by
  have he := Real.add_one_le_exp (c₀ * W)
  have hpos := Real.exp_pos (-(c₀ * W))
  have hmul : Real.exp (c₀ * W) * Real.exp (-(c₀ * W)) = 1 := by
    rw [← Real.exp_add]; simp
  have hcw : c₀ * W * Real.exp (-(c₀ * W)) ≤ 1 := by nlinarith
  have h1 : n * Real.exp (-(c₀ * W)) ≤ T * W * Real.exp (-(c₀ * W)) :=
    mul_le_mul_of_nonneg_right hnT hpos.le
  have hT0 : 0 ≤ T := by
    by_contra h
    have : T * W < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) hW
    linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hcw hT0]

end PairRow

open PairRow

/-- **Pair-law moments of the deleted row** (`ScoreMoments.PairRowMomentStatement`):
`E♯ 1{E ∈ I}‖QK₀v‖^q ≤ C`, uniformly in `4 ≤ n ≤ TW`, models, ranks, pairs, splitting laws and
frames. Hypothesis: `CoareaContract`. -/
theorem pairRowMoment_holds (hC : CoareaContract) : PairRowMomentStatement := by
  intro b T ϑ κ q _ _ hq
  obtain ⟨C₀, c₀, hC₀, hc₀, htail⟩ := gueNormTail_holds
  refine ⟨2 ^ q * (C₀ ^ q + T / (2 * c₀) * gueMomentConst (2 * q) ^ (1 / 2 : ℝ)), ?_⟩
  intro p _ hnT model α _ i Pω hPω U hU
  have h1 := pairExpect_row_le hC hPω hU α κ hq
  have h2 := lintegral_pairDensity_norm_rpow_le hC hPω hU α hC₀ htail hq
  have hm0 : 0 ≤ gueMomentConst (2 * q) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (gueMomentConst_nonneg (by positivity)) _
  have hn2 : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hexp := Real.exp_pos (-(c₀ * p.W))
  have hkey := half_mul_exp_le (Nat.cast_nonneg p.n) hW hc₀ hnT
  have hC0q : 0 ≤ C₀ ^ q := Real.rpow_nonneg hC₀.le _
  set M := gueMomentConst (2 * q) ^ (1 / 2 : ℝ)
  have e : ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal (C₀ ^ q) + ENNReal.ofReal ((p.n : ℝ) / 2) *
      ENNReal.ofReal (Real.exp (-(c₀ * p.W)) * M)) =
      ENNReal.ofReal (2 ^ q * (C₀ ^ q + (p.n : ℝ) / 2 * (Real.exp (-(c₀ * p.W)) * M))) := by
    rw [← ENNReal.ofReal_mul hn2, ← ENNReal.ofReal_add hC0q (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  have hfin : 2 ^ q * (C₀ ^ q + (p.n : ℝ) / 2 * (Real.exp (-(c₀ * p.W)) * M)) ≤
      2 ^ q * (C₀ ^ q + T / (2 * c₀) * M) := by
    have h2q : (0 : ℝ) ≤ 2 ^ q := by positivity
    have : (p.n : ℝ) / 2 * (Real.exp (-(c₀ * p.W)) * M) ≤ T / (2 * c₀) * M := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkey hm0
    nlinarith
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul' le_rfl h2
    _ = _ := e
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

end BlockBand.DeterminantScore.ScoreMoments
