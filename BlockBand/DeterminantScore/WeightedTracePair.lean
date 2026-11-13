module

public import BlockBand.DeterminantScore.WeightedTraceCutoff
public import BlockBand.DeterminantScore.PhysicalColumn

/-!
# Pair-law tools for the weighted trace: the Gaussian norm event and moments

Bounds under the pair law for the reconstructed Gaussian `G_d`, used on the exceptional events.

* `measurable_recG`: the reconstructed Gaussian is jointly measurable in `(θ, G')`.
* `pairExpect_normPow_le`: `E♯‖G_d‖^q ≤ C₀^q + T/(2c₀) C_{2q}^{1/2}` for `n ≤ TW`
  (`ScoreMoments.PairRow.lintegral_pairDensity_norm_rpow_le`).
* `splitPairLaw_gauss_le`: the Gaussian norm event `{‖G_d‖ > C₀}` has pair-law probability
  `≤ (n/2) e^{-2c₀W}` (`dP♯ ≤ (n/2) dP`, GUE norm tail), and `half_exp_le_rpow`:
  `(n/2) e^{-2c₀W} ≤ K W^{-6}` for `n ≤ TW`.
* `pairExpect_hull_eq`: for any split-space event `Ω`, the pair-law expectation of the indicator
  of its measurable hull at the reconstructed Gaussian is `P♯(Ω)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeightedTrace

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.MinorTailInverse
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.GUENormTail
open BlockBand.DeterminantScore.ScoreMoments.PairRow BlockBand.LocalWindow
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

theorem measurable_recG {U : FrameMap p i} (hU : Measurable U) :
    Measurable fun z : OuterData p i × FrameMatrix p =>
      reconstructedGaussian p i U z.1.1 z.1.2.1 z.1.2.2 z.2 := by
  unfold reconstructedGaussian
  have hUv : Measurable fun z : OuterData p i × FrameMatrix p => U z.1.2.2 :=
    hU.comp measurable_fst.snd.snd
  have hF : Measurable fun z : OuterData p i × FrameMatrix p =>
      physicalCoareaF z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2.1 :=
    measurable_physF.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)
  have hv : ∀ a, Measurable fun z : OuterData p i × FrameMatrix p => z.1.2.2 a := fun a =>
    (measurable_pi_apply a).comp measurable_fst.snd.snd
  have hvv : Measurable fun z : OuterData p i × FrameMatrix p =>
      (z.1.2.1 : ℂ) • vecMulVec z.1.2.2 (star z.1.2.2) := by
    refine measurable_of_entry fun a b => ?_
    simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.star_apply]
    exact (Complex.measurable_ofReal.comp measurable_fst.snd.fst).mul
      ((hv a).mul (continuous_star.measurable.comp (hv b)))
  exact measurable_matSub (measurable_matAdd hvv (measurable_matMul (measurable_matMul hUv
    (measurable_matAdd (measurable_matMul (measurable_matMul (measurable_matConjT hUv) hF) hUv)
      measurable_snd)) (measurable_matConjT hUv))) hF

/-- **Pair-law moments of the Gaussian norm**: `E♯‖G_d‖^q ≤ C₀^q + T/(2c₀) C_{2q}^{1/2}`. -/
theorem pairExpect_normPow_le (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N) {T C₀ c₀ : ℝ}
    (hnT : (p.n : ℝ) ≤ T * p.W) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (htail : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      gueMeasure ι t {G | C₀ * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} ≤
        ENNReal.ofReal (Real.exp (-(c₀ * (Fintype.card ι : ℝ)))))
    {q : ℝ} (hq : 0 < q) :
    pairExpect α (splitS p) U Pω (fun θ G' =>
        ENNReal.ofReal (‖reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'‖ ^ q)) ≤
      ENNReal.ofReal (C₀ ^ q + T / (2 * c₀) * gueMomentConst (2 * q) ^ (1 / 2 : ℝ)) := by
  have hΦm : Measurable (Function.uncurry fun (_ : SplitState p i) (G : PairMatrix p i) =>
      ENNReal.ofReal (‖G‖ ^ q)) :=
    ((continuous_norm.measurable.pow_const q).ennreal_ofReal).comp measurable_snd
  rw [pairExpect_reconstructed α (splitS p) U Pω (fun _ G => ENNReal.ofReal (‖G‖ ^ q)),
    ← hC.pairLaw_formula p model α i (splitS p) (BlockBand.Angular.PairCoareaBridge.splitS_pos p)
      le_rfl Pω hPω U hU _ hΦm]
  refine (lintegral_pairDensity_norm_rpow_le hC hPω hU α hC₀ htail hq).trans ?_
  have hm0 : 0 ≤ gueMomentConst (2 * q) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (gueMomentConst_nonneg (by positivity)) _
  have hn2 : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hkey := half_mul_exp_le (Nat.cast_nonneg p.n) hW hc₀ hnT
  have hC0q : 0 ≤ C₀ ^ q := Real.rpow_nonneg hC₀.le _
  rw [← ENNReal.ofReal_mul hn2, ← ENNReal.ofReal_add hC0q (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (p.n : ℝ) / 2 * (Real.exp (-(c₀ * p.W)) * gueMomentConst (2 * q) ^ (1 / 2 : ℝ)) ≤
      T / (2 * c₀) * gueMomentConst (2 * q) ^ (1 / 2 : ℝ) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkey hm0
  linarith

/-- **The Gaussian norm event** has pair-law probability `≤ (n/2) e^{-2c₀W}`. -/
theorem splitPairLaw_gauss_le {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    (α : Fin p.N) {C₀ c₀ : ℝ} (hC₀ : 0 < C₀)
    (htail : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : ℝ≥0),
      gueMeasure ι t {G | C₀ * Real.sqrt ((t : ℝ) * (Fintype.card ι : ℝ)) < ‖G‖} ≤
        ENNReal.ofReal (Real.exp (-(c₀ * (Fintype.card ι : ℝ))))) :
    splitPairLaw p i α Pω {x | C₀ < ‖x.2‖} ≤
      ENNReal.ofReal ((p.n : ℝ) / 2 * Real.exp (-(c₀ * (2 * p.W)))) := by
  set t := pairTime p (splitS p)
  set A : Set (PairMatrix p i) := {G | C₀ < ‖G‖} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const continuous_norm.measurable
  have hS : MeasurableSet {x : SplitState p i × PairMatrix p i | C₀ < ‖x.2‖} :=
    measurableSet_lt measurable_const (continuous_norm.measurable.comp measurable_snd)
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsb : splitS p ≤ p.b := min_le_right _ _
  have hb := p.b_lt_half
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := card_pairSite_real
  have ht : (t : ℝ) = splitS p / (2 * p.W) := Real.coe_toNNReal _ (by positivity)
  have htd : (t : ℝ) * (Fintype.card (PairSite p i) : ℝ) ≤ 1 := by
    rw [ht, hcard, div_mul_cancel₀ _ (by positivity)]; linarith
  have hsub : A ⊆ {G | C₀ * Real.sqrt ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ)) < ‖G‖} := by
    intro G hG
    have h1 := Real.sqrt_le_one.mpr htd
    have : C₀ * Real.sqrt ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ)) ≤ C₀ := by
      nlinarith [Real.sqrt_nonneg ((t : ℝ) * (Fintype.card (PairSite p i) : ℝ))]
    exact lt_of_le_of_lt this hG
  have hgue : gueMeasure (PairSite p i) t A ≤
      ENNReal.ofReal (Real.exp (-(c₀ * (2 * p.W)))) := by
    refine (measure_mono hsub).trans ((htail (PairSite p i) t).trans (le_of_eq ?_))
    rw [hcard]
  have hn2 : (0 : ℝ) ≤ (p.n : ℝ) / 2 := by positivity
  unfold splitPairLaw splitLaw
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  calc (∫⁻ x, {x : SplitState p i × PairMatrix p i | C₀ < ‖x.2‖}.indicator (fun x =>
        ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2))) x ∂splitProd Pω)
      ≤ ∫⁻ x, ENNReal.ofReal ((p.n : ℝ) / 2) * A.indicator 1 x.2 ∂splitProd Pω := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_pairMass_le_one hPω α] with x hx
        by_cases hxS : C₀ < ‖x.2‖
        · rw [Set.indicator_of_mem (show x ∈ {x : SplitState p i × PairMatrix p i |
              C₀ < ‖x.2‖} from hxS), Set.indicator_of_mem (show x.2 ∈ A from hxS),
            Pi.one_apply, mul_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have := BlockBand.DeterminantScore.ScoreMoments.PairRow.pairMass_nonneg' (i := i) α
            (assemble p i x.1 x.2)
          nlinarith
        · simp only [Set.indicator, Set.mem_ofPred_eq, hxS, ite_false]
          exact zero_le
    _ = ENNReal.ofReal ((p.n : ℝ) / 2) * gueMeasure (PairSite p i) t A := by
        rw [lintegral_const_mul _ (f := fun x : SplitState p i × PairMatrix p i => A.indicator 1 x.2)
            ((measurable_one.indicator hAm).comp measurable_snd),
          lintegral_splitProd_snd hPω (measurable_one.indicator hAm), lintegral_indicator_one hAm]
    _ ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * ENNReal.ofReal (Real.exp (-(c₀ * (2 * p.W)))) := by
        gcongr
    _ = _ := (ENNReal.ofReal_mul hn2).symm

/-- `(n/2) e^{-2c₀W} ≤ (T/2)(7!/(2c₀)⁷) W^{-6}` for `n ≤ TW`. -/
theorem half_exp_le_rpow {n W T c₀ : ℝ} (hn : 0 ≤ n) (hW : 1 ≤ W) (hc₀ : 0 < c₀)
    (hnT : n ≤ T * W) :
    n / 2 * Real.exp (-(c₀ * (2 * W))) ≤ T / 2 * (5040 / (2 * c₀) ^ 7) * W ^ (-(6 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hT : 0 ≤ T := by
    by_contra h
    have : T * W < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) hW0
    linarith
  have hx : 0 ≤ c₀ * (2 * W) := by positivity
  have he := Real.pow_div_factorial_le_exp _ hx 7
  have hfac : ((7 : ℕ).factorial : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hfac] at he
  have hpos : 0 < (c₀ * (2 * W)) ^ 7 := by positivity
  have hexp : Real.exp (-(c₀ * (2 * W))) ≤ 5040 / (c₀ * (2 * W)) ^ 7 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact he
  have hrw : W ^ (-(6 : ℝ)) = (W ^ 6)⁻¹ := by
    rw [Real.rpow_neg hW0.le]; norm_cast
  rw [hrw]
  have h1 : n / 2 * Real.exp (-(c₀ * (2 * W))) ≤ T * W / 2 * (5040 / (c₀ * (2 * W)) ^ 7) := by
    have := mul_le_mul (div_le_div_of_nonneg_right hnT (by norm_num : (0 : ℝ) ≤ 2)) hexp
      (Real.exp_pos _).le (by positivity)
    linarith
  refine h1.trans (le_of_eq ?_)
  field_simp

/-- For any event `Ω` of the split space, the pair-law expectation of the indicator of its
measurable hull (for `P♯ = splitPairLaw`) at the reconstructed Gaussian is `P♯(Ω)`. -/
theorem pairExpect_hull_eq (hC : CoareaContract) {model : p.GaussianRingModel}
    {Pω : Measure (SplitState p i)} (hPω : IsPairSplitting p i model (splitS p) Pω)
    {U : FrameMap p i} (hU : IsPairFrame p i U) (α : Fin p.N)
    (Ω : Set (SplitState p i × PairMatrix p i)) :
    pairExpect α (splitS p) U Pω (fun θ G' =>
        (toMeasurable (splitPairLaw p i α Pω) Ω).indicator 1
          (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G')) =
      splitPairLaw p i α Pω Ω := by
  rw [pairExpect_indicator_eq hC hPω hU α (measurableSet_toMeasurable _ _),
    measure_toMeasurable]

end BlockBand.DeterminantScore.WeightedTrace
