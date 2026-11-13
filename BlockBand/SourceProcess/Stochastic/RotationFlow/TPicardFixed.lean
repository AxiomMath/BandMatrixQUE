module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.TPicardContract
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Strong solutions on a finite horizon, time-dependent coefficients

Time-inhomogeneous version of the Picard fixed point. Coefficients `c : TLipCoeff κ E`,
`ξ` is `F_0 ∨ N`-measurable.

* `exists_tPicardMap_fixed`: the Picard map has a fixed point (`SDE.picard_fixedPoint`).
* `TStrongSolOn μ N b σ ξ X`: `X` is `F_t ∨ N`-adapted with everywhere continuous paths,
  `X_0 = ξ`, and a.s. for all `t ≤ N`,
  `X_t = ξ + ∫_0^t b(s, X_s) ds + ∑_j M^j_t e_j`, `M^j` the horizon-`N` continuous integral of
  `ℓ_j(σ(s, X_s))`.
* `exists_tStrongSolOn`: such a solution exists.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.NativeSDE

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (c : TLipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
  (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ)

/-- **Fixed point of the time-dependent Picard map.** -/
theorem exists_tPicardMap_fixed : ∃ Z : PicardSpace (κ := κ) μ N E, tPicardMap c hξ Z = Z := by
  have hmono : ∀ x y : PicardSpace (κ := κ) μ N E,
      MonotoneOn (fun t => picardDelta t x y) (Icc 0 (N : ℝ)) := by
    intro x y s _ s' hs' hss'
    refine ENNReal.toReal_mono (picardGap_lt_top x y ?_).ne
      (picardGap_mono x y (Real.toNNReal_mono hss'))
    rw [Real.toNNReal_le_iff_le_coe]
    exact hs'.2
  have hδT : ∀ x y : PicardSpace (κ := κ) μ N E, picardDelta (N : ℝ) x y = dist x y ^ 2 := by
    intro x y
    unfold picardDelta picardGap
    rw [Real.toNNReal_coe, Subtype.dist_eq, dist_eq_norm, norm_sq_Lp_eq]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (x : Lp E 2 (timeProbMeasure N (driverLaw (κ := κ) μ)))
      (y : Lp E 2 (timeProbMeasure N (driverLaw (κ := κ) μ)))] with p hp
    rw [hp, Pi.sub_apply]
  have hΓ : ∀ x y : PicardSpace (κ := κ) μ N E, ∀ t ∈ Icc 0 (N : ℝ),
      picardDelta t (tPicardMap c hξ x) (tPicardMap c hξ y) ≤
        (tPicardConst c N).toReal * ∫ s in (0 : ℝ)..t, picardDelta s x y := by
    intro x y t ht
    have htN : t.toNNReal ≤ N := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact ht.2
    have h := tPicardGap_map_le c hξ x y htN
    rw [Real.coe_toNNReal _ ht.1] at h
    rw [integral_picardDelta x y ht, ← ENNReal.toReal_mul]
    have hfin : ∫⁻ s in Ioc 0 t, picardGap x y s.toNNReal ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (picardGap_lt_top x y le_rfl).ne
        (ENNReal.ofReal_ne_top (r := t))) ?_
      calc ∫⁻ s in Ioc 0 t, picardGap x y s.toNNReal ≤ ∫⁻ _ in Ioc 0 t, picardGap x y N :=
            setLIntegral_mono' measurableSet_Ioc fun s hs => picardGap_mono x y (by
              rw [Real.toNNReal_le_iff_le_coe]
              exact hs.2.trans ht.2)
        _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (tPicardConst_ne_top c) hfin) h
  obtain ⟨Z, hZ, -, -⟩ := SDE.picard_fixedPoint (Γ := tPicardMap c hξ) (δ := picardDelta)
    ENNReal.toReal_nonneg N.2 (fun _ _ _ _ => ENNReal.toReal_nonneg) hmono hδT hΓ
  exact ⟨Z, hZ⟩

variable (μ) in
/-- Strong pathwise solution on the horizon `N`, time-dependent coefficients. -/
def TStrongSolOn (N : ℝ≥0) (b : ℝ≥0 → E → E) (σ : κ → ℝ≥0 → E → E) (ξ : DriverSample S κ → E)
    (X : ℝ≥0 → DriverSample S κ → E) : Prop :=
  (∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t)) ∧
    (∀ x, Continuous fun t => X t x) ∧ (∀ x, X 0 x = ξ x) ∧
    ∃ hg : ∀ j, NativeIntegrand μ N
        (fun a p => coordCLM E j (σ a p.1.toNNReal (X p.1.toNNReal p.2))),
      ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ N, X t x = ξ x +
        (∫ s in Ioc (0 : ℝ) t, b s.toNNReal (X s.toNNReal x)) +
          ∑ j, nativeAdaptedLimit μ N (hg j).family t x • Module.finBasis ℝ E j

include hξ in
/-- **Existence on a finite horizon** for time-dependent Lipschitz bounded coefficients. -/
theorem exists_tStrongSolOn : ∃ X, TStrongSolOn μ N c.b c.σ ξ X := by
  classical
  obtain ⟨Z, hZ⟩ := exists_tPicardMap_fixed c hξ (N := N)
  have hrep := rep_tPicardMap c hξ Z
  rw [hZ] at hrep
  obtain ⟨G, hGm, hG0, hGc⟩ := exists_good_set μ (ae_continuous_tPicardNoise c hξ Z)
  have hGae : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hG0
  set X : ℝ≥0 → DriverSample S κ → E := fun t x =>
    ξ x + G.indicator (fun x => tPicardProc c hξ Z t x) x with hXdef
  have hX0 : ∀ x, X 0 x = ξ x := by
    intro x
    have hp : tPicardProc c hξ Z 0 x = 0 := by
      simp only [tPicardProc, tPicardDrift, min_eq_left (zero_le : (0 : ℝ≥0) ≤ N),
        NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure, zero_add]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [tPicardNoise, nativeAdaptedLimit_initial, Pi.zero_apply, zero_smul]
    simp only [hXdef]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, hp, add_zero]
    · rw [Set.indicator_of_notMem hx, add_zero]
  have hXae : ∀ᵐ p ∂timeProbMeasure N (driverLaw (κ := κ) μ),
      ξ p.2 + rep Z p = X p.1.toNNReal p.2 := by
    filter_upwards [hrep, ae_timeProb_of_ae (T := N) hGae] with p h1 h2
    simp only [hXdef, Set.indicator_of_mem h2, h1]
  have hg : ∀ j, NativeIntegrand μ N
      (fun a p => coordCLM E j (c.σ a p.1.toNNReal (X p.1.toNNReal p.2))) := fun j =>
    NativeIntegrand.congr (nativeIntegrand_tPicardNoiseFun c hξ Z j) fun a => by
      filter_upwards [hXae] with p hp
      simp only [tPicardNoiseFun, hp]
  have hfam : ∀ j, tPicardNoise c hξ Z j = nativeAdaptedLimit μ N (hg j).family := fun j => by
    unfold tPicardNoise
    rw [NativeIntegrand.family_congr (nativeIntegrand_tPicardNoiseFun c hξ Z j) (hg j)
      fun a => by
        filter_upwards [hXae] with p hp
        simp only [tPicardNoiseFun, hp]]
  have hdrift : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ N,
      tPicardDrift c ξ Z t x = ∫ s in Ioc (0 : ℝ) t, c.b s.toNNReal (X s.toNNReal x) := by
    filter_upwards [ae_ae_of_ae_timeProb hXae] with x hx t ht
    unfold tPicardDrift
    rw [min_eq_left ht]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hx' := (ae_restrict_iff' measurableSet_Ioc).1 hx
    filter_upwards [hx'] with s hs hst
    rw [hs (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 ht) hst)]
  refine ⟨X, ⟨fun t => ?_, fun x => ?_, hX0, hg, ?_⟩⟩
  · exact (hξ.mono ((driverAugmented (κ := κ) μ).mono zero_le)).add
      ((stronglyMeasurable_tPicardProc c hξ Z t).indicator
        (measurableSet_aug_of_full μ hGm hG0 t))
  · by_cases hx : x ∈ G
    · have h1 : (fun t => X t x) = fun t => ξ x + tPicardProc c hξ Z t x := by
        funext t
        simp only [hXdef, Set.indicator_of_mem hx]
      rw [h1]
      exact continuous_const.add ((continuous_tPicardDrift c hξ Z x).add
        (continuous_finsetSum _ fun j _ => (hGc x hx j).smul continuous_const))
    · have h1 : (fun t => X t x) = fun _ => ξ x := by
        funext t
        simp only [hXdef, Set.indicator_of_notMem hx, add_zero]
      rw [h1]
      exact continuous_const
  · filter_upwards [hGae, hdrift] with x hxG hxd t ht
    have h1 : X t x = ξ x + tPicardProc c hξ Z t x := by
      simp only [hXdef, Set.indicator_of_mem hxG]
    rw [h1, tPicardProc, hxd t ht, add_assoc]
    simp only [hfam]

end BlockBand.SourceProcess.Stochastic.RotationFlow
