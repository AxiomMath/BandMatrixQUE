module
public import BlockBand.SourceProcess.Stochastic.SDE.NativePicardContract
public import BlockBand.SourceProcess.Stochastic.SDE.Picard
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Strong solutions on a finite horizon for Lipschitz bounded coefficients

`Ω = DriverSample S κ`, `P = driverLaw μ`, horizon `N`, augmented filtration `F_t ∨ N`.
Coefficients `c : LipCoeff κ E` (globally `K`-Lipschitz, bounded by `C`), `ξ` is
`F_0 ∨ N`-measurable (no integrability).

* `exists_picardMap_fixed`: the Picard map has a fixed point (`SDE.picard_fixedPoint` with
  `δ_t = Q_t.toReal`, contraction `picardGap_map_le`).
* `StrongSolOn μ N b σ ξ X`: `X` is `F_t ∨ N`-adapted with **everywhere** continuous paths,
  `X_0 = ξ`, and a.s. for all `t ≤ N`,
  `X_t = ξ + ∫_0^t b(X_s) ds + ∑_j M^j_t e_j`, `M^j` the horizon-`N` continuous integral of
  `ℓ_j(σ(X))` (`ℓ_j`, `e_j`: coordinates and vectors of `Module.finBasis ℝ E`).
* `exists_strongSolOn`: such a solution exists (fixed point, modified on a null set).
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Real Volterra gap `δ_s = Q_s.toReal`. -/
def picardDelta {N : ℝ≥0} (s : ℝ) (Z Z' : PicardSpace (κ := κ) μ N E) : ℝ :=
  (picardGap Z Z' s.toNNReal).toReal

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem measurable_picardGap {N : ℝ≥0} (Z Z' : PicardSpace (κ := κ) μ N E) :
    Measurable fun s : ℝ => picardGap Z Z' s.toNNReal :=
  Monotone.measurable fun _ _ h => picardGap_mono Z Z' (Real.toNNReal_mono h)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem integral_picardDelta {N : ℝ≥0} (Z Z' : PicardSpace (κ := κ) μ N E) {t : ℝ}
    (ht : t ∈ Icc 0 (N : ℝ)) :
    ∫ s in (0 : ℝ)..t, picardDelta s Z Z' =
      (∫⁻ s in Ioc 0 t, picardGap Z Z' s.toNNReal).toReal := by
  rw [intervalIntegral.integral_of_le ht.1]
  refine integral_toReal (measurable_picardGap Z Z').aemeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  refine picardGap_lt_top Z Z' ?_
  rw [Real.toNNReal_le_iff_le_coe]
  exact hs.2.trans ht.2

variable (c : LipCoeff κ E) {N : ℝ≥0} {ξ : DriverSample S κ → E}
  (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ)

/-- **Fixed point of the Picard map.** -/
theorem exists_picardMap_fixed : ∃ Z : PicardSpace (κ := κ) μ N E, picardMap c hξ Z = Z := by
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
      picardDelta t (picardMap c hξ x) (picardMap c hξ y) ≤
        (picardConst c N).toReal * ∫ s in (0 : ℝ)..t, picardDelta s x y := by
    intro x y t ht
    have htN : t.toNNReal ≤ N := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact ht.2
    have h := picardGap_map_le c hξ x y htN
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
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (picardConst_ne_top c) hfin) h
  obtain ⟨Z, hZ, -, -⟩ := SDE.picard_fixedPoint (Γ := picardMap c hξ) (δ := picardDelta)
    ENNReal.toReal_nonneg N.2 (fun _ _ _ _ => ENNReal.toReal_nonneg) hmono hδT hΓ
  exact ⟨Z, hZ⟩

variable (μ) in
/-- Strong pathwise solution on the horizon `N` (see the module docstring). -/
def StrongSolOn (N : ℝ≥0) (b : E → E) (σ : κ → E → E) (ξ : DriverSample S κ → E)
    (X : ℝ≥0 → DriverSample S κ → E) : Prop :=
  (∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t)) ∧
    (∀ x, Continuous fun t => X t x) ∧ (∀ x, X 0 x = ξ x) ∧
    ∃ hg : ∀ j, NativeIntegrand μ N (fun a p => coordCLM E j (σ a (X p.1.toNNReal p.2))),
      ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ N, X t x = ξ x +
        (∫ s in Ioc (0 : ℝ) t, b (X s.toNNReal x)) +
          ∑ j, nativeAdaptedLimit μ N (hg j).family t x • Module.finBasis ℝ E j

include hξ in
/-- **Existence on a finite horizon** for Lipschitz bounded coefficients. -/
theorem exists_strongSolOn : ∃ X, StrongSolOn μ N c.b c.σ ξ X := by
  classical
  obtain ⟨Z, hZ⟩ := exists_picardMap_fixed c hξ (N := N)
  have hrep := rep_picardMap c hξ Z
  rw [hZ] at hrep
  obtain ⟨G, hGm, hG0, hGc⟩ := exists_good_set μ (ae_continuous_picardNoise c hξ Z)
  have hGae : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hG0
  set X : ℝ≥0 → DriverSample S κ → E := fun t x =>
    ξ x + G.indicator (fun x => picardProc c hξ Z t x) x with hXdef
  have hX0 : ∀ x, X 0 x = ξ x := by
    intro x
    have hp : picardProc c hξ Z 0 x = 0 := by
      simp only [picardProc, picardDrift, min_eq_left (zero_le : (0 : ℝ≥0) ≤ N),
        NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure, zero_add]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [picardNoise, nativeAdaptedLimit_initial, Pi.zero_apply, zero_smul]
    simp only [hXdef]
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, hp, add_zero]
    · rw [Set.indicator_of_notMem hx, add_zero]
  have hXae : ∀ᵐ p ∂timeProbMeasure N (driverLaw (κ := κ) μ),
      ξ p.2 + rep Z p = X p.1.toNNReal p.2 := by
    filter_upwards [hrep, ae_timeProb_of_ae (T := N) hGae] with p h1 h2
    simp only [hXdef, Set.indicator_of_mem h2, h1]
  have hg : ∀ j, NativeIntegrand μ N
      (fun a p => coordCLM E j (c.σ a (X p.1.toNNReal p.2))) := fun j =>
    NativeIntegrand.congr (nativeIntegrand_picardNoiseFun c hξ Z j) fun a => by
      filter_upwards [hXae] with p hp
      simp only [picardNoiseFun, hp]
  have hfam : ∀ j, picardNoise c hξ Z j = nativeAdaptedLimit μ N (hg j).family := fun j => by
    unfold picardNoise
    rw [NativeIntegrand.family_congr (nativeIntegrand_picardNoiseFun c hξ Z j) (hg j)
      fun a => by
        filter_upwards [hXae] with p hp
        simp only [picardNoiseFun, hp]]
  have hdrift : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ N,
      picardDrift c ξ Z t x = ∫ s in Ioc (0 : ℝ) t, c.b (X s.toNNReal x) := by
    filter_upwards [ae_ae_of_ae_timeProb hXae] with x hx t ht
    unfold picardDrift
    rw [min_eq_left ht]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hx' := (ae_restrict_iff' measurableSet_Ioc).1 hx
    filter_upwards [hx'] with s hs hst
    rw [hs (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 ht) hst)]
  refine ⟨X, ⟨fun t => ?_, fun x => ?_, hX0, hg, ?_⟩⟩
  · exact (hξ.mono ((driverAugmented (κ := κ) μ).mono zero_le)).add
      ((stronglyMeasurable_picardProc c hξ Z t).indicator (measurableSet_aug_of_full μ hGm hG0 t))
  · by_cases hx : x ∈ G
    · have h1 : (fun t => X t x) = fun t => ξ x + picardProc c hξ Z t x := by
        funext t
        simp only [hXdef, Set.indicator_of_mem hx]
      rw [h1]
      exact continuous_const.add ((continuous_picardDrift c hξ Z x).add
        (continuous_finsetSum _ fun j _ => (hGc x hx j).smul continuous_const))
    · have h1 : (fun t => X t x) = fun _ => ξ x := by
        funext t
        simp only [hXdef, Set.indicator_of_notMem hx, add_zero]
      rw [h1]
      exact continuous_const
  · filter_upwards [hGae, hdrift] with x hxG hxd t ht
    have h1 : X t x = ξ x + picardProc c hξ Z t x := by
      simp only [hXdef, Set.indicator_of_mem hxG]
    rw [h1, picardProc, hxd t ht, add_assoc]
    simp only [hfam]

end BlockBand.SourceProcess.Stochastic.NativeSDE
