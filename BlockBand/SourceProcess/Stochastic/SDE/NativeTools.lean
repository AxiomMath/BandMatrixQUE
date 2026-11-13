module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeHorizon
public import BlockBand.SourceProcess.Stochastic.Integral.PredictableContinuous
public import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# SDE toolkit: linearity, isometry, augmentation, predictability

Sample space `Ω = DriverSample S κ`, `P = driverLaw μ`, `ν = timeProbMeasure T P`
(`dt ⊗ P` on `(0,T]`), augmented filtration `F_t ∨ N` (`driverAugmented μ`).

* Linearity of the terminal integral in the integrand function
  (`nativeIntegralOf_add`, `nativeIntegralOf_sub`, `nativeIntegralOf_const_mul`,
  `exists_nativeIntegralOf_sum`).
* Itô isometry in function form (`integral_sq_nativeIntegralOf`,
  `lintegral_sq_nativeIntegralOf`): `E (∫ g dW)² = ∑_a ∫ g_a² d(dt ⊗ P)`.
* Augmentation: ambient-measurable functions a.e. equal to `F_t ∨ N`-measurable ones are
  `F_t ∨ N`-measurable (`stronglyMeasurable_aug_of_ae_eq`); every a.e. property holds on a
  measurable full-measure set (`exists_good_set`), which is `F_0 ∨ N`-measurable.
* `aesm_stoppedFun`: for an `E`-valued augmented-adapted a.s. continuous `Y` and an
  augmented stopping time `τ`, `(s,x) ↦ 1{s ≤ τ x} Y_s x` is a.e. raw predictable on `ν`
  (coordinatewise reduction to `aestronglyMeasurable_stoppedComposite`).
* `lintegral_sq_le_measure_mul`: Cauchy–Schwarz `(∫⁻ h)² ≤ m(univ) ∫⁻ h²`.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

section Linear

variable {g h : κ → ℝ × DriverSample S κ → ℝ}

omit [IsProbabilityMeasure μ] in
theorem nativeIntegrand_add (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    NativeIntegrand μ T (fun c p => g c p + h c p) := fun c =>
  ⟨(hg c).1.add (hh c).1, (hg c).2.add (hh c).2⟩

omit [IsProbabilityMeasure μ] in
theorem nativeIntegrand_sub (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    NativeIntegrand μ T (fun c p => g c p - h c p) := fun c =>
  ⟨(hg c).1.sub (hh c).1, (hg c).2.sub (hh c).2⟩

omit [IsProbabilityMeasure μ] in
theorem nativeIntegrand_const_mul (hg : NativeIntegrand μ T g) (r : ℝ) :
    NativeIntegrand μ T (fun c p => r * g c p) := fun c =>
  ⟨(hg c).1.const_mul r, (hg c).2.const_mul r⟩

omit [IsProbabilityMeasure μ] in
theorem nativeIntegrand_zero :
    NativeIntegrand μ T (fun (_ : κ) (_ : ℝ × DriverSample S κ) => (0 : ℝ)) := fun _ =>
  ⟨aestronglyMeasurable_const, MemLp.zero⟩

omit [IsProbabilityMeasure μ] in
theorem family_add (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    (nativeIntegrand_add hg hh).family = hg.family + hh.family := by
  obtain ⟨hs, he⟩ := nativeIntegrand_of_family (G := fun c p => g c p + h c p)
    (hg.family + hh.family) (fun c => by
      filter_upwards [Lp.coeFn_add (((hg.family c : ScalarPredictable (κ := κ) μ T)) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))
          (((hh.family c : ScalarPredictable (κ := κ) μ T)) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))),
        nativeIntegrand_family_coeFn hg c, nativeIntegrand_family_coeFn hh c] with p h1 h2 h3
      change ((((hg.family c : ScalarPredictable (κ := κ) μ T)) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) +
          (((hh.family c : ScalarPredictable (κ := κ) μ T)) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : _ → ℝ) p = _
      rw [h1, Pi.add_apply, h2, h3])
  exact he

omit [IsProbabilityMeasure μ] in
theorem family_const_mul (hg : NativeIntegrand μ T g) (r : ℝ) :
    (nativeIntegrand_const_mul hg r).family = r • hg.family := by
  obtain ⟨hs, he⟩ := nativeIntegrand_of_family (G := fun c p => r * g c p)
    (r • hg.family) (fun c => by
      filter_upwards [Lp.coeFn_smul r (((hg.family c : ScalarPredictable (κ := κ) μ T)) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))),
        nativeIntegrand_family_coeFn hg c] with p h1 h2
      change ((r • ((hg.family c : ScalarPredictable (κ := κ) μ T)) :
          Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : _ → ℝ) p = _
      rw [h1, Pi.smul_apply, h2, smul_eq_mul])
  exact he

theorem nativeIntegralOf_add (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    nativeIntegralOf (nativeIntegrand_add hg hh) = nativeIntegralOf hg + nativeIntegralOf hh := by
  unfold nativeIntegralOf
  rw [family_add, map_add]

theorem nativeIntegralOf_const_mul (hg : NativeIntegrand μ T g) (r : ℝ) :
    nativeIntegralOf (nativeIntegrand_const_mul hg r) = r • nativeIntegralOf hg := by
  unfold nativeIntegralOf
  rw [family_const_mul, map_smul]

theorem nativeIntegralOf_sub (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    nativeIntegralOf (nativeIntegrand_sub hg hh) = nativeIntegralOf hg - nativeIntegralOf hh := by
  have h1 := nativeIntegralOf_add hg (nativeIntegrand_const_mul hh (-1))
  rw [nativeIntegralOf_const_mul hh (-1), neg_one_smul, ← sub_eq_add_neg] at h1
  rw [← h1]
  exact nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p => by
    simp only [sub_eq_add_neg, neg_one_mul]

theorem nativeIntegralOf_zero :
    nativeIntegralOf (nativeIntegrand_zero (μ := μ) (T := T) (κ := κ)) = 0 := by
  have h := nativeIntegralOf_const_mul (nativeIntegrand_zero (μ := μ) (T := T) (κ := κ)) 0
  rw [zero_smul] at h
  rw [← h]
  exact nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p => by simp

/-- Finite linear combinations of integrands. -/
theorem exists_nativeIntegralOf_sum {ι : Type*} (s : Finset ι)
    {G : ι → κ → ℝ × DriverSample S κ → ℝ} (hG : ∀ i, NativeIntegrand μ T (G i)) (r : ι → ℝ) :
    ∃ hs : NativeIntegrand μ T (fun c p => ∑ i ∈ s, r i * G i c p),
      nativeIntegralOf hs = ∑ i ∈ s, r i • nativeIntegralOf (hG i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨nativeIntegrand_zero, nativeIntegralOf_zero⟩
  | insert a s ha ih =>
    obtain ⟨hs, he⟩ := ih
    have hs' := nativeIntegrand_add (nativeIntegrand_const_mul (hG a) (r a)) hs
    refine ⟨fun c => ⟨(hs' c).1.congr (Eventually.of_forall fun p => ?_),
      (hs' c).2.congr_norm ?_ ?_⟩, ?_⟩
    · simp only [Finset.sum_insert ha]
    · exact (hs' c).1.congr (Eventually.of_forall fun p => by simp only [Finset.sum_insert ha]) |>.mono
        (predictableSpace_le _)
    · exact Eventually.of_forall fun p => by simp only [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha, ← he, ← nativeIntegralOf_const_mul, ← nativeIntegralOf_add]
      exact nativeIntegralOf_congr _ _ fun c => Eventually.of_forall fun p => by
        simp only [Finset.sum_insert ha]

end Linear

section Isometry

theorem integral_sq_eq_norm_sq {α : Type*} [MeasurableSpace α] {m : Measure α}
    (F : Lp ℝ 2 m) : ∫ x, ((F : α → ℝ) x) ^ 2 ∂m = ‖F‖ ^ 2 := by
  have h := norm_sq_toLp (Lp.memLp F)
  rw [Lp.toLp_coeFn] at h
  exact h.symm

theorem lintegral_enorm_sq_eq_ofReal {α : Type*} [MeasurableSpace α] {m : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 m) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m = ENNReal.ofReal (∫ x, (f x) ^ 2 ∂m) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- **Itô isometry** for integrands: `E (∫ g dW)² = ∑_a ∫ g_a² d(dt ⊗ P)`. -/
theorem integral_sq_nativeIntegralOf {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) :
    ∫ x, ((nativeIntegralOf hg : DriverSample S κ → ℝ) x) ^ 2 ∂driverLaw (κ := κ) μ =
      ∑ c, ∫ p, (g c p) ^ 2 ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
  rw [integral_sq_eq_norm_sq]
  unfold nativeIntegralOf
  rw [LinearIsometry.norm_map, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun c _ => ?_
  change ‖(hg c).2.toLp (g c)‖ ^ 2 = _
  exact norm_sq_toLp (hg c).2

theorem lintegral_sq_nativeIntegralOf {g : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) :
    ∫⁻ x, ‖(nativeIntegralOf hg : DriverSample S κ → ℝ) x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ =
      ∑ c, ∫⁻ p, ‖g c p‖ₑ ^ 2 ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
  rw [lintegral_enorm_sq_eq_ofReal (Lp.memLp _), integral_sq_nativeIntegralOf,
    ENNReal.ofReal_sum_of_nonneg fun c _ => integral_nonneg fun p => sq_nonneg _]
  exact Finset.sum_congr rfl fun c _ => (lintegral_enorm_sq_eq_ofReal (hg c).2).symm

end Isometry

section CauchySchwarz

/-- Cauchy–Schwarz for `ℝ≥0∞`-valued functions: `(∫⁻ h)² ≤ m(univ) ∫⁻ h²`. -/
theorem lintegral_sq_le_measure_mul {α : Type*} [MeasurableSpace α] {m : Measure α}
    {h : α → ℝ≥0∞} (hh : AEMeasurable h m) :
    (∫⁻ x, h x ∂m) ^ 2 ≤ m Set.univ * ∫⁻ x, h x ^ 2 ∂m := by
  have key := ENNReal.lintegral_mul_norm_pow_le (μ := m) (g := fun _ => (1 : ℝ≥0∞)) (hh.pow_const 2)
    aemeasurable_const
    (p := (2 : ℕ)⁻¹) (q := (2 : ℕ)⁻¹) (by norm_num) (by norm_num) (by norm_num)
  have hl : ∀ x, (h x ^ 2) ^ ((2 : ℕ)⁻¹ : ℝ) * (1 : ℝ≥0∞) ^ ((2 : ℕ)⁻¹ : ℝ) = h x := fun x => by
    rw [ENNReal.one_rpow, mul_one, ENNReal.pow_rpow_inv_natCast two_ne_zero]
  simp only [hl, lintegral_const, one_mul] at key
  calc (∫⁻ x, h x ∂m) ^ 2
      ≤ ((∫⁻ x, h x ^ 2 ∂m) ^ ((2 : ℕ)⁻¹ : ℝ) * m Set.univ ^ ((2 : ℕ)⁻¹ : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le key 2
    _ = m Set.univ * ∫⁻ x, h x ^ 2 ∂m := by
        rw [mul_pow, ENNReal.rpow_inv_natCast_pow two_ne_zero,
          ENNReal.rpow_inv_natCast_pow two_ne_zero, mul_comm]

end CauchySchwarz

section Augmentation

variable (μ)

omit [IsProbabilityMeasure μ] in
/-- Ambient-measurable null sets are augmented events at every time. -/
theorem measurableSet_aug_of_null {N : Set (DriverSample S κ)} (hN : MeasurableSet N)
    (h0 : driverLaw (κ := κ) μ N = 0) (t : ℝ≥0) :
    MeasurableSet[driverAugmented (κ := κ) μ t] N :=
  (le_sup_right : nullSigma (driverLaw (κ := κ) μ) ≤ _) _
    (MeasurableSpace.measurableSet_generateFrom ⟨hN, h0⟩)

omit [IsProbabilityMeasure μ] in
/-- Every a.e. property holds on a measurable set of full measure. -/
theorem exists_good_set {q : DriverSample S κ → Prop}
    (hq : ∀ᵐ x ∂driverLaw (κ := κ) μ, q x) :
    ∃ G : Set (DriverSample S κ), MeasurableSet G ∧ driverLaw (κ := κ) μ Gᶜ = 0 ∧
      ∀ x ∈ G, q x := by
  refine ⟨(toMeasurable (driverLaw (κ := κ) μ) {x | ¬ q x})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun x hx => ?_⟩
  · rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hq
  · by_contra hn
    exact hx (subset_toMeasurable _ _ hn)

omit [IsProbabilityMeasure μ] in
theorem measurableSet_aug_of_full {G : Set (DriverSample S κ)} (hG : MeasurableSet G)
    (h0 : driverLaw (κ := κ) μ Gᶜ = 0) (t : ℝ≥0) :
    MeasurableSet[driverAugmented (κ := κ) μ t] G := by
  have := measurableSet_aug_of_null μ hG.compl h0 t
  rw [← compl_compl G]
  exact this.compl

variable {μ}
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [IsProbabilityMeasure μ] in
/-- An ambient-measurable function a.e. equal to an `F_t ∨ N`-measurable one is
`F_t ∨ N`-measurable. -/
theorem stronglyMeasurable_aug_of_ae_eq {t : ℝ≥0} {f g : DriverSample S κ → E}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable[driverAugmented (κ := κ) μ t] g)
    (hfg : f =ᵐ[driverLaw (κ := κ) μ] g) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] f := by
  have hg' : StronglyMeasurable g := hg.mono ((driverAugmented (κ := κ) μ).le t)
  set N := {x | f x ≠ g x} with hNdef
  have hN : MeasurableSet N := (hf.measurableSet_eq_fun hg').compl
  have hN0 : driverLaw (κ := κ) μ N = 0 := ae_iff.1 hfg
  suffices hm : Measurable[driverAugmented (κ := κ) μ t] f from
    (hm : Measurable[driverAugmented (κ := κ) μ t] f).stronglyMeasurable
  intro U hU
  have he : f ⁻¹' U = (g ⁻¹' U ∩ Nᶜ) ∪ (f ⁻¹' U ∩ N) := by
    ext x
    by_cases hx : x ∈ N
    · simp [hx]
    · have hfx : f x = g x := by simpa [hNdef] using hx
      simp [hx, hfx]
  rw [he]
  refine (MeasurableSet.inter (hg.measurable hU) (measurableSet_aug_of_null μ hN hN0 t).compl).union ?_
  exact measurableSet_aug_of_null μ ((hf.measurable hU).inter hN)
    (measure_mono_null Set.inter_subset_right hN0) t

end Augmentation

section Predictable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Finite sums preserve a.e. strong measurability for a sub-σ-algebra. -/
theorem aesm_finset_sum {α ι : Type*} {m m₀ : MeasurableSpace α} {ν : Measure[m₀] α}
    (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, AEStronglyMeasurable[m] (f i) ν) :
    AEStronglyMeasurable[m] (fun a => ∑ i ∈ s, f i a) ν := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact aestronglyMeasurable_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The stopped `E`-valued process function `(s,x) ↦ 1{s ≤ τ x} Y_s x` on `ℝ × Ω`. -/
def stoppedFun (τ : DriverSample S κ → WithTop ℝ≥0) (Y : ℝ≥0 → DriverSample S κ → E)
    (p : ℝ × DriverSample S κ) : E :=
  if ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2 then Y p.1.toNNReal p.2 else 0

/-- `E`-valued version of `aestronglyMeasurable_stoppedComposite`. -/
theorem aesm_stoppedFun {Y : ℝ≥0 → DriverSample S κ → E}
    (hY : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t))
    (hYc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y t x)
    {τ : DriverSample S κ → WithTop ℝ≥0}
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ) :
    AEStronglyMeasurable[rawPredictable S κ] (stoppedFun τ Y)
      (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
  classical
  let B := Module.finBasis ℝ E
  have hrep : stoppedFun τ Y = fun p => ∑ j, (B.coord j (stoppedFun τ Y p)) • B j := by
    funext p
    exact (B.sum_repr _).symm
  rw [hrep]
  refine aesm_finset_sum _ fun j _ => ?_
  refine AEStronglyMeasurable.smul_const ?_ _
  have hc : Continuous fun v : E => B.coord j v := LinearMap.continuous_of_finiteDimensional _
  have h := aestronglyMeasurable_stoppedComposite (T := T) hY hYc hc hτ
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [stoppedComposite, stoppedFun]
  split_ifs <;> simp

omit [IsProbabilityMeasure μ] in
theorem isStoppingTime_top :
    IsStoppingTime (driverAugmented (κ := κ) μ) (fun _ : DriverSample S κ => (⊤ : WithTop ℝ≥0)) :=
  fun i => by
    simp only [top_le_iff, WithTop.coe_ne_top, Set.ofPred_false]
    exact @MeasurableSet.empty _ (driverAugmented (κ := κ) μ i)

/-- Unstopped version: `(s,x) ↦ Y_s x` is a.e. raw predictable on `ν`. -/
theorem aesm_processFun {Y : ℝ≥0 → DriverSample S κ → E}
    (hY : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t))
    (hYc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y t x) :
    AEStronglyMeasurable[rawPredictable S κ] (fun p : ℝ × DriverSample S κ => Y p.1.toNNReal p.2)
      (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
  refine (aesm_stoppedFun hY hYc isStoppingTime_top).congr (Eventually.of_forall fun p => ?_)
  simp only [stoppedFun, le_top, ite_true]

end Predictable

end BlockBand.SourceProcess.Stochastic.NativeSDE
