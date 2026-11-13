module

public import BlockBand.Center.CenterResidualEnergy

/-!
# The `small` clause of the physical-center domain (constants `cst0`)

Law: the exact pair law `extendedPairMeasure p α i X.P X.Hm` on any extension `X` carrying the
edge splitting `G` (`IsCenterSplitting`); it has density `(n/2)(p_{αi} + p_{α,i+1}) ≤ n/2` with
respect to `X.P` (`csm_pairMeasure_le`).

Proof. Off a null set (`H` Hermitian and bond-regular, no
exterior pole at the deterministic anchor `e_α` nor at `λ_α`) the domain of `cst0` at `λ_α`
is `{λ_α ∈ I_α, ε_e(λ_α) ≤ ε₁}` (`cst0_inCenterDomain_iff`). With the deterministic window
`J = [e_α - δ, e_α + δ]`, `δ = ϑ/(2n)`:
* `λ_α ∉ J` has probability `≤ (‖λ_α - e_α‖_{q₃}/δ)^{q₃}` (Markov and the rank location
  bound, rate `(n√W)⁻¹`); on `λ_α ∈ J` one has `λ_α ∈ I_α`;
* Markov's inequality and the pair density `n/2 ≤ TW/2` give `C_q W^{1-q}`.

The domain clause only needs tail probabilities, for which the elementary window estimate
gives every power of `W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. Markov, Hölder-in-energy and the fundamental theorem of calculus
-/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Markov's inequality for a nonnegative extended function with a bounded `r`-th moment. -/
theorem csm_markov_lintegral (μ : Measure Ω) {Z : Ω → ℝ≥0∞} (hZ : AEMeasurable Z μ) {r t M : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hM : 0 ≤ M)
    (h : ∫⁻ ω, Z ω ^ r ∂μ ≤ ENNReal.ofReal (M ^ r)) :
    μ {ω | ENNReal.ofReal t ≤ Z ω} ≤ ENNReal.ofReal ((M / t) ^ r) := by
  have hsub : {ω | ENNReal.ofReal t ≤ Z ω} ⊆ {ω | ENNReal.ofReal t ^ r ≤ Z ω ^ r} :=
    fun ω hω => ENNReal.rpow_le_rpow hω hr.le
  have hmk := mul_meas_ge_le_lintegral₀ (hZ.pow_const r) (ENNReal.ofReal t ^ r)
  have htr : ENNReal.ofReal t ^ r = ENNReal.ofReal (t ^ r) :=
    ENNReal.ofReal_rpow_of_nonneg ht.le hr.le
  have htr0 : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  rw [htr] at hmk hsub
  calc μ {ω | ENNReal.ofReal t ≤ Z ω}
      ≤ μ {ω | ENNReal.ofReal (t ^ r) ≤ Z ω ^ r} := measure_mono hsub
    _ ≤ ENNReal.ofReal (M ^ r) / ENNReal.ofReal (t ^ r) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using htr0)) (Or.inl ENNReal.ofReal_ne_top),
        mul_comm]
      exact hmk.trans h
    _ = ENNReal.ofReal ((M / t) ^ r) := by
      rw [← ENNReal.ofReal_div_of_pos htr0, Real.div_rpow hM ht.le]

/-- An `L^r` bound as a bound on the `r`-th moment. -/
theorem csm_lintegral_le_of_eLpNorm (μ : Measure Ω) {E' : Type*} [NormedAddCommGroup E']
    {f : Ω → E'} (hf : AEStronglyMeasurable f μ) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (h : eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M) :
    ∫⁻ ω, ‖f ω‖ₑ ^ r ∂μ ≤ ENNReal.ofReal (M ^ r) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hr.le] at h
  have := ENNReal.rpow_le_rpow h hr.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hM hr.le] at this
  exact this

/-- Markov's inequality from an `L^r` bound. -/
theorem csm_markov (μ : Measure Ω) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {r t M : ℝ}
    (hr : 0 < r) (ht : 0 < t) (hM : 0 ≤ M)
    (h : eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M) :
    μ {ω | t ≤ |f ω|} ≤ ENNReal.ofReal ((M / t) ^ r) := by
  have h2 := csm_lintegral_le_of_eLpNorm μ hf hr hM h
  have hset : {ω | t ≤ |f ω|} = {ω | ENNReal.ofReal t ≤ ‖f ω‖ₑ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).symm
  rw [hset]
  exact csm_markov_lintegral μ hf.enorm hr ht hM h2

/-- Hölder (Jensen) in the energy on a window of finite length. -/
theorem csm_lintegral_rpow_le (ν : Measure ℝ) {r : ℝ} (hr : 1 ≤ r) {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f ν) :
    (∫⁻ t, f t ∂ν) ^ r ≤ (∫⁻ t, f t ^ r ∂ν) * (ν Set.univ) ^ (r - 1) := by
  by_cases hr1 : r = 1
  · simp [hr1]
  have hrgt : 1 < r := lt_of_le_of_ne hr (Ne.symm hr1)
  have hr0 : 0 < r := lt_trans zero_lt_one hrgt
  have hconj := Real.HolderConjugate.conjExponent hrgt
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj hf
    (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) ν)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, mul_one] at hh
  have hhpow := ENNReal.rpow_le_rpow hh hr0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hhpow
  have ha : (1 / r) * r = 1 := by field_simp
  have hb : (1 / r.conjExponent) * r = r - 1 := by
    rw [Real.conjExponent]; field_simp
  simpa only [ha, hb, ENNReal.rpow_one, one_mul] using hhpow

/-- **The window moment** (the elementary replacement of the random-energy receiver): for a
jointly measurable `D` with `∫ |D(·,E)|^r ≤ K^r` for every `E` in the window `[a, b]`,
`∫ (∫_a^b |D(·,E)| dE)^r ≤ ((b - a) K)^r`. -/
theorem csm_window_moment (μ : Measure Ω) [SFinite μ] {D : Ω × ℝ → ℂ} (hD : Measurable D)
    {a b : ℝ} {r : ℝ} (hr : 1 ≤ r) (K : ℝ≥0∞)
    (hK : ∀ E ∈ Set.Icc a b, ∫⁻ ω, ‖D (ω, E)‖ₑ ^ r ∂μ ≤ K ^ r) :
    ∫⁻ ω, (∫⁻ E in Set.Icc a b, ‖D (ω, E)‖ₑ) ^ r ∂μ ≤ (ENNReal.ofReal (b - a) * K) ^ r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  set ν : Measure ℝ := volume.restrict (Set.Icc a b) with hν
  have hνu : ν Set.univ = ENNReal.ofReal (b - a) := by
    rw [hν, Measure.restrict_apply_univ, Real.volume_Icc]
  have hDe : Measurable (fun z : Ω × ℝ => ‖D z‖ₑ) := hD.enorm
  calc ∫⁻ ω, (∫⁻ E in Set.Icc a b, ‖D (ω, E)‖ₑ) ^ r ∂μ
      ≤ ∫⁻ ω, (∫⁻ E, ‖D (ω, E)‖ₑ ^ r ∂ν) * (ν Set.univ) ^ (r - 1) ∂μ :=
        lintegral_mono fun ω => csm_lintegral_rpow_le ν hr
          (hDe.comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ = (∫⁻ E, ∫⁻ ω, ‖D (ω, E)‖ₑ ^ r ∂μ ∂ν) * (ν Set.univ) ^ (r - 1) := by
        rw [lintegral_mul_const'' _ (hDe.pow_const r).lintegral_prod_right'.aemeasurable,
          lintegral_lintegral_swap (hDe.pow_const r).aemeasurable]
    _ ≤ (∫⁻ _ in Set.Icc a b, K ^ r) * (ν Set.univ) ^ (r - 1) :=
        mul_le_mul_left (setLIntegral_mono' measurableSet_Icc hK) _
    _ = (ENNReal.ofReal (b - a) * K) ^ r := by
        have hv : ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a) ^ (r - 1) =
            ENNReal.ofReal (b - a) ^ r := by
          calc ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a) ^ (r - 1)
              = ENNReal.ofReal (b - a) ^ (1 : ℝ) * ENNReal.ofReal (b - a) ^ (r - 1) := by
                rw [ENNReal.rpow_one]
            _ = ENNReal.ofReal (b - a) ^ (1 + (r - 1)) :=
                (ENNReal.rpow_add_of_nonneg 1 (r - 1) (by norm_num) (by linarith)).symm
            _ = ENNReal.ofReal (b - a) ^ r := by congr 1; ring
        rw [setLIntegral_const, Real.volume_Icc, hνu, ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
          mul_assoc, hv, mul_comm]

/-- A finite window moment gives a.e. integrability on the window. -/
theorem csm_window_integrableOn_ae (μ : Measure Ω) {D : Ω × ℝ → ℂ} (hD : Measurable D)
    {a b : ℝ} {r : ℝ} (hr : 0 < r)
    (hfin : ∫⁻ ω, (∫⁻ E in Set.Icc a b, ‖D (ω, E)‖ₑ) ^ r ∂μ ≠ ⊤) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun E => D (ω, E)) (Set.Icc a b) := by
  have hZ : Measurable (fun ω => ∫⁻ E in Set.Icc a b, ‖D (ω, E)‖ₑ) :=
    hD.enorm.lintegral_prod_right'
  filter_upwards [ae_lt_top (hZ.pow_const r) hfin] with ω hω
  have hfin' : (∫⁻ E in Set.Icc a b, ‖D (ω, E)‖ₑ) < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos hr).mp hω
  exact ⟨(hD.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr hfin'⟩

/-- **Fundamental theorem of calculus on a window**: `|f(l) - f(e)| ≤ ∫_J |f'|` for `e, l ∈ J`. -/
theorem csm_ftc_enorm_le {f d : ℝ → ℂ} {a b e l : ℝ} (he : e ∈ Set.Icc a b)
    (hl : l ∈ Set.Icc a b) (hderiv : ∀ E ∈ Set.Icc a b, HasDerivAt f (d E) E)
    (hint : IntegrableOn d (Set.Icc a b)) :
    ‖f l - f e‖ₑ ≤ ∫⁻ E in Set.Icc a b, ‖d E‖ₑ := by
  have hsub : Set.uIcc e l ⊆ Set.Icc a b := Set.uIcc_subset_Icc he hl
  have hii : IntervalIntegrable d volume e l := (hint.mono_set hsub).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun E hE => hderiv E (hsub hE)) hii
  rw [← hftc]
  have hn : ‖∫ E in e..l, d E‖ₑ = ‖∫ E in Set.uIoc e l, d E‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, intervalIntegral.norm_intervalIntegral_eq]
  rw [hn]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_mono_set (Set.uIoc_subset_uIcc.trans hsub))

/-- Splitting a threshold over three terms. -/
theorem csm_split3 {t a b c : ℝ≥0∞} (h : t + t + t ≤ a + b + c) : t ≤ a ∨ t ≤ b ∨ t ≤ c := by
  by_contra hne
  simp only [not_or, not_le] at hne
  exact absurd h (not_le.mpr (ENNReal.add_lt_add (ENNReal.add_lt_add hne.1 hne.2.1) hne.2.2))

end Generic

/-!
## 2. The pair law on an extension
-/

section PairLaw

variable {p : Parameters} {model : p.GaussianRingModel} {α : Fin p.N} {i : ZMod p.n}

/-- The pair law has density at most `n/2` with respect to the extension law. -/
theorem csm_pairMeasure_le (X : PairExtension p model) :
    extendedPairMeasure p α i X.P X.Hm ≤ ENNReal.ofReal ((p.n : ℝ) / 2) • X.P := by
  unfold extendedPairMeasure
  rw [← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [csm_ae_ext_of_law X (physicalOrderedBlockMass_sum_ae p model)] with ω hω
  have hle : physicalOrderedBlockMass p (X.Hm ω) α i +
      physicalOrderedBlockMass p (X.Hm ω) α (i + 1) ≤ 1 := by
    rw [← hω α, ← Finset.sum_pair (BlockBand.Layers.rng_add_one_ne p i).symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => physicalOrderedBlockMass_nonneg _ _ _ _)
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  change (p.n : ℝ) / 2 * (_ + _) ≤ _
  have : (0 : ℝ) ≤ p.n / 2 := by positivity
  nlinarith

theorem csm_pairMeasure_apply_le (X : PairExtension p model) (A : Set X.Ω) :
    extendedPairMeasure p α i X.P X.Hm A ≤ ENNReal.ofReal ((p.n : ℝ) / 2) * X.P A := by
  have h := (Measure.le_iff'.mp (csm_pairMeasure_le (α := α) (i := i) X)) A
  simpa using h

/-- The image of the extended pair law under `Hm` is the physical pair law. -/
theorem csm_map_pairMeasure (X : PairExtension p model) :
    (extendedPairMeasure p α i X.P X.Hm).map X.Hm = physicalPairMeasure p model α i := by
  ext A hA
  rw [Measure.map_apply X.measurable_Hm hA]
  unfold extendedPairMeasure physicalPairMeasure
  rw [withDensity_apply _ (X.measurable_Hm hA), withDensity_apply _ hA, ← X.map_eq,
    Measure.restrict_map X.measurable_Hm hA,
    lintegral_map (measurable_physicalPairWeight p α i).coe_nnreal_ennreal X.measurable_Hm]

theorem csm_exteriorBlock_res (H : p.SiteMatrix) (G : PairMatrix p i) :
    exteriorBlock p i (H - embedPair p i G) = exteriorBlock p i H := by
  ext x y
  simp [exteriorBlock, embedPair, x.2]

/-- **No exterior pole at `λ_α`** under the pair law (from
`PairPoleExclusionContract.pole_probability`, `ε → 0`). -/
theorem csm_pole_null (hpole : PairPoleExclusionContract) (X : PairExtension p model)
    (G : X.Ω → PairMatrix p i) :
    extendedPairMeasure p α i X.P X.Hm {ω | (exteriorBlock p i (X.Hm ω - embedPair p i (G ω)) -
      (physicalOrderedEigenvalue p (X.Hm ω) α : ℂ) • 1).det = 0} = 0 := by
  set S := {H : p.SiteMatrix |
    (exteriorBlock p i H - (physicalOrderedEigenvalue p H α : ℂ) • 1).det = 0}
  have hset : {ω | (exteriorBlock p i (X.Hm ω - embedPair p i (G ω)) -
      (physicalOrderedEigenvalue p (X.Hm ω) α : ℂ) • 1).det = 0} = X.Hm ⁻¹' S := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S, csm_exteriorBlock_res]
  rw [hset]
  have hle := Measure.le_map_apply (μ := extendedPairMeasure p α i X.P X.Hm)
    X.measurable_Hm.aemeasurable S
  rw [csm_map_pairMeasure] at hle
  refine le_antisymm (hle.trans ?_) zero_le
  have hs : 0 < splitS p := ctr_splitS_pos
  set C := (p.n : ℝ) * (2 * p.W) * (2 * p.W + 1) / Real.sqrt (2 * Real.pi * splitS p) with hC
  have hC0 : 0 < C := by
    have : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
    have : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    have : 0 < Real.sqrt (2 * Real.pi * splitS p) := Real.sqrt_pos.mpr (by positivity)
    positivity
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have h := hpole.pole_probability p model α i (splitS p) hs le_rfl (ε / C) (div_pos hε' hC0)
  rw [zero_add]
  refine (measure_mono ?_).trans (h.trans (le_of_eq ?_))
  · intro H hH
    exact ⟨physicalOrderedEigenvalue p H α, hH, by
      rw [sub_self, abs_zero]; exact div_pos hε' hC0⟩
  · rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [hC]
    have : 0 < Real.sqrt (2 * Real.pi * splitS p) := Real.sqrt_pos.mpr (by positivity)
    have : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
    have : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
    field_simp

end PairLaw

/-!
## 3. The excluded set: reduction to three tail events
-/

section Core

variable {p : Parameters}

/-- Energies within `ϑ/2` of `e_α` (`ϑ`-bulk rank) lie in `(-2, 2)` and in `I_α`. -/
theorem csm_window_facts {ϑ : ℝ} (hϑ : 0 < ϑ) (α : Fin p.N) (hα : IsBulkRank p ϑ α) {E : ℝ}
    (hE : |E - classicalLocation p α| ≤ ϑ / 2) :
    |E| < 2 ∧ E ∈ bulkInterval (rankMargin p α) ∧ E ∈ bulkInterval (ϑ / 2) := by
  have he := BlockBand.RankLocation.classicalLocation_mem_bulkInterval hϑ p α hα
  have hκ := ctr_rankMargin_ge hϑ α hα
  unfold bulkInterval at he ⊢
  have h1 := abs_le.mp hE
  have hea : |classicalLocation p α| ≤ 2 - ϑ := abs_le.mpr ⟨by linarith [he.1], he.2⟩
  have hκdef : rankMargin p α = (2 - |classicalLocation p α|) / 2 := rfl
  have hle := le_abs_self (classicalLocation p α)
  have hge := neg_abs_le (classicalLocation p α)
  refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨by linarith, by linarith⟩⟩
  · rw [hκdef] at hκ ⊢; linarith
  · rw [hκdef] at hκ ⊢; linarith

variable {model : p.GaussianRingModel} {i : ZMod p.n}

/-- On an extension carrying the splitting, a.s. every `ε_{e,k}` is differentiable on `(-2,2)`
with derivative `csmDeriv`. -/
theorem csm_ae_hasDerivAt (X : PairExtension p model) {G : X.Ω → PairMatrix p i}
    (hG : IsCenterSplitting X G) :
    ∀ᵐ ω ∂X.P, ∀ (k : ZMod p.n) (E : ℝ), |E| < 2 →
      HasDerivAt (csmEps p i (X.Hm ω - embedPair p i (G ω)) k)
        (csmDeriv p i (X.Hm ω - embedPair p i (G ω)) k E) E ∧
      csmDeriv p i (X.Hm ω - embedPair p i (G ω)) k E =
        deriv (csmEps p i (X.Hm ω - embedPair p i (G ω)) k) E := by
  filter_upwards [csm_ae_good X hG] with ω hω k E hE
  have hζ : 0 < ((splitS p : ℂ) * conj (matchedA E)).im := by
    rw [Complex.im_ofReal_mul]
    exact mul_pos ctr_splitS_pos (csm_conj_matchedA_im_pos hE)
  have hdet := csm_ctrFull_det_ne_zero hω.2.2 (G ω) hω.2.1 E hζ
  have hd := csm_differentiableAt_eps (i := i) k hE hdet
  have heq := csm_csmDeriv_eq hd
  refine ⟨?_, heq⟩
  rw [heq]
  exact hd.hasDerivAt

/-- **The excluded set is contained in three tail events** (up to null sets): the displacement
`|λ_α - e_α| ≥ δ`, the anchor residual `obs ≥ ε/6`, and the two window integrals
`∫_J |∂_E ε_{e,k}| ≥ ε/3`; their probabilities are bounded by Markov's inequality and the pair
density `n/2`. Here `δ = ϑ/(2n)`, `J = [e_α - δ, e_α + δ]`, and `M₁, M₃, K` are the `L^{r₁}`
anchor, `L^{r₃}` displacement and `L^{r₂}` energy-derivative bounds. -/
theorem csm_bad_le (hpole : PairPoleExclusionContract) {ϑ : ℝ} (hϑ : 0 < ϑ) (α : Fin p.N)
    (hα : IsBulkRank p ϑ α) (X : PairExtension p model) {G : X.Ω → PairMatrix p i}
    (hG : IsCenterSplitting X G) {εm : ℝ} (hεm : 0 < εm)
    (hεm1 : εm ≤ cst0.ε₁ p.b (rankMargin p α))
    {r₁ r₂ r₃ M₁ M₃ K : ℝ} (hr₁ : 0 < r₁) (hr₂ : 1 ≤ r₂) (hr₃ : 0 < r₃) (hM₁ : 0 ≤ M₁)
    (hM₃ : 0 ≤ M₃) (hK0 : 0 ≤ K)
    (hobs : eLpNorm (fun ω => BlockBand.Layers.rpSplitObs i (classicalLocation p α) (splitS p)
        (BlockBand.Layers.rslUnassemble i (X.Hm ω - embedPair p i (G ω))))
        (ENNReal.ofReal r₁) X.P ≤ ENNReal.ofReal M₁)
    (hloc : eLpNorm (fun ω => physicalOrderedEigenvalue p (X.Hm ω) α - classicalLocation p α)
        (ENNReal.ofReal r₃) X.P ≤ ENNReal.ofReal M₃)
    (hder : ∀ E : ℝ, |E - classicalLocation p α| ≤ ϑ / 2 / p.n → ∀ k : ZMod p.n,
        (k = i ∨ k = i + 1) →
        eLpNorm (fun ω => deriv (csmEps p i (X.Hm ω - embedPair p i (G ω)) k) E)
          (ENNReal.ofReal r₂) X.P ≤ ENNReal.ofReal K) :
    extendedPairMeasure p α i X.P X.Hm {ω | ¬ InCenterDomain p i cst0 α
        (X.Hm ω - embedPair p i (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤
      ENNReal.ofReal ((p.n : ℝ) / 2) *
        (ENNReal.ofReal ((M₃ / (ϑ / 2 / p.n)) ^ r₃) + ENNReal.ofReal ((M₁ / (εm / 6)) ^ r₁) +
          2 * ENNReal.ofReal ((ϑ / p.n * K / (εm / 3)) ^ r₂)) := by
  have hP := csm_isProb_ext X
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  set e := classicalLocation p α with he_def
  set δ := ϑ / 2 / p.n with hδ
  have hδ0 : 0 < δ := by positivity
  have hδϑ : δ ≤ ϑ / 2 := div_le_self (by positivity) hn
  set Hres : X.Ω → p.SiteMatrix := fun ω => X.Hm ω - embedPair p i (G ω) with hHres
  set lam : X.Ω → ℝ := fun ω => physicalOrderedEigenvalue p (X.Hm ω) α with hlam
  set obs : X.Ω → ℝ := fun ω => BlockBand.Layers.rpSplitObs i e (splitS p)
    (BlockBand.Layers.rslUnassemble i (Hres ω)) with hobsdef
  set w := Set.Icc (e - δ) (e + δ) with hw
  set D : ZMod p.n → X.Ω × ℝ → ℂ := fun k z => csmDeriv p i (Hres z.1) k z.2 with hD
  set Z : ZMod p.n → X.Ω → ℝ≥0∞ := fun k ω => ∫⁻ E in w, ‖D k (ω, E)‖ₑ with hZ
  have hRm : Measurable Hres := csm_measurable_res X hG.1
  have hDm : ∀ k, Measurable (D k) := fun k =>
    Measurable.comp (g := fun x : p.SiteMatrix × ℝ => csmDeriv p i x.1 k x.2)
      (f := fun z : X.Ω × ℝ => (Hres z.1, z.2))
      (csm_measurable_csmDeriv i k) ((hRm.comp measurable_fst).prodMk measurable_snd)
  have hZm : ∀ k, Measurable (Z k) := fun k => (hDm k).enorm.lintegral_prod_right'
  have hwin : ∀ E ∈ w, |E - e| ≤ δ := fun E hE =>
    abs_le.mpr ⟨by linarith [hE.1], by linarith [hE.2]⟩
  have hderiv := csm_ae_hasDerivAt X hG
  have hK' : ∀ k : ZMod p.n, (k = i ∨ k = i + 1) → ∀ E ∈ w,
      ∫⁻ ω, ‖D k (ω, E)‖ₑ ^ r₂ ∂X.P ≤ (ENNReal.ofReal K) ^ r₂ := by
    intro k hk E hE
    have hE2 := (csm_window_facts hϑ α hα ((hwin E hE).trans hδϑ)).1
    have hae : (fun ω => D k (ω, E)) =ᵐ[X.P] fun ω => deriv (csmEps p i (Hres ω) k) E := by
      filter_upwards [hderiv] with ω hω
      exact (hω k E hE2).2
    have hb : eLpNorm (fun ω => D k (ω, E)) (ENNReal.ofReal r₂) X.P ≤ ENNReal.ofReal K := by
      rw [eLpNorm_congr_ae hae]
      exact hder E (hwin E hE) k hk
    have := csm_lintegral_le_of_eLpNorm X.P
      ((hDm k).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (by linarith) hK0 hb
    rw [ENNReal.ofReal_rpow_of_nonneg hK0 (by linarith)]
    exact this
  have hlen : ENNReal.ofReal ((e + δ) - (e - δ)) * ENNReal.ofReal K =
      ENNReal.ofReal (ϑ / p.n * K) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [hδ]
    field_simp
    ring
  have hZmom : ∀ k : ZMod p.n, (k = i ∨ k = i + 1) →
      ∫⁻ ω, Z k ω ^ r₂ ∂X.P ≤ ENNReal.ofReal ((ϑ / p.n * K) ^ r₂) := by
    intro k hk
    have := csm_window_moment X.P (hDm k) hr₂ (ENNReal.ofReal K) (hK' k hk)
    rw [hlen, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)] at this
    exact this
  have hint : ∀ k : ZMod p.n, (k = i ∨ k = i + 1) →
      ∀ᵐ ω ∂X.P, IntegrableOn (fun E => D k (ω, E)) w := by
    intro k hk
    exact csm_window_integrableOn_ae X.P (hDm k) (by linarith)
      ((hZmom k hk).trans_lt ENNReal.ofReal_lt_top).ne
  have hall := (csm_ae_good X hG).and ((csm_ae_det_ext X hG e).and
    (hderiv.and ((hint i (Or.inl rfl)).and (hint (i + 1) (Or.inr rfl)))))
  set N := {ω | ¬ (((X.Hm ω).IsHermitian ∧ (Hres ω).IsHermitian ∧ CsmBondGood (X.Hm ω)) ∧
    (exteriorBlock p i (Hres ω) - (e : ℂ) • 1).det ≠ 0 ∧
    (∀ (k : ZMod p.n) (E : ℝ), |E| < 2 →
      HasDerivAt (csmEps p i (Hres ω) k) (D k (ω, E)) E ∧
      D k (ω, E) = deriv (csmEps p i (Hres ω) k) E) ∧
    IntegrableOn (fun E => D i (ω, E)) w ∧ IntegrableOn (fun E => D (i + 1) (ω, E)) w)} with hN
  have hN0 : X.P N = 0 := ae_iff.mp hall
  set Pole := {ω | (exteriorBlock p i (Hres ω) - (lam ω : ℂ) • 1).det = 0} with hPole_def
  have hPole : extendedPairMeasure p α i X.P X.Hm Pole = 0 := csm_pole_null hpole X G
  set A₃ := {ω | δ ≤ |lam ω - e|} with hA₃
  set A₁ := {ω | εm / 6 ≤ |obs ω|} with hA₁
  set A₂ : ZMod p.n → Set X.Ω := fun k => {ω | ENNReal.ofReal (εm / 3) ≤ Z k ω} with hA₂
  have hsub : {ω | ¬ InCenterDomain p i cst0 α (Hres ω) (lam ω)} ⊆
      N ∪ Pole ∪ A₃ ∪ A₁ ∪ A₂ i ∪ A₂ (i + 1) := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨⟨hNω, hPω⟩, h3⟩, h1⟩, h2i⟩, h2i1⟩ := hcon
    rw [hN, Set.mem_ofPred_eq, not_not] at hNω
    obtain ⟨⟨_, hHr, _⟩, hde, hdr, hIi, hIi1⟩ := hNω
    have hpol : (exteriorBlock p i (Hres ω) - (lam ω : ℂ) • 1).det ≠ 0 := hPω
    have hl : |lam ω - e| < δ := lt_of_not_ge h3
    have hlw : lam ω ∈ w := ⟨by linarith [(abs_lt.mp hl).1], by linarith [(abs_lt.mp hl).2]⟩
    have hew : e ∈ w := ⟨by linarith, by linarith⟩
    have hfacts := csm_window_facts hϑ α hα (hl.le.trans hδϑ)
    have hdom := cst0_inCenterDomain_iff hϑ p α hα i hHr hpol
    have hres : cst0.ε₁ p.b (rankMargin p α) < centerResidual p i (Hres ω) (lam ω) := by
      by_contra hle
      exact hω (hdom.mpr ⟨hfacts.2.1, le_of_not_gt hle⟩)
    have hobs0 : 0 ≤ obs ω := le_max_of_le_left (norm_nonneg _)
    have hobsk : ∀ k : ZMod p.n, (k = i ∨ k = i + 1) →
        ‖csmEps p i (Hres ω) k e‖ ≤ obs ω := by
      intro k hk
      rw [csm_norm_eps_eq_obs hHr hde k]
      rcases hk with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hk : ∀ k : ZMod p.n, (k = i ∨ k = i + 1) → IntegrableOn (fun E => D k (ω, E)) w →
        ENNReal.ofReal ‖csmEps p i (Hres ω) k (lam ω)‖ ≤ ENNReal.ofReal (obs ω) + Z k ω := by
      intro k hk hI
      have hf := csm_ftc_enorm_le hew hlw (fun E hE =>
        (hdr k E (csm_window_facts hϑ α hα ((hwin E hE).trans hδϑ)).1).1) hI
      calc ENNReal.ofReal ‖csmEps p i (Hres ω) k (lam ω)‖
          ≤ ENNReal.ofReal (‖csmEps p i (Hres ω) k e‖ +
              ‖csmEps p i (Hres ω) k (lam ω) - csmEps p i (Hres ω) k e‖) :=
            ENNReal.ofReal_le_ofReal (norm_le_norm_add_norm_sub' _ _)
        _ = ENNReal.ofReal ‖csmEps p i (Hres ω) k e‖ +
              ‖csmEps p i (Hres ω) k (lam ω) - csmEps p i (Hres ω) k e‖ₑ := by
            rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
            congr 1
            exact ofReal_norm _
        _ ≤ ENNReal.ofReal (obs ω) + Z k ω :=
            add_le_add (ENNReal.ofReal_le_ofReal (hobsk k hk)) hf
    have hchain : ENNReal.ofReal εm ≤ ENNReal.ofReal (2 * obs ω) + Z i ω + Z (i + 1) ω := by
      have h0 : εm ≤ centerResidual p i (Hres ω) (lam ω) := hεm1.trans hres.le
      have hcr := csm_centerResidual_le (i := i) (Hres ω) (lam ω)
      calc ENNReal.ofReal εm
          ≤ ENNReal.ofReal (‖csmEps p i (Hres ω) i (lam ω)‖ +
              ‖csmEps p i (Hres ω) (i + 1) (lam ω)‖) := ENNReal.ofReal_le_ofReal (h0.trans hcr)
        _ = ENNReal.ofReal ‖csmEps p i (Hres ω) i (lam ω)‖ +
              ENNReal.ofReal ‖csmEps p i (Hres ω) (i + 1) (lam ω)‖ :=
            ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
        _ ≤ (ENNReal.ofReal (obs ω) + Z i ω) + (ENNReal.ofReal (obs ω) + Z (i + 1) ω) :=
            add_le_add (hk i (Or.inl rfl) hIi) (hk (i + 1) (Or.inr rfl) hIi1)
        _ = ENNReal.ofReal (2 * obs ω) + Z i ω + Z (i + 1) ω := by
            rw [two_mul, ENNReal.ofReal_add hobs0 hobs0]
            ring
    have hthird : ENNReal.ofReal (εm / 3) + ENNReal.ofReal (εm / 3) + ENNReal.ofReal (εm / 3) =
        ENNReal.ofReal εm := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [← hthird] at hchain
    rcases csm_split3 hchain with h | h | h
    · have hlt : |obs ω| < εm / 6 := lt_of_not_ge h1
      have h2 : 2 * obs ω < εm / 3 := by
        have := le_abs_self (obs ω)
        linarith
      exact absurd h (not_le.mpr ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h2))
    · exact h2i h
    · exact h2i1 h
  have hc : ∀ A : Set X.Ω, extendedPairMeasure p α i X.P X.Hm A ≤
      ENNReal.ofReal ((p.n : ℝ) / 2) * X.P A := fun A => csm_pairMeasure_apply_le X A
  have hobsm : Measurable obs :=
    (BlockBand.Layers.rp_measurable_splitObs i e (splitS p)).comp
      ((BlockBand.Layers.rsl_measurable_unassemble i).comp hRm)
  have hlamm : Measurable (fun ω => lam ω - e) :=
    ((measurable_physicalOrderedEigenvalue p α).comp X.measurable_Hm).sub_const e
  have hb₃ : X.P A₃ ≤ ENNReal.ofReal ((M₃ / δ) ^ r₃) :=
    csm_markov X.P hlamm.aestronglyMeasurable hr₃ hδ0 hM₃ hloc
  have hb₁ : X.P A₁ ≤ ENNReal.ofReal ((M₁ / (εm / 6)) ^ r₁) :=
    csm_markov X.P hobsm.aestronglyMeasurable hr₁ (by positivity) hM₁ hobs
  have hb₂ : ∀ k : ZMod p.n, (k = i ∨ k = i + 1) →
      X.P (A₂ k) ≤ ENNReal.ofReal ((ϑ / p.n * K / (εm / 3)) ^ r₂) := fun k hk =>
    csm_markov_lintegral X.P (hZm k).aemeasurable (by linarith) (by positivity) (by positivity)
      (hZmom k hk)
  set μ := extendedPairMeasure p α i X.P X.Hm
  set c := ENNReal.ofReal ((p.n : ℝ) / 2)
  have hμN : μ N = 0 := le_antisymm ((hc N).trans (by rw [hN0, mul_zero])) zero_le
  calc μ {ω | ¬ InCenterDomain p i cst0 α (Hres ω) (lam ω)}
      ≤ μ (N ∪ Pole ∪ A₃ ∪ A₁ ∪ A₂ i ∪ A₂ (i + 1)) := measure_mono hsub
    _ ≤ μ N + μ Pole + μ A₃ + μ A₁ + μ (A₂ i) + μ (A₂ (i + 1)) := by
      refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
      refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
      refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
      refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
      exact measure_union_le _ _
    _ ≤ 0 + 0 + c * ENNReal.ofReal ((M₃ / δ) ^ r₃) + c * ENNReal.ofReal ((M₁ / (εm / 6)) ^ r₁) +
        c * ENNReal.ofReal ((ϑ / p.n * K / (εm / 3)) ^ r₂) +
        c * ENNReal.ofReal ((ϑ / p.n * K / (εm / 3)) ^ r₂) := by
      rw [hμN, hPole]
      gcongr
      · exact (hc _).trans (mul_le_mul_right hb₃ _)
      · exact (hc _).trans (mul_le_mul_right hb₁ _)
      · exact (hc _).trans (mul_le_mul_right (hb₂ i (Or.inl rfl)) _)
      · exact (hc _).trans (mul_le_mul_right (hb₂ (i + 1) (Or.inr rfl)) _)
    _ = c * (ENNReal.ofReal ((M₃ / δ) ^ r₃) + ENNReal.ofReal ((M₁ / (εm / 6)) ^ r₁) +
          2 * ENNReal.ofReal ((ϑ / p.n * K / (εm / 3)) ^ r₂)) := by ring

end Core

/-!
## 4. The `small` field of `CenterDomainContract cst0`
-/

section Small

theorem csm_rpow_div_sqrt {x W : ℝ} (hx : 0 ≤ x) (hW : 0 < W) (R : ℝ) :
    (x / Real.sqrt W) ^ (2 * R) = x ^ (2 * R) / W ^ R := by
  rw [Real.div_rpow hx (Real.sqrt_nonneg W), Real.sqrt_eq_rpow, ← Real.rpow_mul hW.le]
  congr 2
  ring

/-- `ε₁` of `cst0` is bounded below uniformly over `ϑ`-bulk ranks (finitely many grid levels). -/
theorem csm_eps1_lower (b ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ εm : ℝ, 0 < εm ∧ ∀ (p : Parameters), p.b = b → ∀ α : Fin p.N, IsBulkRank p ϑ α →
      εm ≤ cst0.ε₁ p.b (rankMargin p α) := by
  set S := Finset.range (ctrLevel (ϑ / 2) + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  refine ⟨S.inf' hS (fun j => (ctrCert (ctrC b) (ctrTheta j)).1) / 2,
    half_pos ((Finset.lt_inf'_iff hS).mpr fun j _ => ctrCert_fst_pos _ _), ?_⟩
  intro p hpb α hα
  subst hpb
  have hlev : ctrLevel (rankMargin p α) ≤ ctrLevel (ϑ / 2) :=
    ctrLevel_mono (by positivity) (ctr_rankMargin_ge hϑ α hα)
  exact div_le_div_of_nonneg_right (Finset.inf'_le (fun j => (ctrCert (ctrC p.b) (ctrTheta j)).1)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hlev))) zero_le_two

/-- **The `small` clause of the physical center theorem** (`CenterDomainContract.small` for
`cst0`): `b, ϑ, T` and every fixed `q` first; then `C_q, W₀`; for `W > W₀`, `4 ≤ n ≤ TW`,
every model, `ϑ`-bulk rank `α`, pair `i` and extension carrying the edge splitting, the
pair-law probability that `λ_α` leaves the regular domain of `cst0` is at most
`C_q W^{1-q}`. Hypotheses: `RankLocationContract.location` (physical law),
`MatchedTracesContract.residualPair` (at `s = min(c,b)`), `FullEnergyTraceBound` (proved as
`fullEnergyTraceBound_holds`) and `PairPoleExclusionContract` (pole null set). -/
theorem centerDomain_small (hrank : RankLocationContract) (hmt : MatchedTracesContract)
    (hfe : FullEnergyTraceBound) (hpole : PairPoleExclusionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ T : ℝ, 0 < ϑ → ϑ < 1 / 2 → ∀ q : ℝ,
      ∃ Cq W₀ : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W → W₀ < (p.W : ℝ) →
        ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α → ∀ (i : ZMod p.n)
          (X : PairExtension p model) (G : X.Ω → PairMatrix p i), IsCenterSplitting X G →
          extendedPairMeasure p α i X.P X.Hm
              {ω | ¬ InCenterDomain p i cst0 α (X.Hm ω - embedPair p i (G ω))
                (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤
            ENNReal.ofReal (Cq * (p.W : ℝ) ^ (1 - q)) := by
  intro b hb hb' ϑ T hϑ hϑ' q
  set R := max q 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hqR : q ≤ R := le_max_left _ _
  set r₁ := max R 2 with hr₁def
  have hr₁2 : 2 ≤ r₁ := le_max_right _ _
  have hRr₁ : R ≤ r₁ := le_max_left _ _
  set r₂ := 2 * R with hr₂def
  have hr₂ : 1 ≤ r₂ := by linarith
  have hs : 0 < ctrC b := lt_min (by linarith) hb
  have hs2 : ctrC b < 2 * min (1 - 2 * b) b := by
    change ctrC b < 2 * ctrC b
    linarith
  obtain ⟨Cloc, hloc⟩ := hrank.location b hb hb' T ϑ hϑ hϑ' r₂ hr₂
  obtain ⟨ε₀, Cmt, hε₀, hmtb⟩ := hmt.residualPair b hb hb' (ϑ / 2) T (ctrC b) (by positivity)
    hs hs2
  obtain ⟨Cfe, Wfe, hfeb⟩ := hfe b hb hb' (ϑ / 2) T (by positivity) r₂ hr₂
  obtain ⟨εm, hεm, hεm1⟩ := csm_eps1_lower b ϑ hϑ
  set Cl := max Cloc 0
  set Cm := max Cmt 0
  set Cf := max Cfe 0
  have hCl : 0 ≤ Cl := le_max_right _ _
  have hCm : 0 ≤ Cm := le_max_right _ _
  have hCf : 0 ≤ Cf := le_max_right _ _
  set A₃ := (2 * Cl / ϑ) ^ r₂
  set A₁ := (6 * Cm * Real.sqrt r₁ / εm) ^ r₁
  set A₂ := (3 * ϑ * Cf / εm) ^ r₂
  have hA₃ : 0 ≤ A₃ := Real.rpow_nonneg (by positivity) _
  have hA₁ : 0 ≤ A₁ := Real.rpow_nonneg (by positivity) _
  have hA₂ : 0 ≤ A₂ := Real.rpow_nonneg (by positivity) _
  refine ⟨|T| / 2 * (A₃ + A₁ + 2 * A₂), max (r₁ / ε₀) Wfe, ?_⟩
  intro p hpb hn hW model α hα i X G hG
  subst hpb
  have hP := csm_isProb_ext X
  have hW0 : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hn0 : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hsq : 0 < Real.sqrt p.W := Real.sqrt_pos.mpr hW0
  set e := classicalLocation p α with he_def
  have he : e ∈ bulkInterval (ϑ / 2) := by
    have h := BlockBand.RankLocation.classicalLocation_mem_bulkInterval hϑ p α hα
    unfold bulkInterval at h ⊢
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- the three moment inputs on the extension
  have hlocX : eLpNorm (fun ω => physicalOrderedEigenvalue p (X.Hm ω) α - e)
      (ENNReal.ofReal r₂) X.P ≤ ENNReal.ofReal (Cl / (p.n * Real.sqrt p.W)) := by
    have h := hloc p rfl hn model MassLaw.physical α hα
    have hm : Measurable (fun H : p.SiteMatrix => physicalOrderedEigenvalue p H α - e) :=
      (measurable_physicalOrderedEigenvalue p α).sub_const e
    change eLpNorm _ _ (model.law : Measure p.SiteMatrix) ≤ _ at h
    rw [← X.map_eq, eLpNorm_map_measure hm.aestronglyMeasurable X.measurable_Hm.aemeasurable] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hobsX : eLpNorm (fun ω => BlockBand.Layers.rpSplitObs i e (splitS p)
      (BlockBand.Layers.rslUnassemble i (X.Hm ω - embedPair p i (G ω))))
      (ENNReal.ofReal r₁) X.P ≤ ENNReal.ofReal (Cm * Real.sqrt r₁ / p.W) := by
    have hr₁ε : r₁ ≤ ε₀ * p.W := by
      have h1 : r₁ / ε₀ < p.W := (le_max_left _ _).trans_lt hW
      rw [div_lt_iff₀ hε₀] at h1
      linarith
    have h := hmtb p rfl hn model i (csmSplitLaw X G) (csm_isPairSplitting X hG) e he r₁ hr₁2
      hr₁ε
    have hS : Measurable (fun ω => BlockBand.Layers.rslUnassemble i (X.Hm ω - embedPair p i (G ω))) :=
      (BlockBand.Layers.rsl_measurable_unassemble i).comp (csm_measurable_res X hG.1)
    change eLpNorm (BlockBand.Layers.rpSplitObs i e (splitS p)) _ (csmSplitLaw X G) ≤ _ at h
    unfold csmSplitLaw at h
    rw [eLpNorm_map_measure (BlockBand.Layers.rp_measurable_splitObs i e (splitS p)).aestronglyMeasurable
      hS.aemeasurable] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _)) hW0.le
  have hderX : ∀ E : ℝ, |E - e| ≤ ϑ / 2 / p.n → ∀ k : ZMod p.n, (k = i ∨ k = i + 1) →
      eLpNorm (fun ω => deriv (csmEps p i (X.Hm ω - embedPair p i (G ω)) k) E)
        (ENNReal.ofReal r₂) X.P ≤ ENNReal.ofReal (Cf * p.n / Real.sqrt p.W) := by
    intro E hE k hk
    have hE2 : |E - e| ≤ ϑ / 2 :=
      hE.trans (div_le_self (by positivity) (by exact_mod_cast p.n_pos))
    have hEI := (csm_window_facts hϑ α hα hE2).2.2
    have h := hfeb p rfl hn ((le_max_right _ _).trans_lt hW) model i X G hG E hEI k hk
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0.le)
      hsq.le
  have hbad := csm_bad_le hpole hϑ α hα X hG hεm (hεm1 p rfl α hα) (by linarith) hr₂
    (by linarith) (by positivity) (by positivity) (by positivity) hobsX hlocX hderX
  refine hbad.trans ?_
  -- arithmetic
  have hWR : 0 < (p.W : ℝ) ^ R := Real.rpow_pos_of_pos hW0 R
  have e₃ : ((Cl / (p.n * Real.sqrt p.W)) / (ϑ / 2 / p.n)) ^ r₂ = A₃ / (p.W : ℝ) ^ R := by
    have : (Cl / (p.n * Real.sqrt p.W)) / (ϑ / 2 / p.n) = (2 * Cl / ϑ) / Real.sqrt p.W := by
      field_simp
    rw [this, hr₂def, csm_rpow_div_sqrt (by positivity) hW0]
  have e₂ : (ϑ / p.n * (Cf * p.n / Real.sqrt p.W) / (εm / 3)) ^ r₂ = A₂ / (p.W : ℝ) ^ R := by
    have : ϑ / p.n * (Cf * p.n / Real.sqrt p.W) / (εm / 3) =
        (3 * ϑ * Cf / εm) / Real.sqrt p.W := by
      field_simp
    rw [this, hr₂def, csm_rpow_div_sqrt (by positivity) hW0]
  have e₁ : ((Cm * Real.sqrt r₁ / p.W) / (εm / 6)) ^ r₁ ≤ A₁ / (p.W : ℝ) ^ R := by
    have : (Cm * Real.sqrt r₁ / p.W) / (εm / 6) = (6 * Cm * Real.sqrt r₁ / εm) / p.W := by
      field_simp
    rw [this, Real.div_rpow (by positivity) hW0.le]
    exact div_le_div_of_nonneg_left hA₁ hWR
      (Real.rpow_le_rpow_of_exponent_le hW1 hRr₁)
  have hsum : ENNReal.ofReal (((Cl / (p.n * Real.sqrt p.W)) / (ϑ / 2 / p.n)) ^ r₂) +
      ENNReal.ofReal (((Cm * Real.sqrt r₁ / p.W) / (εm / 6)) ^ r₁) +
      2 * ENNReal.ofReal ((ϑ / p.n * (Cf * p.n / Real.sqrt p.W) / (εm / 3)) ^ r₂) ≤
      ENNReal.ofReal ((A₃ + A₁ + 2 * A₂) / (p.W : ℝ) ^ R) := by
    rw [e₃, e₂]
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (A₂ / (p.W : ℝ) ^ R) =
        ENNReal.ofReal (2 * (A₂ / (p.W : ℝ) ^ R)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [h2]
    calc ENNReal.ofReal (A₃ / (p.W : ℝ) ^ R) +
          ENNReal.ofReal (((Cm * Real.sqrt r₁ / p.W) / (εm / 6)) ^ r₁) +
          ENNReal.ofReal (2 * (A₂ / (p.W : ℝ) ^ R))
        ≤ ENNReal.ofReal (A₃ / (p.W : ℝ) ^ R) + ENNReal.ofReal (A₁ / (p.W : ℝ) ^ R) +
          ENNReal.ofReal (2 * (A₂ / (p.W : ℝ) ^ R)) := by
          gcongr
      _ = ENNReal.ofReal ((A₃ + A₁ + 2 * A₂) / (p.W : ℝ) ^ R) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
  refine (mul_le_mul_right hsum _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hT : (p.n : ℝ) ≤ |T| * p.W := hn.trans (mul_le_mul_of_nonneg_right (le_abs_self T) hW0.le)
  have hS0 : 0 ≤ A₃ + A₁ + 2 * A₂ := by positivity
  have hpow : (p.W : ℝ) / (p.W : ℝ) ^ R ≤ (p.W : ℝ) ^ (1 - q) := by
    have h1 : (p.W : ℝ) / (p.W : ℝ) ^ R = (p.W : ℝ) ^ (1 - R) := by
      rw [Real.rpow_sub hW0, Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  calc (p.n : ℝ) / 2 * ((A₃ + A₁ + 2 * A₂) / (p.W : ℝ) ^ R)
      ≤ |T| * p.W / 2 * ((A₃ + A₁ + 2 * A₂) / (p.W : ℝ) ^ R) := by
        gcongr
    _ = |T| / 2 * (A₃ + A₁ + 2 * A₂) * ((p.W : ℝ) / (p.W : ℝ) ^ R) := by ring
    _ ≤ |T| / 2 * (A₃ + A₁ + 2 * A₂) * (p.W : ℝ) ^ (1 - q) := by
        gcongr

end Small

end BlockBand.Center
