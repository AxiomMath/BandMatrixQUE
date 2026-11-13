module

public import BlockBand.Diffusion.Base.TransitionLawFactors
public import BlockBand.Diffusion.Base.TransitionLawExt
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The transition law of the base diffusion

Both main results take the two named intermediate statements `McKeanBackwardFacts D0` and
`TimeMollifyDuality D0` as hypotheses (they are proved in `mcKeanBackwardFacts_holds` and
`timeMollifyDuality_holds`):
* `IsExBaseDiffusion.measure_inter_preimage`: for `s < t` (in `ℝ≥0`), `A ∈ 𝓖_s` and Borel
  `B`, `P(A ∩ {Z_t ∈ B}) = ∫_A ∫_B p_{t-s}(Z_s, z') dz' dP`, i.e. the conditional law of `Z_t`
  given `𝓖_s` is `p_{t-s}(Z_s, ·) dz'` (`s = 0` allowed).
* `exBaseTransitionLaw_of : ExLbkBaseTransitionLaw D0` (the local copy of `LbkBaseTransitionLaw`):
  `P(Z_t ∈ B) = ∫_B p_t(z, z') dz'` for all `t > 0`, strip starts `z` and Borel `B`.

Proof. For bounded continuous `g, k ≥ 0` let `uX(τ, x) = P^X_τ g(x)`, `uY(τ, y) = P^Y_τ k(y)`
(`= g`, `k` at `τ = 0`) and `u = exProdSol D0 g k t`, `u(s, (x, y)) = uX(t-s, x) uY(t-s, y)`.
The factors are `C^{0,2}` and solve the forward one-dimensional equations (`exProd_tmInputs`, from
`McKeanBackwardFacts` and the sphere facts), are continuous up to `τ = 0` (semigroup
continuity and the approximate identities) and bounded. `TimeMollifyDuality` gives
`E[g(X_t)k(Y_t) | 𝓖_s] = u(s, Z_s)`, hence `∫_A g(X_t)k(Y_t) dP = ∫_A u(s, Z_s) dP` for `A ∈ 𝓖_s`,
and `u(s, w) = ∫ p_{t-s}(w, z') g(x')k(y') dz'` (Fubini). Hence the finite measure
`B ↦ P(A ∩ {Z_t ∈ B})` and the measure `B ↦ ∫_A p_{t-s}(Z_s, B) dP` agree on all product test
functions `g ⊗ k`, so they are equal (`measure_eq_of_lintegral_prod`: π-λ over rectangles, after
two applications of Mathlib's `ext_of_forall_lintegral_eq_of_IsFiniteMeasure`). No boundary
argument is needed: the test functions are bounded continuous on all of `ℝ`, the equations are
only used on the open strip, and continuity of the factors is proved up to the boundary.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The transition kernel `z ↦ p_h(z, z') dz'` of the base diffusion. -/
def exKer (D0 h : ℝ) : Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  Kernel.withDensity (Kernel.const (ℝ × ℝ) volume) fun z z' =>
    ENNReal.ofReal (exKernel D0 h z z')

theorem measurable_exKernel_uncurry {D0 : ℝ} (hD0 : 0 < D0) (h : ℝ) :
    Measurable (Function.uncurry fun z z' : ℝ × ℝ => ENNReal.ofReal (exKernel D0 h z z')) :=
  ((exKernel_measurable hD0).comp
    (f := fun q : (ℝ × ℝ) × (ℝ × ℝ) => (h, q.1, q.2)) (by fun_prop)).ennreal_ofReal

theorem exKer_apply {D0 : ℝ} (hD0 : 0 < D0) (h : ℝ) (z : ℝ × ℝ) :
    exKer D0 h z = volume.withDensity fun z' => ENNReal.ofReal (exKernel D0 h z z') := by
  rw [exKer, Kernel.withDensity_apply _ (measurable_exKernel_uncurry hD0 h), Kernel.const_apply]

theorem exKer_apply_set {D0 : ℝ} (hD0 : 0 < D0) (h : ℝ) (z : ℝ × ℝ) {B : Set (ℝ × ℝ)}
    (hB : MeasurableSet B) :
    exKer D0 h z B = ∫⁻ z' in B, ENNReal.ofReal (exKernel D0 h z z') := by
  rw [exKer_apply hD0, withDensity_apply _ hB]

theorem exists_abs_le_of_bcf (g : ℝ →ᵇ ℝ≥0) : ∃ M : ℝ, ∀ x, |(g x : ℝ)| ≤ M := by
  obtain ⟨C, hC⟩ := g.bounded
  refine ⟨(g 0 : ℝ) + C, fun x => ?_⟩
  have h1 := hC x 0
  rw [NNReal.dist_eq] at h1
  rw [abs_of_nonneg (NNReal.coe_nonneg _)]
  linarith [(abs_le.1 h1).2]

/-- `∫⁻ p_h(w, ·) F = ofReal (∫ p_h(w, ·) F)` for bounded measurable `F ≥ 0`, `w` in the strip. -/
theorem lintegral_exKer_eq_ofReal {D0 h : ℝ} (hD0 : 0 < D0) (hh : 0 < h) {w : ℝ × ℝ}
    (hw : w ∈ exBaseStrip) {F : ℝ × ℝ → ℝ} (hF : Measurable F) (hF0 : ∀ z', 0 ≤ F z')
    {C : ℝ} (hFC : ∀ z', |F z'| ≤ C) :
    ∫⁻ z', ENNReal.ofReal (F z') ∂exKer D0 h w =
      ENNReal.ofReal (∫ z', exKernel D0 h w z' * F z') := by
  have hpm : Measurable fun z' => ENNReal.ofReal (exKernel D0 h w z') :=
    ((exKernel_measurable hD0).comp (f := fun z' : ℝ × ℝ => (h, w, z'))
      (by fun_prop)).ennreal_ofReal
  rw [exKer_apply hD0, lintegral_withDensity_eq_lintegral_mul _ hpm hF.ennreal_ofReal,
    ofReal_integral_eq_lintegral_ofReal (integrable_exKernel_mul hD0 hh hw hF.aestronglyMeasurable
      hFC) (ae_of_all _ fun z' => mul_nonneg (exKernel_nonneg hD0 _ _ _) (hF0 z'))]
  refine lintegral_congr fun z' => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (exKernel_nonneg hD0 _ _ _)]

section Main

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {z : ℝ × ℝ}
  {Z : ℝ≥0 → Ω → ℝ × ℝ}

/-- **The conditional law, kernel form.** For `s < t`, `A ∈ 𝓖_s` and Borel `B`:
`P(A ∩ {Z_t ∈ B}) = ∫_A exKer D0 (t - s) (Z_s) B dP`. -/
theorem IsExBaseDiffusion.measure_inter_preimage_exKer (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s t : ℝ≥0} (hst : s < t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    P (A ∩ Z t ⁻¹' B) = ∫⁻ ω in A, exKer D0 ((t : ℝ) - s) (Z s ω) B ∂P := by
  have := h.prob
  have hZm : ∀ r, Measurable (Z r) := fun r => (h.adapted r).mono (𝓖.le r) le_rfl
  have hAm : MeasurableSet A := 𝓖.le s A hA
  have hstR : (s : ℝ) < t := by exact_mod_cast hst
  have ht0 : (0 : ℝ≥0) < t := lt_of_le_of_lt zero_le hst
  have hh0 : 0 < (t : ℝ) - s := by linarith
  have hpath : ∀ᵐ ω ∂P, ∀ r, Z r ω ∈ exBaseStrip := h.paths.mono fun ω hω => hω.2
  set κ := exKer D0 ((t : ℝ) - s) with hκ
  set μA := (P.restrict A).map (Z t) with hμA
  set νA := ((P.restrict A).map (Z s)).bind κ with hνA
  have hκm : AEMeasurable (⇑κ) ((P.restrict A).map (Z s)) := κ.measurable.aemeasurable
  have hEq : μA = νA := by
    refine measure_eq_of_lintegral_prod fun g k => ?_
    obtain ⟨Mg, hMg⟩ := exists_abs_le_of_bcf g
    obtain ⟨Mk, hMk⟩ := exists_abs_le_of_bcf k
    set M := max Mg Mk with hM
    have hgM : ∀ x, |(g x : ℝ)| ≤ M := fun x => (hMg x).trans (le_max_left _ _)
    have hkM : ∀ x, |(k x : ℝ)| ≤ M := fun x => (hMk x).trans (le_max_right _ _)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM 0)
    have hgc : Continuous fun x => (g x : ℝ) := NNReal.continuous_coe.comp g.continuous
    have hkc : Continuous fun x => (k x : ℝ) := NNReal.continuous_coe.comp k.continuous
    set u := exProdSol D0 (fun x => (g x : ℝ)) (fun x => (k x : ℝ)) t with hu
    obtain ⟨uXt, uX1, uX2, uYt, uY1, uY2, hXd, hYd, hXpde, hYpde, hXc, hYc, hX0, hY0, hbX, hbY⟩ :=
      exProd_tmInputs hD0 hX hgc hkc hgM hkM t.2 hz
    have hce := hT Ω inferInstance 𝓖 P z Z h t _ uXt uX1 uX2 _ uYt uY1 uY2 hXd hYd hXpde hYpde
      hXc hYc hX0 hY0 M M hbX hbY s hst
    have e0X : ∀ x, mkSemigroupX D0 (fun x => (g x : ℝ)) (0, x) = g x := fun x => by
      simp [mkSemigroupX]
    have e0Y : ∀ y, skSemigroupY0 D0 (fun x => (k x : ℝ)) (0, y) = k y := fun y => by
      simp [skSemigroupY0]
    simp only [e0X, e0Y] at hce
    -- the terminal side
    have hFm : Measurable fun p : ℝ × ℝ => (g p.1 : ℝ) * (k p.2 : ℝ) :=
      (hgc.comp continuous_fst).measurable.mul (hkc.comp continuous_snd).measurable
    have hFi : Integrable (fun ω => (g (Z t ω).1 : ℝ) * k (Z t ω).2) P := by
      refine Integrable.of_bound (hFm.comp (hZm t)).aestronglyMeasurable (M * M)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgM _) (hkM _) (abs_nonneg _) hM0
    have hdual : ∫ ω in A, u ((t : ℝ), Z t ω) ∂P = ∫ ω in A, u ((s : ℝ), Z s ω) ∂P := by
      have e1 : (fun ω => u ((t : ℝ), Z t ω)) = fun ω => (g (Z t ω).1 : ℝ) * k (Z t ω).2 :=
        funext fun ω => by rw [hu, exProdSol_terminal]
      rw [e1, ← setIntegral_condExp (𝓖.le s) hFi hA]
      exact setIntegral_congr_ae (𝓖.le s A hA) (hce.mono fun ω hω _ => hω)
    have hL : ∫⁻ p, (g p.1 : ℝ≥0∞) * k p.2 ∂μA =
        ENNReal.ofReal (∫ ω in A, u ((t : ℝ), Z t ω) ∂P) := by
      have e : ∀ p : ℝ × ℝ, ((g p.1 : ℝ≥0∞) * k p.2) = ENNReal.ofReal ((g p.1 : ℝ) * k p.2) :=
        fun p => by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_coe_nnreal]
      simp_rw [e]
      rw [hμA, lintegral_map hFm.ennreal_ofReal (hZm t),
        ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr fun ω => ?_
        rw [hu, exProdSol_terminal]
      · refine Integrable.of_bound ((hFm.comp (hZm t)).aestronglyMeasurable.congr
          (ae_of_all _ fun ω => by simp only [Function.comp_apply, hu, exProdSol_terminal])) (M * M)
          (ae_of_all _ fun ω => ?_)
        rw [hu, exProdSol_terminal, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hgM _) (hkM _) (abs_nonneg _) hM0
      · exact ae_of_all _ fun ω => by
          simp only [Pi.zero_apply, hu, exProdSol_terminal]; positivity
    -- the initial side
    have hR : ∫⁻ p, (g p.1 : ℝ≥0∞) * k p.2 ∂νA =
        ENNReal.ofReal (∫ ω in A, u ((s : ℝ), Z s ω) ∂P) := by
      have hFm' : Measurable fun p : ℝ × ℝ => (g p.1 : ℝ≥0∞) * k p.2 :=
        (ENNReal.continuous_coe.comp (g.continuous.comp continuous_fst)).measurable.mul
          (ENNReal.continuous_coe.comp (k.continuous.comp continuous_snd)).measurable
      have hum : Measurable fun w => u ((s : ℝ), w) :=
        measurable_exProdSol D0 hgc.measurable hkc.measurable hstR hD0
      rw [hνA, Measure.lintegral_bind hκm hFm'.aemeasurable,
        lintegral_map (hFm'.lintegral_kernel) (hZm s),
        ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr_ae (ae_restrict_of_ae (hpath.mono fun ω hω => ?_))
        have e : ∀ p : ℝ × ℝ, ((g p.1 : ℝ≥0∞) * k p.2) =
            ENNReal.ofReal ((g p.1 : ℝ) * k p.2) := fun p => by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_coe_nnreal]
        simp_rw [e]
        rw [lintegral_exKer_eq_ofReal hD0 hh0 (hω s) hFm
          (fun p => mul_nonneg (g p.1).2 (k p.2).2) (C := M * M) (fun p => by
            rw [abs_mul]; exact mul_le_mul (hgM _) (hkM _) (abs_nonneg _) hM0),
          hu, exProdSol_eq_integral _ _ _ hstR]
      · refine Integrable.of_bound (hum.comp (hZm s)).aestronglyMeasurable (M * M)
          (ae_restrict_of_ae (hpath.mono fun ω hω => ?_))
        rw [Real.norm_eq_abs]
        exact abs_exProdSol_le hD0 hgM hkM t (p := ((s : ℝ), Z s ω)) (hω s)
      · refine ae_of_all _ fun ω => ?_
        simp only [Pi.zero_apply]
        rw [hu, exProdSol_eq_integral _ _ _ hstR]
        exact integral_nonneg fun z' =>
          mul_nonneg (exKernel_nonneg hD0 _ _ _) (mul_nonneg (g _).2 (k _).2)
    rw [hL, hR, hdual]
  have h1 := congrArg (fun ρ => ρ B) hEq
  simp only [hμA, hνA] at h1
  rw [Measure.map_apply (hZm t) hB, Measure.restrict_apply (hZm t hB),
    Measure.bind_apply hB hκm, lintegral_map (κ.measurable_coe hB) (hZm s)] at h1
  rw [inter_comm, h1]

/-- **The conditional law.** For `s < t`, `A ∈ 𝓖_s` and Borel `B`:
`P(A ∩ {Z_t ∈ B}) = ∫_A ∫_B p_{t-s}(Z_s, z') dz' dP`. -/
theorem IsExBaseDiffusion.measure_inter_preimage (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {s t : ℝ≥0} (hst : s < t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    P (A ∩ Z t ⁻¹' B) =
      ∫⁻ ω in A, (∫⁻ z' in B, ENNReal.ofReal (exKernel D0 ((t : ℝ) - s) (Z s ω) z')) ∂P := by
  rw [h.measure_inter_preimage_exKer hD0 hz hX hT hst hA hB]
  exact lintegral_congr fun ω => exKer_apply_set hD0 _ _ hB

/-- **The transition law, kernel form.** `P(Z_t ∈ B) = exKer D0 t z B` for `t > 0`. -/
theorem IsExBaseDiffusion.measure_preimage_exKer (h : IsExBaseDiffusion P 𝓖 D0 z Z)
    (hD0 : 0 < D0) (hz : z ∈ exBaseStrip) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) {t : ℝ≥0} (ht : 0 < t) {B : Set (ℝ × ℝ)}
    (hB : MeasurableSet B) : P (Z t ⁻¹' B) = exKer D0 t z B := by
  have := h.prob
  have h1 := h.measure_inter_preimage_exKer hD0 hz hX hT ht (MeasurableSet.univ (m := 𝓖 0)) hB
  rw [univ_inter, Measure.restrict_univ, NNReal.coe_zero, sub_zero] at h1
  rw [h1, lintegral_congr_ae (g := fun _ => exKer D0 t z B) (h.start.mono fun ω hω => by
    simp only [hω]), lintegral_const, measure_univ, mul_one]

end Main

/-- **The transition law `ExLbkBaseTransitionLaw`** (the local copy of `LbkBaseTransitionLaw`), from
the two named intermediate statements. -/
theorem exBaseTransitionLaw_of {D0 : ℝ} (hD0 : 0 < D0) (hX : McKeanBackwardFacts D0)
    (hT : TimeMollifyDuality D0) : ExLbkBaseTransitionLaw D0 := by
  intro t ht z hz Ω m 𝓖 P Z h B hB
  rw [h.measure_preimage_exKer hD0 hz hX hT ht hB, exKer_apply_set hD0 _ _ hB]

end BlockBand.Diffusion
