module

public import BlockBand.Palm.MomentFlow.BridgeVersion
public import BlockBand.Palm.MomentFlow.MaxPrinciple
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# B-gen: the conditional moments solve the moment flow (support layer)

*Measure:* `flowLaw N a`; *σ-algebra:* `𝓛 = pathSigma F a s c`; *domain:* Hermitian `F`,
`a < s`, `U : ℝ≥0` with `s + U ≤ c`, gap level `δ > 0`, every configuration `ζ`.
The rates are evaluated at the clamped time `s + min(max r 0) U` (`rateC`): on `r ∈ [0, U]` this
is `flowRate F a ω (s + r)`; clamping makes the rate process continuous in `r` and bounded on the
gap event for all `r`, which gives the joint `borel ⊗ 𝓛` measurability needed below.

* `integral_mul_condExp`: pull-out `∫ g f = ∫ g E[f | m]` for bounded `m`-measurable `g`.
* `identity_clamped`: the integrated identity for the clamped moments (from
  `integrated_moment_identity`; consumes `DysonBrownianMotion N`).
* `identity_version`: the same for `momentVersion` (Fubini and pull-out).
* `incV_ae_zero`: `1_{B_δ}(Φ̃_ζ(s+u) - Φ̃_ζ(s) - ∫_{(0,u]} 𝓑 Φ̃) = 0` almost surely.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-!
## Generic helpers
-/

theorem measurable_setIntegral_prod {Ω : Type*} {m : MeasurableSpace Ω} {G : ℝ × Ω → ℝ}
    (hG : Measurable G) (S : Set ℝ) : Measurable (fun ω => ∫ r in S, G (r, ω)) := by
  have h := StronglyMeasurable.integral_prod_right' (ν := volume.restrict S)
    (f := fun p : Ω × ℝ => G (p.2, p.1)) (hG.comp measurable_swap).stronglyMeasurable
  exact h.measurable

/-- Pull-out: `∫ g f = ∫ g E[f | m]` for bounded `m`-measurable `g` and integrable `f`. -/
theorem integral_mul_condExp {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀) {g f : Ω → ℝ}
    (hg : Measurable[m] g) {C : ℝ} (hgb : ∀ ω, |g ω| ≤ C) (hf : Integrable f μ) :
    ∫ ω, g ω * f ω ∂μ = ∫ ω, g ω * (μ[f | m]) ω ∂μ := by
  have hgf : Integrable (g * f) μ :=
    hf.bdd_mul (hg.mono hm le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have e : (fun ω => g ω * f ω) = g * f := rfl
  rw [e, ← integral_condExp hm (f := g * f)]
  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg.stronglyMeasurable hgf hf)

/-- Measurability of the moment generator from measurable rates and values (any σ-algebra). -/
theorem measurable_momentGenerator_param {P : Type*} {m : MeasurableSpace P}
    {c : P → Fin N → Fin N → ℝ} {f : P → Occ N → ℝ} (hc : ∀ i j, Measurable fun p => c p i j)
    (hf : ∀ ζ, Measurable fun p => f p ζ) (ξ : Occ N) :
    Measurable (fun p => momentGenerator (c p) (f p) ξ) := by
  unfold momentGenerator
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((hc i j).mul_const _).mul ((hf _).sub (hf _))

/-- `|𝓑 f(ξ)| ≤ ∑ R ξ_i(1+ξ_j)(L(ξ^{ij}) + L ξ)` when off-diagonal rates are `≤ R` and `|f| ≤ L`. -/
theorem abs_momentGenerator_le {c : Fin N → Fin N → ℝ} {f L : Occ N → ℝ} {R : ℝ}
    (hc : ∀ i j, i ≠ j → |c i j| ≤ R) (hf : ∀ ζ, |f ζ| ≤ L ζ) (ξ : Occ N) :
    |momentGenerator c f ξ| ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, R * jumpCoeff ξ i j * (L (move ξ i j) + L ξ) := by
  unfold momentGenerator
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hj).1
  rw [abs_mul, abs_mul, abs_of_nonneg (jumpCoeff_nonneg ξ i j)]
  have h1 := hc i j hij
  have h2 : |f (move ξ i j) - f ξ| ≤ L (move ξ i j) + L ξ :=
    (abs_sub _ _).trans (add_le_add (hf _) (hf _))
  have hR : 0 ≤ R := (abs_nonneg _).trans h1
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (jumpCoeff_nonneg ξ i j)) h2 (abs_nonneg _)
    (mul_nonneg hR (jumpCoeff_nonneg ξ i j))

/-!
## Rates on the gap event
-/

/-- Off-diagonal rates are at most `(N δ²)⁻¹` where the gap is at least `δ`. -/
theorem flowRate_le_of_gap {F : Matrix (Fin N) (Fin N) ℂ} {a σ δ : ℝ} {ω : FlowSample N}
    {i j : Fin N} (hδ : 0 < δ) (h : δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) :
    flowRate F a ω σ i j ≤ ((N : ℝ) * δ ^ 2)⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast i.pos
  unfold flowRate
  have hsq : δ ^ 2 ≤ (flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j) ^ 2 := by
    rw [← sq_abs (flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j)]
    exact pow_le_pow_left₀ hδ.le h 2
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hsq hN.le)

/-- Clamped time `min (max r 0) U`. -/
def clampTime (U r : ℝ) : ℝ := min (max r 0) U

theorem clampTime_mem {U : ℝ} (hU : 0 ≤ U) (r : ℝ) : clampTime U r ∈ Icc 0 U :=
  ⟨le_min (le_max_right _ _) hU, min_le_right _ _⟩

theorem clampTime_of_mem {U r : ℝ} (hr : r ∈ Icc 0 U) : clampTime U r = r := by
  unfold clampTime; rw [max_eq_left hr.1, min_eq_left hr.2]

theorem continuous_clampTime (U : ℝ) : Continuous (clampTime U) := by
  unfold clampTime; fun_prop

/-- Rates at the clamped time `s + clampTime U r`. -/
def rateC (F : Matrix (Fin N) (Fin N) ℂ) (a s U : ℝ) (ω : FlowSample N) (r : ℝ) :
    Fin N → Fin N → ℝ :=
  flowRate F a ω (s + clampTime U r)

/-- `(𝓑_{s+r} f(s+r))(ζ)` with clamped rates. -/
def genC (F : Matrix (Fin N) (Fin N) ℂ) (a s U : ℝ) (f : Occ N → ℝ → FlowSample N → ℝ)
    (ζ : Occ N) (r : ℝ) (ω : FlowSample N) : ℝ :=
  momentGenerator (rateC F a s U ω r) (fun ζ' => f ζ' (s + r) ω) ζ

/-- The increment `f(s+u) - f(s) - ∫_{(0,u]} 𝓑 f`. -/
def incC (F : Matrix (Fin N) (Fin N) ℂ) (a s U : ℝ) (f : Occ N → ℝ → FlowSample N → ℝ)
    (ζ : Occ N) (u : ℝ) (ω : FlowSample N) : ℝ :=
  f ζ (s + u) ω - f ζ s ω - ∫ r in Ioc (0 : ℝ) u, genC F a s U f ζ r ω

theorem measurable_rateC (F : Matrix (Fin N) (Fin N) ℂ) (a s U : ℝ) (i j : Fin N) :
    Measurable (fun p : ℝ × FlowSample N => rateC F a s U p.2 p.1 i j) := by
  have hg : Measurable (fun p : ℝ × FlowSample N => (s + clampTime U p.1, p.2)) := by
    have h1 : Measurable (fun p : ℝ × FlowSample N => s + clampTime U p.1) :=
      ((continuous_const.add (continuous_clampTime U)).measurable).comp measurable_fst
    exact h1.prodMk measurable_snd
  have hlam : ∀ k, Measurable (fun p : ℝ × FlowSample N => flowEigenvalue F a p.2
      (s + clampTime U p.1) k) := fun k => by
    have := (measurable_flowEigenvalue_uncurry F a k).comp hg
    simpa only [Function.comp_def] using this
  unfold rateC flowRate
  exact (measurable_const.mul (((hlam i).sub (hlam j)).pow_const 2)).inv

/-- Joint `borel ⊗ 𝓛` measurability of the clamped rates. -/
theorem measurable_rateC_pathSigma {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (a : ℝ) {s c U : ℝ} (hU : 0 ≤ U) (hsc : s + U ≤ c) (i j : Fin N) :
    Measurable[@Prod.instMeasurableSpace ℝ (FlowSample N) _ (pathSigma F a s c)]
      (fun p : ℝ × FlowSample N => rateC F a s U p.2 p.1 i j) := by
  have hlam : ∀ k, Measurable[@Prod.instMeasurableSpace ℝ (FlowSample N) _ (pathSigma F a s c)]
      (fun p : ℝ × FlowSample N => flowEigenvalue F a p.2 (s + clampTime U p.1) k) := by
    intro k
    refine measurable_uncurry_of_continuous_of_measurable (m := pathSigma F a s c)
      (u := fun r ω => flowEigenvalue F a ω (s + clampTime U r) k)
      (fun ω => (continuous_flowEigenvalue hF a ω k).comp
        (continuous_const.add (continuous_clampTime U))) (fun r => ?_)
    have hm := clampTime_mem hU r
    exact measurable_flowEigenvalue_pathSigma F a s c ⟨by linarith [hm.1], by linarith [hm.2]⟩ k
  unfold rateC flowRate
  exact (measurable_const.mul (((hlam i).sub (hlam j)).pow_const 2)).inv

theorem measurable_rateC_slice (F : Matrix (Fin N) (Fin N) ℂ)
    (a : ℝ) {s c U : ℝ} (hU : 0 ≤ U) (hsc : s + U ≤ c) (r : ℝ) (i j : Fin N) :
    Measurable[pathSigma F a s c] (fun ω => rateC F a s U ω r i j) := by
  have hm := clampTime_mem hU r
  have hσ : s + clampTime U r ∈ Icc s c := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  unfold rateC flowRate
  exact (measurable_const.mul (((measurable_flowEigenvalue_pathSigma F a s c hσ i).sub
    (measurable_flowEigenvalue_pathSigma F a s c hσ j)).pow_const 2)).inv

theorem rateC_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s δ : ℝ} {U : ℝ≥0}
    (hδ : 0 < δ) {ω : FlowSample N} (hω : ω ∈ gapGood F a δ s U) (r : ℝ) {i j : Fin N}
    (hij : i ≠ j) : |rateC F a s U ω r i j| ≤ ((N : ℝ) * δ ^ 2)⁻¹ := by
  unfold rateC
  rw [abs_of_nonneg (flowRate_nonneg _ _ _ _ _ _)]
  have hm := clampTime_mem U.2 r
  exact flowRate_le_of_gap hδ (gap_ge_of_gapGood hF hω hm.1 hm.2 hij)

theorem rateC_eq {F : Matrix (Fin N) (Fin N) ℂ} {a s : ℝ} {U : ℝ} {ω : FlowSample N} {r : ℝ}
    (hr : r ∈ Icc 0 U) : rateC F a s U ω r = flowRate F a ω (s + r) := by
  unfold rateC; rw [clampTime_of_mem hr]

/-- The generator bound on the gap event. -/
def genBound (N : ℕ) (q : Fin N → ℂ) (δ : ℝ) (ζ : Occ N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ((N : ℝ) * δ ^ 2)⁻¹ * jumpCoeff ζ i j *
    (momentLevel q (move ζ i j) + momentLevel q ζ)

theorem abs_genC_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s δ : ℝ}
    {U : ℝ≥0} (hδ : 0 < δ) (q : Fin N → ℂ) {f : Occ N → ℝ → FlowSample N → ℝ}
    (hf : ∀ ζ σ ω, |f ζ σ ω| ≤ momentLevel q ζ) {ω : FlowSample N}
    (hω : ω ∈ gapGood F a δ s U) (ζ : Occ N) (r : ℝ) :
    |genC F a s U f ζ r ω| ≤ genBound N q δ ζ :=
  abs_momentGenerator_le (fun _ _ hij => rateC_le hF hδ hω r hij) (fun ζ' => hf ζ' _ ω) ζ

theorem measurable_genC (F : Matrix (Fin N) (Fin N) ℂ) (a s U : ℝ)
    {f : Occ N → ℝ → FlowSample N → ℝ} (hf : ∀ ζ, Measurable fun p : ℝ × FlowSample N => f ζ p.1 p.2)
    (ζ : Occ N) : Measurable (fun p : ℝ × FlowSample N => genC F a s U f ζ p.1 p.2) :=
  measurable_momentGenerator_param (fun i j => measurable_rateC F a s U i j)
    (fun ζ' => (hf ζ').comp ((measurable_const.add measurable_fst).prodMk measurable_snd)) ζ

theorem measurable_genC_pathSigma {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {s c U : ℝ} (hU : 0 ≤ U) (hsc : s + U ≤ c) {f : Occ N → ℝ → FlowSample N → ℝ}
    (hf : ∀ ζ, Measurable[@Prod.instMeasurableSpace ℝ (FlowSample N) _ (pathSigma F a s c)]
      fun p : ℝ × FlowSample N => f ζ p.1 p.2) (ζ : Occ N) :
    Measurable[@Prod.instMeasurableSpace ℝ (FlowSample N) _ (pathSigma F a s c)]
      (fun p : ℝ × FlowSample N => genC F a s U f ζ p.1 p.2) :=
  @measurable_momentGenerator_param N (ℝ × FlowSample N)
    (@Prod.instMeasurableSpace ℝ (FlowSample N) _ (pathSigma F a s c)) _ _
    (fun i j => measurable_rateC_pathSigma hF a hU hsc i j)
    (fun ζ' => (hf ζ').comp ((measurable_const.add measurable_fst).prodMk measurable_snd)) ζ

/-!
## Step 1: the identity for the clamped moments
-/

/-- The clamped moments as a process `ζ σ ω`. -/
abbrev Ycl (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) :
    Occ N → ℝ → FlowSample N → ℝ :=
  fun ζ σ ω => clampedMoment F a q ζ σ ω

theorem gapGood_mono {F : Matrix (Fin N) (Fin N) ℂ} {a δ s : ℝ} {u U : ℝ≥0} (hu : u ≤ U) :
    gapGood F a δ s U ⊆ gapGood F a δ s u :=
  fun _ hω v hv0 hvu i j hij => hω v hv0 (hvu.trans (by exact_mod_cast hu)) i j hij

theorem simple_of_gapGood {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a δ s : ℝ}
    (hδ : 0 < δ) {U : ℝ≥0} {ω : FlowSample N} (hω : ω ∈ gapGood F a δ s U)
    (hH : ω.1.IsHermitian) {v : ℝ} (hv0 : 0 ≤ v) (hvU : v ≤ U) :
    HasSimpleSpectrum N (flowMatrix F a ω (s + v)) :=
  hasSimpleSpectrum_of_gap (flowMatrix_isHermitian hF a hH _) hδ fun _ _ hij =>
    gap_ge_of_gapGood hF hω hv0 hvU hij

theorem momentIncrement_eq_incC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s δ : ℝ}
    (hδ : 0 < δ) (q : Fin N → ℂ) (ζ : Occ N) {u U : ℝ≥0} (hu : u ≤ U) {ω : FlowSample N}
    (hω : ω ∈ gapGood F a δ s U) (hH : ω.1.IsHermitian) :
    momentIncrement F a q ζ s u ω = incC F a s U (Ycl F a q) ζ u ω := by
  have hY : ∀ v : ℝ, 0 ≤ v → v ≤ U → ∀ ζ' : Occ N,
      momentMonomial (fun k => flowOverlap F a q (s + v) k ω) ζ' = Ycl F a q ζ' (s + v) ω :=
    fun v hv0 hvU ζ' => (clampedMoment_eq q ζ' (flowMatrix_isHermitian hF a hH _)
      (simple_of_gapGood hF hδ hω hH hv0 hvU)).symm
  have hu' : (u : ℝ) ≤ U := by exact_mod_cast hu
  unfold momentIncrement incC
  rw [hY u u.2 hu' ζ]
  have h0 := hY 0 le_rfl U.2 ζ
  rw [add_zero] at h0
  rw [h0]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hrU : r ∈ Icc 0 (U : ℝ) := ⟨hr.1.le, hr.2.trans hu'⟩
  simp only [genC, flowMomentGenerator]
  rw [rateC_eq hrU]
  congr 1
  funext ζ'
  exact hY r hrU.1 hrU.2 ζ'

/-- **Step 1.** The integrated identity for the clamped moments on `B_δ = gapGood F a δ s U`. -/
theorem identity_clamped (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (has : a < s) (q : Fin N → ℂ) (ζ : Occ N) {U : ℝ≥0}
    (hsc : s + U ≤ c) {u : ℝ≥0} (hu : u ≤ U) {δ : ℝ} (hδ : 0 < δ) {Λ : FlowSample N → ℝ}
    (hΛ : Measurable[pathSigma F a s c] Λ) {C : ℝ} (hΛb : ∀ ω, |Λ ω| ≤ C) :
    Integrable (fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        incC F a s U (Ycl F a q) ζ u ω) (flowLaw N a) ∧
      ∫ ω, (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        incC F a s U (Ycl F a q) ζ u ω ∂flowLaw N a = 0 := by
  set Λ' : FlowSample N → ℝ := fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω
  have hΛ' : Measurable[pathSigma F a s c] Λ' :=
    (measurable_const.indicator (measurableSet_gapGood F a δ hsc)).mul hΛ
  have hΛ'b : ∃ C', ∀ ω, |Λ' ω| ≤ C' := by
    refine ⟨max C 0, fun ω => ?_⟩
    simp only [Λ']
    by_cases h : ω ∈ gapGood F a δ s U
    · rw [Set.indicator_of_mem h, one_mul]; exact (hΛb _).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem h, zero_mul, abs_zero]; exact le_max_right _ _
  have huc : s + (u : ℝ) ≤ c := le_trans (by gcongr) hsc
  have key := integrated_moment_identity hDBM hF has q ζ huc hδ hΛ' hΛ'b
  have hHerm : ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian := by
    filter_upwards [hermProj_ae_eq (N := N) a] with ω hω
    rw [← hω]; exact hermPart_isHermitian _
  have hae : (fun ω => (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ' ω *
      momentIncrement F a q ζ s u ω) =ᵐ[flowLaw N a]
      fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        incC F a s U (Ycl F a q) ζ u ω := by
    filter_upwards [hHerm] with ω hH
    by_cases hω : ω ∈ gapGood F a δ s U
    · simp only [Λ', Set.indicator_of_mem hω, Set.indicator_of_mem (gapGood_mono hu hω), one_mul]
      rw [momentIncrement_eq_incC hF hδ q ζ hu hω hH]
    · simp [Λ', hω]
  exact ⟨key.1.congr hae, (integral_congr_ae hae).symm.trans key.2⟩

/-!
## Step 2: Fubini and pull-out, from the clamped moments to the version
-/

/-- The jointly measurable version as a process `ζ σ ω`. -/
abbrev Vver (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ) :
    Occ N → ℝ → FlowSample N → ℝ :=
  fun ζ σ ω => momentVersion F a s c q ζ σ ω

theorem measurable_Ycl (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) (ζ : Occ N)
    (σ : ℝ) : Measurable (Ycl F a q ζ σ) :=
  (measurable_clampedMomentOf q ζ).comp (measurable_flowMatrix F a σ)

theorem measurable_Vver (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ) (ζ : Occ N)
    (σ : ℝ) : Measurable (Vver F a s c q ζ σ) :=
  (measurable_momentVersion_slice F a s c q ζ σ).mono (pathSigma_le F a s c) le_rfl

theorem genBound_nonneg (q : Fin N → ℂ) (δ : ℝ) (ζ : Occ N) : 0 ≤ genBound N q δ ζ := by
  unfold genBound
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have := momentLevel_nonneg q (move ζ i j)
  have := momentLevel_nonneg q ζ
  have := jumpCoeff_nonneg ζ i j
  have : 0 ≤ ((N : ℝ) * δ ^ 2)⁻¹ := by positivity
  positivity

/-- Hypotheses on a weight `g = 1_{B_δ} Λ`. -/
structure GapWeight (F : Matrix (Fin N) (Fin N) ℂ) (a s c δ : ℝ) (U : ℝ≥0) (C : ℝ)
    (g : FlowSample N → ℝ) : Prop where
  meas : Measurable[pathSigma F a s c] g
  bound : ∀ ω, |g ω| ≤ C
  off : ∀ ω, ω ∉ gapGood F a δ s U → g ω = 0

theorem GapWeight.measurable {F : Matrix (Fin N) (Fin N) ℂ} {a s c δ : ℝ} {U : ℝ≥0} {C : ℝ}
    {g : FlowSample N → ℝ} (hg : GapWeight F a s c δ U C g) : Measurable g :=
  hg.meas.mono (pathSigma_le F a s c) le_rfl

theorem integrable_weight_mul {F : Matrix (Fin N) (Fin N) ℂ} {a s c δ : ℝ} {U : ℝ≥0} {C : ℝ}
    {g : FlowSample N → ℝ} (hg : GapWeight F a s c δ U C g) {h : FlowSample N → ℝ}
    (hh : Measurable h) {L : ℝ} (hhb : ∀ ω, ω ∈ gapGood F a δ s U → |h ω| ≤ L) :
    Integrable (fun ω => g ω * h ω) (flowLaw N a) := by
  refine Integrable.of_bound (C := C * max L 0) (hg.measurable.mul hh).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg.bound ω)
  by_cases hω : ω ∈ gapGood F a δ s U
  · exact mul_le_mul (hg.bound ω) ((hhb ω hω).trans (le_max_left _ _)) (abs_nonneg _) hC
  · rw [hg.off ω hω, abs_zero, zero_mul]; positivity

/-- Pull-out for the clamped moments: `∫ h Ycl = ∫ h Φ̃` for bounded `𝓛`-measurable `h`. -/
theorem integral_mul_Ycl_eq (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) (σ : ℝ) {h : FlowSample N → ℝ} (hh : Measurable[pathSigma F a s c] h) {C : ℝ}
    (hhb : ∀ ω, |h ω| ≤ C) :
    ∫ ω, h ω * Ycl F a q ζ σ ω ∂flowLaw N a = ∫ ω, h ω * Vver F a s c q ζ σ ω ∂flowLaw N a := by
  have hint : Integrable (Ycl F a q ζ σ) (flowLaw N a) :=
    Integrable.of_bound (C := momentLevel q ζ)
      (measurable_Ycl F a q ζ σ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact abs_clampedMoment_le F a q ζ σ ω)
  rw [integral_mul_condExp (pathSigma_le F a s c) hh hhb hint]
  refine integral_congr_ae ?_
  filter_upwards [momentVersion_ae_eq F a s c q ζ σ] with ω hω
  simp only [Vver]
  rw [hω]

/-- `g · 𝓑 f` as a double sum with `𝓛`-measurable coefficients. -/
theorem weight_mul_genC (F : Matrix (Fin N) (Fin N) ℂ) (a s U : ℝ) (g : FlowSample N → ℝ)
    (f : Occ N → ℝ → FlowSample N → ℝ) (ζ : Occ N) (r : ℝ) (ω : FlowSample N) :
    g ω * genC F a s U f ζ r ω = ∑ i, ∑ j ∈ Finset.univ.erase i,
      (g ω * rateC F a s U ω r i j * jumpCoeff ζ i j) * (f (move ζ i j) (s + r) ω - f ζ (s + r) ω) := by
  unfold genC momentGenerator
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem integral_weight_mul_genC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s c δ : ℝ} (hδ : 0 < δ) {U : ℝ≥0} (hsc : s + U ≤ c) {C : ℝ} {g : FlowSample N → ℝ}
    (hg : GapWeight F a s c δ U C g) (q : Fin N → ℂ) {f : Occ N → ℝ → FlowSample N → ℝ}
    (hfm : ∀ ζ σ, Measurable (f ζ σ)) (hfb : ∀ ζ σ ω, |f ζ σ ω| ≤ momentLevel q ζ)
    (ζ : Occ N) (r : ℝ) :
    ∫ ω, g ω * genC F a s U f ζ r ω ∂flowLaw N a = ∑ i, ∑ j ∈ Finset.univ.erase i,
      ((∫ ω, (g ω * rateC F a s U ω r i j * jumpCoeff ζ i j) * f (move ζ i j) (s + r) ω
          ∂flowLaw N a) -
        ∫ ω, (g ω * rateC F a s U ω r i j * jumpCoeff ζ i j) * f ζ (s + r) ω ∂flowLaw N a) := by
  have hcoef : ∀ i j, i ≠ j → GapWeight F a s c δ U (C * ((N : ℝ) * δ ^ 2)⁻¹ * jumpCoeff ζ i j)
      (fun ω => g ω * rateC F a s U ω r i j * jumpCoeff ζ i j) := by
    intro i j hij
    refine ⟨(hg.meas.mul (measurable_rateC_slice F a U.2 hsc r i j)).mul_const _,
      fun ω => ?_, fun ω hω => by simp [hg.off ω hω]⟩
    have hC : 0 ≤ C := (abs_nonneg _).trans (hg.bound ω)
    rw [abs_mul, abs_mul, abs_of_nonneg (jumpCoeff_nonneg ζ i j)]
    refine mul_le_mul_of_nonneg_right ?_ (jumpCoeff_nonneg ζ i j)
    by_cases hω : ω ∈ gapGood F a δ s U
    · exact mul_le_mul (hg.bound ω) (rateC_le hF hδ hω r hij) (abs_nonneg _) hC
    · rw [hg.off ω hω, abs_zero, zero_mul]; positivity
  have hint : ∀ i j, i ≠ j → ∀ ζ', Integrable (fun ω => (g ω * rateC F a s U ω r i j *
      jumpCoeff ζ i j) * f ζ' (s + r) ω) (flowLaw N a) := fun i j hij ζ' =>
    integrable_weight_mul (hcoef i j hij) (hfm ζ' _) (fun ω _ => hfb ζ' _ ω)
  have hterm : ∀ i, ∀ j ∈ Finset.univ.erase i, Integrable (fun ω =>
      (g ω * rateC F a s U ω r i j * jumpCoeff ζ i j) * (f (move ζ i j) (s + r) ω -
        f ζ (s + r) ω)) (flowLaw N a) := by
    intro i j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hj).1
    simp_rw [mul_sub]
    exact (hint i j hij _).sub (hint i j hij _)
  simp_rw [weight_mul_genC]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj => hterm i j hj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j hj => hterm i j hj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hj).1
  simp_rw [mul_sub]
  exact integral_sub (hint i j hij _) (hint i j hij _)

/-- The generator term is the same for the clamped moments and for the version. -/
theorem integral_weight_mul_genC_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s c δ : ℝ} (hδ : 0 < δ) {U : ℝ≥0} (hsc : s + U ≤ c) {C : ℝ} {g : FlowSample N → ℝ}
    (hg : GapWeight F a s c δ U C g) (q : Fin N → ℂ) (ζ : Occ N) (r : ℝ) :
    ∫ ω, g ω * genC F a s U (Ycl F a q) ζ r ω ∂flowLaw N a =
      ∫ ω, g ω * genC F a s U (Vver F a s c q) ζ r ω ∂flowLaw N a := by
  have hYm : ∀ ζ σ, Measurable (Ycl F a q ζ σ) := measurable_Ycl F a q
  have hVm : ∀ ζ σ, Measurable (Vver F a s c q ζ σ) := measurable_Vver F a s c q
  rw [integral_weight_mul_genC hF hδ hsc hg q (f := Ycl F a q) hYm
      (fun ζ σ ω => abs_clampedMoment_le F a q ζ σ ω) ζ r,
    integral_weight_mul_genC hF hδ hsc hg q (f := Vver F a s c q) hVm
      (fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω) ζ r]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hj).1
  have hm : Measurable[pathSigma F a s c]
      (fun ω => g ω * rateC F a s U ω r i j * jumpCoeff ζ i j) :=
    (hg.meas.mul (measurable_rateC_slice F a U.2 hsc r i j)).mul_const _
  have hb : ∀ ω, |g ω * rateC F a s U ω r i j * jumpCoeff ζ i j| ≤
      C * ((N : ℝ) * δ ^ 2)⁻¹ * jumpCoeff ζ i j := by
    intro ω
    have hC : 0 ≤ C := (abs_nonneg _).trans (hg.bound ω)
    rw [abs_mul, abs_mul, abs_of_nonneg (jumpCoeff_nonneg ζ i j)]
    refine mul_le_mul_of_nonneg_right ?_ (jumpCoeff_nonneg ζ i j)
    by_cases hω : ω ∈ gapGood F a δ s U
    · exact mul_le_mul (hg.bound ω) (rateC_le hF hδ hω r hij) (abs_nonneg _) hC
    · rw [hg.off ω hω, abs_zero, zero_mul]; positivity
  rw [integral_mul_Ycl_eq F a s c q _ _ hm hb, integral_mul_Ycl_eq F a s c q _ _ hm hb]

theorem isFiniteMeasure_restrict_Ioc (u : ℝ) :
    IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) u)) :=
  ⟨by simp [Real.volume_Ioc]⟩

/-- Fubini for `∫ g ∫_{(0,u]} 𝓑 f`. -/
theorem integral_weight_mul_integral_genC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s c δ : ℝ} (hδ : 0 < δ) {U : ℝ≥0} {C : ℝ} {g : FlowSample N → ℝ}
    (hg : GapWeight F a s c δ U C g) (q : Fin N → ℂ) {f : Occ N → ℝ → FlowSample N → ℝ}
    (hfm : ∀ ζ, Measurable fun p : ℝ × FlowSample N => f ζ p.1 p.2)
    (hfb : ∀ ζ σ ω, |f ζ σ ω| ≤ momentLevel q ζ) (ζ : Occ N) (u : ℝ) :
    Integrable (fun ω => g ω * ∫ r in Ioc (0 : ℝ) u, genC F a s U f ζ r ω) (flowLaw N a) ∧
    ∫ ω, g ω * (∫ r in Ioc (0 : ℝ) u, genC F a s U f ζ r ω) ∂flowLaw N a =
      ∫ r in Ioc (0 : ℝ) u, ∫ ω, g ω * genC F a s U f ζ r ω ∂flowLaw N a := by
  have := isFiniteMeasure_restrict_Ioc u
  have hG := measurable_genC F a s U hfm ζ
  have hprod : Integrable (Function.uncurry fun ω r => g ω * genC F a s U f ζ r ω)
      ((flowLaw N a).prod (volume.restrict (Ioc (0 : ℝ) u))) := by
    refine Integrable.of_bound (C := C * genBound N q δ ζ)
      ((hg.measurable.comp measurable_fst).mul (hG.comp measurable_swap)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨ω, r⟩ := p
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
    have hC : 0 ≤ C := (abs_nonneg _).trans (hg.bound ω)
    by_cases hω : ω ∈ gapGood F a δ s U
    · exact mul_le_mul (hg.bound _) (abs_genC_le hF hδ q hfb hω ζ r) (abs_nonneg _) hC
    · rw [hg.off _ hω, abs_zero, zero_mul]; exact mul_nonneg hC (genBound_nonneg q δ ζ)
  refine ⟨?_, ?_⟩
  · have := hprod.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Function.uncurry_apply_pair]
    exact integral_const_mul _ _
  · have e : ∀ ω, g ω * ∫ r in Ioc (0 : ℝ) u, genC F a s U f ζ r ω =
        ∫ r in Ioc (0 : ℝ) u, g ω * genC F a s U f ζ r ω := fun ω =>
      (integral_const_mul _ _).symm
    simp_rw [e]
    exact integral_integral_swap hprod

/-- Integrability of `g · incC f`. -/
theorem integrable_weight_mul_incC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s c δ : ℝ} (hδ : 0 < δ) {U : ℝ≥0} {C : ℝ} {g : FlowSample N → ℝ}
    (hg : GapWeight F a s c δ U C g) (q : Fin N → ℂ) {f : Occ N → ℝ → FlowSample N → ℝ}
    (hfm : ∀ ζ, Measurable fun p : ℝ × FlowSample N => f ζ p.1 p.2)
    (hfb : ∀ ζ σ ω, |f ζ σ ω| ≤ momentLevel q ζ) (ζ : Occ N) (u : ℝ) :
    Integrable (fun ω => g ω * f ζ (s + u) ω) (flowLaw N a) ∧
    Integrable (fun ω => g ω * f ζ s ω) (flowLaw N a) ∧
    ∫ ω, g ω * incC F a s U f ζ u ω ∂flowLaw N a =
      ∫ ω, g ω * f ζ (s + u) ω ∂flowLaw N a - ∫ ω, g ω * f ζ s ω ∂flowLaw N a -
        ∫ ω, g ω * (∫ r in Ioc (0 : ℝ) u, genC F a s U f ζ r ω) ∂flowLaw N a := by
  have h1 : Integrable (fun ω => g ω * f ζ (s + u) ω) (flowLaw N a) :=
    integrable_weight_mul hg (by
      have := (hfm ζ).comp (measurable_const.prodMk (measurable_id (α := FlowSample N)))
        (f := fun ω => ((s + u : ℝ), ω))
      simpa only [Function.comp_def] using this) (fun ω _ => hfb ζ _ ω)
  have h2 : Integrable (fun ω => g ω * f ζ s ω) (flowLaw N a) :=
    integrable_weight_mul hg (by
      have := (hfm ζ).comp (measurable_const.prodMk (measurable_id (α := FlowSample N)))
        (f := fun ω => (s, ω))
      simpa only [Function.comp_def] using this) (fun ω _ => hfb ζ _ ω)
  have h3 := (integral_weight_mul_integral_genC hF hδ hg q hfm hfb ζ u).1
  refine ⟨h1, h2, ?_⟩
  have e : (fun ω => g ω * incC F a s U f ζ u ω) = fun ω => g ω * f ζ (s + u) ω -
      g ω * f ζ s ω - g ω * ∫ r in Ioc (0 : ℝ) u, genC F a s U f ζ r ω := by
    funext ω; simp only [incC]; ring
  have h12 : Integrable (fun ω => g ω * f ζ (s + u) ω - g ω * f ζ s ω) (flowLaw N a) :=
    h1.sub h2
  rw [e, integral_sub h12 h3, integral_sub h1 h2]

/-- **Step 2.** The integrated identity for the version on `B_δ`. -/
theorem identity_version (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (has : a < s) (q : Fin N → ℂ) (ζ : Occ N) {U : ℝ≥0}
    (hsc : s + U ≤ c) {u : ℝ≥0} (hu : u ≤ U) {δ : ℝ} (hδ : 0 < δ) {Λ : FlowSample N → ℝ}
    (hΛ : Measurable[pathSigma F a s c] Λ) {C : ℝ} (hΛb : ∀ ω, |Λ ω| ≤ C) :
    ∫ ω, (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
      incC F a s U (Vver F a s c q) ζ u ω ∂flowLaw N a = 0 := by
  set g : FlowSample N → ℝ := fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω
  have hg : GapWeight F a s c δ U (max C 0) g := by
    refine ⟨(measurable_const.indicator (measurableSet_gapGood F a δ hsc)).mul hΛ,
      fun ω => ?_, fun ω hω => by simp [g, hω]⟩
    simp only [g]
    by_cases h : ω ∈ gapGood F a δ s U
    · rw [Set.indicator_of_mem h, one_mul]; exact (hΛb _).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem h, zero_mul, abs_zero]; exact le_max_right _ _
  have hYm : ∀ ζ, Measurable fun p : ℝ × FlowSample N => Ycl F a q ζ p.1 p.2 :=
    fun ζ => measurable_clampedMoment_uncurry F a q ζ
  have hYb : ∀ ζ σ ω, |Ycl F a q ζ σ ω| ≤ momentLevel q ζ :=
    fun ζ σ ω => abs_clampedMoment_le F a q ζ σ ω
  have hVm : ∀ ζ, Measurable fun p : ℝ × FlowSample N => Vver F a s c q ζ p.1 p.2 :=
    fun ζ => measurable_momentVersion F a s c q ζ
  have hVb : ∀ ζ σ ω, |Vver F a s c q ζ σ ω| ≤ momentLevel q ζ :=
    fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω
  have hgb : ∀ ω, |g ω| ≤ max C 0 := hg.bound
  have key := (identity_clamped hDBM hF has q ζ hsc hu hδ hΛ hΛb).2
  change ∫ ω, g ω * incC F a s U (Ycl F a q) ζ u ω ∂flowLaw N a = 0 at key
  change ∫ ω, g ω * incC F a s U (Vver F a s c q) ζ u ω ∂flowLaw N a = 0
  rw [(integrable_weight_mul_incC hF hδ hg q hYm hYb ζ u).2.2] at key
  rw [(integrable_weight_mul_incC hF hδ hg q hVm hVb ζ u).2.2,
    (integral_weight_mul_integral_genC hF hδ hg q hVm hVb ζ u).2]
  rw [(integral_weight_mul_integral_genC hF hδ hg q hYm hYb ζ u).2] at key
  rw [← integral_mul_Ycl_eq F a s c q ζ _ hg.meas hgb,
    ← integral_mul_Ycl_eq F a s c q ζ _ hg.meas hgb]
  have hr : ∀ r, ∫ ω, g ω * genC F a s U (Vver F a s c q) ζ r ω ∂flowLaw N a =
      ∫ ω, g ω * genC F a s U (Ycl F a q) ζ r ω ∂flowLaw N a :=
    fun r => (integral_weight_mul_genC_eq hF hδ hsc hg q ζ r).symm
  simp_rw [hr]
  exact key

/-!
## Step 3: the version's increment vanishes on `B_δ`
-/

theorem measurable_incV_pathSigma {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a s c : ℝ} (q : Fin N → ℂ) (ζ : Occ N) {U : ℝ≥0} (hsc : s + U ≤ c) (u : ℝ) :
    Measurable[pathSigma F a s c] (incC F a s U (Vver F a s c q) ζ u) := by
  have hG := measurable_genC_pathSigma hF a U.2 hsc
    (f := Vver F a s c q) (fun ζ => measurable_momentVersion_pathSigma F a s c q ζ) ζ
  have hI := @measurable_setIntegral_prod (FlowSample N) (pathSigma F a s c) _ hG (Ioc 0 u)
  exact ((measurable_momentVersion_slice F a s c q ζ _).sub
    (measurable_momentVersion_slice F a s c q ζ _)).sub hI

/-- **Step 3.** `Φ̃_ζ(s+u) = Φ̃_ζ(s) + ∫_{(0,u]} 𝓑 Φ̃` almost surely on `B_δ`. -/
theorem incV_ae_zero (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (has : a < s) (q : Fin N → ℂ) (ζ : Occ N) {U : ℝ≥0}
    (hsc : s + U ≤ c) {u : ℝ≥0} (hu : u ≤ U) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂flowLaw N a, ω ∈ gapGood F a δ s U → incC F a s U (Vver F a s c q) ζ u ω = 0 := by
  set D : FlowSample N → ℝ := fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω *
    incC F a s U (Vver F a s c q) ζ u ω
  have hDm : Measurable[pathSigma F a s c] D :=
    (measurable_const.indicator (measurableSet_gapGood F a δ hsc)).mul
      (measurable_incV_pathSigma hF q ζ hsc u)
  have hgw : GapWeight F a s c δ U 1 (fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω) := by
    refine ⟨measurable_const.indicator (measurableSet_gapGood F a δ hsc), fun ω => ?_,
      fun ω hω => by simp [hω]⟩
    by_cases h : ω ∈ gapGood F a δ s U <;> simp [h]
  have hDint : Integrable D (flowLaw N a) := by
    have h := integrable_weight_mul_incC hF hδ hgw q (fun ζ => measurable_momentVersion F a s c q ζ)
      (fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω) ζ u
    have h3 := (integral_weight_mul_integral_genC hF hδ hgw q
      (fun ζ => measurable_momentVersion F a s c q ζ)
      (fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω) ζ u).1
    refine ((h.1.sub h.2.1).sub h3).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [D, incC, Pi.sub_apply]; ring
  have hD0 : D =ᵐ[flowLaw N a] 0 := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (pathSigma_le F a s c)
      (fun A _ _ => hDint.integrableOn) (fun A _ _ => integrableOn_zero) (fun A hA _ => ?_)
      hDm.aestronglyMeasurable stronglyMeasurable_zero.aestronglyMeasurable
    rw [Pi.zero_def, integral_zero, ← integral_indicator ((pathSigma_le F a s c) A hA)]
    have hΛ : Measurable[pathSigma F a s c] (A.indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hA
    have h := identity_version hDBM hF has q ζ hsc hu hδ hΛ (C := 1)
      (fun ω => by by_cases h : ω ∈ A <;> simp [h])
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans h
    simp only [D]
    by_cases h : ω ∈ A <;> simp [h]
  filter_upwards [hD0] with ω hω hB
  simpa [D, hB] using hω

end BlockBand.Palm.MomentFlow
