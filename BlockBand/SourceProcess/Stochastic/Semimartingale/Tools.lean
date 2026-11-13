module
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Measure-theoretic tools for the Taylor scheme

Setting: a probability space `(Ω, m₀, Q)` with an arbitrary (raw, not completed) filtration
`𝓖 : Filtration ℝ≥0 m₀`, or a sub-σ-algebra `m ≤ m₀`. All measurability statements are
`AEStronglyMeasurable[m] f Q` (a.e. equal to an `m`-strongly measurable function), the form
that survives on raw filtrations.

* `aestronglyMeasurable_of_tendsto_ae_sub`: a.e. limits keep `AEStronglyMeasurable[m]`.
* `aestronglyMeasurable_comp_of_continuousOn`: `f ∘ Z` with `f` continuous on a closed set
  containing the values of `Z` a.s.
* `martingale_integral_mul_sub_eq_zero`: `E[g (N_v - N_u)] = 0` for bounded `𝓖_u`-a.e.
  measurable `g`.
* `martingale_integral_mul_incr_incr`: `E[g ΔN¹ ΔN²] = E[g Δ(N¹N² - B)]` for bounded
  martingales `N¹, N²` and a martingale `B`.
* `exists_martingale_modification`: an a.e.-adapted integrable process with the martingale
  set-integral identity has a martingale modification.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped NNReal ENNReal

section Measurability

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {Q : Measure[m₀] Ω}

/-- A.e. limits of `m`-a.e.-strongly measurable functions (into a complete metrizable space)
are `m`-a.e.-strongly measurable, for a measure on a possibly larger σ-algebra. -/
theorem aestronglyMeasurable_of_tendsto_ae_sub {E : Type*} [TopologicalSpace E]
    [IsCompletelyMetrizableSpace E] [Nonempty E] {f : ℕ → Ω → E} {g : Ω → E}
    (hf : ∀ n, AEStronglyMeasurable[m] (f n) Q)
    (lim : ∀ᵐ ω ∂Q, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    AEStronglyMeasurable[m] g Q := by
  choose g' hg'm hg'e using hf
  refine ⟨fun ω => limUnder atTop (fun n => g' n ω), @StronglyMeasurable.limUnder ℕ Ω E m _ _ atTop _ _ _ _ hg'm, ?_⟩
  filter_upwards [lim, ae_all_iff.2 hg'e] with ω hω hω'
  have : Tendsto (fun n => g' n ω) atTop (𝓝 (g ω)) := by
    convert hω using 1
    funext n
    exact (hω' n).symm
  exact this.limUnder_eq.symm

/-- Composition with a function continuous on a closed set `K` that contains the values of
`Z` almost surely. -/
theorem aestronglyMeasurable_comp_of_continuousOn {E F : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] [PseudoMetrizableSpace F] [Zero F]
    [SecondCountableTopology E] [PseudoMetrizableSpace E]
    {K : Set E} (hK : IsClosed K) {f : E → F} (hf : ContinuousOn f K) {Z : Ω → E}
    (hZ : AEStronglyMeasurable[m] Z Q) (hZK : ∀ᵐ ω ∂Q, Z ω ∈ K) :
    AEStronglyMeasurable[m] (fun ω => f (Z ω)) Q := by
  classical
  have hmeas : Measurable (K.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hK.measurableSet
  refine ⟨fun ω => K.piecewise f (fun _ => 0) (hZ.mk Z ω),
    (hmeas.comp (hZ.stronglyMeasurable_mk.measurable)).stronglyMeasurable, ?_⟩
  filter_upwards [hZ.ae_eq_mk, hZK] with ω h1 h2
  rw [← h1, Set.piecewise_eq_of_mem _ _ _ h2]

end Measurability

section Martingale

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 m₀}

/-- `E[g (N_v - N_u)] = 0` for a martingale `N`, `u ≤ v`, and `g` bounded and
`𝓖_u`-a.e.-strongly measurable. -/
theorem martingale_integral_mul_sub_eq_zero {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓖 Q)
    {u v : ℝ≥0} (huv : u ≤ v) {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 u] g Q) {C : ℝ}
    (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * (N v ω - N u ω) ∂Q = 0 := by
  have hg' : AEStronglyMeasurable g Q := hg.mono (𝓖.le u)
  have hiv : Integrable (fun ω => g ω * N v ω) Q := (hN.integrable v).bdd_mul hg' hgC
  have hiu : Integrable (fun ω => g ω * N u ω) Q := (hN.integrable u).bdd_mul hg' hgC
  have h1 : ∫ ω, g ω * N v ω ∂Q = ∫ ω, g ω * N u ω ∂Q := by
    rw [← integral_condExp (𝓖.le u) (f := fun ω => g ω * N v ω)]
    refine integral_congr_ae ?_
    filter_upwards [condExp_mul_of_aestronglyMeasurable_left hg hiv (hN.integrable v),
      hN.condExp_ae_eq huv] with ω h1 h2
    rw [show (fun ω => g ω * N v ω) = g * N v from rfl, h1]
    simp [h2]
  simp_rw [mul_sub]
  rw [integral_sub hiv hiu, h1, sub_self]

/-- Bracket identity for increments: if `N¹, N²` are martingales bounded at times `u ≤ v`
and `B` is a martingale, then for bounded `𝓖_u`-a.e.-strongly measurable `g`,
`E[g (N¹_v - N¹_u)(N²_v - N²_u)] = E[g ((N¹_v N²_v - B_v) - (N¹_u N²_u - B_u))]`. -/
theorem martingale_integral_mul_incr_incr {N₁ N₂ B : ℝ≥0 → Ω → ℝ} (h₁ : Martingale N₁ 𝓖 Q)
    (h₂ : Martingale N₂ 𝓖 Q) (hB : Martingale B 𝓖 Q) {u v : ℝ≥0} (huv : u ≤ v) {M : ℝ}
    (h₁u : ∀ᵐ ω ∂Q, ‖N₁ u ω‖ ≤ M) (h₁v : ∀ᵐ ω ∂Q, ‖N₁ v ω‖ ≤ M)
    (h₂u : ∀ᵐ ω ∂Q, ‖N₂ u ω‖ ≤ M) (h₂v : ∀ᵐ ω ∂Q, ‖N₂ v ω‖ ≤ M)
    {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 u] g Q) {C : ℝ} (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * ((N₁ v ω - N₁ u ω) * (N₂ v ω - N₂ u ω)) ∂Q =
      ∫ ω, g ω * ((N₁ v ω * N₂ v ω - B v ω) - (N₁ u ω * N₂ u ω - B u ω)) ∂Q := by
  have hg' : AEStronglyMeasurable g Q := hg.mono (𝓖.le u)
  have m₁u : AEStronglyMeasurable[𝓖 u] (N₁ u) Q := (h₁.1 u).aestronglyMeasurable
  have m₂u : AEStronglyMeasurable[𝓖 u] (N₂ u) Q := (h₂.1 u).aestronglyMeasurable
  have m₁v : AEStronglyMeasurable (N₁ v) Q := ((h₁.1 v).mono (𝓖.le v)).aestronglyMeasurable
  have m₂v : AEStronglyMeasurable (N₂ v) Q := ((h₂.1 v).mono (𝓖.le v)).aestronglyMeasurable
  have hgN₁ : ∀ᵐ ω ∂Q, ‖g ω * N₁ u ω‖ ≤ C * M := by
    filter_upwards [hgC, h₁u] with ω a b
    rw [norm_mul]; exact mul_le_mul a b (norm_nonneg _) ((norm_nonneg _).trans a)
  have hgN₂ : ∀ᵐ ω ∂Q, ‖g ω * N₂ u ω‖ ≤ C * M := by
    filter_upwards [hgC, h₂u] with ω a b
    rw [norm_mul]; exact mul_le_mul a b (norm_nonneg _) ((norm_nonneg _).trans a)
  have e₁ := martingale_integral_mul_sub_eq_zero h₂ huv (hg.mul m₁u) hgN₁
  have e₂ := martingale_integral_mul_sub_eq_zero h₁ huv (hg.mul m₂u) hgN₂
  have e₃ := martingale_integral_mul_sub_eq_zero hB huv hg hgC
  have bvv : ∀ᵐ ω ∂Q, ‖N₁ v ω * N₂ v ω‖ ≤ M * M := by
    filter_upwards [h₁v, h₂v] with ω a b
    rw [norm_mul]; exact mul_le_mul a b (norm_nonneg _) ((norm_nonneg _).trans a)
  have buu : ∀ᵐ ω ∂Q, ‖N₁ u ω * N₂ u ω‖ ≤ M * M := by
    filter_upwards [h₁u, h₂u] with ω a b
    rw [norm_mul]; exact mul_le_mul a b (norm_nonneg _) ((norm_nonneg _).trans a)
  have iP : Integrable (fun ω => N₁ v ω * N₂ v ω - N₁ u ω * N₂ u ω) Q :=
    (Integrable.of_bound (m₁v.mul m₂v) _ bvv).sub
      (Integrable.of_bound ((m₁u.mono (𝓖.le u)).mul (m₂u.mono (𝓖.le u))) _ buu)
  have i₀ : Integrable (fun ω => g ω * (N₁ v ω * N₂ v ω - N₁ u ω * N₂ u ω)) Q :=
    iP.bdd_mul hg' hgC
  have iB : Integrable (fun ω => g ω * (B v ω - B u ω)) Q :=
    ((hB.integrable v).sub (hB.integrable u)).bdd_mul hg' hgC
  have bd₂ : ∀ᵐ ω ∂Q, ‖N₂ v ω - N₂ u ω‖ ≤ M + M := by
    filter_upwards [h₂u, h₂v] with ω a b
    exact (norm_sub_le _ _).trans (add_le_add b a)
  have bd₁ : ∀ᵐ ω ∂Q, ‖N₁ v ω - N₁ u ω‖ ≤ M + M := by
    filter_upwards [h₁u, h₁v] with ω a b
    exact (norm_sub_le _ _).trans (add_le_add b a)
  have i₁ : Integrable (fun ω => g ω * N₁ u ω * (N₂ v ω - N₂ u ω)) Q :=
    (Integrable.of_bound ((hg.mul m₁u).mono (𝓖.le u)) _ hgN₁).mul_bdd
      (m₂v.sub (m₂u.mono (𝓖.le u))) bd₂
  have i₂ : Integrable (fun ω => g ω * N₂ u ω * (N₁ v ω - N₁ u ω)) Q :=
    (Integrable.of_bound ((hg.mul m₂u).mono (𝓖.le u)) _ hgN₂).mul_bdd
      (m₁v.sub (m₁u.mono (𝓖.le u))) bd₁
  have L : (fun ω => g ω * ((N₁ v ω - N₁ u ω) * (N₂ v ω - N₂ u ω))) =
      fun ω => g ω * (N₁ v ω * N₂ v ω - N₁ u ω * N₂ u ω) -
        g ω * N₁ u ω * (N₂ v ω - N₂ u ω) - g ω * N₂ u ω * (N₁ v ω - N₁ u ω) := by
    funext ω; ring
  have R : (fun ω => g ω * ((N₁ v ω * N₂ v ω - B v ω) - (N₁ u ω * N₂ u ω - B u ω))) =
      fun ω => g ω * (N₁ v ω * N₂ v ω - N₁ u ω * N₂ u ω) - g ω * (B v ω - B u ω) := by
    funext ω; ring
  have i₀₁ : Integrable (fun ω => g ω * (N₁ v ω * N₂ v ω - N₁ u ω * N₂ u ω) -
      g ω * N₁ u ω * (N₂ v ω - N₂ u ω)) Q := i₀.sub i₁
  rw [L, R, integral_sub i₀₁ i₂, integral_sub i₀ i₁, integral_sub i₀ iB]
  simp only [Pi.mul_apply] at e₁ e₂
  rw [e₁, e₂, e₃, sub_zero]

/-- A process that is integrable, `𝓖_t`-a.e.-strongly measurable at each time and satisfies
`∫_A X_t = ∫_A X_s` for `s ≤ t`, `A ∈ 𝓖_s`, has a martingale modification
(`M_t = E[X_t | 𝓖_t]`). -/
theorem exists_martingale_modification {X : ℝ≥0 → Ω → ℝ} (hint : ∀ t, Integrable (X t) Q)
    (hmeas : ∀ t, AEStronglyMeasurable[𝓖 t] (X t) Q)
    (hset : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝓖 s] A →
      ∫ ω in A, X t ω ∂Q = ∫ ω in A, X s ω ∂Q) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] X t := by
  refine ⟨fun t => Q[X t | 𝓖 t], ⟨fun t => stronglyMeasurable_condExp, fun i j hij => ?_⟩,
    fun t => condExp_of_aestronglyMeasurable' (𝓖.le t) (hmeas t) (hint t)⟩
  have h1 := condExp_condExp_of_le (μ := Q) (f := X j) (𝓖.mono hij) (𝓖.le j)
  have h2 : X i =ᵐ[Q] Q[X j | 𝓖 i] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le i) (hint j)
      (fun s _ _ => (hint i).integrableOn) (fun s hs _ => (hset i j hij s hs).symm) (hmeas i)
  exact h1.trans (h2.symm.trans (condExp_of_aestronglyMeasurable' (𝓖.le i) (hmeas i)
    (hint i)).symm)

omit [IsProbabilityMeasure Q] in
/-- Multiplying a martingale by the indicator of a `𝓖_0`-set gives a martingale. -/
theorem martingale_indicator_zero {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓖 Q) {G : Set Ω}
    (hG : MeasurableSet[𝓖 0] G) : Martingale (fun t => G.indicator (N t)) 𝓖 Q := by
  have hGt : ∀ t, MeasurableSet[𝓖 t] G := fun t => 𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t) G hG
  refine ⟨fun t => (hN.1 t).indicator (hGt t), fun i j hij => ?_⟩
  filter_upwards [condExp_indicator (hN.integrable j) (hGt i), hN.condExp_ae_eq hij]
    with ω h1 h2
  rw [h1]
  by_cases hω : ω ∈ G <;> simp [hω, h2]

end Martingale

end BlockBand.SourceProcess.Stochastic.Semimartingale
