module

public import BlockBand.Endpoints.EndpointsAssemblyDefs
public import BlockBand.Model.Construction.MarkedStateTopology

/-!
# Common tools for the endpoint variance

We collect three tools used for the limiting variance of the critical endpoints theorem.

* `epv_markedIntegral f ξ = ∫ f dξ.marked` and its continuity in the vague topology for a
  continuous compactly supported `f` (it is a coordinate of that topology);
* `epv_lintegral_eq_of_laplace`: two nonnegative random variables with the same Laplace
  transform on `(0, ∞)` have the same expectation in `[0, ∞]` (Fatou, with
  `n(1 - e^{-x/n}) → x` and `n(1 - e^{-x/n}) ≤ x`; no finiteness is needed);
* `epv_lintegral_swap`: Tonelli for `∫ dμ(i) E_𝖯 Σ_{x∈ξ} h_i(x)` with `h_i` continuous in `i`,
  continuous in `x`, uniformly bounded and supported in a fixed `K × P(𝕋)` (the joint
  measurability is Carathéodory's: `measurable_uncurry_of_continuous_of_measurable`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

attribute [local instance] BlockBand.Model.Construction.massProfile_borelSpace

/-!
## 1. The vague coordinate `ξ ↦ ∫ f dξ.marked`
-/

/-- The marked integral `ξ ↦ ∫ f dξ.marked` (Bochner). -/
def epv_markedIntegral (f : MarkedSpectralSpace → ℝ) (ξ : MarkedPointMeasure) : ℝ :=
  ∫ x, f x ∂ξ.marked.measure

theorem epv_continuous_markedIntegral {f : MarkedSpectralSpace → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) : Continuous (epv_markedIntegral f) := by
  let F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ := ⟨⟨f, hf⟩, hfs⟩
  have h0 : Continuous fun ξ : VaguePointMeasure MarkedSpectralSpace =>
      fun g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ => ξ.coordinate g :=
    continuous_induced_dom
  have h1 : Continuous fun ξ : VaguePointMeasure MarkedSpectralSpace => ξ.coordinate F :=
    (continuous_apply F).comp h0
  exact h1.comp continuous_induced_dom

theorem epv_measurable_markedIntegral {f : MarkedSpectralSpace → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) : Measurable (epv_markedIntegral f) :=
  (epv_continuous_markedIntegral hf hfs).measurable

theorem epv_integrable_marked {f : MarkedSpectralSpace → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (ξ : MarkedPointMeasure) : Integrable f ξ.marked.measure :=
  hf.integrable_of_hasCompactSupport hfs

theorem epv_markedIntegral_nonneg {f : MarkedSpectralSpace → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (ξ : MarkedPointMeasure) : 0 ≤ epv_markedIntegral f ξ :=
  integral_nonneg hf0

theorem epv_lintegral_marked_eq {f : MarkedSpectralSpace → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) (ξ : MarkedPointMeasure) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ξ.marked.measure = ENNReal.ofReal (epv_markedIntegral f ξ) :=
  (ofReal_integral_eq_lintegral_ofReal (epv_integrable_marked hf hfs ξ)
    (Eventually.of_forall hf0)).symm

/-- A function on `ℝ × P(𝕋)` vanishing off `K × P(𝕋)`, `K` compact, has compact support. -/
theorem epv_hasCompactSupport_of_fst {f : MarkedSpectralSpace → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hf : ∀ x, x.1 ∉ K → f x = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (hK.prod isCompact_univ) fun x hx =>
    hf x fun h => hx ⟨h, mem_univ _⟩

/-- The weighted product `w ⊗ Ψ` of a spectral weight and a bounded continuous mark functional. -/
theorem epv_weight_product_props (w : SpectralWeight) (Ψ : MassProfile →ᵇ ℝ) :
    Continuous (fun x : MarkedSpectralSpace => w x.1 * Ψ x.2) ∧
      HasCompactSupport (fun x : MarkedSpectralSpace => w x.1 * Ψ x.2) :=
  ⟨(w.toContinuousMap.continuous.comp continuous_fst).mul (Ψ.continuous.comp continuous_snd),
    epv_hasCompactSupport_of_fst w.compactSupport fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]⟩

/-!
## 2. Laplace transforms determine expectations of nonnegative variables
-/

theorem epv_exp_bound_upper {c x : ℝ} (hc : 0 < c) :
    c * (1 - Real.exp (-(c⁻¹ * x))) ≤ x := by
  have h := Real.add_one_le_exp (-(c⁻¹ * x))
  have : c * (c⁻¹ * x) = x := by field_simp
  nlinarith

theorem epv_exp_bound_lower {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x - x ^ 2 * c⁻¹ ≤ c * (1 - Real.exp (-(c⁻¹ * x))) := by
  have hy : 0 ≤ c⁻¹ * x := by positivity
  have hE := Real.add_one_le_exp (c⁻¹ * x)
  have hEpos : 0 < Real.exp (c⁻¹ * x) := Real.exp_pos _
  have hinv : Real.exp (-(c⁻¹ * x)) = (Real.exp (c⁻¹ * x))⁻¹ := Real.exp_neg _
  rw [hinv]
  have h1 : (Real.exp (c⁻¹ * x))⁻¹ ≤ (c⁻¹ * x + 1)⁻¹ :=
    inv_anti₀ (by positivity) hE
  have h2 : c * (1 - (c⁻¹ * x + 1)⁻¹) = c * x / (c + x) := by
    field_simp
    ring
  have h3 : x - x ^ 2 * c⁻¹ ≤ c * x / (c + x) := by
    rw [le_div_iff₀ (by positivity)]
    have : (x - x ^ 2 * c⁻¹) * (c + x) = c * x - x ^ 3 * c⁻¹ := by field_simp; ring
    rw [this]
    have : 0 ≤ x ^ 3 * c⁻¹ := by positivity
    linarith
  nlinarith

theorem epv_tendsto_exp_approx {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (1 - Real.exp (-(((n : ℝ) + 1)⁻¹ * x)))) atTop
      (𝓝 x) := by
  have hlow : Tendsto (fun n : ℕ => x - x ^ 2 * ((n : ℝ) + 1)⁻¹) atTop (𝓝 x) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (x ^ 2)
    rw [mul_zero] at this
    simpa [one_div] using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => epv_exp_bound_lower (by positivity) hx)
    (fun n => epv_exp_bound_upper (by positivity))

/-- One inequality: if `E e^{-cX} = E e^{-cY}` for all `c > 0`, then `E X ≤ E Y` in `[0, ∞]`. -/
theorem epv_lintegral_le_of_laplace {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (h : ∀ c : ℝ, 0 < c →
      ∫ ω, Real.exp (-(c * X ω)) ∂P = ∫ ω, Real.exp (-(c * Y ω)) ∂P) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P := by
  set g : ℕ → ℝ → ℝ := fun n x => ((n : ℝ) + 1) * (1 - Real.exp (-(((n : ℝ) + 1)⁻¹ * x)))
    with hg
  have hgm : ∀ n, Measurable (g n) := fun n => by
    simp only [hg]; fun_prop
  -- the expectations of `g n ∘ X` and `g n ∘ Y` agree
  have hint : ∀ (n : ℕ) {Z : Ω → ℝ}, Measurable Z → (∀ ω, 0 ≤ Z ω) →
      Integrable (fun ω => g n (Z ω)) P := by
    intro n Z hZ hZ0
    refine Integrable.of_bound ((hgm n).comp hZ).aestronglyMeasurable ((n : ℝ) + 1)
      (Eventually.of_forall fun ω => ?_)
    have he0 := Real.exp_pos (-(((n : ℝ) + 1)⁻¹ * Z ω))
    have he1 : Real.exp (-(((n : ℝ) + 1)⁻¹ * Z ω)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := hZ0 ω; have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
                                nlinarith)
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [Real.norm_eq_abs, abs_le]
    simp only [hg]
    constructor <;> nlinarith
  have hexp_int : ∀ (n : ℕ) {Z : Ω → ℝ}, Measurable Z → (∀ ω, 0 ≤ Z ω) →
      Integrable (fun ω => Real.exp (-(((n : ℝ) + 1)⁻¹ * Z ω))) P := by
    intro n Z hZ hZ0
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by have := hZ0 ω; have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
                                    nlinarith)
  have hEq : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (g n (X ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (g n (Y ω)) ∂P := by
    intro n
    have hgn : ∀ {Z : Ω → ℝ}, Measurable Z → (∀ ω, 0 ≤ Z ω) →
        ∫ ω, g n (Z ω) ∂P = ((n : ℝ) + 1) * (1 - ∫ ω, Real.exp (-(((n : ℝ) + 1)⁻¹ * Z ω)) ∂P) := by
      intro Z hZ hZ0
      simp only [hg]
      rw [integral_const_mul, integral_sub (integrable_const 1) (hexp_int n hZ hZ0),
        integral_const, probReal_univ, one_smul]
    have hg0 : ∀ {Z : Ω → ℝ}, (∀ ω, 0 ≤ Z ω) → ∀ ω, 0 ≤ g n (Z ω) := by
      intro Z hZ0 ω
      have := epv_exp_bound_lower (c := (n : ℝ) + 1) (by positivity) (hZ0 ω)
      have he1 : Real.exp (-(((n : ℝ) + 1)⁻¹ * Z ω)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by have := hZ0 ω; have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
                                  nlinarith)
      simp only [hg]
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      nlinarith
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n hX hX0) (Eventually.of_forall (hg0 hX0)),
      ← ofReal_integral_eq_lintegral_ofReal (hint n hY hY0) (Eventually.of_forall (hg0 hY0)),
      hgn hX hX0, hgn hY hY0, h _ (by positivity)]
  calc ∫⁻ ω, ENNReal.ofReal (X ω) ∂P
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (g n (X ω))) atTop ∂P := by
        refine lintegral_congr fun ω => ?_
        exact ((ENNReal.continuous_ofReal.tendsto _).comp
          (epv_tendsto_exp_approx (hX0 ω))).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (g n (X ω)) ∂P) atTop :=
        lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp ((hgm n).comp hX)
    _ = liminf (fun n => ∫⁻ ω, ENNReal.ofReal (g n (Y ω)) ∂P) atTop := by simp_rw [hEq]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
        exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
          (epv_exp_bound_upper (by positivity))

/-- Two nonnegative measurable variables with the same Laplace transform on `(0, ∞)` have the
same expectation in `[0, ∞]`. -/
theorem epv_lintegral_eq_of_laplace {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (h : ∀ c : ℝ, 0 < c →
      ∫ ω, Real.exp (-(c * X ω)) ∂P = ∫ ω, Real.exp (-(c * Y ω)) ∂P) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂P = ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P :=
  le_antisymm (epv_lintegral_le_of_laplace P hX hY hX0 hY0 h)
    (epv_lintegral_le_of_laplace P hY hX hY0 hX0 fun c hc => (h c hc).symm)

/-!
## 3. Tonelli for parametrized marked statistics
-/

/-- **Tonelli** for `∫ dμ(i) E_𝖯 Σ_{x∈ξ} h_i(x)`. The family `h_i` is continuous in `i` and in `x`,
nonnegative, uniformly bounded and supported in `K × P(𝕋)` for one compact `K`. -/
theorem epv_lintegral_swap {ι : Type*} [TopologicalSpace ι] [TopologicalSpace.MetrizableSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι] (μ : Measure ι) [SFinite μ]
    (P : ProbabilityMeasure MarkedPointMeasure) (h : ι → MarkedSpectralSpace → ℝ)
    {K : Set ℝ} (hK : IsCompact K) (M : ℝ)
    (hcont : ∀ i, Continuous (h i)) (hcont' : ∀ x, Continuous fun i => h i x)
    (h0 : ∀ i x, 0 ≤ h i x) (hsupp : ∀ i x, x.1 ∉ K → h i x = 0) (hbd : ∀ i x, h i x ≤ M) :
    ∫⁻ i, ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (h i x) ∂ξ.marked.measure ∂(P : Measure MarkedPointMeasure)
        ∂μ =
      ∫⁻ ξ, ∫⁻ x, ∫⁻ i, ENNReal.ofReal (h i x) ∂μ ∂ξ.marked.measure
        ∂(P : Measure MarkedPointMeasure) := by
  have hcs : ∀ i, HasCompactSupport (h i) := fun i => epv_hasCompactSupport_of_fst hK (hsupp i)
  -- the marked statistics as real functions of `(i, ξ)`
  have hinner : ∀ i ξ, ∫⁻ x, ENNReal.ofReal (h i x) ∂ξ.marked.measure =
      ENNReal.ofReal (epv_markedIntegral (h i) ξ) := fun i ξ =>
    epv_lintegral_marked_eq (hcont i) (hcs i) (h0 i) ξ
  have hKm : MeasurableSet (K ×ˢ (univ : Set MassProfile)) :=
    hK.measurableSet.prod MeasurableSet.univ
  have hcontξ : ∀ ξ : MarkedPointMeasure, Continuous fun i => epv_markedIntegral (h i) ξ := by
    intro ξ
    refine continuous_of_dominated (bound := (K ×ˢ (univ : Set MassProfile)).indicator
      fun _ => M) (fun i => (hcont i).aestronglyMeasurable) (fun i => Eventually.of_forall
        fun x => ?_) ?_ (Eventually.of_forall hcont')
    · by_cases hx : x.1 ∈ K
      · rw [indicator_of_mem (mk_mem_prod hx (mem_univ _)), Real.norm_eq_abs,
          abs_of_nonneg (h0 i x)]
        exact hbd i x
      · rw [hsupp i x hx, indicator_of_notMem (fun h' => hx h'.1)]
        simp
    · refine (integrable_indicator_iff hKm).2 (integrableOn_const ?_)
      exact ((hK.prod isCompact_univ).measure_lt_top).ne
  have hmeas : Measurable (Function.uncurry fun i ξ => epv_markedIntegral (h i) ξ) :=
    measurable_uncurry_of_continuous_of_measurable hcontξ
      fun i => epv_measurable_markedIntegral (hcont i) (hcs i)
  simp_rw [hinner]
  rw [lintegral_lintegral_swap (f := fun i ξ => ENNReal.ofReal (epv_markedIntegral (h i) ξ))
    (ENNReal.measurable_ofReal.comp hmeas).aemeasurable]
  refine lintegral_congr fun ξ => ?_
  have hmeas' : Measurable (Function.uncurry fun i x => h i x) :=
    measurable_uncurry_of_continuous_of_measurable hcont' fun i => (hcont i).measurable
  simp_rw [← hinner]
  exact lintegral_lintegral_swap (f := fun i x => ENNReal.ofReal (h i x))
    (ENNReal.measurable_ofReal.comp hmeas').aemeasurable

end BlockBand.Endpoints
