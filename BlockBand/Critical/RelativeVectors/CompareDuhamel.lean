module

public import BlockBand.Critical.RelativeVectors.CompareSample
public import BlockBand.Critical.RelativeVectors.Window

/-!
# The conditional comparison from the Duhamel identity

`compare_of_duhamel`: for an `𝓛`-measurable set `B` of paths that a.s. have simple spectrum
and long gaps on `[a, c]`, the Duhamel identity (`RelativeDuhamelStatement`) applied to the
phase-averaged test `arrayTest ι (f ω)` gives
`|E[1_B ∫(f(z_ι) - ∫ f dγ) dθ]| ≤ (Tot + Cru η + Eq) P(B)`, from
* `Tot`: the integrated generator difference on `B ∩ 𝒜` (`goodSample_integral_le`),
* `Cru`: the crude integrated generator difference on `B` (`crudeSample_integral_le`),
* `Eq`: the equilibration at the start time (`equilSample_le`),
* `η`: the conditional failure `P(B ∩ 𝒜ᶜ) ≤ η P(B)` (`step1_goodPaths`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.MomentFlow

variable {N r k : ℕ}

/-- The backward function of a path-dependent array test (the `g` of `RelativeDuhamelStatement`). -/
def rmvBackward {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (c : ℝ)
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ) (ω : FlowSample N) (s : ℝ)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  ∫ ω', h ω (arrayMul (𝓜 ω s c ω') z + Ξ ω s c ω') ∂Paux

/-- The Duhamel integrand `(𝒜 - 𝓛_ref) g_s(z_s)`. -/
def rmvGenDiff (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ℓ : ℕ) (V : Matrix (Fin N) (Fin r) ℂ)
    (g : FlowSample N → ℝ → (Fin N → Fin r → ℂ) → ℝ) (ω : FlowSample N) (s : ℝ) : ℝ :=
  complexAngularGenerator N r (flowEigenvalue F a ω s) (g ω s)
      (frameArray V (flowMatrix F a ω s)) -
    referenceArrayGenerator F a b₀ ω ℓ s (g ω s) (frameArray V (flowMatrix F a ω s))

theorem measurable_frameArray_flow (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) :
    Measurable fun ω : FlowSample N => frameArray V (flowMatrix F a ω σ) := by
  have hv : ∀ i, Measurable fun ω : FlowSample N => freshEigenvector (flowMatrix F a ω σ) i :=
    fun i => measurable_pi_iff.mpr fun x =>
      (measurable_freshEigenvector i x).comp (measurable_flowMatrix F a σ)
  refine measurable_pi_iff.mpr fun i => ?_
  unfold frameArray
  have hc : Continuous fun v : Fin N → ℂ => ((Real.sqrt N : ℝ) : ℂ) • (Vᴴ *ᵥ v) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).const_smul
      (((Real.sqrt N : ℝ) : ℂ))
  exact hc.measurable.comp (hv i)

theorem pathProd_le {Y : Type*} [MeasurableSpace Y] (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) :
    MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Y) ≤
      (inferInstance : MeasurableSpace (FlowSample N × Y)) :=
  sup_le_sup_right (MeasurableSpace.comap_mono (pathSigma_le F a a c)) _

/-- **The conditional comparison from the Duhamel identity.** See the module docstring. -/
theorem compare_of_duhamel (hD : RelativeDuhamelStatement N r)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c b₀ : ℝ} {ℓ : ℕ}
    (ha : 0 < a) (hac : a < c) (hb₀ : 0 < b₀) (hℓ : 0 < ℓ)
    {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux) [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ)
    (hmeas : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (V : Matrix (Fin N) (Fin r) ℂ) (ι : Fin k → Fin N) (hι : Function.Injective ι)
    (f : FlowSample N → MarkArray k r → ℝ) (hf : IsPathMarkTest (pathSigma F a a c) f)
    {δ : ℝ} (hδ : 0 < δ) (B : Set (FlowSample N)) (hBm : MeasurableSet[pathSigma F a a c] B)
    (hB : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ) ∧
      ∀ i j : Fin N, ℓ ≤ labelDist i j →
        δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    (𝒜 : Set (FlowSample N)) (h𝒜 : MeasurableSet 𝒜) {Tot Cru Eqb η : ℝ}
    (hTot0 : 0 ≤ Tot) (hCru0 : 0 ≤ Cru)
    (hTot : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → ω ∈ 𝒜 → ∫ s in Ioc a c,
      |rmvGenDiff F a b₀ ℓ V (rmvBackward Paux 𝓜 Ξ c fun ω => arrayTest ι (f ω)) ω s| ≤ Tot)
    (hCru : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → ∫ s in Ioc a c,
      |rmvGenDiff F a b₀ ℓ V (rmvBackward Paux 𝓜 Ξ c fun ω => arrayTest ι (f ω)) ω s| ≤ Cru)
    (hEq : ∀ᵐ ω ∂flowLaw N a, ω ∈ B →
      |rmvBackward Paux 𝓜 Ξ c (fun ω => arrayTest ι (f ω)) ω a
          (frameArray V (flowMatrix F a ω a)) -
        ∫ z, arrayTest ι (f ω) z ∂gaussianMarkLaw N r| ≤ Eqb)
    (hη : (flowLaw N a).real (B ∩ 𝒜ᶜ) ≤ η * (flowLaw N a).real B) :
    |∫ ω in B, ∫ θ, (f ω (fun m => relativeMark V (flowMatrix F a ω c) θ (ι m)) -
        ∫ g, f ω g ∂gaussianMarkLaw k r) ∂phaseVectorLaw N ∂flowLaw N a| ≤
      (Tot + Cru * η + Eqb) * (flowLaw N a).real B := by
  classical
  set μ := flowLaw N a with hμ
  set h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ := fun ω => arrayTest ι (f ω) with hhdef
  set g := rmvBackward Paux 𝓜 Ξ c h with hgdef
  have hBm' : MeasurableSet B := pathSigma_le F a a c B hBm
  -- measurability
  have hhm𝓛 : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h) := by
    let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
    exact measurable_arrayTest_uncurry ι hf.measurable
  have hhm : Measurable (Function.uncurry h) := hhm𝓛.mono (pathProd_le F a c) le_rfl
  have hhb : ∀ ω z, |h ω z| ≤ 1 := fun ω z => (isArrayC2Bounded_arrayTest ι (hf.c2 ω)).bound z
  set X : FlowSample N → ℝ := fun ω => h ω (frameArray V (flowMatrix F a ω c)) with hX
  set W : FlowSample N → ℝ := fun ω => g ω a (frameArray V (flowMatrix F a ω a)) with hW
  set Y : FlowSample N → ℝ := fun ω => ∫ z, h ω z ∂gaussianMarkLaw N r with hY
  have hXm : Measurable X := hhm.comp (measurable_id.prodMk (measurable_frameArray_flow F a c V))
  have hYm : StronglyMeasurable Y := hhm.stronglyMeasurable.integral_prod_right'
  have hWm : StronglyMeasurable W := by
    have hM : Measurable fun p : FlowSample N × Ωaux => 𝓜 p.1 a c p.2 :=
      (hmeas a c).1.mono (pathProd_le F a c) le_rfl
    have hΞ : Measurable fun p : FlowSample N × Ωaux => Ξ p.1 a c p.2 :=
      (hmeas a c).2.mono (pathProd_le F a c) le_rfl
    have hZ : Measurable fun p : FlowSample N × Ωaux => frameArray V (flowMatrix F a p.1 a) :=
      (measurable_frameArray_flow F a a V).comp measurable_fst
    have hΦ : Measurable fun p : FlowSample N × Ωaux =>
        h p.1 (arrayMul (𝓜 p.1 a c p.2) (frameArray V (flowMatrix F a p.1 a)) + Ξ p.1 a c p.2) :=
      hhm.comp (measurable_fst.prodMk ((measurable_arrayMul_comp hM hZ).add hΞ))
    exact hΦ.stronglyMeasurable.integral_prod_right'
  have hXb : ∀ ω, |X ω| ≤ 1 := fun ω => hhb _ _
  have hYb : ∀ ω, |Y ω| ≤ 1 := by
    intro ω
    calc |Y ω| ≤ ∫ z, |h ω z| ∂gaussianMarkLaw N r := abs_integral_le_integral_abs
      _ ≤ ∫ _z, (1 : ℝ) ∂gaussianMarkLaw N r :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun z => hhb ω z)
      _ = 1 := by simp
  have hWb : ∀ ω, |W ω| ≤ 1 := by
    intro ω
    calc |W ω| ≤ ∫ ω', |h ω (arrayMul (𝓜 ω a c ω') (frameArray V (flowMatrix F a ω a)) +
          Ξ ω a c ω')| ∂Paux := abs_integral_le_integral_abs
      _ ≤ ∫ _ω', (1 : ℝ) ∂Paux :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun _ => hhb ω _)
      _ = 1 := by simp
  have hint : ∀ {Φ : FlowSample N → ℝ}, AEStronglyMeasurable Φ μ → (∀ ω, |Φ ω| ≤ 1) →
      IntegrableOn Φ B μ := fun hm hb =>
    (Integrable.of_bound hm 1 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hb ω)).integrableOn
  have hXi : IntegrableOn X B μ := hint hXm.aestronglyMeasurable hXb
  have hWi : IntegrableOn W B μ := hint hWm.aestronglyMeasurable hWb
  have hYi : IntegrableOn Y B μ := hint hYm.aestronglyMeasurable hYb
  -- the inner (phase) integral
  have hinner : ∀ ω, ∫ θ, (f ω (fun m => relativeMark V (flowMatrix F a ω c) θ (ι m)) -
      ∫ g, f ω g ∂gaussianMarkLaw k r) ∂phaseVectorLaw N = X ω - Y ω := by
    intro ω
    have hc : Continuous (f ω) := (hf.c2 ω).contDiff.continuous
    have hmk : Continuous fun θ : Fin N → ℂ =>
        (fun m => relativeMark V (flowMatrix F a ω c) θ (ι m)) := by
      refine continuous_pi fun m => ?_
      simp only [relativeMark]
      fun_prop
    have hi : Integrable (fun θ => f ω (fun m => relativeMark V (flowMatrix F a ω c) θ (ι m)))
        (phaseVectorLaw N) := by
      exact Integrable.of_bound (hc.comp hmk).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun θ => by
          rw [Real.norm_eq_abs]; exact (hf.c2 ω).bound _)
    rw [integral_sub hi (integrable_const _), integral_relativeMark_eq, integral_const]
    simp only [probReal_univ, one_smul]
    rw [← integral_arrayTest_gaussian ι hι hc ⟨1, (hf.c2 ω).bound⟩]
  rw [setIntegral_congr_fun hBm' (fun ω _ => hinner ω)]
  -- the splitting
  have hsplit : ∫ ω in B, (X ω - Y ω) ∂μ =
      ∫ ω in B, (X ω - W ω) ∂μ + ∫ ω in B, (W ω - Y ω) ∂μ := by
    have := integral_add (hXi.sub hWi) (hWi.sub hYi)
    simp only [Pi.sub_apply] at this
    rw [← this]
    congr 1; funext ω; ring
  -- the Duhamel identity
  have hDu := hD F a c b₀ ℓ hF ha hac hb₀ hℓ Ωaux Paux 𝓜 Ξ hmeas hRF V 1 h hhm𝓛
    (fun ω => ⟨isArrayC2Bounded_arrayTest ι (hf.c2 ω), isLabelPhaseInvariant_arrayTest ι⟩)
    δ hδ B hBm hB
  have hXW : ∫ ω in B, (X ω - W ω) ∂μ = ∫ ω in B, (∫ s in Ioc a c,
      rmvGenDiff F a b₀ ℓ V g ω s) ∂μ := hDu
  -- first term
  have hfirst : |∫ ω in B, (X ω - W ω) ∂μ| ≤ Tot * μ.real B + Cru * (η * μ.real B) := by
    rw [hXW]
    have hpt : ∀ᵐ ω ∂μ.restrict B, |∫ s in Ioc a c, rmvGenDiff F a b₀ ℓ V g ω s| ≤
        Tot + Cru * (𝒜ᶜ.indicator 1 ω) := by
      rw [ae_restrict_iff' hBm']
      filter_upwards [hTot, hCru] with ω h1 h2 hωB
      have habs := abs_integral_le_integral_abs (f := fun s => rmvGenDiff F a b₀ ℓ V g ω s)
        (μ := volume.restrict (Ioc a c))
      by_cases hω𝒜 : ω ∈ 𝒜
      · have : (𝒜ᶜ.indicator 1 ω : ℝ) = 0 := by simp [hω𝒜]
        rw [this, mul_zero, add_zero]
        exact habs.trans (h1 hωB hω𝒜)
      · have : (𝒜ᶜ.indicator 1 ω : ℝ) = 1 := by simp [hω𝒜]
        rw [this, mul_one]
        linarith [habs.trans (h2 hωB)]
    have hbi : Integrable (fun ω => Tot + Cru * (𝒜ᶜ.indicator 1 ω : ℝ)) (μ.restrict B) :=
      (integrable_const _).add (((integrable_const (1 : ℝ)).indicator h𝒜.compl).const_mul Cru)
    calc |∫ ω in B, (∫ s in Ioc a c, rmvGenDiff F a b₀ ℓ V g ω s) ∂μ|
        ≤ ∫ ω in B, |∫ s in Ioc a c, rmvGenDiff F a b₀ ℓ V g ω s| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω in B, (Tot + Cru * (𝒜ᶜ.indicator 1 ω : ℝ)) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbi hpt
      _ = Tot * μ.real B + Cru * μ.real (B ∩ 𝒜ᶜ) := by
          have hind : Integrable (𝒜ᶜ.indicator (1 : FlowSample N → ℝ)) (μ.restrict B) :=
            (integrable_const (1 : ℝ)).indicator h𝒜.compl
          have e1 : ∫ ω in B, (Tot + Cru * (𝒜ᶜ.indicator 1 ω : ℝ)) ∂μ =
              ∫ _ω in B, Tot ∂μ + ∫ ω in B, Cru * (𝒜ᶜ.indicator 1 ω : ℝ) ∂μ :=
            integral_add (integrable_const _) (hind.const_mul Cru)
          rw [e1, integral_const_mul, integral_indicator_one h𝒜.compl, setIntegral_const,
            measureReal_restrict_apply h𝒜.compl, Set.inter_comm]
          simp [mul_comm]
      _ ≤ Tot * μ.real B + Cru * (η * μ.real B) := by gcongr
  -- second term
  have hsecond : |∫ ω in B, (W ω - Y ω) ∂μ| ≤ Eqb * μ.real B := by
    have hpt : ∀ᵐ ω ∂μ.restrict B, |W ω - Y ω| ≤ Eqb := by
      rw [ae_restrict_iff' hBm']
      filter_upwards [hEq] with ω h1 hωB using h1 hωB
    calc |∫ ω in B, (W ω - Y ω) ∂μ| ≤ ∫ ω in B, |W ω - Y ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ω in B, Eqb ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) hpt
      _ = Eqb * μ.real B := by rw [setIntegral_const]; simp [mul_comm]
  rw [hsplit]
  calc |∫ ω in B, (X ω - W ω) ∂μ + ∫ ω in B, (W ω - Y ω) ∂μ|
      ≤ |∫ ω in B, (X ω - W ω) ∂μ| + |∫ ω in B, (W ω - Y ω) ∂μ| := abs_add_le _ _
    _ ≤ _ := by nlinarith

end BlockBand.Critical.RelativeVectors
