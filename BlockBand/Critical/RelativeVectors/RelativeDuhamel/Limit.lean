module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.Test

/-!
# The angular martingale identity and the limit `n → ∞`

Data as in `relativeDuhamel_identity`; `T = c - a`, `g = backwardFn Paux 𝓜 Ξ c h`,
`Z_σ = frameArray V H_σ`, `H_σ = flowMatrix F a ω σ`, and `D(ω, σ) = (𝒜_σ - 𝓛_ref(σ)) g_σ(Z_σ)`
(`genDiffIntegrand`).

* `m3Process_eq`, `m3Process_terminal`: on a path with `hermProj ω = ω` in the switch set, the
  angular martingale bracket at time `v ≤ T` is `g_{a+v}(Z_{a+v}) - g_a(Z_a) - ∫_0^v D(a + x) dx`;
  at `v = T` it is `h(Z_c) - g_a(Z_a) - ∫_a^c D(σ) dσ` (`g_c = h`, time change `σ = a + x`).
* `abs_m3Process_le`: on such a path, if moreover the long gaps are `≥ δ` on `[a, c]`, the
  bracket at every `v ≤ T` is bounded by `2C + T · genDiffConst · (1 + frameBound V ²)`,
  uniformly in `v` and `ω` (the short rotations cancel in `𝒜 - 𝓛_ref`, `abs_generator_diff_le`).
* `eventually_lt_gapStop`: on such a path, `T < σ_{n+1}` for all large `n` (uniform gap on
  `[a, c]` from `simpleRatSet`, `Angular.lt_gapStop_of_gap`).
* `relativeDuhamel_identity`: the identity of `RelativeDuhamelStatement` for given data with
  `ℓ ≥ 1`, by dominated convergence `n → ∞` with `Λ = 1_B ∘ hermProj`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel

open MeasureTheory Set Filter Topology ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Critical.RelativeVectors
open BlockBand.Palm.MomentFlow
open scoped NNReal

attribute [local instance] Classical.propDecidable

variable {N r : ℕ}

/-!
## The angular martingale bracket
-/

/-- The bracket of the angular martingale (the process inside `stoppedProcess` in
`ComplexAngularMartingaleStatement`): `h(v, Z_v) - h(0, Z_0) - ∫_0^v (h_t + 𝒜_x h)(x, Z_x) dx`
along `F' + G_{s+·}`. -/
def m3Process {Ω : Type*} (F' : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin r) ℂ)
    (h ht : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ) (s : ℝ≥0) (v : ℝ≥0) (ω : Ω) : ℝ :=
  h ω (v : ℝ) (frameArray V (F' ω + G (s + v) ω)) - h ω 0 (frameArray V (F' ω + G s ω)) -
    ∫ x in Ioc (0 : ℝ) (v : ℝ),
      (ht ω x (frameArray V (F' ω + G (s + x.toNNReal) ω)) +
        complexAngularGenerator N r (fun i => freshEigenvalue (F' ω + G (s + x.toNNReal) ω) i)
          (h ω x) (frameArray V (F' ω + G (s + x.toNNReal) ω)))

section Data

variable {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
  (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
  (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (F : Matrix (Fin N) (Fin N) ℂ)
  (a c b₀ : ℝ) (ℓ : ℕ) (V : Matrix (Fin N) (Fin r) ℂ)
  (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)

/-- The concrete angular martingale bracket, stopped at `T ∧ σ_n` (`T = (c - a).toNNReal`). -/
def stoppedBracket (n : ℕ) (ω : FlowSample N) : ℝ :=
  stoppedProcess (m3Process (flowInit F) (flowBM N) V (switchTest Paux 𝓜 Ξ F a c h)
      (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h) 0)
    (gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n) (Real.toNNReal (c - a)) ω

/-- The integrand `(𝒜_σ - 𝓛_ref(σ)) g_σ(Z_σ)` of `RelativeDuhamelStatement`. -/
def genDiffIntegrand (ω : FlowSample N) (σ : ℝ) : ℝ :=
  complexAngularGenerator N r (flowEigenvalue F a ω σ) (backwardFn Paux 𝓜 Ξ c h ω σ)
      (frameArray V (flowMatrix F a ω σ)) -
    referenceArrayGenerator F a b₀ ω ℓ σ (backwardFn Paux 𝓜 Ξ c h ω σ)
      (frameArray V (flowMatrix F a ω σ))

/-- **The angular martingale identity for the switched test** (from `ComplexAngularContract` via
`complexAngularMartingale_any_start` at start time `0`, horizon `(c - a).toNNReal`): for every
bounded multiplier measurable for the eigenvalue-path σ-algebra, `Λ · stoppedBracket` is
integrable with mean zero. -/
theorem m3_identity (hAng : BlockBand.Internal.Contracts.TransmissionAngular.ComplexAngularContract)
    [IsProbabilityMeasure Paux] (hF : F.IsHermitian) (hac : a ≤ c)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    {C : ℝ}
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω)) {n : ℕ} (hn : 0 < n)
    (Λ : FlowSample N → ℝ) (hΛ : Measurable[eigenPathSigma (flowInit F) (flowBM N) 0] Λ)
    (hΛb : ∃ C, ∀ ω, |Λ ω| ≤ C) :
    Integrable (fun ω => Λ ω * stoppedBracket Paux 𝓜 Ξ F a c b₀ ℓ V h n ω) (flowLaw N a) ∧
      ∫ ω, Λ ω * stoppedBracket Paux 𝓜 Ξ F a c b₀ ℓ V h n ω ∂flowLaw N a = 0 :=
  Angular.complexAngularMartingale_any_start hAng N r (FlowSample N) (flowLaw N a)
    (BlockBand.Palm.MomentFlow.flowFiltration N) (flowBM N) (flowInit F)
    (isHermitianBrownian_flowBM a) (measurable_flowInit F) (flowInit_isHermitian hF) 0 V n hn
    (Real.toNNReal (c - a)) (switchTest Paux 𝓜 Ξ F a c h) (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h)
    (isSpaceTimeAngularTest_switchTest Paux 𝓜 Ξ b₀ ℓ h hF hac hMΞ hRF hh hC hn) _ le_rfl Λ hΛ hΛb

/-!
## The bracket along a good path
-/

/-- **The bracket along a path in the switch set** (`hermProj ω = ω`, `ω ∈ simpleRatSet`): for
`v ≤ c - a`, it is `g_{a+v}(Z_{a+v}) - g_a(Z_a) - ∫_0^v D(ω, a + x) dx`. -/
theorem m3Process_eq (hac : a ≤ c) {ω : FlowSample N} (hω : hermProj ω = ω)
    (hS : ω ∈ simpleRatSet F a c) (v : ℝ≥0) (hv : (v : ℝ) ≤ c - a) :
    m3Process (flowInit F) (flowBM N) V (switchTest Paux 𝓜 Ξ F a c h)
        (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h) 0 v ω =
      backwardFn Paux 𝓜 Ξ c h ω (a + v) (frameArray V (flowMatrix F a ω (a + v))) -
        backwardFn Paux 𝓜 Ξ c h ω a (frameArray V (flowMatrix F a ω a)) -
        ∫ x in Ioc (0 : ℝ) (v : ℝ), genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω (a + x) := by
  have hS' : hermProj ω ∈ simpleRatSet F a c := by rw [hω]; exact hS
  unfold m3Process
  rw [setIntegral_congr_fun measurableSet_Ioc
    (g := fun x => genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω (a + x)) ?_]
  · rw [switchTest_of_mem Paux 𝓜 Ξ F a c h hS', switchTest_of_mem Paux 𝓜 Ξ F a c h hS', zero_add,
      flowInit_add_flowBM F a ω, flowInit_add_flowBM F a ω 0, hω, clampTime_eq (NNReal.coe_nonneg v) hv,
      clampTime_eq le_rfl (sub_nonneg.2 hac), NNReal.coe_zero, add_zero]
  · intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have hxT : x ≤ c - a := hx.2.trans hv
    simp only [switchTest_of_mem Paux 𝓜 Ξ F a c h hS',
      switchTestDeriv_of_mem Paux 𝓜 Ξ F a c b₀ ℓ h hS', zero_add, flowInit_add_flowBM F a ω, hω,
      Real.coe_toNNReal x hx0, clampTime_eq hx0 hxT, genDiffIntegrand]
    rw [neg_add_eq_sub]
    rfl

/-- **The bracket at the horizon.** On a path in the switch set carrying a reference flow, the
bracket at `T = c - a` is `h(Z_c) - g_a(Z_a) - ∫_{(a, c]} D(ω, σ) dσ`. -/
theorem m3Process_terminal [IsProbabilityMeasure Paux] (hac : a ≤ c) {ω : FlowSample N}
    (hω : hermProj ω = ω) (hS : ω ∈ simpleRatSet F a c)
    (hRFω : IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω)) :
    m3Process (flowInit F) (flowBM N) V (switchTest Paux 𝓜 Ξ F a c h)
        (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h) 0 (Real.toNNReal (c - a)) ω =
      h ω (frameArray V (flowMatrix F a ω c)) -
        backwardFn Paux 𝓜 Ξ c h ω a (frameArray V (flowMatrix F a ω a)) -
        ∫ σ in Ioc a c, genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω σ := by
  have hT : ((Real.toNNReal (c - a) : ℝ≥0) : ℝ) = c - a := Real.coe_toNNReal _ (sub_nonneg.2 hac)
  rw [m3Process_eq Paux 𝓜 Ξ F a c b₀ ℓ V h hac hω hS _ hT.le, hT, add_sub_cancel,
    backwardFn_terminal Paux 𝓜 Ξ h ω hRFω]
  congr 1
  rw [← intervalIntegral.integral_of_le (sub_nonneg.2 hac),
    intervalIntegral.integral_comp_add_left (genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω) a,
    add_zero, add_sub_cancel, intervalIntegral.integral_of_le hac]

/-- The constant of the generator-difference bound is nonnegative. -/
theorem genDiffConst_nonneg {C : ℝ} (hC : 0 ≤ C) (δ : ℝ) :
    0 ≤ genDiffConst N r C δ b₀ ℓ := by
  have hM := supC2Const_nonneg (N := N) (r := r) hC
  unfold genDiffConst
  positivity

/-- The uniform bound `2C + T · genDiffConst · (1 + frameBound V ²)` of the bracket. -/
def bracketBound (C δ : ℝ) : ℝ :=
  2 * C + (c - a) * (genDiffConst N r C δ b₀ ℓ * (1 + Angular.frameBound V ^ 2))

/-- The bracket bound is nonnegative. -/
theorem bracketBound_nonneg (hac : a ≤ c) {C : ℝ} (hC : 0 ≤ C) (δ : ℝ) :
    0 ≤ bracketBound a c b₀ ℓ V C δ := by
  have := genDiffConst_nonneg b₀ ℓ (N := N) (r := r) hC δ
  have hca : 0 ≤ c - a := sub_nonneg.2 hac
  unfold bracketBound
  positivity

/-- **Pointwise bound on the integrand.** If `ω` carries a reference flow and its long gaps are
`≥ δ` on `[a, c]`, then `|D(ω, σ)| ≤ genDiffConst · (1 + frameBound V ²)` on `[a, c]`. -/
theorem abs_genDiffIntegrand_le (hℓ : 1 ≤ ℓ) {C δ : ℝ} (hδ : 0 < δ) {ω : FlowSample N}
    (hRFω : IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω)) (hCω : IsArrayC2Bounded C (h ω))
    (hlong : ∀ σ ∈ Icc a c, ∀ i j : Fin N, ℓ ≤ labelDist i j →
      δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    {σ : ℝ} (hσ : σ ∈ Icc a c) :
    |genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω σ| ≤
      genDiffConst N r C δ b₀ ℓ * (1 + Angular.frameBound V ^ 2) := by
  have hg := (refFlow_backward hRFω hCω).1 σ hσ
  refine (abs_generator_diff_le hg F a b₀ ω hℓ σ hδ (hlong σ hσ) _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (genDiffConst_nonneg b₀ ℓ (arrayC2_nonneg hCω) δ)
  have hZ := Angular.norm_frameArray_le V (flowMatrix F a ω σ)
  have hZ0 := norm_nonneg (frameArray V (flowMatrix F a ω σ))
  gcongr

/-- **Uniform bound on the bracket.** On a path in the switch set carrying a reference flow,
with long gaps `≥ δ` on `[a, c]`, the bracket at every `v ≤ c - a` is bounded by
`bracketBound`. -/
theorem abs_m3Process_le (hac : a ≤ c) (hℓ : 1 ≤ ℓ) {C δ : ℝ} (hδ : 0 < δ) {ω : FlowSample N}
    (hω : hermProj ω = ω) (hS : ω ∈ simpleRatSet F a c)
    (hRFω : IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω)) (hCω : IsArrayC2Bounded C (h ω))
    (hlong : ∀ σ ∈ Icc a c, ∀ i j : Fin N, ℓ ≤ labelDist i j →
      δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    (v : ℝ≥0) (hv : (v : ℝ) ≤ c - a) :
    |m3Process (flowInit F) (flowBM N) V (switchTest Paux 𝓜 Ξ F a c h)
        (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h) 0 v ω| ≤ bracketBound a c b₀ ℓ V C δ := by
  rw [m3Process_eq Paux 𝓜 Ξ F a c b₀ ℓ V h hac hω hS v hv]
  set K := genDiffConst N r C δ b₀ ℓ * (1 + Angular.frameBound V ^ 2) with hKdef
  have hC0 := arrayC2_nonneg hCω
  have hK0 : 0 ≤ K := mul_nonneg (genDiffConst_nonneg b₀ ℓ hC0 δ) (by positivity)
  have hg := (refFlow_backward hRFω hCω).1
  have hv0 : (0 : ℝ) ≤ v := NNReal.coe_nonneg v
  have h1 := arrayC2_abs_le (hg (a + v) ⟨by linarith, by linarith⟩)
    (frameArray V (flowMatrix F a ω (a + v)))
  have h2 := arrayC2_abs_le (hg a ⟨le_rfl, hac⟩) (frameArray V (flowMatrix F a ω a))
  have hI : |∫ x in Ioc (0 : ℝ) (v : ℝ), genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω (a + x)| ≤
      K * v := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) v) (C := K)
      (by simp [Real.volume_Ioc])
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact abs_genDiffIntegrand_le Paux 𝓜 Ξ F a c b₀ ℓ V h hℓ hδ hRFω hCω hlong
          (σ := a + x) ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    rwa [Real.volume_real_Ioc_of_le hv0, sub_zero, Real.norm_eq_abs] at this
  have hKv : K * v ≤ (c - a) * K := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hv hK0
  unfold bracketBound
  rw [← hKdef]
  calc _ ≤ |backwardFn Paux 𝓜 Ξ c h ω (a + v) (frameArray V (flowMatrix F a ω (a + v))) -
          backwardFn Paux 𝓜 Ξ c h ω a (frameArray V (flowMatrix F a ω a))| +
        |∫ x in Ioc (0 : ℝ) (v : ℝ), genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω (a + x)| :=
        abs_sub _ _
    _ ≤ (C + C) + K * v := add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) hI
    _ ≤ 2 * C + (c - a) * K := by linarith

/-- **Eventually no gap stop before the horizon.** On a path with `hermProj ω = ω` in the switch
set, `(c - a) < σ_{n+1}` for all large `n`. -/
theorem eventually_lt_gapStop {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a ≤ c) {ω : FlowSample N} (hω : hermProj ω = ω) (hS : ω ∈ simpleRatSet F a c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ((Real.toNNReal (c - a) : ℝ≥0) : WithTop ℝ≥0) <
      gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 (n + 1) ω := by
  have hherm : ω.1.IsHermitian := by
    have e : (hermProj ω).1 = ω.1 := by rw [hω]
    rw [← e]
    exact hermPart_isHermitian ω.1
  obtain ⟨m, hm⟩ := hS
  have hcont := fun k => continuous_flowEigenvalue hF a hherm k
  have hunif : ∀ σ ∈ Icc a c, ∀ i j : Fin N, i ≠ j →
      1 / ((m : ℝ) + 1) ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| := by
    intro σ hσ i j hij
    exact ge_on_Icc_of_rat_Icc (((hcont i).sub (hcont j)).abs) hac (hm a (by simp) i j hij)
      (fun q hq => hm q (Or.inr ⟨hq, q, rfl⟩) i j hij) σ hσ
  refine ⟨m + 1, fun n hn => ?_⟩
  have hHc : ∀ ω' : FlowSample N, Continuous fun t => flowInit F ω' + flowBM N t ω' :=
    fun ω' => continuous_const.add ((isHermitianBrownian_flowBM (N := N) a).continuous ω')
  refine Angular.lt_gapStop_of_gap hHc 0 (n + 1) ω _ fun v hv i j hij => ?_
  have hvT : (v : ℝ) ≤ c - a := by
    have := NNReal.coe_le_coe.2 hv
    rwa [Real.coe_toNNReal _ (sub_nonneg.2 hac)] at this
  have hH : (flowMatrix F a ω (a + v)).IsHermitian := flowMatrix_isHermitian_of hF a hherm _
  simp only [Angular.gapFun_coe, zero_add]
  rw [flowInit_add_flowBM F a ω, hω]
  have e : ∀ k : Fin N,
      dysonEigenvalue N (flowMatrix F a ω (a + v)) k = flowEigenvalue F a ω (a + v) k.rev :=
    fun k => by
      simp only [flowEigenvalue]
      rw [freshEigenvalue_eq_dyson hH, Fin.rev_rev]
  rw [e, e]
  have hlt : 1 / ((n + 1 : ℕ) : ℝ) < 1 / ((m : ℝ) + 1) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  exact hlt.trans_le (hunif (a + v) ⟨by linarith [NNReal.coe_nonneg v], by linarith⟩ _ _
    (fun e' => hij (Fin.rev_injective e')))

/-- The stopped bracket is the bracket at some time `v ≤ c - a`. -/
theorem stoppedBracket_eq_m3Process (hac : a ≤ c) (n : ℕ) (ω : FlowSample N) :
    ∃ v : ℝ≥0, (v : ℝ) ≤ c - a ∧ stoppedBracket Paux 𝓜 Ξ F a c b₀ ℓ V h n ω =
      m3Process (flowInit F) (flowBM N) V (switchTest Paux 𝓜 Ξ F a c h)
        (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h) 0 v ω := by
  refine ⟨(min ((Real.toNNReal (c - a) : ℝ≥0) : WithTop ℝ≥0)
    (gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n ω)).untopA, ?_, rfl⟩
  have := Angular.stopTime_le (gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n)
    (Real.toNNReal (c - a)) ω
  unfold Angular.stopTime at this
  rwa [Real.coe_toNNReal _ (sub_nonneg.2 hac)] at this

/-- Before the gap stop the stopped bracket is the bracket at the horizon. -/
theorem stoppedBracket_eq_terminal {n : ℕ} {ω : FlowSample N}
    (hlt : ((Real.toNNReal (c - a) : ℝ≥0) : WithTop ℝ≥0) <
      gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n ω) :
    stoppedBracket Paux 𝓜 Ξ F a c b₀ ℓ V h n ω =
      m3Process (flowInit F) (flowBM N) V (switchTest Paux 𝓜 Ξ F a c h)
        (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h) 0 (Real.toNNReal (c - a)) ω := by
  have e : (min ((Real.toNNReal (c - a) : ℝ≥0) : WithTop ℝ≥0)
      (gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n ω)).untopA =
      Real.toNNReal (c - a) := by
    rw [min_eq_left hlt.le]
    exact WithTop.untopD_coe _ _
  unfold stoppedBracket stoppedProcess
  rw [e]

end Data

/-!
## The limit `n → ∞`
-/

/-- Joint measurability of the backward function `(ω, z) ↦ g_s^ω(z)` (for the ambient product
σ-algebra). -/
theorem measurable_backwardFn_uncurry {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (F : Matrix (Fin N) (Fin N) ℂ)
    (a c : ℝ)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)
    (hh' : Measurable (Function.uncurry h)) (s : ℝ) :
    Measurable fun p : FlowSample N × (Fin N → Fin r → ℂ) => backwardFn Paux 𝓜 Ξ c h p.1 s p.2 := by
  have hle := pathSigma_le F a a c
  have hM' : Measurable fun p : FlowSample N × Ωaux => 𝓜 p.1 s c p.2 :=
    (hMΞ s c).1.mono (sup_le_sup_right (MeasurableSpace.comap_mono hle) _) le_rfl
  have hΞ' : Measurable fun p : FlowSample N × Ωaux => Ξ p.1 s c p.2 :=
    (hMΞ s c).2.mono (sup_le_sup_right (MeasurableSpace.comap_mono hle) _) le_rfl
  have harr : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      arrayMul p.1 p.2 := by
    refine continuous_pi fun i => continuous_pi fun q => ?_
    simp only [arrayMul]
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply_apply i j).comp continuous_fst).mul
        ((continuous_apply_apply j q).comp continuous_snd)
  have hq : Measurable fun q : (FlowSample N × (Fin N → Fin r → ℂ)) × Ωaux => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hf : Measurable fun q : (FlowSample N × (Fin N → Fin r → ℂ)) × Ωaux =>
      h q.1.1 (arrayMul (𝓜 q.1.1 s c q.2) q.1.2 + Ξ q.1.1 s c q.2) :=
    hh'.comp ((measurable_fst.comp measurable_fst).prodMk
      ((harr.measurable.comp ((hM'.comp hq).prodMk (measurable_snd.comp measurable_fst))).add
        (hΞ'.comp hq)))
  exact measurable_integral_prod Paux hf

/-- **The relative Duhamel identity for given data**: under the hypotheses of
`RelativeDuhamelStatement` (with `ℓ ≥ 1`), `E[1_B (h(Z_c) - g_a(Z_a))] =
E[1_B ∫_{(a, c]} (𝒜_σ - 𝓛_ref(σ)) g_σ(Z_σ) dσ]` under `flowLaw N a`. -/
theorem relativeDuhamel_identity
    (hAng : BlockBand.Internal.Contracts.TransmissionAngular.ComplexAngularContract)
    (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (hF : F.IsHermitian) (hac : a < c)
    (hℓ : 1 ≤ ℓ) {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (V : Matrix (Fin N) (Fin r) ℂ) (C : ℝ) (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω))
    (δ : ℝ) (hδ : 0 < δ) (B : Set (FlowSample N)) (hB : MeasurableSet[pathSigma F a a c] B)
    (hBae : ∀ᵐ ω ∂flowLaw N a, ω ∈ B → ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ) ∧
      ∀ i j : Fin N, ℓ ≤ labelDist i j →
        δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) :
    ∫ ω in B, (h ω (frameArray V (flowMatrix F a ω c)) -
        backwardFn Paux 𝓜 Ξ c h ω a (frameArray V (flowMatrix F a ω a))) ∂flowLaw N a =
      ∫ ω in B, (∫ s in Ioc a c, genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω s) ∂flowLaw N a := by
  have hac' := hac.le
  have hBm : MeasurableSet B := pathSigma_le F a a c B hB
  have hC0 : 0 ≤ C := (abs_nonneg _).trans ((hC 0).1.bound 0)
  have hK0 := bracketBound_nonneg a c b₀ ℓ V hac' hC0 δ
  -- the multiplier `Λ = 1_B ∘ hermProj`
  set Λ : FlowSample N → ℝ := (B.indicator fun _ => (1 : ℝ)) ∘ hermProj with hΛdef
  have hΛ : Measurable[eigenPathSigma (flowInit F) (flowBM N) 0] Λ := by
    have := (Angular.multiplier_of_pathSigma F (le_refl a) c
      (Λ₀ := B.indicator fun _ => (1 : ℝ))
      (@Measurable.indicator _ _ _ _ (pathSigma F a a c) _ _ measurable_const hB)).1
    rwa [sub_self, Real.toNNReal_zero] at this
  have hΛb : ∃ C', ∀ ω, |Λ ω| ≤ C' := ⟨1, fun ω => by
    simp only [hΛdef, Function.comp_apply, Set.indicator]
    split_ifs <;> simp⟩
  have hM := fun n : ℕ => m3_identity Paux 𝓜 Ξ F a c b₀ ℓ V h hAng hF hac' hMΞ hRF hh hC
    (Nat.succ_pos n) Λ hΛ hΛb
  -- the good set
  have hgood : ∀ᵐ ω ∂flowLaw N a, hermProj ω = ω ∧ (ω ∈ B →
      (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) ∧ ∀ σ ∈ Icc a c, ∀ i j : Fin N,
        ℓ ≤ labelDist i j → δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) := by
    filter_upwards [hermProj_ae_eq (N := N) a, hBae] with ω h1 h2
    exact ⟨h1, fun hωB => ⟨fun σ hσ => (h2 hωB σ hσ).1, fun σ hσ => (h2 hωB σ hσ).2⟩⟩
  have hherm : ∀ ω : FlowSample N, hermProj ω = ω → ω.1.IsHermitian := fun ω hω => by
    have e : (hermProj ω).1 = ω.1 := by rw [hω]
    rw [← e]
    exact hermPart_isHermitian ω.1
  have hΛ1 : ∀ ω, hermProj ω = ω → ω ∈ B → Λ ω = 1 := fun ω hω hωB => by
    simp [hΛdef, hω, hωB]
  have hΛ0 : ∀ ω, hermProj ω = ω → ω ∉ B → Λ ω = 0 := fun ω hω hωB => by
    simp [hΛdef, hω, hωB]
  -- the limit variable
  set X : FlowSample N → ℝ := fun ω => h ω (frameArray V (flowMatrix F a ω c)) -
    backwardFn Paux 𝓜 Ξ c h ω a (frameArray V (flowMatrix F a ω a)) with hXdef
  set I : FlowSample N → ℝ :=
    fun ω => ∫ s in Ioc a c, genDiffIntegrand Paux 𝓜 Ξ F a c b₀ ℓ V h ω s with hIdef
  set Φ : FlowSample N → ℝ := fun ω => X ω - I ω with hΦdef
  have hlim : ∀ᵐ ω ∂flowLaw N a, Tendsto
      (fun n : ℕ => Λ ω * stoppedBracket Paux 𝓜 Ξ F a c b₀ ℓ V h (n + 1) ω) atTop
      (𝓝 (B.indicator Φ ω)) := by
    filter_upwards [hgood] with ω ⟨hω, hgB⟩
    by_cases hωB : ω ∈ B
    · obtain ⟨hmono, -⟩ := hgB hωB
      have hS := (mem_simpleRatSet_iff hF hac' (hherm ω hω)).2 hmono
      obtain ⟨n₀, hn₀⟩ := eventually_lt_gapStop hF hac' hω hS
      rw [Set.indicator_of_mem hωB]
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
      beta_reduce
      rw [hΛ1 ω hω hωB, one_mul,
        stoppedBracket_eq_terminal Paux 𝓜 Ξ F a c b₀ ℓ V h (hn₀ n hn),
        m3Process_terminal Paux 𝓜 Ξ F a c b₀ ℓ V h hac' hω hS (hRF ω hmono)]
    · rw [Set.indicator_of_notMem hωB]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      beta_reduce
      rw [hΛ0 ω hω hωB, zero_mul]
  have hbound : ∀ n : ℕ, ∀ᵐ ω ∂flowLaw N a,
      ‖Λ ω * stoppedBracket Paux 𝓜 Ξ F a c b₀ ℓ V h (n + 1) ω‖ ≤ bracketBound a c b₀ ℓ V C δ := by
    intro n
    filter_upwards [hgood] with ω ⟨hω, hgB⟩
    rw [Real.norm_eq_abs]
    by_cases hωB : ω ∈ B
    · obtain ⟨hmono, hlong⟩ := hgB hωB
      have hS := (mem_simpleRatSet_iff hF hac' (hherm ω hω)).2 hmono
      obtain ⟨v, hv, hve⟩ := stoppedBracket_eq_m3Process Paux 𝓜 Ξ F a c b₀ ℓ V h hac' (n + 1) ω
      rw [hΛ1 ω hω hωB, one_mul, hve]
      exact abs_m3Process_le Paux 𝓜 Ξ F a c b₀ ℓ V h hac' hℓ hδ hω hS (hRF ω hmono) (hC ω).1
        hlong v hv
    · rw [hΛ0 ω hω hωB, zero_mul, abs_zero]
      exact hK0
  -- dominated convergence
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => bracketBound a c b₀ ℓ V C δ)
    (fun n => (hM n).1.aestronglyMeasurable) (integrable_const _) hbound hlim
  have hzero : ∫ ω, B.indicator Φ ω ∂flowLaw N a = 0 := by
    have e : (fun n : ℕ => ∫ ω, Λ ω * stoppedBracket Paux 𝓜 Ξ F a c b₀ ℓ V h (n + 1) ω
        ∂flowLaw N a) = fun _ => 0 := funext fun n => (hM n).2
    rw [e] at hDCT
    exact tendsto_nhds_unique hDCT tendsto_const_nhds
  have hΦint : Integrable (B.indicator Φ) (flowLaw N a) := by
    refine Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hM n).1.aestronglyMeasurable) hlim) (bracketBound a c b₀ ℓ V C δ) ?_
    filter_upwards [hgood] with ω ⟨hω, hgB⟩
    rw [Real.norm_eq_abs]
    by_cases hωB : ω ∈ B
    · obtain ⟨hmono, hlong⟩ := hgB hωB
      have hS := (mem_simpleRatSet_iff hF hac' (hherm ω hω)).2 hmono
      rw [Set.indicator_of_mem hωB]
      have e := m3Process_terminal Paux 𝓜 Ξ F a c b₀ ℓ V h hac' hω hS (hRF ω hmono)
      have hb := abs_m3Process_le Paux 𝓜 Ξ F a c b₀ ℓ V h hac' hℓ hδ hω hS (hRF ω hmono)
        (hC ω).1 hlong (Real.toNNReal (c - a)) (Real.coe_toNNReal _ (sub_nonneg.2 hac')).le
      rw [e] at hb
      exact hb
    · rw [Set.indicator_of_notMem hωB, abs_zero]
      exact hK0
  -- the endpoint term
  have hh' : Measurable (Function.uncurry h) :=
    hh.mono (sup_le_sup_right (MeasurableSpace.comap_mono (pathSigma_le F a a c)) _) le_rfl
  have hZ : ∀ σ, Measurable fun ω : FlowSample N => frameArray V (flowMatrix F a ω σ) :=
    fun σ => (Angular.measurable_frameArray V).comp (measurable_flowMatrix F a σ)
  have hXm : Measurable X :=
    (hh'.comp (measurable_id.prodMk (hZ c))).sub
      ((measurable_backwardFn_uncurry Paux 𝓜 Ξ F a c hMΞ h hh' a).comp
        (measurable_id.prodMk (hZ a)))
  have hXint : Integrable (B.indicator X) (flowLaw N a) := by
    refine Integrable.of_bound ((hXm.indicator hBm).aestronglyMeasurable) (2 * C) ?_
    filter_upwards [hgood] with ω ⟨hω, hgB⟩
    rw [Real.norm_eq_abs]
    by_cases hωB : ω ∈ B
    · obtain ⟨hmono, -⟩ := hgB hωB
      rw [Set.indicator_of_mem hωB]
      have h1 := arrayC2_abs_le (hC ω).1 (frameArray V (flowMatrix F a ω c))
      have h2 := arrayC2_abs_le ((refFlow_backward (hRF ω hmono) (hC ω).1).1 a ⟨le_rfl, hac'⟩)
        (frameArray V (flowMatrix F a ω a))
      exact (abs_sub _ _).trans (by linarith)
    · rw [Set.indicator_of_notMem hωB, abs_zero]
      positivity
  -- split
  have hI : B.indicator I = fun ω => B.indicator X ω - B.indicator Φ ω := by
    funext ω
    by_cases hωB : ω ∈ B
    · simp only [Set.indicator_of_mem hωB, hΦdef]
      ring
    · simp only [Set.indicator_of_notMem hωB, sub_zero]
  rw [← integral_indicator hBm, ← integral_indicator hBm, hI, integral_sub hXint hΦint, hzero,
    sub_zero]

end BlockBand.Critical.RelativeVectors.RelativeDuhamel
