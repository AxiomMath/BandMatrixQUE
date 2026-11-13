module

public import BlockBand.Coarea.GUELaw
public import BlockBand.Palm.MomentFlow.Generator
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Law and measurability of the matrix flow

* `map_flowMatrix_sub`: `(flowLaw N a).map (fun ω => flowMatrix F a ω σ - F) =
  gueMeasure (Fin N) (σ/N)` for `0 ≤ a ≤ σ`; the ingredients are
  `map_hermitianBrownian` (`hermitianBrownian B t ~ GUE_N(t/N)` under the constructed Wiener law,
  `E|B_ij(t)|² = t/N`), `gueMeasure_eq_map_coords` (`GUE_N(τ)` is the image of the centred product
  Gaussian of variance `τ` under one fixed real-linear map) and `gueMeasure_conv`
  (`GUE(τ₁) ∗ GUE(τ₂) = GUE(τ₁ + τ₂)`).
* Measurability: `measurable_hermitianBrownian`, `measurable_flowMatrix`,
  `measurable_flowEigenvalue`, `measurable_flowOverlap`, and the joint `(σ, ω)` forms
  `measurable_flowMatrix_uncurry`, `measurable_flowEigenvalue_uncurry`,
  `measurable_flowOverlap_uncurry`; `pathSigma_le` (`𝓛 ≤` ambient), so conditional expectations
  given `𝓛` are not vacuous.
* Definitions of `pathSigma` (`𝓛 = σ(λ_k(σ) : k, σ ∈ [s,c])`), `flowOverlap`
  (`X_k(σ) = N|q* u_k(σ)|²`) and `condMoment`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess BlockBand.Coarea.GUELaw
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

/-!
## Vocabulary of the conditional-moments lemma
-/

/-- `𝓛 = σ(λ_k(σ) : k ≤ N, σ ∈ [s, c])` for the flow with base variance `a`. -/
@[instance_reducible]
def pathSigma (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) : MeasurableSpace (FlowSample N) :=
  ⨆ σ ∈ Set.Icc s c, ⨆ k : Fin N,
    MeasurableSpace.comap (fun ω => flowEigenvalue F a ω σ k) inferInstance

/-- `X_k(σ) = N |q* u_k(σ)|²` along the matrix flow. -/
def flowOverlap (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) (σ : ℝ) (k : Fin N)
    (ω : FlowSample N) : ℝ :=
  (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector (flowMatrix F a ω σ) k‖ ^ 2

/-- `F_r(σ, ξ) = E[∏_i X_i(σ)^{ξ_i}/ξ_i! | 𝓛]` with `𝓛 = pathSigma F a a c`. -/
def condMoment (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (σ : ℝ) (ξ : Occ N) :
    FlowSample N → ℝ :=
  (flowLaw N a)[fun ω => momentMonomial (fun k => flowOverlap F a q σ k ω) ξ | pathSigma F a a c]

/-!
## The real-coordinate form of `GUE` and of the Hermitian Brownian increment
-/

/-- `B ↦ hermitianBrownian B t` in real coordinates: `r ↦ (√(2N))⁻¹ (X + Xᴴ)`, `X = circ r`. -/
def brownianOfCoords (N : ℕ) (r : ((Fin N × Fin N) × Fin 2) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => ((Real.sqrt (2 * N))⁻¹ : ℂ) *
    (circularBrownianCoordinates r (a, b) + conj (circularBrownianCoordinates r (b, a)))

theorem hermitianBrownian_eq_coords (B : FlowNoise N) (t : ℝ) :
    hermitianBrownian B t = brownianOfCoords N (fun q => B q (Real.toNNReal t)) := rfl

/-- The fixed real-linear map `K(r) = gueSample 1 (circ r)` (`(√2)⁻¹(X + Xᴴ)`). -/
def gueOfCoords (N : ℕ) (r : ((Fin N × Fin N) × Fin 2) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  gueSample 1 (circularBrownianCoordinates r)

theorem gueOfCoords_apply (r : ((Fin N × Fin N) × Fin 2) → ℝ) (a b : Fin N) :
    gueOfCoords N r a b = (Real.sqrt (1 / 2) : ℂ) *
      (((r ((a, b), 0) : ℂ) + (r ((a, b), 1) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ) +
        conj (((r ((b, a), 0) : ℂ) + (r ((b, a), 1) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ))) := by
  simp [gueOfCoords, gueSample, circularBrownianCoordinates]

theorem gueOfCoords_add (r s : ((Fin N × Fin N) × Fin 2) → ℝ) :
    gueOfCoords N (r + s) = gueOfCoords N r + gueOfCoords N s := by
  ext a b
  simp only [Matrix.add_apply, gueOfCoords_apply, Pi.add_apply, Complex.ofReal_add, map_add,
    map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem gueOfCoords_smul (c : ℝ) (r : ((Fin N × Fin N) × Fin 2) → ℝ) :
    gueOfCoords N (c • r) = (c : ℂ) • gueOfCoords N r := by
  ext a b
  simp only [Matrix.smul_apply, gueOfCoords_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem measurable_gueOfCoords : Measurable (gueOfCoords N) :=
  (measurable_gueSample 1).comp measurable_circularBrownianCoordinates

theorem measurable_brownianOfCoords : Measurable (brownianOfCoords N) := by
  apply Measurable.of_eval_matrix
  intro a b
  simp only [brownianOfCoords, Matrix.of_apply, circularBrownianCoordinates]
  fun_prop

/-- `gueSample τ (circ r) = K(√τ • r)`. -/
theorem gueSample_circ_eq (τ : ℝ≥0) (r : ((Fin N × Fin N) × Fin 2) → ℝ) :
    gueSample τ (circularBrownianCoordinates r) = gueOfCoords N (Real.sqrt τ • r) := by
  rw [gueOfCoords_smul]
  ext a b
  have h : Real.sqrt ((τ : ℝ) / 2) = Real.sqrt τ * Real.sqrt (1 / 2) := by
    rw [← Real.sqrt_mul τ.coe_nonneg]; ring_nf
  simp only [gueSample, gueOfCoords, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    NNReal.coe_one, h, Complex.ofReal_mul]
  ring

/-- `brownianOfCoords N r = K((√N)⁻¹ • r)`. -/
theorem brownianOfCoords_eq (r : ((Fin N × Fin N) × Fin 2) → ℝ) :
    brownianOfCoords N r = gueOfCoords N ((Real.sqrt N)⁻¹ • r) := by
  rw [gueOfCoords_smul]
  ext a b
  have h : (Real.sqrt (2 * N))⁻¹ = (Real.sqrt N)⁻¹ * Real.sqrt (1 / 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv, Real.sqrt_div' 1 (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_one]
    ring
  have hC : ((Real.sqrt (2 * N))⁻¹ : ℂ) = ((Real.sqrt N)⁻¹ : ℂ) * (Real.sqrt (1 / 2) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul, h]
  simp only [brownianOfCoords, gueOfCoords, gueSample, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, NNReal.coe_one]
  rw [hC]
  push_cast
  ring

/-!
## Centred product Gaussians
-/

/-- `(⊗ N(0,v)).map (c • ·) = ⊗ N(0, c²v)`. -/
theorem pi_gaussian_map_smul (κ : Type*) [Fintype κ] (v : ℝ≥0) (c : ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 v).map (fun r => c • r) =
      Measure.pi fun _ : κ => gaussianReal 0 (Real.toNNReal (c ^ 2) * v) := by
  have h := Measure.pi_map_pi (μ := fun _ : κ => gaussianReal 0 v)
    (f := fun (_ : κ) (x : ℝ) => c * x) (fun _ => (measurable_const_mul c).aemeasurable)
  have e : (fun r : κ → ℝ => c • r) = (fun x i => c * x i) := rfl
  rw [e, h]
  congr 1
  funext _
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg c)]

/-- `(⊗ μ_i ⊗ ⊗ ν_i).map (+) = ⊗ (μ_i ∗ ν_i)`. -/
theorem pi_prod_pi_map_add (κ : Type*) [Fintype κ] (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ((Measure.pi fun _ : κ => μ).prod (Measure.pi fun _ : κ => ν)).map (fun p => p.1 + p.2) =
      Measure.pi fun _ : κ => μ ∗ ν := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ κ (fun _ => μ) (fun _ => ν)
  rw [← hmp.map_eq, Measure.map_map (by fun_prop)
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ κ).measurable]
  have hpi := Measure.pi_map_pi (μ := fun _ : κ => μ.prod ν)
    (f := fun (_ : κ) (x : ℝ × ℝ) => x.1 + x.2) (fun _ => (by fun_prop : Measurable
      (fun x : ℝ × ℝ => x.1 + x.2)).aemeasurable)
  have e : ((fun p : (κ → ℝ) × (κ → ℝ) => p.1 + p.2) ∘
      MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ κ) = fun x i => (x i).1 + (x i).2 := rfl
  rw [e, hpi]
  rfl

/-- `GUE_N(τ)` is the image of `⊗ N(0, τ)` under the fixed real-linear map `K`. -/
theorem gueMeasure_eq_map_coords (τ : ℝ≥0) :
    gueMeasure (Fin N) τ =
      (Measure.pi fun _ : (Fin N × Fin N) × Fin 2 => gaussianReal 0 τ).map (gueOfCoords N) := by
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map (measurable_gueSample τ) measurable_circularBrownianCoordinates]
  have hfun : (gueSample τ ∘ circularBrownianCoordinates : _ → Matrix (Fin N) (Fin N) ℂ) =
      gueOfCoords N ∘ (fun r => Real.sqrt τ • r) := by
    funext r; exact gueSample_circ_eq τ r
  rw [hfun, ← Measure.map_map measurable_gueOfCoords (measurable_const_smul _),
    pi_gaussian_map_smul]
  congr 2
  funext _
  congr 1
  ext
  simp [Real.sq_sqrt τ.coe_nonneg]

theorem measurable_matrixEntry (i j : Fin N) :
    Measurable (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- Subtraction of matrices is jointly measurable. -/
theorem measurable_matrix_sub :
    Measurable (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 - p.2) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_matrixEntry i j).comp measurable_fst).sub
    ((measurable_matrixEntry i j).comp measurable_snd)

/-- Addition of matrices is jointly measurable. -/
theorem measurable_matrix_add :
    Measurable (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 + p.2) := by
  apply Measurable.of_eval_matrix
  intro i j
  have h1 : Measurable (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  have h2 : Measurable (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.2 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)
  exact h1.add h2

instance isProbabilityMeasure_flowLaw (a : ℝ) : IsProbabilityMeasure (flowLaw N a) := by
  unfold flowLaw; infer_instance

/-- `GUE(τ₁) ∗ GUE(τ₂) = GUE(τ₁ + τ₂)` (sum of independent GUE matrices). -/
theorem gueMeasure_conv (τ₁ τ₂ : ℝ≥0) :
    ((gueMeasure (Fin N) τ₁).prod (gueMeasure (Fin N) τ₂)).map (fun p => p.1 + p.2) =
      gueMeasure (Fin N) (τ₁ + τ₂) := by
  rw [gueMeasure_eq_map_coords τ₁, gueMeasure_eq_map_coords τ₂,
    Measure.map_prod_map _ _ measurable_gueOfCoords measurable_gueOfCoords,
    Measure.map_map measurable_matrix_add (measurable_gueOfCoords.prodMap measurable_gueOfCoords)]
  have hfun : ((fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 + p.2) ∘
      Prod.map (gueOfCoords N) (gueOfCoords N)) =
      gueOfCoords N ∘ (fun p => p.1 + p.2) := by
    funext p; simp [gueOfCoords_add]
  have hadd : Measurable (fun p : (((Fin N × Fin N) × Fin 2) → ℝ) ×
      (((Fin N × Fin N) × Fin 2) → ℝ) => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [hfun, ← Measure.map_map measurable_gueOfCoords hadd, pi_prod_pi_map_add,
    gueMeasure_eq_map_coords (τ₁ + τ₂)]
  congr 2
  funext _
  exact gaussianReal_conv_gaussianReal.trans (by simp)

/-!
## The Hermitian Brownian increment has law `GUE_N(t/N)`
-/

theorem measurable_wienerValue (t : ℝ≥0) :
    Measurable (fun B : FlowNoise N => fun q => B q t) :=
  Measurable.of_eval fun q => (ContinuousMap.measurable_eval t).comp (measurable_pi_apply q)

/-- The Wiener coordinates at a fixed time `t` are i.i.d. `N(0, t)`. -/
theorem map_wienerValue (t : ℝ≥0) :
    (commonWienerLaw ((Fin N × Fin N) × Fin 2)).map (fun B => fun q => B q t) =
      Measure.pi fun _ : (Fin N × Fin N) × Fin 2 => gaussianReal 0 t := by
  unfold commonWienerLaw
  rw [Measure.pi_map_pi (f := fun (_ : (Fin N × Fin N) × Fin 2) (ω : CanonicalWienerPath) => ω t)
    (fun _ => (ContinuousMap.measurable_eval t).aemeasurable)]
  congr 1
  funext _
  exact (canonicalWiener_isBrownian.toIsPreBrownianReal.hasLaw_eval t).map_eq

theorem measurable_hermitianBrownian (t : ℝ) :
    Measurable (fun B : FlowNoise N => hermitianBrownian B t) :=
  measurable_brownianOfCoords.comp (measurable_wienerValue _)

/-- **`E|B_ij(t)|² = t/N`**: `hermitianBrownian B t ~ GUE_N(t/N)` under the constructed Wiener law.
-/
theorem map_hermitianBrownian (t : ℝ) :
    (commonWienerLaw ((Fin N × Fin N) × Fin 2)).map (fun B => hermitianBrownian B t) =
      gueMeasure (Fin N) (Real.toNNReal t / N) := by
  have hfun : (fun B : FlowNoise N => hermitianBrownian B t) =
      (gueOfCoords N ∘ (fun r => (Real.sqrt N)⁻¹ • r)) ∘
        (fun B => fun q => B q (Real.toNNReal t)) := by
    funext B; simp only [Function.comp_apply, hermitianBrownian_eq_coords, brownianOfCoords_eq]
  rw [hfun, ← Measure.map_map (measurable_gueOfCoords.comp (measurable_const_smul _))
    (measurable_wienerValue _), map_wienerValue,
    ← Measure.map_map measurable_gueOfCoords (measurable_const_smul _), pi_gaussian_map_smul,
    gueMeasure_eq_map_coords]
  congr 2
  funext _
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [Real.coe_toNNReal _ (inv_nonneg.2 (Nat.cast_nonneg N))]
  ring

/-!
## The marginal law of the matrix flow
-/

theorem flowMatrix_sub (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ) :
    flowMatrix F a ω σ - F = ω.1 + hermitianBrownian ω.2 (σ - a) := by
  simp only [flowMatrix]; abel

/-- **Marginal law of the flow.** For `0 ≤ a ≤ σ`,
`flowMatrix F a ω σ - F = G_a + B(σ - a) ~ GUE_N(σ/N)` under `flowLaw N a`. -/
theorem map_flowMatrix_sub (F : Matrix (Fin N) (Fin N) ℂ) {a σ : ℝ} (ha : 0 ≤ a) (haσ : a ≤ σ) :
    (flowLaw N a).map (fun ω => flowMatrix F a ω σ - F) =
      gueMeasure (Fin N) (Real.toNNReal (σ / N)) := by
  have hfun : (fun ω : FlowSample N => flowMatrix F a ω σ - F) =
      (fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ => p.1 + p.2) ∘
        Prod.map id (fun B => hermitianBrownian B (σ - a)) := by
    funext ω; simp [flowMatrix_sub]
  unfold flowLaw
  rw [hfun, ← Measure.map_map measurable_matrix_add (measurable_id.prodMap
    (measurable_hermitianBrownian _)), ← Measure.map_prod_map _ _ measurable_id
    (measurable_hermitianBrownian _), Measure.map_id, map_hermitianBrownian, gueMeasure_conv]
  congr 1
  ext
  simp only [NNReal.coe_add, Real.coe_toNNReal', NNReal.coe_div, NNReal.coe_natCast]
  rw [max_eq_left (by positivity), max_eq_left (by linarith),
    max_eq_left (div_nonneg (by linarith) (Nat.cast_nonneg N))]
  ring

/-!
## Measurability
-/

theorem measurable_flowMatrix (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ) :
    Measurable (fun ω : FlowSample N => flowMatrix F a ω σ) :=
  measurable_matrix_add.comp ((measurable_matrix_add.comp (measurable_const.prodMk measurable_fst)).prodMk
    ((measurable_hermitianBrownian _).comp measurable_snd))

theorem continuous_hermitianBrownian (B : FlowNoise N) :
    Continuous (fun t : ℝ => hermitianBrownian B t) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  have hc : ∀ q, Continuous (fun t : ℝ => B q (Real.toNNReal t)) := fun q =>
    (B q).continuous.comp continuous_real_toNNReal
  simp only [hermitianBrownian, Matrix.of_apply, circularBrownianCoordinates]
  have := hc ((a, b), 0); have := hc ((a, b), 1); have := hc ((b, a), 0); have := hc ((b, a), 1)
  fun_prop

theorem continuous_flowMatrix (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) :
    Continuous (fun σ => flowMatrix F a ω σ) :=
  continuous_const.add ((continuous_hermitianBrownian ω.2).comp (continuous_id.sub continuous_const))

/-- Joint measurability of `(σ, ω) ↦ H_σ(ω)` (continuous in `σ`, measurable in `ω`). -/
theorem measurable_flowMatrix_uncurry (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) :
    Measurable (fun p : ℝ × FlowSample N => flowMatrix F a p.2 p.1) := by
  apply Measurable.of_eval_matrix
  intro i j
  exact measurable_uncurry_of_continuous_of_measurable (u := fun σ ω => flowMatrix F a ω σ i j)
    (fun ω => (continuous_apply_apply i j).comp (continuous_flowMatrix F a ω))
    (fun σ => (measurable_entry i j).comp (measurable_flowMatrix F a σ))
where
  measurable_entry (i j : Fin N) : Measurable (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)

theorem measurable_flowEigenvalue (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ) (k : Fin N) :
    Measurable (fun ω : FlowSample N => flowEigenvalue F a ω σ k) :=
  (BlockBand.Model.Construction.measurable_rawIncreasingEigenvalue _).comp
    (measurable_flowMatrix F a σ)

theorem measurable_flowEigenvalue_uncurry (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (k : Fin N) :
    Measurable (fun p : ℝ × FlowSample N => flowEigenvalue F a p.2 p.1 k) :=
  (BlockBand.Model.Construction.measurable_rawIncreasingEigenvalue _).comp
    (measurable_flowMatrix_uncurry F a)

theorem measurable_freshEigenvector (k x : Fin N) :
    Measurable (fun K : Matrix (Fin N) (Fin N) ℂ => freshEigenvector K k x) :=
  BlockBand.Model.Construction.measurable_rawOrderedColumnSelection _ x

theorem measurable_overlapOf (q : Fin N → ℂ) (k : Fin N) :
    Measurable (fun K : Matrix (Fin N) (Fin N) ℂ =>
      (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K k‖ ^ 2) := by
  refine measurable_const.mul (Measurable.pow_const (Measurable.norm ?_) 2)
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun x _ => measurable_const.mul (measurable_freshEigenvector k x)

theorem measurable_flowOverlap (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ) (σ : ℝ)
    (k : Fin N) : Measurable (flowOverlap F a q σ k) :=
  (measurable_overlapOf q k).comp (measurable_flowMatrix F a σ)

theorem measurable_flowOverlap_uncurry (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ)
    (k : Fin N) : Measurable (fun p : ℝ × FlowSample N => flowOverlap F a q p.1 k p.2) :=
  (measurable_overlapOf q k).comp (measurable_flowMatrix_uncurry F a)

theorem measurable_momentMonomial (ξ : Occ N) :
    Measurable (fun X : Fin N → ℝ => momentMonomial X ξ) := by
  unfold momentMonomial
  exact Finset.measurable_prod _ fun i _ =>
    ((measurable_pi_apply i).pow_const _).div_const _

/-- `𝓛 ≤` ambient σ-algebra (so `condExp` given `𝓛` is a conditional expectation). -/
theorem pathSigma_le (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) :
    pathSigma F a s c ≤ (inferInstance : MeasurableSpace (FlowSample N)) := by
  refine iSup₂_le fun σ _ => iSup_le fun k => ?_
  exact (measurable_flowEigenvalue F a σ k).comap_le

/-- Every eigenvalue in the window is `𝓛`-measurable. -/
theorem measurable_flowEigenvalue_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc s c) (k : Fin N) :
    Measurable[pathSigma F a s c] (fun ω : FlowSample N => flowEigenvalue F a ω σ k) := by
  refine Measurable.of_comap_le ?_
  exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ Set.Icc s c) => ⨆ k : Fin N,
    MeasurableSpace.comap (fun ω : FlowSample N => flowEigenvalue F a ω σ k) inferInstance)
    σ hσ (le_iSup (fun k : Fin N => MeasurableSpace.comap
      (fun ω : FlowSample N => flowEigenvalue F a ω σ k) inferInstance) k)

end BlockBand.Palm.MomentFlow
