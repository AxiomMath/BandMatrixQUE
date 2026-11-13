module

public import BlockBand.Critical.RelativeVectors.AngularFields

/-!
# The Hessian representation of the backward function

For a probability space `(Ω_aux, P)`, measurable `M : Ω_aux → ℂ^{N×N}`, `Ξ : Ω_aux → (ℂ^r)^N`
with `‖z ↦ Mz‖ ≤ B` (operator norm on arrays, uniformly in `ω'`), and `f` of class `C²` with
`|f| ≤ K₀`, `‖Df‖ ≤ K₁`, `‖D²f‖ ≤ K₂` (Lean's operator norms), the function
`g(z) = ∫ f(Mz + Ξ) dP` (the backward function of `IsReferenceFlow.backward`) satisfies
* `fderiv_backward_apply`: `Dg(z)v = ∫ Df(Mz+Ξ)(Mv) dP`;
* `fderiv_fderiv_backward_apply`: `D²g(z)(v, w) = ∫ D²f(Mz+Ξ)(Mv, Mw) dP`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix

variable {N r : ℕ}

/-- The elementary label map `z ↦ e_i z_j`. -/
def Eij (i j : Fin N) : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin N => Fin r → ℂ) i).comp (ContinuousLinearMap.proj j)

/-- `z ↦ Mz` as a continuous `ℝ`-linear map of arrays, `Σ_{ij} M_ij E_ij`. -/
def arrayMulCLM (M : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) :=
  ∑ i, ∑ j, M i j • Eij i j

@[simp] theorem arrayMulCLM_apply (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → Fin r → ℂ) :
    arrayMulCLM M z = arrayMul M z := by
  funext k q
  simp [arrayMulCLM, Eij, arrayMul, Pi.single_apply, Finset.sum_apply, ite_apply]

theorem continuous_arrayMulCLM :
    Continuous (fun M : Matrix (Fin N) (Fin N) ℂ =>
      (arrayMulCLM M : (Fin N → Fin r → ℂ) →L[ℝ] _)) := by
  unfold arrayMulCLM
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).smul continuous_const

theorem continuous_arrayMul_apply (z : Fin N → Fin r → ℂ) :
    Continuous (fun M : Matrix (Fin N) (Fin N) ℂ => arrayMul M z) := by
  have : (fun M : Matrix (Fin N) (Fin N) ℂ => arrayMul M z) =
      fun M => (arrayMulCLM M : (Fin N → Fin r → ℂ) →L[ℝ] _) z := by
    funext M; rw [arrayMulCLM_apply]
  rw [this]
  exact (continuous_arrayMulCLM).clm_apply continuous_const

/-- `‖φ ↦ φ ∘ L‖ ≤ ‖L‖`. -/
theorem norm_compL_flip_le (L : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ)) :
    ‖(ContinuousLinearMap.compL ℝ (Fin N → Fin r → ℂ) (Fin N → Fin r → ℂ) ℝ).flip L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun φ => ?_
  have h := φ.opNorm_comp_le L
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  calc ‖φ.comp L‖ ≤ ‖φ‖ * ‖L‖ := h
    _ = ‖L‖ * ‖φ‖ := mul_comm _ _

section Representation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : Ω → Matrix (Fin N) (Fin N) ℂ} {Ξ : Ω → Fin N → Fin r → ℂ}
  {f : (Fin N → Fin r → ℂ) → ℝ}

/-- The integrand of the second derivative: `v ↦ (D²f(Mz+Ξ)(Mv)) ∘ M`. -/
def hessInt (f : (Fin N → Fin r → ℂ) → ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (x : Fin N → Fin r → ℂ) :
    (Fin N → Fin r → ℂ) →L[ℝ] ((Fin N → Fin r → ℂ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (Fin N → Fin r → ℂ) (Fin N → Fin r → ℂ) ℝ).flip
    (arrayMulCLM M)).comp ((fderiv ℝ (fderiv ℝ f) x).comp (arrayMulCLM M))

theorem hessInt_apply (f : (Fin N → Fin r → ℂ) → ℝ) (M : Matrix (Fin N) (Fin N) ℂ)
    (x v w : Fin N → Fin r → ℂ) :
    hessInt f M x v w = fderiv ℝ (fderiv ℝ f) x (arrayMul M v) (arrayMul M w) := by
  simp [hessInt]

theorem norm_comp_arrayMul_le {K B : ℝ} (φ : (Fin N → Fin r → ℂ) →L[ℝ] ℝ)
    (L : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ)) (hφ : ‖φ‖ ≤ K) (hL : ‖L‖ ≤ B)
    (hK : 0 ≤ K) : ‖φ.comp L‖ ≤ K * B :=
  (φ.opNorm_comp_le L).trans (mul_le_mul hφ hL (norm_nonneg L) hK)

theorem norm_hessInt_le {K₂ B : ℝ} (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → Fin r → ℂ)
    (hf2 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K₂) (hB : ‖(arrayMulCLM M : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ B)
    (hK₂ : 0 ≤ K₂) (hB0 : 0 ≤ B) : ‖hessInt f M x‖ ≤ B * K₂ * B := by
  unfold hessInt
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 := (norm_compL_flip_le (arrayMulCLM M : (Fin N → Fin r → ℂ) →L[ℝ] _)).trans hB
  have h2 : ‖(fderiv ℝ (fderiv ℝ f) x).comp (arrayMulCLM M : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤
      K₂ * B := by
    refine ((fderiv ℝ (fderiv ℝ f) x).opNorm_comp_le _).trans ?_
    exact mul_le_mul hf2 hB (norm_nonneg _) hK₂
  calc _ ≤ B * (K₂ * B) := mul_le_mul h1 h2
        (norm_nonneg ((fderiv ℝ (fderiv ℝ f) x).comp
          (arrayMulCLM M : (Fin N → Fin r → ℂ) →L[ℝ] _))) hB0
    _ = B * K₂ * B := by ring

/-- The first derivative under the integral. -/
theorem hasFDerivAt_backward (hM : Measurable M) (hΞ : Measurable Ξ) (hf : ContDiff ℝ 2 f)
    {B K₀ K₁ : ℝ} (hB : ∀ ω, ‖(arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ B)
    (hf0 : ∀ x, |f x| ≤ K₀) (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ K₁) (hK₁ : 0 ≤ K₁)
    (z : Fin N → Fin r → ℂ) :
    HasFDerivAt (fun z => ∫ ω, f (arrayMul (M ω) z + Ξ ω) ∂P)
      (∫ ω, (fderiv ℝ f (arrayMul (M ω) z + Ξ ω)).comp (arrayMulCLM (M ω)) ∂P) z := by
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hMX : Measurable fun ω => (M ω, Ξ ω) := hM.prodMk hΞ
  have hin : ∀ z : Fin N → Fin r → ℂ, Continuous fun p : Matrix (Fin N) (Fin N) ℂ ×
      (Fin N → Fin r → ℂ) => arrayMul p.1 z + p.2 :=
    fun z => ((continuous_arrayMul_apply z).comp continuous_fst).add continuous_snd
  have hc1 : ∀ z, Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      f (arrayMul p.1 z + p.2) := fun z => hfc.comp (hin z)
  have hc2 : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      (fderiv ℝ f (arrayMul p.1 z + p.2)).comp
        (arrayMulCLM p.1 : (Fin N → Fin r → ℂ) →L[ℝ] _) :=
    (hf'c.comp (hin z)).clm_comp (continuous_arrayMulCLM.comp continuous_fst)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := ℝ)
    (H := Fin N → Fin r → ℂ) (F := fun z ω => f (arrayMul (M ω) z + Ξ ω))
    (F' := fun z ω => (fderiv ℝ f (arrayMul (M ω) z + Ξ ω)).comp (arrayMulCLM (M ω))) (x₀ := z)
    (bound := fun _ => K₁ * B)
    (Filter.univ_mem) ?_ ?_ ?_ ?_ (integrable_const (μ := P) _) ?_
  · exact Filter.Eventually.of_forall fun z => ((hc1 z).measurable.comp hMX).aestronglyMeasurable
  · exact Integrable.of_bound (μ := P) ((hc1 z).measurable.comp hMX).aestronglyMeasurable K₀
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hf0 _)
  · exact (hc2.measurable.comp hMX).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω x _ =>
      norm_comp_arrayMul_le _ _ (hf1 _) (hB ω) hK₁
  · refine Filter.Eventually.of_forall fun ω x _ => ?_
    have hlin : HasFDerivAt (fun z => arrayMul (M ω) z + Ξ ω)
        (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _) x := by
      have := (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _).hasFDerivAt (x := x)
      have e : (fun z => arrayMul (M ω) z + Ξ ω) =
          fun z => (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _) z + Ξ ω := by
        funext z; rw [arrayMulCLM_apply]
      rw [e]
      exact this.add_const (Ξ ω)
    exact (hfd _).hasFDerivAt.comp x hlin

theorem fderiv_backward (hM : Measurable M) (hΞ : Measurable Ξ) (hf : ContDiff ℝ 2 f)
    {B K₀ K₁ : ℝ} (hB : ∀ ω, ‖(arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ B)
    (hf0 : ∀ x, |f x| ≤ K₀) (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ K₁) (hK₁ : 0 ≤ K₁) :
    fderiv ℝ (fun z => ∫ ω, f (arrayMul (M ω) z + Ξ ω) ∂P) =
      fun z => ∫ ω, (fderiv ℝ f (arrayMul (M ω) z + Ξ ω)).comp (arrayMulCLM (M ω)) ∂P := by
  funext z
  exact (hasFDerivAt_backward hM hΞ hf hB hf0 hf1 hK₁ z).fderiv

/-- The second derivative under the integral. -/
theorem hasFDerivAt_fderiv_backward (hM : Measurable M) (hΞ : Measurable Ξ)
    (hf : ContDiff ℝ 2 f) {B K₀ K₁ K₂ : ℝ}
    (hB : ∀ ω, ‖(arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ B) (hB0 : 0 ≤ B)
    (hf0 : ∀ x, |f x| ≤ K₀) (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ K₁) (hK₁ : 0 ≤ K₁)
    (hf2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K₂) (hK₂ : 0 ≤ K₂) (z : Fin N → Fin r → ℂ) :
    HasFDerivAt (fderiv ℝ (fun z => ∫ ω, f (arrayMul (M ω) z + Ξ ω) ∂P))
      (∫ ω, hessInt f (M ω) (arrayMul (M ω) z + Ξ ω) ∂P) z := by
  rw [fderiv_backward hM hΞ hf hB hf0 hf1 hK₁]
  have hf'd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hf''c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hMX : Measurable fun ω => (M ω, Ξ ω) := hM.prodMk hΞ
  have hin : ∀ z : Fin N → Fin r → ℂ, Continuous fun p : Matrix (Fin N) (Fin N) ℂ ×
      (Fin N → Fin r → ℂ) => arrayMul p.1 z + p.2 :=
    fun z => ((continuous_arrayMul_apply z).comp continuous_fst).add continuous_snd
  have hc2 : ∀ z, Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      (fderiv ℝ f (arrayMul p.1 z + p.2)).comp
        (arrayMulCLM p.1 : (Fin N → Fin r → ℂ) →L[ℝ] _) :=
    fun z => (hf'c.comp (hin z)).clm_comp (continuous_arrayMulCLM.comp continuous_fst)
  have hcompc : Continuous fun L : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) =>
      (ContinuousLinearMap.compL ℝ (Fin N → Fin r → ℂ) (Fin N → Fin r → ℂ) ℝ).flip L :=
    (ContinuousLinearMap.compL ℝ (Fin N → Fin r → ℂ) (Fin N → Fin r → ℂ) ℝ).flip.continuous
  have hc3 : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      hessInt f p.1 (arrayMul p.1 z + p.2) := by
    unfold hessInt
    exact (hcompc.comp (continuous_arrayMulCLM.comp continuous_fst)).clm_comp
      ((hf''c.comp (hin z)).clm_comp (continuous_arrayMulCLM.comp continuous_fst))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (E := (Fin N → Fin r → ℂ) →L[ℝ] ℝ) (H := Fin N → Fin r → ℂ)
    (F := fun z ω => (fderiv ℝ f (arrayMul (M ω) z + Ξ ω)).comp (arrayMulCLM (M ω)))
    (F' := fun z ω => hessInt f (M ω) (arrayMul (M ω) z + Ξ ω)) (x₀ := z)
    (bound := fun _ => B * K₂ * B)
    (Filter.univ_mem) ?_ ?_ ?_ ?_ (integrable_const (μ := P) _) ?_
  · exact Filter.Eventually.of_forall fun z => ((hc2 z).measurable.comp hMX).aestronglyMeasurable
  · exact Integrable.of_bound (μ := P) ((hc2 z).measurable.comp hMX).aestronglyMeasurable
      (K₁ * B) (Filter.Eventually.of_forall fun ω => norm_comp_arrayMul_le _ _ (hf1 _) (hB ω) hK₁)
  · exact (hc3.measurable.comp hMX).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω x _ => norm_hessInt_le _ _ (hf2 _) (hB ω) hK₂ hB0
  · refine Filter.Eventually.of_forall fun ω x _ => ?_
    have hlin : HasFDerivAt (fun z => arrayMul (M ω) z + Ξ ω)
        (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _) x := by
      have := (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _).hasFDerivAt (x := x)
      have e : (fun z => arrayMul (M ω) z + Ξ ω) =
          fun z => (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _) z + Ξ ω := by
        funext z; rw [arrayMulCLM_apply]
      rw [e]
      exact this.add_const (Ξ ω)
    have h1 := ((hf'd _).hasFDerivAt.comp x hlin)
    exact (((ContinuousLinearMap.compL ℝ (Fin N → Fin r → ℂ) (Fin N → Fin r → ℂ) ℝ).flip
      (arrayMulCLM (M ω))).hasFDerivAt).comp x h1

/-- **First derivative of the backward function**: `Dg(z)v = ∫ Df(Mz+Ξ)(Mv) dP`. -/
theorem fderiv_backward_apply (hM : Measurable M) (hΞ : Measurable Ξ) (hf : ContDiff ℝ 2 f)
    {B K₀ K₁ : ℝ} (hB : ∀ ω, ‖(arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ B)
    (hf0 : ∀ x, |f x| ≤ K₀) (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ K₁) (hK₁ : 0 ≤ K₁)
    (z v : Fin N → Fin r → ℂ) :
    fderiv ℝ (fun z => ∫ ω, f (arrayMul (M ω) z + Ξ ω) ∂P) z v =
      ∫ ω, fderiv ℝ f (arrayMul (M ω) z + Ξ ω) (arrayMul (M ω) v) ∂P := by
  have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hMX : Measurable fun ω => (M ω, Ξ ω) := hM.prodMk hΞ
  have hc2 : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      (fderiv ℝ f (arrayMul p.1 z + p.2)).comp
        (arrayMulCLM p.1 : (Fin N → Fin r → ℂ) →L[ℝ] _) :=
    (hf'c.comp (((continuous_arrayMul_apply z).comp continuous_fst).add continuous_snd)).clm_comp
      (continuous_arrayMulCLM.comp continuous_fst)
  rw [(hasFDerivAt_backward hM hΞ hf hB hf0 hf1 hK₁ z).fderiv]
  rw [ContinuousLinearMap.integral_apply]
  · simp only [ContinuousLinearMap.comp_apply, arrayMulCLM_apply]
  · exact Integrable.of_bound (μ := P) (hc2.measurable.comp hMX).aestronglyMeasurable
      (K₁ * B) (Filter.Eventually.of_forall fun ω => norm_comp_arrayMul_le _ _ (hf1 _) (hB ω) hK₁)

/-- **Hessian of the backward function**: `D²g(z)(v, w) = ∫ D²f(Mz+Ξ)(Mv, Mw) dP`
(that is, `∇_j²g_s = E_aux T_j^*(∇²f)T_j`). -/
theorem fderiv_fderiv_backward_apply (hM : Measurable M) (hΞ : Measurable Ξ)
    (hf : ContDiff ℝ 2 f) {B K₀ K₁ K₂ : ℝ}
    (hB : ∀ ω, ‖(arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ B) (hB0 : 0 ≤ B)
    (hf0 : ∀ x, |f x| ≤ K₀) (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ K₁) (hK₁ : 0 ≤ K₁)
    (hf2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K₂) (hK₂ : 0 ≤ K₂) (z v w : Fin N → Fin r → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => ∫ ω, f (arrayMul (M ω) z + Ξ ω) ∂P)) z v w =
      ∫ ω, fderiv ℝ (fderiv ℝ f) (arrayMul (M ω) z + Ξ ω) (arrayMul (M ω) v)
        (arrayMul (M ω) w) ∂P := by
  set g : (Fin N → Fin r → ℂ) → ℝ := fun z => ∫ ω, f (arrayMul (M ω) z + Ξ ω) ∂P with hg
  have hf'd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hf''c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hMX : Measurable fun ω => (M ω, Ξ ω) := hM.prodMk hΞ
  have hin : ∀ z : Fin N → Fin r → ℂ, Continuous fun p : Matrix (Fin N) (Fin N) ℂ ×
      (Fin N → Fin r → ℂ) => arrayMul p.1 z + p.2 :=
    fun z => ((continuous_arrayMul_apply z).comp continuous_fst).add continuous_snd
  have hD := hasFDerivAt_fderiv_backward (P := P) hM hΞ hf hB hB0 hf0 hf1 hK₁ hf2 hK₂ z
  set D := ∫ ω, hessInt f (M ω) (arrayMul (M ω) z + Ξ ω) ∂P with hDdef
  -- the derivative of `y ↦ Dg(y)w`, from `hD`
  have h1 : HasFDerivAt (fun y => fderiv ℝ g y w) (D.flip w) z := by
    have := hD.clm_apply (hasFDerivAt_const w z)
    simpa using this
  -- the derivative of `y ↦ Dg(y)w = ∫ Df(My+Ξ)(Mw)`, directly
  set G' : Ω → (Fin N → Fin r → ℂ) →L[ℝ] ℝ := fun ω =>
    ((fderiv ℝ (fderiv ℝ f) (arrayMul (M ω) z + Ξ ω)).flip (arrayMul (M ω) w)).comp
      (arrayMulCLM (M ω)) with hG'
  have hflipc : Continuous fun L : (Fin N → Fin r → ℂ) →L[ℝ] ((Fin N → Fin r → ℂ) →L[ℝ] ℝ) =>
      L.flip := (ContinuousLinearMap.flipₗᵢ ℝ (Fin N → Fin r → ℂ) (Fin N → Fin r → ℂ) ℝ).continuous
  have hGb : ∀ (ω : Ω) (x : Fin N → Fin r → ℂ),
      ‖((fderiv ℝ (fderiv ℝ f) x).flip (arrayMul (M ω) w)).comp
        (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ K₂ * (B * ‖w‖) * B := by
    intro ω x
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ?_ (hB ω) (norm_nonneg _)
      (by positivity))
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    refine mul_le_mul (hf2 x) ?_ (norm_nonneg _) hK₂
    rw [← arrayMulCLM_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hB ω) (norm_nonneg _))
  have h2 : HasFDerivAt (fun y => fderiv ℝ g y w) (∫ ω, G' ω ∂P) z := by
    have e : (fun y => fderiv ℝ g y w) =
        fun y => ∫ ω, fderiv ℝ f (arrayMul (M ω) y + Ξ ω) (arrayMul (M ω) w) ∂P := by
      funext y
      exact fderiv_backward_apply hM hΞ hf hB hf0 hf1 hK₁ y w
    rw [e]
    have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have hc1 : ∀ y, Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
        fderiv ℝ f (arrayMul p.1 y + p.2) (arrayMul p.1 w) :=
      fun y => (hf'c.comp (hin y)).clm_apply ((continuous_arrayMul_apply w).comp continuous_fst)
    have hc2 : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
        ((fderiv ℝ (fderiv ℝ f) (arrayMul p.1 z + p.2)).flip (arrayMul p.1 w)).comp
          (arrayMulCLM p.1 : (Fin N → Fin r → ℂ) →L[ℝ] _) :=
      ((hflipc.comp (hf''c.comp (hin z))).clm_apply
        ((continuous_arrayMul_apply w).comp continuous_fst)).clm_comp
        (continuous_arrayMulCLM.comp continuous_fst)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := ℝ)
      (H := Fin N → Fin r → ℂ)
      (F := fun y ω => fderiv ℝ f (arrayMul (M ω) y + Ξ ω) (arrayMul (M ω) w))
      (F' := fun y ω => ((fderiv ℝ (fderiv ℝ f) (arrayMul (M ω) y + Ξ ω)).flip
        (arrayMul (M ω) w)).comp (arrayMulCLM (M ω))) (x₀ := z)
      (bound := fun _ => K₂ * (B * ‖w‖) * B)
      (Filter.univ_mem) ?_ ?_ ?_ ?_ (integrable_const (μ := P) _) ?_
    · exact Filter.Eventually.of_forall fun y =>
        ((hc1 y).measurable.comp hMX).aestronglyMeasurable
    · refine Integrable.of_bound (μ := P) ((hc1 z).measurable.comp hMX).aestronglyMeasurable
        (K₁ * (B * ‖w‖)) (Filter.Eventually.of_forall fun ω => ?_)
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hf1 _) ?_ (norm_nonneg _) hK₁)
      rw [← arrayMulCLM_apply]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hB ω) (norm_nonneg _))
    · exact (hc2.measurable.comp hMX).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω x _ => hGb ω _
    · refine Filter.Eventually.of_forall fun ω x _ => ?_
      have hlin : HasFDerivAt (fun z => arrayMul (M ω) z + Ξ ω)
          (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _) x := by
        have := (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _).hasFDerivAt (x := x)
        have e : (fun z => arrayMul (M ω) z + Ξ ω) =
            fun z => (arrayMulCLM (M ω) : (Fin N → Fin r → ℂ) →L[ℝ] _) z + Ξ ω := by
          funext z; rw [arrayMulCLM_apply]
        rw [e]
        exact this.add_const (Ξ ω)
      have h3 := ((hf'd (arrayMul (M ω) x + Ξ ω)).hasFDerivAt.clm_apply
        (hasFDerivAt_const (arrayMul (M ω) w) (arrayMul (M ω) x + Ξ ω)))
      simp only [ContinuousLinearMap.comp_zero, zero_add] at h3
      exact h3.comp x hlin
  have hu := h1.unique h2
  have hGi : Integrable G' P := by
    have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have hc2 : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
        ((fderiv ℝ (fderiv ℝ f) (arrayMul p.1 z + p.2)).flip (arrayMul p.1 w)).comp
          (arrayMulCLM p.1 : (Fin N → Fin r → ℂ) →L[ℝ] _) :=
      ((hflipc.comp (hf''c.comp (hin z))).clm_apply
        ((continuous_arrayMul_apply w).comp continuous_fst)).clm_comp
        (continuous_arrayMulCLM.comp continuous_fst)
    exact Integrable.of_bound (μ := P) (hc2.measurable.comp hMX).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => hGb ω _)
  have hv := congrArg (fun L : (Fin N → Fin r → ℂ) →L[ℝ] ℝ => L v) hu
  simp only [ContinuousLinearMap.flip_apply] at hv
  rw [hD.fderiv, hv, ContinuousLinearMap.integral_apply hGi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp [hG', arrayMulCLM_apply]

end Representation

end BlockBand.Critical.RelativeVectors
