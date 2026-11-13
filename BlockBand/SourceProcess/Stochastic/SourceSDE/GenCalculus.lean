module
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionCalculus
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Generator calculus for `C²` maps

The deterministic chain rule behind the Itô computations of the finite Gram law. For drift
`b : E → E` and diffusion `σ : κ → E → E` the *vector generator*
of a map `G : E → F` is
`vecGen b σ G y = DG(y)[b y] + ½ ∑_a D²G(y)[σ_a y, σ_a y]`;
for `F = ℝ` it is `sdeGenerator` (`sdeGenerator_eq_vecGen`).

* `vecGen_bilin`: for a continuous real-bilinear `B` and `C²` maps `G₁, G₂`,
  `𝓛 B(G₁,G₂) = B(G₁, 𝓛G₂) + B(𝓛G₁, G₂) + ∑_a B(DG₁ σ_a, DG₂ σ_a)` (Itô product rule at the
  level of generators); `fderiv_bilin_apply` is the matching first-derivative rule.
* `vecGen_add`, `vecGen_sub`, `vecGen_const`, `vecGen_id`, `vecGen_clm`: linear rules.

No measure appears; `E`, `F` are arbitrary real normed spaces.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*} [Fintype κ]
variable {F F₁ F₂ F₃ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]

/-- The vector generator `DG(y)[b y] + ½ ∑_a D²G(y)[σ_a y, σ_a y]`. -/
def vecGen (b : E → E) (σ : κ → E → E) (G : E → F) (y : E) : F :=
  fderiv ℝ G y (b y) + (1 / 2 : ℝ) • ∑ a, fderiv ℝ (fderiv ℝ G) y (σ a y) (σ a y)

theorem sdeGenerator_eq_vecGen (b : E → E) (σ : κ → E → E) (φ : E → ℝ) (y : E) :
    sdeGenerator b σ φ y = vecGen b σ φ y := by
  simp only [sdeGenerator, vecGen, smul_eq_mul]

/-!
### First derivatives
-/

theorem fderiv_bilin_apply (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {G₁ : E → F₁} {G₂ : E → F₂} {y : E}
    (h₁ : DifferentiableAt ℝ G₁ y) (h₂ : DifferentiableAt ℝ G₂ y) (v : E) :
    fderiv ℝ (fun q => B (G₁ q) (G₂ q)) y v =
      B (G₁ y) (fderiv ℝ G₂ y v) + B (fderiv ℝ G₁ y v) (G₂ y) := by
  rw [ContinuousLinearMap.fderiv_of_bilinear B h₁ h₂]
  simp

theorem contDiff_bilin (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {G₁ : E → F₁} {G₂ : E → F₂} {n : WithTop ℕ∞}
    (h₁ : ContDiff ℝ n G₁) (h₂ : ContDiff ℝ n G₂) : ContDiff ℝ n (fun q => B (G₁ q) (G₂ q)) :=
  (B.contDiff.comp h₁).clm_apply h₂

theorem differentiable_fderiv_of_contDiff {G : E → F} (h : ContDiff ℝ 2 G) :
    Differentiable ℝ (fderiv ℝ G) :=
  (h.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

theorem differentiable_of_contDiff {G : E → F} (h : ContDiff ℝ 2 G) : Differentiable ℝ G :=
  h.differentiable (by norm_num)

/-- Directional second derivative: `D(q ↦ DG(q)[w])(y)[v] = D²G(y)[v, w]`. -/
theorem fderiv_fderiv_apply' {G : E → F} (h : ContDiff ℝ 2 G) (y v w : E) :
    fderiv ℝ (fun q => fderiv ℝ G q w) y v = fderiv ℝ (fderiv ℝ G) y v w := by
  rw [fderiv_clm_apply (differentiable_fderiv_of_contDiff h y) (differentiableAt_const w)]
  simp

theorem differentiable_fderiv_apply {G : E → F} (h : ContDiff ℝ 2 G) (w : E) :
    Differentiable ℝ (fun q => fderiv ℝ G q w) := fun q =>
  (differentiable_fderiv_of_contDiff h q).clm_apply (differentiableAt_const w)

/-!
### Second derivatives
-/

theorem fderiv_fderiv_bilin_apply (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {G₁ : E → F₁} {G₂ : E → F₂}
    (h₁ : ContDiff ℝ 2 G₁) (h₂ : ContDiff ℝ 2 G₂) (y v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => B (G₁ q) (G₂ q))) y v w =
      B (G₁ y) (fderiv ℝ (fderiv ℝ G₂) y v w) + B (fderiv ℝ G₁ y v) (fderiv ℝ G₂ y w) +
        (B (fderiv ℝ G₁ y w) (fderiv ℝ G₂ y v) + B (fderiv ℝ (fderiv ℝ G₁) y v w) (G₂ y)) := by
  have hH := contDiff_bilin B h₁ h₂
  rw [← fderiv_fderiv_apply' hH y v w]
  have hd₁ := differentiable_of_contDiff h₁
  have hd₂ := differentiable_of_contDiff h₂
  have hfun : (fun q => fderiv ℝ (fun q => B (G₁ q) (G₂ q)) q w) =
      fun q => B (G₁ q) (fderiv ℝ G₂ q w) + B (fderiv ℝ G₁ q w) (G₂ q) :=
    funext fun q => fderiv_bilin_apply B (hd₁ q) (hd₂ q) w
  rw [hfun]
  have e₁ := differentiable_fderiv_apply h₁ w
  have e₂ := differentiable_fderiv_apply h₂ w
  have d₁ : DifferentiableAt ℝ (fun q => B (G₁ q) (fderiv ℝ G₂ q w)) y :=
    (B.differentiableAt.comp y (hd₁ y)).clm_apply (e₂ y)
  have d₂ : DifferentiableAt ℝ (fun q => B (fderiv ℝ G₁ q w) (G₂ q)) y :=
    (B.differentiableAt.comp y (e₁ y)).clm_apply (hd₂ y)
  rw [fderiv_fun_add d₁ d₂,
    add_apply, fderiv_bilin_apply B (hd₁ y) (e₂ y),
    fderiv_bilin_apply B (e₁ y) (hd₂ y), fderiv_fderiv_apply' h₂, fderiv_fderiv_apply' h₁]

/-- **Generator of a bilinear composition** (Itô product rule). -/
theorem vecGen_bilin (b : E → E) (σ : κ → E → E) (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {G₁ : E → F₁}
    {G₂ : E → F₂} (h₁ : ContDiff ℝ 2 G₁) (h₂ : ContDiff ℝ 2 G₂) (y : E) :
    vecGen b σ (fun q => B (G₁ q) (G₂ q)) y =
      B (G₁ y) (vecGen b σ G₂ y) + B (vecGen b σ G₁ y) (G₂ y) +
        ∑ a, B (fderiv ℝ G₁ y (σ a y)) (fderiv ℝ G₂ y (σ a y)) := by
  unfold vecGen
  rw [fderiv_bilin_apply B (differentiable_of_contDiff h₁ y) (differentiable_of_contDiff h₂ y)]
  simp only [fderiv_fderiv_bilin_apply B h₁ h₂, map_add, map_smul, map_sum,
    add_apply, smul_apply, FunLike.coe_sum,
    Finset.sum_apply, Finset.sum_add_distrib]
  module

theorem vecGen_add (b : E → E) (σ : κ → E → E) {G₁ G₂ : E → F} (h₁ : ContDiff ℝ 2 G₁)
    (h₂ : ContDiff ℝ 2 G₂) (y : E) :
    vecGen b σ (fun q => G₁ q + G₂ q) y = vecGen b σ G₁ y + vecGen b σ G₂ y := by
  have hd₁ := differentiable_of_contDiff h₁
  have hd₂ := differentiable_of_contDiff h₂
  have hf : fderiv ℝ (fun q => G₁ q + G₂ q) = fun q => fderiv ℝ G₁ q + fderiv ℝ G₂ q :=
    funext fun q => fderiv_fun_add (hd₁ q) (hd₂ q)
  unfold vecGen
  rw [hf, fderiv_fun_add (differentiable_fderiv_of_contDiff h₁ y)
    (differentiable_fderiv_of_contDiff h₂ y)]
  simp only [add_apply, Finset.sum_add_distrib, smul_add]
  abel

theorem vecGen_sub (b : E → E) (σ : κ → E → E) {G₁ G₂ : E → F} (h₁ : ContDiff ℝ 2 G₁)
    (h₂ : ContDiff ℝ 2 G₂) (y : E) :
    vecGen b σ (fun q => G₁ q - G₂ q) y = vecGen b σ G₁ y - vecGen b σ G₂ y := by
  have hd₁ := differentiable_of_contDiff h₁
  have hd₂ := differentiable_of_contDiff h₂
  have hf : fderiv ℝ (fun q => G₁ q - G₂ q) = fun q => fderiv ℝ G₁ q - fderiv ℝ G₂ q :=
    funext fun q => fderiv_fun_sub (hd₁ q) (hd₂ q)
  unfold vecGen
  rw [hf, fderiv_fun_sub (differentiable_fderiv_of_contDiff h₁ y)
    (differentiable_fderiv_of_contDiff h₂ y)]
  simp only [sub_apply, Finset.sum_sub_distrib, smul_sub]
  abel

theorem vecGen_const (b : E → E) (σ : κ → E → E) (c : F) (y : E) :
    vecGen b σ (fun _ => c) y = 0 := by
  have hf : fderiv ℝ (fun _ : E => c) = fun _ => 0 := funext fun q => fderiv_const_apply c
  unfold vecGen
  rw [hf, fderiv_const_apply]
  simp

theorem vecGen_id (b : E → E) (σ : κ → E → E) (y : E) : vecGen b σ (fun q => q) y = b y := by
  have hf : fderiv ℝ (fun q : E => q) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun q => fderiv_fun_id
  unfold vecGen
  rw [hf, fderiv_const_apply]
  simp

/-- Generator of `ℓ ∘ G` for a continuous linear `ℓ`. -/
theorem vecGen_clm (b : E → E) (σ : κ → E → E) (ℓ : F₁ →L[ℝ] F₂) {G : E → F₁}
    (h : ContDiff ℝ 2 G) (y : E) : vecGen b σ (fun q => ℓ (G q)) y = ℓ (vecGen b σ G y) := by
  have e := vecGen_bilin b σ (ContinuousLinearMap.id ℝ (F₁ →L[ℝ] F₂)) (G₁ := fun _ => ℓ)
    contDiff_const h y
  simp only [ContinuousLinearMap.id_apply, vecGen_const, fderiv_const_apply,
    zero_apply, map_zero,
    Finset.sum_const_zero, add_zero] at e
  exact e

/-!
### Matching first-derivative rules
-/

theorem fderiv_add_apply' {G₁ G₂ : E → F} {y : E} (h₁ : DifferentiableAt ℝ G₁ y)
    (h₂ : DifferentiableAt ℝ G₂ y) (v : E) :
    fderiv ℝ (fun q => G₁ q + G₂ q) y v = fderiv ℝ G₁ y v + fderiv ℝ G₂ y v := by
  rw [fderiv_fun_add h₁ h₂, add_apply]

theorem fderiv_sub_apply' {G₁ G₂ : E → F} {y : E} (h₁ : DifferentiableAt ℝ G₁ y)
    (h₂ : DifferentiableAt ℝ G₂ y) (v : E) :
    fderiv ℝ (fun q => G₁ q - G₂ q) y v = fderiv ℝ G₁ y v - fderiv ℝ G₂ y v := by
  rw [fderiv_fun_sub h₁ h₂, sub_apply]

theorem fderiv_clm_apply' (ℓ : F₁ →L[ℝ] F₂) {G : E → F₁} {y : E} (h : DifferentiableAt ℝ G y)
    (v : E) : fderiv ℝ (fun q => ℓ (G q)) y v = ℓ (fderiv ℝ G y v) := by
  rw [show (fun q => ℓ (G q)) = ℓ ∘ G from rfl, fderiv_comp y ℓ.differentiableAt h]
  simp

end BlockBand.SourceProcess.Stochastic.SourceSDE
