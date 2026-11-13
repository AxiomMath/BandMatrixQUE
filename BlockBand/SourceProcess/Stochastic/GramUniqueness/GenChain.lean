module
public import BlockBand.SourceProcess.Stochastic.SourceSDE.GenCalculus
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Chain rule for the generator

For `C²` maps `G : E → F` and `f : F → ℝ`,
`𝓛(f ∘ G)(y) = Df(G y)[𝓛G(y)] + ½ ∑_a D²f(G y)[DG(y) σ_a, DG(y) σ_a]`
(`sdeGenerator_comp`), where `𝓛G = vecGen` is the vector generator.
Pure calculus; no measure appears.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.SourceSDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*} [Fintype κ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_comp_apply' {f : F → ℝ} {G : E → F} {y : E} (hf : DifferentiableAt ℝ f (G y))
    (hG : DifferentiableAt ℝ G y) (v : E) :
    fderiv ℝ (fun q => f (G q)) y v = fderiv ℝ f (G y) (fderiv ℝ G y v) := by
  rw [show (fun q => f (G q)) = f ∘ G from rfl, fderiv_comp y hf hG]
  rfl

/-- Second derivative of a composition. -/
theorem fderiv_fderiv_comp_apply {f : F → ℝ} {G : E → F} (hf : ContDiff ℝ 2 f)
    (hG : ContDiff ℝ 2 G) (y v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => f (G q))) y v w =
      fderiv ℝ (fderiv ℝ f) (G y) (fderiv ℝ G y v) (fderiv ℝ G y w) +
        fderiv ℝ f (G y) (fderiv ℝ (fderiv ℝ G) y v w) := by
  have hH : ContDiff ℝ 2 (fun q => f (G q)) := hf.comp hG
  rw [← fderiv_fderiv_apply' hH y v w]
  have hfun : (fun q => fderiv ℝ (fun q => f (G q)) q w) =
      fun q => (fderiv ℝ f (G q)) (fderiv ℝ G q w) :=
    funext fun q => fderiv_comp_apply' (differentiable_of_contDiff hf _)
      (differentiable_of_contDiff hG q) w
  rw [hfun]
  have hA : DifferentiableAt ℝ (fun q => fderiv ℝ f (G q)) y :=
    (differentiable_fderiv_of_contDiff hf _).comp y (differentiable_of_contDiff hG y)
  have hu : DifferentiableAt ℝ (fun q => fderiv ℝ G q w) y := differentiable_fderiv_apply hG w y
  rw [fderiv_clm_apply hA hu]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [fderiv_fderiv_apply' hG y v w,
    show (fun q => fderiv ℝ f (G q)) = fderiv ℝ f ∘ G from rfl,
    fderiv_comp y (differentiable_fderiv_of_contDiff hf _) (differentiable_of_contDiff hG y)]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  exact add_comm _ _

/-- **Generator chain rule.** -/
theorem sdeGenerator_comp (b : E → E) (σ : κ → E → E) {f : F → ℝ} {G : E → F}
    (hf : ContDiff ℝ 2 f) (hG : ContDiff ℝ 2 G) (y : E) :
    sdeGenerator b σ (fun q => f (G q)) y =
      fderiv ℝ f (G y) (vecGen b σ G y) +
        (1 / 2 : ℝ) * ∑ a, fderiv ℝ (fderiv ℝ f) (G y)
          (fderiv ℝ G y (σ a y)) (fderiv ℝ G y (σ a y)) := by
  unfold sdeGenerator vecGen
  rw [fderiv_comp_apply' (differentiable_of_contDiff hf _) (differentiable_of_contDiff hG y)]
  simp only [fderiv_fderiv_comp_apply hf hG, map_add, map_smul, map_sum, smul_eq_mul,
    Finset.sum_add_distrib]
  ring

/-- The two-term form `Df(G)[d] + ½ ∑_a D²f(G)[ν_a, ν_a]` of a generator value. -/
def genSplit (f : F → ℝ) (G d : F) (ν : κ → F) : ℝ :=
  fderiv ℝ f G d + (1 / 2 : ℝ) * ∑ a, fderiv ℝ (fderiv ℝ f) G (ν a) (ν a)

omit [Fintype κ] in
theorem fderiv_bilin_diag_apply (B : E →L[ℝ] E →L[ℝ] F) (V H : E) :
    fderiv ℝ (fun W => B W W) V H = B H V + B V H := by
  have h := fderiv_bilin_apply B (G₁ := fun q : E => q) (G₂ := fun q => q) (y := V)
    differentiableAt_id differentiableAt_id H
  rw [fderiv_fun_id] at h
  exact h.trans (add_comm _ _)

theorem contDiff_bilin_diag (B : E →L[ℝ] E →L[ℝ] F) : ContDiff ℝ 2 (fun W => B W W) :=
  contDiff_bilin B (G₁ := fun q => q) (G₂ := fun q => q) contDiff_id contDiff_id

theorem vecGen_bilin_diag (b : E → E) (σ : κ → E → E) (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    vecGen b σ (fun W => B W W) y = B y (b y) + B (b y) y + ∑ a, B (σ a y) (σ a y) := by
  have h := vecGen_bilin b σ B (G₁ := fun q : E => q) (G₂ := fun q => q) contDiff_id contDiff_id y
  rw [vecGen_id, fderiv_fun_id] at h
  exact h

/-- **Generator of a function of a quadratic map** `q ↦ B q q`. -/
theorem sdeGenerator_comp_bilin (b : E → E) (σ : κ → E → E) {f : F → ℝ} (hf : ContDiff ℝ 2 f)
    (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    sdeGenerator b σ (fun q => f (B q q)) y =
      genSplit f (B y y) (B y (b y) + B (b y) y + ∑ a, B (σ a y) (σ a y))
        (fun a => B (σ a y) y + B y (σ a y)) := by
  rw [sdeGenerator_comp b σ hf (contDiff_bilin_diag B), vecGen_bilin_diag]
  simp only [genSplit, fderiv_bilin_diag_apply]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
