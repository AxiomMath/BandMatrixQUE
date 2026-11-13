module

public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import BlockBand.SourceProcess.Stochastic.SDE
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Generic second-order calculus for the base diffusion

* `fderiv_fderiv_apply`: `D²φ(y)[h, k] = D(z ↦ Dφ(z)[k])(y)[h]`.
* `fderiv_fderiv_comp`: second-order chain rule
  `D²(g ∘ Φ)(y)[h, k] = D²g(Φ y)[DΦ h, DΦ k] + Dg(Φ y)[D²Φ(y)[h, k]]`.
* `sdeGenerator_comp`: `𝓛(g ∘ Φ) = Dg(Φ)[𝓛Φ] + ½ Σ_c D²g(Φ)[DΦ σ_c, DΦ σ_c]`, where
  `𝓛Φ = DΦ[b] + ½ Σ_c D²Φ[σ_c, σ_c]` (`sdeVecGenerator`).
* `mpGenerator_covOf`: the coordinate generator `mpGenerator b a` with `a = Σ_c σ_c σ_cᵀ`
  equals the coordinate-free `sdeGenerator b σ`.
* `lin_prod`, `bilin_prod`: linear and bilinear maps on `ℝ × ℝ` in coordinates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open BlockBand.SourceProcess.Stochastic

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `D²φ(y)[h, k] = D(z ↦ Dφ(z)[k])(y)[h]`. -/
theorem fderiv_fderiv_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : E → G}
    {y : E} (hφ : DifferentiableAt ℝ (fderiv ℝ φ) y) (h k : E) :
    fderiv ℝ (fderiv ℝ φ) y h k = fderiv ℝ (fun z => fderiv ℝ φ z k) y h := by
  rw [fderiv_clm_apply hφ (differentiableAt_const k)]
  simp

theorem differentiable_of_contDiff_two {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : E → G} (hφ : ContDiff ℝ 2 φ) : Differentiable ℝ φ :=
  hφ.differentiable (by norm_num)

theorem differentiable_fderiv_of_contDiff_two {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {φ : E → G} (hφ : ContDiff ℝ 2 φ) : Differentiable ℝ (fderiv ℝ φ) :=
  (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

/-- First-order chain rule, applied. -/
theorem fderiv_comp_apply' {g : F → ℝ} {Φ : E → F} (hg : ContDiff ℝ 2 g) (hΦ : ContDiff ℝ 2 Φ)
    (y h : E) : fderiv ℝ (g ∘ Φ) y h = fderiv ℝ g (Φ y) (fderiv ℝ Φ y h) := by
  rw [fderiv_comp y (differentiable_of_contDiff_two hg _) (differentiable_of_contDiff_two hΦ y)]
  rfl

/-- **Second-order chain rule.** -/
theorem fderiv_fderiv_comp {g : F → ℝ} {Φ : E → F} (hg : ContDiff ℝ 2 g) (hΦ : ContDiff ℝ 2 Φ)
    (y h k : E) :
    fderiv ℝ (fderiv ℝ (g ∘ Φ)) y h k =
      fderiv ℝ (fderiv ℝ g) (Φ y) (fderiv ℝ Φ y h) (fderiv ℝ Φ y k) +
        fderiv ℝ g (Φ y) (fderiv ℝ (fderiv ℝ Φ) y h k) := by
  have e : fderiv ℝ (g ∘ Φ) = fun z => (fderiv ℝ g (Φ z)).comp (fderiv ℝ Φ z) :=
    funext fun z => fderiv_comp z (differentiable_of_contDiff_two hg _)
      (differentiable_of_contDiff_two hΦ z)
  have hc : HasFDerivAt (fun z => fderiv ℝ g (Φ z))
      ((fderiv ℝ (fderiv ℝ g) (Φ y)).comp (fderiv ℝ Φ y)) y :=
    (differentiable_fderiv_of_contDiff_two hg (Φ y)).hasFDerivAt.comp y
      (differentiable_of_contDiff_two hΦ y).hasFDerivAt
  have hd : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) y) y :=
    (differentiable_fderiv_of_contDiff_two hΦ y).hasFDerivAt
  rw [e, (hc.clm_comp hd).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm]

variable {κ : Type*} [Fintype κ]

/-- The vector generator `𝓛Φ = DΦ[b] + ½ Σ_c D²Φ[σ_c, σ_c]` of a vector-valued function. -/
def sdeVecGenerator (b : E → E) (σ : κ → E → E) (Φ : E → F) (y : E) : F :=
  fderiv ℝ Φ y (b y) + (1 / 2 : ℝ) • ∑ c, fderiv ℝ (fderiv ℝ Φ) y (σ c y) (σ c y)

/-- The generator of a composite. -/
theorem sdeGenerator_comp [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {g : F → ℝ} {Φ : E → F} (hg : ContDiff ℝ 2 g) (hΦ : ContDiff ℝ 2 Φ) (b : E → E)
    (σ : κ → E → E) (y : E) :
    sdeGenerator b σ (g ∘ Φ) y = fderiv ℝ g (Φ y) (sdeVecGenerator b σ Φ y) +
      (1 / 2 : ℝ) * ∑ c, fderiv ℝ (fderiv ℝ g) (Φ y) (fderiv ℝ Φ y (σ c y))
        (fderiv ℝ Φ y (σ c y)) := by
  unfold sdeGenerator sdeVecGenerator
  simp only [fderiv_comp_apply' hg hΦ, fderiv_fderiv_comp hg hΦ, Finset.sum_add_distrib,
    map_add, map_smul, map_sum, smul_eq_mul]
  ring

end Generic

section Coordinates

variable {d m : ℕ}

theorem eq_sum_single (v : Fin d → ℝ) : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- The coordinate generator with `a = Σ_c σ_c σ_cᵀ` is `sdeGenerator`. -/
theorem mpGenerator_covOf (b : (Fin d → ℝ) → Fin d → ℝ) (σ : Fin m → (Fin d → ℝ) → Fin d → ℝ)
    (φ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    mpGenerator b (fun y => Matrix.of fun i j => ∑ c, σ c y i * σ c y j) φ y =
      sdeGenerator b σ φ y := by
  unfold mpGenerator sdeGenerator
  congr 1
  · conv_rhs => rw [eq_sum_single (b y)]
    simp [map_sum, map_smul]
  · congr 1
    have hB : ∀ c, fderiv ℝ (fderiv ℝ φ) y (σ c y) (σ c y) = ∑ i, ∑ j, σ c y i * σ c y j *
        fderiv ℝ (fderiv ℝ φ) y (Pi.single i 1) (Pi.single j 1) := by
      intro c
      conv_lhs => rw [eq_sum_single (σ c y)]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hB, Matrix.of_apply, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]

end Coordinates

section Plane

theorem lin_prod (L : ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) : L p = p.1 * L (1, 0) + p.2 * L (0, 1) := by
  have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [congrArg L hp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem bilin_prod (B : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (p q : ℝ × ℝ) :
    B p q = p.1 * q.1 * B (1, 0) (1, 0) + p.1 * q.2 * B (1, 0) (0, 1) +
      p.2 * q.1 * B (0, 1) (1, 0) + p.2 * q.2 * B (0, 1) (0, 1) := by
  have h1 := lin_prod (B.flip (1, 0)) p
  have h2 := lin_prod (B.flip (0, 1)) p
  simp only [ContinuousLinearMap.flip_apply] at h1 h2
  rw [lin_prod (B p) q, h1, h2]
  ring

end Plane

section Prod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*} [Fintype κ]

theorem fderiv_prod_apply {Φ₁ Φ₂ : E → ℝ} (h₁ : ContDiff ℝ 2 Φ₁) (h₂ : ContDiff ℝ 2 Φ₂)
    (y v : E) : fderiv ℝ (fun z => (Φ₁ z, Φ₂ z)) y v = (fderiv ℝ Φ₁ y v, fderiv ℝ Φ₂ y v) := by
  rw [DifferentiableAt.fderiv_prodMk (differentiable_of_contDiff_two h₁ y)
    (differentiable_of_contDiff_two h₂ y)]
  rfl

theorem fderiv_fderiv_prod_apply {Φ₁ Φ₂ : E → ℝ} (h₁ : ContDiff ℝ 2 Φ₁) (h₂ : ContDiff ℝ 2 Φ₂)
    (y h k : E) : fderiv ℝ (fderiv ℝ (fun z => (Φ₁ z, Φ₂ z))) y h k =
      (fderiv ℝ (fderiv ℝ Φ₁) y h k, fderiv ℝ (fderiv ℝ Φ₂) y h k) := by
  have h12 : ContDiff ℝ 2 (fun z => (Φ₁ z, Φ₂ z)) := h₁.prodMk h₂
  rw [fderiv_fderiv_apply (differentiable_fderiv_of_contDiff_two h12 y),
    fderiv_fderiv_apply (differentiable_fderiv_of_contDiff_two h₁ y),
    fderiv_fderiv_apply (differentiable_fderiv_of_contDiff_two h₂ y)]
  have e : (fun z => fderiv ℝ (fun z => (Φ₁ z, Φ₂ z)) z k) =
      fun z => (fderiv ℝ Φ₁ z k, fderiv ℝ Φ₂ z k) := funext fun z => fderiv_prod_apply h₁ h₂ z k
  rw [e, DifferentiableAt.fderiv_prodMk
    ((differentiable_fderiv_of_contDiff_two h₁ y).clm_apply (differentiableAt_const k))
    ((differentiable_fderiv_of_contDiff_two h₂ y).clm_apply (differentiableAt_const k))]
  rfl

theorem sdeVecGenerator_prod {Φ₁ Φ₂ : E → ℝ} (h₁ : ContDiff ℝ 2 Φ₁) (h₂ : ContDiff ℝ 2 Φ₂)
    (b : E → E) (σ : κ → E → E) (y : E) :
    sdeVecGenerator b σ (fun z => (Φ₁ z, Φ₂ z)) y =
      (sdeVecGenerator b σ Φ₁ y, sdeVecGenerator b σ Φ₂ y) := by
  unfold sdeVecGenerator
  simp only [fderiv_prod_apply h₁ h₂, fderiv_fderiv_prod_apply h₁ h₂]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

end Prod

end BlockBand.Diffusion
