module

public import BlockBand.Transmission.Dual.GHLeibniz

/-!
# Block calculus for diagonal generators: relabelling and products

Deterministic. For a diagonal covariance `diag(δ)`:
* `mpGenerator_comp_equiv`, `htDrift_comp_equiv`: the generator and the h-transformed drift of
  `F ∘ (· ∘ σ)` are those of `F` for the relabelled coefficients (`reindexDrift σ`);
* `mpGenerator_prod_left/right`: the generator of a function of one block of a decoupled
  (`prodDrift`) diagonal problem is that block's generator;
* `mpGenerator_prod_mul`: the generator of `f(left) g(right)` (the cross term vanishes);
* `htDrift_prod`: the h-transformed drift of `f(left) g(right)` is the pair of the factor
  h-transformed drifts, pointwise (no test function is involved).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Filter Topology Set Finset
open BlockBand.SourceProcess.Stochastic BlockBand.Transmission.Dual

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section CLM

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem fderiv_comp_clm_apply {f : F → ℝ} (L : E →L[ℝ] F) {w : E}
    (hf : DifferentiableAt ℝ f (L w)) (v : E) :
    fderiv ℝ (f ∘ L) w v = fderiv ℝ f (L w) (L v) := by
  rw [fderiv_comp w hf L.differentiableAt, L.fderiv]; rfl

theorem fderiv_fderiv_comp_clm_apply {f : F → ℝ} (L : E →L[ℝ] F) {w : E}
    (hf : ContDiffAt ℝ 2 f (L w)) (v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) w v v = fderiv ℝ (fderiv ℝ f) (L w) (L v) (L v) := by
  have hc : ContDiffAt ℝ 2 (f ∘ L) w := hf.comp w L.contDiff.contDiffAt
  rw [Exists.fderiv_fderiv_eq_deriv_line v hc, Exists.fderiv_fderiv_eq_deriv_line _ hf]
  congr 2
  funext r
  simp only [Function.comp_apply, map_add, map_smul]

end CLM

/-!
## Relabelling
-/

section Equiv

variable {d d' : ℕ}

/-- `y ↦ y ∘ σ` as a continuous linear map. -/
def compL (σ : Fin d' ≃ Fin d) : (Fin d → ℝ) →L[ℝ] (Fin d' → ℝ) :=
  ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj (σ s)

@[simp] theorem compL_apply (σ : Fin d' ≃ Fin d) (y : Fin d → ℝ) : compL σ y = y ∘ σ := rfl

theorem single_comp_equiv (σ : Fin d' ≃ Fin d) (k : Fin d) :
    (Pi.single k (1 : ℝ) : Fin d → ℝ) ∘ σ = Pi.single (σ.symm k) 1 := by
  funext s
  simp only [Function.comp_apply, Pi.single_apply, Equiv.eq_symm_apply]

/-- **The generator of a relabelled function.** -/
theorem mpGenerator_comp_equiv (σ : Fin d' ≃ Fin d) (b δ : (Fin d → ℝ) → Fin d → ℝ)
    {F : (Fin d' → ℝ) → ℝ} {w : Fin d → ℝ} (hF : ContDiffAt ℝ 2 F (compL σ w)) :
    mpGenerator b (fun y => Matrix.diagonal (δ y)) (F ∘ compL σ) w =
      mpGenerator (reindexDrift σ b) (fun y => Matrix.diagonal (reindexDrift σ δ y)) F
        (compL σ w) := by
  rw [mpGenerator_diag, mpGenerator_diag]
  simp only [fderiv_comp_clm_apply (compL σ) (hF.differentiableAt (by norm_num)),
    fderiv_fderiv_comp_clm_apply (compL σ) hF, compL_apply, single_comp_equiv, reindexDrift,
    comp_symm_comp]
  congr 1
  · exact Fintype.sum_equiv σ.symm _ _ fun k => by simp
  · congr 1
    exact Fintype.sum_equiv σ.symm _ _ fun k => by simp

/-- **The h-transformed drift of a relabelled function.** -/
theorem htDrift_comp_equiv (σ : Fin d' ≃ Fin d) (b δ : (Fin d → ℝ) → Fin d → ℝ)
    {F : (Fin d' → ℝ) → ℝ} {w : Fin d → ℝ} (hF : DifferentiableAt ℝ F (compL σ w)) :
    htDrift b δ (F ∘ compL σ) w =
      reindexDrift σ.symm (htDrift (reindexDrift σ b) (reindexDrift σ δ) F) w := by
  funext k
  simp only [htDrift, reindexDrift, fderiv_comp_clm_apply (compL σ) hF, compL_apply,
    single_comp_equiv, Equiv.symm_symm, Equiv.apply_symm_apply, Function.comp_apply,
    comp_symm_comp]

theorem reindexDrift_symm_reindexDrift (σ : Fin d' ≃ Fin d) (b : (Fin d' → ℝ) → Fin d' → ℝ) :
    reindexDrift σ (reindexDrift σ.symm b) = b := by
  funext y k
  simp only [reindexDrift, Equiv.symm_symm, Equiv.symm_apply_apply]
  congr 1
  funext i; simp

end Equiv

/-!
## Decoupled products
-/

section Prod

variable {d₁ d₂ : ℕ}

/-- `leftPart` as a continuous linear map. -/
def leftL : (Fin (d₁ + d₂) → ℝ) →L[ℝ] (Fin d₁ → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd d₂ i)

/-- `rightPart` as a continuous linear map. -/
def rightL : (Fin (d₁ + d₂) → ℝ) →L[ℝ] (Fin d₂ → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd d₁ j)

@[simp] theorem leftL_apply (y : Fin (d₁ + d₂) → ℝ) : leftL y = leftPart y := rfl

@[simp] theorem rightL_apply (y : Fin (d₁ + d₂) → ℝ) : rightL y = rightPart y := rfl

@[simp] theorem leftPart_single_castAdd (i : Fin d₁) :
    leftPart (Pi.single (Fin.castAdd d₂ i) (1 : ℝ) : Fin (d₁ + d₂) → ℝ) = Pi.single i 1 := by
  funext k; simp [leftPart, Pi.single_apply]

@[simp] theorem leftPart_single_natAdd (l : Fin d₂) :
    leftPart (Pi.single (Fin.natAdd d₁ l) (1 : ℝ) : Fin (d₁ + d₂) → ℝ) = 0 := by
  funext k; simp [leftPart, castAdd_ne_natAdd']

@[simp] theorem rightPart_single_castAdd (i : Fin d₁) :
    rightPart (Pi.single (Fin.castAdd d₂ i) (1 : ℝ) : Fin (d₁ + d₂) → ℝ) = 0 := by
  funext k; simp [rightPart, (castAdd_ne_natAdd' _ _).symm]

@[simp] theorem rightPart_single_natAdd (l : Fin d₂) :
    rightPart (Pi.single (Fin.natAdd d₁ l) (1 : ℝ) : Fin (d₁ + d₂) → ℝ) = Pi.single l 1 := by
  funext k; simp [rightPart, Pi.single_apply]

variable (b₁ δ₁ : (Fin d₁ → ℝ) → Fin d₁ → ℝ) (b₂ δ₂ : (Fin d₂ → ℝ) → Fin d₂ → ℝ)

/-- **The generator of a function of the left block.** -/
theorem mpGenerator_prod_left {f : (Fin d₁ → ℝ) → ℝ} {u : Fin (d₁ + d₂) → ℝ}
    (hf : ContDiffAt ℝ 2 f (leftL u)) :
    mpGenerator (prodDrift b₁ b₂) (fun y => Matrix.diagonal (prodDrift δ₁ δ₂ y)) (f ∘ leftL) u =
      mpGenerator b₁ (fun y => Matrix.diagonal (δ₁ y)) f (leftPart u) := by
  rw [mpGenerator_diag, mpGenerator_diag, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [fderiv_comp_clm_apply leftL (hf.differentiableAt (by norm_num)),
    fderiv_fderiv_comp_clm_apply leftL hf, leftL_apply, leftPart_single_castAdd,
    leftPart_single_natAdd, map_zero, mul_zero, sum_const_zero,
    add_zero, prodDrift, Fin.append_left]

/-- **The generator of a function of the right block.** -/
theorem mpGenerator_prod_right {g : (Fin d₂ → ℝ) → ℝ} {u : Fin (d₁ + d₂) → ℝ}
    (hg : ContDiffAt ℝ 2 g (rightL u)) :
    mpGenerator (prodDrift b₁ b₂) (fun y => Matrix.diagonal (prodDrift δ₁ δ₂ y)) (g ∘ rightL) u =
      mpGenerator b₂ (fun y => Matrix.diagonal (δ₂ y)) g (rightPart u) := by
  rw [mpGenerator_diag, mpGenerator_diag, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [fderiv_comp_clm_apply rightL (hg.differentiableAt (by norm_num)),
    fderiv_fderiv_comp_clm_apply rightL hg, rightL_apply, rightPart_single_castAdd,
    rightPart_single_natAdd, map_zero, mul_zero, sum_const_zero,
    zero_add, prodDrift, Fin.append_right]

/-- **The generator of a product of functions of the two blocks.** -/
theorem mpGenerator_prod_mul {f : (Fin d₁ → ℝ) → ℝ} {g : (Fin d₂ → ℝ) → ℝ}
    {u : Fin (d₁ + d₂) → ℝ} (hf : ContDiffAt ℝ 2 f (leftL u)) (hg : ContDiffAt ℝ 2 g (rightL u)) :
    mpGenerator (prodDrift b₁ b₂) (fun y => Matrix.diagonal (prodDrift δ₁ δ₂ y))
        (fun y => f (leftPart y) * g (rightPart y)) u =
      f (leftPart u) * mpGenerator b₂ (fun y => Matrix.diagonal (δ₂ y)) g (rightPart u) +
        g (rightPart u) * mpGenerator b₁ (fun y => Matrix.diagonal (δ₁ y)) f (leftPart u) := by
  have hf' : ContDiffAt ℝ 2 (f ∘ leftL) u := hf.comp u leftL.contDiff.contDiffAt
  have hg' : ContDiffAt ℝ 2 (g ∘ rightL) u := hg.comp u rightL.contDiff.contDiffAt
  have e := mpGenerator_mul_diag (prodDrift b₁ b₂) (prodDrift δ₁ δ₂) hf' hg'
  rw [mpGenerator_prod_left b₁ δ₁ b₂ δ₂ hf, mpGenerator_prod_right b₁ δ₁ b₂ δ₂ hg,
    Fin.sum_univ_add] at e
  simp only [fderiv_comp_clm_apply leftL (hf.differentiableAt (by norm_num)),
    fderiv_comp_clm_apply rightL (hg.differentiableAt (by norm_num)), leftL_apply, rightL_apply,
    leftPart_single_castAdd, leftPart_single_natAdd, rightPart_single_castAdd,
    rightPart_single_natAdd, map_zero, mul_zero, zero_mul, sum_const_zero, add_zero,
    Function.comp_apply] at e
  exact e

/-- **The h-transformed drift of a product** is the pair of the factor h-transformed drifts. -/
theorem htDrift_prod {f : (Fin d₁ → ℝ) → ℝ} {g : (Fin d₂ → ℝ) → ℝ} {u : Fin (d₁ + d₂) → ℝ}
    (hf : DifferentiableAt ℝ f (leftL u)) (hg : DifferentiableAt ℝ g (rightL u))
    (hf0 : f (leftPart u) ≠ 0) (hg0 : g (rightPart u) ≠ 0) :
    htDrift (prodDrift b₁ b₂) (prodDrift δ₁ δ₂) (fun y => f (leftPart y) * g (rightPart y)) u =
      prodDrift (htDrift b₁ δ₁ f) (htDrift b₂ δ₂ g) u := by
  have hf' : DifferentiableAt ℝ (f ∘ leftL) u := hf.comp u leftL.differentiableAt
  have hg' : DifferentiableAt ℝ (g ∘ rightL) u := hg.comp u rightL.differentiableAt
  have hd : ∀ v, fderiv ℝ (fun y => f (leftPart y) * g (rightPart y)) u v =
      f (leftPart u) * fderiv ℝ g (rightPart u) (rightPart v) +
        g (rightPart u) * fderiv ℝ f (leftPart u) (leftPart v) := fun v => by
    rw [show (fun y => f (leftPart y) * g (rightPart y)) = fun y => (f ∘ leftL) y * (g ∘ rightL) y
      from rfl, fderiv_mul_apply' hf' hg', fderiv_comp_clm_apply leftL hf,
      fderiv_comp_clm_apply rightL hg]
    rfl
  funext k
  induction k using Fin.addCases with
  | left i =>
    simp only [htDrift, hd, prodDrift, Fin.append_left, leftPart_single_castAdd,
      rightPart_single_castAdd, map_zero, mul_zero, zero_add]
    field_simp
  | right l =>
    simp only [htDrift, hd, prodDrift, Fin.append_right, leftPart_single_natAdd,
      rightPart_single_natAdd, map_zero, mul_zero, add_zero]
    field_simp

end Prod

end BlockBand.Transmission.Dual.G
