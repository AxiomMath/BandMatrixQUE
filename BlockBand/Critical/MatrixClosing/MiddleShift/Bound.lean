module

public import BlockBand.Critical.MatrixClosing.MiddleShift.Params
public import BlockBand.Critical.BoundaryMean.KernelForm
public import BlockBand.Critical.BoundaryMean.NormBound
public import BlockBand.Critical.Collar.Density.UniversalBound

/-!
# The middle-only shifted collar mean: comparison with the common kernel at `(e+s, X - s)`

We compare the middle-only shifted collar kernel with the common collar kernel evaluated at the shifted
energy `e + s` and shifted boundary matrix `X - s`, first pointwise and then in expectation.
Law `collarLaw W b`, deterministic `X` with `Y = -Im X ≻ 0`, no norm bound. No hypothesis is used;
the common kernel enters only through the hypotheses of `middleKernel_mean_le`.

## Main results

* `abs_middle_sub_common_le` (pointwise, Hermitian blocks): with `f = q*𝒫(U_s𝔯)q`, `g₁ = q*𝒫'q`,
  `g₂ = q̃*𝒫'q̃`, `q̃ = Z'⁻*q`: `|ηf - η'g₁| ≤ ‖Δ‖(η'g₁ + B) + ‖Δ‖²B`, `B = 2‖q‖²/(4η') + 2η'g₂`.
  (`𝒫(U_s𝔯) = η⁻¹PYP*`, `P = P' + ΔN⁻¹`, `𝒫' = η'⁻¹P'YP'*`, `N⁻¹ = Z'⁻¹(I - P')`.)
* `middleKernel_mean_le`: if the expected common kernel at `(e+s, X - s)` is within `err'` of `1` in
  operator norm, then the middle kernel is integrable and its expectation is within an explicit
  bound of `1`, linear in `‖Δ‖`, `‖Δ‖²`, `err'` and `|η' - η|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.Collar.Kernel
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

theorem quadForm_real_smul {ι : Type*} [Fintype ι] (c : ℝ) (M : Matrix ι ι ℂ) (q : ι → ℂ) :
    quadForm ((c : ℂ) • M) q = c * quadForm M q := by
  unfold quadForm
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem quadForm_neg_vec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (q : ι → ℂ) :
    quadForm M (-q) = quadForm M q := by
  unfold quadForm
  simp [mulVec_neg]

/-- **Pointwise comparison of the two kernels** (one collar sample with Hermitian blocks,
`Y ≻ 0`). With `f = q*𝒫(U_s𝔯)q`, `g₁ = q*𝒫'q`, `g₂ = q̃*𝒫'q̃`, `q̃ = Z'⁻*q`:
`|ηf - η'g₁| ≤ ‖Δ‖(η'g₁ + B) + ‖Δ‖²B`, `B = 2‖q‖²/(4η') + 2η'g₂`. -/
theorem abs_middle_sub_common_le (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    (hη' : 0 < (boundaryZ b (e + s)).im) {ω : CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef)
    (q : Fin 2 × Fin W → ℂ) :
    |(boundaryZ b e).im * quadForm (middleKernel b e s 1 X ω) q -
        (boundaryZ b (e + s)).im * quadForm (poissonKernel (collarScattering b (e + s) 0 0 ω *
          oldScattering b (e + s) (X - (s : ℂ) • 1))) q| ≤
      ‖shiftDefect b e s‖ * ((boundaryZ b (e + s)).im * quadForm (poissonKernel
          (collarScattering b (e + s) 0 0 ω * oldScattering b (e + s) (X - (s : ℂ) • 1))) q +
        (2 * ((4 * (boundaryZ b (e + s)).im)⁻¹ * ∑ i, ‖q i‖ ^ 2) +
          2 * ((boundaryZ b (e + s)).im * quadForm (poissonKernel (collarScattering b (e + s) 0 0 ω *
            oldScattering b (e + s) (X - (s : ℂ) • 1)))
              (((boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1))⁻¹)ᴴ *ᵥ q)))) +
      ‖shiftDefect b e s‖ ^ 2 * (2 * ((4 * (boundaryZ b (e + s)).im)⁻¹ * ∑ i, ‖q i‖ ^ 2) +
          2 * ((boundaryZ b (e + s)).im * quadForm (poissonKernel (collarScattering b (e + s) 0 0 ω *
            oldScattering b (e + s) (X - (s : ℂ) • 1)))
              (((boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1))⁻¹)ᴴ *ᵥ q))) := by
  set η := (boundaryZ b e).im
  set η' := (boundaryZ b (e + s)).im
  set Δ := shiftDefect b e s
  set Y := -imPart X
  set N := collarSchur (e + s) 0 (X - (s : ℂ) • 1) ω
  set Z' := boundaryZ b (e + s) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (X - (s : ℂ) • 1)
  set P' := 1 - Z' * N⁻¹
  set qt := (Z'⁻¹)ᴴ *ᵥ q
  have hY' : (-imPart (X - (s : ℂ) • 1)).PosSemidef := by
    rw [imPart_sub_smul_one]; exact hY.posSemidef
  have hZ'u : IsUnit Z'.det := isUnit_det_boundaryZ_sub b (e + s) hη' hY'
  have hcom := commonKernel_eq b e s hη' hA hG hY
  have hmid := middleKernel_eq b e s hη hA hG hY
  rw [one_sub_mul_inv_split b e s X] at hmid
  -- the two forms
  have h1 : η * quadForm (middleKernel b e s 1 X ω) q =
      quadForm Y (P'ᴴ *ᵥ q + star Δ • ((N⁻¹)ᴴ *ᵥ q)) := by
    rw [hmid, quadForm_real_smul, ← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul,
      quadForm_sandwich, conjTranspose_add, conjTranspose_smul, add_mulVec, smul_mulVec]
    rfl
  have hcomq : ∀ v, η' * quadForm (poissonKernel (collarScattering b (e + s) 0 0 ω *
      oldScattering b (e + s) (X - (s : ℂ) • 1))) v = quadForm Y (P'ᴴ *ᵥ v) := by
    intro v
    rw [hcom, quadForm_real_smul, ← mul_assoc, mul_inv_cancel₀ hη'.ne', one_mul, quadForm_sandwich]
  rw [h1, hcomq, hcomq]
  have hpert := abs_quadForm_add_smul_sub_le hY.posSemidef (P'ᴴ *ᵥ q) ((N⁻¹)ᴴ *ᵥ q) (star Δ)
  rw [norm_star] at hpert
  -- the bound on the `N⁻¹` term
  have hR : (N⁻¹)ᴴ *ᵥ q = qt + -(P'ᴴ *ᵥ qt) := by
    have hNZ : N⁻¹ = Z'⁻¹ * (1 - P') := by
      simp only [P', sub_sub_cancel, ← Matrix.mul_assoc, nonsing_inv_mul _ hZ'u, Matrix.one_mul]
    rw [hNZ, conjTranspose_mul, ← mulVec_mulVec, conjTranspose_sub, conjTranspose_one, sub_mulVec,
      one_mulVec, sub_eq_add_neg]
  have hRq : quadForm Y ((N⁻¹)ᴴ *ᵥ q) ≤
      2 * ((4 * η')⁻¹ * ∑ i, ‖q i‖ ^ 2) + 2 * quadForm Y (P'ᴴ *ᵥ qt) := by
    rw [hR]
    refine (Collar.Density.quadForm_add_le_two hY.posSemidef _ _).trans ?_
    rw [quadForm_neg_vec]
    gcongr
    have := quadForm_inv_mul_mul_le hη' hZ'u (hZZ_shift b e s X) q
    rwa [quadForm_sandwich] at this
  have hΔ : 0 ≤ ‖Δ‖ := norm_nonneg _
  refine hpert.trans ?_
  have hu := WeightedDensity.quadForm_nonneg_of_posSemidef hY.posSemidef (P'ᴴ *ᵥ q)
  gcongr

/-!
## Expectations
-/

theorem measurable_middleKernel (b e s t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : CollarSample W => middleKernel b e s t X ω := by
  have hK : Measurable fun ω : CollarSample W => middleReaction b e s ω := by
    unfold middleReaction
    exact measurable_matrix_sub' (measurable_matrix_sub' measurable_blockDiag_collar
      measurable_const) (measurable_matrix_mul' (measurable_matrix_mul' measurable_bondMatrix_collar
        (measurable_matrix_inv' (measurable_matrix_sub' measurable_snd measurable_const)))
        (measurable_matrix_conjTranspose' measurable_bondMatrix_collar))
  have hU : Measurable fun ω : CollarSample W => middleScattering b e s ω := by
    unfold middleScattering
    exact measurable_matrix_sub' measurable_const (measurable_matrix_smul' _
      (measurable_matrix_inv' (measurable_matrix_add' hK measurable_const)))
  have hV : Measurable fun ω : CollarSample W => (t : ℂ) •
      (middleScattering b e s ω * oldScattering b e X) :=
    measurable_matrix_smul' _ (measurable_matrix_mul' hU measurable_const)
  unfold middleKernel BlockBand.Internal.Contracts.Critical.poissonKernel
  exact measurable_matrix_sub' (measurable_matrix_add' (measurable_matrix_inv'
    (measurable_matrix_sub' measurable_const hV)) (measurable_matrix_inv'
      (measurable_matrix_sub' measurable_const (measurable_matrix_conjTranspose' hV))))
    measurable_const

/-- `E q*Pq = q*(EP)q` (real parts) for integrable entries. -/
theorem integral_quadForm_eq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {P : Ω → Matrix ι ι ℂ} (hP : ∀ i j, Integrable (fun ω => P ω i j) μ) (q : ι → ℂ) :
    Integrable (fun ω => quadForm (P ω) q) μ ∧
      ∫ ω, quadForm (P ω) q ∂μ = quadForm (matrixExpect μ P) q := by
  have hi := Collar.Density.integrable_star_dotProduct_mulVec hP q
  refine ⟨hi.re, ?_⟩
  unfold quadForm
  rw [BoundaryMean.dotProduct_matrixExpect_mulVec hP q]
  exact integral_re hi

theorem quadForm_le_of_norm_sub_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} {c : ℝ} (h : ‖M - 1‖ ≤ c) (q : ι → ℂ) :
    |quadForm M q - ∑ i, ‖q i‖ ^ 2| ≤ c * ∑ i, ‖q i‖ ^ 2 := by
  have h1 := abs_quadForm_le_opNorm (M - 1) q
  have h2 : quadForm (M - 1) q = quadForm M q - ∑ i, ‖q i‖ ^ 2 := by
    rw [← quadForm_one]; unfold quadForm
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re]
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right h (by positivity))

/-- The constant `B_c = 2/(4η') + 2η'(1+err')/η'²`. -/
def bcConst (η' err' : ℝ) : ℝ := 2 * (4 * η')⁻¹ + 2 * η' * ((1 + err') * (η' ^ 2)⁻¹)

/-- **Mean of the middle kernel.** Integrating `abs_middle_sub_common_le`: the middle kernel is
integrable and `‖E 𝒫(U_s𝔯) - 1‖ ≤ η⁻¹(‖Δ‖(η'(1 + err') + B_c) + ‖Δ‖²B_c + η' err' + |η' - η|)`,
`B_c = bcConst η' err'`, given `‖E 𝒫' - 1‖ ≤ err'`. -/
theorem middleKernel_mean_le {b : ℝ} (e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    (hη' : 0 < (boundaryZ b (e + s)).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-imPart X).PosDef) (hint' : CollarKernelIntegrable b (e + s) 0 0 1 (X - (s : ℂ) • 1))
    {err' : ℝ} (herr' : ‖expectedCollarKernel b (e + s) 0 0 1 (X - (s : ℂ) • 1) - 1‖ ≤ err') :
    MiddleKernelIntegrable b e s 1 X ∧
      ‖expectedMiddleKernel b e s 1 X - 1‖ ≤ ((boundaryZ b e).im)⁻¹ *
        (‖shiftDefect b e s‖ * ((boundaryZ b (e + s)).im * (1 + err') +
            bcConst (boundaryZ b (e + s)).im err') +
          ‖shiftDefect b e s‖ ^ 2 * bcConst (boundaryZ b (e + s)).im err' +
          (boundaryZ b (e + s)).im * err' + |(boundaryZ b (e + s)).im - (boundaryZ b e).im|) := by
  set η := (boundaryZ b e).im
  set η' := (boundaryZ b (e + s)).im
  set Δ := shiftDefect b e s
  set Bc := bcConst η' err'
  set Pc : CollarSample W → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun ω =>
    BlockBand.Internal.Contracts.Critical.poissonKernel (collarScattering b (e + s) 0 0 ω * oldScattering b (e + s) (X - (s : ℂ) • 1))
  have hone : ∀ ω, BlockBand.Internal.Contracts.Critical.poissonKernel (((1 : ℝ) : ℂ) • (collarScattering b (e + s) 0 0 ω *
      oldScattering b (e + s) (X - (s : ℂ) • 1))) = Pc ω := fun ω => by simp [Pc]
  have hPc : ∀ i j, Integrable (fun ω => Pc ω i j) (collarLaw W b) := by
    intro i j; have := hint' i j; simp only [hone] at this; exact this
  have hEPc : expectedCollarKernel b (e + s) 0 0 1 (X - (s : ℂ) • 1) = matrixExpect (collarLaw W b) Pc := by
    unfold expectedCollarKernel; simp only [hone]
  rw [hEPc] at herr'
  have herr0 : 0 ≤ err' := (norm_nonneg _).trans herr'
  set Z' := boundaryZ b (e + s) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (X - (s : ℂ) • 1)
  have hY' : (-imPart (X - (s : ℂ) • 1)).PosSemidef := by
    rw [imPart_sub_smul_one]; exact hY.posSemidef
  have hZ'u : IsUnit Z'.det := isUnit_det_boundaryZ_sub b (e + s) hη' hY'
  -- expectations of the common kernel
  have hEg : ∀ v : Fin 2 × Fin W → ℂ, Integrable (fun ω => quadForm (Pc ω) v) (collarLaw W b) ∧
      ∫ ω, quadForm (Pc ω) v ∂collarLaw W b ≤ (1 + err') * ∑ i, ‖v i‖ ^ 2 ∧
      |∫ ω, quadForm (Pc ω) v ∂collarLaw W b - ∑ i, ‖v i‖ ^ 2| ≤ err' * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    obtain ⟨hi, heq⟩ := integral_quadForm_eq hPc v
    have h := quadForm_le_of_norm_sub_one_le herr' v
    rw [← heq] at h
    refine ⟨hi, ?_, h⟩
    have := (abs_le.1 h).2
    linarith
  -- a.s. Hermitian blocks
  have hH := Collar.Density.ae_collarMatrix_isHermitian b e (rePart_isHermitian X) (W := W)
  -- the pointwise bound, integrated
  have hmeasf : ∀ q, Measurable fun ω => quadForm (middleKernel b e s 1 X ω) q := fun q =>
    Collar.Density.measurable_re_star_dotProduct_mulVec
      (fun i j => Matrix.measurable_apply.comp (measurable_middleKernel b e s 1 X))
      (fun _ => measurable_const)
  set qt : (Fin 2 × Fin W → ℂ) → (Fin 2 × Fin W → ℂ) := fun q => (Z'⁻¹)ᴴ *ᵥ q
  have hqt : ∀ q, ∑ i, ‖qt q i‖ ^ 2 ≤ (η' ^ 2)⁻¹ * ∑ i, ‖q i‖ ^ 2 := fun q =>
    sum_norm_sq_inv_conjTranspose_mulVec_le hη' hY.posSemidef hZ'u (hZZ_shift b e s X) q
  set Bf : (Fin 2 × Fin W → ℂ) → CollarSample W → ℝ := fun q ω =>
    2 * ((4 * η')⁻¹ * ∑ i, ‖q i‖ ^ 2) + 2 * (η' * quadForm (Pc ω) (qt q))
  have hBfi : ∀ q, Integrable (Bf q) (collarLaw W b) := fun q =>
    (integrable_const _).add (((hEg (qt q)).1.const_mul η').const_mul 2)
  have hBfE : ∀ q, ∫ ω, Bf q ω ∂collarLaw W b ≤ Bc * ∑ i, ‖q i‖ ^ 2 := by
    intro q
    have i2 : Integrable (fun ω => 2 * (η' * quadForm (Pc ω) (qt q))) (collarLaw W b) :=
      ((hEg (qt q)).1.const_mul η').const_mul 2
    show ∫ ω, (2 * ((4 * η')⁻¹ * ∑ i, ‖q i‖ ^ 2) + 2 * (η' * quadForm (Pc ω) (qt q)))
      ∂collarLaw W b ≤ _
    rw [integral_add (integrable_const _) i2, integral_const, integral_const_mul,
      integral_const_mul]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have h1 := (hEg (qt q)).2.1
    have h2 := hqt q
    have h3 : η' * ∫ ω, quadForm (Pc ω) (qt q) ∂collarLaw W b ≤
        η' * ((1 + err') * ((η' ^ 2)⁻¹ * ∑ i, ‖q i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))) hη'.le
    calc 2 * ((4 * η')⁻¹ * ∑ i, ‖q i‖ ^ 2) + 2 * (η' * ∫ ω, quadForm (Pc ω) (qt q) ∂collarLaw W b)
        ≤ 2 * ((4 * η')⁻¹ * ∑ i, ‖q i‖ ^ 2) +
          2 * (η' * ((1 + err') * ((η' ^ 2)⁻¹ * ∑ i, ‖q i‖ ^ 2))) := by gcongr
      _ = Bc * ∑ i, ‖q i‖ ^ 2 := by simp only [Bc, bcConst]; ring
  have hpt : ∀ q, ∀ᵐ ω ∂collarLaw W b,
      0 ≤ quadForm (middleKernel b e s 1 X ω) q ∧
      |η * quadForm (middleKernel b e s 1 X ω) q - η' * quadForm (Pc ω) q| ≤
        ‖Δ‖ * (η' * quadForm (Pc ω) q + Bf q ω) + ‖Δ‖ ^ 2 * Bf q ω := by
    intro q
    filter_upwards [hH] with ω hω
    refine ⟨?_, abs_middle_sub_common_le b e s hη hη' hω.2.1 hω.2.2 hY q⟩
    rw [middleKernel_eq b e s hη hω.2.1 hω.2.2 hY, quadForm_real_smul]
    exact mul_nonneg (inv_nonneg.2 hη.le) (WeightedDensity.quadForm_nonneg_of_posSemidef
      (hY.posSemidef.mul_mul_conjTranspose_same _) q)
  set Rf : (Fin 2 × Fin W → ℂ) → CollarSample W → ℝ := fun q ω =>
    ‖Δ‖ * (η' * quadForm (Pc ω) q + Bf q ω) + ‖Δ‖ ^ 2 * Bf q ω
  have hRfi : ∀ q, Integrable (Rf q) (collarLaw W b) := fun q =>
    ((((hEg q).1.const_mul η').add (hBfi q)).const_mul _).add ((hBfi q).const_mul _)
  have hRfE : ∀ q, ∫ ω, Rf q ω ∂collarLaw W b ≤
      (‖Δ‖ * (η' * (1 + err') + Bc) + ‖Δ‖ ^ 2 * Bc) * ∑ i, ‖q i‖ ^ 2 := by
    intro q
    have i1 : Integrable (fun ω => η' * quadForm (Pc ω) q) (collarLaw W b) :=
      (hEg q).1.const_mul η'
    have i2 := hBfi q
    have i12 : Integrable (fun ω => η' * quadForm (Pc ω) q + Bf q ω) (collarLaw W b) := i1.add i2
    show ∫ ω, (‖Δ‖ * (η' * quadForm (Pc ω) q + Bf q ω) + ‖Δ‖ ^ 2 * Bf q ω) ∂collarLaw W b ≤ _
    rw [integral_add (i12.const_mul ‖Δ‖) (i2.const_mul _), integral_const_mul,
      integral_const_mul, integral_add i1 i2, integral_const_mul]
    have h1 := (hEg q).2.1
    have h2 := hBfE q
    have hΔ := norm_nonneg Δ
    have hq : 0 ≤ ∑ i, ‖q i‖ ^ 2 := by positivity
    have : η' * ∫ ω, quadForm (Pc ω) q ∂collarLaw W b ≤ η' * ((1 + err') * ∑ i, ‖q i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hη'.le
    calc ‖Δ‖ * (η' * ∫ ω, quadForm (Pc ω) q ∂collarLaw W b + ∫ ω, Bf q ω ∂collarLaw W b) +
          ‖Δ‖ ^ 2 * ∫ ω, Bf q ω ∂collarLaw W b ≤
        ‖Δ‖ * (η' * ((1 + err') * ∑ i, ‖q i‖ ^ 2) + Bc * ∑ i, ‖q i‖ ^ 2) +
          ‖Δ‖ ^ 2 * (Bc * ∑ i, ‖q i‖ ^ 2) := by gcongr
      _ = _ := by ring
  -- integrability of the middle kernel
  have hBc : 0 ≤ Bc := by simp only [Bc, bcConst]; positivity
  have hKpos : 0 ≤ η⁻¹ * (η' * (1 + err') + (‖Δ‖ * (η' * (1 + err') + Bc) + ‖Δ‖ ^ 2 * Bc)) := by
    positivity
  have hint : ∀ i j, Integrable (fun ω => middleKernel b e s 1 X ω i j) (collarLaw W b) := by
    have hpsd : ∀ᵐ ω ∂collarLaw W b, (middleKernel b e s 1 X ω).PosSemidef := by
      filter_upwards [hH] with ω hω
      rw [middleKernel_eq b e s hη hω.2.1 hω.2.2 hY]
      exact (hY.posSemidef.mul_mul_conjTranspose_same _).smul
        (Complex.zero_le_real.2 (inv_nonneg.2 hη.le))
    refine (integrable_and_posSemidef_of_quad_le (measurable_middleKernel b e s 1 X) hpsd hKpos
      fun q => ?_).1
    have hF : Integrable (fun ω => η⁻¹ * (η' * quadForm (Pc ω) q + Rf q ω)) (collarLaw W b) :=
      (((hEg q).1.const_mul η').add (hRfi q)).const_mul _
    have hle : ∀ᵐ ω ∂collarLaw W b, ENNReal.ofReal (star q ⬝ᵥ (middleKernel b e s 1 X ω *ᵥ q)).re ≤
        ENNReal.ofReal (η⁻¹ * (η' * quadForm (Pc ω) q + Rf q ω)) := by
      filter_upwards [hpt q] with ω hω
      apply ENNReal.ofReal_le_ofReal
      have := (abs_le.1 hω.2).2
      change quadForm _ q ≤ _
      rw [le_inv_mul_iff₀ hη]
      linarith
    have hFnn : 0 ≤ᵐ[collarLaw W b] fun ω => η⁻¹ * (η' * quadForm (Pc ω) q + Rf q ω) := by
      filter_upwards [hpt q] with ω hω
      have := (abs_le.1 hω.2).2
      have h0 := mul_nonneg hη.le hω.1
      exact mul_nonneg (inv_nonneg.2 hη.le) (by linarith)
    calc ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (middleKernel b e s 1 X ω *ᵥ q)).re ∂collarLaw W b ≤
        ∫⁻ ω, ENNReal.ofReal (η⁻¹ * (η' * quadForm (Pc ω) q + Rf q ω)) ∂collarLaw W b :=
          lintegral_mono_ae hle
      _ = ENNReal.ofReal (∫ ω, η⁻¹ * (η' * quadForm (Pc ω) q + Rf q ω) ∂collarLaw W b) :=
          (ofReal_integral_eq_lintegral_ofReal hF hFnn).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_const_mul, integral_add ((hEg q).1.const_mul η') (hRfi q),
            integral_const_mul]
          have h1 := (hEg q).2.1
          have h2 := hRfE q
          have : η' * ∫ ω, quadForm (Pc ω) q ∂collarLaw W b ≤ η' * ((1 + err') * ∑ i, ‖q i‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hη'.le
          calc η⁻¹ * (η' * ∫ ω, quadForm (Pc ω) q ∂collarLaw W b + ∫ ω, Rf q ω ∂collarLaw W b) ≤
              η⁻¹ * (η' * ((1 + err') * ∑ i, ‖q i‖ ^ 2) +
                (‖Δ‖ * (η' * (1 + err') + Bc) + ‖Δ‖ ^ 2 * Bc) * ∑ i, ‖q i‖ ^ 2) := by gcongr
            _ = _ := by ring
  refine ⟨hint, ?_⟩
  have hHerm : (expectedMiddleKernel b e s 1 X - 1).IsHermitian :=
    (BoundaryMean.matrixExpect_isHermitian fun ω => BoundaryMean.poissonKernel_isHermitian _).sub
      isHermitian_one
  have hc0 : 0 ≤ η⁻¹ * (‖Δ‖ * (η' * (1 + err') + Bc) + ‖Δ‖ ^ 2 * Bc + η' * err' + |η' - η|) := by
    positivity
  refine BoundaryMean.norm_le_of_abs_re_quad_le hHerm hc0 fun q => ?_
  obtain ⟨hfi, hfE⟩ := integral_quadForm_eq hint q
  have hsplit : (star q ⬝ᵥ ((expectedMiddleKernel b e s 1 X - 1) *ᵥ q)).re =
      ∫ ω, quadForm (middleKernel b e s 1 X ω) q ∂collarLaw W b - ∑ i, ‖q i‖ ^ 2 := by
    rw [hfE, ← quadForm_one]
    unfold quadForm expectedMiddleKernel
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re]
  rw [hsplit]
  have hg1 := (hEg q).1
  have hdiff : |η * ∫ ω, quadForm (middleKernel b e s 1 X ω) q ∂collarLaw W b -
      η' * ∫ ω, quadForm (Pc ω) q ∂collarLaw W b| ≤
      (‖Δ‖ * (η' * (1 + err') + Bc) + ‖Δ‖ ^ 2 * Bc) * ∑ i, ‖q i‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hfi.const_mul η)
      (hg1.const_mul η')]
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono_ae ((hfi.const_mul η).sub (hg1.const_mul η')).abs (hRfi q) ?_).trans
      (hRfE q)
    filter_upwards [hpt q] with ω hω
    exact hω.2
  have hg1E := (hEg q).2.2
  set F := ∫ ω, quadForm (middleKernel b e s 1 X ω) q ∂collarLaw W b
  set G := ∫ ω, quadForm (Pc ω) q ∂collarLaw W b
  set n := ∑ i, ‖q i‖ ^ 2
  have hn : 0 ≤ n := by positivity
  have hkey : F - n = η⁻¹ * ((η * F - η' * G) + η' * (G - n) + (η' - η) * n) := by
    field_simp; ring
  rw [hkey, abs_mul, abs_of_pos (inv_pos.2 hη), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hη.le)
  have h2 : |η' * (G - n)| ≤ η' * err' * n := by
    rw [abs_mul, abs_of_pos hη', mul_assoc]; exact mul_le_mul_of_nonneg_left hg1E hη'.le
  have h3 : |(η' - η) * n| = |η' - η| * n := by rw [abs_mul, abs_of_nonneg hn]
  calc |(η * F - η' * G) + η' * (G - n) + (η' - η) * n| ≤
      |η * F - η' * G| + |η' * (G - n)| + |(η' - η) * n| := abs_add_three _ _ _
    _ ≤ (‖Δ‖ * (η' * (1 + err') + Bc) + ‖Δ‖ ^ 2 * Bc) * n + η' * err' * n + |η' - η| * n := by
        rw [h3]; gcongr
    _ = _ := by ring

end BlockBand.Critical.MatrixClosing
