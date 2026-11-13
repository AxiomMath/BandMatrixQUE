module

public import BlockBand.Critical.Collar.Density.Canonical
public import BlockBand.Layers.MatchedScalar

/-!
# Kernel identity of the canonical collar density and the universal bound

The kernel identity expresses the Cauchy average of the weighted collar density
`q*(z - X - x)Ψ_X(x)(z - X - x)*q` as the expected resolvent quadratic form of the fresh row.
Combined with the fresh-row bound, it gives the universal bound `K_X Ψ_X(0) K_X* ⪯ C √W I`,
uniform in `W ≥ 1`, `e ∈ bulkInterval κ` and Hermitian `X`.

## Main results

* `lintegral_cauchyKernel_collarWeightedForm`: the kernel identity.
* `collarDensity_exists_universal`: the existence and universal clauses of the collar density
  bound.
* `collarDensityStatement_of_regular`: the regular clause `CollarDensityRegularClause` implies
  `CollarDensityStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Foundations.Spectral BlockBand.Critical.WeightedDensity
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

variable {W : ℕ}

/-!
## The fresh-row identity at an eigenpair
-/

theorem star_dotProduct_collarRowVec_of_eigen (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : CollarSample W} (hA : ∀ k, (ω.1.1 k).IsHermitian)
    {v : LayerSite W .common → ℂ} {lam : ℝ}
    (hv : collarMatrix e X ω *ᵥ v = (lam : ℂ) • v) (z : ℂ) (q : Fin 2 × Fin W → ℂ) :
    star v ⬝ᵥ collarRowVec (star z + e) q ω =
      star v ⬝ᵥ Sum.elim ((z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X -
        (lam : ℂ) • 1)ᴴ *ᵥ q) 0 := by
  set A := blockDiag ω.1.1 with hAdef
  set B := bondMatrix .common ω.1.2
  set D := A - (e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  set v₁ : Fin 2 × Fin W → ℂ := v ∘ Sum.inl
  set v₂ : PortSite W .common → ℂ := v ∘ Sum.inr
  have hAH : A.IsHermitian := BlockBand.Critical.Collar.Kernel.blockDiag_isHermitian' hA
  have hDH : D.IsHermitian := (hAH.sub (isHermitian_one.smul (Complex.conj_ofReal e))).sub hX
  have hvv : v = Sum.elim v₁ v₂ := (Sum.elim_comp_inl_inr v).symm
  have htop : D *ᵥ v₁ + B *ᵥ v₂ = (lam : ℂ) • v₁ := by
    have h := congrArg (fun f => f ∘ Sum.inl) hv
    simp only [collarMatrix, fromBlocks_mulVec] at h
    exact h
  have hstar : star v = Sum.elim (star v₁) (star v₂) := by
    rw [hvv]; funext x; cases x <;> rfl
  have hB : star v₂ ⬝ᵥ (Bᴴ *ᵥ q) = star (B *ᵥ v₂) ⬝ᵥ q := by
    rw [dotProduct_mulVec, star_mulVec]
  have hBv : B *ᵥ v₂ = (lam : ℂ) • v₁ - D *ᵥ v₁ := eq_sub_of_add_eq' htop
  have hD : star (D *ᵥ v₁) ⬝ᵥ q = star v₁ ⬝ᵥ (D *ᵥ q) := by
    rw [star_mulVec, ← dotProduct_mulVec, hDH.eq]
  rw [hstar, collarRowVec, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim,
    dotProduct_neg, hB, hBv, star_sub, sub_dotProduct, hD, star_smul, smul_dotProduct,
    dotProduct_zero, add_zero]
  have hvec : ((star z + e) • q - A *ᵥ q) - (lam : ℂ) • q + D *ᵥ q =
      (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X - (lam : ℂ) • 1)ᴴ *ᵥ q := by
    rw [conjTranspose_sub, conjTranspose_sub, hX.eq, conjTranspose_smul, conjTranspose_smul,
      conjTranspose_one]
    ext x
    simp only [D, sub_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [← hvec]
  simp only [← hAdef, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, add_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-!
## Fixed-matrix spectral identity
-/

/-- `q* M q` for an entrywise integral `M = ∫ f` (general index type). -/
theorem star_dotProduct_of_integral_mulVec' {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {f : Ω → Matrix ι ι ℂ} (hf : ∀ i j, Integrable (fun ω => f ω i j) μ)
    (y : ι → ℂ) :
    star y ⬝ᵥ ((Matrix.of fun i j => ∫ ω, f ω i j ∂μ) *ᵥ y) =
      ∫ ω, star y ⬝ᵥ (f ω *ᵥ y) ∂μ := by
  have hint : ∀ i j, Integrable (fun ω => star y i * (f ω i j * y j)) μ := fun i j =>
    ((hf i j).mul_const (y j)).const_mul (star y i)
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [integral_finsetSum (f := fun i ω => ∑ j, star (y i) * (f ω i j * y j)) _
    fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum (f := fun j ω => star (y i) * (f ω i j * y j)) _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

/-- Quadratic forms of the top block are quadratic forms of the zero-extended vector. -/
theorem star_dotProduct_toBlocks11_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix (m ⊕ n) (m ⊕ n) ℂ) (a : m → ℂ) :
    star a ⬝ᵥ (M.toBlocks₁₁ *ᵥ a) = star (Sum.elim a 0) ⬝ᵥ (M *ᵥ Sum.elim a 0) := by
  have hs : star (Sum.elim a (0 : n → ℂ)) = Sum.elim (star a) 0 := by
    funext x; cases x <;> simp
  conv_rhs => rw [← fromBlocks_toBlocks M, fromBlocks_mulVec, hs, sumElim_dotProduct_sumElim]
  simp

theorem re_star_dotProduct_specSum_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (g : ℝ → ℝ) (v : ι → ℂ) :
    (star v ⬝ᵥ (specSum hM (fun l => ((g l : ℝ) : ℂ)) *ᵥ v)).re =
      ∑ r, g (increasingEigenvalue hM r) * ‖star (increasingEigenvector hM r) ⬝ᵥ v‖ ^ 2 := by
  rw [dotProduct_specSum_mulVec, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Fixed-matrix kernel identity.** For a Hermitian `M`, vectors `a(x)` (continuous in `x`) and
`y(θ)` with `⟨b_r, y(θ)⟩ = ⟨b_r, a(λ_r + θ)⟩` at every eigenpair `(λ_r, b_r)` of `M`:
`∫ P_ε(-x) a(x)* φ_s(x - M) a(x) dx = E_θ π⁻¹ Im⟨y(θ), (M + θ - iε)⁻¹ y(θ)⟩`, `θ ~ N(0, s)`. -/
theorem lintegral_cauchy_cfc_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) {s : ℝ≥0} (hs : s ≠ 0) {ε : ℝ} (hε : 0 < ε) {a : ℝ → ι → ℂ}
    (ha : Continuous a) (y : ℝ → ι → ℂ)
    (hy : ∀ r θ, star (increasingEigenvector hM r) ⬝ᵥ y θ =
      star (increasingEigenvector hM r) ⬝ᵥ a (increasingEigenvalue hM r + θ)) :
    ∫⁻ x, ENNReal.ofReal (cauchyKernel ε (0 - x) *
        (star (a x) ⬝ᵥ (cfc (fun l => gaussianPDFReal 0 s (x - l)) M *ᵥ a x)).re) =
      ∫⁻ θ, ENNReal.ofReal (Real.pi⁻¹ * (star (y θ) ⬝ᵥ
        ((M + (θ : ℂ) • 1 - (⟨0, ε⟩ : ℂ) • 1)⁻¹ *ᵥ y θ)).im) ∂gaussianReal 0 s := by
  set n : Fin (Fintype.card ι) → ℝ → ℝ := fun r x =>
    ‖star (increasingEigenvector hM r) ⬝ᵥ a x‖ ^ 2 with hn
  have hnc : ∀ r, Continuous (n r) := fun r =>
    ((continuous_const.dotProduct ha).norm).pow 2
  have hn0 : ∀ r x, 0 ≤ n r x := fun r x => sq_nonneg _
  have hP0 : ∀ x, 0 ≤ cauchyKernel ε x := cauchyKernel_nonneg hε.le
  -- left side as a finite sum
  have hL : ∀ x, ENNReal.ofReal (cauchyKernel ε (0 - x) *
      (star (a x) ⬝ᵥ (cfc (fun l => gaussianPDFReal 0 s (x - l)) M *ᵥ a x)).re) =
      ∑ r, ENNReal.ofReal (cauchyKernel ε (0 - x) *
        (gaussianPDFReal 0 s (x - increasingEigenvalue hM r) * n r x)) := by
    intro x
    rw [cfc_eq_specSum hM, re_star_dotProduct_specSum_eq hM, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg fun r _ => mul_nonneg (hP0 _)
        (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hn0 r x))]
  -- right side as a finite sum
  have hR : ∀ θ, ENNReal.ofReal (Real.pi⁻¹ * (star (y θ) ⬝ᵥ
      ((M + (θ : ℂ) • 1 - (⟨0, ε⟩ : ℂ) • 1)⁻¹ *ᵥ y θ)).im) =
      ∑ r, ENNReal.ofReal (cauchyKernel ε (0 - (increasingEigenvalue hM r + θ)) *
        n r (increasingEigenvalue hM r + θ)) := by
    intro θ
    have hz : ((⟨0, ε⟩ : ℂ) - θ).im ≠ 0 := by simp [hε.ne']
    have hM' : M + (θ : ℂ) • (1 : Matrix ι ι ℂ) - (⟨0, ε⟩ : ℂ) • 1 =
        M - ((⟨0, ε⟩ : ℂ) - θ) • 1 := by rw [sub_smul]; abel
    rw [hM', inv_sub_eq_specSum hM hz, dotProduct_specSum_mulVec, Complex.im_sum, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [Complex.im_mul_ofReal, hy r θ, cauchyKernel_eq_im_inv hε]
      congr 1
      have : ((increasingEigenvalue hM r : ℂ) - ((⟨0, ε⟩ : ℂ) - θ)) =
          (((increasingEigenvalue hM r + θ : ℝ)) : ℂ) - ⟨0, ε⟩ := by push_cast; ring
      rw [this]
      ring
    · intro r _
      have h1 : 0 ≤ (((increasingEigenvalue hM r : ℂ) - ((⟨0, ε⟩ : ℂ) - θ))⁻¹).im := by
        have : ((increasingEigenvalue hM r : ℂ) - ((⟨0, ε⟩ : ℂ) - θ)) =
            (((increasingEigenvalue hM r + θ : ℝ)) : ℂ) - ⟨0, ε⟩ := by push_cast; ring
        rw [this]
        have h2 := cauchyKernel_eq_im_inv hε 0 (increasingEigenvalue hM r + θ)
        have h3 := hP0 (0 - (increasingEigenvalue hM r + θ))
        rw [h2] at h3
        exact nonneg_of_mul_nonneg_right h3 (inv_pos.2 Real.pi_pos) |>.trans_eq' rfl
      rw [Complex.im_mul_ofReal]
      exact mul_nonneg (inv_nonneg.2 Real.pi_pos.le) (mul_nonneg h1 (sq_nonneg _))
  simp_rw [hL, hR]
  have hmL : ∀ r, Measurable fun x => ENNReal.ofReal (cauchyKernel ε (0 - x) *
      (gaussianPDFReal 0 s (x - increasingEigenvalue hM r) * n r x)) := fun r =>
    (((continuous_cauchyKernel hε).comp (continuous_const.sub continuous_id)).measurable.mul
      (((measurable_gaussianPDFReal 0 s).comp (measurable_id.sub_const _)).mul
        (hnc r).measurable)).ennreal_ofReal
  have hmR : ∀ r, Measurable fun θ => ENNReal.ofReal (cauchyKernel ε
      (0 - (increasingEigenvalue hM r + θ)) * n r (increasingEigenvalue hM r + θ)) := fun r =>
    (((continuous_cauchyKernel hε).comp (continuous_const.sub (continuous_const.add
      continuous_id))).mul ((hnc r).comp (continuous_const.add continuous_id))).measurable.ennreal_ofReal
  rw [lintegral_finsetSum _ fun r _ => hmL r, lintegral_finsetSum _ fun r _ => hmR r]
  refine Finset.sum_congr rfl fun r _ => ?_
  set lam := increasingEigenvalue hM r
  rw [← lintegral_add_left_eq_self (fun x => ENNReal.ofReal (cauchyKernel ε (0 - x) *
      (gaussianPDFReal 0 s (x - lam) * n r x))) lam,
    gaussianReal_of_var_ne_zero 0 hs,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (hmR r)]
  refine lintegral_congr fun θ => ?_
  simp only [Pi.mul_apply, gaussianPDF, add_sub_cancel_left]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  ring

/-!
## The kernel identity of the collar density
-/

/-- `a(x) = (K - x)* q`, `K = z - X` (`z = z_b` gives `K_X = matchedLeadK`). -/
def collarWeightVec (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) (x : ℝ) : Fin 2 × Fin W → ℂ :=
  (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X -
    (x : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))ᴴ *ᵥ q

/-- `ρ_q(x) = q*(K - x) Ψ_X(x) (K - x)* q`, `K = z - X`. -/
def collarWeightedForm (W : ℕ) (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (z : ℂ)
    (q : Fin 2 × Fin W → ℂ) (x : ℝ) : ℝ :=
  (star (collarWeightVec z X q x) ⬝ᵥ (collarDensity W b e X x *ᵥ collarWeightVec z X q x)).re

theorem continuous_collarWeightVec (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) : Continuous (collarWeightVec z X q) :=
  ((continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)).matrix_conjTranspose
    ).matrix_mulVec continuous_const

theorem continuous_collarWeightedForm (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (z : ℂ)
    (q : Fin 2 × Fin W → ℂ) : Continuous (collarWeightedForm W b e X z q) :=
  Complex.continuous_re.comp ((continuous_star.comp (continuous_collarWeightVec z X q)).dotProduct
    ((continuous_collarDensity hW b e hX).matrix_mulVec (continuous_collarWeightVec z X q)))

/-- The resolvent quadratic form of the fresh row, as a measurable function of the sample. -/
theorem measurable_collarRowForm (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (z w : ℂ)
    (q : Fin 2 × Fin W → ℂ) (c : ℝ) :
    Measurable fun ω : CollarSample W => ENNReal.ofReal (c * (star (collarRowVec w q ω) ⬝ᵥ
      ((collarMatrix e X ω - z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
        collarRowVec w q ω)).im) := by
  have hM : Measurable fun ω : CollarSample W =>
      (collarMatrix e X ω - z • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ :=
    (BlockBand.Wegner.measurable_matrix_inv (n := LayerSite W .common)).comp
      (measurable_matrix_of_entries fun i j => ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp (measurable_collarMatrix e X))).sub measurable_const)
  have hcont : Continuous fun p : Matrix (LayerSite W .common) (LayerSite W .common) ℂ ×
      (LayerSite W .common → ℂ) => c * (star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).im :=
    continuous_const.mul (Complex.continuous_im.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd)))
  exact (hcont.measurable.comp (hM.prodMk (measurable_collarRowVec w q))).ennreal_ofReal

theorem measurable_re_star_dotProduct_mulVec {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {M : α → Matrix ι ι ℂ} {v : α → ι → ℂ} (hM : ∀ i j, Measurable fun a => M a i j)
    (hv : ∀ i, Measurable fun a => v a i) :
    Measurable fun a => (star (v a) ⬝ᵥ (M a *ᵥ v a)).re := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ =>
    (Complex.continuous_conj.measurable.comp (hv i)).mul
      (Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j)))

theorem integrable_star_dotProduct_mulVec {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {f : Ω → Matrix ι ι ℂ} (hf : ∀ i j, Integrable (fun ω => f ω i j) μ)
    (a : ι → ℂ) : Integrable (fun ω => star a ⬝ᵥ (f ω *ᵥ a)) μ := by
  have h : ∀ ω, star a ⬝ᵥ (f ω *ᵥ a) = ∑ i, ∑ j, star (a i) * (f ω i j * a j) := fun ω => by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  simp_rw [h]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hf i j).mul_const (a j)).const_mul (star (a i))

/-- **Kernel identity.** For `ε > 0` and every `z ∈ ℂ`:
`∫ P_ε(-x) q*(z - X - x)Ψ_X(x)(z - X - x)*q dx = E_collar π⁻¹ Im⟨y, (ℋ_X - iε)⁻¹ y⟩`,
`y = collarRowVec (z̄ + e) q` (the fresh row `(z + e - A, -B)*q`; the case of interest is `z = z_b`). -/
theorem lintegral_cauchyKernel_collarWeightedForm (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (z : ℂ)
    (q : Fin 2 × Fin W → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x, ENNReal.ofReal (cauchyKernel ε (0 - x) * collarWeightedForm W b e X z q x) =
      ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec (star z + e) q ω) ⬝ᵥ
        ((collarMatrix e X ω - (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec (star z + e) q ω)).im)
        ∂collarLaw W b := by
  set μ' := collarBase W b
  set N := gaussianReal 0 (commonShiftVar W b)
  have hs := commonShiftVar_ne_zero hW hb
  set w : ℂ := star z + e
  set ah : ℝ → LayerSite W .common → ℂ := fun x => Sum.elim (collarWeightVec z X q x) 0
  have hah : Continuous ah := by
    refine continuous_pi fun i => ?_
    cases i with
    | inl i => exact (continuous_apply i).comp (continuous_collarWeightVec z X q)
    | inr i => exact continuous_const
  have hHerm := ae_collarBase_isHermitian hW b e hX
  set Q : ℝ → CollarSample W → ℝ := fun x ω =>
    (star (ah x) ⬝ᵥ (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω) *ᵥ ah x)).re
  set Qr : ℝ → CollarSample W → ℝ := fun x ω =>
    (star (ah x) ⬝ᵥ (rawCfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω) *ᵥ ah x)).re
  have hQQr : ∀ ω, (collarMatrix e X ω).IsHermitian → ∀ x, Qr x ω = Q x ω := by
    intro ω hω x
    simp only [Qr, Q, rawCfc_eq_cfc hω]
  have hQ0 : ∀ ω, (collarMatrix e X ω).IsHermitian → ∀ x, 0 ≤ Q x ω := by
    intro ω hω x
    simp only [Q]
    rw [cfc_eq_specSum hω, re_star_dotProduct_specSum_eq hω]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (shiftWeight_nonneg _ _ _) (sq_nonneg _)
  -- the complex integrand and its integrability
  have hcint : ∀ x, Integrable (fun ω => star (ah x) ⬝ᵥ
      (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω) *ᵥ ah x)) μ' := by
    intro x
    exact integrable_star_dotProduct_mulVec
      (fun i j => integrable_cfc_shiftWeight hW b e hX x i j) (ah x)
  have hform : ∀ x, collarWeightedForm W b e X z q x = ∫ ω, Q x ω ∂μ' := by
    intro x
    simp only [collarWeightedForm, Q]
    have h1 := star_dotProduct_of_integral_mulVec' (μ := μ')
      (f := fun ω => (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)).toBlocks₁₁)
      (fun i j => integrable_cfc_shiftWeight hW b e hX x (Sum.inl i) (Sum.inl j))
      (collarWeightVec z X q x)
    have h2 : collarDensity W b e X x = Matrix.of fun i j => ∫ ω,
        (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)).toBlocks₁₁ i j ∂μ' := rfl
    rw [h2, h1, integral_congr_ae (Eventually.of_forall fun ω => star_dotProduct_toBlocks11_mulVec
      (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)) (collarWeightVec z X q x))]
    exact (integral_re (hcint x)).symm
  have hQint : ∀ x, Integrable (Q x) μ' := fun x => (hcint x).re
  have hstep2 : ∀ x, ENNReal.ofReal (cauchyKernel ε (0 - x) * collarWeightedForm W b e X z q x) =
      ∫⁻ ω, ENNReal.ofReal (cauchyKernel ε (0 - x) * Qr x ω) ∂μ' := by
    intro x
    rw [hform x, ← integral_const_mul,
      ofReal_integral_eq_lintegral_ofReal ((hQint x).const_mul _)]
    · refine lintegral_congr_ae ?_
      filter_upwards [hHerm] with ω hω
      rw [hQQr ω hω.1 x]
    · filter_upwards [hHerm] with ω hω
      exact mul_nonneg (cauchyKernel_nonneg hε.le _) (hQ0 ω hω.1 x)
  have hQrm : Measurable (Function.uncurry fun (x : ℝ) (ω : CollarSample W) =>
      ENNReal.ofReal (cauchyKernel ε (0 - x) * Qr x ω)) := by
    have hent : ∀ i j, Measurable fun p : ℝ × CollarSample W =>
        rawCfc (fun l => shiftWeight W b (p.1 - l)) (collarMatrix e X p.2) i j :=
      fun i j => measurable_rawCfc (measurable_collarMatrix e X)
        (g := fun x l => shiftWeight W b (x - l))
        ((measurable_shiftWeight W b).comp (measurable_fst.sub measurable_snd)) i j
    have hv : ∀ i, Measurable fun p : ℝ × CollarSample W => ah p.1 i := fun i =>
      ((continuous_apply i).comp hah).measurable.comp measurable_fst
    have hQ := measurable_re_star_dotProduct_mulVec hent hv
    exact ((((continuous_cauchyKernel hε).comp (continuous_const.sub continuous_id)).measurable.comp
      measurable_fst).mul hQ).ennreal_ofReal
  simp_rw [hstep2]
  rw [lintegral_lintegral_swap hQrm.aemeasurable]
  have hRm := measurable_collarRowForm (W := W) e X (⟨0, ε⟩ : ℂ) w q Real.pi⁻¹
  have hRm2 : Measurable fun a : CollarSample W × ℝ => ENNReal.ofReal (Real.pi⁻¹ *
      (star (collarRowVec w q (shiftSample a.2 a.1)) ⬝ᵥ ((collarMatrix e X (shiftSample a.2 a.1) -
        (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
          collarRowVec w q (shiftSample a.2 a.1))).im) :=
    Measurable.comp (f := fun p : CollarSample W × ℝ => shiftSample p.2 p.1) hRm measurable_shiftSample
  rw [(collarBase_spec hW b).2, lintegral_map hRm measurable_shiftSample,
    lintegral_prod _ hRm2.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hHerm] with ω hω
  have hM := hω.1
  rw [lintegral_congr fun x => by rw [hQQr ω hM x]]
  have hy : ∀ r θ, star (increasingEigenvector hM r) ⬝ᵥ collarRowVec w q (shiftSample θ ω) =
      star (increasingEigenvector hM r) ⬝ᵥ ah (increasingEigenvalue hM r + θ) := by
    intro r θ
    have hev : collarMatrix e X (shiftSample θ ω) *ᵥ increasingEigenvector hM r =
        (((increasingEigenvalue hM r + θ : ℝ)) : ℂ) • increasingEigenvector hM r := by
      rw [collarMatrix_shiftSample, add_mulVec, mulVec_increasingEigenvector, smul_mulVec,
        one_mulVec, ← add_smul]
      push_cast
      rfl
    have hA' : ∀ k, ((shiftSample θ ω).1.1 k).IsHermitian := fun k =>
      (hω.2.1 k).add (isHermitian_one.smul (Complex.conj_ofReal θ))
    rw [star_dotProduct_collarRowVec_of_eigen e hX hA' hev z q]
    rfl
  have key := lintegral_cauchy_cfc_eq hM hs hε hah
    (fun θ => collarRowVec w q (shiftSample θ ω)) hy
  simp only [Q, shiftWeight]
  rw [key]
  refine lintegral_congr fun θ => ?_
  rw [collarMatrix_shiftSample]

/-!
## The universal bound
-/

/-- **Pointwise universal bound** at zero energy:
`q*K_XΨ_X(0)K_X*q ≤ π⁻¹ C_{b,w} √W ‖q‖²`, `w = z̄_b + e` (every `W ≥ 1`, every Hermitian `X`). -/
theorem collarWeightedForm_zero_le (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (q : Fin 2 × Fin W → ℂ) :
    collarWeightedForm W b e X (boundaryZ b e) q 0 ≤ Real.pi⁻¹ *
      collarRowConst b (star (boundaryZ b e) + e) * Real.sqrt W * ∑ x, ‖q x‖ ^ 2 := by
  have hC := collarRowConst_nonneg hb0.le (star (boundaryZ b e) + e)
  have hq : 0 ≤ ∑ x, ‖q x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine le_of_forall_lintegral_cauchyKernel_le
    (continuous_collarWeightedForm hW b e hX (boundaryZ b e) q)
    (by have := Real.pi_pos; positivity) fun ε hε => ?_
  rw [lintegral_cauchyKernel_collarWeightedForm hW hb e hX (boundaryZ b e) q hε]
  have hRB := lintegral_im_resolvent_collarRow_le_sqrt hb0 hb hW e hX (z := (⟨0, ε⟩ : ℂ)) hε
    (star (boundaryZ b e) + e) q
  calc ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec (star (boundaryZ b e) + e) q ω) ⬝ᵥ
        ((collarMatrix e X ω - (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec (star (boundaryZ b e) + e) q ω)).im)
        ∂collarLaw W b
      = ENNReal.ofReal Real.pi⁻¹ * ∫⁻ ω, ENNReal.ofReal ((star (collarRowVec
          (star (boundaryZ b e) + e) q ω) ⬝ᵥ ((collarMatrix e X ω - (⟨0, ε⟩ : ℂ) •
            (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
              collarRowVec (star (boundaryZ b e) + e) q ω)).im) ∂collarLaw W b := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
    _ ≤ ENNReal.ofReal Real.pi⁻¹ * ENNReal.ofReal (collarRowConst b (star (boundaryZ b e) + e) *
          Real.sqrt W * ∑ x, ‖q x‖ ^ 2) := by gcongr
    _ = ENNReal.ofReal (Real.pi⁻¹ * collarRowConst b (star (boundaryZ b e) + e) *
          Real.sqrt W * ∑ x, ‖q x‖ ^ 2) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
        ring_nf

/-- Raising the scalar in a Loewner bound `M ⪯ K I`. -/
theorem posSemidef_smul_one_sub_mono' {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    {K K' : ℝ} (h : (((K : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - M).PosSemidef) (hKK : K ≤ K') :
    (((K' : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - M).PosSemidef := by
  have hd : ((((K' - K : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
    PosSemidef.one.smul (Complex.zero_le_real.2 (by linarith))
  have := hd.add h
  convert this using 1
  push_cast
  rw [sub_smul]
  abel

/-- Loewner form: `K S Kᴴ ⪯ C I` from `q*K S K*q ≤ C‖q‖²`, `S` Hermitian. -/
theorem posSemidef_smul_one_sub_conj_of_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℂ} (hS : S.IsHermitian) (K : Matrix ι ι ℂ) {C : ℝ}
    (h : ∀ q : ι → ℂ, quadForm S (Kᴴ *ᵥ q) ≤ C * ∑ a, ‖q a‖ ^ 2) :
    (((C : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - K * S * Kᴴ).PosSemidef := by
  have hK : K * S * Kᴴ = (Kᴴ)ᴴ * S * Kᴴ := by rw [conjTranspose_conjTranspose]
  rw [hK]
  refine posSemidef_of_quadForm_nonneg
    (((isHermitian_one).smul (Complex.conj_ofReal C)).sub (isHermitian_conjTranspose_mul_mul _ hS))
    fun q => ?_
  rw [quadForm_sub, quadForm_real_smul, quadForm_one, quadForm_conjTranspose_mul_mul]
  linarith [h q]

/-- **Global collar density bound** for one `(W, e, X)`: every continuous expected top-top density
`S` of `ℋ_X` has `K_X S(0) K_X* ⪯ π⁻¹ C_{b,w} √W I`. -/
theorem collarDensity_universal (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {S : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hS : Continuous S)
    (hSd : IsCollarTopDensity W b e X S) :
    ((((Real.pi⁻¹ * collarRowConst b (star (boundaryZ b e) + e)) * Real.sqrt W : ℝ) : ℂ) •
        (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      matchedLeadK b e X * S 0 * (matchedLeadK b e X)ᴴ).PosSemidef := by
  rw [eq_collarDensity_of_isCollarTopDensity hW hb e hX hS hSd]
  refine posSemidef_smul_one_sub_conj_of_le (collarDensity_isHermitian hW b e hX 0) _ fun q => ?_
  have h := collarWeightedForm_zero_le hW hb0 hb e hX q
  have hv : collarWeightVec (boundaryZ b e) X q 0 = (matchedLeadK b e X)ᴴ *ᵥ q := by
    simp [collarWeightVec, matchedLeadK]
  rw [collarWeightedForm, hv] at h
  exact h

/-- **Existence clause and universal clause of the collar density bound**, with one constant `C` uniform in `W ≥ 1`, `e ∈ bulkInterval κ` and every
Hermitian `X` (no norm bound): a continuous expected top-top density exists, and every continuous
version `S` satisfies `K_X S(0) K_X* ⪯ C √W I`. `C = π⁻¹ C_{b,5}` (`|z̄_b + e| ≤ 5`). -/
theorem collarDensity_exists_universal {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        (∃ S : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
          Continuous S ∧ IsCollarTopDensity W b e X S) ∧
        ∀ S : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Continuous S →
          IsCollarTopDensity W b e X S →
          (((C * Real.sqrt W : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            matchedLeadK b e X * S 0 * (matchedLeadK b e X)ᴴ).PosSemidef := by
  set w' : ℂ := ((5 : ℝ) : ℂ)
  refine ⟨Real.pi⁻¹ * collarRowConst b w', mul_nonneg (inv_nonneg.2 Real.pi_pos.le)
    (collarRowConst_nonneg hb0.le _), fun W hW e he X hX => ⟨⟨collarDensity W b e X,
      continuous_collarDensity hW b e hX, isCollarTopDensity_collarDensity hW hb e hX⟩,
      fun S hS hSd => ?_⟩⟩
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hz3 := BlockBand.Layers.norm_boundaryZ_le hb0.le (by linarith) he2
  have hw : ‖star (boundaryZ b e) + (e : ℂ)‖ ≤ ‖w'‖ := by
    calc ‖star (boundaryZ b e) + (e : ℂ)‖ ≤ ‖star (boundaryZ b e)‖ + ‖(e : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 + 2 := by
          rw [norm_star, Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add hz3 he2
      _ = ‖w'‖ := by simp only [w']; rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
  refine posSemidef_smul_one_sub_mono' (collarDensity_universal hW hb0 hb e hX hS hSd) ?_
  have := collarRowConst_mono b hw
  have hpi : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  gcongr

/-!
## Reduction of the collar density bound to its regular clause
-/

/-- The regular clause of the collar density bound,
stated for the canonical density (equivalently every continuous version, by
`eq_collarDensity_of_isCollarTopDensity`): for `W ≥ W₀`, `e ∈ bulkInterval κ` and Hermitian `X`
with `d(X) ≤ d_*`, `K_X Ψ_X(0) K_X* ⪯ C I`. -/
def CollarDensityRegularClause (b κ dstar C : ℝ) (W₀ : ℕ) : Prop :=
  ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ,
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      matchedDistance b e X ≤ dstar →
        (((C : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          matchedLeadK b e X * collarDensity W b e X 0 * (matchedLeadK b e X)ᴴ).PosSemidef

/-- **Reduction**: the regular clause (for some constants) implies the full
`CollarDensityStatement`; the existence and universal clauses are `collarDensity_exists_universal`.
No hypothesis is added to the statement and nothing is weakened. -/
theorem collarDensityStatement_of_regular
    (hreg : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ CollarDensityRegularClause b κ dstar C W₀) :
    CollarDensityStatement := by
  intro b hb0 hb κ hκ
  obtain ⟨dstar, Cr, W₀, hd, hR⟩ := hreg b hb0 hb κ hκ
  obtain ⟨Cu, hCu, hU⟩ := collarDensity_exists_universal hb0 hb hκ
  refine ⟨dstar, max Cr Cu, W₀, hd, fun W hW e he X hX => ⟨(hU W hW e he X hX).1,
    fun S hS hSd => ⟨?_, fun hW₀ hdX => ?_⟩⟩⟩
  · exact posSemidef_smul_one_sub_mono' ((hU W hW e he X hX).2 S hS hSd)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
  · rw [eq_collarDensity_of_isCollarTopDensity hW hb e hX hS hSd]
    exact posSemidef_smul_one_sub_mono' (hR W hW hW₀ e he X hX hdX) (le_max_left _ _)

end BlockBand.Critical.Collar.Density
