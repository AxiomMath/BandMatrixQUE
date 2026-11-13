module

public import BlockBand.Critical.Collar.Density.UniversalBound

/-!
# Energy shifts and weight comparison for the canonical collar density

*Law.* `collarLaw W b`, `W ≥ 1`, `b < 1/2`; deterministic Hermitian `X`.

* `collarDensity_energy_shift`: `Ψ^{(e)}_X(x) = Ψ^{(e+x)}_X(0)` (the energy `e + x` collar).
* `collarDensity_posSemidef`: `Ψ_X(x) ⪰ 0`.
* `quadForm_add_le_two`: `Q(u+v) ≤ 2Q(u) + 2Q(v)` for PSD forms.
* `norm_sq_inv_conjTranspose_mulVec_le`: `‖(z - X)^{-*} q‖² ≤ ‖q‖²/(Im z)²`, `X` Hermitian.
* `quadForm_shifted_weight_le`: if `K Ψ K* ⪯ c I`, `K = z - X`, then
  `q*(K + δ)Ψ(K + δ)*q ≤ 2c(1 + |δ|²/(Im z)²)‖q‖²` for every scalar `δ` (weight comparison on an
  energy window, with the bounded scalar `δ = z_b(e) - x - z_b(e+x)`).
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

theorem collarMatrix_add_energy (e x : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : CollarSample W) :
    collarMatrix (e + x) X ω = collarMatrix e X ω +
      ((-x : ℝ) : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) := by
  unfold collarMatrix
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  congr 1
  · push_cast; rw [add_smul, neg_smul]; abel
  · simp
  · simp
  · push_cast; rw [add_smul, neg_smul]; abel

/-- **Energy shift**: `Ψ^{(e)}_X(x) = Ψ^{(e+x)}_X(0)`. -/
theorem collarDensity_energy_shift (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (x : ℝ) :
    collarDensity W b e X x = collarDensity W b (e + x) X 0 := by
  ext i j
  simp only [collarDensity, Matrix.of_apply]
  refine integral_congr_ae ?_
  filter_upwards [ae_collarBase_isHermitian hW b e hX] with ω hω
  have hf : (fun l => shiftWeight W b (0 - (l + -x))) = fun l => shiftWeight W b (x - l) := by
    funext l; congr 1; ring
  rw [collarMatrix_add_energy, cfc_add_smul_one hω.1, hf]

theorem re_integral_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : (∫ ω, f ω ∂μ).re = ∫ ω, (f ω).re ∂μ :=
  (integral_re hf).symm

/-- `Ψ_X(x) ⪰ 0`. -/
theorem collarDensity_posSemidef (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (x : ℝ) :
    (collarDensity W b e X x).PosSemidef := by
  refine posSemidef_of_quadForm_nonneg (collarDensity_isHermitian hW b e hX x) fun v => ?_
  have hHerm := ae_collarBase_isHermitian hW b e hX
  have hcint : Integrable (fun ω => star (Sum.elim v (0 : PortSite W .common → ℂ)) ⬝ᵥ
      (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω) *ᵥ Sum.elim v 0))
      (collarBase W b) :=
    integrable_star_dotProduct_mulVec (fun i j => integrable_cfc_shiftWeight hW b e hX x i j) _
  have h1 := star_dotProduct_of_integral_mulVec' (μ := collarBase W b)
    (f := fun ω => (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)).toBlocks₁₁)
    (fun i j => integrable_cfc_shiftWeight hW b e hX x (Sum.inl i) (Sum.inl j)) v
  have h2 : collarDensity W b e X x = Matrix.of fun i j => ∫ ω,
      (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)).toBlocks₁₁ i j
        ∂collarBase W b := rfl
  rw [quadForm, h2, h1, integral_congr_ae (Eventually.of_forall fun ω =>
    star_dotProduct_toBlocks11_mulVec
      (cfc (fun l => shiftWeight W b (x - l)) (collarMatrix e X ω)) v),
    re_integral_eq hcint]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hHerm] with ω hω
  rw [cfc_eq_specSum hω.1]
  have := re_star_dotProduct_specSum_eq hω.1 (fun l => shiftWeight W b (x - l)) (Sum.elim v 0)
  rw [this]
  exact Finset.sum_nonneg fun r _ => mul_nonneg (shiftWeight_nonneg _ _ _) (sq_nonneg _)

/-!
## Quadratic-form comparisons
-/

theorem quadForm_add_le_two {ι : Type*} [Fintype ι] {S : Matrix ι ι ℂ} (hS : S.PosSemidef)
    (u v : ι → ℂ) : quadForm S (u + v) ≤ 2 * quadForm S u + 2 * quadForm S v := by
  have h := quadForm_nonneg_of_posSemidef hS (u - v)
  have hpar : quadForm S (u + v) + quadForm S (u - v) = 2 * quadForm S u + 2 * quadForm S v := by
    simp only [quadForm, mulVec_add, mulVec_sub, star_add, star_sub, dotProduct_add,
      dotProduct_sub, add_dotProduct, sub_dotProduct, Complex.add_re, Complex.sub_re]
    ring
  linarith

theorem quadForm_smul {ι : Type*} [Fintype ι] (S : Matrix ι ι ℂ) (c : ℂ) (v : ι → ℂ) :
    quadForm S (c • v) = ‖c‖ ^ 2 * quadForm S v := by
  simp only [quadForm, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem sum_norm_sq_eq_sum_eigen {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (v : ι → ℂ) :
    ∑ a, ‖v a‖ ^ 2 = ∑ r, ‖star (increasingEigenvector hM r) ⬝ᵥ v‖ ^ 2 := by
  have h := dotProduct_specSum_mulVec hM (fun _ => 1) v
  rw [specSum_one, one_mulVec] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simp only [one_mul, Complex.ofReal_re] at h2
  rw [← h2]
  exact (BlockBand.Wegner.re_star_dotProduct_self v).symm

/-- `‖(z - X)^{-*} q‖² ≤ ‖q‖²/(Im z)²` for Hermitian `X`, `Im z > 0`. -/
theorem isUnit_det_sub_star_smul_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (X - (star z) • (1 : Matrix ι ι ℂ)).det := by
  have h := BlockBand.Critical.Collar.Density.isUnit_det_sub_smul_one' hX hz
  have hc : (X - z • (1 : Matrix ι ι ℂ))ᴴ = X - (star z) • 1 := by
    rw [conjTranspose_sub, hX.eq, conjTranspose_smul, conjTranspose_one]
  rw [← hc, det_conjTranspose]
  exact h.star

theorem inv_neg_of_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (h : IsUnit M.det) : (-M)⁻¹ = -M⁻¹ :=
  inv_eq_left_inv (by rw [neg_mul_neg, nonsing_inv_mul _ h])

theorem norm_sq_inv_conjTranspose_mulVec_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) (q : ι → ℂ) :
    ∑ a, ‖((z • (1 : Matrix ι ι ℂ) - X)ᴴ⁻¹ *ᵥ q) a‖ ^ 2 ≤ (z.im ^ 2)⁻¹ * ∑ a, ‖q a‖ ^ 2 := by
  have hz' : (star z).im ≠ 0 := by simp [hz.ne']
  have hK : (z • (1 : Matrix ι ι ℂ) - X)ᴴ⁻¹ = -(X - star z • 1)⁻¹ := by
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq,
      show star z • (1 : Matrix ι ι ℂ) - X = -(X - star z • 1) by rw [neg_sub],
      inv_neg_of_isUnit_det (isUnit_det_sub_star_smul_one hX hz)]
  have hn : ∀ v : ι → ℂ, ∑ a, ‖(-v) a‖ ^ 2 = ∑ a, ‖v a‖ ^ 2 := fun v => by
    simp only [Pi.neg_apply, norm_neg]
  rw [hK, neg_mulVec, hn, inv_sub_eq_specSum hX hz', sum_norm_sq_eq_sum_eigen hX,
    sum_norm_sq_eq_sum_eigen hX q, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [specSum_mulVec]
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, star_dotProduct_increasingEigenvector,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, norm_mul]
  rw [mul_pow]
  gcongr
  rw [norm_inv, inv_pow]
  refine inv_anti₀ (by positivity) ?_
  have h := Complex.abs_im_le_norm ((increasingEigenvalue hX r : ℂ) - star z)
  have him : ((increasingEigenvalue hX r : ℂ) - star z).im = z.im := by simp
  rw [him, abs_of_pos hz] at h
  exact pow_le_pow_left₀ hz.le h 2

/-- **Weight comparison on an energy window.** If `K Ψ K* ⪯ c I` with `K = z - X`, `X` Hermitian,
`Im z > 0`, `Ψ ⪰ 0`, then for every scalar `δ`:
`q*(K + δ)Ψ(K + δ)*q ≤ 2c(1 + |δ|²/(Im z)²)‖q‖²`. -/
theorem quadForm_shifted_weight_le {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) {S : Matrix ι ι ℂ} (hS : S.PosSemidef) {c : ℝ}
    (hc : (((c : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - (z • 1 - X) * S * (z • 1 - X)ᴴ).PosSemidef)
    (δ : ℂ) (q : ι → ℂ) :
    quadForm S ((z • (1 : Matrix ι ι ℂ) - X + δ • 1)ᴴ *ᵥ q) ≤
      2 * c * (1 + ‖δ‖ ^ 2 / z.im ^ 2) * ∑ a, ‖q a‖ ^ 2 := by
  set K := z • (1 : Matrix ι ι ℂ) - X
  have hKq : ∀ v : ι → ℂ, quadForm S (Kᴴ *ᵥ v) ≤ c * ∑ a, ‖v a‖ ^ 2 := by
    intro v
    have h := quadForm_nonneg_of_posSemidef hc v
    rw [quadForm_sub, quadForm_real_smul, quadForm_one,
      show K * S * Kᴴ = (Kᴴ)ᴴ * S * Kᴴ by rw [conjTranspose_conjTranspose],
      quadForm_conjTranspose_mul_mul] at h
    linarith
  by_cases hq : ∑ a, ‖q a‖ ^ 2 = 0
  · have hq0 : q = 0 := by
      funext a
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖q a‖)).1 hq a
        (Finset.mem_univ a)
      simpa using this
    simp [hq0, quadForm]
  have hqpos : 0 < ∑ a, ‖q a‖ ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hq)
  have hc0 : 0 ≤ c := by
    have h1 := hKq q
    have h2 := quadForm_nonneg_of_posSemidef hS (Kᴴ *ᵥ q)
    by_contra hneg
    push Not at hneg
    nlinarith
  have hzu : (z • (1 : Matrix ι ι ℂ) - X)ᴴ = -(X - (star z) • 1) := by
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq, neg_sub]
  have hdet : IsUnit (Kᴴ).det := by
    have h := isUnit_det_sub_star_smul_one hX hz
    have hu : IsUnit (X - (star z) • (1 : Matrix ι ι ℂ)) := (Matrix.isUnit_iff_isUnit_det _).2 h
    exact (Matrix.isUnit_iff_isUnit_det _).1 (by rw [hzu]; exact hu.neg)
  have hinvq : Kᴴ *ᵥ (Kᴴ⁻¹ *ᵥ q) = q := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hQq : quadForm S q ≤ c * ((z.im ^ 2)⁻¹ * ∑ a, ‖q a‖ ^ 2) := by
    calc quadForm S q = quadForm S (Kᴴ *ᵥ (Kᴴ⁻¹ *ᵥ q)) := by rw [hinvq]
      _ ≤ c * ∑ a, ‖(Kᴴ⁻¹ *ᵥ q) a‖ ^ 2 := hKq _
      _ ≤ c * ((z.im ^ 2)⁻¹ * ∑ a, ‖q a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_sq_inv_conjTranspose_mulVec_le hX hz q) hc0
  have hsplit : (K + δ • (1 : Matrix ι ι ℂ))ᴴ *ᵥ q = Kᴴ *ᵥ q + (star δ) • q := by
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one, add_mulVec, smul_mulVec,
      one_mulVec]
  rw [hsplit]
  have h1 := quadForm_add_le_two hS (Kᴴ *ᵥ q) ((star δ) • q)
  rw [quadForm_smul, norm_star] at h1
  have h2 := hKq q
  have hzi : 0 < z.im ^ 2 := by positivity
  calc quadForm S (Kᴴ *ᵥ q + star δ • q)
      ≤ 2 * quadForm S (Kᴴ *ᵥ q) + 2 * (‖δ‖ ^ 2 * quadForm S q) := h1
    _ ≤ 2 * (c * ∑ a, ‖q a‖ ^ 2) + 2 * (‖δ‖ ^ 2 * (c * ((z.im ^ 2)⁻¹ * ∑ a, ‖q a‖ ^ 2))) := by
        gcongr
    _ = 2 * c * (1 + ‖δ‖ ^ 2 / z.im ^ 2) * ∑ a, ‖q a‖ ^ 2 := by
        field_simp

end BlockBand.Critical.Collar.Density
