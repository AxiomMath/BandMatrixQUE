module

public import BlockBand.Endpoints.Response.PassDerivativePort
public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The physical two-port path with interior absorber

This file defines the objects of the pass-derivative lemma and relates them to the abstract
pencil of `pencilScattering`.

* `portDefect S i = I - S_ii* S_ii` (`T_L`, `T_R`: port `0` is the near port, `1` the far
  port; the sum `F_L + F_R` is symmetric);
* `portRatioSum b E x y W n q κ ω = F_{x,y}(T_0(κ)) + F_{x,y}(T_1(κ))`, i.e. `F_L + F_R` with
  `F_{x,y}(T) = det(I - yT)/det(I + xT)` (`ratioDet`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator ComplexConjugate

/-!
### Definitions
-/

/-- The full path matrix with interior absorber `iκ Q_q/W²`:
`[[H_path - E + i diag(κ q/W²), C], [C*, z_∂]]`. -/
def absorbedFullMatrix (b E : ℝ) (W n : ℕ) (κ : ℝ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    Matrix (FullSite W n) (FullSite W n) ℂ :=
  Matrix.fromBlocks
    (pathMatrix (pathAt W n ω) - (E : ℂ) • 1 +
      absorptionDiag W (layerAbsorption W (fun t => κ * q t) n))
    (pathPortCoupling (pathAt W n ω)) (pathPortCoupling (pathAt W n ω))ᴴ (boundaryZ b E • 1)

/-- The absorbed scattering matrix `𝕊_κ = I - 2iη V*G_κV`. -/
def absorbedScattering (b E : ℝ) (W n : ℕ) (κ : ℝ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - ((2 * etaZ b E : ℝ) * Complex.I) • ((absorbedFullMatrix b E W n κ q ω)⁻¹).toBlocks₂₂

/-- The reflection defect `T_i = I - S_ii* S_ii` of port `i`. -/
def portDefect {W : ℕ} (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    Matrix (Fin W) (Fin W) ℂ :=
  1 - (portBlock S i i)ᴴ * portBlock S i i

/-- `F_L(κ) + F_R(κ)`, with `F_{x,y}(T) = Re(det(I - yT)/det(I + xT))` (the determinant ratio is
real on `0 ⪯ T ⪯ I`). -/
def portRatioSum (b E x y : ℝ) (W n : ℕ) (q : ℝ → ℝ) (κ : ℝ) (ω : GrowthPath W) : ℝ :=
  ratioDet x y (portDefect (absorbedScattering b E W n κ q ω) 0) +
    ratioDet x y (portDefect (absorbedScattering b E W n κ q ω) 1)

/-- The lead inclusion `V : FullSite → ports` (`V*MV` is the port block). -/
def leadInclusion (W n : ℕ) : Matrix (FullSite W n) (Fin 2 × Fin W) ℂ :=
  Matrix.of fun x a => Sum.elim (fun _ => (0 : ℂ)) (fun a' => if a' = a then 1 else 0) x

/-- The inclusion of the channels of port `i`. -/
def portInclusion (W : ℕ) (i : Fin 2) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  Matrix.of fun a y => if a.1 = i ∧ a.2 = y then 1 else 0

/-- The source root `R = Q_q^{1/2}/W` (diagonal, interior sites only). -/
def sourceRoot (W n : ℕ) (q : ℝ → ℝ) : Matrix (FullSite W n) (FullSite W n) ℂ :=
  Matrix.diagonal (Sum.elim
    (fun s => ((Real.sqrt (q (((n - s.1.val : ℕ) : ℝ) / W)) / W : ℝ) : ℂ)) fun _ => 0)

/-!
### The bridge to the abstract pencil
-/

variable {W n : ℕ}

theorem absorbedFullMatrix_eq {b E κ : ℝ} {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (ω : GrowthPath W) :
    absorbedFullMatrix b E W n κ q ω =
      absorbedPencil (fullPathMatrix b E W n ω) (sourceRoot W n q) κ := by
  have hRR : (sourceRoot W n q)ᴴ * sourceRoot W n q = Matrix.diagonal (Sum.elim
      (fun s => ((q (((n - s.1.val : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ)) fun _ => 0) := by
    rw [sourceRoot, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext x
    rcases x with s | a
    · simp only [Pi.star_apply, Sum.elim_inl]
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      rw [div_mul_div_comm, Real.mul_self_sqrt (hq _), sq]
    · simp
  ext x y
  rcases x with s | a <;> rcases y with s' | a' <;>
    simp [absorbedFullMatrix, absorbedPencil, fullPathMatrix, hRR, absorptionDiag,
      layerAbsorption, diagonal_apply]
  split_ifs <;> ring

theorem leadInclusion_conjTranspose_mul_mul (G : Matrix (FullSite W n) (FullSite W n) ℂ) :
    (leadInclusion W n)ᴴ * G * leadInclusion W n = G.toBlocks₂₂ := by
  ext a b
  simp [leadInclusion, mul_apply, Fintype.sum_sum_type, toBlocks₂₂]

theorem leadInclusion_mul_conjTranspose :
    leadInclusion W n * (leadInclusion W n)ᴴ = Matrix.fromBlocks 0 0 0 1 := by
  ext x y
  rcases x with s | a <;> rcases y with s' | a' <;>
    simp [leadInclusion, mul_apply, one_apply]

theorem absorbedScattering_eq {b E κ : ℝ} {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (ω : GrowthPath W) :
    absorbedScattering b E W n κ q ω = pencilScattering (etaZ b E) (leadInclusion W n)
      (absorbedPencil (fullPathMatrix b E W n ω) (sourceRoot W n q) κ) := by
  rw [absorbedScattering, pencilScattering, leadInclusion_conjTranspose_mul_mul,
    absorbedFullMatrix_eq hq]

/-- At zero source the absorbed scattering matrix is the `scatteringMatrix`. -/
theorem absorbedScattering_zero (b E : ℝ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    absorbedScattering b E W n 0 q ω = scatteringMatrix b E W n ω := by
  have : absorbedFullMatrix b E W n 0 q ω = fullPathMatrix b E W n ω := by
    simp [absorbedFullMatrix, fullPathMatrix, absorptionDiag, layerAbsorption]
  rw [absorbedScattering, this]
  rfl

theorem portBlock_eq_compression (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    portBlock S i i = (portInclusion W i)ᴴ * S * portInclusion W i := by
  ext x y
  simp only [portBlock, of_apply, mul_apply, conjTranspose_apply, portInclusion]
  fin_cases i <;>
    simp [Fintype.sum_prod_type, Finset.sum_ite_eq', ite_and, apply_ite (starRingEnd ℂ)]

theorem portDefect_eq (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    portDefect S i = portDefectOf S (portInclusion W i) := by
  rw [portDefect, portDefectOf, portBlock_eq_compression]

theorem portInclusion_conjTranspose_mul (i : Fin 2) :
    (portInclusion W i)ᴴ * portInclusion W i = 1 := by
  ext x y
  simp only [mul_apply, conjTranspose_apply, portInclusion, of_apply, one_apply]
  simp [Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq']
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

theorem portInclusion_norm_le (i : Fin 2) : ‖portInclusion W i‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (portInclusion W i)
  rw [portInclusion_conjTranspose_mul] at h
  have h1 := l2_opNorm_one_le (n := Fin W)
  have h0 := norm_nonneg (portInclusion W i)
  nlinarith

/-- Hermitian GUE blocks make the path matrix Hermitian. -/
theorem pathMatrix_isHermitian {ω : PathSample W n} (h : ∀ i, (ω.1 i).IsHermitian) :
    (pathMatrix ω).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, pathMatrix]
  by_cases hxy : x.1 = y.1
  · have hyx : y.1 = x.1 := hxy.symm
    rw [ite_eq_left hyx, ite_eq_left hxy]
    have := congrFun (congrFun (h y.1).eq x.2) y.2
    rw [conjTranspose_apply] at this
    exact this.trans (by rw [hxy])
  · have hyx : ¬ y.1 = x.1 := Ne.symm hxy
    rw [ite_eq_right hyx, ite_eq_right hxy]
    by_cases h1 : y.1.val + 1 = x.1.val
    · have h2 : ¬ x.1.val + 1 = y.1.val := by omega
      rw [dite_eq_left h1, dite_eq_right h2, dite_eq_left h1]
    · rw [dite_eq_right h1]
      by_cases h2 : x.1.val + 1 = y.1.val
      · rw [dite_eq_left h2, dite_eq_left h2, star_star]
      · rw [dite_eq_right h2, dite_eq_right h1, dite_eq_right h2, star_zero]

theorem etaZ_nonneg {b E : ℝ} (hb : b ≤ 1) (hE1 : -2 < E) (hE2 : E < 2) : 0 ≤ etaZ b E := by
  have h4 : 0 ≤ 4 - E ^ 2 := by nlinarith
  have hs := Real.sq_sqrt h4
  have hn : Complex.normSq (matchedA E) = 1 := by
    rw [Complex.normSq_apply]
    simp only [matchedA]
    nlinarith
  simp only [etaZ, boundaryZ, Complex.add_im, Complex.inv_im, hn,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  simp only [matchedA]
  have := Real.sqrt_nonneg (4 - E ^ 2)
  nlinarith

/-- **Ward identity for the full path matrix**: with Hermitian GUE blocks,
`𝓜 - 𝓜* = 2iη VV*`.
-/
theorem fullPathMatrix_ward {b E : ℝ} {ω : GrowthPath W} (h : ∀ k, (ω.1 k).IsHermitian) :
    fullPathMatrix b E W n ω - (fullPathMatrix b E W n ω)ᴴ =
      (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • (leadInclusion W n * (leadInclusion W n)ᴴ) := by
  have hH : (pathMatrix (pathAt W n ω)).IsHermitian :=
    pathMatrix_isHermitian fun i => h _
  rw [leadInclusion_mul_conjTranspose, fullPathMatrix, fromBlocks_conjTranspose,
    conjTranspose_conjTranspose, fromBlocks_smul]
  have h1 : (pathMatrix (pathAt W n ω) - (E : ℂ) • 1)ᴴ =
      pathMatrix (pathAt W n ω) - (E : ℂ) • 1 := by
    rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  rw [h1]
  ext x y
  rcases x with s | a <;> rcases y with s' | a' <;>
    simp [fromBlocks, conjTranspose_apply, one_apply]
  split_ifs
  · rw [← Complex.conj_ofReal]
    rw [Complex.ext_iff]
    simp [etaZ]
    ring
  · simp

/-- `Tr B_q ≤ (Q/W²) Tr 𝒰*𝒰` for `0 ≤ q ≤ Q` (`𝒰 = G_{int,ports}`). -/
theorem pencilSourceGram_trace_le {q : ℝ → ℝ} {Q : ℝ} (hq : ∀ t, 0 ≤ q t) (hQ : ∀ t, q t ≤ Q)
    (M : Matrix (FullSite W n) (FullSite W n) ℂ) :
    (pencilSourceGram M (sourceRoot W n q) (leadInclusion W n)).trace.re ≤
      Q / (W : ℝ) ^ 2 * ((M⁻¹).toBlocks₁₂ᴴ * (M⁻¹).toBlocks₁₂).trace.re := by
  rw [pencilSourceGram, trace_conjTranspose_mul_self_re_eq_hsSq,
    trace_conjTranspose_mul_self_re_eq_hsSq]
  have hentry : ∀ x a, (sourceFrame M (sourceRoot W n q) (leadInclusion W n)) x a =
      Sum.elim (fun s => ((Real.sqrt (q (((n - s.1.val : ℕ) : ℝ) / W)) / W : ℝ) : ℂ))
        (fun _ => 0) x * M⁻¹ x (Sum.inr a) := by
    intro x a
    simp [sourceFrame, sourceRoot, leadInclusion, mul_apply, Fintype.sum_sum_type,
      diagonal_apply]
  unfold hsSq
  rw [Fintype.sum_sum_type, Finset.mul_sum]
  simp only [hentry, Sum.elim_inl, Sum.elim_inr, zero_mul, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (hq _)]
  have : (M⁻¹).toBlocks₁₂ s a = M⁻¹ (Sum.inl s) (Sum.inr a) := rfl
  rw [this]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hQ _) (sq_nonneg _))
    (sq_nonneg _)

/-- `‖K_q/W²‖ = ‖R G₀ R*‖ ≤ (Q/W²) ‖G₀‖` for `0 ≤ q ≤ Q`. -/
theorem sourceKernel_norm_le {q : ℝ → ℝ} {Q : ℝ} (hq : ∀ t, 0 ≤ q t) (hQ : ∀ t, q t ≤ Q)
    (M : Matrix (FullSite W n) (FullSite W n) ℂ) :
    ‖sourceKernel M (sourceRoot W n q)‖ ≤ Q / (W : ℝ) ^ 2 * ‖M⁻¹‖ := by
  have hQ0 : 0 ≤ Q := (hq 0).trans (hQ 0)
  have hR : ‖sourceRoot W n q‖ ≤ Real.sqrt Q / W := by
    rw [sourceRoot, l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x => ?_
    rcases x with s | a
    · simp only [Sum.elim_inl, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (hQ _)) (Nat.cast_nonneg W)
    · simp only [Sum.elim_inr, norm_zero]; positivity
  have hR2 : ‖sourceRoot W n q‖ ^ 2 ≤ Q / (W : ℝ) ^ 2 := by
    calc ‖sourceRoot W n q‖ ^ 2 ≤ (Real.sqrt Q / W) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hR 2
      _ = Q / (W : ℝ) ^ 2 := by rw [div_pow, Real.sq_sqrt hQ0]
  calc ‖sourceKernel M (sourceRoot W n q)‖
      ≤ ‖sourceRoot W n q * M⁻¹‖ * ‖(sourceRoot W n q)ᴴ‖ := l2_opNorm_mul _ _
    _ ≤ ‖sourceRoot W n q‖ * ‖M⁻¹‖ * ‖sourceRoot W n q‖ := by
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖sourceRoot W n q‖ ^ 2 * ‖M⁻¹‖ := by ring
    _ ≤ Q / (W : ℝ) ^ 2 * ‖M⁻¹‖ := mul_le_mul_of_nonneg_right hR2 (norm_nonneg _)

end BlockBand.Endpoints
