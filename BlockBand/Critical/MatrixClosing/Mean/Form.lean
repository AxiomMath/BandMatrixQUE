module

public import BlockBand.Critical.MatrixClosing.Mean.Spectral
public import BlockBand.Critical.MatrixClosing.Clauses

/-!
# Matrix closing, mean clause: `Im F_W(iY)` in the spectral variables

Deterministic (every collar sample); no hypothesis is used. The mean of `Im F_W(iY)` is obtained by integrating the
shifted weighted density against the Poisson kernel of height `Y/(Wρ(E))`.

* `matrixImaginaryPart_eval_ofAtoms`: `Im(C₀ + Σ_ℓ(x_ℓ - z)⁻¹R_ℓ) = Σ_ℓ (Im z/|x_ℓ - z|²)R_ℓ`.
* `frameFin_eq`: `J*KD⁻¹B = -J*KT` (port index on `Fin W`).
* **`re_quad_imPart_collarFunction`**: for the collar function `F_W`
  (`collarFunction`), `Re v*Im F_W(iY)v = (π/η)Σ_ℓ P_ν(λ_ℓ(Q))|(T*K*Jv)*u_ℓ(Q)|²`,
  `ν = Y/(Wρ(e))` (`P_ν` the Cauchy kernel).
* `re_quad_imPart_eq_toReal`, `re_quad_imPart_nonneg`, `ofReal_re_quad_imPart`: the same through
  `Mean.spectralSum`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Coarea.FreshPalm BlockBand.Critical.Herglotz
open CoareaNative.BlockBand (matrixImaginaryPart)
open scoped ENNReal NNReal ComplexOrder

variable {W : ℕ}

theorem matrixImaginaryPart_eval_ofAtoms {r n : ℕ} (C0 : Matrix (Fin r) (Fin r) ℂ)
    (hC0 : C0.IsHermitian) (pts : Fin n → ℝ) (res : Fin n → Matrix (Fin r) (Fin r) ℂ)
    (hres : ∀ ℓ, (res ℓ).PosSemidef) (z : ℂ) :
    matrixImaginaryPart ((ofAtoms C0 hC0 pts res hres).eval z) =
      ∑ ℓ, ((z.im / Complex.normSq ((pts ℓ : ℂ) - z) : ℝ) : ℂ) • res ℓ := by
  rw [eval_ofAtoms]
  unfold matrixImaginaryPart
  rw [Matrix.conjTranspose_add, hC0.eq, Matrix.conjTranspose_sum,
    add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Matrix.conjTranspose_smul, (hres ℓ).isHermitian.eq, ← sub_smul, smul_smul]
  congr 1
  rw [← ScalarAtomicHerglotz.im_inv_ofReal_sub]
  generalize ((pts ℓ : ℂ) - z)⁻¹ = w
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

theorem frameFin_eq {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) :
    frameFin b e X J ω = -(Jᴴ * matchedLeadK b e X * Collar.Density.collarTW e X ω.1) := by
  ext i j
  simp only [frameFin, collarFrame, Collar.Density.collarTW, Collar.Density.collarT, topBlock,
    Collar.Density.collarTopBlock, submatrix_apply, id, Matrix.neg_apply, Matrix.mul_assoc,
    Matrix.mul_apply, Finset.sum_neg_distrib, mul_neg, neg_neg]
  rfl

/-- **`Im F_W(iY)` in the spectral variables.** For `η > 0`, `Wρ(e) > 0`, `Y > 0`:
`Re v*Im F_W(iY)v = (π/η) Σ_ℓ P_ν(λ_ℓ(Q)) |(T*K*Jv)*u_ℓ(Q)|²`, `ν = Y/(Wρ(e))`. -/
theorem re_quad_imPart_collarFunction {r : ℕ} {b e : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hc : 0 < poleScale W e) {Y : ℝ} (hY : 0 < Y) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) (v : Fin r → ℂ) :
    (star v ⬝ᵥ (matrixImaginaryPart ((collarFunction b e X J ω).eval ((Y : ℂ) * Complex.I)) *ᵥ
        v)).re =
      Real.pi / (boundaryZ b e).im * ∑ ℓ, cauchyKernel (Y / poleScale W e)
        (freshEigenvalue (portSchurFin e X ω) ℓ) *
          ‖star ((Collar.Density.collarTW e X ω.1)ᴴ *ᵥ ((matchedLeadK b e X)ᴴ *ᵥ (J *ᵥ v))) ⬝ᵥ
            freshEigenvector (portSchurFin e X ω) ℓ‖ ^ 2 := by
  unfold collarFunction
  rw [matrixImaginaryPart_eval_ofAtoms]
  change quadForm _ v = _
  rw [Collar.Density.quadForm_sum_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hR : quadForm (collarResidue b e X J ω ℓ) v = residueWeight W b e *
      ‖star ((Collar.Density.collarTW e X ω.1)ᴴ *ᵥ ((matchedLeadK b e X)ᴴ *ᵥ (J *ᵥ v))) ⬝ᵥ
        freshEigenvector (portSchurFin e X ω) ℓ‖ ^ 2 := by
    unfold collarResidue
    have h1 : quadForm (((residueWeight W b e : ℝ) : ℂ) • (frameFin b e X J ω *
        freshProjector (portSchurFin e X ω) ℓ * (frameFin b e X J ω)ᴴ)) v =
        residueWeight W b e * quadForm (frameFin b e X J ω *
          freshProjector (portSchurFin e X ω) ℓ * (frameFin b e X J ω)ᴴ) v := by
      unfold quadForm
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    rw [h1]
    congr 1
    have h2 := quadForm_conjTranspose_mul_mul (frameFin b e X J ω)ᴴ
      (freshProjector (portSchurFin e X ω) ℓ) v
    rw [conjTranspose_conjTranspose] at h2
    rw [h2, Collar.Density.quadForm_freshProjector, frameFin_eq, conjTranspose_neg,
      neg_mulVec, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [← mulVec_mulVec, star_neg, neg_dotProduct, norm_neg]
  rw [hR]
  set p := poleScale W e
  set l := freshEigenvalue (portSchurFin e X ω) ℓ
  have hrw : residueWeight W b e = p / (boundaryZ b e).im :=
    max_eq_left (div_pos hc hη).le
  have hz : ((Y : ℂ) * Complex.I).im = Y := by simp
  have hn : Complex.normSq (((p * l : ℝ) : ℂ) - (Y : ℂ) * Complex.I) = (p * l) ^ 2 + Y ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hrw, hz, hn, cauchyKernel]
  have hpi := Real.pi_pos
  field_simp

theorem re_quad_imPart_eq_toReal {r : ℕ} {b e : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hc : 0 < poleScale W e) {Y : ℝ} (hY : 0 < Y) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) (v : Fin r → ℂ) :
    (star v ⬝ᵥ (matrixImaginaryPart ((collarFunction b e X J ω).eval ((Y : ℂ) * Complex.I)) *ᵥ
        v)).re = Real.pi / (boundaryZ b e).im *
      (spectralSum (cauchyKernel (Y / poleScale W e)) e X
        ((matchedLeadK b e X)ᴴ *ᵥ (J *ᵥ v)) ω).toReal := by
  rw [re_quad_imPart_collarFunction hη hc hY, spectralSum,
    ENNReal.toReal_sum fun ℓ _ => ENNReal.ofReal_ne_top]
  congr 1
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (cauchyKernel_nonneg (div_pos hY hc).le _)
    (sq_nonneg _))]

theorem re_quad_imPart_nonneg {r : ℕ} {b e : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hc : 0 < poleScale W e) {Y : ℝ} (hY : 0 < Y) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) (v : Fin r → ℂ) :
    0 ≤ (star v ⬝ᵥ (matrixImaginaryPart ((collarFunction b e X J ω).eval ((Y : ℂ) * Complex.I)) *ᵥ
        v)).re := by
  rw [re_quad_imPart_eq_toReal hη hc hY]
  exact mul_nonneg (div_pos Real.pi_pos hη).le ENNReal.toReal_nonneg

theorem ofReal_re_quad_imPart {r : ℕ} {b e : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hc : 0 < poleScale W e) {Y : ℝ} (hY : 0 < Y) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) (v : Fin r → ℂ) :
    ENNReal.ofReal (star v ⬝ᵥ (matrixImaginaryPart ((collarFunction b e X J ω).eval
        ((Y : ℂ) * Complex.I)) *ᵥ v)).re =
      ENNReal.ofReal (Real.pi / (boundaryZ b e).im) *
        spectralSum (cauchyKernel (Y / poleScale W e)) e X
          ((matchedLeadK b e X)ᴴ *ᵥ (J *ᵥ v)) ω := by
  rw [re_quad_imPart_eq_toReal hη hc hY, ENNReal.ofReal_mul (div_pos Real.pi_pos hη).le,
    ENNReal.ofReal_toReal]
  exact ENNReal.sum_ne_top.2 fun ℓ _ => ENNReal.ofReal_ne_top

end BlockBand.Critical.MatrixClosing.Mean
