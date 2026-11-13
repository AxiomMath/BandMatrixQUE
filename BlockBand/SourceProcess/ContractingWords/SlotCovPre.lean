module

public import BlockBand.SourceProcess.ContractingWords.SlotPins
public import BlockBand.SourceProcess.FullSourceCovariance.CrossedSameHolds

/-!
# Tools for the slot covariances

Tools for the slot covariance bounds.

* `fscK`, `fscG`, `fscH`: the four tensors of the full-source covariance lemma:
  `(D₀/2W)(P⊗P' + P'⊗P) - σ₋/(4η²W) P𝕊⊗P𝕊 - σ̄₋/(4η²W) 𝕊*P⊗𝕊*P` (`fsc_eq`);
* `bilinear_sandwich`, `crossedTensor_sandwich`: moving Hermitian sandwiches into the vectors;
* `norm_integral_mul_le_amgm`: `|E fg| ≤ (a E|f|² + a⁻¹ E|g|²)/2`, `a > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open scoped ENNReal ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The coefficients of the four tensors. -/
def fscK (b E : ℝ) (s : ℂ) (W : ℕ) : Fin 4 → ℂ :=
  ![(((transportD0 b E / (2 * W) : ℝ)) : ℂ), (((transportD0 b E / (2 * W) : ℝ)) : ℂ),
    -(sigmaMinus b E s / ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ)),
    -(conj (sigmaMinus b E s) / ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ))]

/-- The left matrices of the four tensors. -/
def fscG (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Fin 4 → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ![nearProjection W, (twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX,
    nearProjection W * twoPortScattering b E XX, (twoPortScattering b E XX)ᴴ * nearProjection W]

/-- The right matrices of the four tensors. -/
def fscH (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Fin 4 → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ![(twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX, nearProjection W,
    nearProjection W * twoPortScattering b E XX, (twoPortScattering b E XX)ᴴ * nearProjection W]

theorem fsc_eq (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ) :
    (((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
        (crossedTensor v₁ v₂ v₃ v₄ (nearProjection W)
            ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) +
          crossedTensor v₁ v₂ v₃ v₄
            ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX)
            (nearProjection W)) -
        sigmaMinus b E s / ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ) * crossedTensor v₁ v₂ v₃ v₄
          (nearProjection W * twoPortScattering b E XX)
          (nearProjection W * twoPortScattering b E XX) -
        conj (sigmaMinus b E s) / ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ) * crossedTensor v₁ v₂ v₃ v₄
          ((twoPortScattering b E XX)ᴴ * nearProjection W)
          ((twoPortScattering b E XX)ᴴ * nearProjection W) =
      ∑ k, fscK b E s W k * crossedTensor v₁ v₂ v₃ v₄ (fscG b E XX k) (fscH b E XX k) := by
  rw [Fin.sum_univ_four]
  simp only [fscK, fscG, fscH, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  push_cast
  ring

theorem bilinear_sandwich {n : Type*} [Fintype n] (u : n → ℂ) (A M B : Matrix n n ℂ)
    (v : n → ℂ) : bilinear u (A * M * B) v = bilinear (Aᴴ *ᵥ u) M (B *ᵥ v) := by
  simp only [bilinear, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    conjTranspose_conjTranspose]

theorem crossedTensor_sandwich {n : Type*} [Fintype n] (u v u' v' : n → ℂ)
    (B B' G H : Matrix n n ℂ) (hB : Bᴴ = B) (hB' : B'ᴴ = B') :
    crossedTensor (B *ᵥ u) (B *ᵥ v) (B' *ᵥ u') (B' *ᵥ v') G H =
      crossedTensor u v u' v' (B * G * B') (B' * H * B) := by
  simp only [crossedTensor, bilinear_sandwich, hB, hB']

theorem norm_integral_mul_le_amgm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℂ}
    (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ) (hg2 : Integrable (fun ω => ‖g ω‖ ^ 2) μ)
    {a : ℝ} (ha : 0 < a) :
    ‖∫ ω, f ω * g ω ∂μ‖ ≤
      (a * ∫ ω, ‖f ω‖ ^ 2 ∂μ + a⁻¹ * ∫ ω, ‖g ω‖ ^ 2 ∂μ) / 2 := by
  have hpt : ∀ ω, ‖f ω * g ω‖ ≤ (a * ‖f ω‖ ^ 2 + a⁻¹ * ‖g ω‖ ^ 2) / 2 := fun ω => by
    rw [norm_mul]
    have h1 : 0 ≤ a⁻¹ * (a * ‖f ω‖ - ‖g ω‖) ^ 2 := by positivity
    have h2 : a⁻¹ * (a * ‖f ω‖ - ‖g ω‖) ^ 2 =
        a * ‖f ω‖ ^ 2 + a⁻¹ * ‖g ω‖ ^ 2 - 2 * (‖f ω‖ * ‖g ω‖) := by
      field_simp; ring
    linarith
  have hI : Integrable (fun ω => (a * ‖f ω‖ ^ 2 + a⁻¹ * ‖g ω‖ ^ 2) / 2) μ :=
    ((hf2.const_mul a).add (hg2.const_mul a⁻¹)).div_const 2
  calc ‖∫ ω, f ω * g ω ∂μ‖ ≤ ∫ ω, ‖f ω * g ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (a * ‖f ω‖ ^ 2 + a⁻¹ * ‖g ω‖ ^ 2) / 2 ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI
          (Filter.Eventually.of_forall hpt)
    _ = _ := by
        rw [integral_div, integral_add (hf2.const_mul a) (hg2.const_mul a⁻¹), integral_const_mul,
          integral_const_mul]

end BlockBand.SourceProcess.ContractingWords
