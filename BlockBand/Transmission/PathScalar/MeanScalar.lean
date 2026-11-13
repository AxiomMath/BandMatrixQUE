module

public import BlockBand.Transmission.PathScalar.RowBound

/-!
# The Stieltjes-type function of a passive input

For a passive `X` (`Y = -Im X ⪰ 0`) and `Im ζ > 0`, with `M_ζ = (ζ - X)⁻¹`:
* `stieltjes X ζ = W⁻¹ Tr M_ζ` (`f(z_∂) = W⁻¹Tr R`, so `δ₀(X) = |f(z_∂) - a|`);
* `sqMass X ζ = W⁻¹ Σ |M_ζ(p,q)|² = W⁻¹ Tr M_ζM_ζ*`, and `Im ζ · sqMass ≤ -Im f(ζ)`
  (`im_mul_sqMass_le`, the `k = 1` row bound);
* `crossTr X ζ₁ ζ₂ = W⁻¹ Tr M₁M₂`, `|crossTr| ≤ √sqMass₁ √sqMass₂` (`norm_crossTr_le`), and
  the resolvent identity `f(ζ₁) - f(ζ₂) = -(ζ₁ - ζ₂) crossTr` (`stieltjes_sub`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open Matrix BlockBand.Transmission
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder

variable {W : ℕ}

/-- `f(ζ) = W⁻¹ Tr (ζ - X)⁻¹`. -/
def stieltjes (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) : ℂ :=
  (W : ℂ)⁻¹ * ((ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace

/-- `W⁻¹ Tr M M*`, `M = (ζ - X)⁻¹`. -/
def sqMass (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) : ℝ :=
  (W : ℝ)⁻¹ * ∑ p, ∑ q, ‖(ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ p q‖ ^ 2

/-- `W⁻¹ Tr M₁ M₂`. -/
def crossTr (X : Matrix (Fin W) (Fin W) ℂ) (ζ₁ ζ₂ : ℂ) : ℂ :=
  (W : ℂ)⁻¹ * ∑ p, ∑ q, (ζ₁ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ p q *
    (ζ₂ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ q p

theorem sqMass_nonneg (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) : 0 ≤ sqMass X ζ :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem im_pencil (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) :
    matrixImaginaryPart (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      passiveY X + ζ.im • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have h := matrixImaginaryPart_portPencil_general X ζ
  rw [portPencil] at h
  rw [h, passiveY]; abel

/-- **The Herglotz mass bound** (`k = 1` row bound): `Im ζ · W⁻¹Tr MM* ≤ -Im f(ζ)`. -/
theorem im_mul_sqMass_le {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ζ : ℂ} (hζ : 0 < ζ.im) : ζ.im * sqMass X ζ ≤ -(stieltjes X ζ).im := by
  have h := fun p => (row_col_le _ _ hζ hY (im_pencil X ζ) p).1
  have hs := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => h p
  rw [← Finset.mul_sum] at hs
  have hW : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have him : (stieltjes X ζ).im =
      (W : ℝ)⁻¹ * ∑ p, ((ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ p p).im := by
    simp [stieltjes, Matrix.trace, Complex.im_sum]
  rw [him, sqMass]
  have := mul_le_mul_of_nonneg_left hs hW
  simp only [Finset.sum_neg_distrib] at this
  nlinarith

theorem im_stieltjes_nonpos {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ζ : ℂ} (hζ : 0 < ζ.im) : (stieltjes X ζ).im ≤ 0 := by
  have := im_mul_sqMass_le hY hζ
  have := mul_nonneg hζ.le (sqMass_nonneg X ζ)
  linarith

/-- `|W⁻¹Tr M₁M₂| ≤ √(W⁻¹Tr M₁M₁*) √(W⁻¹Tr M₂M₂*)`. -/
theorem norm_crossTr_le (X : Matrix (Fin W) (Fin W) ℂ) (ζ₁ ζ₂ : ℂ) :
    ‖crossTr X ζ₁ ζ₂‖ ≤ Real.sqrt (sqMass X ζ₁) * Real.sqrt (sqMass X ζ₂) := by
  set M₁ := (ζ₁ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹
  set M₂ := (ζ₂ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹
  have hcs : ‖∑ p, ∑ q, M₁ p q * M₂ q p‖ ≤
      Real.sqrt (∑ p, ∑ q, ‖M₁ p q‖ ^ 2) * Real.sqrt (∑ p, ∑ q, ‖M₂ p q‖ ^ 2) := by
    calc ‖∑ p, ∑ q, M₁ p q * M₂ q p‖ ≤ ∑ p, ∑ q, ‖M₁ p q‖ * ‖M₂ q p‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ =>
            (norm_sum_le _ _).trans (le_of_eq (by simp)))
      _ = ∑ r : Fin W × Fin W, ‖M₁ r.1 r.2‖ * ‖M₂ r.2 r.1‖ := by rw [Fintype.sum_prod_type]
      _ ≤ Real.sqrt (∑ r : Fin W × Fin W, ‖M₁ r.1 r.2‖ ^ 2) *
            Real.sqrt (∑ r : Fin W × Fin W, ‖M₂ r.2 r.1‖ ^ 2) := cs_sqrt _ _ _
      _ = _ := by
          rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm (γ := Fin W)
            (f := fun p q => ‖M₂ q p‖ ^ 2)]
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp only [crossTr]; simp; positivity
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [crossTr, norm_mul, norm_inv, Complex.norm_natCast]
  change (W : ℝ)⁻¹ * ‖∑ p, ∑ q, M₁ p q * M₂ q p‖ ≤
    Real.sqrt ((W : ℝ)⁻¹ * ∑ p, ∑ q, ‖M₁ p q‖ ^ 2) *
      Real.sqrt ((W : ℝ)⁻¹ * ∑ p, ∑ q, ‖M₂ p q‖ ^ 2)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hi : Real.sqrt (W : ℝ)⁻¹ * Real.sqrt (W : ℝ)⁻¹ = (W : ℝ)⁻¹ :=
    Real.mul_self_sqrt (by positivity)
  calc (W : ℝ)⁻¹ * ‖∑ p, ∑ q, M₁ p q * M₂ q p‖
      ≤ (W : ℝ)⁻¹ * (Real.sqrt (∑ p, ∑ q, ‖M₁ p q‖ ^ 2) *
          Real.sqrt (∑ p, ∑ q, ‖M₂ p q‖ ^ 2)) := by gcongr
    _ = (Real.sqrt (W : ℝ)⁻¹ * Real.sqrt (W : ℝ)⁻¹) * (Real.sqrt (∑ p, ∑ q, ‖M₁ p q‖ ^ 2) *
          Real.sqrt (∑ p, ∑ q, ‖M₂ p q‖ ^ 2)) := by rw [hi]
    _ = _ := by ring

/-- **The resolvent identity** `f(ζ₁) - f(ζ₂) = -(ζ₁ - ζ₂) W⁻¹Tr M₁M₂`. -/
theorem stieltjes_sub {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ζ₁ ζ₂ : ℂ}
    (h₁ : 0 < ζ₁.im) (h₂ : 0 < ζ₂.im) :
    stieltjes X ζ₁ - stieltjes X ζ₂ = -(ζ₁ - ζ₂) * crossTr X ζ₁ ζ₂ := by
  set K₁ := ζ₁ • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set K₂ := ζ₂ • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have hK₁ := passive_inverse_constructed K₁ _ h₁ hY (im_pencil X ζ₁)
  have hK₂ := passive_inverse_constructed K₂ _ h₂ hY (im_pencil X ζ₂)
  have hid : K₁⁻¹ - K₂⁻¹ = -(ζ₁ - ζ₂) • (K₁⁻¹ * K₂⁻¹) := by
    have : K₁⁻¹ - K₂⁻¹ = K₁⁻¹ * (K₂ - K₁) * K₂⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hK₁.2.2, Matrix.one_mul, Matrix.mul_assoc, hK₂.2.1,
        Matrix.mul_one]
    rw [this, show K₂ - K₁ = -(ζ₁ - ζ₂) • (1 : Matrix (Fin W) (Fin W) ℂ) by
      simp only [K₁, K₂]; rw [neg_sub, sub_smul]; abel]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [stieltjes, stieltjes, ← mul_sub, ← Matrix.trace_sub, hid, Matrix.trace_smul, crossTr]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, smul_eq_mul]
  ring

end BlockBand.Transmission.PathScalar
