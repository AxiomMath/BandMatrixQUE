module

public import BlockBand.Critical.Collar.Density.CondSchurSigma

/-!
# Conditional Schur identity: Collar

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

Collar algebra: `ℋ_X(G⁰ + ζ) = csPencil(D, B, G⁰ - e) ζ`, `F_{e+x} + A⁰ = S(x)` (reindexed),
`T_{e+x}* u = -y(x)` (reindexed), and the conditional density integrand in Schur variables.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {W : ℕ}

theorem collarMatrix_eq_csPencil (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω₁ : LayerSample W .common) (G0 : Matrix (PortSite W .common) (PortSite W .common) ℂ)
    (ζ : ℝ) :
    collarMatrix e X (ω₁, G0 + (ζ : ℂ) • 1) =
      csPencil (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2) (G0 - (e : ℂ) • 1) ζ := by
  unfold collarMatrix csPencil collarTopBlock
  congr 1
  exact add_sub_right_comm _ _ _

theorem collarTopBlock_add_energy (e x : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω₁ : LayerSample W .common) :
    collarTopBlock (e + x) X ω₁ = collarTopBlock e X ω₁ - (x : ℂ) • 1 := by
  unfold collarTopBlock
  push_cast
  rw [add_smul]
  abel

theorem collarFW_add_eq (e x : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω₁ : LayerSample W .common) (A0 : Matrix (Fin W) (Fin W) ℂ) :
    collarFW (e + x) X ω₁ + A0 = (csS (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2)
      (A0.submatrix (portEquiv W) (portEquiv W) - (e : ℂ) • 1) x).submatrix
        (portEquiv W).symm (portEquiv W).symm := by
  have hA : A0 = (A0.submatrix (portEquiv W) (portEquiv W)).submatrix (portEquiv W).symm
      (portEquiv W).symm := by
    ext i j; simp
  conv_lhs => rw [hA]
  unfold collarFW collarF csS
  rw [show ∀ (P Q : Matrix (PortSite W .common) (PortSite W .common) ℂ),
      P.submatrix (portEquiv W).symm (portEquiv W).symm +
        Q.submatrix (portEquiv W).symm (portEquiv W).symm =
      (P + Q).submatrix (portEquiv W).symm (portEquiv W).symm from fun P Q => rfl,
    collarTopBlock_add_energy]
  congr 1
  push_cast
  rw [add_smul]
  abel

theorem collarTW_conj_mulVec (e x : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (ω₁ : LayerSample W .common) (hD : (collarTopBlock e X ω₁).IsHermitian)
    (u : Fin 2 × Fin W → ℂ) :
    (collarTW (e + x) X ω₁)ᴴ *ᵥ u =
      -(csY (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2) u x ∘ (portEquiv W).symm) := by
  have hDi : ((collarTopBlock e X ω₁ - (x : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))⁻¹).IsHermitian :=
    (hD.sub (isHermitian_one.smul (Complex.conj_ofReal x))).inv
  unfold collarTW collarT csY
  rw [conjTranspose_submatrix, collarTopBlock_add_energy, conjTranspose_neg, conjTranspose_mul,
    hDi.eq]
  have h := submatrix_mulVec_equiv (-((bondMatrix LayerShape.common ω₁.2)ᴴ *
    (collarTopBlock e X ω₁ - (x : ℂ) • 1)⁻¹)) u (portEquiv W).symm (Equiv.refl _)
  simp only [Equiv.coe_refl, Equiv.refl_symm] at h
  rw [h]
  funext i
  simp [neg_mulVec]

theorem quadForm_condCollarDensity_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω₁ : LayerSample W .common) (u : Fin 2 × Fin W → ℂ) :
    quadForm (condCollarDensity b e X ω₁) u =
      quadForm (sigma (collarFW e X ω₁) (1 - 2 * b) 0) ((collarTW e X ω₁)ᴴ *ᵥ u) := by
  have h := quadForm_conjTranspose_mul_mul (collarTW e X ω₁)ᴴ
    (sigma (collarFW e X ω₁) (1 - 2 * b) 0) u
  rw [conjTranspose_conjTranspose] at h
  exact h

/-- The conditional density integrand in the Schur-pencil variables. -/
theorem quadForm_cfc_collarFW_eq (e x : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (ω₁ : LayerSample W .common) (hD : (collarTopBlock e X ω₁).IsHermitian)
    {A0 : Matrix (Fin W) (Fin W) ℂ} (hA0 : A0.IsHermitian) (f : ℝ → ℝ)
    (u : Fin 2 × Fin W → ℂ) :
    quadForm (cfc f (collarFW (e + x) X ω₁ + A0)) ((collarTW (e + x) X ω₁)ᴴ *ᵥ u) =
      quadForm (cfc f (csS (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2)
        (A0.submatrix (portEquiv W) (portEquiv W) - (e : ℂ) • 1) x))
        (csY (collarTopBlock e X ω₁) (bondMatrix .common ω₁.2) u x) := by
  have hG : (A0.submatrix (portEquiv W) (portEquiv W) - (e : ℂ) •
      (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).IsHermitian :=
    (hA0.submatrix _).sub (isHermitian_one.smul (Complex.conj_ofReal e))
  rw [collarFW_add_eq, cfc_submatrix_equiv _ (csS_isHermitian hD hG x),
    collarTW_conj_mulVec e x ω₁ hD, quadForm_neg_vec', quadForm_submatrix_equiv]

end BlockBand.Critical.Collar.Density
