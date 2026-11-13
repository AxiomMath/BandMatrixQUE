module

public import BlockBand.Internal.Contracts.Layers

/-!
# Measurability of the layer resolvent

For every shape, real `E`, complex `z` and deterministic `X`, the augmented layer matrix
`ω ↦ layerMatrix σ E z X ω` is measurable in the Gaussian coordinates, and the layer resolvent
`ω ↦ 𝒢(ω) = (layerMatrix …)⁻¹` (Lean's totalized inverse) and its operator norm are Borel
measurable. This lets the moment integrals over `layerLaw` (for instance in the Gaussian
absorption lemma) be split by Tonelli; no measurability of auxiliary quantities (`d`, `δ`) is
needed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

/-- The matrix inverse is Borel measurable (`A⁻¹ = Ring.inverse (det A) • adjugate A`). -/
theorem measurable_matrix_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  have hdet : Continuous (fun A : Matrix ι ι ℂ => A.det) := continuous_id.matrix_det
  have hadj : Continuous (fun A : Matrix ι ι ℂ => A.adjugate) := continuous_id.matrix_adjugate
  have hinv : Measurable (fun A : Matrix ι ι ℂ => Ring.inverse A.det) := by
    simp_rw [Ring.inverse_eq_inv']
    exact hdet.measurable.inv
  have h : (fun A : Matrix ι ι ℂ => A⁻¹) = fun A => Ring.inverse A.det • A.adjugate := by
    funext A; exact Matrix.inv_def A
  rw [h]
  exact hinv.smul hadj.measurable

/-- The augmented layer matrix is measurable in the Gaussian coordinates (entrywise: every
entry is a coordinate, a conjugated coordinate, a constant, or a difference of these). -/
theorem measurable_layerMatrix {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    Measurable (fun ω : LayerSample W σ => layerMatrix σ E z X ω) := by
  have hcoordA : ∀ (a : Fin σ.blocks) (i j : Fin W),
      Measurable (fun ω : LayerSample W σ => ω.1 a i j) := fun a i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply a).comp measurable_fst))
  have hcoordB : ∀ (a : Fin σ.blocks) (k : Fin σ.ports) (i j : Fin W),
      Measurable (fun ω : LayerSample W σ => ω.2 a k i j) := fun a k i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply k).comp ((measurable_pi_apply a).comp measurable_snd)))
  have hA : ∀ x y,
      Measurable (fun ω : LayerSample W σ => Internal.Contracts.Layers.blockDiag ω.1 x y) := by
    intro x y
    unfold Internal.Contracts.Layers.blockDiag
    split_ifs
    · exact hcoordA _ _ _
    · exact measurable_const
  have hB : ∀ x y, Measurable (fun ω : LayerSample W σ => bondMatrix σ ω.2 x y) := by
    intro x y
    unfold bondMatrix
    split_ifs
    · exact hcoordB _ _ _ _
    · exact measurable_const
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  rcases x with x | x <;> rcases y with y | y
  · simp only [layerMatrix, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply]
    exact ((hA x y).sub measurable_const).sub measurable_const
  · simp only [layerMatrix, Matrix.fromBlocks_apply₁₂]
    exact hB x y
  · simp only [layerMatrix, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    exact continuous_star.measurable.comp (hB y x)
  · simp only [layerMatrix, Matrix.fromBlocks_apply₂₂]
    exact measurable_const

/-- **The layer resolvent is measurable**: `ω ↦ 𝒢(ω)` is Borel for every shape, `E`, `z`, `X`. -/
theorem measurable_layerResolvent {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    Measurable (fun ω : LayerSample W σ => layerResolvent σ E z X ω) :=
  measurable_matrix_inv.comp (measurable_layerMatrix σ E z X)

/-- The operator norm `‖𝒢(ω)‖` is measurable. -/
theorem measurable_norm_layerResolvent {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    Measurable (fun ω : LayerSample W σ => ‖layerResolvent σ E z X ω‖) :=
  continuous_norm.measurable.comp (measurable_layerResolvent σ E z X)

end BlockBand.Layers
