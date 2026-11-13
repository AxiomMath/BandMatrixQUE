module

public import BlockBand.Transmission.PassiveLayer.BilGrad

/-!
# Gaussian `L^p` Poincaré for the regularized bilinear functionals

* `centered_reg_le`: for `ε > 0`, **given the Gaussian `L^p` gradient inequality** (the body of
  `Inputs.GaussianLpGradient`, explicit hypothesis) and `ψ ∈ L^p`,
  `‖ψ - Eψ‖_p ≤ C₀√p · √(12/W)·3‖u‖‖v‖ · ‖psiWeight‖_p` under `freshLaw W b`, through
  `freshLaw = (gaussianProduct v).map coordMap` and `grad_psi_reg`.
* `norm_psiMap_le`: `|ψ| ≤ ‖P_K𝒢‖²‖R‖‖u‖‖v‖`; `continuous_psiMap`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- The regularized functional on the layer sample. -/
def psiLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (u v : Fin W → ℂ) (θ : ℂ)
    (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  psiMap ((pK w X)ᴴ *ᵥ u) ((pK w X)ᴴ *ᵥ v) θ (pTwo W) Γ (layerAt E w X ω)

/-- Its gradient weight `‖P_K𝒢‖²‖𝒢‖(‖𝒢‖+‖Γ‖)`. -/
def psiWeight (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  ‖pK w X * layerAt E w X ω‖ ^ 2 * ‖layerAt E w X ω‖ * (‖layerAt E w X ω‖ + ‖Γ‖)

theorem measurable_psiWeight (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Measurable (psiWeight E w X Γ) := by
  have h := measurable_layerAt E w X
  have h1 : Measurable fun ω => ‖pK w X * layerAt E w X ω‖ :=
    continuous_norm.measurable.comp ((continuous_const.matrix_mul continuous_id).measurable.comp h)
  have h2 : Measurable fun ω => ‖layerAt E w X ω‖ := continuous_norm.measurable.comp h
  exact ((h1.pow_const 2).mul h2).mul (h2.add_const _)

/-- **Gaussian `L^p` Poincaré at fixed `ε > 0`** (from `Inputs.GaussianLpGradient`). -/
theorem centered_reg_le {C₀ : ℝ}
    (hLp : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (C₀ * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ} (hw : 0 < w.im)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (u v : Fin W → ℂ) {θ : ℂ} (hθ : ‖θ‖ ≤ 1)
    (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) {p : ℝ}
    (hp : 1 ≤ p) (hMem : MemLp (psiLayer E w (regX X ε) u v θ Γ) (ENNReal.ofReal p) (freshLaw W b)) :
    eLpNorm (fun ω => psiLayer E w (regX X ε) u v θ Γ ω -
        ∫ ω', psiLayer E w (regX X ε) u v θ Γ ω' ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (C₀ * Real.sqrt p) * (ENNReal.ofReal (Real.sqrt (3 * (4 / W)) * 3 *
        (vecNorm u * vecNorm v)) * eLpNorm (psiWeight E w (regX X ε) Γ) (ENNReal.ofReal p)
          (freshLaw W b)) := by
  set F := psiLayer E w (regX X ε) u v θ Γ
  set f : (CoordW W → ℝ) → ℂ := fun ρ => psiMap ((pK w (regX X ε))ᴴ *ᵥ u)
    ((pK w (regX X ε))ᴴ *ᵥ v) θ (pTwo W) Γ (gReg E w b X ε ρ)
  have hfF : f = F ∘ coordMap W b := rfl
  have hcm := measurable_coordMap W b
  have hfc : ContDiff ℝ 1 f := contDiff_psi_gReg E hw b hY hε _ _ θ _ Γ
  have hFm : AEStronglyMeasurable F ((gaussianProduct (coordVar W b)).map (coordMap W b)) := by
    rw [← freshLaw_eq_map]; exact hMem.aestronglyMeasurable
  have hMf : MemLp f (ENNReal.ofReal p) (gaussianProduct (coordVar W b)) := by
    rw [hfF]
    exact (memLp_map_measure_iff hFm hcm.aemeasurable).mp (by rw [← freshLaw_eq_map]; exact hMem)
  have h := hLp p hp (CoordW W) (coordVar W b) f hfc hMf
  have hk0 : 0 ≤ Real.sqrt (3 * (4 / W)) * 3 * (vecNorm u * vecNorm v) := by
    have := vecNorm_nonneg u; have := vecNorm_nonneg v; positivity
  have hpw := measurable_psiWeight E w (regX X ε) Γ
  have hLHS : eLpNorm (fun ω => F ω - ∫ ω', F ω' ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) =
      eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct (coordVar W b)) (ENNReal.ofReal p)
        (gaussianProduct (coordVar W b)) := by
    rw [freshLaw_eq_map, integral_map hcm.aemeasurable hFm]
    have hg : AEStronglyMeasurable (fun ω => F ω - ∫ y, F (coordMap W b y)
        ∂gaussianProduct (coordVar W b)) ((gaussianProduct (coordVar W b)).map (coordMap W b)) :=
      hFm.sub aestronglyMeasurable_const
    rw [eLpNorm_map_measure hg hcm.aemeasurable]
    rfl
  have hgrad : eLpNorm (weightedGradientNorm (coordVar W b) f) (ENNReal.ofReal p)
      (gaussianProduct (coordVar W b)) ≤ ENNReal.ofReal (Real.sqrt (3 * (4 / W)) * 3 *
        (vecNorm u * vecNorm v)) * eLpNorm (psiWeight E w (regX X ε) Γ) (ENNReal.ofReal p)
          (freshLaw W b) := by
    have hpt : ∀ ρ, ‖weightedGradientNorm (coordVar W b) f ρ‖ ≤
        (Real.sqrt (3 * (4 / W)) * 3 * (vecNorm u * vecNorm v)) *
          psiWeight E w (regX X ε) Γ (coordMap W b ρ) := by
      intro ρ
      rw [Real.norm_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
      refine (grad_psi_reg hb0 hb hW E hw hY hε u v hθ Γ ρ).trans (le_of_eq ?_)
      simp only [psiWeight, gReg, layerAt]; ring
    have hcont : Continuous (weightedGradientNorm (coordVar W b) f) := by
      unfold weightedGradientNorm
      have hd := hfc.continuous_fderiv one_ne_zero
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    refine (eLpNorm_mono_real hcont.aestronglyMeasurable hpt).trans (le_of_eq ?_)
    have hsm := eLpNorm_const_smul (Real.sqrt (3 * (4 / W)) * 3 * (vecNorm u * vecNorm v))
      (psiWeight E w (regX X ε) Γ ∘ coordMap W b) (ENNReal.ofReal p) (gaussianProduct (coordVar W b))
    rw [show ((Real.sqrt (3 * (4 / W)) * 3 * (vecNorm u * vecNorm v)) •
        (psiWeight E w (regX X ε) Γ ∘ coordMap W b)) = fun ρ =>
          Real.sqrt (3 * (4 / W)) * 3 * (vecNorm u * vecNorm v) *
            psiWeight E w (regX X ε) Γ (coordMap W b ρ) from rfl] at hsm
    rw [hsm, Real.enorm_eq_ofReal hk0, freshLaw_eq_map,
      eLpNorm_map_measure (by rw [← freshLaw_eq_map]; exact hpw.aestronglyMeasurable)
        hcm.aemeasurable]
  rw [hLHS]
  exact h.trans (by gcongr)

section Generic
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem norm_psiMap_le (pk : Matrix m n ℂ) (G P Γ : Matrix n n ℂ) (θ : ℂ) (u v : m → ℂ) :
    ‖psiMap (pkᴴ *ᵥ u) (pkᴴ *ᵥ v) θ P Γ G‖ ≤
      ‖pk * G‖ ^ 2 * ‖rMap θ P Γ G‖ * (vecNorm u * vecNorm v) := by
  have hsa : star (pkᴴ *ᵥ u) = star u ᵥ* pk := by
    simp only [star_mulVec, conjTranspose_conjTranspose]
  have e : psiMap (pkᴴ *ᵥ u) (pkᴴ *ᵥ v) θ P Γ G =
      star u ⬝ᵥ (((pk * G) * rMap θ P Γ G * (pk * G)ᴴ) *ᵥ v) := by
    rw [psiMap, dotProduct_mulVec, hsa, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec,
      conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (norm_star_dotProduct_le _ _).trans ?_
  have := vecNorm_mulVec_le ((pk * G) * rMap θ P Γ G * (pk * G)ᴴ) v
  have h1 : ‖(pk * G) * rMap θ P Γ G * (pk * G)ᴴ‖ ≤ ‖pk * G‖ ^ 2 * ‖rMap θ P Γ G‖ := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    have := Matrix.l2_opNorm_mul (pk * G) (rMap θ P Γ G)
    nlinarith [norm_nonneg (pk * G), norm_nonneg (rMap θ P Γ G),
      norm_nonneg (pk * G * rMap θ P Γ G)]
  have hu := vecNorm_nonneg u
  calc vecNorm u * vecNorm (((pk * G) * rMap θ P Γ G * (pk * G)ᴴ) *ᵥ v)
      ≤ vecNorm u * (‖pk * G‖ ^ 2 * ‖rMap θ P Γ G‖ * vecNorm v) :=
        mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_right h1 (vecNorm_nonneg v))) hu
    _ = _ := by ring

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem continuous_psiMap (θ : ℂ) (P Γ : Matrix n n ℂ) :
    Continuous fun x : (n → ℂ) × (n → ℂ) × Matrix n n ℂ => psiMap x.1 x.2.1 θ P Γ x.2.2 := by
  unfold psiMap rMap
  have hG : Continuous fun x : (n → ℂ) × (n → ℂ) × Matrix n n ℂ => x.2.2 :=
    continuous_snd.comp continuous_snd
  have hR : Continuous fun x : (n → ℂ) × (n → ℂ) × Matrix n n ℂ =>
      θ • (P * x.2.2 * P) + Γ :=
    (((continuous_const.matrix_mul hG).matrix_mul continuous_const).const_smul θ).add
      continuous_const
  exact continuous_fst.star.dotProduct
    (((hG.matrix_mul hR).matrix_mul hG.matrix_conjTranspose).matrix_mulVec
      (continuous_fst.comp continuous_snd))

end Generic

end BlockBand.Transmission.PassiveLayer
