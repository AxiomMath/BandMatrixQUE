module

public import BlockBand.Critical.CommonPort.FluctCore

/-!
# Common-port mean: the fluctuation clause

Law: `layerLaw W b .common`, conditional on the old deformation (every deterministic Hermitian
`X`; no regularity domain). Domain: `0 < b < 1/2`, `κ > 0`, `e ∈ bulkInterval κ`, arbitrary
`u, v ∈ ℂ^{2W}`. Norms: `eLpNorm` at `ENNReal.ofReal p`; `CoareaPalm.l2Norm` on vectors;
matrix expectation entrywise (`matrixExpect`). Quantifiers: `b, κ`, then `p ≥ 2`, then
`C, W₀`, then `W ≥ W₀`, `X`, `e`, `u`, `v`.

* `l2Norm_eq_vnorm`, `rpow_neg_half_eq`: normalizations.
* `commonPortMean_fluctuation`: the `fluctuation` field of `CommonPortMeanContract`, from
  `GaussianAbsorptionContract` (with `gaussianLpGradient_holds`,
  `bond_eLpNorm_le`, `gueBlock_eLpNorm_le`). `C = C_g √p C_∇ M_Ψ⁹`,
  `W₀ = max(W₀(moments, p = 2), ⌈36p + 1 + 36p/ε₁⌉)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm (l2Norm)
open BlockBand.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

theorem l2Norm_eq_vnorm {ι : Type*} [Fintype ι] (x : ι → ℂ) : l2Norm x = vnorm x := by
  unfold l2Norm vnorm
  rw [EuclideanSpace.norm_eq]

theorem rpow_neg_half_eq {W : ℝ} (hW : 0 ≤ W) : W ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt W := by
  rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1 / 2) by ring, Real.rpow_neg hW, inv_eq_one_div]

/-- Entries of `LL*` are integrable once `‖L‖ ∈ L²`. -/
theorem integrable_commonPortLL_entry {W : ℕ} (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hL : MemLp (fun ω => ‖commonPortL b e X ω‖) 2 (layerLaw W b .common))
    (x y : Fin 2 × Fin W) :
    Integrable (fun ω => commonPortLL b e X ω x y) (layerLaw W b .common) := by
  have hsq := hL.integrable_sq
  have hm : Measurable (fun ω => commonPortLL b e X ω x y) := by
    have hLm := measurable_commonPortL (W := W) b e X
    have hc : Continuous (fun M : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ => (M * Mᴴ) x y) :=
      ((continuous_id.matrix_mul continuous_id.matrix_conjTranspose).matrix_elem x y)
    exact hc.measurable.comp hLm
  refine hsq.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  refine (tfl_entry_le _ x y).trans ?_
  unfold commonPortLL
  refine (l2_opNorm_mul _ _).trans (le_of_eq ?_)
  rw [l2_opNorm_conjTranspose, sq]

/-- `E[u*(LL*)v] = u* E(LL*) v` (entrywise expectations). -/
theorem integral_dot_commonPortLL {W : ℕ} (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hint : ∀ x y, Integrable (fun ω => commonPortLL b e X ω x y) (layerLaw W b .common))
    (u v : Fin 2 × Fin W → ℂ) :
    ∫ ω, star u ⬝ᵥ (commonPortLL b e X ω *ᵥ v) ∂layerLaw W b .common =
      star u ⬝ᵥ (matrixExpect (layerLaw W b .common) (commonPortLL b e X) *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, matrixExpect, Matrix.of_apply, Pi.star_apply]
  rw [integral_finsetSum _ fun x _ => (Integrable.const_mul (integrable_finsetSum _
    fun y _ => (hint x y).mul_const _) _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun y _ => (hint x y).mul_const _]
  congr 1
  exact Finset.sum_congr rfl fun y _ => integral_mul_const _ _

/-- **Common-port mean, fluctuation clause.** Law `layerLaw W b .common` (conditional on the old deformation: every
deterministic Hermitian `X`, no regularity domain); `0 < b < 1/2`, `κ > 0` first, then `p ≥ 2`,
then `C, W₀`; uniformly in `W ≥ W₀`, Hermitian `X`, `e ∈ bulkInterval κ` and arbitrary
`u, v ∈ ℂ^{2W}`:
`‖u*{LL* - E(LL*)}v‖_{L^p} ≤ C W^{-1/2} ‖u‖ ‖v‖` (`l2Norm`, entrywise `matrixExpect`).
Hypothesis: `GaussianAbsorptionContract`; other inputs `gaussianLpGradient_holds`,
`bond_eLpNorm_le`, `gueBlock_eLpNorm_le`, `commonPortMean_moments` (at `p = 2`). -/
theorem commonPortMean_fluctuation (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 2 ≤ p →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
        ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        ∀ e ∈ bulkInterval κ, ∀ u v : Fin 2 × Fin W → ℂ,
          eLpNorm (fun ω => star u ⬝ᵥ
              ((commonPortLL b e X ω - matrixExpect (layerLaw W b .common) (commonPortLL b e X)) *ᵥ v))
            (ENNReal.ofReal p) (layerLaw W b .common) ≤
          ENNReal.ofReal (C * (W : ℝ) ^ (-(1 : ℝ) / 2) * l2Norm u * l2Norm v) := by
  intro b hb0 hb1 κ hκ p hp
  by_cases hκ2 : 2 < κ
  · refine ⟨0, 0, fun W _ _ X _ e he => ?_⟩
    exact absurd (le_trans he.1 he.2) (by linarith)
  push Not at hκ2
  set η₀ : ℝ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη0 : 0 < η₀ := by
    have hs := Real.sqrt_pos.mpr (BlockBand.Layers.four_sub_sq_pos hκ (by linarith))
    have : 0 < 1 - 2 * b := by linarith
    positivity
  obtain ⟨ε₁, CG, hε₁, hCG, hGA'⟩ := hGA b hb0 hb1 η₀ 3 hη0
  obtain ⟨CA, hCA, hA⟩ := gueBlock_eLpNorm_le
  set CB := bondMomentConst b with hCB
  have hCB0 : 0 < CB := bondMomentConst_pos b
  obtain ⟨Cg, hCg, hgr⟩ := BlockBand.GaussianCalculus.gaussianLpGradient_holds
  obtain ⟨CL2, WL2, hmomL⟩ := commonPortMean_moments hGA b hb0 hb1 κ hκ 2 (by norm_num)
  set Mψ : ℝ := CA * CA * (CB * (1 + CG)) with hMψ
  have hMψ0 : 0 ≤ Mψ := by positivity
  refine ⟨Cg * Real.sqrt p * cpGradConst η₀ * Mψ ^ 9,
    max WL2 ⌈36 * p + 1 + 36 * p / ε₁⌉₊, ?_⟩
  intro W hW hW₀ X hX e he u v
  have hWL2 : WL2 ≤ W := (le_max_left _ _).trans hW₀
  have hWr : 36 * p + 1 + 36 * p / ε₁ ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hW₀)
  have hpe : 0 ≤ 36 * p / ε₁ := by positivity
  have hq36 : 36 * p ≤ ε₁ * W := by
    have : 36 * p / ε₁ ≤ W := by linarith
    rw [div_le_iff₀ hε₁] at this; linarith
  have hq36W : 36 * p ≤ (W : ℝ) - 1 := by linarith
  have := bond_isProbabilityMeasure_layerLaw W b .common
  have heabs : |e| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ he).le
  have hzim : η₀ ≤ (commonZ b e).im := commonZ_im_ge_of_mem_bulkInterval hb1.le hκ he
  have hznorm : ‖commonZ b e‖ ≤ 3 := norm_commonZ_le hb0.le (by linarith) heabs
  obtain ⟨hinv, hmom⟩ := hGA' W hW .common X hX e (commonZ b e) hzim hznorm
  -- leaf bounds at `4 (9p) = 36p`
  have h36 : 4 * (9 * p) = 36 * p := by ring
  have hAl : ∀ a : Fin 2, eLpNorm (fun ω : LayerSample W .common => 1 + ‖ω.1 a‖)
      (ENNReal.ofReal (4 * (9 * p))) (layerLaw W b .common) ≤ ENNReal.ofReal CA := fun a => by
    rw [h36]; exact hA W b hb0.le hb1.le .common a (36 * p) (by linarith) hq36W
  have hBl : eLpNorm (fun ω : LayerSample W .common => 1 + ‖bondMatrix .common ω.2‖)
      (ENNReal.ofReal (4 * (9 * p))) (layerLaw W b .common) ≤ ENNReal.ofReal CB := by
    rw [h36]; exact bond_eLpNorm_le .common hb0 (by linarith) (by linarith)
  have hGl : eLpNorm (fun ω : LayerSample W .common => 1 + ‖commonPortResolvent b e X ω‖)
      (ENNReal.ofReal (4 * (9 * p))) (layerLaw W b .common) ≤ ENNReal.ofReal (1 + CG) := by
    rw [h36]
    exact eLpNorm_one_add_le (by linarith) hCG.le (hmom (36 * p) (by linarith) hq36)
  have hΨ := eLpNorm_cpPsi_le (X := X) (e := e) (by positivity : (0 : ℝ) < 9 * p) hAl hBl hGl
  have hΨeq : ENNReal.ofReal CA * ENNReal.ofReal CA * (ENNReal.ofReal CB * ENNReal.ofReal (1 + CG))
      = ENNReal.ofReal Mψ := by
    rw [hMψ, ← ENNReal.ofReal_mul hCA.le, ← ENNReal.ofReal_mul hCB0.le,
      ← ENNReal.ofReal_mul (by positivity)]
  rw [hΨeq] at hΨ
  have hΨm := measurable_cpPsi (W := W) b e X
  have hΨ9 : eLpNorm (fun ω => cpPsi b e X ω ^ 9) (ENNReal.ofReal p) (layerLaw W b .common) ≤
      ENNReal.ofReal Mψ ^ 9 := by
    rw [eLpNorm_pow_eq hΨm.aestronglyMeasurable
      (fun ω => (zero_le_one.trans (one_le_cpPsi b e X ω))) 9 (by norm_num) (by linarith)]
    push_cast
    exact pow_le_pow_left' hΨ 9
  have hΨint : Integrable (fun ω => cpPsi b e X ω ^ 9) (layerLaw W b .common) := by
    have hlt : eLpNorm (fun ω => cpPsi b e X ω ^ 9) (ENNReal.ofReal p) (layerLaw W b .common) < ⊤ :=
      lt_of_le_of_lt hΨ9 (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    have hmem : MemLp (fun ω => cpPsi b e X ω ^ 9) (ENNReal.ofReal p) (layerLaw W b .common) :=
      hlt
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
    exact hmem.integrable hp1
  have hcore := cp_fluct_core hW hb0 hb1 hX heabs hη0 hzim u v (by linarith : (1 : ℝ) ≤ p)
    hgr hinv hΨ9 hΨint
  -- integrability of the entries and the identification of the centred observable
  have hL2 : MemLp (fun ω => ‖commonPortL b e X ω‖) 2 (layerLaw W b .common) := by
    have := (hmomL W hW hWL2 X hX e he).1
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  have hint := integrable_commonPortLL_entry b e X hL2
  have hfun : (fun ω => star u ⬝ᵥ
      ((commonPortLL b e X ω - matrixExpect (layerLaw W b .common) (commonPortLL b e X)) *ᵥ v)) =
      fun ω => star u ⬝ᵥ (commonPortLL b e X ω *ᵥ v) -
        ∫ ω', star u ⬝ᵥ (commonPortLL b e X ω' *ᵥ v) ∂layerLaw W b .common := by
    funext ω
    rw [integral_dot_commonPortLL b e X hint u v, Matrix.sub_mulVec, dotProduct_sub]
  rw [hfun]
  refine hcore.trans (le_of_eq ?_)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hc0 : 0 ≤ cpGradConst η₀ * vnorm u * vnorm v / Real.sqrt W := by
    have := cpGradConst_nonneg hη0; have := vnorm_nonneg u; have := vnorm_nonneg v
    positivity
  rw [l2Norm_eq_vnorm, l2Norm_eq_vnorm, rpow_neg_half_eq hW'.le, ← ENNReal.ofReal_pow hMψ0,
    ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end BlockBand.Critical.CommonPort
