module

public import BlockBand.SourceProcess.FullSourceCovariance.RightForm
public import BlockBand.Transmission.PassiveCovarianceBulk.SdCross

/-!
# `Φ' = a*K̂𝒢 S (K̂𝒢)ᴴ a'` is a dressed word; its variance is `O(W⁻³)`

`S = diag(s) = W⁻¹ S̃`, `S̃ = diag(Ws)`,
`‖S̃‖ ≤ 1` (`norm_physVar_le`).

* `phiOpp_eq_wordForm` (`W ≠ 0`): `Φ'(x,x') = W⁻¹·wordForm(K̂; ι₁x, ι₁x'; [K̂𝒢, (K̂𝒢)ᴴ];
  [1, S̃, 1])(𝒢)`;
* **`phiOpp_variance_bulk hP hA`**: `Φ' ∈ L²` and `E|Φ' - EΦ'|² ≤ (C/W³)‖x‖²‖x'‖²`, uniformly on
  `bulkInterval κ`, strictly passive `X` (`wordForm_variance_bulk`, `GaussianPoincare`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The letters `[K̂𝒢, (K̂𝒢)ᴴ]`. -/
def wdOpp : Fin 2 → Fin 4 := ![1, 3]

/-- `S̃ = diag(W s_γ)`. -/
def sTilde (W : ℕ) (b : ℝ) : LayerMat W := diagonal fun γ => (W : ℂ) * physVar W b γ

/-- The insertions `[1, S̃, 1]`. -/
def dOpp (W : ℕ) (b : ℝ) : Fin 3 → LayerMat W := ![1, sTilde W b, 1]

theorem norm_sTilde_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) : ‖sTilde W b‖ ≤ 1 := by
  refine norm_diagonal_le _ zero_le_one fun γ => ?_
  rw [norm_mul, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp
  · have := norm_physVar_le (W := W) hb0 hb γ
    have hW : (0 : ℝ) < W := by exact_mod_cast h
    calc (W : ℝ) * ‖physVar W b γ‖ ≤ W * (1 / W) := by gcongr
      _ = 1 := by field_simp

theorem norm_dOpp_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (j : Fin 3) : ‖dOpp W b j‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_sTilde_le hb0 hb
  · exact norm_one_matrix_le

theorem phiOpp_eq_wordForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (hW : W ≠ 0)
    (x x' : Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    phiOpp b E X x x' ω = (W : ℂ)⁻¹ *
      wordForm (kHat b E X) (physVec x) (physVec x') wdOpp (dOpp W b) (gRes b E X ω) := by
  set M := kHat b E X * gRes b E X ω
  have hv : wordVal (kHat b E X) (gRes b E X ω) wdOpp (dOpp W b) = M * sTilde W b * Mᴴ := by
    simp [wordVal, List.ofFn_succ, wLetter, wdOpp, dOpp, M, Matrix.mul_assoc]
  have h2 : star (physVec x) ⬝ᵥ ((M * sTilde W b * Mᴴ) *ᵥ physVec x') =
      ∑ γ, (star (physVec x) ᵥ* M) γ * (((W : ℂ) * physVar W b γ) * (Mᴴ *ᵥ physVec x') γ) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    simp only [dotProduct, sTilde, mulVec_diagonal]
  rw [wordForm, hv, h2, Finset.mul_sum]
  simp only [phiOpp]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have e : star ((star (physVec x') ᵥ* M) γ) = (Mᴴ *ᵥ physVec x') γ := by
    rw [← star_star (Mᴴ *ᵥ physVec x'), star_mulVec, conjTranspose_conjTranspose]; rfl
  rw [e]
  field_simp
  simp only [M]; ring

theorem eLpNorm_two_le_of_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℂ} (hg : MemLp g 2 μ) {V : ℝ} (hV : ∫ ω, ‖g ω‖ ^ 2 ∂μ ≤ V) :
    eLpNorm g 2 μ ≤ ENNReal.ofReal (Real.sqrt V) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) hV (by norm_num)

/-- **`Φ'` in `L²` with centred norm `O(W^{-3/2})`** (bulk-uniform, strictly passive `X`). -/
theorem phiOpp_l2_bulk (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → ∀ x x' : Fin W → ℂ,
        MemLp (phiOpp b E X x x') 2 (freshLaw W b) ∧
        eLpNorm (fun ω => phiOpp b E X x x' ω - ∫ ω', phiOpp b E X x x' ω' ∂freshLaw W b) 2
            (freshLaw W b) ≤
          ENNReal.ofReal (C / (W * Real.sqrt W) * vecNorm x * vecNorm x') := by
  obtain ⟨C, W₀, hC, hv⟩ := CovarianceBulk.wordForm_variance_bulk hP hA hb0 hb hκ 2 1
  refine ⟨Real.sqrt C, max W₀ 1, Real.sqrt_nonneg _, fun W hW E hE X hY x x' => ?_⟩
  have hW0 : W ≠ 0 := by have := le_of_max_le_right hW; omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW0
  obtain ⟨hm, hvar⟩ := hv W (le_of_max_le_left hW) E hE X hY 2 le_rfl wdOpp (dOpp W b)
    (norm_dOpp_le hb0 hb) (physVec x) (physVec x')
  rw [vecNorm_physVec, vecNorm_physVec] at hvar
  set P := fun ω => wordForm (kHat b E X) (physVec x) (physVec x') wdOpp (dOpp W b) (gRes b E X ω)
  have he : phiOpp b E X x x' = fun ω => (W : ℂ)⁻¹ * P ω :=
    funext fun ω => phiOpp_eq_wordForm b E X hW0 x x' ω
  rw [he]
  refine ⟨hm.const_mul _, ?_⟩
  have hc : (fun ω => (W : ℂ)⁻¹ * P ω - ∫ ω', (W : ℂ)⁻¹ * P ω' ∂freshLaw W b) =
      fun ω => (W : ℂ)⁻¹ * (P ω - ∫ ω', P ω' ∂layerLaw W b .oneBlockOnePort) := by
    funext ω; rw [integral_const_mul]; ring
  rw [hc]
  have hm0 : MemLp (fun ω => P ω - ∫ ω', P ω' ∂layerLaw W b .oneBlockOnePort) 2
      (layerLaw W b .oneBlockOnePort) := hm.sub (memLp_const _)
  have h1 := eLpNorm_two_le_of_integral hm0 hvar
  have hsm := eLpNorm_const_smul ((W : ℂ)⁻¹)
    (fun ω => P ω - ∫ ω', P ω' ∂layerLaw W b .oneBlockOnePort) 2 (layerLaw W b .oneBlockOnePort)
  simp only [Pi.smul_def, smul_eq_mul] at hsm
  change eLpNorm (fun ω => (W : ℂ)⁻¹ * (P ω - ∫ ω', P ω' ∂layerLaw W b .oneBlockOnePort)) 2
    (layerLaw W b .oneBlockOnePort) ≤ _
  rw [hsm]
  have hnorm : ‖(W : ℂ)⁻¹‖ₑ = ENNReal.ofReal (W : ℝ)⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_natCast]
  rw [hnorm]
  refine (mul_le_mul' le_rfl h1).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have := PassiveCovariance.vecNorm_nonneg x; have := PassiveCovariance.vecNorm_nonneg x'
  rw [show C / W * (vecNorm x ^ 2 * vecNorm x' ^ 2) = (C / W) * (vecNorm x * vecNorm x') ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_div' _ hWr.le]
  field_simp

end BlockBand.SourceProcess.FullSourceCovariance
