module

public import BlockBand.SourceProcess.ProjSeparator.MeanArith

/-!
# The mean of the projected separator `ProjGammaMean`

`projGammaMean_holds`: under `GaussianAbsorptionContract`, `GaussianLpGradient` and
`GaussianPoincare`, the mean of the projected separator of one fresh layer is
`E C_NC_N* = (D₀g/2W)P + R`, `P` the near projection, with a remainder `R` of size
`C(δ₀² + gW⁻² + (g/W)(δ₀ + δ₁ + g/W))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceCovariance BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.SourceProcess.ContractingWords
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem bilinear_sub_smul {n : Type*} [Fintype n] (u v : n → ℂ) (A B : Matrix n n ℂ) (c : ℂ) :
    bilinear u (A - c • B) v = bilinear u A v - c * bilinear u B v := by
  simp [bilinear, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

theorem inv_sq_le_of_le {η ηL : ℝ} (hηL : 0 < ηL) (h : ηL ≤ η) : η⁻¹ ^ 2 ≤ ηL⁻¹ ^ 2 :=
  pow_le_pow_left₀ (inv_nonneg.mpr (hηL.le.trans h)) (inv_anti₀ hηL h) 2

/-- The last step of `ProjGammaMean`, abstracted. -/
theorem final_mean_bound {z₁ z₂ : ℂ} {m nM ce S CO CO' nx ny nu nv B : ℝ}
    (h1 : ‖z₁‖ ≤ m * nM ^ 2 * nx * ny) (h3 : ‖z₂‖ ≤ CO * ce * nx * ny * S) (hCO : CO ≤ CO')
    (hce : 0 ≤ ce) (hS : 0 ≤ S) (hnx : 0 ≤ nx) (hny : 0 ≤ ny) (hxy : nx * ny ≤ nu * nv)
    (hm0 : 0 ≤ m) (hCO' : 0 ≤ CO') (harith : m * nM ^ 2 + CO' * ce * S ≤ B) :
    ‖z₁ + z₂‖ ≤ B * (nu * nv) := by
  have hxy0 : 0 ≤ nx * ny := mul_nonneg hnx hny
  have h3' : CO * ce * nx * ny * S ≤ CO' * ce * S * (nx * ny) := by
    have := mul_le_mul_of_nonneg_right hCO (mul_nonneg (mul_nonneg hce hxy0) hS)
    calc CO * ce * nx * ny * S = CO * (ce * (nx * ny) * S) := by ring
      _ ≤ CO' * (ce * (nx * ny) * S) := this
      _ = _ := by ring
  have h0 : 0 ≤ m * nM ^ 2 + CO' * ce * S := by positivity
  have hB0 : 0 ≤ B := h0.trans harith
  calc ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
    _ ≤ (m * nM ^ 2 + CO' * ce * S) * (nx * ny) := by nlinarith
    _ ≤ B * (nu * nv) := mul_le_mul harith hxy hxy0 hB0

/-- **`ProjGammaMean` from input hypotheses.** -/
theorem projGammaMean_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : ProjGammaMean := by
  intro b hb0 hb κ hκ
  obtain ⟨C₂, C₄, CM, W₁, -, -, hCM, hin⟩ := delta_inputs hGA hLp hb0 hb hκ
  obtain ⟨CO, W₂, hO⟩ := deltaCovarianceOpposite_holds hGA hLp hP b hb0 hb κ hκ
  set ηL := (1 - b) * κ / 4
  have hηL : 0 < ηL := by
    have : 0 < 1 - b := by linarith
    positivity
  set CO' := max CO 0
  refine ⟨(2 * CM ^ 2 + CO') * ηL⁻¹ ^ 2, max (max W₁ W₂) 1, by positivity, ?_⟩
  intro W hW E hE s hs XX hXX X g
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hWo⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) hE1 hE2
  have hηge : ηL ≤ etaZ b E := FullSource.etaZ_ge hb0 hb hκ hE
  have hY : (passiveY X).PosSemidef := FullSource.nearSchur_passive hη hXX
  obtain ⟨hD, h2, -, hM⟩ := hin W hW1 E hE X hY
  have hL2 : ∀ x y, MemLp (fun ω => bilinear x (freshDelta b E X ω -
      matrixExpect (freshLaw W b) (freshDelta b E X)) y) 2 (freshLaw W b) :=
    fun x y => lt_of_le_of_lt (h2 x y) ENNReal.ofReal_lt_top
  obtain ⟨-, hmean⟩ := projGamma_mean (XX := XX) hD hL2
  set Q := farQ b E XX
  set M := matrixExpect (freshLaw W b) (freshDelta b E X)
  have hQ : ‖Q‖ ≤ (etaZ b E)⁻¹ := norm_farQ_le b E hXX hη
  have hS : frob Q = g / (4 * etaZ b E ^ 2) := frob_farQ hb0 hb hE1 hE2 hXX
  have hg0 : 0 ≤ g := conductance_nonneg b E hη.le hY
  have hδ₀ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδ₁ : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWo
  have hw0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hw1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWr
  have harith := mean_arith (δ₁ := jetDistance1 b E s X) hδ₀ hδ₁ hg0 hw0 hw1 hη
    (le_max_right CO 0) (inv_sq_le_of_le hηL hηge) (norm_nonneg M) (hM)
  have hcov : covErr b E s X = (W : ℝ)⁻¹ ^ 2 +
      (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X + g * (W : ℝ)⁻¹) := by
    rw [covErr, div_eq_mul_inv]
  have hce0 : 0 ≤ covErr b E s X := covErr_nonneg b E s hη.le hY
  set B := (2 * CM ^ 2 + CO') * ηL⁻¹ ^ 2 * (jetDistance0 b E X ^ 2 + g * ((W : ℝ)⁻¹) ^ 2 +
    g / W * (jetDistance0 b E X + jetDistance1 b E s X + g / W))
  have hB : (2 * CM ^ 2 + CO') * ηL⁻¹ ^ 2 * (jetDistance0 b E X ^ 2 + g * ((W : ℝ)⁻¹) ^ 2 +
      g * (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X + g * (W : ℝ)⁻¹)) = B := by
    simp only [B, div_eq_mul_inv]
  rw [hB] at harith
  have hm0 : 0 ≤ min ((etaZ b E)⁻¹ ^ 2) (g / (4 * etaZ b E ^ 2)) :=
    le_min (by positivity) (by positivity)
  have hS0 : 0 ≤ g / (4 * etaZ b E ^ 2) := by positivity
  rw [← hcov] at harith
  have hB0 : 0 ≤ B := le_trans (by positivity) harith
  refine opNorm_le_of_bilinear _ hB0 fun u v => ?_
  set x := nearSel W *ᵥ u
  set y := nearSel W *ᵥ v
  obtain ⟨hm1, hm2⟩ := hmean u v
  have hc : (((transportD0 b E * g / (2 * W) : ℝ)) : ℂ) =
      ((sigmaPlus b : ℝ) : ℂ) / W * ((∑ j, vecNorm (colQ Q j) ^ 2 : ℝ) : ℂ) := by
    rw [dZero_g_eq hb0 hE1 hE2 hη.ne', sum_vecNorm_colQ_sq, hS]; push_cast; ring
  rw [bilinear_sub_smul, hm1, hm2, bilinear_nearProjection, hc, add_sub_assoc,
    sum_vecNorm_colQ_sq, hS]
  have hx := FullSource.vecNorm_nearSel_mulVec_le u
  have hy := FullSource.vecNorm_nearSel_mulVec_le v
  have hx0 := vecNorm_nonneg x; have hy0 := vecNorm_nonneg y
  have h1 := norm_bilinear_MQ_le M Q (inv_nonneg.mpr hη.le) hQ x y
  have h3 := sum_cross_sub_le x y (colQ Q) _ (sigmaPlus b) (CO * covErr b E s X)
    (fun j => hO W hW2 E hE s hs X hY x (colQ Q j) y (colQ Q j))
  rw [sum_vecNorm_colQ_sq, hS] at h3
  rw [hS] at h1
  have hxy : vecNorm x * vecNorm y ≤ vecNorm u * vecNorm v :=
    mul_le_mul hx hy hy0 (vecNorm_nonneg u)
  exact final_mean_bound h1 h3 (le_max_left CO 0) hce0 hS0 hx0 hy0 hxy hm0 (le_max_right CO 0) harith

end BlockBand.SourceProcess.ProjSeparator
