module

public import BlockBand.SourceProcess.ProjSeparator.Layer
public import BlockBand.SourceProcess.ProjSeparator.FluctArith
public import BlockBand.SourceProcess.ContractingWords.SlotMom

/-!
# The fluctuation of the projected separator `ProjGammaFluct`

`projGammaFluct_holds`: under `GaussianAbsorptionContract` and `GaussianLpGradient`, the centred
quadratic expression of the projected separator of one fresh layer has second moment at most
`(C(g/W + δ₀√(g/W))‖u‖‖v‖)²`.
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

theorem bilinear_sub' {n : Type*} [Fintype n] (u v : n → ℂ) (A B : Matrix n n ℂ) :
    bilinear u (A - B) v = bilinear u A v - bilinear u B v := by
  simp [bilinear, Matrix.sub_mulVec, dotProduct_sub]

/-- **`ProjGammaFluct` from input hypotheses.** -/
theorem projGammaFluct_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ProjGammaFluct := by
  intro b hb0 hb κ hκ
  obtain ⟨C₂, C₄, CM, W₁, hC₂, hC₄, hCM, hin⟩ := delta_inputs hGA hLp hb0 hb hκ
  set ηL := (1 - b) * κ / 4
  have hηL : 0 < ηL := by
    have : 0 < 1 - b := by linarith
    positivity
  refine ⟨2 * (C₂ * CM + C₄ ^ 2) * ηL⁻¹ ^ 2, max W₁ 1, by positivity, ?_⟩
  intro W hW E hE XX hXX u v X g
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans hW
  have hWo : 1 ≤ W := (le_max_right _ _).trans hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) hE1 hE2
  have hηge : ηL ≤ etaZ b E := FullSource.etaZ_ge hb0 hb hκ hE
  have hH : (etaZ b E)⁻¹ ^ 2 ≤ ηL⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hη.le) (inv_anti₀ hηL hηge) 2
  have hY : (passiveY X).PosSemidef := FullSource.nearSchur_passive hη hXX
  obtain ⟨hD, h2, h4, hM⟩ := hin W hW1 E hE X hY
  have hL2 : ∀ x y, MemLp (fun ω => bilinear x (freshDelta b E X ω -
      matrixExpect (freshLaw W b) (freshDelta b E X)) y) 2 (freshLaw W b) :=
    fun x y => lt_of_le_of_lt (h2 x y) ENNReal.ofReal_lt_top
  obtain ⟨-, hmean⟩ := projGamma_mean (XX := XX) hD hL2
  set Q := farQ b E XX
  set M := matrixExpect (freshLaw W b) (freshDelta b E X)
  set x := nearSel W *ᵥ u
  set y := nearSel W *ᵥ v
  have hQ : ‖Q‖ ≤ (etaZ b E)⁻¹ := norm_farQ_le b E hXX hη
  have hS : frob Q = g / (4 * etaZ b E ^ 2) := frob_farQ hb0 hb hE1 hE2 hXX
  have hg0 : 0 ≤ g := conductance_nonneg b E hη.le hY
  have hδ₀ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWo
  have hc := eLpNorm_gamma_centered (μ := freshLaw W b) (freshDelta b E X) Q hD
    (c₂ := C₂ / Real.sqrt W) (c₄ := C₄ / Real.sqrt W) (by positivity) (by positivity) h2 h4 x y
  have he : (fun ω => bilinear u (projGamma b E XX ω -
      matrixExpect (freshLaw W b) (projGamma b E XX)) v) = fun ω =>
      bilinear x (freshDelta b E X ω * Q * (freshDelta b E X ω * Q)ᴴ) y -
        ∫ ω', bilinear x (freshDelta b E X ω' * Q * (freshDelta b E X ω' * Q)ᴴ) y
          ∂freshLaw W b := by
    funext ω
    rw [bilinear_sub', (hmean u v).1, bilinear_projGamma]
    simp only [bilinear_projGamma]
    rfl
  set β := C₂ / Real.sqrt W * vecNorm x * vecNorm (wVec M Q y) +
    C₂ / Real.sqrt W * vecNorm y * vecNorm (wVec M Q x) +
    2 * ((C₄ / Real.sqrt W) ^ 2 * vecNorm x * vecNorm y * frob Q)
  have hx0 := vecNorm_nonneg x; have hy0 := vecNorm_nonneg y
  have hβ0 : 0 ≤ β := by
    have := vecNorm_nonneg (wVec M Q y); have := vecNorm_nonneg (wVec M Q x)
    have := frob_nonneg Q
    positivity
  have haesm := MemLp.aestronglyMeasurable (lt_of_le_of_lt hc ENNReal.ofReal_lt_top)
  obtain ⟨-, hmom⟩ := moments_of_eLpNorm haesm (M := 2) hβ0 (by simpa using hc) 2 (by norm_num)
    le_rfl
  refine le_trans (le_of_eq ?_) (hmom.trans (pow_le_pow_left₀ hβ0 ?_ 2))
  · congr 1; funext ω; rw [congrFun he ω]
  obtain ⟨hx1, hx2⟩ := vecNorm_wVec_le M Q (inv_nonneg.mpr hη.le) hQ x
  obtain ⟨hy1, hy2⟩ := vecNorm_wVec_le M Q (inv_nonneg.mpr hη.le) hQ y
  rw [hS] at hx1 hx2 hy1 hy2
  have hf := fluct_arith (C₄ := C₄) hWr hη hH hg0 hδ₀ hC₂ hCM hx0 hy0 hM hx1 hx2 hy1 hy2
  have hxu := FullSource.vecNorm_nearSel_mulVec_le u
  have hyv := FullSource.vecNorm_nearSel_mulVec_le v
  have hK : 0 ≤ 2 * (C₂ * CM + C₄ ^ 2) * ηL⁻¹ ^ 2 *
      (g / W + jetDistance0 b E X * Real.sqrt (g / W)) := by positivity
  simp only [β]
  rw [hS]
  refine hf.trans ?_
  calc 2 * (C₂ * CM + C₄ ^ 2) * ηL⁻¹ ^ 2 * (g / W + jetDistance0 b E X * Real.sqrt (g / W)) *
        vecNorm x * vecNorm y
      = 2 * (C₂ * CM + C₄ ^ 2) * ηL⁻¹ ^ 2 * (g / W + jetDistance0 b E X * Real.sqrt (g / W)) *
        (vecNorm x * vecNorm y) := by ring
    _ ≤ 2 * (C₂ * CM + C₄ ^ 2) * ηL⁻¹ ^ 2 * (g / W + jetDistance0 b E X * Real.sqrt (g / W)) *
        (vecNorm u * vecNorm v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hxu hyv hy0 (vecNorm_nonneg u)) hK
    _ = _ := by ring

end BlockBand.SourceProcess.ProjSeparator
