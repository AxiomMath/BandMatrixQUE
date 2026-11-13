module

public import BlockBand.SourceProcess.CompleteSourceGap.GapMeanEq

/-!
# `EΓ` in terms of bounded letters (strictly passive `X`)

**`gap_mean_eq`**: with `L𝒢₂₁ = kfGap`, `K𝒢₁₁ = passiveLetter 4`,
`EΓ = (z+E)E[L𝒢₂₁] + c(E[τ₀K𝒢₁₁] + E[⟨𝒢₁₁⟩L𝒢₂₁]) + b(E[τ₁K𝒢₁₁] + E[⟨𝒢₂₂⟩L𝒢₂₁])`, exactly.
As in `delta_mean_eq`, `EΓ = K·EF·K` and `EF·K = z·EF - EF·X`, with `EF·X` from
`meanSD_gap_matrix`; no error term is ever multiplied by the unbounded `K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer (passiveLetter layerAt g11 g12 g21 g22 kG11 lAt)
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `L𝒢₂₁` (`= K·F`). -/
abbrev kfGap (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  passiveLetter E (boundaryZ b E) X ω 5 * passiveLetter E (boundaryZ b E) X ω 2

theorem gapLetter_eq_kfk (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    gapLetter b E X ω = (boundaryZ b E • 1 - X) * fGap b E X ω * (boundaryZ b E • 1 - X) := by
  show (boundaryZ b E • 1 - X) * g12 E (boundaryZ b E) X ω * g21 E (boundaryZ b E) X ω *
    (boundaryZ b E • 1 - X) = (boundaryZ b E • 1 - X) * (g12 E (boundaryZ b E) X ω *
      g21 E (boundaryZ b E) X ω) * (boundaryZ b E • 1 - X)
  rw [Matrix.mul_assoc (boundaryZ b E • 1 - X)]

theorem kfGap_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    kfGap b E X ω = (boundaryZ b E • 1 - X) * fGap b E X ω := by
  show (boundaryZ b E • 1 - X) * g12 E (boundaryZ b E) X ω * g21 E (boundaryZ b E) X ω =
    (boundaryZ b E • 1 - X) * (g12 E (boundaryZ b E) X ω * g21 E (boundaryZ b E) X ω)
  rw [Matrix.mul_assoc]

theorem letter4_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    passiveLetter E (boundaryZ b E) X ω 4 =
      (boundaryZ b E • 1 - X) * passiveLetter E (boundaryZ b E) X ω 0 := rfl

section Eq
variable {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C4 C6 : ℝ}

/-- **The exact form of `EΓ`** at a strictly passive input. -/
theorem gap_mean_eq (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hX : (passiveY X).PosDef)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hm6 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (3 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C6) (hW : 0 < W) :
    let μ := layerLaw W b .oneBlockOnePort
    matrixExpect μ (gapLetter b E X) =
      (boundaryZ b E + E) • matrixExpect μ (kfGap b E X) +
        ((1 - 2 * b : ℝ) : ℂ) • (matrixExpect μ (fun ω => tau0 b E X ω •
            passiveLetter E (boundaryZ b E) X ω 4) +
          matrixExpect μ (fun ω => physTr b E X ω • kfGap b E X ω)) +
        (b : ℂ) • (matrixExpect μ (fun ω => tau1 b E X ω • passiveLetter E (boundaryZ b E) X ω 4) +
          matrixExpect μ (fun ω => portTr b E X ω • kfGap b E X ω)) := by
  intro μ
  have hI : (E : ℂ) • matrixExpect μ (fGap b E X) + matrixExpect μ (fGap b E X) * X =
      -((1 - 2 * b : ℝ) : ℂ) • matrixExpect μ (fun ω => tau0 b E X ω •
          passiveLetter E (boundaryZ b E) X ω 0 + physTr b E X ω • fGap b E X ω) -
        (b : ℂ) • matrixExpect μ (fun ω => tau1 b E X ω • passiveLetter E (boundaryZ b E) X ω 0 +
          portTr b E X ω • fGap b E X ω) := meanSD_gap_matrix hb0 hb h1 h2 hX hm4 hm6 hW
  have hint := fun x y => gap_integrable (b := b) (E := E) (X := X) hm4 hm6 x y
  set z := boundaryZ b E
  set K : Matrix (Fin W) (Fin W) ℂ := z • 1 - X
  set F0 := matrixExpect μ (fGap b E X)
  set A0 := matrixExpect μ (fun ω => tau0 b E X ω • passiveLetter E z X ω 0)
  set P0 := matrixExpect μ (fun ω => physTr b E X ω • fGap b E X ω)
  set A1 := matrixExpect μ (fun ω => tau1 b E X ω • passiveLetter E z X ω 0)
  set Q0 := matrixExpect μ (fun ω => portTr b E X ω • fGap b E X ω)
  have hM1 : matrixExpect μ (fun ω => tau0 b E X ω • passiveLetter E z X ω 0 +
      physTr b E X ω • fGap b E X ω) = A0 + P0 :=
    matrixExpect_add' _ _ (fun x y => (hint x y).2.1) (fun x y => (hint x y).2.2.1)
  have hM2 : matrixExpect μ (fun ω => tau1 b E X ω • passiveLetter E z X ω 0 +
      portTr b E X ω • fGap b E X ω) = A1 + Q0 :=
    matrixExpect_add' _ _ (fun x y => (hint x y).2.2.2.1) (fun x y => (hint x y).2.2.2.2)
  rw [hM1, hM2] at hI
  have eΓ : matrixExpect μ (gapLetter b E X) = K * F0 * K := by
    have h := FullSource.matrixExpect_sandwich (μ := μ) K K 0 (fGap b E X) fun x y => (hint x y).1
    simp only [sub_zero] at h
    rw [← h]; congr 1; funext ω; exact gapLetter_eq_kfk b E X ω
  have eKF : matrixExpect μ (kfGap b E X) = K * F0 := by
    rw [← FullSource.matrixExpect_mul_left K _ fun x y => (hint x y).1]
    congr 1; funext ω; exact kfGap_eq b E X ω
  have eA0 : matrixExpect μ (fun ω => tau0 b E X ω • passiveLetter E z X ω 4) = K * A0 := by
    rw [← FullSource.matrixExpect_mul_left K _ fun x y => (hint x y).2.1]
    congr 1; funext ω; rw [letter4_eq, Matrix.mul_smul]
  have eP0 : matrixExpect μ (fun ω => physTr b E X ω • kfGap b E X ω) = K * P0 := by
    rw [← FullSource.matrixExpect_mul_left K _ fun x y => (hint x y).2.2.1]
    congr 1; funext ω; rw [kfGap_eq, Matrix.mul_smul]
  have eA1 : matrixExpect μ (fun ω => tau1 b E X ω • passiveLetter E z X ω 4) = K * A1 := by
    rw [← FullSource.matrixExpect_mul_left K _ fun x y => (hint x y).2.2.2.1]
    congr 1; funext ω; rw [letter4_eq, Matrix.mul_smul]
  have eQ0 : matrixExpect μ (fun ω => portTr b E X ω • kfGap b E X ω) = K * Q0 := by
    rw [← FullSource.matrixExpect_mul_left K _ fun x y => (hint x y).2.2.2.2]
    congr 1; funext ω; rw [kfGap_eq, Matrix.mul_smul]
  rw [eΓ, eKF, eA0, eP0, eA1, eQ0]
  have hFX : F0 * X = (-((1 - 2 * b : ℝ) : ℂ) • (A0 + P0) - (b : ℂ) • (A1 + Q0)) - (E : ℂ) • F0 := by
    rw [← hI]; abel
  have hKK : K * F0 * K = z • (K * F0) - K * (F0 * X) := by
    simp only [K, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hKK, hFX]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add]
  module

end Eq

end BlockBand.SourceProcess.CompleteSourceGap
