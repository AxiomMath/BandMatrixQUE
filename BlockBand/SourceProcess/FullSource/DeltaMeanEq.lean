module

public import BlockBand.SourceProcess.FullSource.DeltaMeanSD

/-!
# `EΔ = (z+E)E[K𝒢₁₁] + c E[⟨𝒢₁₁⟩K𝒢₁₁] + b E[⟨𝒢₂₂⟩K𝒢₁₁]` (strictly passive `X`)

The exact form of the mean of `Δ` at a strictly passive input, from the right Schwinger–Dyson
identity.

* `meanSD_right_matrix`: `1 + E·M₀ + M₀X = -c E[⟨𝒢₁₁⟩𝒢₁₁] - b E[⟨𝒢₂₂⟩𝒢₁₁]`, `M₀ = E𝒢₁₁`;
* `delta_mean_eq`: the exact form of `EΔ`. Only `K` times the identity is used: `EΔ = KM₀K - K`
  and `KM₀K = z·KM₀ - K(M₀X)`, with `M₀X` from the right identity, so every term carries the
  bounded letter `K𝒢₁₁` and no error is multiplied by the unbounded `K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The right physical mean identity in matrix form.** -/
theorem meanSD_right_matrix {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef) {C2 C4 : ℝ}
    (hm2 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hint : ∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 0 x y)
      (layerLaw W b .oneBlockOnePort)) (hW : 0 < W) :
    let μ := layerLaw W b .oneBlockOnePort
    let M0 := matrixExpect μ fun ω => passiveLetter E (boundaryZ b E) X ω 0
    (1 : Matrix (Fin W) (Fin W) ℂ) + (E : ℂ) • M0 + M0 * X =
      -((1 - 2 * b : ℝ) : ℂ) • matrixExpect μ (fun ω => physTr b E X ω •
          passiveLetter E (boundaryZ b E) X ω 0) -
        (b : ℂ) • matrixExpect μ (fun ω => portTr b E X ω • passiveLetter E (boundaryZ b E) X ω 0) := by
  intro μ M0
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  ext x y
  have hSD := meanSD_right_of hη hX hm2 hm4 (phys x) y
  have hg : ∀ x y, Integrable (fun ω => gRes b E X ω (phys x) (phys y)) μ := fun x y => hint x y
  have hl : ∫ ω, (gRes b E X ω * layerLin ω) (phys x) (phys y) ∂μ =
      (if x = y then (1 : ℂ) else 0) + (E : ℂ) * M0 x y + ∑ k, M0 x k * X k y := by
    have hi : ∀ k, Integrable (fun ω => gRes b E X ω (phys x) (phys k) * X k y) μ :=
      fun k => (hg x k).mul_const _
    have hc : Integrable (fun ω => (if x = y then (1 : ℂ) else 0) +
        (E : ℂ) * gRes b E X ω (phys x) (phys y)) μ :=
      (integrable_const _).add ((hg x y).const_mul _)
    calc ∫ ω, (gRes b E X ω * layerLin ω) (phys x) (phys y) ∂μ
        = ∫ ω, ((if x = y then (1 : ℂ) else 0) + (E : ℂ) * gRes b E X ω (phys x) (phys y)) +
            ∑ k, gRes b E X ω (phys x) (phys k) * X k y ∂μ := by
          refine integral_congr_ae ((ae_mul_layerLin hb h1 h2 hX).mono fun ω h => ?_)
          dsimp only
          rw [h, Matrix.sub_apply, H0_phys_right]
          simp [Matrix.one_apply]; ring
      _ = _ := by
          rw [integral_add hc (integrable_finsetSum _ fun k _ => hi k),
            integral_add (integrable_const _) ((hg x y).const_mul _), integral_const_mul,
            integral_finsetSum _ fun k _ => hi k]
          have hconst : ∫ _ω, (if x = y then (1 : ℂ) else 0) ∂μ = if x = y then 1 else 0 := by
            simp
          simp only [integral_mul_const, M0, matrixExpect, Matrix.of_apply, hconst]
          rfl
  rw [gueVar_cast hb, ginVar_cast hb0] at hSD
  have e1 : ∫ ω, (∑ y', gRes b E X ω (phys y') (phys y')) * gRes b E X ω (phys x) (phys y) ∂μ =
      (W : ℂ) * ∫ ω, physTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω
    simp only [physTr, trace_letter0]; field_simp
  have e2 : ∫ ω, (∑ y', gRes b E X ω (port y') (port y')) * gRes b E X ω (phys x) (phys y) ∂μ =
      (W : ℂ) * ∫ ω, portTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω
    simp only [portTr, trace_letter3]; field_simp
  calc ((1 : Matrix (Fin W) (Fin W) ℂ) + (E : ℂ) • M0 + M0 * X) x y
      = (if x = y then (1 : ℂ) else 0) + (E : ℂ) * M0 x y + ∑ k, M0 x k * X k y := by
        simp [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply]
    _ = ∫ ω, (gRes b E X ω * layerLin ω) (phys x) (phys y) ∂μ := hl.symm
    _ = -(((1 - 2 * b : ℝ) : ℂ) * ∫ ω, physTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ) -
          (b : ℂ) * ∫ ω, portTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ := by
        rw [hSD, e1, e2]; field_simp
    _ = _ := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, matrixExpect,
          Matrix.of_apply, neg_mul]
        rfl

/-- `E[AFB - C] = A(EF)B - C` for a probability measure and integrable entries. -/
theorem matrixExpect_sandwich {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A B C : Matrix n n ℂ) (F : Ω → Matrix n n ℂ)
    (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) :
    matrixExpect μ (fun ω => A * F ω * B - C) = A * matrixExpect μ F * B - C := by
  ext i j
  have h1 : ∀ k, Integrable (fun ω => ∑ l, A i l * F ω l k) μ := fun k =>
    integrable_finsetSum _ fun l _ => (hF l k).const_mul _
  have h2 : Integrable (fun ω => ∑ k, (∑ l, A i l * F ω l k) * B k j) μ :=
    integrable_finsetSum _ fun k _ => (h1 k).mul_const _
  simp only [matrixExpect, Matrix.of_apply, Matrix.sub_apply, Matrix.mul_apply]
  have hc : ∫ _ω, C i j ∂μ = C i j := by simp
  rw [integral_sub h2 (integrable_const _), hc,
    integral_finsetSum _ fun k _ => (h1 k).mul_const _]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, integral_finsetSum _ fun l _ => (hF l k).const_mul _]
  simp only [integral_const_mul]

theorem matrixExpect_mul_left {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    (A : Matrix n n ℂ) (F : Ω → Matrix n n ℂ) (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) :
    matrixExpect μ (fun ω => A * F ω) = A * matrixExpect μ F := by
  ext i j
  simp only [matrixExpect, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ fun k _ => (hF k j).const_mul _]
  simp only [integral_const_mul]

/-- **The exact form of `EΔ`** at a strictly passive input. -/
theorem delta_mean_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef) {C2 C4 : ℝ}
    (hm2 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hint : ∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 0 x y)
      (layerLaw W b .oneBlockOnePort))
    (hintP : ∀ x y, Integrable (fun ω => physTr b E X ω * passiveLetter E (boundaryZ b E) X ω 0 x y)
      (layerLaw W b .oneBlockOnePort))
    (hintQ : ∀ x y, Integrable (fun ω => portTr b E X ω * passiveLetter E (boundaryZ b E) X ω 0 x y)
      (layerLaw W b .oneBlockOnePort)) (hW : 0 < W) :
    let μ := layerLaw W b .oneBlockOnePort
    matrixExpect μ (freshDelta b E X) =
      (boundaryZ b E + E) • matrixExpect μ (fun ω => kG11 E (boundaryZ b E) X ω) +
        ((1 - 2 * b : ℝ) : ℂ) • matrixExpect μ (fun ω => physTr b E X ω • kG11 E (boundaryZ b E) X ω) +
        (b : ℂ) • matrixExpect μ (fun ω => portTr b E X ω • kG11 E (boundaryZ b E) X ω) := by
  intro μ
  have hI := meanSD_right_matrix hb0 hb h1 h2 hX hm2 hm4 hint hW
  set z := boundaryZ b E
  set K : Matrix (Fin W) (Fin W) ℂ := z • 1 - X
  set M0 := matrixExpect μ fun ω => passiveLetter E z X ω 0
  set Mp := matrixExpect μ fun ω => physTr b E X ω • passiveLetter E z X ω 0
  set Mq := matrixExpect μ fun ω => portTr b E X ω • passiveLetter E z X ω 0
  have hΔ : freshDelta b E X = fun ω => K * passiveLetter E z X ω 0 * K - K := by
    funext ω; rw [freshDelta_eq]; rfl
  have hk : (fun ω => kG11 E z X ω) = fun ω => K * passiveLetter E z X ω 0 := rfl
  have hkp : (fun ω => physTr b E X ω • kG11 E z X ω) =
      fun ω => K * (physTr b E X ω • passiveLetter E z X ω 0) := by
    funext ω; rw [Matrix.mul_smul]; rfl
  have hkq : (fun ω => portTr b E X ω • kG11 E z X ω) =
      fun ω => K * (portTr b E X ω • passiveLetter E z X ω 0) := by
    funext ω; rw [Matrix.mul_smul]; rfl
  have e1 : matrixExpect μ (fun ω => kG11 E z X ω) = K * M0 := by
    rw [hk]; exact matrixExpect_mul_left K _ hint
  have e2 : matrixExpect μ (fun ω => physTr b E X ω • kG11 E z X ω) = K * Mp := by
    rw [hkp]; exact matrixExpect_mul_left K _ hintP
  have e3 : matrixExpect μ (fun ω => portTr b E X ω • kG11 E z X ω) = K * Mq := by
    rw [hkq]; exact matrixExpect_mul_left K _ hintQ
  rw [hΔ, matrixExpect_sandwich K K K _ hint, e1, e2, e3]
  have hMX : M0 * X = (-((1 - 2 * b : ℝ) : ℂ) • Mp - (b : ℂ) • Mq) - 1 - (E : ℂ) • M0 := by
    rw [← hI]; abel
  have hKK : K * M0 * K = z • (K * M0) - K * (M0 * X) := by
    simp only [K, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  rw [hKK, hMX]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  module

end BlockBand.SourceProcess.FullSource
