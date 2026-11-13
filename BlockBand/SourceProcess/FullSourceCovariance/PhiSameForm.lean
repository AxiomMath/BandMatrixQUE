module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiOppHolds
public import BlockBand.SourceProcess.FullSourceCovariance.DeltaIBP

/-!
# `W·Φ` without its right weight: `W·Φ = (z+E)T₂ + T₁ - T₃`

The right weight `K` is removed from the equal-sign ladder functional `Φ` by the resolvent
identity, leaving only the bounded letter `K̂𝒢`.

* `phiSame_eq_form`: `W·Φ(x,y') = a*(K̂𝒢)S̃(𝒢K̂)c'`;
* **`phiSame_split`** (wherever `𝒢V = 1 - 𝒢H₀`, i.e. a.s. at `Y ≻ 0`, `FullSource.ae_mul_layerLin`):
  `W·Φ = (z+E)·a*K̂𝒢S̃𝒢c' + a*K̂𝒢S̃c' - a*K̂𝒢S̃𝒢Vc'`. The right `K` is gone, exactly as in
  `delta_form_eq` (`𝒢K̂c' = c' + (z+E)𝒢c' - 𝒢Vc'`).
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

/-- The deterministic layer matrix `H₀` (zero sample). -/
abbrev hZero (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : LayerMat W :=
  layerMatrix .oneBlockOnePort E (boundaryZ b E) (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0

theorem phiSame_eq_form (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (x y' : Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    (W : ℂ) * phiSame b E X x y' ω = star (physVec x) ⬝ᵥ
      (((kHat b E X * gRes b E X ω) * sTilde W b * (gRes b E X ω * kHat b E X)) *ᵥ physVec y') := by
  set M := kHat b E X * gRes b E X ω
  set N := gRes b E X ω * kHat b E X
  have h2 : star (physVec x) ⬝ᵥ ((M * sTilde W b * N) *ᵥ physVec y') =
      ∑ γ, (star (physVec x) ᵥ* M) γ * (((W : ℂ) * physVar W b γ) * (N *ᵥ physVec y') γ) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    simp only [dotProduct, sTilde, mulVec_diagonal]
  rw [h2, phiSame, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have e : (gRes b E X ω *ᵥ (kHat b E X *ᵥ physVec y')) γ = (N *ᵥ physVec y') γ := by
    simp only [N, mulVec_mulVec]
  rw [e]; ring

/-- **The right weight removed from `W·Φ`.** -/
theorem phiSame_split (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (hω : gRes b E X ω * layerLin ω = 1 - gRes b E X ω * hZero b E X) (P : LayerMat W)
    (x y' : Fin W → ℂ) :
    star (physVec x) ⬝ᵥ ((P * (gRes b E X ω * kHat b E X)) *ᵥ physVec y') =
      (boundaryZ b E + E) * (star (physVec x) ⬝ᵥ ((P * gRes b E X ω) *ᵥ physVec y')) +
        star (physVec x) ⬝ᵥ (P *ᵥ physVec y') -
        star (physVec x) ⬝ᵥ ((P * (gRes b E X ω * layerLin ω)) *ᵥ physVec y') := by
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set G := gRes b E X ω
  obtain ⟨h00, h10⟩ := blkAt_H0 b E X
  have e1 : blkAt (P * (G * kHat b E X)) 0 0 = blkAt (P * G) 0 0 * K := by
    rw [← Matrix.mul_assoc, blkAt_mul_kHat_zero]
  have e2 : blkAt (P * (G * layerLin ω)) 0 0 =
      blkAt P 0 0 - blkAt (P * G) 0 0 * (-(E : ℂ) • 1 - X) := by
    rw [hω, Matrix.mul_sub, Matrix.mul_one, blkAt_sub', ← Matrix.mul_assoc, blkAt_mul (P * G),
      Fin.sum_univ_two, h00, h10, Matrix.mul_zero, add_zero]
  rw [form_physVec, form_physVec, form_physVec, form_physVec, e1, e2]
  have hK : K = (boundaryZ b E + E) • (1 : Matrix (Fin W) (Fin W) ℂ) + (-(E : ℂ) • 1 - X) := by
    simp only [K, add_smul, neg_smul]; abel
  rw [hK, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  simp only [bilinear, Matrix.add_mulVec, Matrix.sub_mulVec, smul_mulVec, dotProduct_add,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

end BlockBand.SourceProcess.FullSourceCovariance
