module

public import BlockBand.SourceProcess.FullSourceCovariance.Interface
public import BlockBand.SourceProcess.FullSource.DeltaReduction

/-!
# The deterministic factors of the full-source covariance tensor

Identities for the factors `ι` and `F` of the Ward identity, used to assemble the covariance
tensor.

With `ι* = nearSel W`, `F = ι*(ℝ - c₀)` (`FullSource.wardF`), `P = nearProjection W`,
`𝕊 = I - 2iηℝ` and `c₀ = (2iη)⁻¹`:
* `nearSel_conj_mul_nearSel`: `ιι* = P`;
* `iota_wardF`: `ιF = -c₀ P𝕊`, and `iota_wardF_conj`: `(ιF)* = c₀ 𝕊*P`;
* `wardF_conj_mul`: `F*F = (4η²)⁻¹ 𝕊*P𝕊` (`= P'/(4η²)`);
* `bilinear_mulVec_one`: `(Au)*(Bv) = u*(A*B)v`, the vector form used in the assembly.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveCovariance
open scoped ComplexConjugate

variable {W : ℕ}

/-- `ιι* = P`. -/
theorem nearSel_conj_mul_nearSel : (nearSel W)ᴴ * nearSel W = nearProjection W := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, nearSel, nearProjection,
    Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> by_cases hxy : x = y <;>
    simp [hi, hj, hxy, eq_comm]

/-- `ℝ - c₀ = -c₀𝕊`. -/
theorem resolvent_sub_cZero (b E : ℝ) (hη : etaZ b E ≠ 0)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    twoPortResolvent b E XX - cZero b E • 1 = -cZero b E • twoPortScattering b E XX := by
  have hη' : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη
  have h : cZero b E * (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [cZero]; push_cast; field_simp
  rw [twoPortScattering, smul_sub, smul_smul, neg_mul, h, neg_smul, neg_one_smul]
  abel

/-- `ιF = -c₀ P𝕊`. -/
theorem iota_wardF (b E : ℝ) (hη : etaZ b E ≠ 0) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (nearSel W)ᴴ * wardF b E XX = -cZero b E • (nearProjection W * twoPortScattering b E XX) := by
  rw [wardF, ← Matrix.mul_assoc, nearSel_conj_mul_nearSel, resolvent_sub_cZero b E hη,
    Matrix.mul_smul]

/-- `(ιF)* = c₀ 𝕊*P`. -/
theorem iota_wardF_conj (b E : ℝ) (hη : etaZ b E ≠ 0)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ((nearSel W)ᴴ * wardF b E XX)ᴴ = cZero b E • ((twoPortScattering b E XX)ᴴ * nearProjection W) := by
  have hP : (nearProjection W)ᴴ = nearProjection W := by
    rw [← nearSel_conj_mul_nearSel, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [iota_wardF b E hη, conjTranspose_smul, conjTranspose_mul, hP, star_neg]
  have : star (cZero b E) = -cZero b E := conj_cZero b E
  rw [this, neg_neg]

/-- `F*F = (4η²)⁻¹ 𝕊*P𝕊`. -/
theorem wardF_conj_mul (b E : ℝ) (hη : etaZ b E ≠ 0) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (wardF b E XX)ᴴ * wardF b E XX = ((4 * etaZ b E ^ 2 : ℝ) : ℂ)⁻¹ •
      ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) := by
  have hc : star (cZero b E) * cZero b E = ((4 * etaZ b E ^ 2 : ℝ) : ℂ)⁻¹ := by
    have : star (cZero b E) = -cZero b E := conj_cZero b E
    rw [this, neg_mul, ← sq, cZero_sq b E hη, neg_neg]
  rw [wardF, resolvent_sub_cZero b E hη, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (nearSel W)ᴴ, nearSel_conj_mul_nearSel, conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, star_neg, neg_mul_neg, hc,
    Matrix.mul_assoc]

/-- `(Au)*1(Bv) = u*(A*B)v` for rectangular `A, B`. -/
theorem bilinear_mulVec_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A B : Matrix m n ℂ) (u v : n → ℂ) :
    bilinear (A *ᵥ u) 1 (B *ᵥ v) = bilinear u (Aᴴ * B) v := by
  rw [← bilinear_sandwich' u v A 1 B, Matrix.one_mul]

end BlockBand.SourceProcess.FullSourceCovariance
