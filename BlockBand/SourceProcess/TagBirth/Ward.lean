module

public import BlockBand.SourceProcess.FullSource.WardIdentity
public import BlockBand.SourceProcess.FullSource.DeltaMeanStrict
public import BlockBand.SourceProcess.TagBirth.Interface

/-!
# The Ward identity of the injected tag

Deterministic statements, for a Hermitian old two-port `𝕏`, `X = nearSchur z 𝕏`, `η > 0` and a
fresh sample with `A` Hermitian and `B` invertible:
* `freshD_mul_conjTranspose`: `D₊D₊* = 𝒢₁₂𝒢₁₂* + (𝒢₁₁Kℝ₁₂)(𝒢₁₁Kℝ₁₂)*`;
* `eta_trace_freshD`: `η Tr D₊*D₊ = -Im Tr 𝒢₁₁`;
* `dStar_mul_eta`: `d_* η = -Im a` (from `z + E = -(1-b)a`);
* `norm_birthTrace_sub_le`: `|W⁻¹Tr D₊*D₊ - d_*| ≤ η⁻¹ |⟨𝒢₁₁⟩ - a|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.TagBirth

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-- `D₊D₊* = 𝒢₁₂𝒢₁₂* + (𝒢₁₁Kℝ₁₂)(𝒢₁₁Kℝ₁₂)*`. -/
theorem freshD_mul_conjTranspose (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshD b E XX ω * (freshD b E XX ω)ᴴ =
      g12 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω *
          (g12 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω)ᴴ +
        g11 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω *
            (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX) *
            portBlock (twoPortResolvent b E XX) 0 1 *
          (g11 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω *
            (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX) *
            portBlock (twoPortResolvent b E XX) 0 1)ᴴ := by
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, freshD]
  simp
  rfl

/-- **`η Tr D₊*D₊ = -Im Tr 𝒢₁₁`.** -/
theorem eta_trace_freshD (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    ((etaZ b E : ℝ) : ℂ) * ((freshD b E XX ω)ᴴ * freshD b E XX ω).trace =
      -(((g11 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω).trace.im : ℝ) : ℂ) := by
  set z := boundaryZ b E
  set X := nearSchur z XX
  set K : Matrix (Fin W) (Fin W) ℂ := z • 1 - X
  set R := passiveResolvent b E X
  set Q := portBlock (twoPortResolvent b E XX) 0 1
  set G1 := g11 E z X ω
  set G2 := g12 E z X ω
  set Y := passiveY X
  have hz : 0 < z.im := hη
  have hY : Y.PosSemidef := nearSchur_passive hz hXX
  have hK : IsUnit K := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  have hKR : K * R = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hK)
  have hfar : R * Y * Rᴴ = ((etaZ b E : ℝ) : ℂ) • (Q * Qᴴ) := far_absorption b E hXX hη
  have hKY : ((etaZ b E : ℝ) : ℂ) • (K * Q * (K * Q)ᴴ) = Y := by
    have : K * (R * Y * Rᴴ) * Kᴴ = Y := by
      rw [show K * (R * Y * Rᴴ) * Kᴴ = (K * R) * Y * (K * R)ᴴ by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc], hKR, Matrix.one_mul,
        conjTranspose_one, Matrix.mul_one]
    rw [hfar] at this
    rw [← this, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have him := im_g11 E hz hY hA hB
  have hD := freshD_mul_conjTranspose b E XX ω
  have h3 : ((etaZ b E : ℝ) : ℂ) * ((freshD b E XX ω)ᴴ * freshD b E XX ω).trace =
      ((etaZ b E : ℝ) : ℂ) * (G2 * G2ᴴ).trace + (G1 * Y * G1ᴴ).trace := by
    rw [Matrix.trace_mul_comm, hD, Matrix.trace_add, mul_add, ← hKY, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    congr 3
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl
  have h1 := congrArg Matrix.trace him
  rw [Matrix.trace_sub, Matrix.trace_conjTranspose, Matrix.trace_neg, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at h1
  have h2 : G1.trace - star G1.trace = 2 * ((G1.trace.im : ℝ) : ℂ) * Complex.I := by
    rw [Complex.star_def, Complex.sub_conj]; push_cast; ring
  rw [h2] at h1
  have hzη : ((z.im : ℝ) : ℂ) = ((etaZ b E : ℝ) : ℂ) := rfl
  rw [hzη] at h1
  rw [h3]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(Complex.I / 2)) * h1 +
    ((G1 * Y * G1ᴴ).trace + ((etaZ b E : ℝ) : ℂ) * (G2 * G2ᴴ).trace + (G1.trace.im : ℂ)) * hI

/-- `d_* η = -Im a`, from `z + E = -(1-b)a`. -/
theorem dStar_mul_eta {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    dStar b * etaZ b E = -(matchedA E).im := by
  have h := congrArg Complex.im (boundaryZ_add_E (b := b) h1 h2)
  simp at h
  have hb1 : (1 - b) ≠ 0 := by linarith
  rw [dStar, etaZ, h]
  field_simp
  ring

/-- **The birth value at one fresh sample:** `|W⁻¹Tr D₊*D₊ - d_*| ≤ η⁻¹ |⟨𝒢₁₁⟩ - a|`. -/
theorem norm_birthTrace_sub_le {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian)
    {ω : LayerSample W .oneBlockOnePort} (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    ‖(W : ℂ)⁻¹ * ((freshD b E XX ω)ᴴ * freshD b E XX ω).trace - (dStar b : ℂ)‖ ≤
      (etaZ b E)⁻¹ * ‖physTr b E (nearSchur (boundaryZ b E) XX) ω - matchedA E‖ := by
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) h1 h2
  set t := (g11 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω).trace
  have hT := eta_trace_freshD b E hXX hη hA hB
  have hηc : ((etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hTr : ((freshD b E XX ω)ᴴ * freshD b E XX ω).trace = -((t.im : ℝ) : ℂ) / (etaZ b E : ℂ) := by
    rw [eq_div_iff hηc, mul_comm, hT]
  have hph : physTr b E (nearSchur (boundaryZ b E) XX) ω = (W : ℂ)⁻¹ * t := rfl
  have hd := dStar_mul_eta (b := b) hb h1 h2
  have key : (W : ℂ)⁻¹ * ((freshD b E XX ω)ᴴ * freshD b E XX ω).trace - (dStar b : ℂ) =
      ((-(etaZ b E)⁻¹ * ((W : ℂ)⁻¹ * t - matchedA E).im : ℝ) : ℂ) := by
    have him : ((W : ℂ)⁻¹ * t - matchedA E).im = (W : ℝ)⁻¹ * t.im - (matchedA E).im := by
      rw [Complex.sub_im, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
    rw [him, hTr]
    have hd' : (dStar b : ℂ) = -((matchedA E).im : ℂ) / (etaZ b E : ℂ) := by
      rw [eq_div_iff hηc]; exact_mod_cast hd
    rw [hd']
    push_cast
    field_simp
    ring
  rw [key, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_of_pos hη, hph]
  exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (inv_nonneg.mpr hη.le)

end BlockBand.SourceProcess.TagBirth
