module

public import BlockBand.SourceProcess.ContractingWords.SlotPins
public import BlockBand.SourceProcess.ContractingWords.IdProjAlg
public import BlockBand.SourceProcess.FullSourceCovariance.Assembly

/-!
# The projected separator: exact algebra

* `farQ = ℝ₁₂` (the far block of `ℝ = (z - 𝕏)⁻¹`), `colQ Q j` its columns, `frob Q = Σ|Q_ij|²`;
* `projGamma_eq`: `projGamma = ι*(CC*)ι`, `C = Δℝ₁₂` (every sample, no a.s. qualifier);
* `bilinear_cqqc`: `x*(DQQ*D*)x' = Σ_j (x*Dq_j)·conj(x'*Dq_j)`;
* `vecNorm_mulVec_sq_le_frob`: `‖Mz‖² ≤ frob M ‖z‖²` (Cauchy–Schwarz); `frob_conjTranspose`;
* `trace_mul_conjTranspose_eq_frob`, `frob_farQ`: `Tr ℝ₁₂ℝ₁₂* = frob ℝ₁₂ = g/(4η²)` (Hermitian `𝕏`, bulk `E`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.ContractingWords BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `ℝ₁₂`, the near–far block of `ℝ = (z - 𝕏)⁻¹`. -/
def farQ (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  portBlock (twoPortResolvent b E XX) 0 1

/-- Column `j` of `Q`. -/
def colQ (Q : Matrix (Fin W) (Fin W) ℂ) (j : Fin W) : Fin W → ℂ := fun i => Q i j

/-- The squared Hilbert–Schmidt norm `Σ|Q_ij|²`. -/
def frob {m n : Type*} [Fintype m] [Fintype n] (Q : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖Q i j‖ ^ 2

theorem frob_nonneg {m n : Type*} [Fintype m] [Fintype n] (Q : Matrix m n ℂ) : 0 ≤ frob Q := by
  unfold frob; positivity

/-- `ιN(ιN)* = LL* + CC*`. -/
theorem nearSel_transport_sq (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (y : LayerSample W .oneBlockOnePort) :
    nearSel W * freshTransport b E XX y * (freshTransport b E XX y)ᴴ * (nearSel W)ᴴ =
      freshU b E (nearSchur (boundaryZ b E) XX) y +
        freshDelta b E (nearSchur (boundaryZ b E) XX) y * farQ b E XX *
          (freshDelta b E (nearSchur (boundaryZ b E) XX) y * farQ b E XX)ᴴ := by
  have e : nearSel W * freshTransport b E XX y * (freshTransport b E XX y)ᴴ * (nearSel W)ᴴ =
      (nearSel W * freshTransport b E XX y) * (nearSel W * freshTransport b E XX y)ᴴ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, freshU]
  ext x x'
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.mul_apply, Matrix.mul_apply]
  simp only [conjTranspose_apply, nearSel_mul_apply]
  simp [freshTransport, farQ]

/-- **`projGamma = ι*(CC*)ι`**, `C = Δℝ₁₂`. -/
theorem projGamma_eq (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (y : LayerSample W .oneBlockOnePort) :
    projGamma b E XX y = (nearSel W)ᴴ * (freshDelta b E (nearSchur (boundaryZ b E) XX) y *
      farQ b E XX * (freshDelta b E (nearSchur (boundaryZ b E) XX) y * farQ b E XX)ᴴ) *
        nearSel W := by
  rw [projGamma, transportedSep_proj, ← FullSourceCovariance.nearSel_conj_mul_nearSel]
  have e : (nearSel W)ᴴ * nearSel W * transportedSep b E XX .id y * ((nearSel W)ᴴ * nearSel W) =
      (nearSel W)ᴴ * (nearSel W * freshTransport b E XX y * (freshTransport b E XX y)ᴴ *
        (nearSel W)ᴴ) * nearSel W := by
    simp only [transportedSep, sepOf, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, nearSel_transport_sq, Matrix.mul_add, Matrix.add_mul]
  abel

theorem bilinear_mul_conjTranspose {n : Type*} [Fintype n] (x x' : n → ℂ) (M : Matrix n n ℂ) :
    bilinear x (M * Mᴴ) x' =
      ∑ j, (star x ⬝ᵥ fun i => M i j) * star (star x' ⬝ᵥ fun i => M i j) := by
  simp only [bilinear, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, Finset.mul_sum,
    Finset.sum_mul, star_sum, star_mul', star_star, Pi.star_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem mulVec_colQ (D Q : Matrix (Fin W) (Fin W) ℂ) (j : Fin W) :
    D *ᵥ colQ Q j = fun i => (D * Q) i j := by
  funext i; simp [mulVec, dotProduct, Matrix.mul_apply, colQ]

/-- `x*(DQQ*D*)x' = Σ_j (x*Dq_j)·conj(x'*Dq_j)`. -/
theorem bilinear_cqqc (x x' : Fin W → ℂ) (D Q : Matrix (Fin W) (Fin W) ℂ) :
    bilinear x (D * Q * (D * Q)ᴴ) x' =
      ∑ j, bilinear x D (colQ Q j) * star (bilinear x' D (colQ Q j)) := by
  rw [bilinear_mul_conjTranspose]
  simp only [bilinear, mulVec_colQ]

/-- `Σ_j ‖q_j‖² = frob Q`. -/
theorem sum_vecNorm_colQ_sq (Q : Matrix (Fin W) (Fin W) ℂ) :
    ∑ j, vecNorm (colQ Q j) ^ 2 = frob Q := by
  simp only [vecNorm_sq_eq, colQ, frob]
  exact Finset.sum_comm

theorem frob_conjTranspose {m n : Type*} [Fintype m] [Fintype n] (Q : Matrix m n ℂ) :
    frob Qᴴ = frob Q := by
  simp only [frob, conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-- Cauchy–Schwarz: `‖Mz‖² ≤ frob M ‖z‖²`. -/
theorem vecNorm_mulVec_sq_le_frob {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (z : n → ℂ) : vecNorm (M *ᵥ z) ^ 2 ≤ frob M * vecNorm z ^ 2 := by
  rw [vecNorm_sq_eq, frob, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_star_dotProduct_le (star (fun j => M i j)) z
  rw [star_star] at h
  have hr : vecNorm (star fun j => M i j) ^ 2 = ∑ j, ‖M i j‖ ^ 2 := by
    rw [vecNorm_sq_eq]; simp
  have h0 : 0 ≤ ‖(M *ᵥ z) i‖ := norm_nonneg _
  have : ‖(M *ᵥ z) i‖ ^ 2 ≤ (vecNorm (star fun j => M i j) * vecNorm z) ^ 2 :=
    pow_le_pow_left₀ h0 h 2
  rw [mul_pow, hr] at this
  exact this

theorem vecNorm_mulVec_le_frob {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (z : n → ℂ) : vecNorm (M *ᵥ z) ≤ Real.sqrt (frob M) * vecNorm z := by
  rw [← Real.sqrt_sq (vecNorm_nonneg (M *ᵥ z)), ← Real.sqrt_sq (vecNorm_nonneg z),
    ← Real.sqrt_mul (frob_nonneg M)]
  exact Real.sqrt_le_sqrt (vecNorm_mulVec_sq_le_frob M z)

/-- `Tr QQ* = frob Q`. -/
theorem trace_mul_conjTranspose_eq_frob (Q : Matrix (Fin W) (Fin W) ℂ) :
    (Q * Qᴴ).trace = ((frob Q : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, frob]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

/-- **`Tr ℝ₁₂ℝ₁₂* = g/(4η²)`** (far absorption `RYR* = ηℝ₁₂ℝ₁₂*`, `Tr RYR* = Tr R*YR`). -/
theorem frob_farQ {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian) :
    frob (farQ b E XX) =
      conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) /
        (4 * etaZ b E ^ 2) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hY := FullSource.nearSchur_passive (z := boundaryZ b E) hη hXX
  have hfar := FullSource.far_absorption b E hXX hη
  have htr := congrArg Matrix.trace hfar
  rw [trace_tildeQ hb0 hb h1 h2 hY, Matrix.trace_smul, ← farQ, trace_mul_conjTranspose_eq_frob,
    smul_eq_mul] at htr
  have hg : conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) =
      4 * etaZ b E * (passiveQ b E (nearSchur (boundaryZ b E) XX)).trace.re := by
    simp [conductanceOf, passiveTransmission, Matrix.trace_smul]
  have hre := congrArg Complex.re htr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  rw [hg, hre]
  field_simp

end BlockBand.SourceProcess.ProjSeparator
