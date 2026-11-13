module

public import BlockBand.Transmission.PositiveResolvent

/-!
# Constructive two-port Schur passivity

Eliminating the far port of a Hermitian two-port block with the matched pencil `portPencil` gives
the near Schur input `passiveSchurInput`, whose imaginary part is computed exactly and is negative
semidefinite. Consequences: invertibility, the dissipative balance, the scattering identity and
the transmission constraints of the near Schur matrix (`passiveSchur_transmission_constraints`).
-/

@[expose] public section
noncomputable section
namespace BlockBand.Transmission
open Matrix
open scoped ComplexOrder

/-- Matched far-port pencil before elimination. -/
def portPencil {ι : Type*} [DecidableEq ι] (D : Matrix ι ι ℂ) (z : ℂ) :=
  z • (1 : Matrix ι ι ℂ) - D

/-- Exact matrix imaginary part at a Hermitian port input. -/
theorem matrixImaginaryPart_portPencil {ι : Type*} [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) (z : ℂ) :
    matrixImaginaryPart (portPencil D z) = z.im • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    apply Complex.ext <;> simp [portPencil, matrixImaginaryPart, hD.eq]
    ring
  · simp [portPencil, matrixImaginaryPart, hD.eq, hij]

/-- The far inverse exists for every Hermitian block and positive port height. -/
theorem portPencil_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (portPencil D z) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  rw [matrixImaginaryPart_portPencil D hD z]
  exact Matrix.PosDef.one.smul hz

/-- Imaginary part commutes with a rectangular congruence. -/
theorem matrixImaginaryPart_congruence {ι κ : Type*} [Fintype ι]
    (B : Matrix ι κ ℂ) (R : Matrix ι ι ℂ) :
    matrixImaginaryPart (Bᴴ * R * B) = Bᴴ * matrixImaginaryPart R * B := by
  simp only [matrixImaginaryPart, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- The eliminated near Schur input, keeping both rectangular bond orders. -/
def passiveSchurInput {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix κ κ ℂ) (B : Matrix ι κ ℂ) (D : Matrix ι ι ℂ) (z : ℂ) :=
  A + Bᴴ * (portPencil D z)⁻¹ * B

/-- The imaginary part of the Schur input: `Im(A + Bᴴ P⁻¹ B) = Bᴴ Im(P⁻¹) B` for Hermitian `A`,
`P = portPencil D z`. -/
theorem passiveSchurInput_imaginary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix κ κ ℂ) (hA : A.IsHermitian) (B : Matrix ι κ ℂ)
    (D : Matrix ι ι ℂ) (z : ℂ) :
    matrixImaginaryPart (passiveSchurInput A B D z) =
      Bᴴ * matrixImaginaryPart (portPencil D z)⁻¹ * B := by
  rw [← matrixImaginaryPart_congruence]
  simp only [passiveSchurInput, matrixImaginaryPart, Matrix.conjTranspose_add, hA.eq]
  congr 1
  abel

/-- Positive far lead absorption constructs positive near Schur dissipation. -/
theorem passiveSchurInput_negativeImaginary_posSemidef
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix κ κ ℂ) (hA : A.IsHermitian) (B : Matrix ι κ ℂ)
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    (-matrixImaginaryPart (passiveSchurInput A B D z)).PosSemidef := by
  have hu := portPencil_isUnit D hD hz
  have hpos : (matrixImaginaryPart (portPencil D z)).PosSemidef := by
    rw [matrixImaginaryPart_portPencil D hD z]
    exact Matrix.PosSemidef.one.smul hz.le
  have hr := neg_matrixImaginaryPart_nonsing_inv_posSemidef (portPencil D z)
    ((Matrix.isUnit_iff_isUnit_det _).mp hu) hpos
  rw [passiveSchurInput_imaginary A hA B D z]
  have hneg : -(Bᴴ * matrixImaginaryPart (portPencil D z)⁻¹ * B) =
      Bᴴ * (-matrixImaginaryPart (portPencil D z)⁻¹) * B := by
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  rw [hneg]
  exact hr.conjTranspose_mul_mul_same B

/-- Exact additivity of matrix imaginary parts for arbitrary nonnormal matrices. -/
theorem matrixImaginaryPart_sub {ι : Type*} (A B : Matrix ι ι ℂ) :
    matrixImaginaryPart (A - B) = matrixImaginaryPart A - matrixImaginaryPart B := by
  simp only [matrixImaginaryPart, Matrix.conjTranspose_sub]
  module

/-- The near pencil has imaginary part eta I plus its passive absorber. -/
theorem matrixImaginaryPart_portPencil_general {ι : Type*} [DecidableEq ι]
    (X : Matrix ι ι ℂ) (z : ℂ) :
    matrixImaginaryPart (portPencil X z) =
      z.im • (1 : Matrix ι ι ℂ) - matrixImaginaryPart X := by
  rw [portPencil, matrixImaginaryPart_sub]
  have h := matrixImaginaryPart_portPencil (0 : Matrix ι ι ℂ) Matrix.isHermitian_zero z
  simpa only [portPencil, sub_zero] using congrArg (fun M => M - matrixImaginaryPart X) h

/-- Positive-height near inverse constructed from the eliminated input. -/
theorem passiveSchur_near_isUnit {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (hA : A.IsHermitian) (B : Matrix ι κ ℂ)
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (portPencil (passiveSchurInput A B D z) z) := by
  have hY := passiveSchurInput_negativeImaginary_posSemidef A hA B D hD hz
  apply isUnit_of_matrixImaginaryPart_posDef
  rw [matrixImaginaryPart_portPencil_general, sub_eq_add_neg, add_comm]
  exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hz)

/-- Reconstruct the exact anti-Hermitian difference from its matrix imaginary part. -/
theorem matrix_difference_eq_twoI_imaginaryPart {ι : Type*}
    (M : Matrix ι ι ℂ) :
    M - Mᴴ = (2 * Complex.I) • matrixImaginaryPart M := by
  have hc : (2 * Complex.I) * (-Complex.I / 2) = 1 := by
    calc
      _ = -(Complex.I * Complex.I) := by ring
      _ = 1 := by rw [Complex.I_mul_I]; ring
  rw [matrixImaginaryPart, smul_smul, hc, one_smul]

/-- The near-pencil balance used by physical scattering, derived rather
than supplied: K-K*=2i eta I+2iY, with Y=-Im X. -/
theorem passiveSchur_near_balance {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (B : Matrix ι κ ℂ) (D : Matrix ι ι ℂ) (z : ℂ) :
    let X := passiveSchurInput A B D z
    let K := portPencil X z
    K - star K = (2 * Complex.I * (z.im : ℂ)) • (1 : Matrix κ κ ℂ) +
      (2 * Complex.I) • (-matrixImaginaryPart X) := by
  dsimp only
  rw [Matrix.star_eq_conjTranspose, matrix_difference_eq_twoI_imaginaryPart,
    matrixImaginaryPart_portPencil_general, sub_eq_add_neg, smul_add]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- Physical finite scattering T=4 eta R*YR=I-S*S for a Hermitian
rectangular Schur input. Both inverses and the dissipative balance are constructed. -/
theorem passiveSchur_scattering_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (hA : A.IsHermitian) (B : Matrix ι κ ℂ)
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    let X := passiveSchurInput A B D z
    let R := (portPencil X z)⁻¹
    1 - star (1 - (2 * Complex.I * (z.im : ℂ)) • R) *
      (1 - (2 * Complex.I * (z.im : ℂ)) • R) =
      (4 * (z.im : ℂ)) • (star R * (-matrixImaginaryPart X) * R) := by
  dsimp only
  apply passive_scattering_physical
  · exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (passiveSchur_near_isUnit A hA B D hD hz))
  · exact passiveSchur_near_balance A B D z

/-- Construct both finite transmission constraints 0<=T<=I from Hermitian
blocks and Im z>0; the passivity, the inverses and the scattering identity are all derived. -/
theorem passiveSchur_transmission_constraints {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (hA : A.IsHermitian) (B : Matrix ι κ ℂ)
    (D : Matrix ι ι ℂ) (hD : D.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    let R := (portPencil (passiveSchurInput A B D z) z)⁻¹
    let S := 1 - (2 * Complex.I * (z.im : ℂ)) • R
    (1 - star S * S).PosSemidef ∧ (1 - (1 - star S * S)).PosSemidef := by
  dsimp only
  constructor
  · rw [passiveSchur_scattering_identity A hA B D hD hz]
    have hc : (0 : ℂ) ≤ 4 * (z.im : ℂ) :=
      Complex.nonneg_iff.mpr ⟨by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hz.le, by simp⟩
    exact ((passiveSchurInput_negativeImaginary_posSemidef A hA B D hD hz).conjTranspose_mul_mul_same _).smul hc
  · exact passive_transmission_complement_posSemidef _ z.im

end BlockBand.Transmission
