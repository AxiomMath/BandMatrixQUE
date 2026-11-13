module

public import BlockBand.SourceProcess.PositiveResponse
public import BlockBand.SourceProcess.CurrentAlgebra

/-!
# Ordered source Gram identities

For a frame `V`, a projection `P` and `P' = P + VDVᴴ`, the sandwiches of `V` between `P` and `P'`
are the ordered Gram expressions `C0 = B + MDM`, `C1 = B + MDB`, `C2 = B + BDB` with
`M = VᴴV`, `B = VᴴPV`; the far Gram is `M - B`, and the projection constraint gives the quadratic
feasibility identity.
-/

@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess
open Matrix
open scoped ComplexOrder

/-- Full column Gram matrix M=VᴴV. -/
def sourceGram {ι κ : Type*} [Fintype ι] (V : Matrix ι κ ℂ) : Matrix κ κ ℂ :=
  Vᴴ * V

/-- Near Gram matrix B=VᴴPV. -/
def nearGram {ι κ : Type*} [Fintype ι] (P : Matrix ι ι ℂ)
    (V : Matrix ι κ ℂ) : Matrix κ κ ℂ := Vᴴ * P * V

/-- The transported projection candidate `P' = P + VDVᴴ`. -/
def gramProjection {ι κ : Type*} [Fintype κ]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ) :
    Matrix ι ι ℂ := P + V * D * Vᴴ

/-- Ordered C0=B+MDM. -/
def gramC0 {κ : Type*} [Fintype κ] (M B D : Matrix κ κ ℂ) := B + M * D * M
/-- Ordered C1=B+MDB, generally non-Hermitian. -/
def gramC1 {κ : Type*} [Fintype κ] (M B D : Matrix κ κ ℂ) := B + M * D * B
/-- Ordered C2=B+BDB. -/
def gramC2 {κ : Type*} [Fintype κ] (B D : Matrix κ κ ℂ) := B + B * D * B

/-- The `P'` sandwich gives `C0` (no invertibility needed). -/
theorem gram_sandwich_C0 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ) :
    Vᴴ * gramProjection P V D * V = gramC0 (sourceGram V) (nearGram P V) D := by
  simp [gramProjection, gramC0, sourceGram, nearGram, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- The order `P'`, `P` gives `C1`. -/
theorem gram_sandwich_C1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hP : P * P = P) :
    Vᴴ * gramProjection P V D * P * V =
      gramC1 (sourceGram V) (nearGram P V) D := by
  simp [gramProjection, gramC1, sourceGram, nearGram, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, hP]

/-- The reverse order `P`, `P'` gives the adjoint of `C1`. -/
theorem gram_sandwich_C1_adjoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hP : P * P = P) (hPH : Pᴴ = P) (hDH : Dᴴ = D) :
    Vᴴ * P * gramProjection P V D * V =
      (gramC1 (sourceGram V) (nearGram P V) D)ᴴ := by
  simp [gramProjection, gramC1, sourceGram, nearGram, Matrix.mul_add, Matrix.add_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, hP, hPH, hDH]

/-- Both projected frames give C2. -/
theorem gram_sandwich_C2 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hP : P * P = P) :
    Vᴴ * P * gramProjection P V D * P * V = gramC2 (nearGram P V) D := by
  simp [gramProjection, gramC2, nearGram, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hP]

/-- The near-frame Gram is B, with all projection factors retained. -/
theorem near_frame_gram {ι κ : Type*} [Fintype ι]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (hP : P * P = P) :
    Vᴴ * P * P * P * V = nearGram P V := by
  simp [nearGram, Matrix.mul_assoc, hP]

/-- Feasibility includes positivity of M at every rank boundary. -/
theorem sourceGram_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
    (V : Matrix ι κ ℂ) : (sourceGram V).PosSemidef :=
  posSemidef_conjTranspose_mul_self V

/-- A positive near projection gives positive B, also for singular frames. -/
theorem nearGram_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) (V : Matrix ι κ ℂ) :
    (nearGram P V).PosSemidef := hP.conjTranspose_mul_mul_same V

/-- The far Gram is `M - B`. -/
theorem far_gram_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) :
    Vᴴ * (1 - P) * V = sourceGram V - nearGram P V := by
  simp [sourceGram, nearGram, Matrix.mul_sub, Matrix.sub_mul]

/-- Feasibility includes positivity of M-B at singular boundaries. -/
theorem farGram_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (hP : (1 - P).PosSemidef) :
    (sourceGram V - nearGram P V).PosSemidef := by
  rw [← far_gram_eq P V]
  exact hP.conjTranspose_mul_mul_same V

/-- The current contribution with its signature factor. -/
theorem gram_current_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ) :
    fullCurrent P (gramProjection P V D) = V * D * Vᴴ := by
  simp [fullCurrent, gramProjection]

/-- The projection constraint implies the quadratic Gram feasibility identity (no inverse of `M`
needed). -/
theorem gram_projection_constraint {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (D : Matrix κ κ ℂ)
    (hP : P * P = P)
    (hPprime : gramProjection P V D * gramProjection P V D = gramProjection P V D) :
    nearGram P V * D * sourceGram V + sourceGram V * D * nearGram P V +
      sourceGram V * D * sourceGram V * D * sourceGram V =
      sourceGram V * D * sourceGram V := by
  have h := congrArg (fun A => Vᴴ * A * V) hPprime
  simp only [gramProjection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hP] at h
  have h' : nearGram P V +
      (nearGram P V * D * sourceGram V + sourceGram V * D * nearGram P V +
        sourceGram V * D * sourceGram V * D * sourceGram V) =
      nearGram P V + sourceGram V * D * sourceGram V := by
    simp only [nearGram, sourceGram, Matrix.mul_assoc]
    convert h using 1
    abel
  exact add_left_cancel h'

end BlockBand.SourceProcess
