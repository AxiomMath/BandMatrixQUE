module

public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartSigma
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Every frame with a feasible Gram pair satisfies the two-projection constraint

Write `P' = P + V𝖣Vᴴ` and `K = P'P' - P'`. With `W = [V, PV]`, `Y = [[𝖣M𝖣 - 𝖣, 𝖣], [𝖣, 0]]`
and `Γ = WᴴW = [[M, B], [B, B]]` (`P` Hermitian idempotent), `K = WYWᴴ` (`defect_eq`), so
`Tr(K K) = Tr(YΓYΓ)` depends only on `(M, B)`. A feasible realization has `K = 0`; hence every
frame `V` with the same Gram pair has `Tr(KᴴK) = Tr(KK) = 0`, i.e. `K = 0`
(`twoProjection_of_feasible`). The trace clause is `Tr(𝖣M) = 0`, also a function of `M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder

variable {c : Type*} [Fintype c]
variable {ι : Type*} [Fintype ι]

/-- `Y(M) = [[𝖣M𝖣 - 𝖣, 𝖣], [𝖣, 0]]`. -/
def defectCore (D M : Matrix c c ℂ) : Matrix (c ⊕ c) (c ⊕ c) ℂ :=
  fromBlocks (D * M * D - D) D D 0

/-- `Γ = [[M, B], [B, B]]`. -/
def gramBlock (G : Matrix c c ℂ × Matrix c c ℂ) : Matrix (c ⊕ c) (c ⊕ c) ℂ :=
  fromBlocks G.1 G.2 G.2 G.2

/-- `W = [V, PV]`. -/
def defectFrame (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) : Matrix ι (c ⊕ c) ℂ :=
  fromCols V (P * V)

/-- The projection defect `K = P'P' - P'`. -/
def defect (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) (D : Matrix c c ℂ) : Matrix ι ι ℂ :=
  gramProjection P V D * gramProjection P V D - gramProjection P V D

theorem defect_eq {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P) (V : Matrix ι c ℂ)
    (D : Matrix c c ℂ) :
    defect P V D = defectFrame P V * defectCore D (sourceGram V) * (defectFrame P V)ᴴ := by
  simp only [defect, gramProjection, defectFrame, defectCore, sourceGram,
    fromCols_mul_fromBlocks, conjTranspose_fromCols_eq_fromRows_conjTranspose,
    fromCols_mul_fromRows, conjTranspose_mul, hPH, Matrix.mul_zero, add_zero]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    hPP]
  abel

omit [Fintype c] in
theorem defectFrame_gram {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P)
    (V : Matrix ι c ℂ) :
    (defectFrame P V)ᴴ * defectFrame P V = gramBlock (gramPair P V) := by
  simp only [defectFrame, gramBlock, gramPair, sourceGram, nearGram,
    conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, conjTranspose_mul,
    hPH]
  congr 1 <;> simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P, hPP]

theorem trace_defect_sq {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P)
    (V : Matrix ι c ℂ) (D : Matrix c c ℂ) :
    trace (defect P V D * defect P V D) =
      trace (defectCore D (gramPair P V).1 * gramBlock (gramPair P V) *
        defectCore D (gramPair P V).1 * gramBlock (gramPair P V)) := by
  rw [defect_eq hPH hPP, ← defectFrame_gram hPH hPP]
  set W := defectFrame P V
  set Y := defectCore D (sourceGram V)
  have e : W * Y * Wᴴ * (W * Y * Wᴴ) = W * (Y * (Wᴴ * W) * Y * Wᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [e, trace_mul_comm]
  simp only [gramPair, Matrix.mul_assoc]
  rfl

omit [Fintype ι] in
theorem defect_herm {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) {D : Matrix c c ℂ} (hDH : Dᴴ = D)
    (V : Matrix ι c ℂ) : (gramProjection P V D)ᴴ = gramProjection P V D := by
  simp [gramProjection, conjTranspose_mul, hPH, hDH, Matrix.mul_assoc]

theorem trace_gramProjection (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) (D : Matrix c c ℂ) :
    (gramProjection P V D).trace = P.trace + (D * (gramPair P V).1).trace := by
  rw [gramProjection, trace_add, gramPair, sourceGram, Matrix.mul_assoc, trace_mul_comm V,
    ← Matrix.mul_assoc, trace_mul_comm]

/-- **Every frame realizing a feasible Gram pair satisfies the two-projection constraint.** -/
theorem twoProjection_of_feasible {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P)
    {D : Matrix c c ℂ} (hD : IsSignature D) {V : Matrix ι c ℂ}
    (hG : GramFeasible D (gramPair P V)) : TwoProjection P D V := by
  obtain ⟨n, P₁, V₁, hP₁H, hP₁P, hV₁, hG₁⟩ := hG
  have hK₁ : defect P₁ V₁ D = 0 := sub_eq_zero.2 hV₁.2.1
  have htr := trace_defect_sq hP₁H hP₁P V₁ D
  rw [hK₁, Matrix.zero_mul, trace_zero, hG₁] at htr
  have hK : defect P V D = 0 := by
    have hKH : (defect P V D)ᴴ = defect P V D := by
      simp only [defect, conjTranspose_sub, conjTranspose_mul, defect_herm hPH hD.1]
    rw [← trace_conjTranspose_mul_self_eq_zero_iff, hKH, trace_defect_sq hPH hPP V D, ← htr]
  have htr₁ := trace_gramProjection P₁ V₁ D
  rw [hV₁.2.2, hG₁, left_eq_add] at htr₁
  refine ⟨defect_herm hPH hD.1 V, sub_eq_zero.1 hK, ?_⟩
  rw [trace_gramProjection, htr₁, add_zero]

end BlockBand.SourceProcess.HorizonExt
