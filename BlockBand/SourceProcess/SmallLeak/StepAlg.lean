module

public import BlockBand.SourceProcess.SmallLeak.Defs
public import BlockBand.SourceProcess.FullSourceStops.WordBounds
public import BlockBand.SourceProcess.FullSourceCovariance.WardTensor
public import BlockBand.Transmission.PassiveLayer.BlockAlgebra

/-!
# One layer of the omitted flux and of the omitted leakage: exact algebra

`N = [[L, Δℝ₀₁],[0, I]]` (near block first) keeps the far amplitudes, so for the far projection
`F = farEmbed A` (the paper's `A_-`): `NF = F + Z`, `Z = ι*Δ(ιℝF)` (`freshTransport_mul_farEmbed`).
This is the paper's `NA_-N* - A_- = [[CA_-C*, CA_-],[A_-C*, 0]]`, `C = Δℝ₁₂`, read on the input side.
Two exact consequences, for past Hermitian `M, Q`:
* flux (`flux_step_le`): `Re Tr F(N*(M-P)N + P)F ≤ Re Tr FMF + 2Re Tr Z*MF` when `M ⪯ 1`;
* leakage (`leak_step_eq`): `Re Tr F N*QN = Re Tr FQF + 2Re Tr Z*QF + Re Tr Z*QZ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## The far selector
-/

/-- `ι_f`: the far coordinates of a two-port vector. -/
def farSel (W : ℕ) : Matrix (Fin W) (Fin 2 × Fin W) ℂ :=
  fun x c => if c = (1, x) then 1 else 0

theorem farEmbed_eq (A : Matrix (Fin W) (Fin W) ℂ) : farEmbed A = (farSel W)ᴴ * A * farSel W := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [farEmbed, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, farSel,
    Prod.mk.injEq]
  by_cases hi : i = 1 <;> by_cases hj : j = 1 <;> simp [hi, hj]

theorem nearSel_mul_farSel_conj : nearSel W * (farSel W)ᴴ = 0 := by
  ext x y
  simp [nearSel, farSel, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem nearSel_mul_farEmbed (A : Matrix (Fin W) (Fin W) ℂ) : nearSel W * farEmbed A = 0 := by
  rw [farEmbed_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nearSel_mul_farSel_conj,
    Matrix.zero_mul, Matrix.zero_mul]

theorem nearProjection_mul_farEmbed (A : Matrix (Fin W) (Fin W) ℂ) :
    nearProjection W * farEmbed A = 0 := by
  rw [← FullSourceCovariance.nearSel_conj_mul_nearSel, Matrix.mul_assoc, nearSel_mul_farEmbed,
    Matrix.mul_zero]

/-- **The far columns of `N`**: `N ι_f* = ι_f* + ι*Δℝ₀₁`. -/
theorem freshTransport_mul_farSel_conj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (f : LayerSample W .oneBlockOnePort) :
    freshTransport b E XX f * (farSel W)ᴴ = (farSel W)ᴴ + (nearSel W)ᴴ *
      (freshDelta b E (nearSchur (boundaryZ b E) XX) f *
        (nearSel W * twoPortResolvent b E XX * (farSel W)ᴴ)) := by
  ext ⟨i, x⟩ y
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;>
    simp [freshTransport, nearSel, farSel, portBlock, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Matrix.one_apply, eq_comm]

/-- The near input `ιℝF` produced by the omitted far inputs (`ℝ₀₁A_-` in the far columns). -/
def leakInput (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Matrix (Fin W) (Fin 2 × Fin W) ℂ :=
  nearSel W * twoPortResolvent b E XX * F

/-- **`NF = F + ι*Δ(ιℝF)`** for `F = farEmbed A`. -/
theorem freshTransport_mul_farEmbed (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (f : LayerSample W .oneBlockOnePort) (A : Matrix (Fin W) (Fin W) ℂ) :
    freshTransport b E XX f * farEmbed A = farEmbed A + (nearSel W)ᴴ *
      (freshDelta b E (nearSchur (boundaryZ b E) XX) f * leakInput b E XX (farEmbed A)) := by
  rw [farEmbed_eq, leakInput, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    freshTransport_mul_farSel_conj]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

/-!
## The two exact one-step identities
-/

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem re_trace_conjTranspose (A : Matrix ι ι ℂ) : (Aᴴ).trace.re = A.trace.re := by
  rw [Matrix.trace_conjTranspose]; simp

/-- **The flux step.** If `NF = F + Z`, `PF = 0`, `PZ = Z`, `F = Fᴴ`, `P = Pᴴ`, `FPF = 0`,
`M = Mᴴ ⪯ 1`, then `Re Tr F(N*(M-P)N + P)F ≤ Re Tr FMF + 2Re Tr Z*MF`. -/
theorem flux_step_le {F Z P M N : Matrix ι ι ℂ} (hNF : N * F = F + Z) (hF : Fᴴ = F)
    (hPF : P * F = 0) (hPZ : P * Z = Z) (hP : Pᴴ = P) (hP2 : P * P = P) (hFPF : F * P * F = 0)
    (hM : Mᴴ = M)
    (hM1 : (1 - M).PosSemidef) :
    (F * (Nᴴ * (M - P) * N + P) * F).trace.re ≤
      (F * M * F).trace.re + 2 * (Zᴴ * M * F).trace.re := by
  have hFN : F * Nᴴ = (F + Z)ᴴ := by rw [← hNF, Matrix.conjTranspose_mul, hF]
  have e1 : F * (Nᴴ * (M - P) * N + P) * F = (F + Z)ᴴ * M * (F + Z) - (F + Z)ᴴ * P * (F + Z) +
      F * P * F := by
    rw [← hFN, ← hNF]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
  have hPFZ : P * (F + Z) = Z := by rw [Matrix.mul_add, hPF, hPZ, zero_add]
  have e2 : (F + Z)ᴴ * P * (F + Z) = Zᴴ * Z := by
    have : (F + Z)ᴴ * P * (F + Z) = (P * (F + Z))ᴴ * (P * (F + Z)) := by
      rw [Matrix.conjTranspose_mul, hP]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P (F + Z), hP2]
    rw [this, hPFZ]
  have e3 : (F + Z)ᴴ * M * (F + Z) = F * M * F + F * M * Z + Zᴴ * M * F + Zᴴ * M * Z := by
    rw [Matrix.conjTranspose_add, hF]
    simp only [Matrix.add_mul, Matrix.mul_add]; abel
  have e4 : (F * M * Z).trace.re = (Zᴴ * M * F).trace.re := by
    rw [← re_trace_conjTranspose (Zᴴ * M * F)]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hM, hF,
      Matrix.mul_assoc]
  have hneg : 0 ≤ (Zᴴ * (1 - M) * Z).trace.re := by
    have := (hM1.conjTranspose_mul_mul_same Z).trace_nonneg
    exact (Complex.nonneg_iff.mp this).1
  have e5 : (Zᴴ * (1 - M) * Z).trace.re = (Zᴴ * Z).trace.re - (Zᴴ * M * Z).trace.re := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re]
  rw [e1, e2, e3, hFPF, add_zero, Matrix.trace_sub, Complex.sub_re]
  simp only [Matrix.trace_add, Complex.add_re]
  linarith

omit [DecidableEq ι] in
/-- **The leakage step.** If `NF = F + Z`, `F = Fᴴ = F²`, `Q = Qᴴ`, then
`Re Tr F N*QN = Re Tr FQF + 2Re Tr Z*QF + Re Tr Z*QZ`. -/
theorem leak_step_eq {F Z Q N : Matrix ι ι ℂ} (hNF : N * F = F + Z) (hF : Fᴴ = F)
    (hF2 : F * F = F) (hQ : Qᴴ = Q) :
    (F * (Nᴴ * Q * N)).trace.re =
      (F * Q * F).trace.re + 2 * (Zᴴ * Q * F).trace.re + (Zᴴ * Q * Z).trace.re := by
  have hFN : F * Nᴴ = (F + Z)ᴴ := by rw [← hNF, Matrix.conjTranspose_mul, hF]
  have e1 : (F * (Nᴴ * Q * N)).trace = ((F + Z)ᴴ * Q * (F + Z)).trace := by
    calc (F * (Nᴴ * Q * N)).trace = (F * (F * (Nᴴ * Q * N))).trace := by
          rw [← Matrix.mul_assoc F F, hF2]
      _ = (F * (Nᴴ * Q * N) * F).trace := by rw [Matrix.trace_mul_comm F]
      _ = ((F * Nᴴ) * Q * (N * F)).trace := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFN, hNF]
  have e3 : (F + Z)ᴴ * Q * (F + Z) = F * Q * F + F * Q * Z + Zᴴ * Q * F + Zᴴ * Q * Z := by
    rw [Matrix.conjTranspose_add, hF]
    simp only [Matrix.add_mul, Matrix.mul_add]; abel
  have e4 : (F * Q * Z).trace.re = (Zᴴ * Q * F).trace.re := by
    rw [← re_trace_conjTranspose (Zᴴ * Q * F)]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ, hF,
      Matrix.mul_assoc]
  rw [e1, e3]
  simp only [Matrix.trace_add, Complex.add_re]
  linarith

end Abstract

/-!
## Hilbert–Schmidt against the operator norm
-/

theorem hsNorm_mul_le_opNorm {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]
    (D : Matrix m n ℂ) (V : Matrix n k ℂ) : hsNorm (D * V) ≤ ‖D‖ * hsNorm V := by
  have hcol : ∀ y : k, ∑ x, ‖(D * V) x y‖ ^ 2 ≤ ‖D‖ ^ 2 * ∑ x, ‖V x y‖ ^ 2 := by
    intro y
    have h := vecNorm_mulVec_le' D (fun x => V x y)
    have e1 : ∑ x, ‖(D * V) x y‖ ^ 2 = vecNorm (D *ᵥ fun x => V x y) ^ 2 := by
      rw [vecNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]; rfl
    have e2 : ∑ x, ‖V x y‖ ^ 2 = vecNorm (fun x => V x y) ^ 2 := by
      rw [vecNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    rw [e1, e2, ← mul_pow]
    exact pow_le_pow_left₀ (vecNorm_nonneg _) h 2
  have hsq : hsNorm (D * V) ^ 2 ≤ (‖D‖ * hsNorm V) ^ 2 := by
    calc hsNorm (D * V) ^ 2 = ∑ y, ∑ x, ‖(D * V) x y‖ ^ 2 := by rw [hsNorm_sq, Finset.sum_comm]
      _ ≤ ∑ y, ‖D‖ ^ 2 * ∑ x, ‖V x y‖ ^ 2 := Finset.sum_le_sum fun y _ => hcol y
      _ = (‖D‖ * hsNorm V) ^ 2 := by
          rw [mul_pow, hsNorm_sq]
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (hsNorm_nonneg _) (mul_nonneg (norm_nonneg _) (hsNorm_nonneg _))
    two_ne_zero).mp hsq

end BlockBand.SourceProcess.SmallLeak
