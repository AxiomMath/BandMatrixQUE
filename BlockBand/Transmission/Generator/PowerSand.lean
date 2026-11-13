module

public import BlockBand.Transmission.Generator.PowerDiag
public import BlockBand.Transmission.SourceMixing.TraceSpectral

/-!
# The Hermitian representative `T^{1/2} U T^{1/2}` in an eigenbasis of `T`

For `Q ⪰ 0` with eigenbasis `V` (`ts_U`) and eigenvalues `λ_i` (`ts_lam`), put
`Δ = diag(√λ_i)` and `sand Q Z = Δ V*ZV Δ` (the matrix of `Q^{1/2}ZQ^{1/2}` in the eigenbasis):
* `sand_apply`: `(sand Q Z)_{ij} = √λ_i√λ_j u_i*Zu_j`; `sand` is linear; `sand_one`: `sand Q 1 =
  diag(λ)`;
* `trace_pow_sand`: `Tr (QZ)^k = Tr (sand Q Z)^k` (the eigenvalues of `Q₊ = L*QL` are those of
  `Q^{1/2}LL*Q^{1/2}`, with `trace_pow_mul_comm`);
* `frobSq_sand`: `‖sand Q Z‖²_HS = hsSandwich Q Z ^ 2`;
* `norm_sand_le`: `‖sand Q Z‖ ≤ ‖Z‖` if `λ_i ≤ 1`; `norm_le_sqrt_frobSq`: `‖B‖ ≤ ‖B‖_HS`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing
open scoped ComplexOrder Matrix.Norms.L2Operator

/-!
## General facts
-/

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem pow_succ_mul_comm (A B : Matrix n n ℂ) (k : ℕ) :
    (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

theorem trace_pow_mul_comm (A B : Matrix n n ℂ) (k : ℕ) :
    ((A * B) ^ k).trace = ((B * A) ^ k).trace := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [pow_succ_mul_comm, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

/-- `‖B‖ ≤ ‖B‖_HS`. -/
theorem norm_le_sqrt_frobSq (B : Matrix n n ℂ) : ‖B‖ ≤ Real.sqrt (frobSq B) := by
  refine opNorm_le_of_vec _ (Real.sqrt_nonneg _) fun x => ?_
  have hrow : ∀ i, ‖(B *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖B i j‖ ^ 2) * vecNorm x ^ 2 := by
    intro i
    have h := norm_star_dotProduct_le (star fun j => B i j) x
    rw [star_star] at h
    have hv : vecNorm (star fun j => B i j) ^ 2 = ∑ j, ‖B i j‖ ^ 2 := by
      rw [vecNorm, Real.sq_sqrt (by positivity)]; simp
    have e : (B *ᵥ x) i = (fun j => B i j) ⬝ᵥ x := rfl
    rw [e, ← hv, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hs : vecNorm (B *ᵥ x) ^ 2 ≤ frobSq B * vecNorm x ^ 2 := by
    rw [vecNorm, Real.sq_sqrt (by positivity), frobSq, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hrow i
  have h0 := vecNorm_nonneg (B *ᵥ x)
  have h1 := vecNorm_nonneg x
  rw [← Real.sqrt_sq h0, ← Real.sqrt_sq h1, ← Real.sqrt_mul (frobSq_nonneg B)]
  exact Real.sqrt_le_sqrt hs

theorem norm_unitary_le {V : Matrix n n ℂ} (hV : star V * V = 1) : ‖V‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [← Matrix.star_eq_conjTranspose, hV] at h
  have h1 := norm_one_matrix_le (n := n)
  nlinarith [norm_nonneg V]

end General

/-!
## The eigenbasis sandwich
-/

variable {W : ℕ} {Q : Matrix (Fin W) (Fin W) ℂ}

/-- `Δ = diag(√λ_i)`. -/
def sqD (hQ : Q.PosSemidef) : Matrix (Fin W) (Fin W) ℂ :=
  diagonal fun i => ((Real.sqrt (ts_lam hQ i) : ℝ) : ℂ)

/-- `sand Q Z = Δ V*ZV Δ`, the matrix of `Q^{1/2}ZQ^{1/2}` in the eigenbasis of `Q`. -/
def sand (hQ : Q.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  sqD hQ * (star (ts_U hQ) * Z * ts_U hQ) * sqD hQ

theorem ts_U_star_mul (hQ : Q.PosSemidef) : star (ts_U hQ) * ts_U hQ = 1 :=
  Unitary.coe_star_mul_self _

theorem ts_U_mul_star (hQ : Q.PosSemidef) : ts_U hQ * star (ts_U hQ) = 1 :=
  Unitary.coe_mul_star_self _

theorem sand_apply (hQ : Q.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    sand hQ Z i j =
      ((Real.sqrt (ts_lam hQ i) * Real.sqrt (ts_lam hQ j) : ℝ) : ℂ) * ts_ent hQ Z i j := by
  rw [sand, sqD, Matrix.mul_diagonal, Matrix.diagonal_mul, ts_ent_eq]
  push_cast; ring

theorem sand_add (hQ : Q.PosSemidef) (Z Z' : Matrix (Fin W) (Fin W) ℂ) :
    sand hQ (Z + Z') = sand hQ Z + sand hQ Z' := by
  simp only [sand, Matrix.mul_add, Matrix.add_mul]

theorem sand_sub (hQ : Q.PosSemidef) (Z Z' : Matrix (Fin W) (Fin W) ℂ) :
    sand hQ (Z - Z') = sand hQ Z - sand hQ Z' := by
  simp only [sand, Matrix.mul_sub, Matrix.sub_mul]

theorem sand_smul (hQ : Q.PosSemidef) (c : ℂ) (Z : Matrix (Fin W) (Fin W) ℂ) :
    sand hQ (c • Z) = c • sand hQ Z := by
  simp only [sand, Matrix.mul_smul, Matrix.smul_mul]

theorem sqD_mul_sqD (hQ : Q.PosSemidef) :
    sqD hQ * sqD hQ = diagonal fun i => (ts_lam hQ i : ℂ) := by
  rw [sqD, diagonal_mul_diagonal]
  congr 1; funext i
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ts_lam_nonneg hQ i)]

theorem sand_one (hQ : Q.PosSemidef) : sand hQ 1 = diagonal fun i => (ts_lam hQ i : ℂ) := by
  rw [sand, Matrix.mul_one, ts_U_star_mul, Matrix.mul_one, sqD_mul_sqD]

/-- **`Tr (QZ)^k = Tr (sand Q Z)^k`.** -/
theorem trace_pow_sand (hQ : Q.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) (k : ℕ) :
    ((Q * Z) ^ k).trace = ((sand hQ Z) ^ k).trace := by
  set V := ts_U hQ
  set Z' := star V * Z * V
  have hconj : ∀ (Y : Matrix (Fin W) (Fin W) ℂ) (m : ℕ),
      (V * Y * star V) ^ m = V * Y ^ m * star V := by
    intro Y m
    induction m with
    | zero => simp [V]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc V * Y ^ m * star V * (V * Y * star V)
          = V * Y ^ m * (star V * V) * Y * star V := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [ts_U_star_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e1 : Q * Z = V * ((sqD hQ * sqD hQ) * Z') * star V := by
    rw [sqD_mul_sqD]
    conv_lhs => rw [ts_spectral hQ]
    calc V * diagonal (fun i => (ts_lam hQ i : ℂ)) * star V * Z
        = V * diagonal (fun i => (ts_lam hQ i : ℂ)) * (star V * Z * (V * star V)) := by
          rw [ts_U_mul_star, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Z', Matrix.mul_assoc]
  rw [e1, hconj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ts_U_star_mul, Matrix.one_mul,
    Matrix.mul_assoc, trace_pow_mul_comm]
  rfl

theorem frobSq_sand (hQ : Q.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) :
    frobSq (sand hQ Z) = hsSandwich Q Z ^ 2 := by
  rw [ts_hs_eq hQ, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ j)) (sq_nonneg _)), frobSq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sand_apply, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (ts_lam_nonneg hQ i), Real.sq_sqrt (ts_lam_nonneg hQ j)]

theorem norm_sqD_le (hQ : Q.PosSemidef) (h1 : ∀ i, ts_lam hQ i ≤ 1) : ‖sqD hQ‖ ≤ 1 := by
  rw [sqD, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (h1 i)

theorem norm_sand_le (hQ : Q.PosSemidef) (h1 : ∀ i, ts_lam hQ i ≤ 1)
    (Z : Matrix (Fin W) (Fin W) ℂ) : ‖sand hQ Z‖ ≤ ‖Z‖ := by
  have hD := norm_sqD_le hQ h1
  have hV : ‖ts_U hQ‖ ≤ 1 := norm_unitary_le (ts_U_star_mul hQ)
  have hV' : ‖star (ts_U hQ)‖ ≤ 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]; exact hV
  have hZ := norm_nonneg Z
  calc ‖sand hQ Z‖ ≤ ‖sqD hQ‖ * (‖star (ts_U hQ)‖ * ‖Z‖ * ‖ts_U hQ‖) * ‖sqD hQ‖ := by
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * ‖Z‖ * 1) * 1 := by gcongr
    _ = ‖Z‖ := by ring

end BlockBand.Transmission.Generator
