module

public import BlockBand.SourceProcess.FullSource.LayerStep

/-!
# Deterministic trace algebra for the tag square

* `norm_trace_mul_le_amgm`: `|Tr(PQ)| ≤ (Tr PP* + Tr Q*Q)/2` (Hilbert–Schmidt AM–GM);
* `norm_trace_sandwich_le`: `|Tr(BYAY)| ≤ (‖B‖² + ‖A‖²)/2 · Tr Y²` (`Y` Hermitian);
* `trace_sq_transport`: `Tr(Y₊²) = TrY² + 2Tr(Y²𝓔) + Tr(Y𝓔Y𝓔)` for `Y₊ = N*YN`, `𝓔 = NN* - I`;
* `re_trace_sq_transport_le`: `Tr Y₊² ≤ ‖N‖⁴ Tr Y²`;
* `re_trace_noise_sq_le`: `Tr(Y𝓔Y𝓔) ≤ 2‖A‖²TrY² + 2Σ_{x,y}|v_x*(𝓔-A)v_y|²` (`𝓔 = A + F`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

section Frob
variable {m n : Type*} [Fintype m] [Fintype n]

theorem re_trace_mul_conjTranspose (P : Matrix m n ℂ) :
    (P * Pᴴ).trace.re = ∑ i, ∑ j, ‖P i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem re_trace_conjTranspose_mul (Q : Matrix n m ℂ) :
    (Qᴴ * Q).trace.re = ∑ i, ∑ j, ‖Q j i‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Hilbert–Schmidt AM–GM**: `|Tr(PQ)| ≤ (Tr PP* + Tr Q*Q)/2`. -/
theorem norm_trace_mul_le_amgm (P : Matrix m n ℂ) (Q : Matrix n m ℂ) :
    ‖(P * Q).trace‖ ≤ ((P * Pᴴ).trace.re + (Qᴴ * Q).trace.re) / 2 := by
  rw [re_trace_mul_conjTranspose, re_trace_conjTranspose_mul, ← Finset.sum_add_distrib,
    Finset.sum_div]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  nlinarith [sq_nonneg (‖P i j‖ - ‖Q j i‖)]

theorem re_trace_conjTranspose_mul_nonneg (Q : Matrix n m ℂ) : 0 ≤ (Qᴴ * Q).trace.re := by
  rw [re_trace_conjTranspose_mul]; positivity

end Frob

section Sandwich
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem norm_conjTranspose_mul_self_le (B : Matrix n n ℂ) : ‖Bᴴ * B‖ ≤ ‖B‖ ^ 2 := by
  have h := norm_mul_conjTranspose_le Bᴴ
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h

/-- `Re Tr(Y² M) ≤ ‖M‖ Re Tr Y²` for Hermitian `Y`. -/
theorem norm_trace_sq_mul_le {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (M : Matrix n n ℂ) :
    ‖(Y * Y * M).trace‖ ≤ ‖M‖ * (Y * Y).trace.re := by
  have h := norm_trace_factor_le Y M
  rwa [hY.eq] at h

/-- **The sandwich bound**: `|Tr(BYAY)| ≤ (‖B‖² + ‖A‖²)/2 · Re Tr Y²` for Hermitian `Y`. -/
theorem norm_trace_sandwich_le {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (A B : Matrix n n ℂ) :
    ‖(B * Y * A * Y).trace‖ ≤ (‖B‖ ^ 2 + ‖A‖ ^ 2) / 2 * (Y * Y).trace.re := by
  have hT : 0 ≤ (Y * Y).trace.re := by
    have := trace_factor_re_nonneg Y; rwa [hY.eq] at this
  have h := norm_trace_mul_le_amgm (B * Y) (A * Y)
  rw [show B * Y * A * Y = B * Y * (A * Y) by simp only [Matrix.mul_assoc]]
  refine h.trans ?_
  have e1 : ((B * Y) * (B * Y)ᴴ).trace = (Y * Y * (Bᴴ * B)).trace := by
    rw [Matrix.conjTranspose_mul, hY.eq, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have e2 : ((A * Y)ᴴ * (A * Y)).trace = (Y * Y * (Aᴴ * A)).trace := by
    rw [Matrix.conjTranspose_mul, hY.eq, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [e1, e2]
  have h1 := (Complex.re_le_norm _).trans (norm_trace_sq_mul_le hY (Bᴴ * B))
  have h2 := (Complex.re_le_norm _).trans (norm_trace_sq_mul_le hY (Aᴴ * A))
  have h3 := mul_le_mul_of_nonneg_right (norm_conjTranspose_mul_self_le B) hT
  have h4 := mul_le_mul_of_nonneg_right (norm_conjTranspose_mul_self_le A) hT
  linarith

end Sandwich

section Square
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [Fintype m] [DecidableEq n] in
/-- Entries of `S F S*` are bilinear forms in the conjugated rows. -/
theorem sandwich_apply (S : Matrix m n ℂ) (F : Matrix n n ℂ) (x y : m) :
    (S * F * Sᴴ) x y = bilinear (rowv S x) F (rowv S y) := by
  simp only [Matrix.mul_apply, bilinear, dotProduct, mulVec, rowv, Pi.star_apply, star_star,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **Square transport**: with `Y = S*S`, `𝓔 = NN* - I`,
`Tr(Y₊²) = Tr Y² + 2Tr(Y²𝓔) + Tr(Y𝓔Y𝓔)` for `Y₊ = (SN)*(SN)`. -/
theorem trace_sq_transport (S : Matrix m n ℂ) (N : Matrix n n ℂ) :
    (((S * N)ᴴ * (S * N)) * ((S * N)ᴴ * (S * N))).trace =
      (Sᴴ * S * (Sᴴ * S)).trace + 2 * (Sᴴ * S * (Sᴴ * S) * (N * Nᴴ - 1)).trace +
        (Sᴴ * S * (N * Nᴴ - 1) * (Sᴴ * S) * (N * Nᴴ - 1)).trace := by
  set Y := Sᴴ * S
  set P := N * Nᴴ
  have e0 : (((S * N)ᴴ * (S * N)) * ((S * N)ᴴ * (S * N))).trace = (Y * P * Y * P).trace := by
    rw [Matrix.conjTranspose_mul]
    simp only [Y, P, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hP : P = 1 + (P - 1) := by abel
  set F := P - 1
  have e1 : Y * P * Y * P = Y * Y + Y * Y * F + Y * F * Y + Y * F * Y * F := by
    rw [hP]; noncomm_ring
  have e2 : (Y * F * Y).trace = (Y * Y * F).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [e0, e1, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, e2]
  ring

/-- **Crude square transport**: `Re Tr(Y₊²) ≤ ‖N‖⁴ Re Tr Y²`. -/
theorem re_trace_sq_transport_le (S : Matrix m n ℂ) (N : Matrix n n ℂ) :
    (((S * N)ᴴ * (S * N)) * ((S * N)ᴴ * (S * N))).trace.re ≤
      ‖N‖ ^ 4 * (Sᴴ * S * (Sᴴ * S)).trace.re := by
  have hY : (Sᴴ * S).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self S
  have e0 : (((S * N)ᴴ * (S * N)) * ((S * N)ᴴ * (S * N))).trace =
      ((N * Nᴴ) * (Sᴴ * S) * (N * Nᴴ) * (Sᴴ * S)).trace := by
    have e1 : (((S * N)ᴴ * (S * N)) * ((S * N)ᴴ * (S * N))).trace =
        (Sᴴ * S * (N * Nᴴ) * (Sᴴ * S) * (N * Nᴴ)).trace := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e1, show Sᴴ * S * (N * Nᴴ) * (Sᴴ * S) * (N * Nᴴ) =
      Sᴴ * S * ((N * Nᴴ) * (Sᴴ * S) * (N * Nᴴ)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
  rw [e0]
  have hT : 0 ≤ (Sᴴ * S * (Sᴴ * S)).trace.re := by
    have := trace_factor_re_nonneg (Sᴴ * S); rwa [hY.eq] at this
  have h := (Complex.re_le_norm _).trans (norm_trace_sandwich_le hY (N * Nᴴ) (N * Nᴴ))
  have hP := norm_mul_conjTranspose_le N
  have hP2 : ‖N * Nᴴ‖ ^ 2 ≤ (‖N‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP 2
  have := mul_le_mul_of_nonneg_right hP2 hT
  nlinarith

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_add_sq_le' (a c : ℂ) : ‖a + c‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
  have := norm_add_le a c
  nlinarith [norm_nonneg (a + c), sq_nonneg (‖a‖ - ‖c‖), norm_nonneg a, norm_nonneg c]

/-- **The quadratic noise term**: for `𝓔 = A + F`,
`Re Tr(Y𝓔Y𝓔) ≤ 2‖A‖² Re Tr Y² + 2Σ_{x,y}|v_x*Fv_y|²` (`Y = S*S`). -/
theorem re_trace_noise_sq_le (S : Matrix m n ℂ) (A F : Matrix n n ℂ) :
    (Sᴴ * S * (A + F) * (Sᴴ * S) * (A + F)).trace.re ≤
      2 * ‖A‖ ^ 2 * (Sᴴ * S * (Sᴴ * S)).trace.re +
        2 * ∑ x, ∑ y, ‖bilinear (rowv S x) F (rowv S y)‖ ^ 2 := by
  have hY : (Sᴴ * S).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self S
  set M := S * (A + F) * Sᴴ
  have e0 : (Sᴴ * S * (A + F) * (Sᴴ * S) * (A + F)).trace = (M * M).trace := by
    simp only [M, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hMM : ‖(M * M).trace‖ ≤ ∑ x, ∑ y, ‖M x y‖ ^ 2 := by
    refine (norm_trace_mul_le_amgm M M).trans (le_of_eq ?_)
    rw [re_trace_mul_conjTranspose, re_trace_conjTranspose_mul, Finset.sum_comm]
    ring
  have hent : ∀ x y, ‖M x y‖ ^ 2 ≤ 2 * ‖(S * A * Sᴴ) x y‖ ^ 2 +
      2 * ‖bilinear (rowv S x) F (rowv S y)‖ ^ 2 := by
    intro x y
    have : M x y = (S * A * Sᴴ) x y + (S * F * Sᴴ) x y := by
      simp only [M, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    rw [this, sandwich_apply S F]
    exact norm_add_sq_le' _ _
  have hA : ∑ x, ∑ y, ‖(S * A * Sᴴ) x y‖ ^ 2 ≤ ‖A‖ ^ 2 * (Sᴴ * S * (Sᴴ * S)).trace.re := by
    rw [← re_trace_mul_conjTranspose]
    have e : ((S * A * Sᴴ) * (S * A * Sᴴ)ᴴ).trace = (A * (Sᴴ * S) * Aᴴ * (Sᴴ * S)).trace := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e]
    refine (Complex.re_le_norm _).trans ((norm_trace_sandwich_le hY Aᴴ A).trans (le_of_eq ?_))
    rw [Matrix.l2_opNorm_conjTranspose]; ring
  rw [e0]
  refine (Complex.re_le_norm _).trans (hMM.trans ?_)
  calc ∑ x, ∑ y, ‖M x y‖ ^ 2 ≤ ∑ x, ∑ y, (2 * ‖(S * A * Sᴴ) x y‖ ^ 2 +
        2 * ‖bilinear (rowv S x) F (rowv S y)‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hent x y
    _ = 2 * ∑ x, ∑ y, ‖(S * A * Sᴴ) x y‖ ^ 2 +
        2 * ∑ x, ∑ y, ‖bilinear (rowv S x) F (rowv S y)‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith

end Square

end BlockBand.SourceProcess.FullSource
