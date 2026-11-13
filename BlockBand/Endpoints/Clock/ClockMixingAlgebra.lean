module

public import BlockBand.Endpoints.Clock.OpenInputsPath
public import BlockBand.Layers.TraceFluctuation
public import BlockBand.Layers.LayerMeanBounds
public import BlockBand.Layers.MatchedScalar

/-!
# The clock-mixing lemma: deterministic building blocks

We collect the deterministic matrix identities and bounds used in the proof of the clock-mixing
lemma.

For a positive semidefinite `Q` with eigenvalues `q_i ≥ 0` and eigenvectors `u_i`
(Mathlib's unitary diagonalization), with `N = U*MU` (`N_ik = u_i* M u_k`):

* `trace_mul_eq_sum`: `Tr(QM) = Σ_i q_i N_ii`; `trace_sandwich_eq_sum`:
  `Tr(QMQM*) = Σ_{ik} q_i q_k |N_ik|²` (the "Minkowski over the eigenbasis of `Q`" form);
* `hsSandwich_add_le` (triangle inequality for `M ↦ ‖Q^{1/2}MQ^{1/2}‖_HS`),
  `hsSandwich_smul`, `norm_trace_mul_le` (`|Tr QM| ≤ ‖M‖ Tr Q`),
  `hsSandwich_le` (`‖Q^{1/2}MQ^{1/2}‖_HS ≤ ‖M‖ Tr Q`, the trivial bound at `j₀`);
* `norm_le_trace` (`‖B‖ ≤ Tr B` for `B ⪰ 0`);
* the identity `S(A+B,f) = S(A,f) + S(B,f) + Tr(AfBf*) + Tr(BfAf*)` (`clockS_add`), the cross-term bound `|Tr(AfBf*)| ≤ ‖f‖² Tr A Tr B` (`norm_trace_cross_le`), and the
  resulting injection bound `hsSandwich_add_le_injection`:
  `√S(A+B,f) ≤ √S(A,f) + ‖f‖ (2 Tr B · Tr(A+B))^{1/2}`;
* transport identities `Tr((L*QL)f) = Tr(Q·LfL*)`, `S(L*QL,f) = S(Q,LfL*)`;
* one-ended layer facts: `X₊` Hermitian for Hermitian `X` and `A`, `Y(X) = 0` and
  `q(X) = 0` for Hermitian `X` (so `oneStepMean`'s `q/W` term vanishes on the one-ended
  path), `‖f(X)‖ ≤ (Im z)⁻¹ + |c₀|`,
  `Tr C ≤ W‖𝒢‖²`;
* `norm_thetaStar_lt_one`: `|θ_*| < 1` at every stationary jet;
* `geom_bound`: the geometric recursion `a_{j+1} ≤ θa_j + F ⇒ a_j ≤ a_{j₀} + F/(1-θ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

namespace ClockMixingAlg

/-!
## 1. Spectral form of the weighted traces
-/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}

/-- The eigenvector unitary of a Hermitian `Q`, as a matrix. -/
abbrev eU (hQ : Q.IsHermitian) : Matrix n n ℂ := (hQ.eigenvectorUnitary : Matrix n n ℂ)

/-- `N = U*MU`, the matrix of `M` in the eigenbasis of `Q`. -/
def rot (hQ : Q.IsHermitian) (M : Matrix n n ℂ) : Matrix n n ℂ := star (eU hQ) * M * eU hQ

theorem spec (hQ : Q.IsHermitian) :
    Q = eU hQ * diagonal (fun i => (hQ.eigenvalues i : ℂ)) * star (eU hQ) := by
  conv_lhs => rw [hQ.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem eU_star_mul (hQ : Q.IsHermitian) : star (eU hQ) * eU hQ = 1 :=
  Unitary.coe_star_mul_self _

theorem eU_mul_star (hQ : Q.IsHermitian) : eU hQ * star (eU hQ) = 1 :=
  Unitary.coe_mul_star_self _

theorem norm_eU_le (hQ : Q.IsHermitian) : ‖eU hQ‖ ≤ 1 := by
  have h1 : ‖(eU hQ)ᴴ * eU hQ‖ = ‖eU hQ‖ * ‖eU hQ‖ := l2_opNorm_conjTranspose_mul_self _
  rw [← star_eq_conjTranspose, eU_star_mul] at h1
  have h2 := BlockBand.Layers.lct_norm_one_le (n := n)
  have h0 := norm_nonneg (eU hQ)
  nlinarith

theorem norm_star_eU_le (hQ : Q.IsHermitian) : ‖star (eU hQ)‖ ≤ 1 := by
  rw [star_eq_conjTranspose, l2_opNorm_conjTranspose]; exact norm_eU_le hQ

theorem norm_rot_le (hQ : Q.IsHermitian) (M : Matrix n n ℂ) : ‖rot hQ M‖ ≤ ‖M‖ := by
  unfold rot
  calc ‖star (eU hQ) * M * eU hQ‖ ≤ ‖star (eU hQ)‖ * ‖M‖ * ‖eU hQ‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by
        gcongr
        · exact norm_star_eU_le hQ
        · exact norm_eU_le hQ
    _ = ‖M‖ := by ring

theorem norm_rot_apply_le (hQ : Q.IsHermitian) (M : Matrix n n ℂ) (i k : n) :
    ‖rot hQ M i k‖ ≤ ‖M‖ :=
  (BlockBand.Layers.tfl_entry_le _ i k).trans (norm_rot_le hQ M)

theorem rot_add (hQ : Q.IsHermitian) (M M' : Matrix n n ℂ) :
    rot hQ (M + M') = rot hQ M + rot hQ M' := by
  unfold rot; rw [mul_add, add_mul]

theorem rot_smul (hQ : Q.IsHermitian) (c : ℂ) (M : Matrix n n ℂ) :
    rot hQ (c • M) = c • rot hQ M := by
  unfold rot; rw [mul_smul_comm, smul_mul_assoc]

theorem rot_conjTranspose (hQ : Q.IsHermitian) (M : Matrix n n ℂ) :
    rot hQ Mᴴ = (rot hQ M)ᴴ := by
  unfold rot
  rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- The entries of `N = U*MU` are the bilinear forms `u_i* M u_k` of the eigenvectors. -/
theorem rot_apply (hQ : Q.IsHermitian) (M : Matrix n n ℂ) (i k : n) :
    rot hQ M i k = bilinear (fun a => eU hQ a i) M (fun a => eU hQ a k) := by
  unfold rot bilinear
  simp only [Matrix.mul_apply, star_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The eigenvectors are unit vectors. -/
theorem vecNorm_eU_col (hQ : Q.IsHermitian) (i : n) : vecNorm (fun a => eU hQ a i) = 1 := by
  have h := congrFun (congrFun (eU_star_mul hQ) i) i
  simp only [Matrix.mul_apply, star_apply, Matrix.one_apply_eq] at h
  have h' : ∑ a, ‖eU hQ a i‖ ^ 2 = 1 := by
    have : ((∑ a, ‖eU hQ a i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]; push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Complex.conj_mul', RCLike.star_def]
    exact_mod_cast this
  unfold vecNorm; rw [h', Real.sqrt_one]

theorem trace_mul_eq_sum (hQ : Q.IsHermitian) (M : Matrix n n ℂ) :
    (Q * M).trace = ∑ i, (hQ.eigenvalues i : ℂ) * rot hQ M i i := by
  conv_lhs => rw [spec hQ]
  have : eU hQ * diagonal (fun i => (hQ.eigenvalues i : ℂ)) * star (eU hQ) * M =
      eU hQ * (diagonal (fun i => (hQ.eigenvalues i : ℂ)) * star (eU hQ) * M) := by
    simp only [Matrix.mul_assoc]
  rw [this, trace_mul_comm]
  have : diagonal (fun i => (hQ.eigenvalues i : ℂ)) * star (eU hQ) * M * eU hQ =
      diagonal (fun i => (hQ.eigenvalues i : ℂ)) * rot hQ M := by
    unfold rot; simp only [Matrix.mul_assoc]
  rw [this]
  simp [trace, diagonal_mul]

/-- The real weighted sum `Σ_{ik} q_i q_k |N_ik|²`. -/
def sandwichSum (hQ : Q.IsHermitian) (M : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ k, hQ.eigenvalues i * hQ.eigenvalues k * ‖rot hQ M i k‖ ^ 2

/-- `Tr(D N D N*) = Σ_{ik} d_i d_k |N_ik|²` for a real diagonal `D = diag(d)`. -/
theorem trace_diag_sandwich (d : n → ℝ) (N : Matrix n n ℂ) :
    (diagonal (fun i => (d i : ℂ)) * N * diagonal (fun i => (d i : ℂ)) * Nᴴ).trace =
      ((∑ i, ∑ k, d i * d k * ‖N i k‖ ^ 2 : ℝ) : ℂ) := by
  have hentry : ∀ i, (diagonal (fun i => (d i : ℂ)) * N * diagonal (fun i => (d i : ℂ)) * Nᴴ) i i =
      ∑ k, (d i : ℂ) * N i k * (d k : ℂ) * star (N i k) := by
    intro i
    rw [Matrix.mul_apply]
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply]
  rw [trace]
  simp only [diag_apply, hentry]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  have h := Complex.mul_conj' (N i k)
  rw [RCLike.star_def]
  linear_combination ((d i : ℂ) * (d k : ℂ)) * h

theorem trace_sandwich_eq_sum (hQ : Q.IsHermitian) (M : Matrix n n ℂ) :
    (Q * M * Q * Mᴴ).trace = (sandwichSum hQ M : ℂ) := by
  have key : Q * M * Q * Mᴴ = eU hQ * (diagonal (fun i => (hQ.eigenvalues i : ℂ)) * rot hQ M *
      diagonal (fun i => (hQ.eigenvalues i : ℂ)) * (rot hQ M)ᴴ * star (eU hQ)) := by
    rw [← rot_conjTranspose]
    unfold rot
    conv_lhs => rw [spec hQ]
    calc eU hQ * diagonal (fun i => (hQ.eigenvalues i : ℂ)) * star (eU hQ) * M *
          (eU hQ * diagonal (fun i => (hQ.eigenvalues i : ℂ)) * star (eU hQ)) * Mᴴ
        = eU hQ * diagonal (fun i => (hQ.eigenvalues i : ℂ)) * (star (eU hQ) * M * eU hQ) *
            diagonal (fun i => (hQ.eigenvalues i : ℂ)) * (star (eU hQ) * Mᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = eU hQ * diagonal (fun i => (hQ.eigenvalues i : ℂ)) * (star (eU hQ) * M * eU hQ) *
            diagonal (fun i => (hQ.eigenvalues i : ℂ)) * (star (eU hQ) * Mᴴ * (eU hQ * star (eU hQ))) := by
          rw [eU_mul_star hQ, Matrix.mul_one]
      _ = eU hQ * (diagonal (fun i => (hQ.eigenvalues i : ℂ)) * (star (eU hQ) * M * eU hQ) *
            diagonal (fun i => (hQ.eigenvalues i : ℂ)) * (star (eU hQ) * Mᴴ * eU hQ) *
              star (eU hQ)) := by
          simp only [Matrix.mul_assoc]
  rw [key, trace_mul_comm, Matrix.mul_assoc, eU_star_mul hQ, Matrix.mul_one]
  exact trace_diag_sandwich _ _

theorem sandwichSum_nonneg (hQ : Q.PosSemidef) (M : Matrix n n ℂ) :
    0 ≤ sandwichSum hQ.1 M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hQ.eigenvalues_nonneg i) (hQ.eigenvalues_nonneg k)) (sq_nonneg _)

theorem trace_re_eq_sum (hQ : Q.IsHermitian) : Q.trace.re = ∑ i, hQ.eigenvalues i := by
  rw [hQ.trace_eq_sum_eigenvalues]
  simp

/-- Weighted Minkowski: `√(Σ w|a+b|²) ≤ √(Σ w|a|²) + √(Σ w|b|²)` for `w ≥ 0`. -/
theorem sqrt_wsum_add_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a c : ι → ℂ) :
    Real.sqrt (∑ i, w i * ‖a i + c i‖ ^ 2) ≤
      Real.sqrt (∑ i, w i * ‖a i‖ ^ 2) + Real.sqrt (∑ i, w i * ‖c i‖ ^ 2) := by
  let v : (ι → ℂ) → EuclideanSpace ℂ ι := fun x => WithLp.toLp 2 fun i => (Real.sqrt (w i) : ℂ) * x i
  have hv : ∀ x, ‖v x‖ = Real.sqrt (∑ i, w i * ‖x i‖ ^ 2) := by
    intro x
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [v, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw i)]
  have hadd : v (a + c) = v a + v c := by
    ext i; simp [v, mul_add]
  rw [← hv, ← hv, ← hv]
  exact (congrArg norm hadd).le.trans (norm_add_le _ _)

theorem sandwichSum_add_sqrt_le (hQ : Q.PosSemidef) (M M' : Matrix n n ℂ) :
    Real.sqrt (sandwichSum hQ.1 (M + M')) ≤
      Real.sqrt (sandwichSum hQ.1 M) + Real.sqrt (sandwichSum hQ.1 M') := by
  have h := sqrt_wsum_add_le (fun p : n × n => hQ.1.eigenvalues p.1 * hQ.1.eigenvalues p.2)
    (fun p => mul_nonneg (hQ.eigenvalues_nonneg _) (hQ.eigenvalues_nonneg _))
    (fun p => rot hQ.1 M p.1 p.2) (fun p => rot hQ.1 M' p.1 p.2)
  simp only [sandwichSum, rot_add, Matrix.add_apply]
  simpa only [Fintype.sum_prod_type] using h

end Spectral

/-!
## 2. Trace and Hilbert–Schmidt bounds for `W × W` clocks
-/

section Bounds

variable {W : ℕ}

theorem hsSandwich_eq_sqrt {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.IsHermitian)
    (M : Matrix (Fin W) (Fin W) ℂ) : hsSandwich Q M = Real.sqrt (sandwichSum hQ M) := by
  unfold hsSandwich
  rw [trace_sandwich_eq_sum hQ, Complex.ofReal_re]

/-- Triangle inequality for `M ↦ ‖Q^{1/2} M Q^{1/2}‖_HS`, `Q ⪰ 0`. -/
theorem hsSandwich_add_le {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (M M' : Matrix (Fin W) (Fin W) ℂ) :
    hsSandwich Q (M + M') ≤ hsSandwich Q M + hsSandwich Q M' := by
  rw [hsSandwich_eq_sqrt hQ.1, hsSandwich_eq_sqrt hQ.1, hsSandwich_eq_sqrt hQ.1]
  exact sandwichSum_add_sqrt_le hQ M M'

theorem hsSandwich_smul {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.IsHermitian) (c : ℂ)
    (M : Matrix (Fin W) (Fin W) ℂ) : hsSandwich Q (c • M) = ‖c‖ * hsSandwich Q M := by
  rw [hsSandwich_eq_sqrt hQ, hsSandwich_eq_sqrt hQ]
  have : sandwichSum hQ (c • M) = ‖c‖ ^ 2 * sandwichSum hQ M := by
    unfold sandwichSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rot_smul, Matrix.smul_apply, smul_eq_mul, norm_mul]
    ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem hsSandwich_nonneg (Q M : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ hsSandwich Q M :=
  Real.sqrt_nonneg _

/-- `|Tr(QM)| ≤ ‖M‖ Tr Q` for `Q ⪰ 0`. -/
theorem norm_trace_mul_le {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}
    (hQ : Q.PosSemidef) (M : Matrix n n ℂ) : ‖(Q * M).trace‖ ≤ ‖M‖ * Q.trace.re := by
  rw [trace_mul_eq_sum hQ.1, trace_re_eq_sum hQ.1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hQ.eigenvalues_nonneg i),
    mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_rot_apply_le hQ.1 M i i) (hQ.eigenvalues_nonneg i)

/-- `‖Q^{1/2} M Q^{1/2}‖_HS ≤ ‖M‖ Tr Q` for `Q ⪰ 0`. -/
theorem hsSandwich_le {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (M : Matrix (Fin W) (Fin W) ℂ) : hsSandwich Q M ≤ ‖M‖ * Q.trace.re := by
  rw [hsSandwich_eq_sqrt hQ.1, trace_re_eq_sum hQ.1]
  have hs : sandwichSum hQ.1 M ≤ (‖M‖ * ∑ i, hQ.1.eigenvalues i) ^ 2 := by
    have hexp : (‖M‖ * ∑ i, hQ.1.eigenvalues i) ^ 2 =
        ∑ i, ∑ k, hQ.1.eigenvalues i * hQ.1.eigenvalues k * ‖M‖ ^ 2 := by
      rw [show (‖M‖ * ∑ i, hQ.1.eigenvalues i) ^ 2 =
          ‖M‖ ^ 2 * ((∑ i, hQ.1.eigenvalues i) * ∑ i, hQ.1.eigenvalues i) by ring,
        Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hexp]
    unfold sandwichSum
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := norm_rot_apply_le hQ.1 M i k
    have h2 : ‖rot hQ.1 M i k‖ ^ 2 ≤ ‖M‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := mul_nonneg (hQ.eigenvalues_nonneg i) (hQ.eigenvalues_nonneg k)
    nlinarith
  have hpos : 0 ≤ ‖M‖ * ∑ i, hQ.1.eigenvalues i :=
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => hQ.eigenvalues_nonneg i)
  calc Real.sqrt (sandwichSum hQ.1 M) ≤ Real.sqrt ((‖M‖ * ∑ i, hQ.1.eigenvalues i) ^ 2) :=
        Real.sqrt_le_sqrt hs
    _ = ‖M‖ * ∑ i, hQ.1.eigenvalues i := Real.sqrt_sq hpos

/-- `‖B‖ ≤ Tr B` for `B ⪰ 0`. -/
theorem norm_le_trace {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℂ}
    (hB : B.PosSemidef) : ‖B‖ ≤ B.trace.re := by
  have hspec := spec hB.1
  rw [trace_re_eq_sum hB.1]
  have hD : ‖diagonal (fun i => (hB.1.eigenvalues i : ℂ))‖ ≤ ∑ i, hB.1.eigenvalues i := by
    rw [l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hB.eigenvalues_nonneg i)).mpr
      fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB.eigenvalues_nonneg i)]
    exact Finset.single_le_sum (f := fun i => hB.1.eigenvalues i)
      (fun i _ => hB.eigenvalues_nonneg i) (Finset.mem_univ i)
  have hS0 : 0 ≤ ∑ i, hB.1.eigenvalues i := Finset.sum_nonneg fun i _ => hB.eigenvalues_nonneg i
  calc ‖B‖ = ‖eU hB.1 * diagonal (fun i => (hB.1.eigenvalues i : ℂ)) * star (eU hB.1)‖ :=
        congrArg norm hspec
    _ ≤ ‖eU hB.1‖ * ‖diagonal (fun i => (hB.1.eigenvalues i : ℂ))‖ * ‖star (eU hB.1)‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * (∑ i, hB.1.eigenvalues i) * 1 :=
        mul_le_mul (mul_le_mul (norm_eU_le hB.1) hD (norm_nonneg _) zero_le_one)
          (norm_star_eU_le hB.1) (norm_nonneg _) (by positivity)
    _ = ∑ i, hB.1.eigenvalues i := by ring

theorem trace_re_nonneg {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℂ}
    (hB : B.PosSemidef) : 0 ≤ B.trace.re :=
  (norm_nonneg _).trans (norm_le_trace hB)

/-- The exact identity of:
`S(A+B,f) = S(A,f) + S(B,f) + Tr(AfBf*) + Tr(BfAf*)` (traces before taking real parts). -/
theorem clockS_add (A B f : Matrix (Fin W) (Fin W) ℂ) :
    ((A + B) * f * (A + B) * fᴴ).trace =
      (A * f * A * fᴴ).trace + (B * f * B * fᴴ).trace + (A * f * B * fᴴ).trace +
        (B * f * A * fᴴ).trace := by
  simp only [add_mul, mul_add, trace_add]
  ring

/-- The cross terms: `|Tr(AfBf*)| ≤ ‖f‖² Tr A Tr B` for `A, B ⪰ 0` (: bounded by
`‖B‖‖f‖² Tr A ≤ ‖f‖² Tr B Tr A`). -/
theorem norm_trace_cross_le {A B : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (f : Matrix (Fin W) (Fin W) ℂ) :
    ‖(A * f * B * fᴴ).trace‖ ≤ ‖f‖ ^ 2 * A.trace.re * B.trace.re := by
  have h : A * f * B * fᴴ = A * (f * B * fᴴ) := by simp only [Matrix.mul_assoc]
  rw [h]
  refine (norm_trace_mul_le hA _).trans ?_
  have h1 : ‖f * B * fᴴ‖ ≤ ‖f‖ ^ 2 * B.trace.re := by
    calc ‖f * B * fᴴ‖ ≤ ‖f‖ * ‖B‖ * ‖fᴴ‖ :=
          (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ ‖f‖ * B.trace.re * ‖f‖ := by
          rw [l2_opNorm_conjTranspose]
          gcongr
          exact norm_le_trace hB
      _ = ‖f‖ ^ 2 * B.trace.re := by ring
  have hA0 := trace_re_nonneg hA
  calc ‖f * B * fᴴ‖ * A.trace.re ≤ ‖f‖ ^ 2 * B.trace.re * A.trace.re :=
        mul_le_mul_of_nonneg_right h1 hA0
    _ = ‖f‖ ^ 2 * A.trace.re * B.trace.re := by ring

/-- `√(x+y) ≤ √x + √y` for `x, y ≥ 0`. -/
theorem sqrt_add_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

/-- **Injection bound**: for `A, B ⪰ 0`,
`√S(A+B,f) ≤ √S(A,f) + ‖f‖ (2 Tr B · Tr(A+B))^{1/2}`, `√S = hsSandwich`. -/
theorem hsSandwich_add_le_injection {A B : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (f : Matrix (Fin W) (Fin W) ℂ) :
    hsSandwich (A + B) f ≤
      hsSandwich A f + ‖f‖ * Real.sqrt (2 * B.trace.re * (A + B).trace.re) := by
  have hA0 := trace_re_nonneg hA
  have hB0 := trace_re_nonneg hB
  have hSA : 0 ≤ (A * f * A * fᴴ).trace.re := by
    rw [trace_sandwich_eq_sum hA.1, Complex.ofReal_re]; exact sandwichSum_nonneg hA f
  have hsum : ((A + B) * f * (A + B) * fᴴ).trace.re ≤
      (A * f * A * fᴴ).trace.re + ‖f‖ ^ 2 * (2 * B.trace.re * (A + B).trace.re) := by
    rw [clockS_add, Complex.add_re, Complex.add_re, Complex.add_re, trace_add, Complex.add_re]
    have h1 := (Complex.re_le_norm _).trans (norm_trace_cross_le hB hB f)
    have h2 := (Complex.re_le_norm _).trans (norm_trace_cross_le hA hB f)
    have h3 := (Complex.re_le_norm _).trans (norm_trace_cross_le hB hA f)
    have hf := sq_nonneg ‖f‖
    nlinarith [mul_nonneg hf (mul_nonneg hA0 hB0), mul_nonneg hf (mul_nonneg hB0 hB0)]
  unfold hsSandwich
  have hy : 0 ≤ ‖f‖ ^ 2 * (2 * B.trace.re * (A + B).trace.re) := by
    rw [trace_add, Complex.add_re]; positivity
  calc Real.sqrt ((A + B) * f * (A + B) * fᴴ).trace.re
      ≤ Real.sqrt ((A * f * A * fᴴ).trace.re + ‖f‖ ^ 2 * (2 * B.trace.re * (A + B).trace.re)) :=
        Real.sqrt_le_sqrt hsum
    _ ≤ Real.sqrt (A * f * A * fᴴ).trace.re +
          Real.sqrt (‖f‖ ^ 2 * (2 * B.trace.re * (A + B).trace.re)) :=
        sqrt_add_le_add hSA hy
    _ = Real.sqrt (A * f * A * fᴴ).trace.re +
          ‖f‖ * Real.sqrt (2 * B.trace.re * (A + B).trace.re) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Transport of the trace: `Tr((L*QL) f) = Tr(Q · L f L*)`. -/
theorem trace_transport (L Q f : Matrix (Fin W) (Fin W) ℂ) :
    (Lᴴ * Q * L * f).trace = (Q * (L * f * Lᴴ)).trace := by
  rw [show Lᴴ * Q * L * f = Lᴴ * (Q * (L * f)) by simp only [Matrix.mul_assoc], trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- Transport of the weighted HS norm: `S(L*QL, f) = S(Q, L f L*)`. -/
theorem hsSandwich_transport (L Q f : Matrix (Fin W) (Fin W) ℂ) :
    hsSandwich (Lᴴ * Q * L) f = hsSandwich Q (L * f * Lᴴ) := by
  unfold hsSandwich
  congr 2
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [show Lᴴ * Q * L * f * (Lᴴ * Q * L) * fᴴ = Lᴴ * (Q * L * f * Lᴴ * Q * L * fᴴ) by
    simp only [Matrix.mul_assoc], trace_mul_comm]
  simp only [Matrix.mul_assoc]

end Bounds

/-!
## 3. One-ended layer facts
-/

section Layer

variable {W : ℕ}

/-- The embedding of a `W × W` matrix as the physical matrix of a one-block layer. -/
abbrev physEmbed (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
  Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2

theorem physEmbed_isHermitian {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    (physEmbed X).IsHermitian := by
  ext u v
  simp only [conjTranspose_apply, Matrix.of_apply]
  exact congrFun (congrFun hX u.2) v.2

/-- `X₊ = B*(A - E - X)⁻¹B` is Hermitian for Hermitian `X` and Hermitian `A`. -/
theorem freshSchur_isHermitian (E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (ω : OneEndedLayer W) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (freshSchur E X ω).IsHermitian := by
  have hT := BlockBand.Layers.lct_top_isHermitian (σ := .oneBlockOnePort) E
    (physEmbed_isHermitian hX) hA
  have hS : (layerSchur .oneBlockOnePort E (physEmbed X) ω).IsHermitian := by
    unfold layerSchur
    exact isHermitian_conjTranspose_mul_mul _ hT.inv
  ext x y
  simp only [freshSchur, conjTranspose_apply, Matrix.of_apply]
  exact congrFun (congrFun hS ((0 : Fin 1), x)) ((0 : Fin 1), y)

theorem passiveY_eq_zero {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    passiveY X = 0 := by
  unfold passiveY BlockBand.Transmission.matrixImaginaryPart
  rw [hX.eq, sub_self, smul_zero, neg_zero]

theorem passiveY_posSemidef {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    (passiveY X).PosSemidef := by
  rw [passiveY_eq_zero hX]; exact PosSemidef.zero

theorem passiveMass_eq_zero (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    passiveMass b E X = 0 := by
  unfold passiveMass passiveQ
  rw [passiveY_eq_zero hX, Matrix.mul_zero, Matrix.zero_mul, trace_zero, Complex.zero_re]

/-- `‖(z - X)⁻¹‖ ≤ (Im z)⁻¹` for Hermitian `X`, `Im z > 0`. -/
theorem norm_resolvent_le {z : ℂ} (hz : 0 < z.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) : ‖(z • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹‖ ≤ z.im⁻¹ := by
  have h := BlockBand.Layers.lct_norm_shifted_inv_le (-X) hX.neg (fun _ => -z) hz
    (fun _ => by simp)
  have he : -X - diagonal (fun _ : Fin W => -z) = z • (1 : Matrix (Fin W) (Fin W) ℂ) - X := by
    rw [← smul_one_eq_diagonal, neg_smul]; abel
  rwa [he] at h

/-- The deterministic bound `‖f(X)‖ ≤ (Im z)⁻¹ + |c₀|` for Hermitian `X` (:
"`f` itself has a deterministic bounded operator norm"). -/
theorem norm_passiveF_le (b E : ℝ) (hz : 0 < (boundaryZ b E).im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) : ‖passiveF b E X‖ ≤ (boundaryZ b E).im⁻¹ + ‖cZero b E‖ := by
  unfold passiveF passiveResolvent
  refine (norm_sub_le _ _).trans (add_le_add (norm_resolvent_le hz hX) ?_)
  refine (norm_smul_le _ _).trans ?_
  have := BlockBand.Layers.lct_norm_one_le (n := Fin W)
  nlinarith [norm_nonneg (cZero b E)]

/-- `c₀ = (2iη)⁻¹ = (z - z̄)⁻¹`, so `passiveF` is `f(X) = (z-X)⁻¹ - (z-z̄)⁻¹I`. -/
theorem cZero_eq (b E : ℝ) : cZero b E = (boundaryZ b E - conj (boundaryZ b E))⁻¹ := by
  unfold cZero etaZ
  congr 1
  apply Complex.ext <;> simp; ring

/-- `Tr C ≤ W‖𝒢‖²` (`C = 𝒢₁₂*𝒢₁₂`, column sums of `|𝒢|²`). -/
theorem trace_freshC_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    (freshC b E X ω).trace.re ≤ W * ‖freshLayer b E X ω‖ ^ 2 := by
  set G := freshLayer b E X ω
  have htr : (freshC b E X ω).trace.re =
      ∑ y : Fin W, ∑ x : Fin W, ‖G (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))‖ ^ 2 := by
    unfold freshC freshG12
    simp only [trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]
  rw [htr]
  have hcol : ∀ y : Fin W,
      ∑ x : Fin W, ‖G (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    intro y
    refine le_trans ?_ (BlockBand.Layers.tfl_col_sq_le G (Sum.inr ((0 : Fin 1), y)))
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_one]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc ∑ y : Fin W, ∑ x : Fin W, ‖G (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))‖ ^ 2
      ≤ ∑ _y : Fin W, ‖G‖ ^ 2 := Finset.sum_le_sum fun y _ => hcol y
    _ = W * ‖G‖ ^ 2 := by simp

theorem freshC_posSemidef (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    (freshC b E X ω).PosSemidef :=
  posSemidef_conjTranspose_mul_self _

end Layer

/-!
## 4. The contraction coefficient `|θ_*| < 1`
-/

/-- `|k₋| < (1-b)²` in the bulk (: `|k| < c + b² = (1-b)²` whenever `a² ≠ 1`). -/
theorem norm_kMinus_lt {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) :
    ‖kMinus b E‖ < (1 - b) ^ 2 := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE1.le, hE2.le⟩
  have hsq := BlockBand.Layers.matchedA_sq hE
  have hs := BlockBand.Layers.sqrt_four_sub_sq_sq hE
  set r := Real.sqrt (4 - E ^ 2)
  have hre : (kMinus b E).re = (1 - 2 * b) + b ^ 2 * (E ^ 2 / 2 - 1) := by
    unfold kMinus; rw [hsq]; simp [pow_two]
  have him : (kMinus b E).im = b ^ 2 * (E * r / 2) := by
    unfold kMinus; rw [hsq]; simp [pow_two]
  have hn : ‖kMinus b E‖ ^ 2 = (1 - 2 * b) ^ 2 + (1 - 2 * b) * b ^ 2 * (E ^ 2 - 2) + b ^ 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have : r ^ 2 = 4 - E ^ 2 := hs
    linear_combination (b ^ 4 * E ^ 2 / 4) * this
  have hE4 : E ^ 2 < 4 := by nlinarith
  have hlt : ‖kMinus b E‖ ^ 2 < ((1 - b) ^ 2) ^ 2 := by
    rw [hn]
    have hc : 0 < 1 - 2 * b := by linarith
    have hb2 : 0 < b ^ 2 := by positivity
    nlinarith [mul_pos hc hb2]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

/-- **`|θ_*| < 1`** at every stationary jet `s` (`|s| ≤ (1-b)⁻¹`), in the bulk. -/
theorem norm_thetaStar_lt_one {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) : ‖thetaStar b E s‖ < 1 := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE1.le, hE2.le⟩
  have hk := norm_kMinus_lt hb0 hb1 hE1 hE2
  have hs' : ‖s‖ ≤ 1 / (1 - b) := hs.2
  have h1b : 0 < 1 - b := by linarith
  have hks : ‖kMinus b E * s‖ < 1 - b := by
    rw [norm_mul]
    calc ‖kMinus b E‖ * ‖s‖ ≤ ‖kMinus b E‖ * (1 / (1 - b)) :=
          mul_le_mul_of_nonneg_left hs' (norm_nonneg _)
      _ < (1 - b) ^ 2 * (1 / (1 - b)) := mul_lt_mul_of_pos_right hk (by positivity)
      _ = 1 - b := by field_simp
  have hden : b < ‖1 + kMinus b E * s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(kMinus b E * s))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this
    linarith
  have hb : 0 < ‖1 + kMinus b E * s‖ := hb0.trans hden
  unfold thetaStar
  rw [norm_div, norm_mul, norm_pow, BlockBand.Layers.norm_matchedA hE, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hb0, one_pow, mul_one, div_lt_one hb]
  exact hden

/-!
## 5. The geometric recursion
-/

/-- **Geometric recursion**: if `a_{j₀} ≤ A` and
`a_{j+1} ≤ θ a_j + F` for `j₀ ≤ j < N`, with `0 ≤ θ < 1`, then `a_j ≤ A + F/(1-θ)` on
`j₀ ≤ j ≤ N`. -/
theorem geom_bound {a : ℕ → ℝ≥0∞} {θ A F : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hA : 0 ≤ A)
    (hF : 0 ≤ F) {j₀ N : ℕ} (h0 : a j₀ ≤ ENNReal.ofReal A)
    (hstep : ∀ j, j₀ ≤ j → j < N → a (j + 1) ≤ ENNReal.ofReal θ * a j + ENNReal.ofReal F) :
    ∀ j, j₀ ≤ j → j ≤ N → a j ≤ ENNReal.ofReal (A + F / (1 - θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hB : 0 ≤ A + F / (1 - θ) := by positivity
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    exact h0.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity)))
  | succ k hk ih =>
    intro hkN
    have ih' := ih (by omega)
    calc a (k + 1) ≤ ENNReal.ofReal θ * a k + ENNReal.ofReal F := hstep k hk (by omega)
      _ ≤ ENNReal.ofReal θ * ENNReal.ofReal (A + F / (1 - θ)) + ENNReal.ofReal F := by gcongr
      _ = ENNReal.ofReal (θ * (A + F / (1 - θ)) + F) := by
          rw [← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_add (mul_nonneg hθ0 hB) hF]
      _ ≤ ENNReal.ofReal (A + F / (1 - θ)) := by
          apply ENNReal.ofReal_le_ofReal
          have : θ * (A + F / (1 - θ)) + F = θ * A + F / (1 - θ) := by
            field_simp; ring
          rw [this]
          nlinarith

end ClockMixingAlg

end BlockBand.Endpoints.Clock
