module

public import BlockBand.SourceProcess.Stochastic.Dyson.Lagrange

/-!
# Dyson Brownian motion: algebra of first-order spectral perturbation

`SpecFamily H P μ` bundles the algebra of a complete family of spectral projections of `H` with
pairwise distinct eigenvalues `μ`. `SpecFamily.firstOrder` is purely algebraic: if `(l, Q)`
satisfy the differentiated identities
`H Q + K P_i = μ_i Q + l P_i`, `Q H + P_i K = μ_i Q + l P_i`, `P_i Q + Q P_i = Q`
(directional derivatives of `H P_i = μ_i P_i`, `P_i H = μ_i P_i`, `P_i² = P_i` along `K`), then
`l = tr(P_i K)` and `Q = ∑_{j ≠ i} (μ_i - μ_j)⁻¹ (P_j K P_i + P_i K P_j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix
open scoped Matrix
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- A complete family of spectral projections with pairwise distinct eigenvalues. -/
structure SpecFamily (H : Matrix (Fin N) (Fin N) ℂ) (P : Fin N → Matrix (Fin N) (Fin N) ℂ)
    (μ : Fin N → ℂ) : Prop where
  mul_proj : ∀ i j, P i * P j = if i = j then P i else 0
  sum_proj : ∑ i, P i = 1
  H_mul : ∀ i, H * P i = μ i • P i
  mul_H : ∀ i, P i * H = μ i • P i
  trace_proj : ∀ i, trace (P i) = 1
  distinct : ∀ i j, i ≠ j → μ i ≠ μ j

/-- The Lagrange projections of a Hermitian matrix with simple spectrum form a `SpecFamily`. -/
theorem specFamily_dyson {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) :
    SpecFamily H (dysonProjection N H) (fun i => (dysonEigenvalue N H i : ℂ)) where
  mul_proj := proj_mul_proj hH hs
  sum_proj := sum_proj hH hs
  H_mul := mul_proj hH hs
  mul_H := proj_mul hH hs
  trace_proj := trace_proj hH hs
  distinct i j hij := by exact_mod_cast HasSimpleSpectrum.ne hs hij

namespace SpecFamily

variable {H : Matrix (Fin N) (Fin N) ℂ} {P : Fin N → Matrix (Fin N) (Fin N) ℂ} {μ : Fin N → ℂ}
  (hS : SpecFamily H P μ)
include hS

theorem proj_mul_self (i : Fin N) : P i * P i = P i := by simpa using hS.mul_proj i i

theorem proj_mul_ne {i j : Fin N} (h : i ≠ j) : P i * P j = 0 := by
  simpa [h] using hS.mul_proj i j

theorem sub_ne_zero' {i j : Fin N} (h : i ≠ j) : μ i - μ j ≠ 0 :=
  sub_ne_zero.mpr (hS.distinct i j h)

/-- `M = ∑_j P_j M`. -/
theorem sum_proj_mul (M : Matrix (Fin N) (Fin N) ℂ) : ∑ j, P j * M = M := by
  rw [← Finset.sum_mul, hS.sum_proj, Matrix.one_mul]

/-- `M = ∑_j M P_j`. -/
theorem sum_mul_proj (M : Matrix (Fin N) (Fin N) ℂ) : ∑ j, M * P j = M := by
  rw [← Finset.mul_sum, hS.sum_proj, Matrix.mul_one]

/-- **First-order perturbation algebra** (Hadamard): `l = tr(P_i K)` and
`Q = ∑_{j ≠ i} (μ_i - μ_j)⁻¹ (P_j K P_i + P_i K P_j)`. -/
theorem firstOrder {K Q : Matrix (Fin N) (Fin N) ℂ} {l : ℂ} (i : Fin N)
    (h1 : H * Q + K * P i = μ i • Q + l • P i) (h2 : Q * H + P i * K = μ i • Q + l • P i)
    (h3 : P i * Q + Q * P i = Q) :
    l = trace (P i * K) ∧
      Q = ∑ j ∈ Finset.univ.erase i, (μ i - μ j)⁻¹ • (P j * K * P i + P i * K * P j) := by
  -- `P_j H = μ_j P_j` in left-multiplied form
  have hPH : ∀ j M, P j * (H * M) = μ j • (P j * M) := fun j M => by
    rw [← Matrix.mul_assoc, hS.mul_H, Matrix.smul_mul]
  have hHP : ∀ j M, (M * H) * P j = μ j • (M * P j) := fun j M => by
    rw [Matrix.mul_assoc, hS.H_mul, Matrix.mul_smul]
  -- (a) the eigenvalue derivative
  have ha : P i * K * P i = l • P i := by
    have := congrArg (fun M => P i * M) h1
    simp only [Matrix.mul_add, Matrix.mul_smul, hPH, hS.proj_mul_self] at this
    rw [Matrix.mul_assoc]
    exact add_left_cancel this
  have hl : l = trace (P i * K) := by
    have := congrArg trace ha
    rw [trace_smul, hS.trace_proj, smul_eq_mul, mul_one, Matrix.mul_assoc, trace_mul_comm,
      Matrix.mul_assoc, hS.proj_mul_self] at this
    exact this.symm.trans (trace_mul_comm _ _)
  refine ⟨hl, ?_⟩
  -- (b) `P_j Q` for `j ≠ i`
  have hb : ∀ j, j ≠ i → P j * Q = (μ i - μ j)⁻¹ • (P j * K * P i) := by
    intro j hj
    have := congrArg (fun M => P j * M) h1
    simp only [Matrix.mul_add, Matrix.mul_smul, hPH, hS.proj_mul_ne hj, smul_zero,
      add_zero] at this
    have e : (μ i - μ j) • (P j * Q) = P j * K * P i := by
      rw [sub_smul, ← this, Matrix.mul_assoc]; abel
    rw [← e, smul_smul, inv_mul_cancel₀ (hS.sub_ne_zero' (Ne.symm hj)), one_smul]
  -- (c) `Q P_j` for `j ≠ i`
  have hc : ∀ j, j ≠ i → Q * P j = (μ i - μ j)⁻¹ • (P i * K * P j) := by
    intro j hj
    have := congrArg (fun M => M * P j) h2
    simp only [Matrix.add_mul, Matrix.smul_mul, hHP, hS.proj_mul_ne (Ne.symm hj), smul_zero,
      add_zero, Matrix.mul_assoc] at this
    have e : (μ i - μ j) • (Q * P j) = P i * K * P j := by
      rw [sub_smul, ← this, Matrix.mul_assoc]; abel
    rw [← e, smul_smul, inv_mul_cancel₀ (hS.sub_ne_zero' (Ne.symm hj)), one_smul]
  -- (d) `P_i Q P_i = 0`
  have hd : P i * Q * P i = 0 := by
    have := congrArg (fun M => P i * M * P i) h3
    simp only [Matrix.mul_add, Matrix.add_mul] at this
    have e1 : P i * (P i * Q) * P i = P i * Q * P i := by
      rw [← Matrix.mul_assoc, hS.proj_mul_self]
    have e2 : P i * (Q * P i) * P i = P i * Q * P i := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hS.proj_mul_self, ← Matrix.mul_assoc]
    rw [e1, e2] at this
    have : P i * Q * P i + P i * Q * P i - P i * Q * P i = 0 := by rw [this]; abel
    simpa using this
  -- (e) assemble `Q = ∑_j P_j Q` and `P_i Q = ∑_l P_i Q P_l`
  have hPiQ : P i * Q = ∑ j ∈ Finset.univ.erase i, (μ i - μ j)⁻¹ • (P i * K * P j) := by
    rw [← hS.sum_mul_proj (P i * Q), ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hd,
      zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Matrix.mul_assoc, hc j (Finset.ne_of_mem_erase hj), Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hS.proj_mul_self]
  rw [← hS.sum_proj_mul Q, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hPiQ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hb j (Finset.ne_of_mem_erase hj), smul_add, add_comm]

end SpecFamily

end BlockBand.SourceProcess.Stochastic.Dyson
