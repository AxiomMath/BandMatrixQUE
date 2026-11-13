module

public import BlockBand.Endpoints.Response.FractionalTraceJensen

/-!
# The Klein upper bound of a fresh fractional clock and its linear fluctuation

Part of the remote higher-moment theorem. Deterministic matrix facts for the higher one-layer
step.

* `rhc_trace_spec_mul` — `Tr(V diag(g) V* M) = Σ_i g_i (V*MV)_ii`.
* `rhc_klein_sandwich` — **Klein's inequality at the old clock**: for `A ⪰ 0` with eigenbasis
  `V`, eigenvalues `λ`, and `U ⪰ 0`,
  `Tr(A^{1/2} U A^{1/2})^p ≤ (1 - p) Tr A^p + p Σ_i λ_i^p Re (V*UV)_ii` (`0 < p < 1`).
  Proved from `ftj_klein` at `A + ε` and `ε ↓ 0`; no derivative of `Tr(·)^p`.
  With `U = LL*` this bounds the new clock `H_p(L*AL)` by an affine function of `LL*`, whose
  mean is controlled by `OnePortPassiveMean` and whose fluctuation is a sum of centered bilinear
  entries (`PassiveSourceMixingContract.oneStepFluctuation`).
* `rhc_diag_le_of_posSemidef_sub` — `Re (V*ŪV)_ii ≤ c` when `c I - Ū ⪰ 0`, `V` unitary.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Tr(V diag(g) V* M) = Σ_i g_i (V*MV)_ii`. -/
theorem rhc_trace_spec_mul (V M : Matrix n n ℂ) (g : n → ℝ) :
    (ftj_spec V g * M).trace = ∑ i, ((g i : ℝ) : ℂ) * (star V * M * V) i i := by
  unfold ftj_spec
  have := trace_mul_comm V (diagonal (fun i => ((g i : ℝ) : ℂ)) * star V * M)
  rw [show V * diagonal (fun i => ((g i : ℝ) : ℂ)) * star V * M =
      V * (diagonal (fun i => ((g i : ℝ) : ℂ)) * star V * M) by simp only [Matrix.mul_assoc],
    this]
  simp only [trace, diag_apply, Matrix.mul_assoc, diagonal_mul]

/-- `Re (V*ŪV)_ii ≤ c` when `c I - Ū ⪰ 0` and `V` is unitary. -/
theorem rhc_diag_le_of_posSemidef_sub {V Ub : Matrix n n ℂ} (hV : V ∈ unitaryGroup n ℂ) {c : ℝ}
    (h : (((c : ℝ) : ℂ) • (1 : Matrix n n ℂ) - Ub).PosSemidef) (i : n) :
    ((star V * Ub * V) i i).re ≤ c := by
  have hP := (h.conjTranspose_mul_mul_same V).diag_nonneg (i := i)
  rw [← star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ftj_star_mul_self hV, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq] at hP
  have := (Complex.le_def.mp hP).1
  simp only [Complex.zero_re, Complex.sub_re, smul_eq_mul, mul_one, Complex.ofReal_re] at this
  linarith

omit [DecidableEq n] in
/-- The diagonal of `V*UV` is real-nonnegative for `U ⪰ 0`. -/
theorem rhc_diag_re_nonneg {U : Matrix n n ℂ} (hU : U.PosSemidef) (V : Matrix n n ℂ) (i : n) :
    0 ≤ ((star V * U * V) i i).re := by
  have hP := (hU.conjTranspose_mul_mul_same V).diag_nonneg (i := i)
  rw [← star_eq_conjTranspose] at hP
  exact (Complex.le_def.mp hP).1

end General

variable {W : ℕ}

/-- **Klein's inequality at the old clock** (`0 < p < 1`, `A, U ⪰ 0`):
`Tr(A^{1/2} U A^{1/2})^p ≤ (1 - p) Tr A^p + p Σ_i λ_i^p Re (V*UV)_ii`, `V`, `λ` the eigenbasis and
eigenvalues of `A` (`cej_sqrt` is `A^{1/2}`). -/
theorem rhc_klein_sandwich {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {A U : Matrix (Fin W) (Fin W) ℂ}
    (hA : A.PosSemidef) (hU : U.PosSemidef) :
    fracTrace p (cej_sqrt hA * U * cej_sqrt hA) ≤
      (1 - p) * fracTrace p A + p * ∑ i, hA.isHermitian.eigenvalues i ^ p *
        ((star (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) * U *
          (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) i i).re := by
  set V : Matrix (Fin W) (Fin W) ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
    with hVdef
  have hV : V ∈ unitaryGroup (Fin W) ℂ := hA.isHermitian.eigenvectorUnitary.2
  set lam := hA.isHermitian.eigenvalues with hlam
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => hA.eigenvalues_nonneg i
  set S := cej_sqrt hA
  set Y := S * U * S with hYdef
  have hY : Y.PosSemidef := by
    have := hU.conjTranspose_mul_mul_same S
    rwa [cej_sqrt_conjTranspose] at this
  set u : Fin W → ℝ := fun i => ((star V * U * V) i i).re with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => rhc_diag_re_nonneg hU V i
  set R := ∑ i, lam i ^ p * u i
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hlam0 i) _) (hu0 i)
  have hH : fracTrace p A = ∑ i, lam i ^ p := fracTrace_eq_sum_eigenvalues_of_posSemidef hA p
  -- the regularized bound
  have key : ∀ ε : ℝ, 0 < ε →
      fracTrace p Y ≤ (1 - p) * (fracTrace p A + Fintype.card (Fin W) * ε ^ p) + p * R := by
    intro ε hε
    set x : Fin W → ℝ := fun i => lam i + ε with hx
    have hxp : ∀ i, 0 < x i := fun i => by simp only [hx]; linarith [hlam0 i]
    have hYh := hY.isHermitian
    set Wv : Matrix (Fin W) (Fin W) ℂ := (hYh.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
    have hWv : Wv ∈ unitaryGroup (Fin W) ℂ := hYh.eigenvectorUnitary.2
    have hy0 : ∀ j, 0 ≤ hYh.eigenvalues j := fun j => hY.eigenvalues_nonneg j
    have kl := ftj_klein hp0.le hp1.le hV hWv x hYh.eigenvalues hxp hy0
    rw [← ftj_spec_eigen hYh, ← fracTrace_eq_sum_eigenvalues_of_posSemidef hY p, Matrix.mul_sub,
      trace_sub, Complex.sub_re] at kl
    -- `Re Tr(∇X · Y)`
    have e1 : (ftj_grad p V x * Y).trace.re = p * ∑ i, x i ^ (p - 1) * (lam i * u i) := by
      unfold ftj_grad
      rw [rhc_trace_spec_mul, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hYdef, cej_sandwich_entry hA U i i]
      have hs : ((Real.sqrt (lam i) : ℝ) : ℂ) * (star V * U * V) i i *
          ((Real.sqrt (lam i) : ℝ) : ℂ) = ((lam i : ℝ) : ℂ) * (star V * U * V) i i := by
        rw [mul_comm _ ((Real.sqrt (lam i) : ℝ) : ℂ), ← mul_assoc, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (hlam0 i)]
      rw [hs, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
      simp only [hu]; ring
    -- `Re Tr(∇X · X) = p Σ x^p`
    have e2 : (ftj_grad p V x * ftj_spec V x).trace.re = p * ∑ i, x i ^ p := by
      unfold ftj_grad
      rw [ftj_trace_spec_same hV, Complex.ofReal_re, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, ← Real.rpow_add_one (hxp i).ne', sub_add_cancel]
    rw [e1, e2] at kl
    -- termwise bounds
    have b1 : ∀ i, x i ^ (p - 1) * (lam i * u i) ≤ lam i ^ p * u i := by
      intro i
      rcases (hlam0 i).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul, mul_zero]; exact mul_nonneg (Real.rpow_nonneg le_rfl _) (hu0 i)
      · have : x i ^ (p - 1) * lam i ≤ lam i ^ p := by
          have h1 : x i ^ (p - 1) ≤ lam i ^ (p - 1) :=
            Real.rpow_le_rpow_of_nonpos h0 (by simp only [hx]; linarith) (by linarith)
          calc x i ^ (p - 1) * lam i ≤ lam i ^ (p - 1) * lam i :=
                mul_le_mul_of_nonneg_right h1 h0.le
            _ = lam i ^ p := by rw [← Real.rpow_add_one h0.ne', sub_add_cancel]
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right this (hu0 i)
    have b2 : ∑ i, x i ^ p ≤ fracTrace p A + Fintype.card (Fin W) * ε ^ p := by
      rw [hH, Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ =>
        Real.rpow_add_le_add_rpow (hlam0 i) hε.le hp0.le hp1.le
    have b1' : ∑ i, x i ^ (p - 1) * (lam i * u i) ≤ R := Finset.sum_le_sum fun i _ => b1 i
    have : p * ∑ i, x i ^ (p - 1) * (lam i * u i) ≤ p * R := mul_le_mul_of_nonneg_left b1' hp0.le
    nlinarith
  -- `ε ↓ 0`
  refine le_of_forall_pos_lt_add fun η hη => ?_
  set N : ℝ := (Fintype.card (Fin W) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set ε := (η / (2 * (N + 1))) ^ (1 / p) with hε
  have hεpos : 0 < ε := Real.rpow_pos_of_pos (by positivity) _
  have hεp : ε ^ p = η / (2 * (N + 1)) := by
    rw [hε, ← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
  have h := key ε hεpos
  rw [hεp] at h
  have : (1 - p) * (N * (η / (2 * (N + 1)))) < η := by
    have h1 : N * (η / (2 * (N + 1))) < η := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
    have h2 : 0 ≤ N * (η / (2 * (N + 1))) := by positivity
    nlinarith
  calc fracTrace p (S * U * S) ≤ (1 - p) * (fracTrace p A + N * (η / (2 * (N + 1)))) + p * R := h
    _ < (1 - p) * fracTrace p A + p * R + η := by nlinarith

end BlockBand.Endpoints
