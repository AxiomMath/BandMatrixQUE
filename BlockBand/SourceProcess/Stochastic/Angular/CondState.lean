module

public import BlockBand.SourceProcess.Stochastic.Angular.Conj
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularIdent

/-!
# Complex angular martingale problem: the conditioning state

The state is `z = (y, V₀, V₁, t) ∈ ℝ^{N² + 3}` with `y = hermVec H`: drift
`(0, θ·b(λ(y)), A(y), 1)` (`condDrift`) and covariance `diag(I/N, 0)` (`condCov`). It replaces
the overlap state `(λ, X, …)` of the Dyson angular martingale problem.

This file contains:
* `sum_fderiv_lam_mul`: `⟨∇λ_i, ∇λ_j⟩ = δ_ij` in the coordinates;
* the coordinates `cstY`, `cstW`, the projections `stY`, `stW`, the drift `condDrift`, the
  covariance `condCov` and the contraction `sum_condCov`.

These are the inputs of `itoDrift_Pcond`: for `Pcond = e^{c_θ t} h(θ·λ(y) - V₀) (φ(y) - V₁)`, the
Itô drift vanishes on `simpleSet × ℝ³`, by `genL_mul`, `lapl_lam`, `sum_fderiv_lam_mul` and the
two hypotheses on `φ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Matrix Filter Topology
open scoped Matrix ComplexConjugate NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.SourceProcess.Stochastic.Dyson.Angular (genL genL_mul itoDrift_eq_genL
  fderiv_mul_apply fderiv2_eq diff_fderiv_apply fderiv_real_apply fderiv_comp_clm_apply
  fderiv2_comp_clm_apply Trig cθ contDiff_trig)

variable {N : ℕ}

/-!
### Orthonormal eigenvalue gradients
-/

/-- `⟨∇λ_i, ∇λ_j⟩ = δ_ij` in the coordinates. -/
theorem sum_fderiv_lam_mul {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i j : Fin N) :
    ∑ a, fderiv ℝ (lam N i) y (Pi.single a 1) * fderiv ℝ (lam N j) y (Pi.single a 1) =
      if i = j then 1 else 0 := by
  have hl : ∀ k a, fderiv ℝ (lam N k) y (Pi.single a 1) = hermVec N (proj N k y) a := by
    intro k a
    have h := congrFun (sum_fderiv_lam_smul hy k) a
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    exact h
  simp_rw [hl]
  have hH := vecHerm_isHermitian y
  rw [sum_hermVec_mul (A := proj N i y) (B := proj N j y) (proj_isHermitian hH hy i) (proj_isHermitian hH hy j),
    show proj N i y * proj N j y = _ from proj_mul_proj hH hy i j]
  split_ifs with h
  · subst h; rw [trace_proj hH hy i]; simp
  · simp

/-!
### The state
-/

/-- The `y` coordinates of the state. -/
def cstY (a : Fin (N * N)) : Fin (N * N + 3) := Fin.castAdd 3 a
/-- The auxiliary coordinates `V₀, V₁, t`. -/
def cstW (N : ℕ) (k : Fin 3) : Fin (N * N + 3) := Fin.natAdd (N * N) k

/-- The `y` block. -/
def stY (N : ℕ) : (Fin (N * N + 3) → ℝ) →L[ℝ] (Fin (N * N) → ℝ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (cstY a)
/-- An auxiliary coordinate. -/
def stW (N : ℕ) (k : Fin 3) : (Fin (N * N + 3) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (cstW N k)

@[simp] theorem stY_apply (z : Fin (N * N + 3) → ℝ) (a : Fin (N * N)) :
    stY N z a = z (cstY a) := rfl
@[simp] theorem stW_apply (z : Fin (N * N + 3) → ℝ) (k : Fin 3) : stW N k z = z (cstW N k) := rfl

theorem stY_single_cstY (a : Fin (N * N)) : stY N (Pi.single (cstY a) 1) = Pi.single a 1 := by
  funext b
  simp only [stY_apply, Pi.single_apply, cstY, (Fin.castAdd_injective _ _).eq_iff]

theorem stY_single_cstW (k : Fin 3) : stY N (Pi.single (cstW N k) 1) = 0 := by
  funext b
  simp [Pi.single_apply, cstY, cstW, Fin.ext_iff]; omega

theorem single_cstW_cstY (k : Fin 3) (a : Fin (N * N)) :
    (Pi.single (cstY a) 1 : Fin (N * N + 3) → ℝ) (cstW N k) = 0 := by
  simp [Pi.single_apply, cstY, cstW, Fin.ext_iff]; omega

/-- `θ·λ(y)`. -/
def thLam (θ : Fin N → ℝ) (y : Fin (N * N) → ℝ) : ℝ := ∑ i, θ i * lam N i y

/-- Drift of the auxiliary coordinates: `(θ·b(λ(y)), A(y), 1)`. -/
def condVd (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (y : Fin (N * N) → ℝ) : Fin 3 → ℝ :=
  ![∑ i, θ i * dysonDrift N (fun j => lam N j y) i, A y, 1]

/-- Joint drift of the state. -/
def condDrift (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (z : Fin (N * N + 3) → ℝ) :
    Fin (N * N + 3) → ℝ :=
  concatCoord (0 : Fin (N * N) → ℝ) (condVd θ A (stY N z))

/-- Joint covariance of the state. -/
def condCov (N : ℕ) : Matrix (Fin (N * N + 3)) (Fin (N * N + 3)) ℝ :=
  concatCov (gueCovVec N) 0 0

theorem stY_condDrift (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (z : Fin (N * N + 3) → ℝ) :
    stY N (condDrift θ A z) = 0 := by
  funext a; simp [condDrift, cstY]

theorem condDrift_cstW (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (z : Fin (N * N + 3) → ℝ)
    (k : Fin 3) : condDrift θ A z (cstW N k) = condVd θ A (stY N z) k := by
  simp [condDrift, cstW]

/-- **Covariance contraction**: only the `y` block, with weight `1/N`. -/
theorem sum_condCov (F : Fin (N * N + 3) → Fin (N * N + 3) → ℝ) :
    ∑ k, ∑ l, condCov N k l * F k l = (1 / (N : ℝ)) * ∑ a, F (cstY a) (cstY a) := by
  simp only [condCov, concatCov, Fin.sum_univ_add, Matrix.of_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    gueCovVec_eq, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.mul_sum, Matrix.transpose_zero]
  rfl

end BlockBand.SourceProcess.Stochastic.ComplexAngular
