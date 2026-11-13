module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularGenerator
public import BlockBand.SourceProcess.Stochastic.Bridges.Concat

/-!
# The augmented Dyson state `(λ, X, ∫θ·b, ∫𝒜f, t)` and its characteristics

Coordinates of `ℝ^{(N+N)+3}`: `cL i` (eigenvalue `λ_i`), `cX i` (overlap `X_i`), `cV 0`
(`∫ θ·b(λ)`), `cV 1` (`∫ 𝒜 f`), `cV 2` (clock). `plusDrift θ f` and `plusCov` are the joint
drift and covariance: the `(λ, X)` block from contract (b2) and zero covariance for the
absolutely continuous coordinates. `sum_plusCov` evaluates covariance contractions: only the
diagonal `λ` block `I/N` and the overlap block `ovlCov` contribute (the `λ`–`X` block vanishes).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open Filter Topology
open scoped NNReal ContDiff
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges

variable {N : ℕ}

/-- Eigenvalue coordinate `λ_i`. -/
def cL (i : Fin N) : Fin ((N + N) + 3) := Fin.castAdd 3 (Fin.castAdd N i)
/-- Overlap coordinate `X_i`. -/
def cX (i : Fin N) : Fin ((N + N) + 3) := Fin.castAdd 3 (Fin.natAdd N i)
/-- Auxiliary coordinates. -/
def cV (N : ℕ) (k : Fin 3) : Fin ((N + N) + 3) := Fin.natAdd (N + N) k

/-- The `(λ, X)` block. -/
def prY (N : ℕ) : (Fin ((N + N) + 3) → ℝ) →L[ℝ] (Fin (N + N) → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd 3 i)
/-- The overlap block. -/
def prX (N : ℕ) : (Fin ((N + N) + 3) → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (cX i)
/-- An auxiliary coordinate. -/
def prV (N : ℕ) (k : Fin 3) : (Fin ((N + N) + 3) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (cV N k)
/-- `ℓ_θ(y) = θ·λ - V₀`, the phase of the exponential martingale. -/
def ell (θ : Fin N → ℝ) : (Fin ((N + N) + 3) → ℝ) →L[ℝ] ℝ :=
  ∑ i, θ i • ContinuousLinearMap.proj (cL i) - ContinuousLinearMap.proj (cV N 0)

@[simp] theorem prY_apply (y : Fin ((N + N) + 3) → ℝ) (i : Fin (N + N)) :
    prY N y i = y (Fin.castAdd 3 i) := rfl
@[simp] theorem prX_apply (y : Fin ((N + N) + 3) → ℝ) (i : Fin N) : prX N y i = y (cX i) := rfl
@[simp] theorem prV_apply (y : Fin ((N + N) + 3) → ℝ) (k : Fin 3) : prV N k y = y (cV N k) := rfl
theorem ell_apply (θ : Fin N → ℝ) (y : Fin ((N + N) + 3) → ℝ) :
    ell θ y = ∑ i, θ i * y (cL i) - y (cV N 0) := by simp [ell]

/-- Eigenvalue and overlap parts of a `(λ, X)` state. -/
def lamOf (y : Fin (N + N) → ℝ) : Fin N → ℝ := fun i => y (Fin.castAdd N i)
def xOf (y : Fin (N + N) → ℝ) : Fin N → ℝ := fun i => y (Fin.natAdd N i)

theorem lamOf_eq (y : Fin (N + N) → ℝ) : lamOf y = fun i => y (Fin.castAdd N i) := rfl
theorem xOf_eq (y : Fin (N + N) → ℝ) : xOf y = fun i => y (Fin.natAdd N i) := rfl

/-- Drift of the auxiliary coordinates. -/
def vdOf (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin (N + N) → ℝ) : Fin 3 → ℝ :=
  ![∑ i, θ i * dysonDrift N (lamOf y) i, angularGenerator N (lamOf y) f (xOf y), 1]

/-- Joint drift of the augmented state. -/
def plusDrift (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) :
    Fin ((N + N) + 3) → ℝ :=
  concatCoord (dysonStateDrift N (prY N y)) (vdOf θ f (prY N y))

/-- Joint covariance of the augmented state. -/
def plusCov (y : Fin ((N + N) + 3) → ℝ) : Matrix (Fin ((N + N) + 3)) (Fin ((N + N) + 3)) ℝ :=
  concatCov (dysonStateCov N (prY N y)) 0 0

theorem prY_concatCoord (u : Fin (N + N) → ℝ) (v : Fin 3 → ℝ) :
    prY N (concatCoord u v) = u := by ext i; simp

theorem plusDrift_cL (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ)
    (i : Fin N) : plusDrift θ f y (cL i) = dysonDrift N (lamOf (prY N y)) i := by
  simp [plusDrift, cL, dysonStateDrift, lamOf_eq]

theorem plusDrift_cX (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ)
    (i : Fin N) : plusDrift θ f y (cX i) = ovlDrift N (lamOf (prY N y)) (xOf (prY N y)) i := by
  simp only [plusDrift, cX, concatCoord_castAdd, dysonStateDrift, finSumFinEquiv_symm_apply_natAdd]
  simp [lamOf_eq, xOf_eq, ovlDrift]

theorem plusDrift_cV0 (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) :
    plusDrift θ f y (cV N 0) = ∑ i, θ i * dysonDrift N (lamOf (prY N y)) i := by
  simp [plusDrift, cV, vdOf]

theorem plusDrift_cV1 (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) :
    plusDrift θ f y (cV N 1) = angularGenerator N (lamOf (prY N y)) f (xOf (prY N y)) := by
  simp [plusDrift, cV, vdOf]

theorem plusDrift_cV2 (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) :
    plusDrift θ f y (cV N 2) = 1 := by
  simp [plusDrift, cV, vdOf]

/-- **Covariance contractions of the augmented state.** -/
theorem sum_plusCov (y : Fin ((N + N) + 3) → ℝ) (F : Fin ((N + N) + 3) → Fin ((N + N) + 3) → ℝ) :
    ∑ k, ∑ l, plusCov y k l * F k l = (1 / (N : ℝ)) * ∑ i, F (cL i) (cL i) +
      ∑ i, ∑ j, ovlCov N (lamOf (prY N y)) (xOf (prY N y)) i j * F (cX i) (cX j) := by
  simp only [plusCov, concatCov, Fin.sum_univ_add, Matrix.of_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.transpose_apply, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp only [dysonStateCov, Matrix.of_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, prY_apply]
  simp only [Finset.mul_sum, cL, cX, ovlCov, lamOf_eq, xOf_eq, prY_apply, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-!
### Values of coordinate functionals on basis vectors
-/

theorem cL_injective : Function.Injective (cL (N := N)) := fun i j h => by
  simpa [cL] using h
theorem cX_injective : Function.Injective (cX (N := N)) := fun i j h => by
  simpa [cX] using h
theorem cL_ne_cX (i j : Fin N) : cL i ≠ cX j := by
  intro h; simp [cL, cX, Fin.ext_iff] at h; omega
theorem cL_ne_cV (i : Fin N) (k : Fin 3) : cL i ≠ cV N k := by
  intro h; simp [cL, cV, Fin.ext_iff] at h; omega
theorem cX_ne_cV (i : Fin N) (k : Fin 3) : cX i ≠ cV N k := by
  intro h; simp [cX, cV, Fin.ext_iff] at h; omega

theorem single_cL_apply (i : Fin N) (k : Fin ((N + N) + 3)) :
    (Pi.single (cL i) (1 : ℝ) : Fin ((N + N) + 3) → ℝ) k = if k = cL i then 1 else 0 := by
  by_cases h : k = cL i <;> simp [h]

theorem ell_single_cL (θ : Fin N → ℝ) (i : Fin N) : ell θ (Pi.single (cL i) 1) = θ i := by
  rw [ell_apply]
  simp only [Pi.single_apply, cL_injective.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, (cL_ne_cV i 0).symm, ite_false, sub_zero]

theorem ell_single_cX (θ : Fin N → ℝ) (i : Fin N) : ell θ (Pi.single (cX i) 1) = 0 := by
  rw [ell_apply]
  simp [(cL_ne_cX _ i).symm, (cX_ne_cV i 0).symm]

theorem ell_plusDrift (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) :
    ell θ (plusDrift θ f y) = 0 := by
  rw [ell_apply, plusDrift_cV0]; simp_rw [plusDrift_cL]; ring

theorem prX_single_cL (i : Fin N) : prX N (Pi.single (cL i) 1) = 0 := by
  ext j; simp [(cL_ne_cX i j).symm]

theorem prX_single_cX (i : Fin N) : prX N (Pi.single (cX i) 1) = Pi.single i 1 := by
  ext j; simp [Pi.single_apply, cX_injective.eq_iff]

theorem single_cV_cL (k : Fin 3) (i : Fin N) :
    (Pi.single (cL i) (1 : ℝ) : Fin ((N + N) + 3) → ℝ) (cV N k) = 0 := by
  simp [(cL_ne_cV i k).symm]

theorem single_cV_cX (k : Fin 3) (i : Fin N) :
    (Pi.single (cX i) (1 : ℝ) : Fin ((N + N) + 3) → ℝ) (cV N k) = 0 := by
  simp [(cX_ne_cV i k).symm]

theorem prX_plusDrift (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) :
    prX N (plusDrift θ f y) = ovlDrift N (lamOf (prY N y)) (xOf (prY N y)) := by
  ext i; simp only [prX_apply]; exact plusDrift_cX θ f y i

theorem prX_eq_xOf (y : Fin ((N + N) + 3) → ℝ) : prX N y = xOf (prY N y) := by
  ext i; simp [xOf_eq, cX]

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
