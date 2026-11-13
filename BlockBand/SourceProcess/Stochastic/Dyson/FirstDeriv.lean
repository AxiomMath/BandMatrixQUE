module

public import BlockBand.SourceProcess.Stochastic.Dyson.Smooth
public import BlockBand.SourceProcess.Stochastic.Dyson.PerturbAlgebra
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Dyson Brownian motion: first derivatives of eigenvalues and spectral projections

On the open set `simpleSet N` of coordinates `y` (`H(y) = vecHerm N y`) with simple spectrum:
* `contDiffAt_proj`: `y ↦ P_i(H(y))` (Lagrange product) is `C^n`;
* `hasFDerivAt_lam`, `hasFDerivAt_lamC`, `hasFDerivAt_proj`: `λ_i` and `P_i` are differentiable on
  `simpleSet N`;
* `fderiv_lam_proj`: `Dλ_i(y)[v] = tr(P_i K)`, `K = H(v)`, and
  `DP_i(y)[v] = ∑_{j ≠ i} (λ_i - λ_j)⁻¹ (P_j K P_i + P_i K P_j)`.

Matrices carry the (scoped) `L∞`-operator normed algebra structure `Matrix.Norms.Operator`,
whose topology is the entrywise one; the statements themselves do not depend on that choice.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix Filter Topology
open scoped Matrix ContDiff Matrix.Norms.Operator
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- `vecHerm` as a real-linear map. -/
def vecHermL (N : ℕ) : (Fin (N * N) → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun := vecHerm N
  map_add' y z := by
    simp only [vecHerm, hermOfCoord, Pi.add_apply, Complex.ofReal_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [vecHerm, hermOfCoord, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul, Complex.coe_smul]

/-- `vecHerm` as a continuous real-linear map. -/
def vecHermCLM (N : ℕ) : (Fin (N * N) → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap (vecHermL N)

theorem vecHermCLM_apply (v : Fin (N * N) → ℝ) : vecHermCLM N v = vecHerm N v := rfl

theorem hasFDerivAt_vecHerm (y : Fin (N * N) → ℝ) :
    HasFDerivAt (vecHerm N) (vecHermCLM N) y :=
  (vecHermCLM N).hasFDerivAt

/-- The eigenvalue in coordinates. -/
def lam (N : ℕ) (i : Fin N) (y : Fin (N * N) → ℝ) : ℝ := dysonEigenvalue N (vecHerm N y) i

/-- The spectral projection in coordinates. -/
def proj (N : ℕ) (i : Fin N) (y : Fin (N * N) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  dysonProjection N (vecHerm N y) i

theorem contDiffAt_list_prod {n : WithTop ℕ∞} {ι : Type*} {y : Fin (N * N) → ℝ} (L : List ι)
    (f : ι → (Fin (N * N) → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (hf : ∀ j ∈ L, ContDiffAt ℝ n (f j) y) :
    ContDiffAt ℝ n (fun y => (L.map fun j => f j y).prod) y := by
  induction L with
  | nil => simpa using contDiffAt_const
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf a List.mem_cons_self).mul (ih fun j hj => hf j (List.mem_cons_of_mem a hj))

theorem contDiffAt_lamC {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (i : Fin N) : ContDiffAt ℝ n (fun y => ((lam N i y : ℝ) : ℂ)) y :=
  contDiff_complex_ofReal.contDiffAt.comp y (contDiffAt_eigenvalue hy i)

/-- **Smoothness of the Lagrange projections** on simple spectrum. -/
theorem contDiffAt_proj {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (i : Fin N) : ContDiffAt ℝ n (proj N i) y := by
  have e : proj N i = fun y => (((List.finRange N).filter fun j => j ≠ i).map
      fun j => projFactor N i j (vecHerm N y)).prod := by
    funext y; rfl
  rw [e]
  refine contDiffAt_list_prod _ _ fun j hj => ?_
  have hji : j ≠ i := by simpa using (List.mem_filter.mp hj).2
  unfold projFactor
  refine ContDiffAt.fun_smul (𝕜' := ℂ) ?_ ?_
  · refine ((contDiffAt_lamC hy i).sub (contDiffAt_lamC hy j)).inv ?_
    rw [sub_ne_zero]; exact_mod_cast HasSimpleSpectrum.ne hy hji.symm
  · exact (vecHermCLM N).contDiff.contDiffAt.sub ((contDiffAt_lamC hy j).smul contDiffAt_const)

theorem eventually_simpleSet {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    ∀ᶠ y' in 𝓝 y, y' ∈ simpleSet N :=
  isOpen_simpleSet.mem_nhds hy

theorem specFamily_coord {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    SpecFamily (vecHerm N y) (fun j => proj N j y) (fun j => ((lam N j y : ℝ) : ℂ)) :=
  specFamily_dyson (vecHerm_isHermitian y) hy

theorem hasFDerivAt_proj {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    HasFDerivAt (proj N i) (fderiv ℝ (proj N i) y) y :=
  ((contDiffAt_proj (n := 1) hy i).differentiableAt (by norm_num)).hasFDerivAt

theorem hasFDerivAt_lam {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    HasFDerivAt (lam N i) (fderiv ℝ (lam N i) y) y :=
  ((contDiffAt_eigenvalue (n := 1) hy i).differentiableAt (by norm_num)).hasFDerivAt

theorem hasFDerivAt_lamC {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    HasFDerivAt (fun y => ((lam N i y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ (lam N i) y))
      y :=
  Complex.ofRealCLM.hasFDerivAt.comp y (hasFDerivAt_lam hy i)

/-- **First variation** (Hadamard): `Dλ_i[v] = tr(P_i K)` and
`DP_i[v] = ∑_{j ≠ i} (λ_i - λ_j)⁻¹ (P_j K P_i + P_i K P_j)`, `K = H(v)`. -/
theorem fderiv_lam_proj {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    (v : Fin (N * N) → ℝ) :
    ((fderiv ℝ (lam N i) y v : ℝ) : ℂ) = trace (proj N i y * vecHerm N v) ∧
      fderiv ℝ (proj N i) y v = ∑ j ∈ Finset.univ.erase i,
        (((lam N i y : ℝ) : ℂ) - ((lam N j y : ℝ) : ℂ))⁻¹ •
          (proj N j y * vecHerm N v * proj N i y + proj N i y * vecHerm N v * proj N j y) := by
  have hP := hasFDerivAt_proj hy i
  have hLC := hasFDerivAt_lamC hy i
  have hH := hasFDerivAt_vecHerm (N := N) y
  -- `H P_i = λ_i P_i`
  have u1 := (hH.fun_mul' hP).unique ((hLC.fun_smul hP).congr_of_eventuallyEq
    (by filter_upwards [eventually_simpleSet hy] with y' hy'
        exact mul_proj (vecHerm_isHermitian y') hy' i))
  -- `P_i H = λ_i P_i`
  have u2 := (hP.fun_mul' hH).unique ((hLC.fun_smul hP).congr_of_eventuallyEq
    (by filter_upwards [eventually_simpleSet hy] with y' hy'
        exact proj_mul (vecHerm_isHermitian y') hy' i))
  -- `P_i P_i = P_i`
  have u3 := (hP.fun_mul' hP).unique (hP.congr_of_eventuallyEq
    (by filter_upwards [eventually_simpleSet hy] with y' hy'
        exact (specFamily_coord hy').proj_mul_self i))
  have k1 := congrArg (fun L => L v) u1
  have k2 := congrArg (fun L => L v) u2
  have k3 := congrArg (fun L => L v) u3
  simp only [FunLike.coe_add, Pi.add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply] at k1 k2 k3
  set Q := fderiv ℝ (proj N i) y v
  set l : ℂ := ((fderiv ℝ (lam N i) y v : ℝ) : ℂ)
  have k1' : vecHerm N y * Q + vecHerm N v * proj N i y =
      ((lam N i y : ℝ) : ℂ) • Q + l • proj N i y := k1
  have k2' : Q * vecHerm N y + proj N i y * vecHerm N v =
      ((lam N i y : ℝ) : ℂ) • Q + l • proj N i y := by
    rw [add_comm]; exact k2
  have k3' : proj N i y * Q + Q * proj N i y = Q := k3
  exact (specFamily_coord hy).firstOrder i k1' k2' k3'

end BlockBand.SourceProcess.Stochastic.Dyson
