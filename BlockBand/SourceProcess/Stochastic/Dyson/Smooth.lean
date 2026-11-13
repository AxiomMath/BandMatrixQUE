module

public import BlockBand.SourceProcess.Stochastic.Dyson.Lagrange
public import BlockBand.SourceProcess.Stochastic.Dyson.BrownianSemimartingale
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Dyson Brownian motion: smoothness of the ordered eigenvalues on simple spectrum

In the coordinates `vecHerm N : ℝ^{N·N} → Herm_N`, with `simpleSet N` the (open) set of
coordinates of matrices with simple spectrum:
* `charFun_eq_prod`: `Re det(x - H(y)) = ∏_m (x - λ_m(y))`;
* `contDiffAt_eigenvalue`: every `y ↦ λ_i(H(y))` is `C^n` (any `n`) at every point of
  `simpleSet N`, by the implicit function theorem applied to the characteristic polynomial at the
  simple root `λ_i` (its `x`-derivative is `∏_{m ≠ i} (λ_i - λ_m) ≠ 0`), together with the
  continuity of the ordered eigenvalues, which selects the implicit branch.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix Filter Topology
open scoped Matrix ContDiff
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

@[fun_prop]
theorem contDiff_complex_ofReal {n : WithTop ℕ∞} : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

/-- Coordinates of matrices with simple spectrum. -/
def simpleSet (N : ℕ) : Set (Fin (N * N) → ℝ) := {y | HasSimpleSpectrum N (vecHerm N y)}

theorem isOpen_simpleSet : IsOpen (simpleSet N) :=
  isOpen_hasSimpleSpectrum.preimage continuous_vecHerm

/-- The characteristic function `(y, x) ↦ Re det(x - H(y))`. -/
def charFun (N : ℕ) (p : (Fin (N * N) → ℝ) × ℝ) : ℝ :=
  (det ((p.2 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - vecHerm N p.1)).re

theorem contDiff_charFun {n : WithTop ℕ∞} : ContDiff ℝ n (charFun N) := by
  unfold charFun
  refine Complex.reCLM.contDiff.comp ?_
  simp only [det_apply, vecHerm, hermOfCoord, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.one_apply, Units.smul_def, zsmul_eq_mul]
  fun_prop

/-- `det(x - H) = ∏_m (x - λ_m)` for Hermitian `H`. -/
theorem det_sub_eq_prod {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (x : ℝ) :
    det ((x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H) =
      ∏ m, ((x : ℂ) - dysonEigenvalue N H m) := by
  have hone : (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
      specU H * diagonal (fun _ => (x : ℂ)) * star (specU H) := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      specU_mul_star]
  have key : (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H =
      specU H * diagonal (fun k => (x : ℂ) - dysonEigenvalue N H (specPerm N k)) *
        star (specU H) := by
    rw [hone]
    conv_lhs => arg 2; rw [spectral_eq hH]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  rw [key, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, specU_star_mul, det_one,
    one_mul, det_diagonal]
  exact Fintype.prod_equiv (specPerm N) _ _ (fun k => rfl)

theorem charFun_eq_prod (y : Fin (N * N) → ℝ) (x : ℝ) :
    charFun N (y, x) = ∏ m, (x - dysonEigenvalue N (vecHerm N y) m) := by
  unfold charFun
  rw [det_sub_eq_prod (vecHerm_isHermitian y)]
  rw [show ∏ m, ((x : ℂ) - dysonEigenvalue N (vecHerm N y) m) =
    ((∏ m, (x - dysonEigenvalue N (vecHerm N y) m) : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.ofReal_re _

theorem charFun_eigenvalue (y : Fin (N * N) → ℝ) (i : Fin N) :
    charFun N (y, dysonEigenvalue N (vecHerm N y) i) = 0 := by
  rw [charFun_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

/-- The `x`-derivative of `∏_m (x - λ_m)` at a simple root `λ_i`. -/
theorem hasDerivAt_prod_sub (c : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun x => ∏ m, (x - c m)) (∏ m ∈ Finset.univ.erase i, (c i - c m)) (c i) := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun m (x : ℝ) => x - c m)
    (f' := fun _ => 1) (x := c i) (fun m _ => (hasDerivAt_id (c i)).sub_const (c m))
  convert h using 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro m _ hm
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hm, Finset.mem_univ i⟩) (sub_self _),
      zero_smul]
  · simp

theorem prod_erase_ne_zero {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    ∏ m ∈ Finset.univ.erase i,
      (dysonEigenvalue N (vecHerm N y) i - dysonEigenvalue N (vecHerm N y) m) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun m hm => sub_ne_zero.mpr ?_
  exact HasSimpleSpectrum.ne hy (Finset.ne_of_mem_erase hm).symm

/-- The partial `x`-derivative of `charFun` at `(y, λ_i(y))`, as a value of the `fderiv`. -/
theorem fderiv_charFun_inr (y : Fin (N * N) → ℝ) (i : Fin N) :
    fderiv ℝ (charFun N) (y, dysonEigenvalue N (vecHerm N y) i) (0, 1) =
      ∏ m ∈ Finset.univ.erase i,
        (dysonEigenvalue N (vecHerm N y) i - dysonEigenvalue N (vecHerm N y) m) := by
  set c := fun m => dysonEigenvalue N (vecHerm N y) m
  have hd : HasFDerivAt (charFun N) (fderiv ℝ (charFun N) (y, c i)) (y, c i) :=
    ((contDiff_charFun (n := 1)).differentiable (by norm_num) _).hasFDerivAt
  have hline : HasDerivAt (fun x : ℝ => ((y, x) : (Fin (N * N) → ℝ) × ℝ)) (0, 1) (c i) :=
    HasDerivAt.prodMk (hasDerivAt_const _ y) (hasDerivAt_id _)
  have h1 := hd.comp_hasDerivAt (c i) hline
  have h2 : HasDerivAt (fun x => charFun N (y, x)) (∏ m ∈ Finset.univ.erase i, (c i - c m))
      (c i) := by
    have := hasDerivAt_prod_sub c i
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    exact charFun_eq_prod y x
  exact h1.unique h2

theorem isInvertible_fderiv_charFun_inr {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (i : Fin N) :
    (fderiv ℝ (charFun N) (y, dysonEigenvalue N (vecHerm N y) i) ∘L
      ContinuousLinearMap.inr ℝ (Fin (N * N) → ℝ) ℝ).IsInvertible := by
  set d := ∏ m ∈ Finset.univ.erase i,
    (dysonEigenvalue N (vecHerm N y) i - dysonEigenvalue N (vecHerm N y) m)
  have hd : d ≠ 0 := prod_erase_ne_zero hy i
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hd), ?_⟩
  refine ContinuousLinearMap.ext_ring ?_
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply,
    Units.val_mk0, one_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  exact (fderiv_charFun_inr y i).symm

/-- **Smoothness of the ordered eigenvalues on simple spectrum** (implicit function theorem). -/
theorem contDiffAt_eigenvalue {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (i : Fin N) :
    ContDiffAt ℝ n (fun y => dysonEigenvalue N (vecHerm N y) i) y := by
  set u : (Fin (N * N) → ℝ) × ℝ := (y, dysonEigenvalue N (vecHerm N y) i)
  have cdf : ContDiffAt ℝ (max n 1) (charFun N) u := contDiff_charFun.contDiffAt
  have pn : max n 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hinv := isInvertible_fderiv_charFun_inr hy i
  have hψ := cdf.contDiffAt_implicitFunction pn hinv
  have heq := cdf.eventually_apply_eq_iff_implicitFunction pn hinv
  have hcont : Tendsto (fun y' => ((y', dysonEigenvalue N (vecHerm N y') i) :
      (Fin (N * N) → ℝ) × ℝ)) (𝓝 y) (𝓝 u) :=
    (continuous_id.prodMk ((continuous_dysonEigenvalue i).comp continuous_vecHerm)).tendsto y
  have hev : (fun y' => dysonEigenvalue N (vecHerm N y') i) =ᶠ[𝓝 y]
      cdf.implicitFunction pn hinv := by
    filter_upwards [hcont.eventually heq] with y' hy'
    exact ((hy'.mp (by rw [charFun_eigenvalue, charFun_eigenvalue]))).symm
  exact (hψ.of_le (le_max_left _ _)).congr_of_eventuallyEq hev

end BlockBand.SourceProcess.Stochastic.Dyson
