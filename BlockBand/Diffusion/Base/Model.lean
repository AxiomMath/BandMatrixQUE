module

public import BlockBand.Diffusion.Base.Calculus
public import BlockBand.Diffusion.Base.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The linear five-dimensional SDE behind the base diffusion

State `y = (w₀, w₁, v₀, v₁, v₂) ∈ ℝ⁵` (indices `0, 1` and `2, 3, 4`), six drivers, `D₀ ≥ 0`:
* drift `b(y) = (D₀ w, −D₀ v)` (`exDrift`);
* `exPhi y = ((√(1 + |w|²) − 1)/2, (1 − v₂)/2)` maps the state to the strip coordinates.
* `exStart z` is a preimage of `z ∈ [0, ∞) × [0, 1]` with `|v| = 1`.

**Generator identities** (`mpGenerator` with `a = Σ_c σ_c σ_cᵀ`):
* `exGen_comp_exPhi`: for `f ∈ C²(ℝ²)` and `|v| = 1`,
  `𝓛(f ∘ Φ)(y) = (D₀/2)[x(1+x) f_xx + (1+2x) f_x + y(1−y) f_yy + (1−2y) f_y]` at `(x, y) = Φ(y)`;
* `exGen_sphereDefect`: `𝓛((|v|² − 1)²) = 0` everywhere (the sphere is conserved);
* `exGen_lyap_le`: `𝓛|y|² ≤ 3D₀(1 + |y|²)` (nonexplosion).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open BlockBand.SourceProcess.Stochastic

/-!
### Coefficients
-/

/-- Drift `b(y) = (D₀ w, −D₀ v)`. -/
def exDrift (D0 : ℝ) (y : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![D0 * y 0, D0 * y 1, -(D0 * y 2), -(D0 * y 3), -(D0 * y 4)]

/-- Diffusion columns: `√D₀ e₀, √D₀ e₁, √D₀ (w,0)` and `√D₀ (0, e_a × v)`. -/
def exDiff (D0 : ℝ) (c : Fin 6) (y : Fin 5 → ℝ) : Fin 5 → ℝ :=
  (![![√D0, 0, 0, 0, 0], ![0, √D0, 0, 0, 0], ![√D0 * y 0, √D0 * y 1, 0, 0, 0],
      ![0, 0, 0, -(√D0 * y 4), √D0 * y 3], ![0, 0, √D0 * y 4, 0, -(√D0 * y 2)],
      ![0, 0, -(√D0 * y 3), √D0 * y 2, 0]] : Fin 6 → Fin 5 → ℝ) c

/-- Covariance `a = Σ_c σ_c σ_cᵀ`. -/
def exCov (D0 : ℝ) (y : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of fun i j => ∑ c, exDiff D0 c y i * exDiff D0 c y j

/-!
### Weighted sums of squares
-/

/-- `Σ_i wt_i y_i²`. -/
def wsq (wt : Fin 5 → ℝ) (y : Fin 5 → ℝ) : ℝ := ∑ i, wt i * (y i * y i)

theorem contDiff_wsq (wt : Fin 5 → ℝ) : ContDiff ℝ ⊤ (wsq wt) := by
  unfold wsq
  fun_prop

theorem fderiv_wsq (wt y h : Fin 5 → ℝ) :
    fderiv ℝ (wsq wt) y h = ∑ i, 2 * wt i * y i * h i := by
  have H : HasFDerivAt (wsq wt) (∑ i, wt i • (y i • ContinuousLinearMap.proj i +
      y i • ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ)) y := by
    unfold wsq
    exact HasFDerivAt.fun_sum fun i _ =>
      ((hasFDerivAt_apply i y).mul (hasFDerivAt_apply i y)).const_mul (wt i)
  rw [H.fderiv]
  simp only [sum_apply, smul_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem fderiv_fderiv_wsq (wt y h k : Fin 5 → ℝ) :
    fderiv ℝ (fderiv ℝ (wsq wt)) y h k = ∑ i, 2 * wt i * h i * k i := by
  rw [fderiv_fderiv_apply ((differentiable_fderiv_of_contDiff_two
    ((contDiff_wsq wt).of_le le_top)) y)]
  have e : (fun z => fderiv ℝ (wsq wt) z k) = fun z => ∑ i, 2 * wt i * (z i * k i) :=
    funext fun z => by simp only [fderiv_wsq, mul_assoc]
  have H : HasFDerivAt (fun z : Fin 5 → ℝ => ∑ i, 2 * wt i * (z i * k i))
      (∑ i, (2 * wt i) • (k i • ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ)) y :=
    HasFDerivAt.fun_sum fun i _ => ((hasFDerivAt_apply i y).mul_const (k i)).const_mul (2 * wt i)
  rw [e, H.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem wsq_nonneg {wt : Fin 5 → ℝ} (hwt : ∀ i, 0 ≤ wt i) (y : Fin 5 → ℝ) : 0 ≤ wsq wt y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hwt i) (mul_self_nonneg _)

/-!
### The hyperbolic coordinate
-/

/-- Weights of `|w|²`. -/
def wW : Fin 5 → ℝ := ![1, 1, 0, 0, 0]

/-- Weights of `|v|²`. -/
def wV : Fin 5 → ℝ := ![0, 0, 1, 1, 1]

theorem wW_nonneg (i : Fin 5) : 0 ≤ wW i := by
  fin_cases i <;> simp [wW]

theorem wV_nonneg (i : Fin 5) : 0 ≤ wV i := by
  fin_cases i <;> simp [wV]

/-- `s = √(1 + |w|²)` (`= 1 + 2X`). -/
def exS (y : Fin 5 → ℝ) : ℝ := √(1 + wsq wW y)

theorem one_add_wsq_pos (y : Fin 5 → ℝ) : 0 < 1 + wsq wW y := by
  have := wsq_nonneg wW_nonneg y
  linarith

theorem exS_pos (y : Fin 5 → ℝ) : 0 < exS y := Real.sqrt_pos.2 (one_add_wsq_pos y)

theorem exS_sq (y : Fin 5 → ℝ) : exS y ^ 2 = 1 + wsq wW y :=
  Real.sq_sqrt (one_add_wsq_pos y).le

theorem one_le_exS (y : Fin 5 → ℝ) : 1 ≤ exS y := by
  have h := exS_sq y
  have h0 := exS_pos y
  have := wsq_nonneg wW_nonneg y
  nlinarith

theorem contDiff_exS : ContDiff ℝ ⊤ exS :=
  (contDiff_const.add (contDiff_wsq wW)).sqrt fun y => (one_add_wsq_pos y).ne'

theorem fderiv_exS (y h : Fin 5 → ℝ) :
    fderiv ℝ exS y h = fderiv ℝ (wsq wW) y h / (2 * exS y) := by
  have hQ : HasFDerivAt (fun z => 1 + wsq wW z) (fderiv ℝ (wsq wW) y) y :=
    (((contDiff_wsq wW).differentiable (by simp)) y).hasFDerivAt.const_add 1
  have H := hQ.sqrt (one_add_wsq_pos y).ne'
  change HasFDerivAt exS _ y at H
  rw [H.fderiv]
  simp only [smul_apply, smul_eq_mul]
  unfold exS
  field_simp

theorem fderiv_fderiv_exS (y h k : Fin 5 → ℝ) :
    fderiv ℝ (fderiv ℝ exS) y h k = fderiv ℝ (fderiv ℝ (wsq wW)) y h k / (2 * exS y) -
      fderiv ℝ (wsq wW) y h * fderiv ℝ (wsq wW) y k / (4 * exS y ^ 3) := by
  have hS2 := (contDiff_exS.of_le le_top : ContDiff ℝ 2 exS)
  have hQ2 := ((contDiff_wsq wW).of_le le_top : ContDiff ℝ 2 (wsq wW))
  have hdS : Differentiable ℝ exS := differentiable_of_contDiff_two hS2
  have hdSk : Differentiable ℝ (fun z => fderiv ℝ exS z k) := fun z =>
    (differentiable_fderiv_of_contDiff_two hS2 z).clm_apply (differentiableAt_const k)
  have hdQk : Differentiable ℝ (fun z => fderiv ℝ (wsq wW) z k) := fun z =>
    (differentiable_fderiv_of_contDiff_two hQ2 z).clm_apply (differentiableAt_const k)
  have hprod : (fun z => fderiv ℝ exS z k * (2 * exS z)) = fun z => fderiv ℝ (wsq wW) z k := by
    funext z
    rw [fderiv_exS]
    field_simp [(exS_pos z).ne']
  have hD := congrArg (fun F => fderiv ℝ F y h) hprod
  rw [fderiv_fun_mul (hdSk y) ((hdS y).const_mul 2), fderiv_const_mul (hdS y)] at hD
  simp only [add_apply, smul_apply, smul_eq_mul] at hD
  rw [← fderiv_fderiv_apply (differentiable_fderiv_of_contDiff_two hS2 y),
    ← fderiv_fderiv_apply (differentiable_fderiv_of_contDiff_two hQ2 y), fderiv_exS y k,
    fderiv_exS y h] at hD
  have hs := (exS_pos y).ne'
  generalize fderiv ℝ (fderiv ℝ exS) y h k = A at hD ⊢
  generalize fderiv ℝ (fderiv ℝ (wsq wW)) y h k = B at hD ⊢
  generalize fderiv ℝ (wsq wW) y h = C at hD ⊢
  generalize fderiv ℝ (wsq wW) y k = C' at hD ⊢
  generalize exS y = S at hD hs ⊢
  rw [← hD]
  field_simp
  ring

/-- `X = (s − 1)/2`, the hyperbolic radial coordinate. -/
def exX (y : Fin 5 → ℝ) : ℝ := (exS y - 1) / 2

/-- `Y = (1 − v₂)/2`, the spherical radial coordinate. -/
def exY (y : Fin 5 → ℝ) : ℝ := (1 - y 4) / 2

/-- The map to the strip, `Φ = (X, Y)`. -/
def exPhi (y : Fin 5 → ℝ) : ℝ × ℝ := (exX y, exY y)

theorem contDiff_exX : ContDiff ℝ ⊤ exX := by
  unfold exX
  exact (contDiff_exS.sub contDiff_const).div_const 2

theorem contDiff_exY : ContDiff ℝ ⊤ exY := by
  unfold exY
  fun_prop

theorem contDiff_exPhi : ContDiff ℝ ⊤ exPhi := contDiff_exX.prodMk contDiff_exY

theorem exX_nonneg (y : Fin 5 → ℝ) : 0 ≤ exX y := by
  have := one_le_exS y
  unfold exX
  linarith

theorem fderiv_exX (y h : Fin 5 → ℝ) : fderiv ℝ exX y h = fderiv ℝ exS y h / 2 := by
  have H : HasFDerivAt exX ((1 / 2 : ℝ) • fderiv ℝ exS y) y := by
    have h1 := ((((contDiff_exS.differentiable (by simp)) y).hasFDerivAt).sub_const 1).const_mul
      (1 / 2 : ℝ)
    convert h1 using 1
    funext z
    unfold exX
    ring
  rw [H.fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem fderiv_fderiv_exX (y h k : Fin 5 → ℝ) :
    fderiv ℝ (fderiv ℝ exX) y h k = fderiv ℝ (fderiv ℝ exS) y h k / 2 := by
  have e : fderiv ℝ exX = (1 / 2 : ℝ) • fderiv ℝ exS := by
    funext z
    ext v
    simp only [fderiv_exX, Pi.smul_apply, smul_apply, smul_eq_mul]
    ring
  rw [e, (((differentiable_fderiv_of_contDiff_two
    (contDiff_exS.of_le le_top)) y).hasFDerivAt.const_smul (1 / 2 : ℝ)).fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem fderiv_exY (y h : Fin 5 → ℝ) : fderiv ℝ exY y h = -(h 4 / 2) := by
  have H : HasFDerivAt exY
      ((-(1 / 2 : ℝ)) • (ContinuousLinearMap.proj (4 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ)) y := by
    have h0 : HasFDerivAt (fun f : Fin 5 → ℝ => f 4) (ContinuousLinearMap.proj (4 : Fin 5)) y :=
      hasFDerivAt_apply (𝕜 := ℝ) 4 y
    have h1 := (h0.const_sub 1).const_mul (1 / 2 : ℝ)
    convert h1 using 1
    · funext z
      unfold exY
      ring
    · ext v
      simp
  rw [H.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem fderiv_fderiv_exY (y h k : Fin 5 → ℝ) : fderiv ℝ (fderiv ℝ exY) y h k = 0 := by
  have e : fderiv ℝ exY = fun _ =>
      (-(1 / 2 : ℝ)) • (ContinuousLinearMap.proj (4 : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ) := by
    funext z
    ext v
    simp only [fderiv_exY, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  rw [e, (hasFDerivAt_const _ _).fderiv]
  rfl

/-!
### The generator of `Φ` and its carré du champ
-/

theorem sqrt_mul_self' {D0 : ℝ} (hD0 : 0 ≤ D0) : √D0 * √D0 = D0 := Real.mul_self_sqrt hD0

/-- `𝓛X = (D₀/2)(1 + 2X)`. -/
theorem sdeVecGenerator_exX {D0 : ℝ} (hD0 : 0 ≤ D0) (y : Fin 5 → ℝ) :
    sdeVecGenerator (exDrift D0) (exDiff D0) exX y = D0 / 2 * (1 + 2 * exX y) := by
  unfold sdeVecGenerator
  simp only [fderiv_exX, fderiv_fderiv_exX, fderiv_exS, fderiv_fderiv_exS, fderiv_wsq,
    fderiv_fderiv_wsq, Fin.sum_univ_five, Fin.sum_univ_six, wW, exDrift, exDiff, exX,
    smul_eq_mul]
  simp
  have hs := (exS_pos y).ne'
  have hsq := exS_sq y
  have hD := sqrt_mul_self' hD0
  simp only [wsq, Fin.sum_univ_five, wW] at hsq
  simp at hsq
  field_simp
  rw [Real.sq_sqrt hD0]
  linear_combination (4 * D0 * (y 0 ^ 2 + y 1 ^ 2) - 8 * D0 * exS y ^ 2) * hsq

/-- `𝓛Y = (D₀/2)(1 − 2Y)`. -/
theorem sdeVecGenerator_exY (D0 : ℝ) (y : Fin 5 → ℝ) :
    sdeVecGenerator (exDrift D0) (exDiff D0) exY y = D0 / 2 * (1 - 2 * exY y) := by
  unfold sdeVecGenerator
  simp only [fderiv_exY, fderiv_fderiv_exY, exDrift, exY]
  simp
  ring

theorem exX_mul_one_add (y : Fin 5 → ℝ) : exX y * (1 + exX y) = wsq wW y / 4 := by
  unfold exX
  linear_combination (1 / 4 : ℝ) * exS_sq y

theorem sum_sq_fderiv_exX {D0 : ℝ} (hD0 : 0 ≤ D0) (y : Fin 5 → ℝ) :
    ∑ c, fderiv ℝ exX y (exDiff D0 c y) * fderiv ℝ exX y (exDiff D0 c y) =
      D0 * (exX y * (1 + exX y)) := by
  rw [exX_mul_one_add]
  simp only [fderiv_exX, fderiv_exS, fderiv_wsq, Fin.sum_univ_five, Fin.sum_univ_six, wW,
    exDiff, wsq]
  simp
  have hs := (exS_pos y).ne'
  have hsq := exS_sq y
  simp only [wsq, Fin.sum_univ_five, wW] at hsq
  simp at hsq
  field_simp
  rw [Real.sq_sqrt hD0]
  linear_combination (-4 * D0 * (y 0 ^ 2 + y 1 ^ 2)) * hsq

theorem sum_sq_fderiv_exY (D0 : ℝ) (y : Fin 5 → ℝ) :
    ∑ c, fderiv ℝ exY y (exDiff D0 c y) * fderiv ℝ exY y (exDiff D0 c y) =
      √D0 * √D0 * (y 2 ^ 2 + y 3 ^ 2) / 4 := by
  simp only [fderiv_exY, Fin.sum_univ_six, exDiff]
  simp
  ring

theorem sum_cross_fderiv (D0 : ℝ) (y : Fin 5 → ℝ) :
    ∑ c, fderiv ℝ exX y (exDiff D0 c y) * fderiv ℝ exY y (exDiff D0 c y) = 0 := by
  simp only [fderiv_exX, fderiv_exS, fderiv_wsq, fderiv_exY, Fin.sum_univ_five,
    Fin.sum_univ_six, wW, exDiff]
  simp

theorem sum_cross_fderiv' (D0 : ℝ) (y : Fin 5 → ℝ) :
    ∑ c, fderiv ℝ exY y (exDiff D0 c y) * fderiv ℝ exX y (exDiff D0 c y) = 0 := by
  simp only [mul_comm (fderiv ℝ exY y _)]
  exact sum_cross_fderiv D0 y

theorem exCov_eq (D0 : ℝ) :
    exCov D0 = fun y => Matrix.of fun i j => ∑ c, exDiff D0 c y i * exDiff D0 c y j := rfl

/-- **The generator identity**: on `|v| = 1`, the coordinate generator of the five-dimensional
equation applied to `f ∘ Φ` is the base generator `𝒟₀ f` at `Φ(y)`. -/
theorem exGen_comp_exPhi {D0 : ℝ} (hD0 : 0 ≤ D0) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {y : Fin 5 → ℝ} (hy : wsq wV y = 1) :
    mpGenerator (exDrift D0) (exCov D0) (f ∘ exPhi) y = exBaseGenerator D0 f (exPhi y) := by
  have hX : ContDiff ℝ 2 exX := contDiff_exX.of_le le_top
  have hY : ContDiff ℝ 2 exY := contDiff_exY.of_le le_top
  rw [exCov_eq, mpGenerator_covOf, sdeGenerator_comp hf (contDiff_exPhi.of_le le_top)]
  rw [show exPhi = fun z => (exX z, exY z) from rfl, sdeVecGenerator_prod hX hY,
    sdeVecGenerator_exX hD0, sdeVecGenerator_exY]
  simp only [fderiv_prod_apply hX hY]
  rw [lin_prod (fderiv ℝ f (exX y, exY y))]
  rw [Finset.sum_congr rfl fun c _ => bilin_prod (fderiv ℝ (fderiv ℝ f) (exX y, exY y)) _ _]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [sum_sq_fderiv_exX hD0, sum_sq_fderiv_exY, sum_cross_fderiv, sum_cross_fderiv']
  unfold exBaseGenerator
  have hd := differentiable_fderiv_of_contDiff_two hf (exX y, exY y)
  rw [← fderiv_fderiv_apply hd, ← fderiv_fderiv_apply hd, sqrt_mul_self' hD0]
  simp only [wsq, Fin.sum_univ_five, wV] at hy
  simp at hy
  simp only [exY]
  linear_combination (D0 / 8 * fderiv ℝ (fderiv ℝ f) (exX y, (1 - y 4) / 2) (0, 1) (0, 1)) * hy

/-!
### Conservation of the sphere and nonexplosion
-/

/-- The sphere defect `(|v|² − 1)²`. -/
def sphereDefect (y : Fin 5 → ℝ) : ℝ := (wsq wV y - 1) ^ 2

theorem contDiff_sphereDefect : ContDiff ℝ ⊤ sphereDefect := by
  unfold sphereDefect wsq
  fun_prop

theorem sdeVecGenerator_wsq_wV {D0 : ℝ} (hD0 : 0 ≤ D0) (y : Fin 5 → ℝ) :
    sdeVecGenerator (exDrift D0) (exDiff D0) (wsq wV) y = 0 := by
  unfold sdeVecGenerator
  simp only [fderiv_wsq, fderiv_fderiv_wsq, Fin.sum_univ_five, Fin.sum_univ_six, wV, exDrift,
    exDiff]
  simp
  linear_combination (2 * (y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2)) * Real.sq_sqrt hD0

theorem fderiv_wsq_wV_exDiff (D0 : ℝ) (y : Fin 5 → ℝ) (c : Fin 6) :
    fderiv ℝ (wsq wV) y (exDiff D0 c y) = 0 := by
  simp only [fderiv_wsq, Fin.sum_univ_five, wV, exDiff]
  fin_cases c <;> simp <;> ring

/-- `𝓛((|v|² − 1)²) = 0` everywhere: the sphere `|v| = 1` is conserved. -/
theorem exGen_sphereDefect {D0 : ℝ} (hD0 : 0 ≤ D0) (y : Fin 5 → ℝ) :
    mpGenerator (exDrift D0) (exCov D0) sphereDefect y = 0 := by
  have hg : ContDiff ℝ 2 (fun u : ℝ => (u - 1) ^ 2) := by fun_prop
  have e : sphereDefect = (fun u : ℝ => (u - 1) ^ 2) ∘ wsq wV := rfl
  rw [exCov_eq, mpGenerator_covOf, e,
    sdeGenerator_comp hg ((contDiff_wsq wV).of_le le_top), sdeVecGenerator_wsq_wV hD0]
  simp [fderiv_wsq_wV_exDiff]

/-- All-one weights: `wsq wOne y = |y|²`. -/
def wOne : Fin 5 → ℝ := fun _ => 1

/-- **Lyapunov bound** `𝓛|y|² = D₀(2 + 3|w|²) ≤ 3D₀(1 + |y|²)`. -/
theorem exGen_lyap_le {D0 : ℝ} (hD0 : 0 ≤ D0) (y : Fin 5 → ℝ) :
    sdeGenerator (exDrift D0) (exDiff D0) (wsq wOne) y ≤ 3 * D0 * (1 + wsq wOne y) := by
  unfold sdeGenerator
  simp only [fderiv_wsq, fderiv_fderiv_wsq, Fin.sum_univ_five, Fin.sum_univ_six, wOne, exDrift,
    exDiff, wsq]
  simp
  have hD := sqrt_mul_self' hD0
  nlinarith [mul_nonneg hD0 (mul_self_nonneg (y 0)), mul_nonneg hD0 (mul_self_nonneg (y 1)),
    mul_nonneg hD0 (mul_self_nonneg (y 2)), mul_nonneg hD0 (mul_self_nonneg (y 3)),
    mul_nonneg hD0 (mul_self_nonneg (y 4))]

/-!
### The starting point
-/

/-- A preimage of `z = (x, y)` under `Φ` on the sphere:
`(√((1+2x)² − 1), 0, √(1 − (1−2y)²), 0, 1 − 2y)`. -/
def exStart (z : ℝ × ℝ) : Fin 5 → ℝ :=
  ![√((1 + 2 * z.1) ^ 2 - 1), 0, √(1 - (1 - 2 * z.2) ^ 2), 0, 1 - 2 * z.2]

theorem exPhi_exStart {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) : exPhi (exStart z) = z := by
  obtain ⟨hx, hy0, hy1⟩ := hz
  simp only [Set.mem_Ici] at hx
  have h1 : 0 ≤ (1 + 2 * z.1) ^ 2 - 1 := by nlinarith
  refine Prod.ext ?_ ?_
  · simp only [exPhi, exX, exS, wsq, Fin.sum_univ_five, wW, exStart]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_mul, zero_mul,
      add_zero, Real.mul_self_sqrt h1]
    rw [show 1 + ((1 + 2 * z.1) ^ 2 - 1) = (1 + 2 * z.1) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
    ring
  · simp [exPhi, exY, exStart]

theorem wsq_wV_exStart {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) : wsq wV (exStart z) = 1 := by
  obtain ⟨-, hy0, hy1⟩ := hz
  have h1 : 0 ≤ 1 - (1 - 2 * z.2) ^ 2 := by nlinarith
  simp only [wsq, Fin.sum_univ_five, wV, exStart]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_mul, zero_mul,
    zero_add, add_zero, Real.mul_self_sqrt h1]
  ring

end BlockBand.Diffusion
