module

public import BlockBand.Transmission.DualLift.Gen
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The smooth lift of the `p = 1` dual: state, coefficients, projection, section

**State** `ξ ∈ ℝ⁶` (`Fin 6 → ℝ`): `w = (ξ₀, ξ₁) ∈ ℝ²`, `v = (ξ₂, ξ₃, ξ₄) ∈ ℝ³` and an auxiliary
coordinate `s = ξ₅`, which carries `1/S̃` with `S̃ = |w|² + (1 − v₃)/2`. **Drivers** `Fin 5`
(two for `w`, three for `v`). With `x = |w|²`, `y = (1 − v₃)/2`, `ρ = √(D₀(1+x))`:
* `dw = (D₀/4) w dt + ½ ρ dB_w − (D₀/2)(1+x) s w dt` (that is, `−D₀(1+|w|²)w/(2S̃)` on the
  manifold);
* `dv = √D₀ (I − vvᵀ) dB_v − D₀ v dt + (D₀/2) s (I − vvᵀ) e₃ dt` (spherical Brownian motion plus
  the `H`-drift; `σ_v` and `−D₀v` are not cut off);
* `ds = D₀ s³ Q dt − s² dM`, `Q = x(1+x) + y(1−y)`, `dM = 2w·(½ρ dB_w) − ½ (√D₀(I−vvᵀ)dB_v)₃`
  (Itô for `1/S̃` along the target dynamics, written polynomially in `s`).

All coefficients are polynomials in `(ξ, ρ)`, hence `C^∞` on `ℝ⁶` and locally Lipschitz
(`contDiff_liftDrift`, `contDiff_liftSigma`): no cutoff is needed, and the exit time from the
sup-norm ball of radius `n ≥ 2` is, on the invariant manifold, the exit from
`{S̃ > 1/n, |w|_∞ < n}`. The **invariant manifold** is `liftM = {|v|² = 1, s S̃ = 1}`; its
defect is `liftDefect = (|v|² − 1)² + (s S̃ − 1)²`.

**Projection** `liftProj ξ = (x, y)` and **section** `liftSection x y = (√x, 0, 2√(y(1−y)), 0,
1 − 2y, 1/(x+y))`: on the closed strip minus the corner, the section lies in `liftM` and
`liftProj ∘ liftSection = id`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open Real

/-!
## Scalar functions of the state
-/

/-- `x = |w|²`. -/
def lx (ξ : Fin 6 → ℝ) : ℝ := ξ 0 * ξ 0 + ξ 1 * ξ 1

/-- `y = (1 − v₃)/2`. -/
def ly (ξ : Fin 6 → ℝ) : ℝ := (1 - ξ 4) / 2

/-- `S̃ = x + y`. -/
def lS (ξ : Fin 6 → ℝ) : ℝ := lx ξ + ly ξ

/-- `Q = x(1+x) + y(1−y)` (the bracket density of `S` over `D₀`). -/
def lQ (ξ : Fin 6 → ℝ) : ℝ := lx ξ * (1 + lx ξ) + ly ξ * (1 - ly ξ)

/-- `|v|²`. -/
def vSq (ξ : Fin 6 → ℝ) : ℝ := ξ 2 * ξ 2 + ξ 3 * ξ 3 + ξ 4 * ξ 4

/-- `ρ = √(D₀(1+x))`. -/
def rho (D0 : ℝ) (ξ : Fin 6 → ℝ) : ℝ := √(D0 * (1 + lx ξ))

theorem lx_nonneg (ξ : Fin 6 → ℝ) : 0 ≤ lx ξ := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem rho_sq {D0 : ℝ} (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    rho D0 ξ * rho D0 ξ = D0 * (1 + lx ξ) :=
  Real.mul_self_sqrt (mul_nonneg hD0 (by linarith [lx_nonneg ξ]))

/-!
## Coefficients
-/

/-- The drift of the lifted SDE. -/
def liftDrift (D0 : ℝ) (ξ : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![D0 / 4 * ξ 0 - D0 / 2 * (1 + lx ξ) * ξ 5 * ξ 0,
    D0 / 4 * ξ 1 - D0 / 2 * (1 + lx ξ) * ξ 5 * ξ 1,
    -D0 * ξ 2 - D0 / 2 * ξ 5 * (ξ 2 * ξ 4),
    -D0 * ξ 3 - D0 / 2 * ξ 5 * (ξ 3 * ξ 4),
    -D0 * ξ 4 + D0 / 2 * ξ 5 * (1 - ξ 4 * ξ 4),
    D0 * (ξ 5 * ξ 5 * ξ 5) * lQ ξ]

/-- The noise columns of the lifted SDE (drivers `0, 1` for `w`, `2, 3, 4` for `v`). -/
def liftSigma (D0 : ℝ) (a : Fin 5) (ξ : Fin 6 → ℝ) : Fin 6 → ℝ :=
  (![![rho D0 ξ / 2, 0, 0, 0, 0, -(ξ 5 * ξ 5) * (ξ 0 * rho D0 ξ)],
      ![0, rho D0 ξ / 2, 0, 0, 0, -(ξ 5 * ξ 5) * (ξ 1 * rho D0 ξ)],
      ![0, 0, √D0 * (1 - ξ 2 * ξ 2), -(√D0 * (ξ 3 * ξ 2)), -(√D0 * (ξ 4 * ξ 2)),
        -(ξ 5 * ξ 5) * (√D0 * (ξ 4 * ξ 2)) / 2],
      ![0, 0, -(√D0 * (ξ 2 * ξ 3)), √D0 * (1 - ξ 3 * ξ 3), -(√D0 * (ξ 4 * ξ 3)),
        -(ξ 5 * ξ 5) * (√D0 * (ξ 4 * ξ 3)) / 2],
      ![0, 0, -(√D0 * (ξ 2 * ξ 4)), -(√D0 * (ξ 3 * ξ 4)), √D0 * (1 - ξ 4 * ξ 4),
        ξ 5 * ξ 5 * (√D0 * (1 - ξ 4 * ξ 4)) / 2]] : Fin 5 → Fin 6 → ℝ) a

/-!
## Projection, section, invariant manifold
-/

/-- The projection `π(ξ) = (x, y)` to flat dual coordinates. -/
def liftProj (ξ : Fin 6 → ℝ) : Fin 2 → ℝ := ![lx ξ, ly ξ]

/-- The section `σ(x, y)`. -/
def liftSection (x y : ℝ) : Fin 6 → ℝ :=
  ![√x, 0, 2 * √(y * (1 - y)), 0, 1 - 2 * y, 1 / (x + y)]

/-- The invariant manifold `{|v|² = 1, s S̃ = 1}`. -/
def liftM : Set (Fin 6 → ℝ) := {ξ | vSq ξ = 1 ∧ ξ 5 * lS ξ = 1}

/-- The defect `(|v|² − 1)² + (s S̃ − 1)²`, which vanishes exactly on `liftM`. -/
def liftDefect (ξ : Fin 6 → ℝ) : ℝ :=
  (vSq ξ - 1) * (vSq ξ - 1) + (ξ 5 * lS ξ - 1) * (ξ 5 * lS ξ - 1)

theorem liftDefect_nonneg (ξ : Fin 6 → ℝ) : 0 ≤ liftDefect ξ :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem liftDefect_eq_zero_iff (ξ : Fin 6 → ℝ) : liftDefect ξ = 0 ↔ ξ ∈ liftM := by
  unfold liftDefect liftM
  constructor
  · intro h
    have h1 := mul_self_nonneg (vSq ξ - 1)
    have h2 := mul_self_nonneg (ξ 5 * lS ξ - 1)
    have e1 : (vSq ξ - 1) * (vSq ξ - 1) = 0 := by linarith
    have e2 : (ξ 5 * lS ξ - 1) * (ξ 5 * lS ξ - 1) = 0 := by linarith
    exact ⟨by linarith [mul_self_eq_zero.1 e1], by linarith [mul_self_eq_zero.1 e2]⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

@[simp] theorem liftProj_zero (ξ : Fin 6 → ℝ) : liftProj ξ 0 = lx ξ := rfl
@[simp] theorem liftProj_one (ξ : Fin 6 → ℝ) : liftProj ξ 1 = ly ξ := rfl

theorem lS_pos_of_mem {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) : 0 < lS ξ ∨ lS ξ < 0 := by
  rcases lt_trichotomy (lS ξ) 0 with h0 | h0 | h0
  · exact Or.inr h0
  · have := h.2; rw [h0, mul_zero] at this; exact absurd this zero_ne_one
  · exact Or.inl h0

/-- On the manifold, `|v₃| ≤ 1`, so `0 ≤ y ≤ 1`. -/
theorem ly_mem_of_mem {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) : 0 ≤ ly ξ ∧ ly ξ ≤ 1 := by
  have h1 := h.1
  unfold vSq at h1
  have h4 : ξ 4 * ξ 4 ≤ 1 := by nlinarith [mul_self_nonneg (ξ 2), mul_self_nonneg (ξ 3)]
  have : -1 ≤ ξ 4 ∧ ξ 4 ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  unfold ly; constructor <;> linarith [this.1, this.2]

/-- On the manifold, `S̃ > 0` and `s = 1/S̃ > 0`. -/
theorem lS_pos {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) : 0 < lS ξ := by
  rcases lS_pos_of_mem h with h0 | h0
  · exact h0
  · have := (ly_mem_of_mem h).1
    have := lx_nonneg ξ
    unfold lS at h0; linarith

theorem s_eq_inv {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) : ξ 5 = 1 / lS ξ := by
  have := lS_pos h
  field_simp
  exact h.2

theorem liftSection_mem {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hxy : 0 < x + y) :
    liftSection x y ∈ liftM := by
  have hyy : 0 ≤ y * (1 - y) := mul_nonneg hy0 (by linarith)
  have hs := Real.mul_self_sqrt hyy
  have hsx := Real.mul_self_sqrt hx
  refine ⟨?_, ?_⟩
  · simp only [vSq, liftSection, Matrix.cons_val]
    nlinarith
  · simp only [lS, lx, ly, liftSection, Matrix.cons_val]
    rw [hsx]
    field_simp
    ring

theorem liftProj_liftSection {x y : ℝ} (hx : 0 ≤ x) : liftProj (liftSection x y) = ![x, y] := by
  funext i
  fin_cases i
  · simp [liftProj, lx, liftSection, Real.mul_self_sqrt hx]
  · simp only [liftProj, ly, liftSection, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.cons_val]
    ring

/-!
## Smoothness
-/

theorem contDiff_lx : ContDiff ℝ ⊤ lx := by unfold lx; fun_prop

theorem contDiff_ly : ContDiff ℝ ⊤ ly := by unfold ly; fun_prop

theorem contDiff_lQ : ContDiff ℝ ⊤ lQ := by
  unfold lQ lx ly; fun_prop

theorem contDiff_rho {D0 : ℝ} (hD0 : 0 < D0) : ContDiff ℝ ⊤ (rho D0) := by
  refine ContDiff.sqrt (contDiff_const.mul (contDiff_const.add contDiff_lx)) fun ξ => ?_
  have := lx_nonneg ξ
  exact (mul_pos hD0 (by linarith)).ne'

theorem contDiff_liftDrift (D0 : ℝ) : ContDiff ℝ ⊤ (liftDrift D0) := by
  have hx := contDiff_lx
  have hQ := contDiff_lQ
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [liftDrift, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, Fin.isValue] <;> fun_prop

theorem contDiff_liftSigma {D0 : ℝ} (hD0 : 0 < D0) (a : Fin 5) :
    ContDiff ℝ ⊤ (liftSigma D0 a) := by
  have hr := contDiff_rho hD0
  refine contDiff_pi.2 fun i => ?_
  fin_cases a <;> fin_cases i <;> simp only [liftSigma, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] <;> fun_prop

theorem locallyLipschitz_liftDrift (D0 : ℝ) : LocallyLipschitz (liftDrift D0) :=
  ((contDiff_liftDrift D0).of_le (by norm_num)).locallyLipschitz

theorem locallyLipschitz_liftSigma {D0 : ℝ} (hD0 : 0 < D0) (a : Fin 5) :
    LocallyLipschitz (liftSigma D0 a) :=
  ((contDiff_liftSigma hD0 a).of_le (by norm_num)).locallyLipschitz

theorem contDiff_liftProj : ContDiff ℝ ⊤ liftProj := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_lx
  · exact contDiff_ly

theorem contDiff_liftDefect : ContDiff ℝ ⊤ liftDefect := by
  unfold liftDefect vSq lS lx ly; fun_prop

end BlockBand.Transmission.DualLift
