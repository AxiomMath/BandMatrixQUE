module

public import BlockBand.Endpoints.Response.NearSchattenScalar

/-!
# The spectral trace generator of `Tr f_ε(A)`: sign and dissipation bound

For `f_ε(x) = (x+ε)^p - ε^p` (`0 ≤ p ≤ 1`, `ε > 0`) write `f_ε' = nsgDeriv`,
`f_ε'' = nsgDeriv2` and `nsgDivDiff x y` for the divided difference of `f_ε'`
(`= f_ε''(x)` on the diagonal). In an eigenbasis of the clock `A` (eigenvalues `λ_i ≥ 0`), with
`S_ii` the diagonal of the projected `P'`-block and `g` the conductance, the right side of the
Schatten trace generator is

`nsgSpecGen D p ε g λ S = -(D/2) g Σ_i λ_i f'(λ_i) + (D/2) Σ_{i,j} λ_i λ_j S_jj DD f'(λ_i, λ_j)`

(the double sum is the diagonal `(D/2) Σ_i λ_i² S_ii f''(λ_i)` plus the off-diagonal
`(D/2) Σ_{i<j} λ_iλ_j (S_ii + S_jj) DD f'(λ_i, λ_j)`).

* `nsg_hasDerivAt_regFun`, `nsg_hasDerivAt_deriv`: `nsgDeriv`, `nsgDeriv2` are the first two
  derivatives of `f_ε` on `x > -ε`.
* `nsg_divDiff_nonpos`: the divided-difference sign, `DD f_ε'(x, y) ≤ 0` for `x, y ≥ 0`
  (concavity of `f_ε`).
* `nsg_firstTwo_le`: the first two terms, `-g λ f'(λ) + λ² S f''(λ) ≤ -p(1-p) λ²(λ+ε)^{p-2}`
  for `λ ≥ 0`, `g ≥ 0`, `1 - S ≤ g` (`gu + (1-p)u²S ≥ (1-p)u²`, `u = λ/(λ+ε)`, from
  `T = 1 - S ≤ g`).
* `nsg_specGen_le`: the combined bound
  `nsgSpecGen ≤ -(Dp(1-p)/2) Σ_i λ_i · λ_i(λ_i+ε)^{p-2}` (kernel `nsDissKernel`) for `D ≥ 0`,
  `λ_i ≥ 0`, `S_ii ≥ 0`, `g ≥ 0`, `1 - S_ii ≤ g`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Finset

/-- `f_ε'(x) = p (x+ε)^{p-1}`. -/
def nsgDeriv (p ε x : ℝ) : ℝ := p * (x + ε) ^ (p - 1)

/-- `f_ε''(x) = p (p-1) (x+ε)^{p-2}`. -/
def nsgDeriv2 (p ε x : ℝ) : ℝ := p * (p - 1) * (x + ε) ^ (p - 2)

/-- The divided difference of `f_ε'`: `(f'(x) - f'(y))/(x - y)`, and `f''(x)` on the diagonal. -/
def nsgDivDiff (p ε x y : ℝ) : ℝ :=
  if x = y then nsgDeriv2 p ε x else (nsgDeriv p ε x - nsgDeriv p ε y) / (x - y)

/-- The spectral form of the right side of the Schatten trace generator for `f_ε`: eigenvalues
`lam`, diagonal `s` of the projected block, conductance `g`, diffusion constant `D`. -/
def nsgSpecGen {ι : Type*} [Fintype ι] (D p ε g : ℝ) (lam s : ι → ℝ) : ℝ :=
  -(D / 2) * g * ∑ i, lam i * nsgDeriv p ε (lam i) +
    D / 2 * ∑ i, ∑ j, lam i * lam j * s j * nsgDivDiff p ε (lam i) (lam j)

/-!
## Derivatives
-/

/-- `f_ε' = nsgDeriv` on `x > -ε` (`f_ε(x) = (x+ε)^p - ε^p`). -/
theorem nsg_hasDerivAt_regFun {p ε x : ℝ} (hx : -ε < x) :
    HasDerivAt (fun y => (y + ε) ^ p - ε ^ p) (nsgDeriv p ε x) x := by
  have h := (ns_hasDerivAt_shiftPow (p := p) hx).sub_const (ε ^ p)
  exact h

/-- `f_ε'' = nsgDeriv2` on `x > -ε`. -/
theorem nsg_hasDerivAt_deriv {p ε x : ℝ} (hx : -ε < x) :
    HasDerivAt (nsgDeriv p ε) (nsgDeriv2 p ε x) x := by
  have hne : x + ε ≠ 0 := ne_of_gt (by linarith)
  have h := (((hasDerivAt_id' x).add_const ε).rpow_const (p := p - 1) (Or.inl hne)).const_mul p
  unfold nsgDeriv nsgDeriv2
  convert h using 1
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

/-!
## The divided-difference sign
-/

/-- `f_ε'` is antitone on `[0, ∞)` (`0 ≤ p ≤ 1`). -/
theorem nsg_deriv_anti {p ε x y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x)
    (hxy : x ≤ y) : nsgDeriv p ε y ≤ nsgDeriv p ε x := by
  unfold nsgDeriv
  have h : (y + ε) ^ (p - 1) ≤ (x + ε) ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left h hp0

theorem nsg_deriv2_nonpos {p ε x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x) :
    nsgDeriv2 p ε x ≤ 0 := by
  unfold nsgDeriv2
  have h : 0 ≤ (x + ε) ^ (p - 2) := Real.rpow_nonneg (by linarith) _
  have h' : p * (p - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 (by linarith)
  exact mul_nonpos_of_nonpos_of_nonneg h' h

/-- The divided-difference sign: `DD f_ε'(x, y) ≤ 0` for `x, y ≥ 0`. -/
theorem nsg_divDiff_nonpos {p ε x y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : nsgDivDiff p ε x y ≤ 0 := by
  unfold nsgDivDiff
  split_ifs with hxy
  · exact nsg_deriv2_nonpos hp0 hp1 hε hx
  · rcases lt_or_gt_of_ne hxy with h | h
    · have h1 := nsg_deriv_anti hp0 hp1 hε hx h.le
      exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    · have h1 := nsg_deriv_anti hp0 hp1 hε hy h.le
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-!
## The first two terms
-/

/-- The first two terms of the Schatten trace generator for `f_ε`:
`-g λ f'(λ) + λ² S f''(λ) ≤ -p(1-p) λ · λ(λ+ε)^{p-2}` for `λ ≥ 0`, `g ≥ 0`, `1 - S ≤ g`. -/
theorem nsg_firstTwo_le {p ε g s x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x)
    (hg : 0 ≤ g) (hgs : 1 - s ≤ g) :
    -g * x * nsgDeriv p ε x + x ^ 2 * s * nsgDeriv2 p ε x ≤
      -(p * (1 - p)) * (x * nsDissKernel p ε x) := by
  have hy : 0 < x + ε := by linarith
  set r := (x + ε) ^ (p - 2) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hy.le _
  have h1 : (x + ε) ^ (p - 1) = r * (x + ε) := by
    rw [hr, ← Real.rpow_add_one hy.ne']
    congr 1; ring
  have hD : nsDissKernel p ε x = x * r := by
    unfold nsDissKernel; rw [max_eq_left hx]
  unfold nsgDeriv nsgDeriv2
  rw [h1, hD, ← hr]
  -- reduce to `p r (g x (x+ε) + (1-p) x² (s - 1)) ≥ 0`
  have hkey : 0 ≤ g * x * (x + ε) + (1 - p) * x ^ 2 * (s - 1) := by
    rcases le_or_gt s 1 with hs | hs
    · have h2 : (1 - s) * x ^ 2 ≤ g * x * (x + ε) := by
        have : (1 - s) * x ^ 2 ≤ g * x ^ 2 := mul_le_mul_of_nonneg_right hgs (sq_nonneg x)
        nlinarith [mul_nonneg hg (mul_nonneg hx hε.le)]
      have h3 : (s - 1) * x ^ 2 ≤ (1 - p) * x ^ 2 * (s - 1) := by
        have : 0 ≤ p * x ^ 2 * (1 - s) := by
          have := sq_nonneg x
          have : 0 ≤ 1 - s := by linarith
          positivity
        nlinarith
      nlinarith
    · have : 0 ≤ (1 - p) * x ^ 2 * (s - 1) := by
        have := sq_nonneg x
        have : 0 ≤ s - 1 := by linarith
        have : 0 ≤ 1 - p := by linarith
        positivity
      have : 0 ≤ g * x * (x + ε) := by positivity
      linarith
  have := mul_nonneg (mul_nonneg hp0 hr0) hkey
  nlinarith

/-!
## The combined spectral bound
-/

/-- The regularized trace generator is dissipative: with `D ≥ 0`, eigenvalues `λ_i ≥ 0`, diagonal
entries `S_ii ≥ 0` and a conductance `g ≥ 0` with `1 - S_ii ≤ g`, the spectral form of the
Schatten trace generator for `f_ε` is at most `-(Dp(1-p)/2) Σ_i λ_i² (λ_i+ε)^{p-2}`. -/
theorem nsg_specGen_le {ι : Type*} [Fintype ι] [DecidableEq ι] {D p ε g : ℝ} {lam s : ι → ℝ}
    (hD : 0 ≤ D) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hlam : ∀ i, 0 ≤ lam i)
    (hs : ∀ i, 0 ≤ s i) (hg : 0 ≤ g) (hgs : ∀ i, 1 - s i ≤ g) :
    nsgSpecGen D p ε g lam s ≤ -(D * p * (1 - p) / 2) * ∑ i, lam i * nsDissKernel p ε (lam i) := by
  -- off-diagonal summands are `≤ 0`
  have hrow : ∀ i, ∑ j, lam i * lam j * s j * nsgDivDiff p ε (lam i) (lam j) ≤
      lam i ^ 2 * s i * nsgDeriv2 p ε (lam i) := by
    intro i
    calc ∑ j, lam i * lam j * s j * nsgDivDiff p ε (lam i) (lam j)
        ≤ ∑ j, if j = i then lam i ^ 2 * s i * nsgDeriv2 p ε (lam i) else 0 := by
          refine sum_le_sum fun j _ => ?_
          split_ifs with hji
          · subst hji
            simp [nsgDivDiff, sq]
          · have h1 : 0 ≤ lam i * lam j * s j :=
              mul_nonneg (mul_nonneg (hlam i) (hlam j)) (hs j)
            exact mul_nonpos_of_nonneg_of_nonpos h1
              (nsg_divDiff_nonpos hp0 hp1 hε (hlam i) (hlam j))
      _ = lam i ^ 2 * s i * nsgDeriv2 p ε (lam i) := by simp
  have hsum : ∑ i, ∑ j, lam i * lam j * s j * nsgDivDiff p ε (lam i) (lam j) ≤
      ∑ i, lam i ^ 2 * s i * nsgDeriv2 p ε (lam i) := sum_le_sum fun i _ => hrow i
  have hD2 : 0 ≤ D / 2 := by positivity
  have hfirst : ∑ i, (-g * lam i * nsgDeriv p ε (lam i) + lam i ^ 2 * s i * nsgDeriv2 p ε (lam i))
      ≤ ∑ i, -(p * (1 - p)) * (lam i * nsDissKernel p ε (lam i)) :=
    sum_le_sum fun i _ => nsg_firstTwo_le hp0 hp1 hε (hlam i) hg (hgs i)
  rw [sum_add_distrib] at hfirst
  have e1 : ∑ i, -g * lam i * nsgDeriv p ε (lam i) = -g * ∑ i, lam i * nsgDeriv p ε (lam i) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, -(p * (1 - p)) * (lam i * nsDissKernel p ε (lam i)) =
      -(p * (1 - p)) * ∑ i, lam i * nsDissKernel p ε (lam i) := by rw [mul_sum]
  rw [e1, e2] at hfirst
  unfold nsgSpecGen
  have h3 := mul_le_mul_of_nonneg_left hsum hD2
  have h4 := mul_le_mul_of_nonneg_left hfirst hD2
  have e3 : -(D * p * (1 - p) / 2) * ∑ i, lam i * nsDissKernel p ε (lam i) =
      D / 2 * (-(p * (1 - p)) * ∑ i, lam i * nsDissKernel p ε (lam i)) := by ring
  rw [e3]
  nlinarith

end BlockBand.Endpoints
