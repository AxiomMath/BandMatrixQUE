module

public import Mathlib

/-!
# The CEH observables

The domain is finite complex matrices on `Fin N`; trace is divided by `N`.
The source coupling `lambda` is real. The source MDE regime later requires
`N > 0`, `lambda > 0`, and upper-half-plane matrices; those hypotheses are
not needed to define these total expressions. Every adjoint constellation
in (2.14) is retained. In particular the cutoff at equality is `1/2`.

These definitions and finite identities contain no probability law,
stochastic domination, asymptotic estimate, regular-window reduction, or
CEH theorem assumption. The statement of Theorem 2.5, the MDE and spacing
realization, the nonnegativity of its control parameter, and the physical
conditional and window adapters are treated elsewhere.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.External.CEH

open Matrix

/-- The CEH normalized trace; its total value at `N = 0` is zero. -/
def normalizedTrace {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  (N : ℂ)⁻¹ * A.trace

/-- Matrix imaginary part in the source Hermitian convention. -/
def imaginaryPart {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (2 * Complex.I)⁻¹ • (A - Aᴴ)

/-- Exact Heaviside convention in CEH (2.13), including the half-weight at zero. -/
def cehTheta (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x = 0 then 1 / 2 else 1

@[simp] theorem cehTheta_of_neg {x : ℝ} (hx : x < 0) : cehTheta x = 0 := by
  simp [cehTheta, hx]

@[simp] theorem cehTheta_zero : cehTheta 0 = 1 / 2 := by
  norm_num [cehTheta]

@[simp] theorem cehTheta_of_pos {x : ℝ} (hx : 0 < x) : cehTheta x = 1 := by
  simp [cehTheta, not_lt_of_ge hx.le, ne_of_gt hx]

/-- The cutoff lies between zero and one for every finite real argument. -/
theorem cehTheta_mem_Icc (x : ℝ) : cehTheta x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold cehTheta
  split_ifs <;> norm_num

/-- Cutoff from the mixed MDE pairing. `M₂minus` is the adjoint of
`M₂plus` in CEH (2.13); no unrelated cutoff may replace this coefficient. -/
def regularizationCoefficient {N : ℕ} (lambda : ℝ)
    (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  cehTheta (lambda ^ 2 * (normalizedTrace (M₁plus * M₂minus)).re - 1 / 2)

/-- Strictly positive mixed-pairing margin gives the active cutoff. This finite
identity is the only bridge to a Boolean theta-one helper supplied here. -/
theorem regularizationCoefficient_eq_one {N : ℕ} (lambda : ℝ)
    (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hmargin : 1 / 2 < lambda ^ 2 * (normalizedTrace (M₁plus * M₂minus)).re) :
    regularizationCoefficient lambda M₁plus M₂minus = 1 := by
  exact cehTheta_of_pos (sub_pos.mpr hmargin)

/-- CEH (2.13): the regularized deterministic observable, with total scalar
inverse. The specialization supplies the displayed coefficient. -/
def regularizedObservable {N : ℕ} (theta : ℝ)
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  A - ((theta : ℂ) * (normalizedTrace (M₁plus * A * M₂minus) /
    normalizedTrace (M₁plus * M₂minus))) • (1 : Matrix (Fin N) (Fin N) ℂ)

@[simp] theorem regularizedObservable_inactive {N : ℕ}
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ) :
    regularizedObservable 0 M₁plus M₂minus A = A := by
  simp [regularizedObservable]

/-- CEH (2.7): the relative matrix Gamma, retaining its matrix structure. -/
def gammaMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (normalizedTrace (imaginaryPart M))⁻¹ • imaginaryPart M

/-- All four choices of adjoints in the maximum of CEH (2.14). -/
def allAdjointObservables {N : ℕ}
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) : Fin 4 → ℂ
  | 0 => normalizedTrace (M₁ * A * M₂)
  | 1 => normalizedTrace (M₁ * A * M₂ᴴ)
  | 2 => normalizedTrace (M₁ᴴ * A * M₂)
  | _ => normalizedTrace (M₁ᴴ * A * M₂ᴴ)

/-- The squared eigenstate thermalization (ETH) control (2.14), with all adjoint choices. Traces real and nonnegative
in the upper-half-plane MDE regime are represented by their real parts;
that regime and those positivity proofs are not assumed by this definition.
The two MDE matrices here are upper-half-plane values, while `Areg` is the
observable regularized using the second matrix's adjoint. -/
def sTwoSq {N : ℕ} (theta lambda : ℝ)
    (M₁plus M₂plus Areg : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  let Γ₁ := gammaMatrix M₁plus
  let Γ₂ := gammaMatrix M₂plus
  let base := (normalizedTrace (Γ₁ * Areg * Γ₂ * Aregᴴ)).re
  let stable := ‖normalizedTrace (M₁plus * Areg * Γ₂) *
    normalizedTrace (Γ₁ * Aregᴴ * M₂plus) /
      (1 - (lambda : ℂ) ^ 2 * normalizedTrace (M₁plus * M₂plus))‖
  let vals := allAdjointObservables M₁plus Areg M₂plus
  let off := (max (max ‖vals 0‖ ‖vals 1‖) (max ‖vals 2‖ ‖vals 3‖)) ^ 2 *
    (normalizedTrace (Γ₁ * Γ₂)).re
  base + theta * lambda ^ 2 * stable + (1 - theta) * lambda ^ 4 * off

/-- The ETH control: the total real square root of `sTwoSq` (the square is not assumed
nonnegative). -/
def sTwo {N : ℕ} (theta lambda : ℝ)
    (M₁plus M₂plus Areg : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (sTwoSq theta lambda M₁plus M₂plus Areg)

end BlockBand.External.CEH
