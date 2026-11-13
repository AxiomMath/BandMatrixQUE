module

public import BlockBand.External.ErdosRiabov.NativeModel
public import BlockBand.External.ErdosRiabov.Semicircle

/-!
# Admissible control families and admissible variance profiles

This file states Definitions 2.4 and 2.5 of Erdős–Riabov (ER): the spectral domain, the
two-resolvent kernels `Θ` and `Ξ` of a variance profile `S`, the seven conditions on a control
family `Υ_η` (`AdmissibleControl`), and admissibility of a variance profile.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.External.ErdosRiabov

open scoped BigOperators

/-- The spectral domain of ER (2.9): `N^{-1+δ₀} ≤ |Im z|`, `|z| ≤ C₀` and
`κ ≤ |(m/|m|)² - 1|`, with `m = semicircleM z`. -/
def SpectralDomain (p : ModelParameters) (N : ℕ) (z : ℂ) : Prop :=
  (N : ℝ) ^ (-1 + p.delta0) ≤ |z.im| ∧ ‖z‖ ≤ p.C0 ∧
    p.kappa ≤ ‖(semicircleM z / ‖semicircleM z‖) ^ 2 - 1‖

/-- The heights `N^{-1+δ₀} ≤ η ≤ C₀` on which the control family is defined. -/
def ControlHeight (p : ModelParameters) (N : ℕ) (η : ℝ) : Prop :=
  (N : ℝ) ^ (-1 + p.delta0) ≤ η ∧ η ≤ p.C0

/-- `z₁` and `z₂` lie in the same open half-plane. -/
def SameHalfPlane (z₁ z₂ : ℂ) : Prop := 0 < z₁.im * z₂.im

/-- The localization length `ℓ(η) = min(W/√η, N)` of ER (2.15). -/
def localizationLength (N W : ℕ) (η : ℝ) : ℝ :=
  min ((W : ℝ) / Real.sqrt η) (N : ℝ)

/-- The distance on the cycle `ℤ/Nℤ`. -/
def cyclicDistance (N : ℕ) (x y : Fin N) : ℕ :=
  let d := max x.val y.val - min x.val y.val
  min d (N - d)

/-- The kernel `Θ = A(1 - A)⁻¹`, `A = m(z₁) conj(m(z₂)) S`, of ER (2.10). -/
def theta {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z₁ z₂ : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let A := (semicircleM z₁ * starRingEnd ℂ (semicircleM z₂)) •
    (S.map (algebraMap ℝ ℂ))
  A * (1 - A)⁻¹

/-- The kernel `Ξ = A(1 - A)⁻¹`, `A = m(z₁) m(z₂) S`, of ER (2.10). -/
def xi {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z₁ z₂ : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let A := (semicircleM z₁ * semicircleM z₂) • (S.map (algebraMap ℝ ℂ))
  A * (1 - A)⁻¹

/-- An admissible control family (ER Definition 2.4): a positive symmetric family `Υ_η`
satisfying conditions (i)–(vii), with the constants taken from the model parameters. The inverse
in `Θ` and `Ξ` is Mathlib's matrix inverse; on the spectral domain `1 - A` is invertible since
`S` is stochastic and symmetric and `|m| < 1`. -/
structure AdmissibleControl (p : ModelParameters) (N W : ℕ)
    (S : Matrix (Fin N) (Fin N) ℝ)
    (Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ) : Prop where
  entrywisePositive : ∀ η, ControlHeight p N η →
    ∀ x y, 0 < Upsilon η x y
  symmetric : ∀ η, ControlHeight p N η →
    ∀ x y, Upsilon η x y = Upsilon η y x
  /-- Condition (i), ER (2.18): `Θ` is bounded by `Υ` at the smaller height and `Ξ` by `Υ` at
  height one. -/
  clause1 : ∀ z₁ z₂, SpectralDomain p N z₁ →
    SpectralDomain p N z₂ → SameHalfPlane z₁ z₂ →
    ∀ x y,
      ‖theta S z₁ z₂ x y‖ ≤ p.C1 * Upsilon (min |z₁.im| |z₂.im|) x y ∧
      ‖xi S z₁ z₂ x y‖ ≤ p.C1 * Upsilon 1 x y
  /-- Condition (ii), ER (2.19)–(2.21): pointwise and row-sum upper bounds, the polynomial lower
  bound, and the two-sided comparison with `1/(Nη)` for `η ≤ (W/N)²`. -/
  clause2 : ∀ η, ControlHeight p N η →
    (∀ x y, Upsilon η x y ≤ p.C1 / (localizationLength N W η * η)) ∧
    (∀ x, ∑ a, Upsilon η x a ≤ p.C1 / η) ∧
    (∀ x y, Real.rpow (N : ℝ) (-2 * p.DPrime) ≤ Upsilon η x y) ∧
    (η ≤ ((W : ℝ) / (N : ℝ)) ^ 2 →
      ∀ x y,
        (1 / p.C1) * (1 / ((N : ℝ) * η)) ≤ Upsilon η x y ∧
        Upsilon η x y ≤ p.C1 * (1 / ((N : ℝ) * η)))
  /-- Condition (iii), ER (2.22): monotonicity in `η` up to the constant `p.C1`. -/
  clause3 : ∀ η₁ η₂, ControlHeight p N η₁ →
    ControlHeight p N η₂ → η₁ ≤ η₂ →
    ∀ x y, Upsilon η₂ x y ≤ p.C1 * Upsilon η₁ x y
  /-- Condition (iv), ER (2.23)–(2.24): the pointwise product estimate and the square-root
  convolution estimate. -/
  clause4 : ∀ η₁ η₂, ControlHeight p N η₁ →
    ControlHeight p N η₂ → η₁ ≤ η₂ →
    ∀ x y,
      (∀ a, Upsilon η₂ x a * Upsilon η₁ a y ≤
        p.C1 / (localizationLength N W η₂ * η₂) * Upsilon η₁ x y) ∧
      (∑ a, Real.sqrt (Upsilon η₂ x a * Upsilon η₁ a y)) ≤
        p.C1 / η₂ *
          Real.sqrt (localizationLength N W η₂ * η₂ * Upsilon η₁ x y)
  /-- Condition (v), ER (2.25): the weighted convolution estimate for each choice
  `ηᵢ ∈ {η₁,η₂}`. -/
  clause5 : ∀ η₁ η₂, ControlHeight p N η₁ →
    ControlHeight p N η₂ → η₁ ≤ η₂ →
    ∀ ηi, (ηi = η₁ ∨ ηi = η₂) → ∀ x y,
      (∑ a,
        (min ((cyclicDistance N a x : ℝ) + W)
            (localizationLength N W η₁) / localizationLength N W η₁) *
          Real.sqrt (Upsilon η₂ x a * Upsilon ηi a y)) ≤
        p.C1 / η₂ *
          (localizationLength N W η₂ / localizationLength N W η₁) *
          Real.sqrt
            ((localizationLength N W η₂ * η₂) /
              (localizationLength N W ηi * ηi)) *
          Real.sqrt
            (localizationLength N W η₁ * η₁ * Upsilon η₁ x y)
  /-- Condition (vi), ER (2.26): regularity of `Θ` at distance `min(d(b, c) + W, ℓ(η))`, for
  `η ≥ p.c2(W/N)²`. -/
  clause6 : ∀ z₁ z₂, SpectralDomain p N z₁ →
    SpectralDomain p N z₂ → SameHalfPlane z₁ z₂ →
    let η := min |z₁.im| |z₂.im|
    p.c2 * ((W : ℝ) / (N : ℝ)) ^ 2 ≤ η →
      ∀ a b c,
        ‖theta S z₁ z₂ a b - theta S z₁ z₂ a c‖ ≤
          p.C1 *
            (min ((cyclicDistance N b c : ℝ) + W)
                (localizationLength N W η) / localizationLength N W η) *
            (Upsilon η a b + Upsilon η a c)
  /-- Condition (vii), ER (2.27): after subtracting its row average, `Θ` is `O(N/W²)`, on the
  whole spectral domain. -/
  clause7 : ∀ z₁ z₂, SpectralDomain p N z₁ →
    SpectralDomain p N z₂ → SameHalfPlane z₁ z₂ →
    ∀ a b,
      ‖theta S z₁ z₂ a b -
          (1 / (N : ℂ)) * ∑ c, theta S z₁ z₂ a c‖ ≤
        p.C1 * (N : ℝ) / (W : ℝ) ^ 2

/-- An admissible variance profile (ER Definition 2.5): a symmetric nonnegative `S` with an
admissible control family. The model assumptions (2.1)–(2.4) are in `NativeProfile`. -/
def AdmissibleVarianceProfile (p : ModelParameters) (N W : ℕ)
    (S : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ x y, S x y = S y x) ∧ (∀ x y, 0 ≤ S x y) ∧
    ∃ Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ,
      AdmissibleControl p N W S Upsilon

/-- A profile satisfying `NativeProfile` with an admissible control family is admissible. -/
theorem admissibleVarianceProfile_of_control {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ} (hS : NativeProfile p N W S)
    {Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ}
    (hU : AdmissibleControl p N W S Upsilon) :
    AdmissibleVarianceProfile p N W S :=
  ⟨hS.symmetric, hS.nonnegative, Upsilon, hU⟩

/-- Points of the spectral domain are nonreal. -/
theorem SpectralDomain.im_ne_zero {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ} (hS : NativeProfile p N W S)
    {z : ℂ} (hz : SpectralDomain p N z) : z.im ≠ 0 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast hS.N_pos
  exact abs_pos.mp (lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) hz.1)

/-- The cyclic distance is symmetric. -/
theorem cyclicDistance_comm (N : ℕ) (x y : Fin N) :
    cyclicDistance N x y = cyclicDistance N y x := by
  simp only [cyclicDistance]
  omega

end BlockBand.External.ErdosRiabov
