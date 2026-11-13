module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventDeterministic
public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.ResolventIdentities

/-!
# Concrete CEH two-resolvent observables

This module defines the finite-matrix words occurring in CEH
(5.12)--(5.23): all four adjoint constellations, the cutoff regularization
`A°`, `Gamma`, `s₂`, and the two normalized errors `Psi₁,Psi₂`.  It also proves
the exact algebraic underlined representations from inverse-pencil (resolvent)
data and the fourfold polarization of the positive chain.

There is no probability in this file.  In particular it proves no local law,
Gaussian contraction estimate, beta lower bound, or stochastic domination.
Those analytic/probabilistic obligations are visible at the bottom of the API
as quantities to be bounded, not hypotheses asserting a representation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

abbrev NTrace {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  CEHNative.BlockBand.Conventions.normalizedTrace X

theorem NTrace_add {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (X + Y) = NTrace X + NTrace Y :=
  CEHNative.BlockBand.Conventions.normalizedTrace_add X Y

theorem NTrace_sub {N : ℕ} (X Y : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (X - Y) = NTrace X - NTrace Y := by
  simp [NTrace, CEHNative.BlockBand.Conventions.normalizedTrace,
    Matrix.trace_sub, mul_sub]

theorem NTrace_smul {N : ℕ} (z : ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (z • X) = z * NTrace X :=
  CEHNative.BlockBand.Conventions.normalizedTrace_smul z X

/-- Whether a resolvent in a two-word constellation is replaced by its
conjugate transpose. -/
inductive AdjointChoice
  | plain
  | adjoint
  deriving DecidableEq

/-- Select a matrix or its conjugate transpose. -/
def chooseAdjoint {N : ℕ} (choice : AdjointChoice)
    (G : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  match choice with
  | .plain => G
  | .adjoint => Gᴴ

@[simp] theorem chooseAdjoint_plain {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) :
    chooseAdjoint .plain G = G := rfl

@[simp] theorem chooseAdjoint_adjoint {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) :
    chooseAdjoint .adjoint G = Gᴴ := rfl

/-- The CEH two-resolvent matrix word for one adjoint constellation. -/
def twoResolventWord {N : ℕ} (c₁ c₂ : AdjointChoice)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  chooseAdjoint c₁ G₁ * A * chooseAdjoint c₂ G₂

/-- Its normalized trace. -/
def twoResolventObservable {N : ℕ} (c₁ c₂ : AdjointChoice)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  NTrace (twoResolventWord c₁ c₂ G₁ A G₂)

/-- All four adjoint constellations, in the order `++,+-,-+,--`. -/
def allAdjointObservables {N : ℕ}
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) : Fin 4 → ℂ
  | 0 => twoResolventObservable .plain .plain G₁ A G₂
  | 1 => twoResolventObservable .plain .adjoint G₁ A G₂
  | 2 => twoResolventObservable .adjoint .plain G₁ A G₂
  | _ => twoResolventObservable .adjoint .adjoint G₁ A G₂

/-- CEH's scalar cutoff `θ(x) = (1 + sgn x) / 2`, including the value
`θ(0) = 1/2` at the transition point. -/
def cehTheta (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x = 0 then 1 / 2 else 1

@[simp] theorem cehTheta_of_neg {x : ℝ} (hx : x < 0) :
    cehTheta x = 0 := by
  simp [cehTheta, hx]

@[simp] theorem cehTheta_zero : cehTheta 0 = 1 / 2 := by
  norm_num [cehTheta]

@[simp] theorem cehTheta_of_pos {x : ℝ} (hx : 0 < x) :
    cehTheta x = 1 := by
  simp [cehTheta, not_lt_of_ge hx.le, ne_of_gt hx]

/-- CEH's cutoff `theta(z₁,z₂)`, expressed from the MDE word.  Unlike a
Boolean cutoff, this records the source value `1/2` when the argument is
exactly at the threshold. -/
def regularizationCoefficient {N : ℕ} (lambda : ℂ)
    (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  cehTheta ((lambda ^ 2 * NTrace (M₁plus * M₂minus)).re - 1 / 2)

/-- The CEH regularization `A°`, Definition 5.1. -/
def regularizedObservable {N : ℕ} (theta : ℝ)
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  A - ((theta : ℂ) * (NTrace (M₁plus * A * M₂minus) /
    NTrace (M₁plus * M₂minus))) • (1 : Matrix (Fin N) (Fin N) ℂ)

@[simp] theorem regularizedObservable_inactive {N : ℕ}
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ) :
    regularizedObservable 0 M₁plus M₂minus A = A := by
  simp [regularizedObservable]

/-- At cutoff coefficient one the unstable MDE trace direction is killed exactly. -/
theorem regularizedObservable_trace_zero {N : ℕ}
    (M₁plus M₂minus A : Matrix (Fin N) (Fin N) ℂ)
    (hpair : NTrace (M₁plus * M₂minus) ≠ 0) :
    NTrace (M₁plus * regularizedObservable 1 M₁plus M₂minus A * M₂minus) = 0 := by
  simp only [regularizedObservable, Complex.ofReal_one, one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul,
    NTrace_sub]
  rw [show M₁plus *
      ((NTrace (M₁plus * A * M₂minus) / NTrace (M₁plus * M₂minus)) •
        (1 : Matrix (Fin N) (Fin N) ℂ)) * M₂minus =
      (NTrace (M₁plus * A * M₂minus) / NTrace (M₁plus * M₂minus)) •
        (M₁plus * M₂minus) by
    simp [Matrix.mul_assoc]]
  rw [NTrace_smul]
  rw [div_mul_cancel₀ _ hpair]
  ring

/-- `Gamma = Im M / <Im M>` from CEH Definition 5.1. -/
def gammaMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (NTrace (CEHNative.BlockBand.matrixImaginaryPart M))⁻¹ •
    CEHNative.BlockBand.matrixImaginaryPart M

/-- The square of the CEH control parameter `s₂`.  The cutoff
coefficient blends the stable and off-diagonal terms, including the source
half-weight at the transition point.  The traces which are nonnegative in the
analytic MDE regime are represented by their real parts; the absolute-value
term is represented by the complex norm. -/
def sTwoSq {N : ℕ} (theta : ℝ) (lambda : ℂ)
    (M₁plus M₂plus Areg : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  let Γ₁ := gammaMatrix M₁plus
  let Γ₂ := gammaMatrix M₂plus
  let base := (NTrace (Γ₁ * Areg * Γ₂ * Aregᴴ)).re
  let stable := ‖NTrace (M₁plus * Areg * Γ₂) *
    NTrace (Γ₁ * Aregᴴ * M₂plus) /
      stabilityDenominator lambda (NTrace (M₁plus * M₂plus))‖
  let off := (max (max
      ‖twoResolventObservable .plain .plain M₁plus Areg M₂plus‖
      ‖twoResolventObservable .plain .adjoint M₁plus Areg M₂plus‖)
    (max
      ‖twoResolventObservable .adjoint .plain M₁plus Areg M₂plus‖
      ‖twoResolventObservable .adjoint .adjoint M₁plus Areg M₂plus‖)) ^ 2 *
      (NTrace (Γ₁ * Γ₂)).re
  base + theta * ‖lambda‖ ^ 2 * stable + (1 - theta) * ‖lambda‖ ^ 4 * off

/-- CEH's `s₂`, without an assumption that `sTwoSq` is nonnegative. -/
def sTwo {N : ℕ} (theta : ℝ) (lambda : ℂ)
    (M₁plus M₂plus Areg : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (sTwoSq theta lambda M₁plus M₂plus Areg)

/-- The deterministic two-resolvent approximation in each constellation. -/
def deterministicConstellation {N : ℕ} (lambda : ℂ)
    (c₁ c₂ : AdjointChoice) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :=
  twoResolventApprox lambda (chooseAdjoint c₁ M₁) A (chooseAdjoint c₂ M₂)

/-- The normalized trace error for one constellation. -/
def constellationError {N : ℕ} (lambda : ℂ)
    (c₁ c₂ : AdjointChoice)
    (G₁ M₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  NTrace (twoResolventWord c₁ c₂ G₁ A G₂ -
    deterministicConstellation lambda c₁ c₂ M₁ A M₂)

/-- Maximum of the four constellation errors. -/
def maxConstellationError {N : ℕ} (lambda : ℂ)
    (G₁ M₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  max (max
    ‖constellationError lambda .plain .plain G₁ M₁ A G₂ M₂‖
    ‖constellationError lambda .plain .adjoint G₁ M₁ A G₂ M₂‖)
  (max
    ‖constellationError lambda .adjoint .plain G₁ M₁ A G₂ M₂‖
    ‖constellationError lambda .adjoint .adjoint G₁ M₁ A G₂ M₂‖)

/-- CEH `Psi₁`, equation (5.17). -/
def PsiOne {N : ℕ} (ell eta₁ eta₂ rho₁ rho₂ s₂ : ℝ) (lambda : ℂ)
    (G₁ M₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (N * ell) * Real.sqrt (N * eta₁ * eta₂ / (rho₁ * rho₂)) * s₂⁻¹ *
    maxConstellationError lambda G₁ M₁ A G₂ M₂

/-- Fourfold deterministic approximation `M-hat` for the positive chain. -/
def positiveDeterministicApprox {N : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (-(1 / 4 : ℂ)) •
    (deterministicConstellation lambda .plain .plain M₁ A M₂ +
    deterministicConstellation lambda .adjoint .adjoint M₁ A M₂ -
    deterministicConstellation lambda .plain .adjoint M₁ A M₂ -
    deterministicConstellation lambda .adjoint .plain M₁ A M₂)

/-- Positive two-resolvent error in CEH (5.18). -/
def positiveChainError {N : ℕ} (lambda : ℂ)
    (G₁ M₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  NTrace (CEHNative.BlockBand.matrixImaginaryPart G₁ * A *
    CEHNative.BlockBand.matrixImaginaryPart G₂ * Aᴴ -
      positiveDeterministicApprox lambda M₁ A M₂ * Aᴴ)

/-- CEH `Psi₂`, equation (5.18). -/
def PsiTwo {N : ℕ} (ell rho₁ rho₂ s₂ : ℝ) (lambda : ℂ)
    (G₁ M₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (N * ell) / (rho₁ * rho₂ * s₂ ^ 2) *
    ‖positiveChainError lambda G₁ M₁ A G₂ M₂‖

/-!
## Exact inverse-pencil and underlined identities
-/

/-- The two-body stability operator in CEH (5.20),
`B₁₂[X] = X - λ² M₁ ⟨X⟩ M₂`. -/
def twoBodyStability {N : ℕ} (lambda : ℂ)
    (M₁ M₂ X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  X - (lambda ^ 2 * NTrace X) • (M₁ * M₂)

/-- The underlined matrix word appearing in CEH (5.20).  This is a
definition, not an assumed error representation. -/
def underlinedTwoResolventWord {N : ℕ} (lambda : ℂ)
    (W G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  lambda • (W * G₁ * A * G₂) +
    (lambda ^ 2 * NTrace G₁) • (G₁ * A * G₂) +
    (lambda ^ 2 * NTrace (G₁ * A * G₂)) • G₂

/-- Basic inverse-pencil resolvent identity.  These are precisely the algebraic
parts of the resolvent and MDE equations: `M Q = I`, `P G = I`, and
`Q-P=D`. -/
theorem resolvent_sub_from_pencils {N : ℕ}
    (P Q G M D : Matrix (Fin N) (Fin N) ℂ)
    (hMQ : M * Q = 1) (hPG : P * G = 1) (hD : Q - P = D) :
    G - M = M * D * G := by
  calc
    G - M = M * Q * G - M * P * G := by
      rw [hMQ, Matrix.mul_assoc, hPG]
      simp
    _ = M * (Q - P) * G := by noncomm_ring
    _ = M * D * G := by rw [hD]

/-- The one-resolvent identity specialized to the CEH inverse pencils.  The
last hypothesis is the scalar MDE self-energy in inverse-pencil form. -/
theorem resolvent_sub_from_ceh_pencils {N : ℕ} (lambda : ℂ)
    (P Q W G M : Matrix (Fin N) (Fin N) ℂ)
    (hMQ : M * Q = 1) (hPG : P * G = 1)
    (hD : Q - P =
      (-lambda) • W - (lambda ^ 2 * NTrace M) •
        (1 : Matrix (Fin N) (Fin N) ℂ)) :
    G - M =
      (-lambda) • (M * W * G) -
        (lambda ^ 2 * NTrace M) • (M * G) := by
  rw [resolvent_sub_from_pencils P Q G M
    (Q - P) hMQ hPG rfl, hD]
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- The deterministic approximation solves the rank-one stability equation
exactly.  This is the MDE algebra used when deriving CEH (5.20). -/
theorem twoResolventApprox_fixedPoint {N : ℕ} (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hstable : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0) :
    twoResolventApprox lambda M₁ A M₂ =
      M₁ * A * M₂ +
        (lambda ^ 2 * NTrace (twoResolventApprox lambda M₁ A M₂)) •
          (M₁ * M₂) := by
  rw [twoResolventApprox]
  simp only [NTrace_add, NTrace_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  unfold stabilityDenominator at hstable ⊢
  field_simp [hstable]
  ring

/-- Exact CEH basic identity (5.20), derived from the two inverse-pencil
equations and the scalar MDE self-energy.  In particular the underlined word
is not supplied as a hypothesis. -/
theorem twoResolvent_basicIdentity {N : ℕ} (lambda : ℂ)
    (P₁ Q₁ W G₁ M₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hMQ : M₁ * Q₁ = 1) (hPG : P₁ * G₁ = 1)
    (hD : Q₁ - P₁ =
      (-lambda) • W - (lambda ^ 2 * NTrace M₁) •
        (1 : Matrix (Fin N) (Fin N) ℂ))
    (hstable : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0) :
    twoBodyStability lambda M₁ M₂
        (G₁ * A * G₂ - twoResolventApprox lambda M₁ A M₂) =
      M₁ * A * (G₂ - M₂) -
        M₁ * underlinedTwoResolventWord lambda W G₁ A G₂ +
        (lambda ^ 2 * NTrace (G₁ * A * G₂)) • (M₁ * (G₂ - M₂)) +
        (lambda ^ 2 * NTrace (G₁ - M₁)) • (M₁ * G₁ * A * G₂) := by
  have hGM := resolvent_sub_from_ceh_pencils lambda P₁ Q₁ W G₁ M₁ hMQ hPG hD
  have hword :
      G₁ * A * G₂ - M₁ * A * M₂ =
        (-lambda) • (M₁ * W * G₁ * A * G₂) -
          (lambda ^ 2 * NTrace M₁) • (M₁ * G₁ * A * G₂) +
          M₁ * A * (G₂ - M₂) := by
    calc
      G₁ * A * G₂ - M₁ * A * M₂ =
          (G₁ - M₁) * A * G₂ + M₁ * A * (G₂ - M₂) := by
            noncomm_ring
      _ = _ := by
        rw [hGM]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
          Matrix.smul_mul]
  have hleft :
      twoBodyStability lambda M₁ M₂
          (G₁ * A * G₂ - twoResolventApprox lambda M₁ A M₂) =
        G₁ * A * G₂ - M₁ * A * M₂ -
          (lambda ^ 2 * NTrace (G₁ * A * G₂)) • (M₁ * M₂) := by
    unfold twoBodyStability twoResolventApprox
    simp only [NTrace_sub, NTrace_add, NTrace_smul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    unfold stabilityDenominator at hstable ⊢
    field_simp [hstable]
    ring
  rw [hleft, hword, underlinedTwoResolventWord]
  simp only [NTrace_sub, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_assoc, Matrix.mul_smul]
  module

/-- On normalized traces the two-body stability operator is multiplication by
the CEH scalar denominator. -/
theorem NTrace_twoBodyStability {N : ℕ} (lambda : ℂ)
    (M₁ M₂ X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (twoBodyStability lambda M₁ M₂ X) =
      stabilityDenominator lambda (NTrace (M₁ * M₂)) * NTrace X := by
  rw [twoBodyStability, NTrace_sub, NTrace_smul]
  simp only [stabilityDenominator]
  ring

/-- Exact normalized-trace version of CEH (5.20)--(5.21).  This is the
underlined representation before any local-law estimates or Gaussian
integration by parts. -/
theorem twoResolvent_basicTraceIdentity {N : ℕ} (lambda : ℂ)
    (P₁ Q₁ W G₁ M₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hMQ : M₁ * Q₁ = 1) (hPG : P₁ * G₁ = 1)
    (hD : Q₁ - P₁ =
      (-lambda) • W - (lambda ^ 2 * NTrace M₁) •
        (1 : Matrix (Fin N) (Fin N) ℂ))
    (hstable : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0) :
    stabilityDenominator lambda (NTrace (M₁ * M₂)) *
        NTrace (G₁ * A * G₂ - twoResolventApprox lambda M₁ A M₂) =
      NTrace (M₁ * A * (G₂ - M₂)) -
        NTrace (M₁ * underlinedTwoResolventWord lambda W G₁ A G₂) +
        lambda ^ 2 * NTrace (G₁ * A * G₂) * NTrace (M₁ * (G₂ - M₂)) +
        lambda ^ 2 * NTrace (G₁ - M₁) * NTrace (M₁ * G₁ * A * G₂) := by
  have h := congrArg NTrace
    (twoResolvent_basicIdentity lambda P₁ Q₁ W G₁ M₁ A G₂ M₂
      hMQ hPG hD hstable)
  rw [NTrace_twoBodyStability] at h
  simp only [NTrace_add, NTrace_sub, NTrace_smul] at h
  rw [NTrace_sub, NTrace_sub]
  simpa [mul_assoc] using h

/-- Exact matrix underlined representation of a two-resolvent word.  It is
derived from the inverse-pencil data, not passed as a representation
hypothesis. -/
theorem twoResolventWord_underlined {N : ℕ}
    (P₁ Q₁ G₁ M₁ D₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hMQ : M₁ * Q₁ = 1) (hPG : P₁ * G₁ = 1) (hD : Q₁ - P₁ = D₁) :
    G₁ * A * G₂ - M₁ * A * M₂ =
      M₁ * D₁ * G₁ * A * G₂ + M₁ * A * (G₂ - M₂) := by
  have hsub := resolvent_sub_from_pencils P₁ Q₁ G₁ M₁ D₁ hMQ hPG hD
  calc
    G₁ * A * G₂ - M₁ * A * M₂ =
        (G₁ - M₁) * A * G₂ + M₁ * A * (G₂ - M₂) := by noncomm_ring
    _ = _ := by rw [hsub]

/-- Exact normalized-trace underlined representation. -/
theorem twoResolventTrace_underlined {N : ℕ}
    (P₁ Q₁ G₁ M₁ D₁ A G₂ M₂ : Matrix (Fin N) (Fin N) ℂ)
    (hMQ : M₁ * Q₁ = 1) (hPG : P₁ * G₁ = 1) (hD : Q₁ - P₁ = D₁) :
    NTrace (G₁ * A * G₂ - M₁ * A * M₂) =
      NTrace (M₁ * D₁ * G₁ * A * G₂) +
        NTrace (M₁ * A * (G₂ - M₂)) := by
  rw [twoResolventWord_underlined P₁ Q₁ G₁ M₁ D₁ A G₂ M₂ hMQ hPG hD,
    NTrace_add]

/-- Matrix fourfold polarization of the positive chain. -/
theorem positiveChain_eq_fourfold {N : ℕ}
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    CEHNative.BlockBand.matrixImaginaryPart G₁ * A *
        CEHNative.BlockBand.matrixImaginaryPart G₂ * Aᴴ =
      (-(1 / 4 : ℂ)) •
        (G₁ * A * G₂ * Aᴴ + G₁ᴴ * A * G₂ᴴ * Aᴴ -
          G₁ * A * G₂ᴴ * Aᴴ - G₁ᴴ * A * G₂ * Aᴴ) := by
  have hexpand :
      (G₁ - G₁ᴴ) * A * (G₂ - G₂ᴴ) * Aᴴ =
        G₁ * A * G₂ * Aᴴ + G₁ᴴ * A * G₂ᴴ * Aᴴ -
          G₁ * A * G₂ᴴ * Aᴴ - G₁ᴴ * A * G₂ * Aᴴ := by
    noncomm_ring
  have hsmul (c : ℂ) (X Y Z : Matrix (Fin N) (Fin N) ℂ) :
      (c • X) * A * (c • Y) * Z = (c * c) • (X * A * Y * Z) := by
    calc
      (c • X) * A * (c • Y) * Z =
          (c • (X * A)) * (c • Y) * Z := by rw [Matrix.smul_mul]
      _ = (c • ((X * A) * (c • Y))) * Z := by rw [Matrix.smul_mul]
      _ = (c • (c • ((X * A) * Y))) * Z := by
        apply congrArg (fun T : Matrix (Fin N) (Fin N) ℂ => T * Z)
        apply congrArg (fun T : Matrix (Fin N) (Fin N) ℂ => c • T)
        rw [Matrix.mul_smul]
      _ = ((c * c) • ((X * A) * Y)) * Z := by
        apply congrArg (fun T : Matrix (Fin N) (Fin N) ℂ => T * Z)
        exact smul_smul c c ((X * A) * Y)
      _ = (c * c) • (X * A * Y * Z) := by rw [Matrix.smul_mul]
  have hc : (-Complex.I / 2) * (-Complex.I / 2) = -(1 / 4 : ℂ) := by
    apply Complex.ext <;> norm_num
  rw [CEHNative.BlockBand.matrixImaginaryPart,
    CEHNative.BlockBand.matrixImaginaryPart, hsmul, hexpand]
  rw [hc]

/-- Normalized-trace form of the fourfold polarization. -/
theorem positiveChainTrace_eq_fourfold {N : ℕ}
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (CEHNative.BlockBand.matrixImaginaryPart G₁ * A *
        CEHNative.BlockBand.matrixImaginaryPart G₂ * Aᴴ) =
      NTrace ((-(1 / 4 : ℂ)) •
        (G₁ * A * G₂ * Aᴴ + G₁ᴴ * A * G₂ᴴ * Aᴴ -
          G₁ * A * G₂ᴴ * Aᴴ - G₁ᴴ * A * G₂ * Aᴴ)) := by
  rw [positiveChain_eq_fourfold]

end CEHNative.BlockBand.External.CEH
