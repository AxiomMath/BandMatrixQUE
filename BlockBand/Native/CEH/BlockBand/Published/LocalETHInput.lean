module

public import BlockBand.Native.CEH.BlockBand.Conventions
public import BlockBand.Native.CEH.BlockBand.Spectral.Measurable.Counts
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Conditional local-ETH input

The regular-window consequence of the Cipolloni–Erdős–Henheik eigenstate-thermalization
estimate (the external ETH theorem), recorded as explicit data: the statement does not assert
the cited theorem, and a user must supply a value of `LocalETHInput gue` for the chosen
deformed-GUE laws.

A sample is `F + G`, with `G ∼ GUE_N(s/N)` represented by `gue N (s/N)`. The deterministic MDE
branch solves

`M = (F - z - s ⟨M⟩)⁻¹`,

`ρ_s = π⁻¹ |Im ⟨M⟩|`, and `Γ = Im M / Im ⟨M⟩`. The bad event is simultaneous
in every orthonormal eigenbasis and every pair of eigenvalues in the window of
radius `N^(-1+β)`. The observable `J` is fixed before the random matrix; the
probability cutoff is uniform in `s`, `F`, the MDE branch, the spacing function,
the center energy, and `J`. The loss is the stochastic-domination loss
`N^δ`; it is not replaced by a constant.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory
open scoped ComplexOrder Matrix ENNReal Matrix.Norms.L2Operator

/-- Complex `N × N` matrices used in the MDE and ETH statements. -/
abbrev LocalETHMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-- A dimension- and variance-indexed family of Hermitian probability laws.
The intended specialization is `GUE_N(t)`, with `t = s/N` below. -/
abbrev LocalETHGUEFamily :=
  (N : ℕ) → ℝ → ProbabilityMeasure (HermitianMatrix (Fin N))

/-- Matrix imaginary part `(A - Aᴴ)/(2i)`. -/
noncomputable def localETHImPart {N : ℕ} (A : LocalETHMatrix N) : LocalETHMatrix N :=
  (2 * Complex.I)⁻¹ • (A - Aᴴ)

/-- The matrix Dyson equation together with its half-plane sign
condition. The displayed multiplication is the one-sided inverse equation
`(F - z - s⟨M⟩)M = 1`. -/
structure IsLocalETHMDESolution {N : ℕ} (s : ℝ) (F : LocalETHMatrix N)
    (z : ℂ) (M : LocalETHMatrix N) : Prop where
  inv : (F - (z + (s : ℂ) * Conventions.normalizedTrace M) • (1 : LocalETHMatrix N)) * M = 1
  pos : (((z.im : ℝ) : ℂ) • localETHImPart M).PosDef

/-- The self-consistent density `ρ_s(z) = π⁻¹ |Im ⟨M(z)⟩|`. -/
noncomputable def localETHMDEDensity {N : ℕ} (M : LocalETHMatrix N) : ℝ :=
  |(Conventions.normalizedTrace M).im| / Real.pi

/-- The relative matrix `Γ(z) = Im M(z) / Im ⟨M(z)⟩`. -/
noncomputable def localETHGamma {N : ℕ} (M : LocalETHMatrix N) : LocalETHMatrix N :=
  (((Conventions.normalizedTrace M).im : ℂ))⁻¹ • localETHImPart M

/-- The large-deformation hypothesis `‖F‖ ≤ C N^κ √s`. -/
def LocalETHDeformationBound {N : ℕ} (κ C s : ℝ) (F : LocalETHMatrix N) : Prop :=
  ‖F‖ ≤ C * (N : ℝ) ^ κ * Real.sqrt s

/-- A branch of solutions of the MDE at every non-real spectral parameter. -/
def IsLocalETHMDEBranch {N : ℕ} (s : ℝ) (F : LocalETHMatrix N)
    (Mf : ℂ → LocalETHMatrix N) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → IsLocalETHMDESolution s F z (Mf z)

/-- The typical spacing equation
`N η ρ_s(x + iη) = 1`, including positivity of `η`. -/
def IsLocalETHTypicalSpacing {N : ℕ} (Mf : ℂ → LocalETHMatrix N)
    (x η : ℝ) : Prop :=
  0 < η ∧
    (N : ℝ) * η *
      localETHMDEDensity (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) = 1

/-- Entrywise derivative of a matrix-valued function. -/
def HasLocalETHMatrixDerivAt {N : ℕ} (f : ℝ → LocalETHMatrix N)
    (f' : LocalETHMatrix N) (x : ℝ) : Prop :=
  ∀ a b : Fin N, HasDerivAt (fun t => f t a b) (f' a b) x

/-- The regular-boundary hypotheses of the external ETH theorem on the open
neighborhood `(E₀-r,E₀+r)`. `Mb` is the upper boundary value of the MDE
branch and `Mb'` its derivative. The derivative bound on the normalized trace
is a consequence of the displayed matrix derivative bound and is therefore not
stored as an additional assumption. -/
structure LocalETHRegularBoundaryWindow {N : ℕ} (s : ℝ)
    (Mf : ℂ → LocalETHMatrix N) (E₀ r c K : ℝ) : Prop where
  boundary : ∃ Mb Mb' : ℝ → LocalETHMatrix N,
    ∀ x ∈ Set.Ioo (E₀ - r) (E₀ + r),
      Filter.Tendsto
          (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (Mb x)) ∧
        HasLocalETHMatrixDerivAt Mb (Mb' x) x ∧
        ‖Mb' x‖ ≤ K ∧
        c ≤ (Conventions.normalizedTrace (Mb x)).im ∧
        ‖Mb x‖ ≤ K ∧
        c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb x * Mb x)‖

/-- An orthonormal eigenvector family of `A`, with real eigenvalues `lam`.
No order is imposed because the cited consequence only uses membership in the
shrinking energy window. -/
def IsLocalETHOrthonormalEigenFamily {N : ℕ} (A : LocalETHMatrix N)
    (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ) : Prop :=
  (∀ i j, star (u i) ⬝ᵥ u j = if i = j then 1 else 0) ∧
    ∀ i, A *ᵥ u i = (lam i : ℂ) • u i

/-- CEH equation (2.12): `x + i N^ξ η_f(x)`. -/
noncomputable def localETHSpectralPoint
    (N : ℕ) (etaF : ℝ → ℝ) (ξ x : ℝ) : ℂ :=
  (x : ℂ) + (((N : ℝ) ^ ξ * etaF x : ℝ) : ℂ) * Complex.I

/-- The deterministic diagonal center
`⟨Γ(x + i N^ξ η_f(x)) J⟩`. -/
noncomputable def localETHCenter {N : ℕ} (Mf : ℂ → LocalETHMatrix N)
    (etaF : ℝ → ℝ) (ξ x : ℝ) (J : LocalETHMatrix N) : ℂ :=
  Conventions.normalizedTrace
    (localETHGamma (Mf (localETHSpectralPoint N etaF ξ x)) * J)

/-- The overlap error in the external ETH estimate, including its Kronecker delta. -/
noncomputable def localETHError {N : ℕ} (Mf : ℂ → LocalETHMatrix N)
    (etaF : ℝ → ℝ) (ξ : ℝ) (J : LocalETHMatrix N)
    (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ) (i j : Fin N) : ℝ :=
  ‖star (u i) ⬝ᵥ (J *ᵥ u j) -
    if i = j then localETHCenter Mf etaF ξ (lam i) J else 0‖

/-- The bad event of the external ETH estimate. It quantifies over every
orthonormal eigenbasis and every pair in the window of radius `N^(β-1)`, and
uses the stochastic-domination threshold `N^δ N^(-1/2)`. -/
def LocalETHWindowBad {N : ℕ} (Mf : ℂ → LocalETHMatrix N)
    (etaF : ℝ → ℝ) (ξ β δ E₀ : ℝ) (F J : LocalETHMatrix N)
    (G : HermitianMatrix (Fin N)) : Prop :=
  ∃ (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ),
    IsLocalETHOrthonormalEigenFamily (F + G.1) lam u ∧
      ∃ i j : Fin N,
        |lam i - E₀| ≤ (N : ℝ) ^ (β - 1) ∧
        |lam j - E₀| ≤ (N : ℝ) ^ (β - 1) ∧
        (N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ)) <
          localETHError Mf etaF ξ J lam u i j

/-- The cutoff depends only on the fixed parameters appearing before it.  It is
uniform over the dimension-dependent variance, deformation, MDE branch,
typical-spacing function, window center, and deterministic observable. -/
def LocalETHRegularWindowBound (gue : LocalETHGUEFamily) : Prop :=
  ∀ κ C : ℝ, 0 ≤ κ → 0 < C →
  ∀ sLo sHi : ℝ, 0 < sLo → sLo ≤ sHi →
  ∀ r c K : ℝ, 0 < r → 0 < c → 0 < K →
  ∀ β : ℝ, 0 < β → β ≤ 1 / 2 →
  ∀ ξ : ℝ, 0 < ξ → ξ < β →
  ∀ δ D : ℝ, 0 < δ → 0 < D →
  ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
    ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
    ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
    ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
    ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
    ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
          {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The conditional input for the external local ETH theorem.

This is a proposition-valued structure, used as a hypothesis; it is not an axiom and does not
assert that the CEH estimate is formalized. -/
structure LocalETHInput (gue : LocalETHGUEFamily) : Prop where
  regularWindow : LocalETHRegularWindowBound gue

/-- The fixed-variance form of the external ETH statement: the variance `s > 0` is fixed before
`β₀` and `N₀` are chosen. -/
def LocalETHSourceForm (gue : LocalETHGUEFamily) : Prop :=
  ∀ κ C : ℝ, 0 ≤ κ → 0 < C →
  ∀ s : ℝ, 0 < s →
  ∀ r c K : ℝ, 0 < r → 0 < c → 0 < K →
  ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ β : ℝ, 0 < β → β ≤ β₀ →
    ∀ ξ : ℝ, 0 < ξ → ξ < β →
    ∀ δ D : ℝ, 0 < δ → 0 < D →
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- A uniform local-ETH input implies the fixed-variance statement, with `β₀ = 1/2`. -/
theorem LocalETHInput.sourceForm {gue : LocalETHGUEFamily}
    (input : LocalETHInput gue) : LocalETHSourceForm gue := by
  intro κ C hκ hC s hs r c K hr hc hK
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro β hβ hβ₀ ξ hξ hξβ δ D hδ hD
  obtain ⟨N₀, hN₀, hmain⟩ :=
    input.regularWindow κ C hκ hC s s hs le_rfl r c K hr hc hK
      β hβ hβ₀ ξ hξ hξβ δ D hδ hD
  exact ⟨N₀, hN₀, fun N hN => hmain N hN s le_rfl le_rfl⟩

end CEHNative.BlockBand
