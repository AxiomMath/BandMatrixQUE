module

public import BlockBand.Native.CEH.BlockBand.External.CEH.LocalLawContract

/-!
# Source-shaped CEH eigenstate-thermalization statement

The regular-window specialization of Cipolloni–Erdős–Henheik, Theorem 2.5 and equations
(2.12)–(2.15), used as the external ETH theorem. The binder order, normalized trace,
`GUE_N(s/N)` scaling, typical-spacing equation, `N^ξ η_f` regularization, Kronecker diagonal
center, and `N^δ N⁻¹ᐟ²` stochastic-domination loss are explicit below.

The CEH-facing theorem schema records the `θ = 1` part in the order supported by
the printed proof: after the loss and tail exponents there is a sufficiently small
`ξ₀`, and the estimate holds for every `0 < ξ ≤ ξ₀`. The regular-window statement is
definitionally `LocalETHRegularWindowBound`.

Everything here is a proposition or an explicit input structure. In particular, this module
declares no value of `CEHETHInput` and no assumption; it does not claim the cited theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory
open scoped ComplexOrder Matrix ENNReal Matrix.Norms.L2Operator

/-- Complex `N × N` matrices in the CEH ETH statement. -/
abbrev CEHETHMatrix (N : ℕ) := LocalETHMatrix N

/-- Dimension- and variance-indexed Hermitian laws; `(N,t)` means `GUE_N(t)`. -/
abbrev CEHETHGUEFamily := LocalETHGUEFamily

/-!
## Definitional CEH names for the published regular-window vocabulary
-/

/-- A branch of MDE solutions at every non-real spectral parameter. -/
abbrev IsMDEBranch {N : ℕ} (s : ℝ) (F : CEHETHMatrix N)
    (Mf : ℂ → CEHETHMatrix N) : Prop :=
  IsLocalETHMDEBranch s F Mf

/-- The equation `N η ρ_s(x+iη)=1`, including `η>0`. -/
abbrev IsTypicalSpacing {N : ℕ} (Mf : ℂ → CEHETHMatrix N)
    (x η : ℝ) : Prop :=
  IsLocalETHTypicalSpacing Mf x η

/-- Entrywise derivative of a matrix-valued boundary function. -/
abbrev HasMatrixDerivAt {N : ℕ} (f : ℝ → CEHETHMatrix N)
    (f' : CEHETHMatrix N) (x : ℝ) : Prop :=
  HasLocalETHMatrixDerivAt f f' x

/-- The exact regular boundary window. -/
abbrev RegularBoundaryWindow {N : ℕ} (s : ℝ)
    (Mf : ℂ → CEHETHMatrix N) (E₀ r c K : ℝ) : Prop :=
  LocalETHRegularBoundaryWindow s Mf E₀ r c K

/-- An orthonormal eigenfamily, with no ordering imposed on its labels. -/
abbrev IsOrthonormalEigenFamily {N : ℕ} (A : CEHETHMatrix N)
    (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ) : Prop :=
  IsLocalETHOrthonormalEigenFamily A lam u

/-- CEH (2.12), `x+i N^ξ η_f(x)`. -/
abbrev specPoint (N : ℕ) (etaF : ℝ → ℝ) (ξ x : ℝ) : ℂ :=
  localETHSpectralPoint N etaF ξ x

/-- The diagonal center `⟨Γ(x+iN^ξ η_f(x))J⟩`. -/
abbrev ethCenter {N : ℕ} (Mf : ℂ → CEHETHMatrix N)
    (etaF : ℝ → ℝ) (ξ x : ℝ) (J : CEHETHMatrix N) : ℂ :=
  localETHCenter Mf etaF ξ x J

/-- The overlap error `|u_i^*Ju_j-δ_ij⟨Γ(λ̂_i)J⟩|`. -/
abbrev ethError {N : ℕ} (Mf : ℂ → CEHETHMatrix N)
    (etaF : ℝ → ℝ) (ξ : ℝ) (J : CEHETHMatrix N)
    (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ) (i j : Fin N) : ℝ :=
  localETHError Mf etaF ξ J lam u i j

/-- The simultaneous regular-window bad event at threshold `N^δ N⁻¹ᐟ²`. -/
abbrev ETHWindowBad {N : ℕ} (Mf : ℂ → CEHETHMatrix N)
    (etaF : ℝ → ℝ) (ξ β δ E₀ : ℝ) (F J : CEHETHMatrix N)
    (G : HermitianMatrix (Fin N)) : Prop :=
  LocalETHWindowBad Mf etaF ξ β δ E₀ F J G

/-- The quantifier order is exactly
`κ,C,sLo,sHi,r,c,K,β,ξ,δ,D; ∃ N₀; ∀ N,s,F,Mf,etaF,E₀,J`.
Thus the cutoff may depend on precisely the fixed parameters before it, while the
probability estimate is uniform in every dimension-dependent object after it.
The law is evaluated at variance `s/N` and the tail is `N⁻ᴰ`. -/
abbrev ExternalETHRegularWindow (gue : CEHETHGUEFamily) : Prop :=
  LocalETHRegularWindowBound gue

/-- The fixed-variance, sufficiently-small-window form of the external ETH theorem. -/
abbrev ExternalETHSourceForm (gue : CEHETHGUEFamily) : Prop :=
  LocalETHSourceForm gue

/-- The source-shaped regular-window schema and the published vocabulary are
judgmentally the same proposition. -/
theorem externalETHRegularWindow_iff_localETHRegularWindowBound
    (gue : CEHETHGUEFamily) :
    ExternalETHRegularWindow gue ↔ LocalETHRegularWindowBound gue :=
  Iff.rfl

/-- The fixed-variance source form and the published vocabulary are
judgmentally the same proposition. -/
theorem externalETHSourceForm_iff_localETHSourceForm
    (gue : CEHETHGUEFamily) :
    ExternalETHSourceForm gue ↔ LocalETHSourceForm gue :=
  Iff.rfl

/-- The uniform statement implies the fixed-variance source form, with `β₀=1/2`. -/
theorem ExternalETHRegularWindow.sourceForm {gue : CEHETHGUEFamily}
    (h : ExternalETHRegularWindow gue) : ExternalETHSourceForm gue :=
  LocalETHInput.sourceForm ⟨h⟩

/-!
## CEH Theorem 2.5 in the `θ = 1` regime
-/

/-- CEH (2.13) when `θ_ij=1`:
`A° = A - ⟨M_i A M_j^*⟩/⟨M_i M_j^*⟩ I`. -/
noncomputable def regObs {N : ℕ} (Mi Mj A : CEHETHMatrix N) : CEHETHMatrix N :=
  A - (Conventions.normalizedTrace (Mi * A * Mjᴴ) /
    Conventions.normalizedTrace (Mi * Mjᴴ)) • (1 : CEHETHMatrix N)

/-- CEH (2.14) at `θ_ij=1`, with `λ²=s`, normalized trace, and
`Γ=Im M/Im⟨M⟩`. -/
noncomputable def s2SqTheta1 {N : ℕ} (s : ℝ)
    (Mi Mj A : CEHETHMatrix N) : ℝ :=
  (Conventions.normalizedTrace
      (localETHGamma Mi * regObs Mi Mj A *
        localETHGamma Mj * (regObs Mi Mj A)ᴴ)).re +
    s * ‖Conventions.normalizedTrace
          (Mi * regObs Mi Mj A * localETHGamma Mj) *
        Conventions.normalizedTrace
          (localETHGamma Mi * (regObs Mi Mj A)ᴴ * Mj) /
        (1 - (s : ℂ) * Conventions.normalizedTrace (Mi * Mj))‖

/-- The strict `θ=1` condition `1/2 < s Re⟨M_i M_j^*⟩`. -/
def ThetaOne {N : ℕ} (s : ℝ) (Mi Mj : CEHETHMatrix N) : Prop :=
  1 / 2 < s * (Conventions.normalizedTrace (Mi * Mjᴴ)).re

/-- Bad event in CEH (2.15), restricted to `θ=1` and simultaneous over
orthonormal eigenfamilies and ordered index pairs. -/
def CEHETHTheta1Bad {N : ℕ} (s : ℝ)
    (Mf : ℂ → CEHETHMatrix N) (etaF : ℝ → ℝ) (ξ δ : ℝ)
    (F A : CEHETHMatrix N) (G : HermitianMatrix (Fin N)) : Prop :=
  ∃ (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ),
    IsOrthonormalEigenFamily (F + G.1) lam u ∧
      ∃ i j : Fin N,
        ThetaOne s (Mf (specPoint N etaF ξ (lam i)))
          (Mf (specPoint N etaF ξ (lam j))) ∧
        (N : ℝ) ^ δ *
              Real.sqrt (s2SqTheta1 s
                (Mf (specPoint N etaF ξ (lam i)))
                (Mf (specPoint N etaF ξ (lam j))) A) *
              (N : ℝ) ^ (-(1 / 2 : ℝ)) <
          ‖star (u i) ⬝ᵥ (A *ᵥ u j) -
            if i = j then
              Conventions.normalizedTrace
                (localETHGamma (Mf (specPoint N etaF ξ (lam i))) * A)
            else 0‖

/-- CEH Theorem 2.5, equations (2.12)–(2.15), for `GUE_N(s/N)` in the
`θ=1` regime and in the quantifier order supported by its printed proof.

For fixed deformation parameters and stochastic-domination exponents `δ,D`,
the statement supplies `ξ₀`; every `0<ξ≤ξ₀` then has a cutoff uniform in
`N,s,F,Mf,etaF,A`. The event threshold is
`N^δ sqrt(s₂²) N⁻¹ᐟ²` and its probability is at most `N⁻ᴰ`. -/
def CEHETHTheta1Bound (gue : CEHETHGUEFamily) : Prop :=
  ∀ κ C : ℝ, 0 ≤ κ → 0 < C →
  ∀ δ D : ℝ, 0 < δ → 0 < D →
  ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
  ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ s : ℝ, 0 < s →
    ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
    ∀ Mf : ℂ → CEHETHMatrix N, IsMDEBranch s F.1 Mf →
    ∀ etaF : ℝ → ℝ, (∀ x, IsTypicalSpacing Mf x (etaF x)) →
    ∀ A : CEHETHMatrix N,
      (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
          {G | CEHETHTheta1Bad s Mf etaF ξ δ F.1 A G} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- Explicit source-shaped CEH ETH input.

The `window` field is the regular-window specialization; it is an explicit field, not derived
here from the other fields. This declaration packages propositions only and introduces no
witness of them. -/
structure CEHETHInput (gue : CEHETHGUEFamily) : Prop where
  spacing_exists :
    ∀ (N : ℕ), 4 ≤ N → ∀ s : ℝ, 0 < s →
    ∀ (F : HermitianMatrix (Fin N)) (Mf : ℂ → CEHETHMatrix N),
      IsMDEBranch s F.1 Mf →
      ∀ x : ℝ, ∃ η : ℝ, IsTypicalSpacing Mf x η
  spacing_unique :
    ∀ (N : ℕ) (s : ℝ), 0 < s →
    ∀ (F : HermitianMatrix (Fin N)) (Mf : ℂ → CEHETHMatrix N),
      IsMDEBranch s F.1 Mf →
      ∀ x η η' : ℝ,
        IsTypicalSpacing Mf x η → IsTypicalSpacing Mf x η' → η = η'
  ceh : CEHETHTheta1Bound gue
  window : ExternalETHRegularWindow gue

/-- Definitional adapter from the CEH package to the `LocalETHInput` vocabulary. It forgets
the source-shaped data and keeps exactly the regular-window statement. -/
theorem CEHETHInput.toLocalETHInput {gue : CEHETHGUEFamily}
    (input : CEHETHInput gue) : LocalETHInput gue :=
  ⟨input.window⟩

/-- The adapter preserves the regular-window field by definitional equality. -/
theorem CEHETHInput.toLocalETHInput_regularWindow {gue : CEHETHGUEFamily}
    (input : CEHETHInput gue) :
    input.toLocalETHInput.regularWindow = input.window :=
  rfl

/-- A supplied CEH package exposes a typical-spacing function at every energy
once the source-required dimension guard `4 ≤ N` holds. -/
theorem CEHETHInput.exists_spacing_function {gue : CEHETHGUEFamily}
    (input : CEHETHInput gue) {N : ℕ} (hN : 4 ≤ N)
    {s : ℝ} (hs : 0 < s) (F : HermitianMatrix (Fin N))
    (Mf : ℂ → CEHETHMatrix N) (hMf : IsMDEBranch s F.1 Mf) :
    ∃ etaF : ℝ → ℝ, ∀ x, IsTypicalSpacing Mf x (etaF x) :=
  ⟨fun x => Classical.choose (input.spacing_exists N hN s hs F Mf hMf x),
    fun x => Classical.choose_spec (input.spacing_exists N hN s hs F Mf hMf x)⟩

end CEHNative.BlockBand
