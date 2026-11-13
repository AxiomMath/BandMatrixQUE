module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The complete-source gap lemma: statement

**Setting.** One fresh one-port layer `ω ~ freshLaw W b` (`A = ω.1 0`,
`B = ω.2 0 0`) is integrated at a *deterministic* Hermitian old two-port Schur matrix `𝕏` (the
old path integrated out); `X = nearSchur z 𝕏` (far port eliminated), `ℝ = (z - 𝕏)⁻¹`,
`𝕊 = I - 2iηℝ`, `P = nearProjection W`, `N = freshTransport b E 𝕏 ω`.

* `sepOf b E 𝕏 σ` is the separator `σ` (`Separator`) evaluated at `𝕊 = twoPortScattering b E 𝕏`
  (the same table as `separatorMatrix`).
* `gapFactor b E s σ = θ_*^{unconj σ} θ̄_*^{conj σ}`: `θ_*` for `P𝕊`, `P𝕊P`; `θ̄_*` for `𝕊*P`,
  `P𝕊*P`.

**Statement.** Fixed `0 < b < 1/2` and bulk `E`; the stationary jet exists, and at every stationary
jet `s` (`θ_* = thetaStar b E s`), for the four contracting separators (`σ.unconj + σ.conj = 1`):
* `CompleteSourceGapStatement.mean` (the complete-source gap and the near-source gap, and their adjoints):
  `‖E[N σ(𝕏₊) N*] - gapFactor σ · σ(𝕏)‖ ≤ C(δ₀ + δ₁ + g/W + W⁻²)`, operator norm,
  `δ₀, δ₁, g = Tr T` of `X`;
* `CompleteSourceGapStatement.fluctuation`: for `p ≥ 1`,
  `‖u*(U - EU)v‖_{L^p} ≤ C_p W^{-1/2}‖u‖‖v‖`, `U = N σ(𝕏₊) N*`.

Both are **uniform in Hermitian `𝕏`**. The lemma in the paper is stated on the fixed scalar and
first-jet domain; the uniform form is stronger and true (off a domain `δ₀ + δ₁ + g/W ≤ d` the mean
bound follows from the moment bound `‖‖N‖‖_{L^2} ≤ C` with `C/d`; the fluctuation bound, by
Gaussian Poincaré on bounded weighted words, has no domain restriction).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

/-- The two-port matrix with port blocks `M₀₀, M₀₁, M₁₀, M₁₁` (port `0` = near). -/
def ofPortBlocks {W : ℕ} (M₀₀ M₀₁ M₁₀ M₁₁ : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.of fun x y => (![![M₀₀, M₀₁], ![M₁₀, M₁₁]] x.1 y.1) x.2 y.2

/-- **The new two-port Schur matrix** `𝕏₊` of one near-end growth step:
fresh block `A = ω.1 0`, new near bond `B = ω.2 0 0`, `G₀ = (A - E - 𝕏₀₀)⁻¹`,
`𝕏₊ = [[B*G₀B, -B*G₀𝕏₀₁], [-𝕏₁₀G₀B, 𝕏₁₁ + 𝕏₁₀G₀𝕏₀₁]]`. -/
def freshTwoPortSchur {W : ℕ} (E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  let A := ω.1 0
  let B := ω.2 0 0
  let G₀ := (A - (E : ℂ) • 1 - portBlock XX 0 0)⁻¹
  ofPortBlocks (Bᴴ * G₀ * B) (-(Bᴴ * G₀ * portBlock XX 0 1)) (-(portBlock XX 1 0 * G₀ * B))
    (portBlock XX 1 1 + portBlock XX 1 0 * G₀ * portBlock XX 0 1)

/-- The separator matrices (as in `separatorMatrix`) at a two-port Schur matrix `𝕏`,
`𝕊 = twoPortScattering b E 𝕏`: `I, P, P𝕊, 𝕊*P, P𝕊P, P𝕊*P`. -/
def sepOf {W : ℕ} (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | .id => 1
  | .proj => nearProjection W
  | .projS => nearProjection W * twoPortScattering b E XX
  | .sStarProj => (twoPortScattering b E XX)ᴴ * nearProjection W
  | .projSProj => nearProjection W * twoPortScattering b E XX * nearProjection W
  | .projSStarProj => nearProjection W * (twoPortScattering b E XX)ᴴ * nearProjection W

/-- The mean contraction factor of a separator: `θ_*` (unconjugated), `θ̄_*` (conjugated). -/
def gapFactor (b E : ℝ) (s : ℂ) (σ : Separator) : ℂ :=
  thetaStar b E s ^ σ.unconj * conj (thetaStar b E s) ^ σ.conj

/-- The transported new separator `N σ(𝕏₊) N*` of one growth step. -/
def transportedSep {W : ℕ} (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (σ : Separator) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  freshTransport b E XX ω * sepOf b E (freshTwoPortSchur E XX ω) σ * (freshTransport b E XX ω)ᴴ

/-- **The complete-source gap lemma.** Fixed `b`, bulk `E`; uniform in the
deterministic Hermitian old two-port Schur matrix `𝕏` and over the four contracting separators. -/
structure CompleteSourceGapStatement : Prop where
  mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ∀ σ : Separator, σ.unconj + σ.conj = 1 →
          let X := nearSchur (boundaryZ b E) XX
          ‖matrixExpect (freshLaw W b) (transportedSep b E XX σ) -
              gapFactor b E s σ • sepOf b E XX σ‖ ≤
            C * (jetDistance0 b E X + jetDistance1 b E s X +
              conductanceOf (passiveTransmission b E X) / W + ((W : ℝ)⁻¹) ^ 2)
  fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ : Separator, σ.unconj + σ.conj = 1 → ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (transportedSep b E XX σ ω -
            matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)

end BlockBand.SourceProcess.CompleteSourceGap
