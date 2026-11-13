module

public import BlockBand.SourceProcess.CompleteSourceGap.GapIdentity

/-!
# The one-port content of the complete-source gap lemma

By the exact identity `N P𝕊₊ N* = ι (L𝒢₂₁K) ι* 𝕊` (`transportedSep_projS`) the
unprojected letters `P𝕊`, `𝕊*P` are controlled by the **one-port gap letter**
`Γ = L𝒢₂₁K = K𝒢₁₂𝒢₂₁K = -∂_wΔ|_{w=z}` (`gapLetter`) of one fresh layer at the passive input
`X = nearSchur z 𝕏`. The differentiated weighted mean `∂_wE_jΔ = -θ_*I + O_op(δ₀ + δ₁ + g/W + W⁻²)`
(from `Ω' = -θ_*`, `∂_w(KM(w)K) = Ω'KM(w)²K`, the passive scalar trace reduction and Cauchy's
formula) and its fluctuation (differentiating the bounded weighted words and applying Gaussian
Poincaré) are exactly `GapLetterMean` and `GapLetterFluctuation`.

**Proof outline for `GapLetterMean`** (no `w`-derivative needed). Write `K̂ = diag(K, 1)`,
`V_L = [[A, B], [B*, 0]]`, `Λ = diag((z+E), (1-z))`; then `𝒢K̂ = 1 + 𝒢(Λ - V_L)` and
`Γ = (K̂𝒢P₂𝒢K̂)₁₁ = (z+E)(K̂𝒢P₂𝒢)₁₁ - (K̂𝒢P₂𝒢V_L)₁₁`. The first word is the `weightedExpansion`
instance `w = P₂𝒢` (its scalar `θ = σ(E𝒢P₂𝒢)` solves `θ(1 - (c + b²v²)⟨M²⟩) = bv²`, i.e.
`(1-(c+b²v²)A)Ω' = -bv²` with `Ω' = -θ`, identified with `θ_*` on the jet domain). The second is a
right Gaussian integration by parts (`replica_right`, `meanSD_right_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- **The mean of the one-port gap letter** (`∂_wEΔ = -θ_*I + O`). -/
def GapLetterMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef →
        ‖matrixExpect (freshLaw W b) (gapLetter b E X) -
            thetaStar b E s • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
            ((W : ℝ)⁻¹) ^ 2)

/-- **Centered bilinear entries of the one-port gap letter** are `O(W^{-1/2})` in `L^p`. -/
def GapLetterFluctuation : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ x y : Fin W → ℂ,
        eLpNorm (fun ω => bilinear x (gapLetter b E X ω -
            matrixExpect (freshLaw W b) (gapLetter b E X)) y) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm x * vecNorm y)

end BlockBand.SourceProcess.CompleteSourceGap
