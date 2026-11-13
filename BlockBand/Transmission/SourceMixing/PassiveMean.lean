module

public import BlockBand.Transmission.SourceMixing.Weighted
public import BlockBand.Transmission.PassiveCovariance.FreshUWord

/-!
# The two-resolvent mean (layer form)

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X`, operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` (and
`L_w, K_d`) only, uniformly in `W ≥ W₀` and `X`.

The weighted expansion `weightedExpansion` specialized to the word `w = P₂(K̂𝒢)ᴴ`.

* `twoResolvent_weighted` (the instance `w = P₂(K̂𝒢)ᴴ`, `P₂` the port projector):
  `‖K̂·E[𝒢P₂(K̂𝒢)ᴴ] - K̂D⁻¹(P₂ + 𝒮[t₁, t₂])·E[(K̂𝒢)ᴴ]‖ ≤ C/W²`, `t_r = E⟨(𝒢P₂𝒢ᴴ)_{rr}⟩`.
  Its `(1,1)` block gives `E[LL*] = s₁ (KM)(KM)* + O(W⁻²)` with `s₁ = (1-2b)t₁ + bt₂`
  (`freshU_mean`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The port projector `P₂` as an insertion. -/
abbrev pTwo : LayerMat W := portProj

/-- Letters of `P₂(K̂𝒢)ᴴ`. -/
def wdStar : Fin 1 → Fin 4 := fun _ => 3

/-- Insertions of `P₂(K̂𝒢)ᴴ`. -/
def dStar2 : Fin (1 + 1) → LayerMat W := fun j => if j = 0 then pTwo else 1

theorem dStar2_zero : (dStar2 0 : LayerMat W) = pTwo := by unfold dStar2; simp

theorem dStar2_one : (dStar2 (Fin.succ 0) : LayerMat W) = 1 := by unfold dStar2; simp

theorem norm_dStar2_le (j : Fin (1 + 1)) : ‖(dStar2 j : LayerMat W)‖ ≤ 1 := by
  unfold dStar2
  split_ifs
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem wordVal_star (Kh G : LayerMat W) : wordVal Kh G wdStar dStar2 = pTwo * (Kh * G)ᴴ := by
  rw [wordVal_succ, wordVal_zero]
  show dStar2 0 * wLetter Kh G (wdStar 0) * dStar2 (Fin.succ 0) = _
  rw [dStar2_zero, dStar2_one, Matrix.mul_one]; rfl

theorem wordAlpha_star (Kh G : LayerMat W) (j : Fin 1) :
    wordAlpha Kh G 1 wdStar dStar2 j = pTwo * Gᴴ := by
  rw [Subsingleton.elim j 0]
  show dStar2 0 * wLeft Kh G (wdStar 0) = _
  rw [dStar2_zero]; rfl

theorem wordGamma_star (Kh G : LayerMat W) (j : Fin 1) :
    wordGamma Kh G 1 wdStar dStar2 j = (Kh * G)ᴴ := by
  rw [Subsingleton.elim j 0]
  show wRight Kh G (wdStar 0) * wordVal Kh G (fun j => wdStar j.succ) (fun j => dStar2 j.succ) = _
  rw [wordVal_zero]
  show wRight Kh G (wdStar 0) * dStar2 (Fin.succ 0) = _
  rw [dStar2_one, Matrix.mul_one]; rfl

/-- The two-resolvent weighted equation (`w = P₂(K̂𝒢)ᴴ`). -/
theorem twoResolvent_weighted (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ)) -
          kHat b E X * (dressed b E X)⁻¹ *
            (matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => pTwo * (kHat b E X * gRes b E X ω)ᴴ) +
              selfEnergy b
                (∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) 0 ∂layerLaw W b .oneBlockOnePort)
                (∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) 1 ∂layerLaw W b .oneBlockOnePort) *
              matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => (kHat b E X * gRes b E X ω)ᴴ))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₀, hC, h⟩ := weightedExpansion hA hb0 hb h1 h2 1 1
  refine ⟨C, W₀, hC, fun W hW X hX => ?_⟩
  have := h W hW X hX 1 le_rfl wdStar dStar2 norm_dStar2_le
  rw [Fin.sum_univ_one] at this
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wdStar dStar2) =
      fun ω => gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordVal_star]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) wdStar dStar2) =
      fun ω => pTwo * (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_star]
  have e3 : ∀ r : Fin 2, (fun ω => blkTr (gRes b E X ω *
      wordAlpha (kHat b E X) (gRes b E X ω) 1 wdStar dStar2 0) r) =
      fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r :=
    fun r => funext fun ω => by rw [wordAlpha_star]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 wdStar dStar2 0) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_star]
  rw [e1, e2, e3 0, e3 1, e4] at this
  exact this

end BlockBand.Transmission.SourceMixing
