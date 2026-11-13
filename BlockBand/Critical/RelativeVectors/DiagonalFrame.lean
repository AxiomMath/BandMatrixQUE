module

public import BlockBand.Critical.RelativeVectors.Diagonal
public import BlockBand.Critical.RelativeVectors.GammaShift

/-!
# The diagonal error in the frame

For `Δ_j = Σ_{|i-j| ≥ ℓ} (z_iz_i^* - I_r)/(N(λ_i - λ_j)²)`, `z_i = √N V^*u_i(H)`. Deterministic, at
one time `s ∈ [c - t, c]` with `c - s₀ ≤ c - t`. `diagonal_frame_le`: if the eigenvalues of `H`
increase strictly, satisfy the long-gap bound (clause 1 of `SpectralGoodEventContract`), the
middle line of the interval bound holds with bound `M‖p‖²` (the event of `relativeInterval_event`)
and the distant-label bound holds with `C_d‖p‖²` (the event of `relativeCoarse_event`), then for a
label `j` with `|λ_j - E| ≤ ρ ≤ r₀/8`:
`|p^*Δ_jp| ≤ [2NM/(c₁²ℓ²) + C(2(1 + log N)/c₁ + 4N(ρ + t)/(c₁²ℓ)) + C_d + 64/r₀²] ‖p‖²`,
`C = gammaShiftConst` (the third line of the interval bound is `frame_gamma_shift_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Finset Set Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.CoarseRelative

variable {N r : ℕ}

/-- **The diagonal error in the frame.** See the module docstring. -/
theorem diagonal_frame_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1) {s t : ℝ}
    (hs : s ∈ Icc (c - s₀) c) (hst : c - t ≤ s) (ht : 0 ≤ t) {H : Matrix (Fin N) (Fin N) ℂ}
    (hlam : StrictMono (freshEigenvalue H)) {c₁ ρ M Cd : ℝ} (hc₁ : 0 < c₁) (j : Fin N) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hρ : |freshEigenvalue H j - E| ≤ ρ) (hρ8 : ρ ≤ r₀ / 8)
    (hgap : ∀ i, ℓ ≤ labelDist i j →
      c₁ * labelDist i j / N ≤ |freshEigenvalue H i - freshEigenvalue H j|)
    (p : Fin r → ℂ)
    (hS1 : ∀ x y, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 →
      |∑ i ∈ univ.filter (fun i => freshEigenvalue H i ∈ Icc x y),
          (‖star p ⬝ᵥ frameArray V H i‖ ^ 2 -
            quadForm (freshGamma F s (freshEigenvalue H i)) (V *ᵥ p))| ≤ M * nsq p)
    (hS2 : ∑ i ∈ univ.filter (fun i => r₀ / 4 < |freshEigenvalue H i - E|),
      ‖star p ⬝ᵥ frameArray V H i‖ ^ 2 /
        ((N : ℝ) * (freshEigenvalue H i - freshEigenvalue H j) ^ 2) ≤ Cd * ∑ b, ‖p b‖ ^ 2) :
    |∑ i ∈ univ.filter (fun i => ℓ ≤ labelDist i j),
        (‖star p ⬝ᵥ frameArray V H i‖ ^ 2 - nsq p) /
          (N * (freshEigenvalue H i - freshEigenvalue H j) ^ 2)| ≤
      (2 * (M * (N / (c₁ ^ 2 * ℓ ^ 2))) +
        gammaShiftConst c r₀ s₀ v₀ * (2 * (1 + Real.log N) / c₁ + 4 * N * (ρ + t) / (c₁ ^ 2 * ℓ)) +
        Cd + 64 / r₀ ^ 2) * nsq p := by
  have hr₀ := hK.2.2.1
  have hCγ : 0 ≤ gammaShiftConst c r₀ s₀ v₀ := by
    have hκ'0 : 0 < c - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
    have hv0 := hK.2.2.2.2.2
    have hc0 := hK.1
    have hs0 := hK.2.2.2.1
    unfold gammaShiftConst
    positivity
  have hp0 := nsq_nonneg p
  have h := diagonal_le hlam (fun i => ‖star p ⬝ᵥ frameArray V H i‖ ^ 2)
    (fun i => quadForm (freshGamma F s (freshEigenvalue H i)) (V *ᵥ p)) (fun i => by positivity)
    hp0 hN hr₀ hc₁ hCγ ht j hℓ hρ hρ8 hgap hS1
    (fun i hi => frame_gamma_shift_le hN hK hC hV hs hst (by linarith) p) hS2
  refine h.trans (le_of_eq ?_)
  ring

end BlockBand.Critical.RelativeVectors
