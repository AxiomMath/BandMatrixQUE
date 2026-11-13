module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneMonolithicClosure

/-!
# Compact theta-one `s₂` API

The explicit polynomial bound is intentionally hidden behind a small
proposition so that downstream regular-window assembly does not normalize the
large base/stable expression merely to use the result.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH

/-- Structure-free compact interface saying that the theta-one CEH
parameter has a finite deterministic bound.  In eventual family theorems the
witness is chosen before the dimension quantifier, which expresses uniformity. -/
def HasSTwoBound {N : ℕ} (lambda : ℂ)
    (M₁ M₂ Areg : Matrix (Fin N) (Fin N) ℂ) (C : ℝ) : Prop :=
  sTwo 1 lambda M₁ M₂ Areg ≤ C

/-- Compact wrapper around the checked explicit spectral-lift estimate. -/
theorem hasSTwoBound_spectralLift_regularizedObservable
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {lambda : ℂ} (q₁ q₂ q₂minus : Fin N → ℂ)
    (J : LocalETHMatrix N) {L cΓ p d : ℝ}
    (hL : 0 ≤ L) (hcΓ : 0 < cΓ) (hp : 0 < p) (hd : 0 < d)
    (hq₁ : ∀ i, ‖q₁ i‖ ≤ L) (hq₂ : ∀ i, ‖q₂ i‖ ≤ L)
    (hq₂minus : ∀ i, ‖q₂minus i‖ ≤ L)
    (htrace₁ : cΓ ≤ |(NTrace (spectralLift hF q₁)).im|)
    (htrace₂ : cΓ ≤ |(NTrace (spectralLift hF q₂)).im|)
    (hJ : ‖J‖ ≤ 1)
    (hpair : p ≤ ‖NTrace
      (spectralLift hF q₁ * spectralLift hF q₂minus)‖)
    (hden : d ≤ ‖stabilityDenominator lambda
      (NTrace (spectralLift hF q₁ * spectralLift hF q₂))‖) :
    HasSTwoBound lambda (spectralLift hF q₁) (spectralLift hF q₂)
      (regularizedObservable 1 (spectralLift hF q₁)
        (spectralLift hF q₂minus) J)
      (Real.sqrt (thetaOneSTwoBound ‖lambda‖ L cΓ p d)) := by
  unfold HasSTwoBound thetaOneSTwoBound
  exact sTwo_spectralLift_regularizedObservable_le
    (L := L) (cΓ := cΓ) (p := p) (d := d)
    hN hF q₁ q₂ q₂minus J hL hcΓ hp hd hq₁ hq₂ hq₂minus
    htrace₁ htrace₂ hJ hpair hden

/-- Compact conjugate-transpose specialization used by the published source
pair.  This declaration is deliberately separated from the explicit bound. -/
theorem hasSTwoBound_spectralLift_conjTranspose
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {lambda : ℂ} (q₁ q₂ : Fin N → ℂ) (J : LocalETHMatrix N)
    {L cΓ p d : ℝ} (hL : 0 ≤ L) (hcΓ : 0 < cΓ) (hp : 0 < p) (hd : 0 < d)
    (hq₁ : ∀ i, ‖q₁ i‖ ≤ L) (hq₂ : ∀ i, ‖q₂ i‖ ≤ L)
    (htrace₁ : cΓ ≤ |(NTrace (spectralLift hF q₁)).im|)
    (htrace₂ : cΓ ≤ |(NTrace (spectralLift hF q₂)).im|)
    (hJ : ‖J‖ ≤ 1)
    (hpair : p ≤ ‖NTrace
      (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)‖)
    (hden : d ≤ ‖stabilityDenominator lambda
      (NTrace (spectralLift hF q₁ * spectralLift hF q₂))‖) :
    HasSTwoBound lambda (spectralLift hF q₁) (spectralLift hF q₂)
      (regularizedObservable 1 (spectralLift hF q₁)
        (spectralLift hF q₂)ᴴ J)
      (Real.sqrt (thetaOneSTwoBound ‖lambda‖ L cΓ p d)) := by
  have hq₂star (i : Fin N) : ‖star (q₂ i)‖ ≤ L := by
    rw [norm_star]
    exact hq₂ i
  have hpair' : p ≤ ‖NTrace
      (spectralLift hF q₁ * spectralLift hF (fun i => star (q₂ i)))‖ := by
    rw [← spectralLift_conjTranspose]
    exact hpair
  rw [spectralLift_conjTranspose]
  exact hasSTwoBound_spectralLift_regularizedObservable hN hF
    q₁ q₂ (fun i => star (q₂ i)) J hL hcΓ hp hd hq₁ hq₂ hq₂star
    htrace₁ htrace₂ hJ hpair' hden

/-- Compact joint endpoint: the exact cutoff is one and the
theta-one regularized observable satisfies the explicit dimension-free `s₂`
bound. -/
theorem thetaOneCompactClosure
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) (q₁ q₂ : Fin N → ℂ) (J : LocalETHMatrix N)
    {L cΓ p d : ℝ} (hL : 0 ≤ L) (hcΓ : 0 < cΓ) (hp : 0 < p) (hd : 0 < d)
    (hq₁ : ∀ i, ‖q₁ i‖ ≤ L) (hq₂ : ∀ i, ‖q₂ i‖ ≤ L)
    (htrace₁ : cΓ ≤ |(NTrace (spectralLift hF q₁)).im|)
    (htrace₂ : cΓ ≤ |(NTrace (spectralLift hF q₂)).im|)
    (hJ : ‖J‖ ≤ 1)
    (hpair : 1 / 2 <
      (s * NTrace (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)).re)
    (hpairNorm : p ≤ ‖NTrace
      (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)‖)
    (hden : d ≤ ‖stabilityDenominator (Real.sqrt s : ℂ)
      (NTrace (spectralLift hF q₁ * spectralLift hF q₂))‖) :
    regularizationCoefficient (Real.sqrt s : ℂ)
        (spectralLift hF q₁) (spectralLift hF q₂)ᴴ = 1 ∧
      HasSTwoBound (Real.sqrt s : ℂ)
        (spectralLift hF q₁) (spectralLift hF q₂)
        (regularizedObservable 1 (spectralLift hF q₁)
          (spectralLift hF q₂)ᴴ J)
        (Real.sqrt (thetaOneSTwoBound
          ‖(Real.sqrt s : ℂ)‖ L cΓ p d)) := by
  constructor
  · exact regularizationCoefficient_eq_one_of_scaled_pairing
      (Real.sq_sqrt hs.le) _ _ hpair
  · exact hasSTwoBound_spectralLift_conjTranspose hN hF q₁ q₂ J
      hL hcΓ hp hd hq₁ hq₂ htrace₁ htrace₂ hJ hpairNorm hden

end CEHNative.BlockBand.External.CEH
