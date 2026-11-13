module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneSTwoDenominatorTransfer

/-!
# Published spectral-lift adapter for theta-one `s₂`

This module performs the norm bookkeeping specific to the spectral-lift
matrices and the source observable.  All constants remain explicit and
independent of the matrix dimension.
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

/-- Uniform entry control becomes an operator-norm bound after the
unitary spectral lift. -/
theorem norm_spectralLift_le_of_forall {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (q : Fin N → ℂ)
    {L : ℝ} (hL : 0 ≤ L) (hq : ∀ i, ‖q i‖ ≤ L) :
    ‖spectralLift hF q‖ ≤ L := by
  rw [norm_spectralLift]
  exact (pi_norm_le_iff_of_nonneg hL).2 hq

/-- A uniform perturbation of a uniformly bounded boundary vector gives the
plus-branch operator-norm bound used in `s₂`. -/
theorem norm_spectralLift_le_of_uniform_close {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (q₀ q : Fin N → ℂ) {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ B) (hq : ∀ i, ‖q i - q₀ i‖ ≤ δ) :
    ‖spectralLift hF q‖ ≤ B + δ := by
  apply norm_spectralLift_le_of_forall hF q (add_nonneg hB hδ)
  intro i
  calc
    ‖q i‖ = ‖(q i - q₀ i) + q₀ i‖ := by
      congr 1
      ring
    _ ≤ ‖q i - q₀ i‖ + ‖q₀ i‖ := norm_add_le _ _
    _ ≤ δ + B := add_le_add (hq i) (hq₀ i)
    _ = B + δ := by ring

/-- Fully instantiated deterministic published adapter.  The matrices are the
spectral lifts, `J` is the source observable, and `A°` is the
theta-one regularization.  The hypotheses are scalar/norm conclusions
already supplied by the canonical-entry, density, pairing, and direct
ordinary-denominator packages; no certificate structure is introduced. -/
theorem sTwo_spectralLift_regularizedObservable_le
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {lambda : ℂ} (q₁ q₂ q₂minus : Fin N → ℂ)
    (J : LocalETHMatrix N) {L cΓ p d : ℝ}
    (hL : 0 ≤ L) (hcΓ : 0 < cΓ) (hp : 0 < p) (hd : 0 < d)
    (hq₁ : ∀ i, ‖q₁ i‖ ≤ L) (hq₂ : ∀ i, ‖q₂ i‖ ≤ L)
    (hq₂minus : ∀ i, ‖q₂minus i‖ ≤ L)
    (htrace₁ : cΓ ≤ |(NTrace (spectralLift hF q₁)).im|)
    (htrace₂ : cΓ ≤ |(NTrace (spectralLift hF q₂)).im|)
    (hJ : ‖J‖ ≤ 1)
    (hpair : p ≤ ‖NTrace (spectralLift hF q₁ * spectralLift hF q₂minus)‖)
    (hden : d ≤ ‖stabilityDenominator lambda
      (NTrace (spectralLift hF q₁ * spectralLift hF q₂))‖) :
    let M₁ := spectralLift hF q₁
    let M₂ := spectralLift hF q₂
    let M₂minus := spectralLift hF q₂minus
    let Areg := regularizedObservable 1 M₁ M₂minus J
    sTwo 1 lambda M₁ M₂ Areg ≤ Real.sqrt
      ((cΓ⁻¹ * L) * (1 + L * L / p) *
          (cΓ⁻¹ * L) * (1 + L * L / p) +
        ‖lambda‖ ^ 2 *
          ((L * (1 + L * L / p) * (cΓ⁻¹ * L)) *
            ((cΓ⁻¹ * L) * (1 + L * L / p) * L) / d)) := by
  dsimp only
  let M₁ := spectralLift hF q₁
  let M₂ := spectralLift hF q₂
  let M₂minus := spectralLift hF q₂minus
  let Areg := regularizedObservable 1 M₁ M₂minus J
  have hM₁ : ‖M₁‖ ≤ L := norm_spectralLift_le_of_forall hF q₁ hL hq₁
  have hM₂ : ‖M₂‖ ≤ L := norm_spectralLift_le_of_forall hF q₂ hL hq₂
  have hM₂m : ‖M₂minus‖ ≤ L :=
    norm_spectralLift_le_of_forall hF q₂minus hL hq₂minus
  have hΓ₁ : ‖gammaMatrix M₁‖ ≤ cΓ⁻¹ * L :=
    norm_gammaMatrix_le_of_traceImaginaryPart hN M₁ hcΓ htrace₁ hM₁
  have hΓ₂ : ‖gammaMatrix M₂‖ ≤ cΓ⁻¹ * L :=
    norm_gammaMatrix_le_of_traceImaginaryPart hN M₂ hcΓ htrace₂ hM₂
  have hA : ‖Areg‖ ≤ 1 + L * 1 * L / p :=
    norm_regularizedObservable_one_le hN M₁ M₂minus J hL zero_le_one hp
      hM₁ hM₂m hJ hpair
  have hA' : ‖Areg‖ ≤ 1 + L * L / p := by
    simpa [mul_assoc] using hA
  have hs2 := sTwo_one_le_sqrt_of_denominatorLower hN lambda M₁ M₂ Areg hd hden
  apply hs2.trans
  apply Real.sqrt_le_sqrt
  gcongr

end CEHNative.BlockBand.External.CEH
