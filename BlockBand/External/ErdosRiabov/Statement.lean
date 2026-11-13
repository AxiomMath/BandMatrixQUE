module

public import BlockBand.External.ErdosRiabov.SourceObservables

/-!
# The single-resolvent local law of Erdős–Riabov, as a hypothesis

This file states the case `k = 1` of Erdős–Riabov Theorem 3.3 (isotropic and averaged local laws
for one resolvent) as the proposition `SourceContract`. It is used as an explicit hypothesis (a
cited result of the paper). The deterministic bounds (3.18) on `M` are proved separately; nothing is stated
about chains of `k ≥ 2` resolvents.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.External.ErdosRiabov

open MeasureTheory

universe u

/-- The isotropic and averaged local laws for one resolvent (ER Theorem 3.3, `k = 1`): for
fixed model parameters and `ξ, D > 0` there is `N₀` such that for `N ≥ N₀`, every law with these
parameters, every admissible control family and every `z` in the spectral domain, the isotropic
bad event (for each pair of deterministic vectors) and the averaged bad event (for each
deterministic diagonal observable) have probability at most `N^{-D}`. -/
def SourceContract : Prop :=
  ∀ (p : ModelParameters) (ξ D : ℝ), 0 < ξ → 0 < D →
    ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ (N W : ℕ), N0 ≤ N → ∀ (L : NativeLaw.{u} p N W),
        ∀ Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ,
          AdmissibleControl p N W L.S Upsilon →
          ∀ z : ℂ, SpectralDomain p N z →
            (∀ u v : Vector N,
              L.P (isotropicBad L Upsilon z u v ξ) ≤
                ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
            (∀ A : Fin N → ℂ,
              L.P (averagedBad L z A ξ) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)))

/-- The bounds of `SourceContract`, with the same quantifiers. -/
theorem source_k1_bounds (hER : SourceContract.{u}) (p : ModelParameters)
    (ξ D : ℝ) (hξ : 0 < ξ) (hD : 0 < D) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ (N W : ℕ), N0 ≤ N → ∀ (L : NativeLaw.{u} p N W),
        ∀ Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ,
          AdmissibleControl p N W L.S Upsilon →
          ∀ z : ℂ, SpectralDomain p N z →
            (∀ u v : Vector N,
              L.P (isotropicBad L Upsilon z u v ξ) ≤
                ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
            (∀ A : Fin N → ℂ,
              L.P (averagedBad L z A ξ) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :=
  hER p ξ D hξ hD

end BlockBand.External.ErdosRiabov
