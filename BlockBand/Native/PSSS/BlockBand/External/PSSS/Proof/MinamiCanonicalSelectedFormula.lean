module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCanonicalSchurMeasurability
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiAbsorbedCountFormula

/-!
# Canonical selected-block PSSS count formula

For a fixed exterior sample, the weighted regulated trace of the selected block equals a
Cauchy-weighted `(t, ξ)` integral of the eigenvalue count of the selected GUE block added to the
canonical background shifted by `t` times the canonical absorber.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The canonical background of the selected block, as a Hermitian matrix. -/
def publicFrozenCanonicalHermitian {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e eta : ℝ) : HermitianMatrix (Fin (dims j)) :=
  ⟨canonicalFrozenBackground
      (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
      (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext) e eta,
    canonicalFrozenBackground_isHermitian _ _ _ _ _ _⟩

/-- The canonical absorber of the selected block is positive semidefinite for `η > 0`. -/
theorem publicFrozenCanonicalAbsorber_posSemidef {k : ℕ}
    {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (canonicalFrozenAbsorber
      (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
      (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext)
      e eta).PosSemidef :=
  canonicalFrozenAbsorber_posSemidef _ _ _ _
    (frozenExteriorReindexed_isHermitian A₀ j Gext) e heta

/-- **Canonical weighted selected-block first-reduction formula.**  The
selected regulated trace equals the `(t,ξ)` integral of the auxiliary
selected-block multiplicity count, with the arbitrary finite weight retained
inside the count integrand. -/
theorem publicBlockRegulatedSelectedTrace_weighted_count_formula
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta)
    (w : ℝ≥0∞) (hw : w ≠ ⊤) :
    w * publicBlockRegulatedSelectedTrace A₀ j e eta
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) =
      ∫⁻ t : ℝ,
        ENNReal.ofReal (standardCauchyWeight t) *
          (∫⁻ xi : ℝ in Ioi 0,
            w *
              ((eigenCount
                  (addHermitian
                    (publicGUERealBackground
                      (publicFrozenCanonicalHermitian A₀ j Gext e eta)
                      (canonicalFrozenAbsorber
                        (frozenSelectedA A₀ j Gext)
                        (frozenSelectedB A₀ j Gext)
                        (frozenSelectedC A₀ j Gext)
                        (frozenSelectedD A₀ j Gext) e eta)
                      (publicFrozenCanonicalAbsorber_posSemidef
                        A₀ j Gext e heta) t)
                    (Gj ⟨j, by simp⟩))
                  (Ioo (-xi) xi) : ℝ≥0∞) *
                ENNReal.ofReal (poissonRadialWeight eta xi))) := by
  rw [publicBlockRegulatedSelectedTrace_split_eq_frozen]
  let Abg := publicFrozenCanonicalHermitian A₀ j Gext e eta
  let Q := canonicalFrozenAbsorber
    (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
    (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext) e eta
  have hQ : Q.PosSemidef :=
    publicFrozenCanonicalAbsorber_posSemidef A₀ j Gext e heta
  rw [frozenSelectedInverse_eq_canonicalSchur
    (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
    (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext)
    (frozenExteriorReindexed_isHermitian A₀ j Gext)
    (Gj ⟨j, by simp⟩).1 (Gj ⟨j, by simp⟩).2 e heta]
  rw [show (Gj ⟨j, by simp⟩).1 +
      canonicalFrozenBackground
        (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
        (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext) e eta =
      Abg.1 + (Gj ⟨j, by simp⟩).1 by
    dsimp [Abg, publicFrozenCanonicalHermitian]
    abel]
  change w * ENNReal.ofReal
      (publicGUEAbsorbedTrace Abg (Gj ⟨j, by simp⟩) Q eta) = _
  exact mul_publicGUEAbsorbedTrace_eq_lintegral_eigenCount_Ioo
    Abg (Gj ⟨j, by simp⟩) Q hQ heta w hw

end PSSSNative.BlockBand.PSSS
