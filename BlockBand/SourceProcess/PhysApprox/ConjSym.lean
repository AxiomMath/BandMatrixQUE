module

public import BlockBand.SourceProcess.PhysApprox.ConjSymCfc
public import BlockBand.SourceProcess.PhysApprox.Assembly

/-!
# The output leakage from the input leakage

This file proves `TargetT4`: the input leakage `TagChannelLeakage` (L) implies the output
leakage `TagChannelLeakageOut` (Lo). Measure `growthPathLaw W b`. For Hermitian blocks (a.s.) and
`h² < 1`, the (Lo) integrand at `ω` equals the (L) integrand at the entrywise-conjugated path `ω̄`
(`leakIn_conjPath`: `A_-(ω̄) = conj(ΠᴴΠ)`, `Y(ω̄) = conj(𝕊Y𝕊ᴴ)`, `Re Tr conj = Re Tr`), and
`growthPathLaw` is conjugation invariant (`lintegral_conjPath`). So the two lower integrals are
equal for every `W`, every `h ∈ (0, 1)` and all lengths, and (L) gives (Lo) with the same `h`, `W`
filters.

* `tagChannelLeakageOut_of : TagChannelLeakage → TagChannelLeakageOut`;
* `t4 : TargetT4`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open scoped ENNReal

variable {W : ℕ}

theorem farEmbed_matConj (X : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed (matConj X) = matConj (farEmbed X) := by
  ext x y
  simp only [farEmbed, of_apply, matConj_apply]
  split_ifs <;> simp

/-- **Pathwise conjugation identity**: the (L) trace at `ω̄` is the (Lo) trace at `ω`. -/
theorem leakIn_conjPath (b E h : ℝ) (hh : h ^ 2 < 1) (ns nT k : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    (farEmbed (omittedProj b E h W ns (conjPath ω)) *
        tagResponse b E W nT k (conjPath ω)).trace.re =
      (farEmbed ((closingPairing b E h W ns ω)ᴴ * closingPairing b E h W ns ω) *
        scatteringMatrix b E W nT ω * tagResponse b E W nT k ω *
        (scatteringMatrix b E W nT ω)ᴴ).trace.re := by
  rw [omittedProj_conjPath b E h hh ns ω hA, tagResponse_conjPath b E nT k ω hA,
    farEmbed_matConj, ← matConj_mul, re_trace_matConj]
  simp only [Matrix.mul_assoc]

/-- The (L) integrand. -/
def leakInIntegrand (b E s T τ h : ℝ) (W : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ENNReal.ofReal ((farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) *
    tagResponse b E W ⌊(W : ℝ) * T⌋₊ ⌊(W : ℝ) * τ⌋₊ ω).trace.re / W)

/-- **(L) ⇒ (Lo).** -/
theorem tagChannelLeakageOut_of (hL : TagChannelLeakage) : TagChannelLeakageOut := by
  intro b hb0 hb1 E hE1 hE2 s τ T hs hsτ hτT ε hε
  have hlt : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  filter_upwards [hL b hb0 hb1 E hE1 hE2 s τ T hs hsτ hτT ε hε, hlt, self_mem_nhdsWithin]
    with h hh hh1 hh0
  filter_upwards [hh] with W hW
  have hh2 : h ^ 2 < 1 := by
    have h0 : (0 : ℝ) < h := hh0
    nlinarith
  have hW' : ∫⁻ ω, leakInIntegrand b E s T τ h W ω ∂growthPathLaw W b ≤ ENNReal.ofReal ε := hW
  refine le_trans (le_of_eq ?_) hW'
  rw [← lintegral_conjPath b (leakInIntegrand b E s T τ h W)]
  refine lintegral_congr_ae ?_
  filter_upwards [BlockBand.Transmission.Bridge.ae_growth_isHermitian W b] with ω hA
  rw [leakInIntegrand, leakIn_conjPath b E h hh2 _ _ _ ω hA]

/-- **`TargetT4`.** -/
theorem t4 : TargetT4 := tagChannelLeakageOut_of

end BlockBand.SourceProcess.PhysApprox
