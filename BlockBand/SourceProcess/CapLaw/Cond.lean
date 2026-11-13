module

public import BlockBand.SourceProcess.CapLaw.TightS

/-!
# The conditioned laws `ν_W[|A_W]` on the Borel cap event

`capY W` is the Borel cap event `{μ_W(s) ∈ capSet K h}` read on the joint sample `y`
(`physCapEventM`, a.e. equal to `physCapEvent`, `capPre_ae_eq`). `condLaw W` is
`lawW` conditioned on it.

* `condLaw_le`: if `P_W(A_W) ≥ c > 0` and `P_W(cap ∩ S) ≤ cθ`, then `P_W(S | A_W) ≤ θ`; the event
  `cap ∩ S` may use the non-Borel `physCapEvent`, as in the statements.
* `isProbabilityMeasure_condLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLaw

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSumProof
open scoped ENNReal

variable {W p K M : ℕ}

/-- The Borel cap event on the joint sample. -/
def capY (b E s h : ℝ) (K W p M : ℕ) : Set (SampledPath W p M × ℝ) :=
  {y | y.1.1 ∈ physCapEventM b E s h K W}

theorem measurableSet_capY (b E s h : ℝ) (K W p M : ℕ) : MeasurableSet (capY b E s h K W p M) :=
  (measurable_fst.comp measurable_fst) (measurableSet_physCapEventM b E s h K W)

/-- The law conditioned on the cap event. -/
def condLaw (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (K M W : ℕ) : Measure (SampledPath W p M × ℝ) :=
  (lawW b T q M W)[|capY b E s h K W p M]

theorem isProbabilityMeasure_lawW {b T : ℝ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) :
    IsProbabilityMeasure (lawW b T q M W) := by
  have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq ⌊(W : ℝ) * T⌋₊
  unfold lawW; infer_instance

theorem isProbabilityMeasure_condLaw {b E s T h : ℝ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    (h0 : lawW b T q M W (capY b E s h K W p M) ≠ 0) :
    IsProbabilityMeasure (condLaw b E s T h q K M W) := by
  have := isProbabilityMeasure_lawW (b := b) (T := T) (W := W) (M := M) hq
  exact cond_isProbabilityMeasure h0

theorem ofReal_inv_mul {c θ : ℝ} (hc : 0 < c) :
    (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal (c * θ) = ENNReal.ofReal θ := by
  rw [ENNReal.ofReal_mul hc.le, ← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hc)
    ENNReal.ofReal_ne_top, one_mul]

/-- **Conditioned bounds from bounds on the cap event.** -/
theorem condLaw_le {b E s T h : ℝ} {q : Fin p → ℝ → ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hq : ∀ i x, 0 ≤ q i x) {c θ : ℝ} (hc : 0 < c)
    (hcap : ENNReal.ofReal c ≤ lawW b T q M W (capY b E s h K W p M))
    {S : Set (SampledPath W p M × ℝ)}
    (hS : lawW b T q M W {y | y.1.1 ∈ physCapEvent b E s h K W ∧ y ∈ S} ≤ ENNReal.ofReal (c * θ)) :
    condLaw b E s T h q K M W S ≤ ENNReal.ofReal θ := by
  rw [condLaw, cond_apply (measurableSet_capY b E s h K W p M)]
  have e : capY b E s h K W p M ∩ S =ᵐ[lawW b T q M W]
      {y | y.1.1 ∈ physCapEvent b E s h K W ∧ y ∈ S} := by
    have := (capPre_ae_eq (W := W) (K := K) (M := M) hb hE1 hE2 s h hq ⌊(W : ℝ) * T⌋₊).symm
    exact this.inter (EventuallyEq.refl _ S)
  rw [measure_congr e]
  refine (mul_le_mul' (ENNReal.inv_le_inv.2 hcap) hS).trans (le_of_eq (ofReal_inv_mul hc))

end BlockBand.SourceProcess.CapLaw
