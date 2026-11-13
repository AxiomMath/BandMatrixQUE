module

public import BlockBand.Transmission.DualAtomless.Lifetime
public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# `RatioDualityPrinciple`, endpoint input: `1{ζ ≤ t}` versus `1{ζ < t}`

Letting the dual time `r ↑ t` gives the terminal term with `1{ζ < t}`, while the dual law of the
transmission (`dualTransform`) has `1{ζ ≤ t}`. They agree because the lifetime is atomless
(`DualAtomless.dualLifetimeAtomless_holds`, every `p ≥ 1`; for `p = 0`, `ζ = 0 < t`).
* **`ae_dualExtinction_ne`**: for every realization, a.s. `ζ ≠ t` (`t > 0`, all `p`).
* **`dualTransform_eq_lt`**: `dualTransform E κ t = E[exp(−∫_0^t h(t−s)R_s ds) 1{ζ < t}]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.DualAtomless
open scoped NNReal ENNReal

variable {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m} {P : Measure Ω}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}

/-- **The lifetime has no atom at a positive time**, for every realization and every `p`. -/
theorem ae_dualExtinction_ne (hD0 : 0 < D0) (hxy : IsRatioParameter x y)
    (hD : IsDualDeletionProcess P 𝓖 D0 x y N X Y) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, dualExtinction N ω ≠ ENNReal.ofReal t := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · filter_upwards [hD.start] with ω hω
    rw [DualAtomless.dualExtinction_eq_zero_of_level_zero hω.1]
    exact (ENNReal.ofReal_pos.2 ht).ne
  · rw [ae_iff]
    simp only [not_not]
    exact dualLifetimeAtomless_holds hD0 hp x y hxy Ω m 𝓖 P N X Y hD t.toNNReal

/-- **The dual transform with the strict indicator.** -/
theorem dualTransform_eq_lt (hD0 : 0 < D0) (hxy : IsRatioParameter x y)
    (hD : IsDualDeletionProcess P 𝓖 D0 x y N X Y) (E : ℝ) (κ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    dualTransform E κ t P N X Y =
      ∫ ω, (if dualExtinction N ω < ENNReal.ofReal t then
        Real.exp (-∫ s in (0 : ℝ)..t,
          absorptionRate E κ (t - s) * dualTotal (N s.toNNReal ω) (X s.toNNReal ω)
            (Y s.toNNReal ω))
      else 0) ∂P := by
  unfold dualTransform
  refine integral_congr_ae ?_
  filter_upwards [ae_dualExtinction_ne hD0 hxy hD ht] with ω hω
  simp only [hω.le_iff_lt]

end BlockBand.Transmission.LawDuality
