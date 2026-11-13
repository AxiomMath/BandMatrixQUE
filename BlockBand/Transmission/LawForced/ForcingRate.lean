module

public import BlockBand.Transmission.LawForced.Interface
public import BlockBand.Transmission.Bridge.AlmostSure

/-!
# The forcing rate: `4η d_* = 4πρ(E)`

The first deterministic input of `RatioDriftSummable`. The injection satisfies
`W⁻¹E(Tr C ∣ X) = d_* + O(…)` and adds `h(t)` only to the drift of `P₁`. With
`T₊ = L*TL + 4ηεC` (`AbsorbedWardIdentity` times `4η`) and `ε = κ/W²`, the injected trace per
step is `4ηκW⁻² · W d_* = 4ηd_*κ/W`; this file checks that the coefficient is the killing rate
`h = absorptionRate E κ = 4πρ(E)κ`.

* `etaZ_mul_dStar`: `η d_* = √(4−E²)/2` (`b < 1`, `E² ≤ 4`);
* **`four_eta_dStar`**: `4η d_* = 4πρ(E)`;
* **`absorptionRate_eq_injection`**: `h(s) = 4η d_* κ(s)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open BlockBand.Internal.Contracts.TransmissionPath

theorem etaZ_mul_dStar {b E : ℝ} (hb : b < 1) (hE : E ^ 2 ≤ 4) :
    etaZ b E * dStar b = Real.sqrt (4 - E ^ 2) / 2 := by
  have h1b : (1 - b) ≠ 0 := by linarith
  rw [etaZ, Bridge.boundaryZ_im b E hE, dStar]
  field_simp

/-- **`4η d_* = 4πρ(E)`.** -/
theorem four_eta_dStar {b E : ℝ} (hb : b < 1) (hE : E ^ 2 ≤ 4) :
    4 * etaZ b E * dStar b = 4 * Real.pi * Parameters.semicircleDensity E := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [mul_assoc, etaZ_mul_dStar hb hE, Parameters.semicircleDensity]
  field_simp

/-- **The killing rate is the injected trace rate.** -/
theorem absorptionRate_eq_injection {b E : ℝ} (hb : b < 1) (hE : E ^ 2 ≤ 4) (κ : ℝ → ℝ)
    (s : ℝ) : absorptionRate E κ s = 4 * etaZ b E * dStar b * κ s := by
  rw [four_eta_dStar hb hE, absorptionRate]

end BlockBand.Transmission.LawForced
