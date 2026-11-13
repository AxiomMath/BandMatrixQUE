module

public import BlockBand.Transmission.PassiveCovariance.Reduction
public import BlockBand.Transmission.PassiveLayer.Consistency

/-!
# From the passive bounds to the inputs of the passive covariance

`PassiveBoundsStatement` gives the `L²` fluctuation bound `PassiveFluctuationL2`; together with
the near-domain bound it gives `PassiveCovarianceContract`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.Transmission.PassiveCovariance

open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveLayer

/-- `PassiveBoundsStatement → PassiveFluctuationL2` (the `p = 2`, `w = z_∂` case of `bilinear`). -/
theorem passiveFluctuationL2_of_passiveBounds (h : PassiveBoundsStatement) :
    PassiveFluctuationL2 := by
  intro b hb0 hb E h1 h2
  obtain ⟨C, W₀, hC⟩ := oneStepFluctuation_of_passiveBounds h b hb0 hb E h1 h2 2 one_le_two
  refine ⟨C, W₀, fun W hW X hX u v => ?_⟩
  have := (hC W hW X hX u v).1
  rwa [ENNReal.ofReal_ofNat] at this

/-- `PassiveCovarianceContract` from `PassiveBoundsStatement` and the near-domain bound. -/
theorem passiveCovariance_of_domain_of_passiveBounds (hdom : PassiveCovarianceOnDomain)
    (h : PassiveBoundsStatement) : PassiveCovarianceContract :=
  passiveCovariance_of_domain hdom (passiveFluctuationL2_of_passiveBounds h)

end BlockBand.Transmission.PassiveCovariance
