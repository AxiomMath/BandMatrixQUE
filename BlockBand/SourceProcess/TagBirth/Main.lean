module

public import BlockBand.SourceProcess.TagBirth.PathTrace
public import BlockBand.SourceProcess.TagBirth.Square

/-!
# Tag-birth values: assembly

The tag-birth value estimates used in the tagged convex-order theorem.

* `tagBirthValueEnergyUniform_of hF hδ hS`: the energy-uniform `TagBirthValueEnergyUniformContract`
  from `FreshPhysTraceLp`, the `T`-free `δ₀` moments `DeltaZeroLengthUniform` and
  `SqBirthMoments`;
* **`tagBirthValueEnergyUniform_holds hMT hGA hLp`**: the same from the contract hypotheses
  `MatchedTracesContract`, `GaussianAbsorptionContract` and `GaussianLpGradient` only;
* `tagBirthValue_of_uniform`: the fixed-`E` `TagBirthValueContract` by specialization to
  `κI = min(E+2, 2-E)`;
* **`tagBirthValue_holds hMT hGA hLp`**: the fixed-`E` contract from the contract hypotheses
  only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.TagBirth

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform2 BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.LengthUniform

theorem tagBirthValueEnergyUniform_of (hF : FreshPhysTraceLp) (hδ : DeltaZeroLengthUniform)
    (hS : SqBirthMoments) : TagBirthValueEnergyUniformContract :=
  ⟨tagBirthTrace_of hF hδ, tagBirthSquare_of hS⟩

/-- **`TagBirthValueEnergyUniformContract`** from the contract hypotheses only. -/
theorem tagBirthValueEnergyUniform_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    TagBirthValueEnergyUniformContract :=
  tagBirthValueEnergyUniform_of (freshPhysTraceLp_holds hGA hLp)
    (deltaZeroLengthUniform_holds hMT hGA hLp) (sqBirthMoments_of (fullSourceEstimates_holds hGA hLp) hGA)

theorem mem_bulkInterval_self {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) :=
  ⟨lt_min (by linarith) (by linarith),
    ⟨by linarith [min_le_left (E + 2) (2 - E)], by linarith [min_le_right (E + 2) (2 - E)]⟩⟩

/-- **The fixed-`E` contract** from the energy-uniform one (`κI = min(E+2, 2-E)`). -/
theorem tagBirthValue_of_uniform (h : TagBirthValueEnergyUniformContract) :
    TagBirthValueContract where
  trace b hb0 hb E h1 h2 ε T p hε hεT hp θ hθ := by
    obtain ⟨hκ, hE⟩ := mem_bulkInterval_self h1 h2
    obtain ⟨W₀, hW⟩ := h.trace b hb0 hb _ hκ ε T p hε hεT hp θ hθ
    exact ⟨W₀, fun W hW' k hk hkT => hW W hW' E hE k hk hkT⟩
  square b hb0 hb E h1 h2 ε T hε hεT := by
    obtain ⟨hκ, hE⟩ := mem_bulkInterval_self h1 h2
    obtain ⟨C, W₀, hW⟩ := h.square b hb0 hb _ hκ ε T hε hεT
    exact ⟨C, W₀, fun W hW' k hk hkT => hW W hW' E hE k hk hkT⟩

/-- **`TagBirthValueContract`** from the contract hypotheses only. -/
theorem tagBirthValue_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : TagBirthValueContract :=
  tagBirthValue_of_uniform (tagBirthValueEnergyUniform_holds hMT hGA hLp)

end BlockBand.SourceProcess.TagBirth
