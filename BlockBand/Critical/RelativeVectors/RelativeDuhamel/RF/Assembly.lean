module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.AsmBackward

/-!
# The reference flow statement

`referenceFlowStatement_holds (N r : ℕ) : ReferenceFlowStatement N r`, with no hypothesis. For
Hermitian `F`, `a < c`, `b₀ > 0`, `ℓ > 0`:

* `Ω_aux = (unitInterval × Torus N) × ℂ^{N×r}` with `P_aux = (Lebesgue ⊗ Haar) ⊗ CN`
  (`AuxSample`, `auxLaw`);
* `𝓜(ω, s, u, ((t, θ), G)) = P_θ'⁻¹ K P_θ'`, `Ξ(ω, s, u, ((t, θ), G)) = P_θ'⁻¹ √(1 - KKᴴ) G`, with
  `K = 1` if `s = u` and otherwise the realization at `t` of the kernel law of the path `ω`
  (`refM`, `refXi`, `rawKernel`, `realize`);
* joint measurability for `comap fst (pathSigma F a a c) ⊔ comap snd Borel(Ω_aux)`, for every
  `s, u` (`measurable_refM_joint`, `measurable_refXi_joint`);
* for every `ω` with `StrictMono (flowEigenvalue F a ω σ)` on `[a, c]` (equivalently
  `ω ∈ simpleRatSet F a c`): `IsReferenceFlow` (`isReferenceFlow_witness`) and the mass identity
  (`witness_mass`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.ReferenceFlow

variable {N r : ℕ}

/-- **The witness is a reference flow** (`IsReferenceFlow`) of every path
`ω ∈ simpleRatSet F a c`. -/
theorem isReferenceFlow_witness {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a < c) {b₀ : ℝ} (hb₀ : 0 < b₀) {ℓ : ℕ} (hℓ : 0 < ℓ) {ω : FlowSample N}
    (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) :
    BlockBand.Critical.RelativeVectors.IsReferenceFlow F a c b₀ ℓ ω (auxLaw N r)
      (refM F a c b₀ ℓ ω) (refXi F a c b₀ ℓ ω) where
  measurable s u := ⟨measurable_refM F a c b₀ ℓ ω s u, measurable_refXi F a c b₀ ℓ ω s u⟩
  initial s x := ⟨refM_self F a c b₀ ℓ ω s x, refXi_self F a c b₀ ℓ ω s x⟩
  contraction _ _ has hsu huc x v := refM_contracts hF hac b₀ ℓ has hsu huc ω x v
  covariance _ _ has hsu huc h hh hC w :=
    refM_covariance hF hac hb₀ hℓ has hsu huc ω h hh hC w
  phase_covariant s u _ _ _ α := refM_phase_covariant F a c b₀ ℓ ω s u α
  backward C f hf := witness_backward hF hac hb₀ hℓ hω C f hf

/-- **`ReferenceFlowStatement N r`**, with no hypothesis. -/
theorem referenceFlowStatement_holds (N r : ℕ) :
    BlockBand.Critical.RelativeVectors.ReferenceFlowStatement N r := by
  intro F a c b₀ ℓ hF hac hb₀ hℓ
  refine ⟨AuxSample N r, inferInstance, auxLaw N r, inferInstance, refM F a c b₀ ℓ,
    refXi F a c b₀ ℓ, fun s u => ⟨measurable_refM_joint F a c b₀ ℓ s u,
      measurable_refXi_joint F a c b₀ ℓ s u⟩, fun ω hmono => ?_⟩
  have hω := (strictMono_iff_mem_simpleRatSet hF hac.le ω).1 hmono
  exact ⟨isReferenceFlow_witness hF hac hb₀ hℓ hω, witness_mass hF hac hb₀ hℓ hω⟩

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
