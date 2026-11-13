module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHRectangularGridFinalPackaging
public import BlockBand.Internal.Contracts.Inputs

/-!
# CEH ETH: interface statements

The GUE family used for the eigenstate thermalization statement, and the two-resolvent positive-chain
laws restricted to pairs with regularization coefficient `θ(z₁, z₂) = 1`.

## Main definitions

* `gueLawFamily`: the GUE family `N, v ↦ law of √(N v) W`, `W ~ gueSourceLaw N` (`GUE_N(1/N)`), as a
  `LocalETHGUEFamily`, so that `gueLawFamily N (s/N)` is the law of `√s W`, the noise of
  `deformedHermitian (√s) F W = F + √s W` in `ExternalETH`.
* `TwoResolventPositiveChainLawThetaOne gue`: the two-resolvent law `CEHTwoResolventPositiveChainLaw`
  (CEH Theorem 4.2, (5.18)) restricted to pairs with `θ(z₁, z₂) = 1`, the domain of CEH Theorem 5.7.
* `FixedPointPositiveChainLawThetaOne gue`: the weaker bound form (4.4) on `θ = 1` pairs
  (`CEHFixedPointPositiveChainLaw` with `θ = 1`), the form CEH prints for the imaginary chain.

Each restricted law follows from the corresponding unrestricted law (`thetaOne_of_positiveChainLaw`,
`fixedPointThetaOne_of_fixedPointLaw`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open scoped Matrix Matrix.Norms.L2Operator ENNReal

/-- `√(N v) W` as a Hermitian matrix. -/
def scaledSource (N : ℕ) (v : ℝ) (W : BlockBand.External.CEH.SourceHermitian N) :
    HermitianMatrix (Fin N) :=
  ⟨((Real.sqrt ((N : ℝ) * v) : ℝ) : ℂ) • W.1, W.2.smul (Complex.conj_ofReal _)⟩

theorem measurable_scaledSource (N : ℕ) (v : ℝ) : Measurable (scaledSource N v) := by
  apply Measurable.subtype_mk
  fun_prop

theorem isProbabilityMeasure_gueSourceLaw (N : ℕ) :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.Inputs.gueSourceLaw N) := by
  have := BlockBand.External.Johansson.coordinateMeasure_probability N (1 / (N : NNReal))
  unfold BlockBand.Internal.Contracts.Inputs.gueSourceLaw
  infer_instance

/-- **The GUE family** `N, v ↦ law of √(N v) W`, `W ~ gueSourceLaw N`; at `v = s/N` this is the law
of the noise `√s W` of `ExternalETH`. -/
def gueLawFamily : LocalETHGUEFamily := fun N v =>
  ⟨(BlockBand.Internal.Contracts.Inputs.gueSourceLaw N).map (scaledSource N v), by
    have := isProbabilityMeasure_gueSourceLaw N
    infer_instance⟩

/-- **The two-resolvent positive-chain law on `θ = 1` pairs** (CEH Thm 4.2 (5.18) on the domain
of Thm 5.7): `CEHTwoResolventPositiveChainLaw` with the additional premise that the CEH cutoff
`θ(z₁, z₂) = regularizationCoefficient (√s) (M(z₁)) (M(z₂))ᴴ` equals `1`. An intermediate
statement; it is not a hypothesis of `externalETH_holds`. -/
def TwoResolventPositiveChainLawThetaOne (gue : LocalETHGUEFamily) : Prop :=
  ∀ κ C : ℝ, 0 ≤ κ → 0 < C →
  ∀ sLo sHi : ℝ, 0 < sLo → sLo ≤ sHi →
  ∀ r c K : ℝ, 0 < r → 0 < c → 0 < K →
  ∀ ε₀ ε₁ : ℝ, 0 < ε₀ → ε₀ ≤ ε₁ → ε₁ < 1 →
  ∀ ε D : ℝ, 0 < ε → 0 < D →
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
    ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
    ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
    ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
    ∀ z₁ z₂ : ℂ,
      z₁.re ∈ Ioo (E₀ - r) (E₀ + r) → z₂.re ∈ Ioo (E₀ - r) (E₀ + r) →
      (N : ℝ) ^ (ε₀ - 1) ≤ z₁.im → z₁.im ≤ (N : ℝ) ^ (ε₁ - 1) →
      (N : ℝ) ^ (ε₀ - 1) ≤ z₂.im → z₂.im ≤ (N : ℝ) ^ (ε₁ - 1) →
      regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1 →
    ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
          {G | CEHTwoResolventLawBad s ε Mf F.1 J z₁ z₂ G} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The unrestricted law implies the `θ = 1` law (sanity direction). -/
theorem thetaOne_of_positiveChainLaw {gue : LocalETHGUEFamily}
    (h : CEHTwoResolventPositiveChainLaw gue) : TwoResolventPositiveChainLawThetaOne gue := by
  intro κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK ε₀ ε₁ h0 h01 h1 ε D hε hD
  obtain ⟨N₀, hN₀⟩ := h κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK ε₀ ε₁ h0 h01 h1 ε D hε hD
  exact ⟨N₀, fun N hN s hs hs' F hF Mf hMf E₀ hreg z₁ z₂ h1r h2r h1l h1u h2l h2u _ J hJ hJn =>
    hN₀ N hN s hs hs' F hF Mf hMf E₀ hreg z₁ z₂ h1r h2r h1l h1u h2l h2u J hJ hJn⟩

/-- **The fixed-point positive-chain bound on `θ = 1` pairs** (CEH Thm 4.2, (4.4), the form CEH
prints for the `Im G A Im G` chain, (7.8)): `CEHFixedPointPositiveChainLaw`
(`⟨Im G₁ A° Im G₂ A°*⟩ ≺ 1` at deterministic pairs) with the additional premise
`θ(z₁, z₂) = 1`. Weaker than `TwoResolventPositiveChainLawThetaOne`. An intermediate statement;
it is not a hypothesis of `externalETH_holds`. -/
def FixedPointPositiveChainLawThetaOne (gue : LocalETHGUEFamily) : Prop :=
  ∀ κ C : ℝ, 0 ≤ κ → 0 < C →
  ∀ sLo sHi : ℝ, 0 < sLo → sLo ≤ sHi →
  ∀ r c K : ℝ, 0 < r → 0 < c → 0 < K →
  ∀ ε₀ ε₁ : ℝ, 0 < ε₀ → ε₀ ≤ ε₁ → ε₁ < 1 →
  ∀ ε D : ℝ, 0 < ε → 0 < D →
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
    ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
    ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
    ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
    ∀ z₁ z₂ : ℂ,
      z₁.re ∈ Ioo (E₀ - r) (E₀ + r) → z₂.re ∈ Ioo (E₀ - r) (E₀ + r) →
      (N : ℝ) ^ (ε₀ - 1) ≤ z₁.im → z₁.im ≤ (N : ℝ) ^ (ε₁ - 1) →
      (N : ℝ) ^ (ε₀ - 1) ≤ z₂.im → z₂.im ≤ (N : ℝ) ^ (ε₁ - 1) →
      regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1 →
    ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
          {G | CEHFixedPointPositiveChainBad s ε Mf F.1 J z₁ z₂ G} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The unrestricted fixed-point law implies the `θ = 1` one (sanity direction). -/
theorem fixedPointThetaOne_of_fixedPointLaw {gue : LocalETHGUEFamily}
    (h : CEHFixedPointPositiveChainLaw gue) : FixedPointPositiveChainLawThetaOne gue := by
  intro κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK ε₀ ε₁ h0 h01 h1 ε D hε hD
  obtain ⟨N₀, hN₀⟩ := h κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK ε₀ ε₁ h0 h01 h1 ε D hε hD
  exact ⟨N₀, fun N hN s hs hs' F hF Mf hMf E₀ hreg z₁ z₂ h1r h2r h1l h1u h2l h2u _ J hJ hJn =>
    hN₀ N hN s hs hs' F hF Mf hMf E₀ hreg z₁ z₂ h1r h2r h1l h1u h2l h2u J hJ hJn⟩

end BlockBand.Native.CEH.ETH

