module

public import BlockBand.Native.CEH.ETH.Extraction
public import BlockBand.Native.CEH.Deterministic.Fields

/-!
# The CEH eigenstate thermalization estimate: adapter to `Inputs.ExternalETH`

The CEH local eigenstate thermalization (ETH) input `LocalETHRegularWindowBound` gives the external ETH statement
`Inputs.ExternalETH`, by translating each hypothesis:

* deformation: `(√s)⁻¹ ‖F‖ ≤ C N^A` gives `LocalETHDeformationBound (max A 0) (max C 1) s F.1`
  (`N ≥ 1`, `s > 0`);
* window: `RegularWindow M E₀ r K` gives `LocalETHRegularBoundaryWindow s M.matrix E₀ r (1/K) K`
  with `Mb' := deriv Mb` (differentiability on the open interval gives the entrywise derivative);
* spacing: `TypicalSpacing M` gives `etaF := spacing.eta` with `IsLocalETHTypicalSpacing`;
* law: `gueSourceLaw N (W-event) ≤ gueLawFamily N (s/N) (G-event)` by `Measure.le_map_apply`.

`externalETH_of_thetaOneLaw` composes this with the extraction from the two-resolvent
positive-chain law `TwoResolventPositiveChainLawThetaOne`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Set Filter Topology
open CEHNative.BlockBand
open scoped Matrix Matrix.Norms.L2Operator ENNReal

/-- The relative matrix `Γ` of `External.CEH` is `localETHGamma` (`⟨Im M⟩ = Im ⟨M⟩`). -/
theorem gammaMatrix_eq_localETHGamma {N : ℕ} (M : BlockBand.External.CEH.SourceMatrix N) :
    BlockBand.External.CEH.gammaMatrix M = localETHGamma M := by
  unfold BlockBand.External.CEH.gammaMatrix localETHGamma
  congr 2
  unfold BlockBand.External.CEH.normalizedTrace BlockBand.External.CEH.imaginaryPart
    Conventions.normalizedTrace
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, smul_eq_mul]
  have hN : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hN]
  apply Complex.ext <;> simp
  left
  ring

/-- An `External.CEH.MDEBranch` at `λ = √s` is an MDE branch at `s` (`s ≥ 0`). -/
theorem isLocalETHMDEBranch_of_mdeBranch {N : ℕ} {s : ℝ} (hs : 0 ≤ s)
    {F : BlockBand.External.CEH.SourceHermitian N}
    (M : BlockBand.External.CEH.MDEBranch (Real.sqrt s) F) :
    IsLocalETHMDEBranch s F.1 M.matrix := by
  intro z hz
  have h := BlockBand.Native.CEH.isMDESolution_iff_localETH.1 (M.solution z hz)
  rwa [Real.sq_sqrt hs] at h

/-- An `External.CEH.TypicalSpacing` is a typical-spacing function. -/
theorem isLocalETHTypicalSpacing_of_typicalSpacing {N : ℕ} {s : ℝ}
    {F : BlockBand.External.CEH.SourceHermitian N}
    {M : BlockBand.External.CEH.MDEBranch (Real.sqrt s) F}
    (spacing : BlockBand.External.CEH.TypicalSpacing M) (x : ℝ) :
    IsLocalETHTypicalSpacing M.matrix x (spacing.eta x) :=
  ⟨spacing.positive x, spacing.equation x⟩

/-- Entrywise derivative from the matrix derivative. -/
theorem hasLocalETHMatrixDerivAt_of_differentiableAt {N : ℕ}
    {Mb : ℝ → BlockBand.External.CEH.SourceMatrix N} {x : ℝ}
    (hd : DifferentiableAt ℝ Mb x) : HasLocalETHMatrixDerivAt Mb (deriv Mb x) x := by
  intro a b
  let L : BlockBand.External.CEH.SourceMatrix N →L[ℝ] ℂ :=
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := (continuous_apply b).comp (continuous_apply a) }
  exact L.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt

/-- `RegularWindow M E₀ r K` is a regular boundary window with `c = 1/K`. -/
theorem localETHRegularBoundaryWindow_of_regularWindow {N : ℕ} {s : ℝ}
    {F : BlockBand.External.CEH.SourceHermitian N}
    {M : BlockBand.External.CEH.MDEBranch (Real.sqrt s) F} {E₀ r K : ℝ}
    (h : BlockBand.Internal.Contracts.Inputs.RegularWindow M E₀ r K) :
    LocalETHRegularBoundaryWindow s M.matrix E₀ r (1 / K) K := by
  obtain ⟨Mb, hlim, hdiff, hbd⟩ := h
  refine ⟨⟨Mb, deriv Mb, fun x hx => ?_⟩⟩
  obtain ⟨h1, h2, h3, h4⟩ := hbd x hx
  have hd : DifferentiableAt ℝ Mb x := hdiff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  exact ⟨hlim x hx, hasLocalETHMatrixDerivAt_of_differentiableAt hd, h1, h3, h2, h4⟩

/-- The deformation hypothesis of `ExternalETH` gives the one with `κ = max A 0` and
constant `max C 1`, for `N ≥ 1` and `s > 0`.
-/
theorem localETHDeformationBound_of_external {N : ℕ} (hN : 1 ≤ N) {A C s : ℝ} (hs : 0 < s)
    (F : BlockBand.External.CEH.SourceHermitian N)
    (hF : (Real.sqrt s)⁻¹ * ‖F.1‖ ≤ C * (N : ℝ) ^ A) :
    LocalETHDeformationBound (max A 0) (max C 1) s F.1 := by
  unfold LocalETHDeformationBound
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hF' : ‖F.1‖ ≤ C * (N : ℝ) ^ A * Real.sqrt s := by
    rw [inv_mul_le_iff₀ hsq] at hF
    linarith
  have hpow : (N : ℝ) ^ A ≤ (N : ℝ) ^ (max A 0) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have hpos : 0 ≤ (N : ℝ) ^ A := by positivity
  have hC : C * (N : ℝ) ^ A ≤ max C 1 * (N : ℝ) ^ (max A 0) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 1) hpos).trans
      (mul_le_mul_of_nonneg_left hpow (by positivity))
  exact hF'.trans (mul_le_mul_of_nonneg_right hC hsq.le)

/-- `scaledSource N (s/N) W = √s W` as a matrix, for `N ≥ 1`. -/
theorem scaledSource_val_eq {N : ℕ} (hN : 1 ≤ N) (s : ℝ)
    (W : BlockBand.External.CEH.SourceHermitian N) :
    (scaledSource N (s / N) W).1 = ((Real.sqrt s : ℝ) : ℂ) • W.1 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [scaledSource]
  rw [mul_div_cancel₀ s hN0]

/-- **Bad-event inclusion.** For `N ≥ 1`, the bad event `Inputs.ethBadEvent` is contained in the
preimage under `W ↦ √(N (s/N)) W` of the bad event `LocalETHWindowBad`, with
`etaF := spacing.eta`. The selection is one orthonormal eigenfamily of `F + √s W`. -/
theorem ethBadEvent_subset_preimage {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    {F : BlockBand.External.CEH.SourceHermitian N}
    (M : BlockBand.External.CEH.MDEBranch (Real.sqrt s) F)
    (spacing : BlockBand.External.CEH.TypicalSpacing M)
    (sel : BlockBand.External.CEH.EigenpairSelection N) (E₀ β ξ ε : ℝ)
    (J : BlockBand.External.CEH.SourceMatrix N) :
    BlockBand.Internal.Contracts.Inputs.ethBadEvent M spacing sel E₀ β ξ ε J ⊆
      scaledSource N (s / N) ⁻¹'
        {G | LocalETHWindowBad M.matrix spacing.eta ξ β ε E₀ F.1 J G} := by
  intro W hW
  obtain ⟨i, j, hi, hj, hlt⟩ := hW
  set H := BlockBand.External.CEH.deformedHermitian (Real.sqrt s) F W with hHdef
  have hH : H.1 = F.1 + (scaledSource N (s / N) W).1 := by
    rw [scaledSource_val_eq hN]
    rfl
  have hwin : ∀ k, sel.eigenvalue H k ∈
      Icc (E₀ - (N : ℝ) ^ (-1 + β)) (E₀ + (N : ℝ) ^ (-1 + β)) →
      |sel.eigenvalue H k - E₀| ≤ (N : ℝ) ^ (β - 1) := by
    intro k hk
    rw [show β - 1 = -1 + β by ring, abs_le]
    constructor <;> linarith [hk.1, hk.2]
  refine ⟨sel.eigenvalue H, sel.eigenvector H, ⟨sel.orthonormal H, ?_⟩, i, j, hwin i hi,
    hwin j hj, ?_⟩
  · intro k
    rw [← hH]
    exact sel.eigen_equation H k
  · have hexp : (N : ℝ) ^ (-(1 : ℝ) / 2) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      congr 1; ring
    rw [hexp] at hlt
    refine lt_of_lt_of_eq hlt ?_
    unfold localETHError localETHCenter
    rw [← gammaMatrix_eq_localETHGamma]
    rfl

/-- **E2: adapter.** The published regular-window bound at the GUE family `gueLawFamily`
implies the `Inputs.ExternalETH`, with `β₀:= 1/2`.
-/
theorem externalETH_of_localETHRegularWindowBound
    (h : LocalETHRegularWindowBound gueLawFamily) :
    BlockBand.Internal.Contracts.Inputs.ExternalETH := by
  intro A C sLo sHi r K hsLo hsHi hr hK
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro β ξ hξ hξβ hβ ε D hε hD
  obtain ⟨N₀, hN₀1, hN₀⟩ := h (max A 0) (max C 1) (le_max_right _ _)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) sLo sHi hsLo hsHi r (1 / K) K hr
    (by positivity) hK β (by linarith) hβ.le ξ hξ hξβ ε D hε hD
  refine ⟨N₀, fun N hN s hs F hF M E₀ hreg spacing sel J hJh hJ => ?_⟩
  have hN1 : 1 ≤ N := hN₀1.trans hN
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs.1
  have key := hN₀ N hN s hs.1 hs.2 F (localETHDeformationBound_of_external hN1 hs0 F hF)
    M.matrix (isLocalETHMDEBranch_of_mdeBranch hs0.le M) spacing.eta
    (isLocalETHTypicalSpacing_of_typicalSpacing spacing) E₀
    (localETHRegularBoundaryWindow_of_regularWindow hreg) J hJh hJ
  refine le_trans ?_ key
  change BlockBand.Internal.Contracts.Inputs.gueSourceLaw N _ ≤
    ((BlockBand.Internal.Contracts.Inputs.gueSourceLaw N).map (scaledSource N (s / N))) _
  exact (measure_mono (ethBadEvent_subset_preimage hN1 M spacing sel E₀ β ξ ε J)).trans
    (Measure.le_map_apply (measurable_scaledSource N (s / N)).aemeasurable _)

/-- The `θ = 1` two-resolvent law at the GUE family implies `Inputs.ExternalETH`. -/
theorem externalETH_of_thetaOneLaw (hlaw : TwoResolventPositiveChainLawThetaOne gueLawFamily) :
    BlockBand.Internal.Contracts.Inputs.ExternalETH :=
  externalETH_of_localETHRegularWindowBound
    (localETHRegularWindowBound_of_thetaOneLaw gueLawFamily hlaw)

end BlockBand.Native.CEH.ETH
