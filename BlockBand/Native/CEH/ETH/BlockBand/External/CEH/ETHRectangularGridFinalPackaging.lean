module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHCanonicalHeightRectangle
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHRectangularGridTailAbsorption
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHRegularizedObservableAdapter
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneRegularWindowWitness
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventLemma56Positive

/-!
# Final rectangular-grid packaging of the CEH ETH extraction

This module proves the deterministic part of the CEH ETH extraction. Its endpoint
`localETHRegularWindowBound_of_fixedPointPositiveChainLaw` derives the full
regular-window ETH statement `LocalETHRegularWindowBound gue` (hence
`LocalETHInput gue`) from a single hypothesis, `CEHFixedPointPositiveChainLaw
gue`: the order-one stochastic-domination bound for the positive
two-resolvent chain `⟨Im G(z₁) A° Im G(z₂) A°*⟩` at deterministic spectral
parameters, with the CEH regularized observable `A°` formed at those
parameters.  That law is stated below as a `Prop`; it is a hypothesis here.

A second, stronger endpoint,
`localETHRegularWindowBound_of_twoResolventPositiveChainLaw`, takes instead
the CEH Theorem 4.2 positive-chain law
`CEHTwoResolventPositiveChainLaw gue` and proves the conversion to the
order-one bound on the grid, including the fifth bound of CEH Lemma 5.6 for
the Hermitian branch, `θ = 1`, the `s₂` bound and the density bounds on the
rectangle.

Every deterministic step is proved:
* canonicalization of the MDE branch and the typical spacing;
* the deterministic rectangle `[E₀ - N^(β-1), E₀ + N^(β-1)] × [π√s N^(ξ-1),
  (2π/c) N^(ξ-1)]` containing all canonical CEH spectral points in the window;
* snapping to a product grid with `N^4` steps per direction;
* the positive spectral extraction `|u_i* A u_j|² ≤ N η_i η_j |⟨Im G A Im G A*⟩|`;
* the resolvent modulus of the positive chain on the rectangle;
* at coincident grid points, `θ = 1` and the subtracted scalar is the
  published center `⟨Γ J⟩` (MDE Ward identity);
* MDE continuity of the center on the rectangle (vertical first-exit bound
  and horizontal boundary modulus);
* the `N^20` ordered-pair union cost and the polynomial tail absorption;
* the reduction of an arbitrary loss exponent `δ` to a small auxiliary height
  exponent (`localETHWindowBad_polynomialTail_of_auxiliaryLoss`).

The extraction bound holds for every orthonormal eigenfamily, so no
simple-spectrum argument is needed and the result holds for an arbitrary
family `gue`.

Source: Cipolloni–Erdős–Henheik, proof of Theorem 2.5 from Theorem 4.2; the external ETH
theorem.  Normalization: normalized trace, resolvent
`(H - z)⁻¹`, `GUE_N(s/N)`, `λ = √s`, spectral point `x + i N^ξ η_f(x)`,
threshold `N^δ N^(-1/2)`, tail `N^(-D)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator ComplexConjugate Topology ENNReal
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH

/-!
## The fixed-point two-resolvent law
-/

/-- The CEH positive two-resolvent chain `⟨Im G(z₁) A Im G(z₂) A*⟩`, with
`G(z) = (H - z)⁻¹`, matrix imaginary part `(X - X*)/(2i)` and normalized trace
`N⁻¹ Tr`. -/
def cehPositiveChain {N : ℕ} (H : LocalETHMatrix N) (z₁ z₂ : ℂ)
    (A : LocalETHMatrix N) : ℂ :=
  NTrace (matrixImaginaryPart (cehHermitianResolvent H z₁) * A *
    matrixImaginaryPart (cehHermitianResolvent H z₂) * Aᴴ)

/-- CEH Definition 5.1 at the pair `(z₁, z̄₂)` with `λ = √s`:
`A° = A - θ ⟨M₁ A M₂*⟩/⟨M₁ M₂*⟩`, where `θ = θ(s Re⟨M₁ M₂*⟩ - 1/2)` is CEH's
cutoff including the value `1/2` at the threshold.  `M₂*` is `(Mf z₂)ᴴ`. -/
def cehETHRegularizedObservable {N : ℕ} (s : ℝ)
    (Mf : ℂ → LocalETHMatrix N) (z₁ z₂ : ℂ) (J : LocalETHMatrix N) :
    LocalETHMatrix N :=
  regularizedObservable
    (regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ)
    (Mf z₁) (Mf z₂)ᴴ J

/-- Failure of the order-one positive-chain bound `N^ε` at one fixed pair
of deterministic spectral parameters, for the sample `F + G`. -/
def CEHFixedPointPositiveChainBad {N : ℕ} (s ε : ℝ)
    (Mf : ℂ → LocalETHMatrix N) (F J : LocalETHMatrix N) (z₁ z₂ : ℂ)
    (G : HermitianMatrix (Fin N)) : Prop :=
  (N : ℝ) ^ ε ≤
    ‖cehPositiveChain (F + G.1) z₁ z₂ (cehETHRegularizedObservable s Mf z₁ z₂ J)‖

/-- **The fixed-point two-resolvent law** (the sole hypothesis of
the final theorem).

Source shape: the stochastic-domination statement
`⟨Im G(z₁) A° Im G(z₂) A°*⟩ ≺ 1` used in the proof of CEH Theorem 2.5, where
it follows from the averaged two-resolvent law (CEH Theorem 4.2) together with
the deterministic bounds of CEH Lemma 5.6 on the regular domain.  The
observable `A°` is the CEH regularization of a fixed Hermitian `J`, `‖J‖ ≤ 1`,
formed at the same deterministic pair `(z₁, z₂)`.

Normalization: `GUE_N(s/N)`, sample `F + G`, normalized trace, resolvent
`(F + G - z)⁻¹`, `λ = √s`.

Quantifiers and uniformity: the cutoff `N₀` depends only on
`κ, C, sLo, sHi, r, c, K, ε₀, ε₁, ε, D`; for every `N ≥ N₀` the bound holds
uniformly in `s ∈ [sLo, sHi]`, the deformation `F` with `‖F‖ ≤ C N^κ √s`, the
MDE branch, the regular boundary window center `E₀`, the two deterministic
spectral parameters with real parts in `(E₀ - r, E₀ + r)` and heights in
`[N^(ε₀-1), N^(ε₁-1)]`, and the observable `J`.  Limit order: parameters,
then `N₀`, then `N` and every dimension-dependent object; the points and the
observable are fixed before the random matrix. -/
def CEHFixedPointPositiveChainLaw (gue : LocalETHGUEFamily) : Prop :=
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
    ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
          {G | CEHFixedPointPositiveChainBad s ε Mf F.1 J z₁ z₂ G} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-!
## Grid vocabulary
-/

/-- The deterministic lower height `N^ξ π √s / N`. -/
def cehETHHeightLower (N : ℕ) (ξ s : ℝ) : ℝ :=
  (N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ))

/-- The product grid on the window rectangle. -/
def cehETHGrid (N : ℕ) (E₀ β ξ s c : ℝ) (m : ℕ) :
    Fin (m + 1) × Fin (m + 1) → ℂ :=
  localETHRectangularSpectralGridPoint E₀ ((N : ℝ) ^ (β - 1))
    (cehETHHeightLower N ξ s) (canonicalHeightRate N ξ c) m m

/-- The snapping radius of `cehETHGrid`. -/
def cehETHMeshRadius (N : ℕ) (β ξ s c : ℝ) (m : ℕ) : ℝ :=
  2 * (N : ℝ) ^ (β - 1) / m +
    (canonicalHeightRate N ξ c - cehETHHeightLower N ξ s) / m

/-- The explicit scalar conditions of the deterministic extraction. -/
def CEHETHGridScalarConditions (N : ℕ) (s r c K β ξ δ ε : ℝ) (m : ℕ) : Prop :=
  (N : ℝ) ^ (β - 1) < r ∧
  1 < (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
    (c / (2 * Real.pi)) ∧
  canonicalHeightRate N ξ c ≤ s * c / 2 ∧
  canonicalVerticalEntryRate N ξ s c +
      (1 + s * K) * cehETHMeshRadius N β ξ s c m * (s * c)⁻¹ ^ 2 ≤ c / 2 ∧
  (2 / c + 2 * K / c ^ 2) *
      (2 * canonicalVerticalEntryRate N ξ s c +
        (1 + s * K) * cehETHMeshRadius N β ξ s c m * (s * c)⁻¹ ^ 2) ≤
    (N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ)) / 2 ∧
  (N : ℝ) * canonicalHeightRate N ξ c ^ 2 *
      ((N : ℝ) ^ ε + 2 * cehETHMeshRadius N β ξ s c m *
        (cehETHHeightLower N ξ s)⁻¹ ^ 3 * (1 + 8 / (s * c ^ 2)) ^ 2) <
    ((N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 / 4

/-!
## Resolvent-side estimates
-/

/-- Resolvent modulus of the positive chain above a common height `eta`:
moving both spectral parameters by at most `r` changes the chain by at most
`2 r eta⁻³ ‖A‖²`. -/
theorem norm_cehPositiveChain_sub_le
    {N : ℕ} (hN : 0 < N) (H : LocalETHMatrix N) (hH : H.IsHermitian)
    {z₁ z₂ w₁ w₂ : ℂ} {eta r : ℝ} (heta : 0 < eta)
    (hz₁ : eta ≤ z₁.im) (hz₂ : eta ≤ z₂.im)
    (hw₁ : eta ≤ w₁.im) (hw₂ : eta ≤ w₂.im)
    (h₁ : ‖z₁ - w₁‖ ≤ r) (h₂ : ‖z₂ - w₂‖ ≤ r) (A : LocalETHMatrix N) :
    ‖cehPositiveChain H z₁ z₂ A - cehPositiveChain H w₁ w₂ A‖ ≤
      2 * r * eta⁻¹ ^ 3 * ‖A‖ ^ 2 := by
  have hpos : ∀ {z : ℂ}, eta ≤ z.im → eta ≤ |z.im| := fun h =>
    h.trans (le_abs_self _)
  have hne : ∀ {z : ℂ}, eta ≤ z.im → z.im ≠ 0 := fun h => by
    intro h0; rw [h0] at h; linarith
  have hinv : ∀ {z : ℂ}, eta ≤ z.im → |z.im|⁻¹ ≤ eta⁻¹ := fun h => by
    simpa [one_div] using one_div_le_one_div_of_le heta (hpos h)
  have hG : ∀ {z : ℂ}, eta ≤ z.im →
      ‖matrixImaginaryPart (cehHermitianResolvent H z)‖ ≤ eta⁻¹ := fun h =>
    (norm_matrixImaginaryPart_le _).trans
      ((norm_cehHermitianResolvent_le H hH (hne h)).trans (hinv h))
  have hlin : ∀ P Q : LocalETHMatrix N,
      matrixImaginaryPart P - matrixImaginaryPart Q =
        matrixImaginaryPart (P - Q) := by
    intro P Q
    unfold matrixImaginaryPart
    rw [Matrix.conjTranspose_sub, ← smul_sub]
    congr 1
    abel
  have hD : ∀ {z w : ℂ}, eta ≤ z.im → eta ≤ w.im → ‖z - w‖ ≤ r →
      ‖matrixImaginaryPart (cehHermitianResolvent H z) -
        matrixImaginaryPart (cehHermitianResolvent H w)‖ ≤ r * eta⁻¹ ^ 2 := by
    intro z w hz hw hzw
    rw [hlin]
    exact (norm_matrixImaginaryPart_le _).trans
      (norm_cehHermitianResolvent_sub_le H hH heta (hpos hz) (hpos hw) hzw)
  set X₁ := matrixImaginaryPart (cehHermitianResolvent H z₁)
  set X₂ := matrixImaginaryPart (cehHermitianResolvent H z₂)
  set Y₁ := matrixImaginaryPart (cehHermitianResolvent H w₁)
  set Y₂ := matrixImaginaryPart (cehHermitianResolvent H w₂)
  have hX₂ : ‖X₂‖ ≤ eta⁻¹ := hG hz₂
  have hY₁ : ‖Y₁‖ ≤ eta⁻¹ := hG hw₁
  have hD₁ : ‖X₁ - Y₁‖ ≤ r * eta⁻¹ ^ 2 := hD hz₁ hw₁ h₁
  have hD₂ : ‖X₂ - Y₂‖ ≤ r * eta⁻¹ ^ 2 := hD hz₂ hw₂ h₂
  have hAH : ‖Aᴴ‖ = ‖A‖ := Matrix.l2_opNorm_conjTranspose A
  have hsplit : X₁ * A * X₂ * Aᴴ - Y₁ * A * Y₂ * Aᴴ =
      (X₁ - Y₁) * A * X₂ * Aᴴ + Y₁ * A * (X₂ - Y₂) * Aᴴ := by
    noncomm_ring
  unfold cehPositiveChain
  rw [← NTrace_sub]
  refine (norm_NTrace_le_l2_opNorm hN _).trans ?_
  rw [hsplit]
  have hei : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hr : 0 ≤ r := (norm_nonneg _).trans h₁
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have t1 : ‖(X₁ - Y₁) * A * X₂ * Aᴴ‖ ≤ r * eta⁻¹ ^ 2 * ‖A‖ * eta⁻¹ * ‖A‖ := by
    refine (norm_mul_le _ _).trans ?_
    rw [hAH]
    gcongr
    refine (norm_mul_le _ _).trans ?_
    gcongr
    refine (norm_mul_le _ _).trans ?_
    gcongr
  have t2 : ‖Y₁ * A * (X₂ - Y₂) * Aᴴ‖ ≤ eta⁻¹ * ‖A‖ * (r * eta⁻¹ ^ 2) * ‖A‖ := by
    refine (norm_mul_le _ _).trans ?_
    rw [hAH]
    gcongr
    refine (norm_mul_le _ _).trans ?_
    gcongr
    refine (norm_mul_le _ _).trans ?_
    gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ r * eta⁻¹ ^ 2 * ‖A‖ * eta⁻¹ * ‖A‖ +
        eta⁻¹ * ‖A‖ * (r * eta⁻¹ ^ 2) * ‖A‖ := add_le_add t1 t2
    _ = 2 * r * eta⁻¹ ^ 3 * ‖A‖ ^ 2 := by ring

/-- Matrix elements of the CEH regularized observable in an orthonormal
eigenfamily: the scalar shift only affects the diagonal. -/
theorem spectralMatrixElement_regularizedObservable
    {N : ℕ} {H : LocalETHMatrix N} {lam : Fin N → ℝ}
    {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily H lam u)
    (θ : ℝ) (M₁ M₂ J : LocalETHMatrix N) (i j : Fin N) :
    spectralMatrixElement u (regularizedObservable θ M₁ M₂ J) i j =
      star (u i) ⬝ᵥ (J *ᵥ u j) -
        ((θ : ℂ) * (NTrace (M₁ * J * M₂) / NTrace (M₁ * M₂))) *
          (if i = j then 1 else 0) := by
  unfold spectralMatrixElement regularizedObservable
  rw [Matrix.vecMul_sub, sub_dotProduct, Matrix.dotProduct_mulVec]
  congr 1
  rw [Matrix.vecMul_smul, Matrix.vecMul_one, smul_dotProduct]
  change ((θ : ℂ) * (NTrace (M₁ * J * M₂) / NTrace (M₁ * M₂))) *
      (star (u i) ⬝ᵥ u j) = _
  rw [hfamily.1 i j]

/-- Positive spectral extraction: `|u_i* A u_j|² ≤ N η₁ η₂ |⟨Im G A Im G A*⟩|`
at the points `λ_i + i η₁` and `λ_j + i η₂`. -/
theorem norm_spectralMatrixElement_sq_le_cehPositiveChain
    {N : ℕ} (hN : 0 < N) {H : LocalETHMatrix N}
    {lam : Fin N → ℝ} {u : Fin N → Fin N → ℂ}
    (hfamily : IsLocalETHOrthonormalEigenFamily H lam u)
    {eta₁ eta₂ : ℝ} (heta₁ : 0 < eta₁) (heta₂ : 0 < eta₂)
    (A : LocalETHMatrix N) (i j : Fin N) :
    ‖spectralMatrixElement u A i j‖ ^ 2 ≤
      (N : ℝ) * eta₁ * eta₂ *
        ‖cehPositiveChain H
          ((lam i : ℂ) + (eta₁ : ℂ) * Complex.I)
          ((lam j : ℂ) + (eta₂ : ℂ) * Complex.I) A‖ := by
  refine (spectralMatrixElement_sq_le_positiveResolvent_at_eigenvalues
    hN hfamily heta₁ heta₂ A i j).trans ?_
  have hfac : 0 ≤ (N : ℝ) * eta₁ * eta₂ := by positivity
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hfac

/-!
## MDE-side estimates on the regular rectangle
-/

/-- Vertical comparison at an arbitrary height below the IFT cutoff. -/
theorem norm_hermitianMDEBranch_sub_boundary_le
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s c x η : ℝ} (hs : 0 < s) (hc : 0 < c) {Mb : LocalETHMatrix N}
    (hboundary : Tendsto
      (fun t : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds Mb))
    (hdensity : c ≤ (Conventions.normalizedTrace Mb).im)
    (hstab : c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb * Mb)‖)
    (hη : 0 < η) (hηH : η ≤ quantitativeIFTHeight s c) :
    ‖hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I) - Mb‖ ≤
      (η + s * (8 * η / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ := by
  obtain ⟨hsol, hMb, hstabId⟩ :=
    boundary_matrix_scalar_identification hF hN hs hc hboundary hdensity
  have hbx : Tendsto (fun t : ℝ => upperBranch hN (hermitianSpectrum hF) hs
      ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (Conventions.normalizedTrace Mb)) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp hboundary
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hF hN hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hF hN hs (by simpa using htpos')]
  have hstab' : c ≤ ‖BlockBand.CEH.stabilityDenominator (hermitianSpectrum hF) s (x : ℂ)
      (Conventions.normalizedTrace Mb)‖ := by
    rw [← hstabId]
    exact hstab
  have hentry (i : Fin N) := norm_upperBranch_entry_sub_boundary_le hN
    (hermitianSpectrum hF) hs hc hsol hdensity hstab' hbx hη hηH i
  have hz : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  rw [hermitianMDEBranch_eq_spectralLift_upper hF hN hs hz]
  have hrate0 : 0 ≤ (η + s * (8 * η / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ :=
    (norm_nonneg _).trans (hentry ⟨0, hN⟩)
  rw [hMb, spectralLift_sub, norm_spectralLift]
  exact (pi_norm_le_iff_of_nonneg hrate0).2 fun i => hentry i

/-- The scalar density stays above `c/2` below the IFT cutoff. -/
theorem half_lt_im_upperBranch_of_boundary
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s c x η : ℝ} (hs : 0 < s) (hc : 0 < c) {Mb : LocalETHMatrix N}
    (hboundary : Tendsto
      (fun t : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds Mb))
    (hdensity : c ≤ (Conventions.normalizedTrace Mb).im)
    (hstab : c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb * Mb)‖)
    (hη : 0 < η) (hηH : η ≤ quantitativeIFTHeight s c) :
    c / 2 < (upperBranch hN (hermitianSpectrum hF) hs
      ((x : ℂ) + (η : ℂ) * Complex.I)).im := by
  obtain ⟨hsol, hMb, hstabId⟩ :=
    boundary_matrix_scalar_identification hF hN hs hc hboundary hdensity
  have hbx : Tendsto (fun t : ℝ => upperBranch hN (hermitianSpectrum hF) hs
      ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (Conventions.normalizedTrace Mb)) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp hboundary
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hF hN hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hF hN hs (by simpa using htpos')]
  have hstab' : c ≤ ‖BlockBand.CEH.stabilityDenominator (hermitianSpectrum hF) s (x : ℂ)
      (Conventions.normalizedTrace Mb)‖ := by
    rw [← hstabId]
    exact hstab
  have hclose := upperBranch_close_boundary_below_quantitativeIFTHeight
    hN (hermitianSpectrum hF) hs hc hsol hdensity hstab' hbx η hη hηH
  have hspec := quantitativeIFTRadius_height_spec hs hc
  have himdiff := Complex.abs_im_le_norm
    (upperBranch hN (hermitianSpectrum hF) hs ((x : ℂ) + (η : ℂ) * Complex.I) -
      Conventions.normalizedTrace Mb)
  rw [Complex.sub_im] at himdiff
  have hlower := neg_le_of_abs_le himdiff
  linarith [hspec.2.2.1]

/-- Horizontal modulus of the boundary matrix on a regular window. -/
theorem norm_boundaryMatrix_sub_le
    {N : ℕ} (hN : 0 < N) {s E₀ r c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {Mb Mb' : ℝ → LocalETHMatrix N}
    (hdata : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      Tendsto (fun η : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)) ∧
        HasLocalETHMatrixDerivAt Mb (Mb' x) x ∧
        ‖Mb' x‖ ≤ K ∧
        c ≤ (Conventions.normalizedTrace (Mb x)).im ∧
        ‖Mb x‖ ≤ K ∧
        c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb x * Mb x)‖)
    {x y : ℝ} (hx : x ∈ Ioo (E₀ - r) (E₀ + r)) (hy : y ∈ Ioo (E₀ - r) (E₀ + r)) :
    ‖Mb y - Mb x‖ ≤ (1 + s * K) * |y - x| * (s * c)⁻¹ ^ 2 := by
  have hxy (u v : ℝ) (hu : u ∈ Ioo (E₀ - r) (E₀ + r)) (hv : v ∈ Ioo (E₀ - r) (E₀ + r))
      (huv : u ≤ v) :
      ‖Conventions.normalizedTrace (Mb v) - Conventions.normalizedTrace (Mb u)‖ ≤
        K * |v - u| := by
    have hseg : Icc u v ⊆ Ioo (E₀ - r) (E₀ + r) := by
      intro t ht
      exact ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩
    simpa [abs_of_nonneg (sub_nonneg.mpr huv)] using
      norm_normalizedTrace_sub_le_of_regularDerivative hN
        huv hseg (fun t ht => (hdata t ht).2.1)
        (fun t ht => (hdata t ht).2.2.1)
  have hmxy : ‖Conventions.normalizedTrace (Mb y) -
      Conventions.normalizedTrace (Mb x)‖ ≤ K * |y - x| := by
    rcases le_total x y with h | h
    · exact hxy x y hx hy h
    · rw [norm_sub_rev, abs_sub_comm]
      exact hxy y x hy hx h
  have hK : 0 ≤ K := (norm_nonneg (Mb' x)).trans (hdata x hx).2.2.1
  obtain ⟨-, hMbx, -⟩ :=
    boundary_matrix_scalar_identification hF hN hs hc (hdata x hx).1 (hdata x hx).2.2.2.1
  obtain ⟨-, hMby, -⟩ :=
    boundary_matrix_scalar_identification hF hN hs hc (hdata y hy).1 (hdata y hy).2.2.2.1
  have hentry (i : Fin N) := norm_boundary_entry_sub_le_of_mean_modulus
    (hermitianSpectrum hF) hs hc hK (hdata x hx).2.2.2.1 (hdata y hy).2.2.2.1 hmxy i
  have hrate0 : 0 ≤ (1 + s * K) * |y - x| * (s * c)⁻¹ ^ 2 := by positivity
  rw [hMby, hMbx, spectralLift_sub, norm_spectralLift]
  exact (pi_norm_le_iff_of_nonneg hrate0).2 fun i => hentry i

/-- Below the cutoff, the Hermitian branch has operator norm at most `2/(sc)`. -/
theorem norm_hermitianMDEBranch_le_two_div_of_half_lt
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s c x η : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hm : c / 2 < (upperBranch hN (hermitianSpectrum hF) hs
      ((x : ℂ) + (η : ℂ) * Complex.I)).im) (hη : 0 < η) :
    ‖hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I)‖ ≤ 2 / (s * c) := by
  set z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : 0 < z.im := hzim ▸ hη
  set m := upperBranch hN (hermitianSpectrum hF) hs z with hmdef
  have hh : s * c / 2 ≤ effectiveHeight s z m := by
    unfold effectiveHeight
    rw [hzim]
    nlinarith
  have hscpos : 0 < s * c / 2 := by positivity
  have hhpos : 0 < effectiveHeight s z m := lt_of_lt_of_le hscpos hh
  rw [hermitianMDEBranch_eq_spectralLift_upper hF hN hs hz, norm_spectralLift]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖entry (hermitianSpectrum hF) s z m i‖ ≤ (effectiveHeight s z m)⁻¹ :=
        norm_entry_le_inv_effectiveHeight _ hhpos i
    _ ≤ (s * c / 2)⁻¹ := inv_anti₀ hscpos hh
    _ = 2 / (s * c) := by field_simp

/-- At coincident arguments below the cutoff the CEH coefficient is one and
the regularization subtracts the published center. -/
theorem cehETHRegularizedObservable_self_eq
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s c x η : ℝ} (hs : 0 < s) (hc : 0 < c) {Mb : LocalETHMatrix N}
    (hboundary : Tendsto
      (fun t : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds Mb))
    (hdensity : c ≤ (Conventions.normalizedTrace Mb).im)
    (hstab : c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb * Mb)‖)
    (hη : 0 < η) (hηH : η ≤ quantitativeIFTHeight s c) (hηs : η ≤ s * c / 2)
    (J : LocalETHMatrix N) :
    cehETHRegularizedObservable s (hermitianMDEBranch hF hs)
        ((x : ℂ) + (η : ℂ) * Complex.I) ((x : ℂ) + (η : ℂ) * Complex.I) J =
      regularizedObservable 1
        (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))
        (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))ᴴ J ∧
    NTrace (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I) * J *
          (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))ᴴ) /
        NTrace (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I) *
          (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))ᴴ) =
      NTrace (localETHGamma
        (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I)) * J) := by
  set z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I with hzdef
  have hzim : z.im = η := by simp [hzdef]
  have hz : 0 < z.im := hzim ▸ hη
  have hm : c / 2 < (upperBranch hN (hermitianSpectrum hF) hs z).im :=
    half_lt_im_upperBranch_of_boundary hN hF hs hc hboundary hdensity hstab hη hηH
  set M := hermitianMDEBranch hF hs z with hMdef
  set m := upperBranch hN (hermitianSpectrum hF) hs z with hmdef
  have hward := matrix_imaginaryPart_Ward_identity hF hN hs hz
  have havg := normalizedTrace_star_mul_hermitianMDEBranch hF hN hs hz
  set a := averageReal (fun i => ‖entry (hermitianSpectrum hF) s z m i‖ ^ 2) with hadef
  rw [havg] at hward
  have hwardR : m.im = effectiveHeight s z m * a := by exact_mod_cast hward
  have hcyc : NTrace (M * Mᴴ) = (a : ℂ) := by
    rw [← havg, Matrix.star_eq_conjTranspose]
    unfold NTrace Conventions.normalizedTrace
    rw [Matrix.trace_mul_comm]
  have hθ : regularizationCoefficient (Real.sqrt s : ℂ) M Mᴴ = 1 := by
    unfold regularizationCoefficient
    apply cehTheta_of_pos
    rw [hcyc, ← Complex.ofReal_pow, Real.sq_sqrt hs.le, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    have hh : effectiveHeight s z m = η + s * m.im := by
      unfold effectiveHeight
      rw [hzim]
    rw [hh] at hwardR
    have hhpos : 0 < η + s * m.im := by nlinarith
    nlinarith
  refine ⟨?_, normalizedTrace_mde_word_div_eq_normalizedTrace_gamma hF hN hs hz J⟩
  unfold cehETHRegularizedObservable
  rw [hθ]

/-- The CEH regularized observable has a dimension-free norm bound at two
points below the IFT cutoff of a regular window. -/
theorem norm_cehETHRegularizedObservable_le
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s c x₁ x₂ η₁ η₂ : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hm₁ : c / 2 < (upperBranch hN (hermitianSpectrum hF) hs
      ((x₁ : ℂ) + (η₁ : ℂ) * Complex.I)).im)
    (hm₂ : c / 2 < (upperBranch hN (hermitianSpectrum hF) hs
      ((x₂ : ℂ) + (η₂ : ℂ) * Complex.I)).im)
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) :
    ‖cehETHRegularizedObservable s (hermitianMDEBranch hF hs)
        ((x₁ : ℂ) + (η₁ : ℂ) * Complex.I) ((x₂ : ℂ) + (η₂ : ℂ) * Complex.I) J‖ ≤
      1 + 8 / (s * c ^ 2) := by
  set z₁ : ℂ := (x₁ : ℂ) + (η₁ : ℂ) * Complex.I with hz₁def
  set z₂ : ℂ := (x₂ : ℂ) + (η₂ : ℂ) * Complex.I with hz₂def
  have hM₁ := norm_hermitianMDEBranch_le_two_div_of_half_lt hN hF hs hc hm₁ hη₁
  have hM₂ := norm_hermitianMDEBranch_le_two_div_of_half_lt hN hF hs hc hm₂ hη₂
  set M₁ := hermitianMDEBranch hF hs z₁ with hM₁def
  set M₂ := hermitianMDEBranch hF hs z₂ with hM₂def
  have : NeZero N := ⟨hN.ne'⟩
  unfold cehETHRegularizedObservable regularizedObservable
  set θ := regularizationCoefficient (Real.sqrt s : ℂ) M₁ M₂ᴴ with hθdef
  have hB : 0 ≤ 8 / (s * c ^ 2) := by positivity
  by_cases h0 : θ = 0
  · rw [h0]
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, sub_zero]
    linarith
  · have harg : 0 ≤ ((Real.sqrt s : ℂ) ^ 2 * NTrace (M₁ * M₂ᴴ)).re - 1 / 2 := by
      by_contra hneg
      exact h0 (by rw [hθdef]; exact cehTheta_of_neg (not_le.mp hneg))
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le, Complex.re_ofReal_mul] at harg
    have hden : 1 / (2 * s) ≤ ‖NTrace (M₁ * M₂ᴴ)‖ := by
      have := Complex.re_le_norm (NTrace (M₁ * M₂ᴴ))
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hdenpos : 0 < ‖NTrace (M₁ * M₂ᴴ)‖ := lt_of_lt_of_le (by positivity) hden
    have hnum : ‖NTrace (M₁ * J * M₂ᴴ)‖ ≤ (2 / (s * c)) * 1 * (2 / (s * c)) := by
      calc ‖NTrace (M₁ * J * M₂ᴴ)‖ ≤ ‖M₁ * J * M₂ᴴ‖ :=
            norm_normalizedTrace_le_localETHNorm hN _
        _ ≤ ‖M₁‖ * ‖J‖ * ‖M₂ᴴ‖ := by
            refine (norm_mul_le _ _).trans ?_
            gcongr
            exact norm_mul_le _ _
        _ ≤ _ := by
            rw [Matrix.l2_opNorm_conjTranspose]
            gcongr
    have hθ1 : θ ≤ 1 := by
      rw [hθdef]
      unfold regularizationCoefficient cehTheta
      split_ifs <;> norm_num
    have hθ0 : 0 ≤ θ := by
      rw [hθdef]
      unfold regularizationCoefficient cehTheta
      split_ifs <;> norm_num
    have hratio : ‖NTrace (M₁ * J * M₂ᴴ) / NTrace (M₁ * M₂ᴴ)‖ ≤ 8 / (s * c ^ 2) := by
      rw [norm_div, div_le_iff₀ hdenpos]
      calc ‖NTrace (M₁ * J * M₂ᴴ)‖ ≤ (2 / (s * c)) * 1 * (2 / (s * c)) := hnum
        _ = 8 / (s * c ^ 2) * (1 / (2 * s)) := by field_simp; ring
        _ ≤ _ := by gcongr
    calc ‖J - ((θ : ℂ) * (NTrace (M₁ * J * M₂ᴴ) / NTrace (M₁ * M₂ᴴ))) •
          (1 : Matrix (Fin N) (Fin N) ℂ)‖
        ≤ ‖J‖ + ‖((θ : ℂ) * (NTrace (M₁ * J * M₂ᴴ) / NTrace (M₁ * M₂ᴴ))) •
          (1 : Matrix (Fin N) (Fin N) ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 8 / (s * c ^ 2) := by
        gcongr
        rw [norm_smul, norm_one, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hθ0]
        calc θ * ‖NTrace (M₁ * J * M₂ᴴ) / NTrace (M₁ * M₂ᴴ)‖ ≤ 1 * (8 / (s * c ^ 2)) := by
              gcongr
          _ = _ := one_mul _

/-!
## Eventual scalar conditions
-/

/-- The lower height is `π √s N^(ξ-1)`. -/
theorem cehETHGrid_heightLower_eq {N : ℕ} (hN : 0 < N) (ξ s : ℝ) :
    cehETHHeightLower N ξ s = Real.pi * Real.sqrt s * (N : ℝ) ^ (ξ - 1) := by
  have hx : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [cehETHHeightLower, Real.rpow_sub_one hx.ne']
  field_simp

/-- At mesh `N^4`, the snapping radius is at most `(r+1) N^(-4)` once the
window is at most `r/2` and the canonical height is at most `1`. -/
theorem cehETHGrid_meshRadius_le {N : ℕ} (hN : 0 < N) {β ξ s c r : ℝ}
    (hR : 2 * (N : ℝ) ^ (β - 1) ≤ r)
    (hH : canonicalHeightRate N ξ c ≤ 1) :
    cehETHMeshRadius N β ξ s c (N ^ 4) ≤ (r + 1) * (N : ℝ) ^ (-4 : ℝ) := by
  have hx : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlow : 0 ≤ cehETHHeightLower N ξ s := by
    unfold cehETHHeightLower; positivity
  have hQ : (N : ℝ) ^ (-4 : ℝ) = ((N : ℝ) ^ 4)⁻¹ := by
    rw [Real.rpow_neg hx.le]; norm_num
  rw [hQ, cehETHMeshRadius]
  push_cast
  rw [← add_div, div_eq_mul_inv]
  gcongr
  linarith

/-- Eventually the source window satisfies `2 N^(β-1) ≤ r`. -/
theorem cehETHGrid_eventually_window {β r : ℝ} (hβ : β < 1) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (β - 1) ≤ r := by
  filter_upwards [eventually_natCast_rpow_le_mul_rpow (a := β - 1) (b := 0)
    (by linarith) (half_pos hr)] with N h
  rw [Real.rpow_zero, mul_one] at h
  linarith

/-- A negative power is eventually below any positive constant. -/
theorem cehETHGrid_eventually_rpow_le {a e : ℝ} (ha : a < 0) (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ e := by
  filter_upwards [eventually_natCast_rpow_le_mul_rpow (a := a) (b := 0) ha he]
    with N h
  rwa [Real.rpow_zero, mul_one] at h

/-- All scalar conditions of the deterministic extraction hold eventually in
`N`, with mesh `N^4`, uniformly in `s ∈ [sLo, sHi]`, together with the two
height-domain conditions of `CEHFixedPointPositiveChainLaw` at
`ε₀ = ξ/2`, `ε₁ = 2ξ`.  The cutoff depends only on
`sLo, sHi, r, c, K, β, ξ, δ, ε`. -/
theorem eventually_cehETHGridScalarConditions
    {sLo sHi r c K β ξ δ ε : ℝ} (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi)
    (hr : 0 < r) (hc : 0 < c) (hK : 0 < K) (hβ : β < 1)
    (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hε : 0 < ε)
    (hεδ : 2 * ξ + ε < 2 * δ) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      CEHETHGridScalarConditions N s r c K β ξ δ ε (N ^ 4) ∧
      (N : ℝ) ^ (ξ / 2 - 1) ≤ cehETHHeightLower N ξ s ∧
      canonicalHeightRate N ξ c ≤ (N : ℝ) ^ (2 * ξ - 1) := by
  have hsHi0 : 0 < sHi := lt_of_lt_of_le hsLo hsHi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt sLo := Real.sqrt_pos.mpr hsLo
  set κ := canonicalVerticalRateConstant sLo c with hκdef
  have hκ : 0 < κ := canonicalVerticalRateConstant_pos hsLo hc
  set L := 2 / c + 2 * K / c ^ 2 with hLdef
  have hL : 0 < L := by positivity
  set A := r + 1 with hAdef
  have hA : 0 < A := by positivity
  set B := (1 + sHi * K) * A * (sLo * c)⁻¹ ^ 2 with hBdef
  have hB : 0 < B := by positivity
  set Λ := 1 + 8 / (sLo * c ^ 2) with hΛdef
  set C1 := (2 * Real.pi / c) ^ 2 with hC1def
  have hC1 : 0 < C1 := by positivity
  set C2 := C1 * (2 * A * (Real.pi * Real.sqrt sLo)⁻¹ ^ 3 * Λ ^ 2) with hC2def
  have hC2 : 0 < C2 := by positivity
  have hHq : 0 < quantitativeIFTHeight sLo c :=
    (quantitativeIFTRadius_height_spec hsLo hc).2.1
  filter_upwards [eventually_ge_atTop 4,
    cehETHGrid_eventually_window hβ hr,
    eventually_one_lt_ceh_test_density_scale (by linarith : ξ < 1) hHq hc,
    cehETHGrid_eventually_rpow_le (a := ξ - 1) (by linarith)
      (by positivity : 0 < c / (2 * Real.pi)),
    cehETHGrid_eventually_rpow_le (a := ξ - 1) (by linarith)
      (by positivity : 0 < sLo * c ^ 2 / (4 * Real.pi)),
    cehETHGrid_eventually_rpow_le (a := ξ - 1) (by linarith)
      (by positivity : 0 < c / (4 * κ)),
    cehETHGrid_eventually_rpow_le (a := -4) (by norm_num)
      (by positivity : 0 < c / (4 * B)),
    eventually_natCast_rpow_le_mul_rpow (a := ξ - 1) (b := δ - 1 / 2)
      (by linarith) (by positivity : 0 < 1 / (8 * L * κ)),
    eventually_natCast_rpow_le_mul_rpow (a := -4) (b := δ - 1 / 2)
      (by linarith) (by positivity : 0 < 1 / (4 * L * B)),
    eventually_natCast_rpow_le_mul_rpow (a := 2 * ξ - 1 + ε) (b := 2 * δ - 1)
      (by linarith) (by positivity : 0 < 1 / (16 * C1)),
    eventually_natCast_rpow_le_mul_rpow (a := -2 - ξ) (b := 2 * δ - 1)
      (by linarith) (by positivity : 0 < 1 / (16 * C2)),
    cehETHGrid_eventually_rpow_le (a := -(ξ / 2)) (by linarith)
      (by positivity : 0 < Real.pi * Real.sqrt sLo),
    eventually_natCast_rpow_le_mul_rpow (a := 0) (b := ξ) hξ
      (by positivity : 0 < c / (2 * Real.pi))]
    with N hN4 hwin hlg hP1 hP2 hP3 hQ4 hP5 hQ5 h61 h62 hlowN hup
  have hN0 : 0 < N := by omega
  have hx : 0 < (N : ℝ) := by exact_mod_cast hN0
  refine ⟨hN4, ?_⟩
  intro s hs hsU
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  set x := (N : ℝ) with hxdef
  set P := x ^ (ξ - 1) with hPdef
  have hP0 : 0 < P := by positivity
  set Q := x ^ (-4 : ℝ) with hQdef
  have hQ0 : 0 < Q := by positivity
  set T := x ^ (δ - 1 / 2) with hTdef
  have hT0 : 0 < T := by positivity
  have hT : x ^ δ * x ^ (-(1 / 2 : ℝ)) = T := by
    rw [hTdef, ← Real.rpow_add hx]; ring_nf
  have hT2 : x ^ (2 * δ - 1) = T ^ 2 := by
    rw [hTdef, sq, ← Real.rpow_add hx]; ring_nf
  have hHdef : canonicalHeightRate N ξ c = (2 * Real.pi / c) * P := rfl
  have hH1 : canonicalHeightRate N ξ c ≤ 1 := by
    rw [hHdef]
    calc (2 * Real.pi / c) * P ≤ (2 * Real.pi / c) * (c / (2 * Real.pi)) := by
          gcongr
      _ = 1 := by field_simp
  have hlow := cehETHGrid_heightLower_eq hN0 ξ s
  have hlowLo : Real.pi * Real.sqrt sLo * P ≤ cehETHHeightLower N ξ s := by
    rw [hlow]; gcongr
  have hmesh := cehETHGrid_meshRadius_le hN0 (β := β) (s := s) hwin hH1
  rw [← hQdef] at hmesh
  have hQ := quantitativeIFTHeight_le_of_le hsLo hs hc
  have hκs := canonicalVerticalRateConstant_le_of_le hsLo hs hc
  have hrate : canonicalVerticalEntryRate N ξ s c ≤ κ * P := by
    rw [canonicalVerticalEntryRate_eq hs0 hc]
    gcongr
  -- the mesh contribution to the boundary-entry terms
  have hmeshTerm : (1 + s * K) * cehETHMeshRadius N β ξ s c (N ^ 4) *
      (s * c)⁻¹ ^ 2 ≤ B * Q := by
    calc (1 + s * K) * cehETHMeshRadius N β ξ s c (N ^ 4) * (s * c)⁻¹ ^ 2
        ≤ (1 + s * K) * (A * Q) * (s * c)⁻¹ ^ 2 := by gcongr
      _ ≤ (1 + sHi * K) * (A * Q) * (sLo * c)⁻¹ ^ 2 := by gcongr
      _ = B * Q := by rw [hBdef]; ring
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have : (0 : ℝ) < x ^ (β - 1) := by positivity
    linarith
  · refine lt_of_lt_of_le hlg ?_
    gcongr
  · rw [hHdef]
    calc (2 * Real.pi / c) * P ≤ (2 * Real.pi / c) * (sLo * c ^ 2 / (4 * Real.pi)) := by
          gcongr
      _ = sLo * c / 2 := by field_simp; ring
      _ ≤ s * c / 2 := by gcongr
  · calc _ ≤ κ * P + B * Q := add_le_add hrate hmeshTerm
      _ ≤ κ * (c / (4 * κ)) + B * (c / (4 * B)) := by gcongr
      _ = c / 2 := by field_simp; ring
  · rw [hT]
    calc _ ≤ L * (2 * (κ * P) + B * Q) := by gcongr
      _ ≤ L * (2 * (κ * (1 / (8 * L * κ) * T)) + B * (1 / (4 * L * B) * T)) := by
          gcongr
      _ = T / 2 := by field_simp; ring
  · rw [hT]
    have hΛs : 1 + 8 / (s * c ^ 2) ≤ Λ := by rw [hΛdef]; gcongr
    have hinv : (cehETHHeightLower N ξ s)⁻¹ ≤ (Real.pi * Real.sqrt sLo * P)⁻¹ := by
      gcongr
    have hlow0 : 0 < cehETHHeightLower N ξ s := lt_of_lt_of_le (by positivity) hlowLo
    have hX1 : x ^ (2 * ξ - 1 + ε) = x * P ^ 2 * x ^ ε := by
      rw [show 2 * ξ - 1 + ε = 1 + (ξ - 1) + (ξ - 1) + ε by ring,
        Real.rpow_add hx, Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one, hPdef]
      ring
    have hX2 : x ^ (-2 - ξ) = x * P ^ 2 * Q * P⁻¹ ^ 3 := by
      rw [show -2 - ξ = 1 + (ξ - 1) + (ξ - 1) + (-4) + (-(ξ - 1)) + (-(ξ - 1)) +
          (-(ξ - 1)) by ring]
      simp only [Real.rpow_add hx]
      rw [Real.rpow_neg hx.le (ξ - 1), Real.rpow_one, hPdef, hQdef]
      ring
    rw [hT2] at h61 h62
    calc x * canonicalHeightRate N ξ c ^ 2 *
          (x ^ ε + 2 * cehETHMeshRadius N β ξ s c (N ^ 4) *
            (cehETHHeightLower N ξ s)⁻¹ ^ 3 * (1 + 8 / (s * c ^ 2)) ^ 2)
        ≤ x * canonicalHeightRate N ξ c ^ 2 *
          (x ^ ε + 2 * (A * Q) * (cehETHHeightLower N ξ s)⁻¹ ^ 3 *
            (1 + 8 / (s * c ^ 2)) ^ 2) := by gcongr
      _ ≤ x * canonicalHeightRate N ξ c ^ 2 *
          (x ^ ε + 2 * (A * Q) * (Real.pi * Real.sqrt sLo * P)⁻¹ ^ 3 * Λ ^ 2) := by
          gcongr
      _ = C1 * x ^ (2 * ξ - 1 + ε) + C2 * x ^ (-2 - ξ) := by
          rw [hX1, hX2, hHdef, hC2def, hC1def]
          ring
      _ ≤ C1 * (1 / (16 * C1) * T ^ 2) + C2 * (1 / (16 * C2) * T ^ 2) := by gcongr
      _ = T ^ 2 / 8 := by field_simp; ring
      _ < T ^ 2 / 4 := by have : 0 < T ^ 2 := by positivity
                          linarith
  · have hsplit : x ^ (ξ / 2 - 1) = x ^ (-(ξ / 2)) * P := by
      rw [hPdef, ← Real.rpow_add hx]; ring_nf
    rw [hsplit]
    calc x ^ (-(ξ / 2)) * P ≤ Real.pi * Real.sqrt sLo * P := by gcongr
      _ ≤ cehETHHeightLower N ξ s := hlowLo
  · have hsplit : x ^ (2 * ξ - 1) = x ^ ξ * P := by
      rw [hPdef, ← Real.rpow_add hx]; ring_nf
    rw [hsplit, hHdef]
    rw [Real.rpow_zero] at hup
    have : 2 * Real.pi / c ≤ x ^ ξ := by
      rw [div_le_iff₀ hc]
      have := mul_le_mul_of_nonneg_left hup (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      calc 2 * Real.pi = 2 * Real.pi * 1 := by ring
        _ ≤ 2 * Real.pi * (c / (2 * Real.pi) * x ^ ξ) := this
        _ = x ^ ξ * c := by field_simp
    gcongr

/-!
## Deterministic assembly
-/

/-- The vertical modulus at a height below the canonical rate is at most the
canonical vertical entry rate. -/
theorem verticalModulus_le_canonicalVerticalEntryRate
    {N : ℕ} {s c ξ η : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hηH : η ≤ canonicalHeightRate N ξ c) :
    (η + s * (8 * η / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ ≤
      canonicalVerticalEntryRate N ξ s c := by
  unfold canonicalVerticalEntryRate
  dsimp only
  have h1 : 0 ≤ (s * c / 2)⁻¹ := by positivity
  have h2 : 0 ≤ (s * c)⁻¹ := by positivity
  gcongr

/-- On a regular window the deterministic lower height is strictly below the
canonical upper height rate. -/
theorem cehETHHeightLower_lt_canonicalHeightRate
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s E₀ r c K ξ : ℝ} (hs : 0 < s) (hc : 0 < c) (hr : 0 < r)
    (hregular : LocalETHRegularBoundaryWindow s (hermitianMDEBranch hF hs) E₀ r c K) :
    cehETHHeightLower N ξ s < canonicalHeightRate N ξ c := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  have hx₀ : E₀ ∈ Ioo (E₀ - r) (E₀ + r) := by
    constructor <;> linarith
  obtain ⟨hboundary, _hderiv, _hderivBound, hdensity, _hnorm, _hstability⟩ :=
    hdata E₀ hx₀
  obtain ⟨hsol, _hMb, _hstabId⟩ :=
    boundary_matrix_scalar_identification hF hN hs hc hboundary hdensity
  exact canonicalHeightLower_lt_canonicalHeightRate_of_boundarySolution
    hN (hermitianSpectrum hF) hs hc hsol hdensity

/-- **Center comparison between a grid point and a canonical point.**  Both
centers are compared with the boundary center at the canonical energy. -/
theorem norm_gridCenter_sub_canonicalCenter_le
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s E₀ r c K ξ : ℝ} (hs : 0 < s) (hc : 0 < c)
    {Mb Mb' : ℝ → LocalETHMatrix N}
    (hdata : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      Tendsto (fun η : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)) ∧
        HasLocalETHMatrixDerivAt Mb (Mb' x) x ∧
        ‖Mb' x‖ ≤ K ∧
        c ≤ (Conventions.normalizedTrace (Mb x)).im ∧
        ‖Mb x‖ ≤ K ∧
        c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb x * Mb x)‖)
    (hHq : canonicalHeightRate N ξ c ≤ quantitativeIFTHeight s c)
    {x x' η η' : ℝ} (hx : x ∈ Ioo (E₀ - r) (E₀ + r))
    (hx' : x' ∈ Ioo (E₀ - r) (E₀ + r))
    (hη : 0 < η) (hηH : η ≤ canonicalHeightRate N ξ c)
    (hη' : 0 < η') (hη'H : η' ≤ canonicalHeightRate N ξ c)
    (hbudget : canonicalVerticalEntryRate N ξ s c +
      (1 + s * K) * |x' - x| * (s * c)⁻¹ ^ 2 ≤ c / 2)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) :
    ‖NTrace (localETHGamma
          (hermitianMDEBranch hF hs ((x' : ℂ) + (η' : ℂ) * Complex.I)) * J) -
        NTrace (localETHGamma
          (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I)) * J)‖ ≤
      (2 / c + 2 * K / c ^ 2) *
        (2 * canonicalVerticalEntryRate N ξ s c +
          (1 + s * K) * |x' - x| * (s * c)⁻¹ ^ 2) := by
  obtain ⟨hb, _hd, _hd', hdens, hnorm, hstab⟩ := hdata x hx
  obtain ⟨hb', _hdx, _hdx', hdens', _hnorm', hstab'⟩ := hdata x' hx'
  set V := canonicalVerticalEntryRate N ξ s c
  set Hor := (1 + s * K) * |x' - x| * (s * c)⁻¹ ^ 2
  have hHor : 0 ≤ Hor := by
    have hK : 0 ≤ K := (norm_nonneg _).trans _hd'
    positivity
  have hv : ‖hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I) - Mb x‖ ≤ V :=
    (norm_hermitianMDEBranch_sub_boundary_le hN hF hs hc hb hdens hstab hη
      (hηH.trans hHq)).trans
      (verticalModulus_le_canonicalVerticalEntryRate hs hc hηH)
  have hv' : ‖hermitianMDEBranch hF hs ((x' : ℂ) + (η' : ℂ) * Complex.I) - Mb x'‖ ≤ V :=
    (norm_hermitianMDEBranch_sub_boundary_le hN hF hs hc hb' hdens' hstab' hη'
      (hη'H.trans hHq)).trans
      (verticalModulus_le_canonicalVerticalEntryRate hs hc hη'H)
  have hh : ‖Mb x' - Mb x‖ ≤ Hor := norm_boundaryMatrix_sub_le hN hs hc hF hdata hx hx'
  have hv'' : ‖hermitianMDEBranch hF hs ((x' : ℂ) + (η' : ℂ) * Complex.I) - Mb x‖ ≤
      V + Hor := by
    calc
      _ = ‖(hermitianMDEBranch hF hs ((x' : ℂ) + (η' : ℂ) * Complex.I) - Mb x') +
            (Mb x' - Mb x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ V + Hor := add_le_add hv' hh
  have hV0 : 0 ≤ V := (norm_nonneg _).trans hv
  have e₁ := norm_normalizedTrace_localETHGamma_mul_sub_le hN hc hv''
    hbudget hnorm hdens hJ
  have e₂ := norm_normalizedTrace_localETHGamma_mul_sub_le hN hc hv
    (by linarith) hnorm hdens hJ
  set P := NTrace (localETHGamma
    (hermitianMDEBranch hF hs ((x' : ℂ) + (η' : ℂ) * Complex.I)) * J)
  set Q := NTrace (localETHGamma
    (hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I)) * J)
  set B := Conventions.normalizedTrace (localETHGamma (Mb x) * J)
  have hL : 0 ≤ 2 / c + 2 * K / c ^ 2 := by
    have hK : 0 ≤ K := (norm_nonneg _).trans _hd'
    positivity
  calc
    ‖P - Q‖ ≤ ‖P - B‖ + ‖Q - B‖ := by
      calc
        ‖P - Q‖ = ‖(P - B) - (Q - B)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    _ ≤ (2 / c + 2 * K / c ^ 2) * (V + Hor) + (2 / c + 2 * K / c ^ 2) * V :=
      add_le_add e₁ e₂
    _ = (2 / c + 2 * K / c ^ 2) * (2 * V + Hor) := by ring

/-- The real and imaginary parts of a rectangular grid point. -/
theorem cehETHGrid_eq (N : ℕ) (E₀ β ξ s c : ℝ) (m : ℕ)
    (a : Fin (m + 1) × Fin (m + 1)) :
    cehETHGrid N E₀ β ξ s c m a =
      ((localETHRealGridPoint E₀ ((N : ℝ) ^ (β - 1)) m a.1 : ℝ) : ℂ) +
        ((localETHHeightGridPoint (cehETHHeightLower N ξ s)
          (canonicalHeightRate N ξ c) m a.2 : ℝ) : ℂ) * Complex.I :=
  rfl

/-- **Deterministic random-to-grid extraction.**  Under the explicit scalar
conditions, a sample in the bad event at `(ξ, δ)` fails the
order-one positive-chain bound `N^ε` at some ordered pair of points of the
rectangular grid, with the CEH regularized observable formed at that pair. -/
theorem exists_gridPositiveChainBad_of_localETHWindowBad
    {N : ℕ} (hN : 4 ≤ N) {s : ℝ} (hs : 0 < s) (F : HermitianMatrix (Fin N))
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F.1 Mf)
    {etaF : ℝ → ℝ} (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x))
    {E₀ r c K β ξ δ ε : ℝ} (hr : 0 < r) (hc : 0 < c) (hξ : 0 ≤ ξ)
    (hreg : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) {m : ℕ} (hm : 0 < m)
    (hcond : CEHETHGridScalarConditions N s r c K β ξ δ ε m)
    (G : HermitianMatrix (Fin N))
    (hbad : LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G) :
    ∃ a b : Fin (m + 1) × Fin (m + 1),
      CEHFixedPointPositiveChainBad s ε Mf F.1 J
        (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) G := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcond
  have hN0 : 0 < N := by omega
  have hF : F.1.IsHermitian := F.2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch hF hs hMf hreg
  have hetaEq := localETHTypicalSpacingFunction_eq_canonical hN hF hs hMf hetaF
  obtain ⟨Mb, Mb', hdata⟩ := hregC.boundary
  have hK : 0 ≤ K := by
    have hx₀ : E₀ ∈ Ioo (E₀ - r) (E₀ + r) := by constructor <;> linarith
    exact (norm_nonneg _).trans (hdata E₀ hx₀).2.2.1
  obtain ⟨lam, u, hfam, i, j, hi, hj, hlt⟩ := hbad
  set R : ℝ := (N : ℝ) ^ (β - 1) with hRdef
  set Hr : ℝ := canonicalHeightRate N ξ c with hHrdef
  set lo : ℝ := cehETHHeightLower N ξ s with hlodef
  set ρ : ℝ := cehETHMeshRadius N β ξ s c m with hρdef
  set V : ℝ := canonicalVerticalEntryRate N ξ s c with hVdef
  set T : ℝ := (N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ)) with hTdef
  set Mc : ℂ → LocalETHMatrix N := hermitianMDEBranch hF hs with hMcdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hNr _
  have hlopos : 0 < lo := by
    rw [hlodef, cehETHHeightLower]
    exact mul_pos (Real.rpow_pos_of_pos hNr ξ)
      (div_pos (mul_pos Real.pi_pos (Real.sqrt_pos.2 hs)) hNr)
  have hloH : lo < Hr :=
    cehETHHeightLower_lt_canonicalHeightRate hN0 hF hs hc hr hregC
  have hHq : Hr < quantitativeIFTHeight s c := by
    have h2' := h2
    rw [hHrdef, canonicalHeightRate, Real.rpow_sub_one hNr.ne']
    have hpow : 0 < (N : ℝ) ^ ξ := Real.rpow_pos_of_pos hNr ξ
    have h2'' : (N : ℝ) ^ ξ * (2 * Real.pi / c) <
        (N : ℝ) * quantitativeIFTHeight s c := by
      have hcpi : 0 < c / (2 * Real.pi) := by positivity
      have := h2'
      rw [show (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
          (c / (2 * Real.pi)) =
          ((N : ℝ) * quantitativeIFTHeight s c) / ((N : ℝ) ^ ξ * (2 * Real.pi / c)) by
        field_simp] at this
      exact (one_lt_div (by positivity)).1 this
    rw [show 2 * Real.pi / c * ((N : ℝ) ^ ξ / (N : ℝ)) =
        ((N : ℝ) ^ ξ * (2 * Real.pi / c)) / (N : ℝ) by ring]
    rw [div_lt_iff₀ hNr]
    linarith
  -- window memberships
  have hwinIcc : ∀ k, |lam k - E₀| ≤ R → lam k ∈ Icc (E₀ - R) (E₀ + R) := by
    intro k hk
    rw [abs_le] at hk
    constructor <;> linarith
  have hwinIoo : ∀ k, |lam k - E₀| ≤ R → lam k ∈ Ioo (E₀ - r) (E₀ + r) := by
    intro k hk
    rw [abs_le] at hk
    constructor <;> linarith
  have hgridRe : ∀ a : Fin (m + 1),
      localETHRealGridPoint E₀ R m a ∈ Ioo (E₀ - r) (E₀ + r) := by
    intro a
    have := localETHRealGridPoint_mem_Icc (E₀ := E₀) hRpos.le hm a
    constructor <;> linarith [this.1, this.2]
  have hgridIm : ∀ b : Fin (m + 1),
      localETHHeightGridPoint lo Hr m b ∈ Icc lo Hr :=
    fun b => localETHHeightGridPoint_mem_Icc hloH.le hm b
  -- canonical heights
  set η : Fin N → ℝ := fun k =>
    (N : ℝ) ^ ξ * cehTypicalSpacing N hN (hermitianSpectrum hF) hs (lam k) with hηdef
  have hηmem : ∀ k, |lam k - E₀| ≤ R → η k ∈ Icc lo Hr := by
    intro k hk
    exact canonicalHeight_mem_Icc_of_regularWindow hN hF hs hc hξ hregC
      (hwinIoo k hk) h2
  have hspec : ∀ k, localETHSpectralPoint N etaF ξ (lam k) =
      ((lam k : ℝ) : ℂ) + ((η k : ℝ) : ℂ) * Complex.I := by
    intro k
    rw [hetaEq]
    rfl
  -- snapping
  have hsnap : ∀ k, |lam k - E₀| ≤ R → ∃ a : Fin (m + 1) × Fin (m + 1),
      ‖(((lam k : ℝ) : ℂ) + ((η k : ℝ) : ℂ) * Complex.I) -
        cehETHGrid N E₀ β ξ s c m a‖ ≤ ρ := by
    intro k hk
    obtain ⟨a, ha⟩ := exists_localETHRectangularSpectralGridPoint_near
      hRpos hloH hm hm (hwinIcc k hk) (hηmem k hk)
    exact ⟨a, by simpa [cehETHGrid, hρdef, cehETHMeshRadius] using ha⟩
  -- grid-point facts
  have hgrid_im_pos : ∀ a : Fin (m + 1) × Fin (m + 1),
      (cehETHGrid N E₀ β ξ s c m a).im ≠ 0 := by
    intro a
    rw [cehETHGrid_eq]
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero]
    exact (hlopos.trans_le (hgridIm a.2).1).ne'
  have hMfgrid : ∀ a, Mf (cehETHGrid N E₀ β ξ s c m a) =
      Mc (cehETHGrid N E₀ β ξ s c m a) := fun a =>
    localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf (hgrid_im_pos a)
  have hobs : ∀ a b, cehETHRegularizedObservable s Mf
      (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) J =
      cehETHRegularizedObservable s Mc
        (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) J := by
    intro a b
    unfold cehETHRegularizedObservable
    rw [hMfgrid a, hMfgrid b]
  have hhalf : ∀ a : Fin (m + 1) × Fin (m + 1),
      c / 2 < (upperBranch hN0 (hermitianSpectrum hF) hs
        (((localETHRealGridPoint E₀ R m a.1 : ℝ) : ℂ) +
          ((localETHHeightGridPoint lo Hr m a.2 : ℝ) : ℂ) * Complex.I)).im := by
    intro a
    obtain ⟨hb, _, _, hdens, _, hstab⟩ := hdata _ (hgridRe a.1)
    exact half_lt_im_upperBranch_of_boundary hN0 hF hs hc hb hdens hstab
      (hlopos.trans_le (hgridIm a.2).1) ((hgridIm a.2).2.trans hHq.le)
  have hΛ : ∀ a b, ‖cehETHRegularizedObservable s Mc
      (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) J‖ ≤
      1 + 8 / (s * c ^ 2) := by
    intro a b
    rw [cehETHGrid_eq, cehETHGrid_eq]
    exact norm_cehETHRegularizedObservable_le hN0 hF hs hc (hhalf a) (hhalf b)
      (hlopos.trans_le (hgridIm a.2).1) (hlopos.trans_le (hgridIm b.2).1) J hJ
  -- the common contradiction argument
  have hHor_mono : ∀ t : ℝ, 0 ≤ t → t ≤ ρ →
      (1 + s * K) * t * (s * c)⁻¹ ^ 2 ≤ (1 + s * K) * ρ * (s * c)⁻¹ ^ 2 := by
    intro t _ ht
    gcongr
  have hT : 0 ≤ T := by positivity
  have hkey : ∀ (a b : Fin (m + 1) × Fin (m + 1)),
      ‖(((lam i : ℝ) : ℂ) + ((η i : ℝ) : ℂ) * Complex.I) -
        cehETHGrid N E₀ β ξ s c m a‖ ≤ ρ →
      ‖(((lam j : ℝ) : ℂ) + ((η j : ℝ) : ℂ) * Complex.I) -
        cehETHGrid N E₀ β ξ s c m b‖ ≤ ρ →
      ¬ CEHFixedPointPositiveChainBad s ε Mf F.1 J
        (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) G →
      ‖spectralMatrixElement u (cehETHRegularizedObservable s Mc
        (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) J) i j‖ < T / 2 := by
    intro a b ha hb hnot
    set A := cehETHRegularizedObservable s Mc
      (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) J
    have hnot' : ‖cehPositiveChain (F.1 + G.1) (cehETHGrid N E₀ β ξ s c m a)
        (cehETHGrid N E₀ β ξ s c m b) A‖ < (N : ℝ) ^ ε := by
      unfold CEHFixedPointPositiveChainBad at hnot
      rw [hobs a b] at hnot
      exact lt_of_not_ge hnot
    have hηi := hηmem i hi
    have hηj := hηmem j hj
    have hext := norm_spectralMatrixElement_sq_le_cehPositiveChain hN0 hfam
      (hlopos.trans_le hηi.1) (hlopos.trans_le hηj.1) A i j
    have him : ∀ x : Fin (m + 1) × Fin (m + 1),
        lo ≤ (cehETHGrid N E₀ β ξ s c m x).im := by
      intro x
      rw [cehETHGrid_eq]
      simpa using (hgridIm x.2).1
    have hmod := norm_cehPositiveChain_sub_le hN0 (F.1 + G.1) (hF.add G.2) hlopos
      (z₁ := ((lam i : ℝ) : ℂ) + ((η i : ℝ) : ℂ) * Complex.I)
      (z₂ := ((lam j : ℝ) : ℂ) + ((η j : ℝ) : ℂ) * Complex.I)
      (by simpa using hηi.1) (by simpa using hηj.1) (him a) (him b) ha hb A
    have hAnorm : ‖A‖ ≤ 1 + 8 / (s * c ^ 2) := hΛ a b
    set P := cehPositiveChain (F.1 + G.1)
      (((lam i : ℝ) : ℂ) + ((η i : ℝ) : ℂ) * Complex.I)
      (((lam j : ℝ) : ℂ) + ((η j : ℝ) : ℂ) * Complex.I) A
    set Pw := cehPositiveChain (F.1 + G.1) (cehETHGrid N E₀ β ξ s c m a)
      (cehETHGrid N E₀ β ξ s c m b) A
    have hP : ‖P‖ ≤ (N : ℝ) ^ ε + 2 * ρ * lo⁻¹ ^ 3 * (1 + 8 / (s * c ^ 2)) ^ 2 := by
      have h0 : ‖P‖ ≤ ‖Pw‖ + ‖P - Pw‖ := by
        calc ‖P‖ = ‖Pw + (P - Pw)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans ha
      have hmod' : ‖P - Pw‖ ≤ 2 * ρ * lo⁻¹ ^ 3 * (1 + 8 / (s * c ^ 2)) ^ 2 := by
        refine hmod.trans ?_
        gcongr
      linarith
    have hηprod : (N : ℝ) * η i * η j ≤ (N : ℝ) * Hr ^ 2 := by
      have := mul_le_mul hηi.2 hηj.2 (hlopos.le.trans hηj.1) (hlopos.le.trans hloH.le)
      nlinarith
    have hsq : ‖spectralMatrixElement u A i j‖ ^ 2 < (T / 2) ^ 2 := by
      have hPnn : 0 ≤ ‖P‖ := norm_nonneg _
      calc ‖spectralMatrixElement u A i j‖ ^ 2 ≤ (N : ℝ) * η i * η j * ‖P‖ := hext
        _ ≤ (N : ℝ) * Hr ^ 2 * ‖P‖ := mul_le_mul_of_nonneg_right hηprod hPnn
        _ ≤ (N : ℝ) * Hr ^ 2 *
            ((N : ℝ) ^ ε + 2 * ρ * lo⁻¹ ^ 3 * (1 + 8 / (s * c ^ 2)) ^ 2) := by
          gcongr
        _ < T ^ 2 / 4 := h6
        _ = (T / 2) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  by_cases hij : i = j
  · subst hij
    obtain ⟨a, ha⟩ := hsnap i hi
    refine ⟨a, a, ?_⟩
    by_contra hnot
    have hme := hkey a a ha ha hnot
    -- identify the matrix element with the center-shifted overlap
    set xa := localETHRealGridPoint E₀ R m a.1
    set ya := localETHHeightGridPoint lo Hr m a.2
    have hya : 0 < ya := hlopos.trans_le (hgridIm a.2).1
    obtain ⟨hb, _, _, hdens, _, hstab⟩ := hdata xa (hgridRe a.1)
    obtain ⟨hself, hratio⟩ := cehETHRegularizedObservable_self_eq hN0 hF hs hc hb hdens
      hstab hya ((hgridIm a.2).2.trans hHq.le) ((hgridIm a.2).2.trans h3) J
    have hgrid : cehETHGrid N E₀ β ξ s c m a =
        ((xa : ℝ) : ℂ) + ((ya : ℝ) : ℂ) * Complex.I := cehETHGrid_eq _ _ _ _ _ _ _ a
    rw [hgrid, hself, spectralMatrixElement_regularizedObservable hfam, ite_eq_left rfl,
      hratio] at hme
    -- the published error
    have herr : localETHError Mf etaF ξ J lam u i i =
        ‖star (u i) ⬝ᵥ (J *ᵥ u i) -
          NTrace (localETHGamma (Mc (((lam i : ℝ) : ℂ) + ((η i : ℝ) : ℂ) * Complex.I)) * J)‖ := by
      rw [localETHError_eq_canonicalSpacing hN hF hs hMf hetaF]
      unfold localETHError localETHCenter
      rw [ite_eq_left rfl, ← hspec i, hetaEq]
    -- center comparison
    have hdist : |xa - lam i| ≤ ρ := by
      have h := Complex.abs_re_le_norm
        ((((lam i : ℝ) : ℂ) + ((η i : ℝ) : ℂ) * Complex.I) -
          cehETHGrid N E₀ β ξ s c m a)
      rw [hgrid] at h ha
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero] at h
      rw [abs_sub_comm]
      exact h.trans ha
    have hηi := hηmem i hi
    have hcen := norm_gridCenter_sub_canonicalCenter_le hN0 hF hs hc hdata hHq.le
      (hwinIoo i hi) (hgridRe a.1) (hlopos.trans_le hηi.1) hηi.2 hya (hgridIm a.2).2
      (by linarith [hHor_mono |xa - lam i| (abs_nonneg _) hdist]) J hJ
    have hcen' : ‖NTrace (localETHGamma (Mc (((xa : ℝ) : ℂ) + ((ya : ℝ) : ℂ) * Complex.I)) * J) -
        NTrace (localETHGamma (Mc (((lam i : ℝ) : ℂ) + ((η i : ℝ) : ℂ) * Complex.I)) * J)‖ ≤
        T / 2 := by
      refine hcen.trans (le_trans ?_ h5)
      have hL : 0 ≤ 2 / c + 2 * K / c ^ 2 := by positivity
      gcongr
    have htri : localETHError Mf etaF ξ J lam u i i ≤
        ‖star (u i) ⬝ᵥ (J *ᵥ u i) - ((1 : ℝ) : ℂ) *
          NTrace (localETHGamma (Mc (((xa : ℝ) : ℂ) + ((ya : ℝ) : ℂ) * Complex.I)) * J) * 1‖ +
          T / 2 := by
      rw [herr]
      set X := star (u i) ⬝ᵥ (J *ᵥ u i)
      set Cw := NTrace (localETHGamma (Mc (((xa : ℝ) : ℂ) + ((ya : ℝ) : ℂ) * Complex.I)) * J)
      set Cz := NTrace (localETHGamma (Mc (((lam i : ℝ) : ℂ) + ((η i : ℝ) : ℂ) * Complex.I)) * J)
      have : X - Cz = (X - ((1 : ℝ) : ℂ) * Cw * 1) + (Cw - Cz) := by push_cast; ring
      rw [this]
      exact (norm_add_le _ _).trans (by linarith [hcen'])
    linarith
  · obtain ⟨a, ha⟩ := hsnap i hi
    obtain ⟨b, hb⟩ := hsnap j hj
    refine ⟨a, b, ?_⟩
    by_contra hnot
    have hme := hkey a b ha hb hnot
    unfold cehETHRegularizedObservable at hme
    rw [spectralMatrixElement_regularizedObservable hfam, ite_eq_right hij, mul_zero,
      sub_zero] at hme
    have herr : localETHError Mf etaF ξ J lam u i j = ‖star (u i) ⬝ᵥ (J *ᵥ u j)‖ := by
      unfold localETHError
      rw [ite_eq_right hij, sub_zero]
    linarith

/-!
## Probability assembly
-/

/-- The squared cardinality of the polynomial rectangular grid with `N^4`
steps in each direction is at most `N^20`. -/
theorem rectangularGrid_card_sq_le_rpow {N : ℕ} (hN : 2 ≤ N) :
    (((((N ^ 4 + 1) * (N ^ 4 + 1)) ^ 2 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (20 : ℝ) := by
  have h5 : N ^ 4 + 1 ≤ N ^ 5 := by
    have h1 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ (by omega)
    calc N ^ 4 + 1 ≤ N ^ 4 + N ^ 4 := by omega
      _ = N ^ 4 * 2 := by ring
      _ ≤ N ^ 4 * N := Nat.mul_le_mul_left _ hN
      _ = N ^ 5 := by ring
  have hnat : ((N ^ 4 + 1) * (N ^ 4 + 1)) ^ 2 ≤ N ^ 20 := by
    calc ((N ^ 4 + 1) * (N ^ 4 + 1)) ^ 2 ≤ (N ^ 5 * N ^ 5) ^ 2 := by gcongr
      _ = N ^ 20 := by ring
  rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast hnat

/-- **Extraction at a small height exponent, from grid-pair tails.**  If the
order-one positive-chain bound `N^(δ-ξ)` fails with probability at most
`N^(-(D+20))` at every ordered pair of points of the `N^4` rectangular grid
(uniformly as below), then for every `0 < ξ < δ`, `ξ < 1/2`, the bad
event at `(ξ, δ)` has `GUE_N(s/N)` probability at most `N^(-D)`, eventually
in `N` and uniformly in exactly the quantifiers of
`LocalETHRegularWindowBound`. -/
theorem measure_localETHWindowBad_le_of_gridTail
    (gue : LocalETHGUEFamily)
    {κ C sLo sHi r c K β ξ δ D : ℝ}
    (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hc : 0 < c) (hK : 0 < K)
    (hβ : β < 1) (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hξδ : ξ < δ)
    (hgrid : ∃ Ng : ℕ, ∀ N : ℕ, Ng ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      ∀ a b : Fin (N ^ 4 + 1) × Fin (N ^ 4 + 1),
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | CEHFixedPointPositiveChainBad s (δ - ξ) Mf F.1 J
              (cehETHGrid N E₀ β ξ s c (N ^ 4) a)
              (cehETHGrid N E₀ β ξ s c (N ^ 4) b) G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-(D + 20)))) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  set ε : ℝ := δ - ξ with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨Nlaw, hNlaw⟩ := hgrid
  obtain ⟨Ndet, hNdet⟩ := eventually_atTop.1
    (eventually_cehETHGridScalarConditions (δ := δ) (ε := ε) hsLo hsHi hr hc hK hβ
      hξ hξhalf hε (by rw [hεdef]; linarith))
  refine ⟨max Nlaw Ndet, ?_⟩
  intro N hN s hs hsH F hFdef Mf hMf etaF hetaF E₀ hreg J hJh hJ
  obtain ⟨hN4, hall⟩ := hNdet N (le_of_max_le_right hN)
  obtain ⟨hcond, -, -⟩ := hall s hs hsH
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set m : ℕ := N ^ 4 with hmdef
  have hm : 0 < m := by positivity
  set grid := cehETHGrid N E₀ β ξ s c m with hgriddef
  set μ := (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
  set p : ℝ≥0∞ := ENNReal.ofReal ((N : ℝ) ^ (-(D + 20)))
  have hpair : ∀ a b : Fin (m + 1) × Fin (m + 1),
      μ {G | CEHFixedPointPositiveChainBad s ε Mf F.1 J (grid a) (grid b) G} ≤ p := by
    intro a b
    exact hNlaw N (le_of_max_le_left hN) s hs hsH F hFdef Mf hMf E₀ hreg J hJh hJ a b
  have hsub : {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ⊆
      ⋃ a : Fin (m + 1) × Fin (m + 1), ⋃ b : Fin (m + 1) × Fin (m + 1),
        {G | CEHFixedPointPositiveChainBad s ε Mf F.1 J (grid a) (grid b) G} := by
    intro G hG
    obtain ⟨a, b, hab⟩ := exists_gridPositiveChainBad_of_localETHWindowBad hN4 hs0 F hMf
      hetaF hr hc hξ.le hreg J hJ hm hcond G hG
    exact mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨b, hab⟩⟩
  calc μ {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G}
      ≤ μ (⋃ a : Fin (m + 1) × Fin (m + 1), ⋃ b : Fin (m + 1) × Fin (m + 1),
          {G | CEHFixedPointPositiveChainBad s ε Mf F.1 J (grid a) (grid b) G}) :=
        measure_mono hsub
    _ ≤ ∑ a : Fin (m + 1) × Fin (m + 1), ∑ b : Fin (m + 1) × Fin (m + 1),
          μ {G | CEHFixedPointPositiveChainBad s ε Mf F.1 J (grid a) (grid b) G} :=
        (measure_iUnion_fintype_le μ _).trans
          (Finset.sum_le_sum fun a _ => measure_iUnion_fintype_le μ _)
    _ ≤ ∑ _a : Fin (m + 1) × Fin (m + 1), ∑ _b : Fin (m + 1) × Fin (m + 1), p := by
        gcongr with a _ b _
        exact hpair a b
    _ = ((((m + 1) * (m + 1)) ^ 2 : ℕ) : ℝ≥0∞) * p := by
        simp [Finset.sum_const, Finset.card_univ, pow_two, mul_assoc]
    _ = ENNReal.ofReal ((((((m + 1) * (m + 1)) ^ 2 : ℕ) : ℝ)) *
          (N : ℝ) ^ (-(D + 20))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have hcard := rectangularGrid_card_sq_le_rpow (N := N) (by omega)
        calc (((((m + 1) * (m + 1)) ^ 2 : ℕ) : ℝ)) * (N : ℝ) ^ (-(D + 20))
            ≤ (N : ℝ) ^ (20 : ℝ) * (N : ℝ) ^ (-(D + 20)) := by
              gcongr
          _ = (N : ℝ) ^ (-D) := by
              rw [← Real.rpow_add hNr]
              congr 1
              ring

/-- The rectangular grid points lie in the regular window and in the
deterministic height interval. -/
theorem cehETHGrid_mem {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    {F : LocalETHMatrix N} (hF : F.IsHermitian) {E₀ r c K β ξ : ℝ}
    (hr : 0 < r) (hc : 0 < c)
    (hregC : LocalETHRegularBoundaryWindow s (hermitianMDEBranch hF hs) E₀ r c K)
    (hR : (N : ℝ) ^ (β - 1) < r) {m : ℕ} (hm : 0 < m)
    (a : Fin (m + 1) × Fin (m + 1)) :
    (cehETHGrid N E₀ β ξ s c m a).re ∈
        Icc (E₀ - (N : ℝ) ^ (β - 1)) (E₀ + (N : ℝ) ^ (β - 1)) ∧
      (cehETHGrid N E₀ β ξ s c m a).re ∈ Ioo (E₀ - r) (E₀ + r) ∧
      cehETHHeightLower N ξ s ≤ (cehETHGrid N E₀ β ξ s c m a).im ∧
      (cehETHGrid N E₀ β ξ s c m a).im ≤ canonicalHeightRate N ξ c ∧
      0 < cehETHHeightLower N ξ s := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hRpos : 0 < (N : ℝ) ^ (β - 1) := Real.rpow_pos_of_pos hNr _
  have hloH : cehETHHeightLower N ξ s < canonicalHeightRate N ξ c :=
    cehETHHeightLower_lt_canonicalHeightRate hN hF hs hc hr hregC
  have hlopos : 0 < cehETHHeightLower N ξ s := by
    unfold cehETHHeightLower
    exact mul_pos (Real.rpow_pos_of_pos hNr ξ)
      (div_pos (mul_pos Real.pi_pos (Real.sqrt_pos.2 hs)) hNr)
  have h := localETHRealGridPoint_mem_Icc (E₀ := E₀) hRpos.le hm a.1
  have h' := localETHHeightGridPoint_mem_Icc hloH.le hm a.2
  have hre : (cehETHGrid N E₀ β ξ s c m a).re =
      localETHRealGridPoint E₀ ((N : ℝ) ^ (β - 1)) m a.1 := by
    rw [cehETHGrid_eq]; simp
  have him : (cehETHGrid N E₀ β ξ s c m a).im = localETHHeightGridPoint
      (cehETHHeightLower N ξ s) (canonicalHeightRate N ξ c) m a.2 := by
    rw [cehETHGrid_eq]; simp
  rw [hre, him]
  refine ⟨h, ⟨by linarith [h.1], by linarith [h.2]⟩, h'.1, h'.2, hlopos⟩

/-- **Extraction at a small height exponent.**  If the fixed-point positive
chain law holds, then for every `0 < ξ < δ`, `ξ < 1/2`, the bad
event at `(ξ, δ)` has `GUE_N(s/N)` probability at most `N^(-D)`, eventually
in `N` and uniformly in exactly the quantifiers of
`LocalETHRegularWindowBound`. -/
theorem measure_localETHWindowBad_le_of_fixedPointPositiveChainLaw
    (gue : LocalETHGUEFamily) (hlaw : CEHFixedPointPositiveChainLaw gue)
    {κ C sLo sHi r c K β ξ δ D : ℝ} (hκ : 0 ≤ κ) (hC : 0 < C)
    (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hc : 0 < c) (hK : 0 < K)
    (hβ : β < 1) (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hξδ : ξ < δ) (hD : 0 < D) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hε : 0 < δ - ξ := by linarith
  refine measure_localETHWindowBad_le_of_gridTail gue hsLo hsHi hr hc hK hβ hξ hξhalf
    hξδ ?_
  obtain ⟨Nlaw, hNlaw⟩ := hlaw κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK
    (ξ / 2) (2 * ξ) (by positivity) (by linarith) (by linarith)
    (δ - ξ) (D + 20) hε (by linarith)
  obtain ⟨Ndet, hNdet⟩ := eventually_atTop.1
    (eventually_cehETHGridScalarConditions (δ := δ) (ε := δ - ξ) hsLo hsHi hr hc hK hβ
      hξ hξhalf hε (by linarith))
  refine ⟨max Nlaw Ndet, ?_⟩
  intro N hN s hs hsH F hFdef Mf hMf E₀ hreg J hJh hJ a b
  obtain ⟨hN4, hall⟩ := hNdet N (le_of_max_le_right hN)
  obtain ⟨hcond, hlo, hHup⟩ := hall s hs hsH
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch F.2 hs0 hMf hreg
  have hma := cehETHGrid_mem (ξ := ξ) (by omega) hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) a
  have hmb := cehETHGrid_mem (ξ := ξ) (by omega) hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) b
  exact hNlaw N (le_of_max_le_left hN) s hs hsH F hFdef Mf hMf E₀ hreg
    _ _ hma.2.1 hmb.2.1 (hlo.trans hma.2.2.1) (hma.2.2.2.1.trans hHup)
    (hlo.trans hmb.2.2.1) (hmb.2.2.2.1.trans hHup) J hJh hJ

/-!
## The final source-shaped theorem
-/

/-- **CEH ETH extraction, final rectangular-grid form.**

Source: Cipolloni–Erdős–Henheik, proof of Theorem 2.5 from Theorem 4.2,
specialized to the the external ETH theorem
(`LocalETHRegularWindowBound`, normalized trace, `GUE_N(s/N)`, CEH spectral
point `x + i N^ξ η_f(x)`, threshold `N^δ N^(-1/2)`, tail `N^(-D)`).

The only hypothesis is `CEHFixedPointPositiveChainLaw gue`, the order-one
stochastic-domination bound for the positive two-resolvent chain
`⟨Im G(z₁) A° Im G(z₂) A°*⟩` at deterministic spectral parameters with the
CEH regularized observable `A°` of Definition 5.1.  All deterministic steps
are proved: canonicalization of the MDE branch and the typical spacing, the
deterministic canonical-height rectangle, snapping to a polynomial product
grid, the positive spectral extraction, the resolvent modulus of the chain,
the identification of the diagonal regularization with the published center
(coefficient `θ = 1` at coincident points), MDE continuity of the center on
the rectangle, the `N^20` union cost, and the reduction of an arbitrary loss
exponent `δ` to a small auxiliary height exponent.  The quantifier order is
that of `LocalETHRegularWindowBound`: the cutoff depends only on
`κ, C, sLo, sHi, r, c, K, β, ξ, δ, D` and is uniform in
`N, s, F, Mf, etaF, E₀, J`.  The theorem holds for an arbitrary family `gue`;
no simple-spectrum or eigenbasis-choice argument is needed because the
spectral extraction bound holds for every orthonormal eigenfamily. -/
theorem localETHRegularWindowBound_of_fixedPointPositiveChainLaw
    (gue : LocalETHGUEFamily) (hlaw : CEHFixedPointPositiveChainLaw gue) :
    LocalETHRegularWindowBound gue := by
  intro κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK β hβ hβ2 ξ hξ hξβ δ D hδ hD
  set ξ' : ℝ := min ξ (δ / 4) with hξ'def
  have hξ'pos : 0 < ξ' := lt_min hξ (by positivity)
  have hξ'ξ : ξ' ≤ ξ := min_le_left _ _
  have hξ'δ : ξ' ≤ δ / 4 := min_le_right _ _
  have hβ1 : β < 1 := lt_of_le_of_lt hβ2 (by norm_num)
  exact CEH.localETHWindowBad_polynomialTail_of_auxiliaryLoss gue
    (ξ' := ξ') (δ' := δ / 2) hsLo hr hc hK hξ hξβ hβ2 hξ'pos.le hξ'ξ hδ (by linarith)
    (measure_localETHWindowBad_le_of_fixedPointPositiveChainLaw gue hlaw hκ hC hsLo
      hsHi hr hc hK hβ1 hξ'pos (by linarith) (by linarith) hD)

/-- The published conditional local-ETH input follows from the fixed-point
positive-chain law alone. -/
theorem localETHInput_of_fixedPointPositiveChainLaw
    (gue : LocalETHGUEFamily) (hlaw : CEHFixedPointPositiveChainLaw gue) :
    LocalETHInput gue :=
  ⟨localETHRegularWindowBound_of_fixedPointPositiveChainLaw gue hlaw⟩

/-!
## The CEH Theorem 4.2 positive-chain law
-/

/-- The self-consistent density `ρ = π⁻¹ ⟨Im M⟩`, as in CEH Lemma 5.6. -/
def cehDensityOf {N : ℕ} (M : LocalETHMatrix N) : ℝ :=
  (NTrace (matrixImaginaryPart M)).re / Real.pi

/-- The CEH (5.18) error scale `ρ₁ ρ₂ s₂² / √(N ℓ)`, with
`ℓ = min (η₁ ρ₁) (η₂ ρ₂)`, `λ = √s`, the CEH cutoff `θ(z₁,z₂)` in `s₂`, and
the regularized observable `A°` of `cehETHRegularizedObservable`. -/
def cehTwoResolventLawScale {N : ℕ} (s : ℝ) (Mf : ℂ → LocalETHMatrix N)
    (z₁ z₂ : ℂ) (J : LocalETHMatrix N) : ℝ :=
  cehDensityOf (Mf z₁) * cehDensityOf (Mf z₂) *
      sTwo (regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ)
        (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)
        (cehETHRegularizedObservable s Mf z₁ z₂ J) ^ 2 /
    Real.sqrt ((N : ℝ) *
      min (z₁.im * cehDensityOf (Mf z₁)) (z₂.im * cehDensityOf (Mf z₂)))

/-- The CEH positive two-resolvent error `⟨(Im G₁ A° Im G₂ - M̂₁₂) A°*⟩` at a
fixed pair of spectral parameters for the sample `F + G`. -/
def cehTwoResolventLawError {N : ℕ} (s : ℝ) (Mf : ℂ → LocalETHMatrix N)
    (F J : LocalETHMatrix N) (z₁ z₂ : ℂ) (G : HermitianMatrix (Fin N)) : ℂ :=
  positiveChainError (Real.sqrt s : ℂ)
    (cehHermitianResolvent (F + G.1) z₁) (Mf z₁)
    (cehETHRegularizedObservable s Mf z₁ z₂ J)
    (cehHermitianResolvent (F + G.1) z₂) (Mf z₂)

/-- Failure of CEH Theorem 4.2 (5.18) at one fixed pair: the positive-chain
error exceeds `N^ε` times its error scale. -/
def CEHTwoResolventLawBad {N : ℕ} (s ε : ℝ) (Mf : ℂ → LocalETHMatrix N)
    (F J : LocalETHMatrix N) (z₁ z₂ : ℂ) (G : HermitianMatrix (Fin N)) : Prop :=
  (N : ℝ) ^ ε * cehTwoResolventLawScale s Mf z₁ z₂ J <
    ‖cehTwoResolventLawError s Mf F J z₁ z₂ G‖

/-- **The fixed-point CEH two-resolvent law** (the sole hypothesis
of `localETHRegularWindowBound_of_twoResolventPositiveChainLaw`).

Source: Cipolloni–Erdős–Henheik, Theorem 4.2, positive-chain estimate
(5.18) `Ψ₂ ≺ 1` with `Ψ₂ = √(Nℓ)/(ρ₁ρ₂s₂²) |⟨(Im G₁ A Im G₂ - M̂₁₂) A*⟩|`,
written multiplicatively (no division by `s₂`):
`|⟨(Im G₁ A° Im G₂ - M̂₁₂) A°*⟩| ≤ N^ε ρ₁ ρ₂ s₂² / √(Nℓ)` with probability at
least `1 - N^(-D)`.  Here `M̂₁₂ = positiveDeterministicApprox` (CEH (5.12)),
`A°` is the CEH regularization (Definition 5.1) of a fixed Hermitian `J`,
`‖J‖ ≤ 1`, at the same pair, `s₂ = sTwo θ(z₁,z₂)` with CEH's cutoff `θ`,
`ρᵢ = π⁻¹ ⟨Im M(zᵢ)⟩` and `ℓ = min (ηᵢ ρᵢ)`.

Normalization: `GUE_N(s/N)`, sample `F + G`, resolvent `(F + G - z)⁻¹`,
normalized trace, `λ = √s`, MDE branch `Mf`.

Quantifiers and uniformity: the cutoff `N₀` depends only on
`κ, C, sLo, sHi, r, c, K, ε₀, ε₁, ε, D`; for `N ≥ N₀` the bound is uniform in
`s ∈ [sLo, sHi]`, the deformation with `‖F‖ ≤ C N^κ √s`, the MDE branch, the
regular boundary window center `E₀`, the deterministic pair with real parts
in `(E₀ - r, E₀ + r)` and heights in `[N^(ε₀-1), N^(ε₁-1)]`, and `J`.  The
pair and the observable are fixed before the random matrix.  The spectral
domain is restricted to the regular window (a weakening of the source
domain, which only weakens this hypothesis). -/
def CEHTwoResolventPositiveChainLaw (gue : LocalETHGUEFamily) : Prop :=
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
    ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
          {G | CEHTwoResolventLawBad s ε Mf F.1 J z₁ z₂ G} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-!
## Lemma 5.6 on the regular rectangle
-/

section SpectralConj

variable {N : ℕ}

/-- Conjugation by a unitary preserves the normalized trace. -/
theorem spectralConj_NTrace (U : unitary (Matrix (Fin N) (Fin N) ℂ))
    (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (Unitary.conjStarAlgAut ℂ (Matrix (Fin N) (Fin N) ℂ) U X) = NTrace X := by
  rw [Unitary.conjStarAlgAut_apply]
  simp only [NTrace, CEHNative.BlockBand.Conventions.normalizedTrace]
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

variable (φ : Matrix (Fin N) (Fin N) ℂ ≃⋆ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ)
  (hφ : ∀ X, NTrace (φ X) = NTrace X)
include hφ

omit hφ in
theorem spectralConj_conjTranspose' (X : Matrix (Fin N) (Fin N) ℂ) :
    (φ X)ᴴ = φ Xᴴ := by
  simp only [← Matrix.star_eq_conjTranspose, map_star]

omit hφ in
theorem spectralConj_matrixImaginaryPart (X : Matrix (Fin N) (Fin N) ℂ) :
    matrixImaginaryPart (φ X) = φ (matrixImaginaryPart X) := by
  unfold matrixImaginaryPart
  rw [spectralConj_conjTranspose' φ, ← map_sub, map_smul]

omit hφ in
theorem spectralConj_chooseAdjoint (c : AdjointChoice) (X : Matrix (Fin N) (Fin N) ℂ) :
    chooseAdjoint c (φ X) = φ (chooseAdjoint c X) := by
  cases c
  · rfl
  · exact spectralConj_conjTranspose' φ X

theorem spectralConj_twoResolventApprox (l : ℂ) (A B C : Matrix (Fin N) (Fin N) ℂ) :
    twoResolventApprox l (φ A) (φ B) (φ C) = φ (twoResolventApprox l A B C) := by
  unfold twoResolventApprox
  have h := hφ
  simp only [NTrace] at h
  simp only [← map_mul, h, map_add, map_smul]

theorem spectralConj_positiveDeterministicApprox (l : ℂ) (A B C : Matrix (Fin N) (Fin N) ℂ) :
    positiveDeterministicApprox l (φ A) (φ B) (φ C) =
      φ (positiveDeterministicApprox l A B C) := by
  unfold positiveDeterministicApprox deterministicConstellation
  simp only [spectralConj_chooseAdjoint φ, spectralConj_twoResolventApprox φ hφ,
    map_add, map_sub, map_smul]

theorem spectralConj_regularizedObservable (t : ℝ) (A B C : Matrix (Fin N) (Fin N) ℂ) :
    regularizedObservable t (φ A) (φ B) (φ C) = φ (regularizedObservable t A B C) := by
  unfold regularizedObservable
  simp only [← map_mul, hφ, map_sub, map_smul, map_one]

theorem spectralConj_regularizationCoefficient (l : ℂ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    regularizationCoefficient l (φ A) (φ B) = regularizationCoefficient l A B := by
  unfold regularizationCoefficient
  rw [← map_mul, hφ]

theorem spectralConj_gammaMatrix (A : Matrix (Fin N) (Fin N) ℂ) :
    gammaMatrix (φ A) = φ (gammaMatrix A) := by
  unfold gammaMatrix
  rw [spectralConj_matrixImaginaryPart φ, hφ, map_smul]

theorem spectralConj_twoResolventObservable (c₁ c₂ : AdjointChoice)
    (A B C : Matrix (Fin N) (Fin N) ℂ) :
    twoResolventObservable c₁ c₂ (φ A) (φ B) (φ C) = twoResolventObservable c₁ c₂ A B C := by
  unfold twoResolventObservable twoResolventWord
  rw [spectralConj_chooseAdjoint φ, spectralConj_chooseAdjoint φ, ← map_mul, ← map_mul, hφ]

theorem spectralConj_sTwo (t : ℝ) (l : ℂ) (A B C : Matrix (Fin N) (Fin N) ℂ) :
    sTwo t l (φ A) (φ B) (φ C) = sTwo t l A B C := by
  unfold sTwo sTwoSq
  simp only [spectralConj_gammaMatrix φ hφ, spectralConj_twoResolventObservable φ hφ,
    spectralConj_conjTranspose' φ, ← map_mul, hφ]

theorem spectralConj_cehDensityOf (A : Matrix (Fin N) (Fin N) ℂ) :
    cehDensityOf (φ A) = cehDensityOf A := by
  unfold cehDensityOf
  rw [spectralConj_matrixImaginaryPart φ, hφ]

end SpectralConj

/-- **CEH Lemma 5.6, fifth bound, for the Hermitian branch.**  For
`θ(z₁,z₂) = 1` and the regularized observable `A° = A - ⟨M₁AM₂*⟩/⟨M₁M₂*⟩`,
`|⟨M̂₁₂ A°*⟩| ≤ 2π² ρ₁ ρ₂ s₂²`, with `λ = √s`.  Transferred by unitary
conjugation from the diagonal statement `lemma56_fifth_bound`. -/
theorem lemma56_fifth_bound_hermitianMDEBranch
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (J : LocalETHMatrix N)
    (htheta : regularizationCoefficient (Real.sqrt s : ℂ)
      (hermitianMDEBranch hF hs z₁) (hermitianMDEBranch hF hs z₂)ᴴ = 1) :
    ‖NTrace (positiveDeterministicApprox (Real.sqrt s : ℂ)
        (hermitianMDEBranch hF hs z₁)
        (regularizedObservable 1 (hermitianMDEBranch hF hs z₁)
          (hermitianMDEBranch hF hs z₂)ᴴ J)
        (hermitianMDEBranch hF hs z₂) *
      (regularizedObservable 1 (hermitianMDEBranch hF hs z₁)
          (hermitianMDEBranch hF hs z₂)ᴴ J)ᴴ)‖ ≤
      2 * Real.pi ^ 2 * cehDensityOf (hermitianMDEBranch hF hs z₁) *
        cehDensityOf (hermitianMDEBranch hF hs z₂) *
        sTwo 1 (Real.sqrt s : ℂ) (hermitianMDEBranch hF hs z₁)
          (hermitianMDEBranch hF hs z₂)
          (regularizedObservable 1 (hermitianMDEBranch hF hs z₁)
            (hermitianMDEBranch hF hs z₂)ᴴ J) ^ 2 := by
  obtain ⟨l, hl, rfl⟩ : ∃ l : ℝ, 0 < l ∧ l ^ 2 = s :=
    ⟨Real.sqrt s, Real.sqrt_pos.2 hs, Real.sq_sqrt hs.le⟩
  rw [Real.sqrt_sq hl.le] at htheta ⊢
  set φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin N) (Fin N) ℂ) hF.eigenvectorUnitary with hφdef
  have hφ : ∀ X, NTrace (φ X) = NTrace X := spectralConj_NTrace _
  have hM : ∀ {z : ℂ}, 0 < z.im → hermitianMDEBranch hF hs z =
      φ (PencilAdapter.mdeMatrix (hermitianSpectrum hF) l z
        (upperBranch hN (hermitianSpectrum hF) (sq_pos_of_pos hl) z)) := by
    intro z hz
    rw [hermitianMDEBranch_eq_spectralLift_upper hF hN hs hz]
    rfl
  have hJ : J = φ (φ.symm J) := (φ.apply_symm_apply J).symm
  rw [hM hz₁, hM hz₂] at htheta ⊢
  rw [hJ]
  rw [spectralConj_conjTranspose' φ, spectralConj_regularizationCoefficient φ hφ] at htheta
  have key := lemma56_fifth_bound hN (hermitianSpectrum hF) l hl hz₁ hz₂ (φ.symm J)
    .plain .plain htheta
  simp only [chooseAdjoint_plain] at key
  rw [spectralConj_conjTranspose' φ, spectralConj_regularizedObservable φ hφ,
    spectralConj_positiveDeterministicApprox φ hφ, spectralConj_conjTranspose' φ, ← map_mul, hφ,
    spectralConj_cehDensityOf φ hφ, spectralConj_cehDensityOf φ hφ, spectralConj_sTwo φ hφ]
  exact key

/-- The real part of the normalized trace of the matrix imaginary part
`(X - Xᴴ)/(2i)` is the imaginary part of the normalized trace of `X`. -/
theorem gridPair_re_NTrace_matrixImaginaryPart {N : ℕ} (M : LocalETHMatrix N) :
    (NTrace (matrixImaginaryPart M)).re = (NTrace M).im := by
  simp only [NTrace, Conventions.normalizedTrace, matrixImaginaryPart,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, smul_eq_mul]
  have hN : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hN]
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The CEH density of a spectral lift is `Im ⟨q⟩ / π`. -/
theorem gridPair_cehDensityOf_spectralLift {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (q : Fin N → ℂ) :
    cehDensityOf (spectralLift hF q) = (average q).im / Real.pi := by
  unfold cehDensityOf
  rw [gridPair_re_NTrace_matrixImaginaryPart]
  change (Conventions.normalizedTrace (spectralLift hF q)).im / Real.pi = _
  rw [normalizedTrace_spectralLift]

/-- **Deterministic CEH bounds at a pair on the regular rectangle.**  For
two points `xₖ + i ηₖ` of a regular boundary window below the IFT cutoff
whose MDE entries are within `δ` of the boundary entries at `x₁`, with the
explicit budgets on `δ`: CEH's cutoff is `θ = 1`, `s₂` is bounded by the
dimension-free `thetaOneSTwoBound`, and `c/(2π) ≤ ρₖ ≤ ((sc)⁻¹ + 1)/π`. -/
theorem regularWindow_pair_thetaOne_sTwo_density
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s E₀ r c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    {Mb Mb' : ℝ → LocalETHMatrix N}
    (hdata : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      Tendsto (fun η : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)) ∧
        HasLocalETHMatrixDerivAt Mb (Mb' x) x ∧
        ‖Mb' x‖ ≤ K ∧
        c ≤ (Conventions.normalizedTrace (Mb x)).im ∧
        ‖Mb x‖ ≤ K ∧
        c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb x * Mb x)‖)
    {x₁ x₂ η₁ η₂ δ : ℝ} (hx₁ : x₁ ∈ Ioo (E₀ - r) (E₀ + r))
    (hx₂ : x₂ ∈ Ioo (E₀ - r) (E₀ + r))
    (hη₁ : 0 < η₁) (hη₁H : η₁ ≤ quantitativeIFTHeight s c)
    (hη₂ : 0 < η₂) (hη₂H : η₂ ≤ quantitativeIFTHeight s c)
    (hv₁ : (η₁ + s * (8 * η₁ / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ ≤ δ)
    (hv₂ : (η₂ + s * (8 * η₂ / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ +
      (1 + s * K) * |x₂ - x₁| * (s * c)⁻¹ ^ 2 ≤ δ)
    (hδ1 : δ ≤ 1) (hδc : δ ≤ c / 2)
    (hbudget : s * (2 * (s * c)⁻¹ * δ + δ ^ 2) < 1 / 2)
    (hbudget' : s * (2 * (s * c)⁻¹ * δ + δ ^ 2) ≤ c / 2)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) :
    regularizationCoefficient (Real.sqrt s : ℂ)
        (hermitianMDEBranch hF hs ((x₁ : ℂ) + (η₁ : ℂ) * Complex.I))
        (hermitianMDEBranch hF hs ((x₂ : ℂ) + (η₂ : ℂ) * Complex.I))ᴴ = 1 ∧
    sTwo 1 (Real.sqrt s : ℂ)
        (hermitianMDEBranch hF hs ((x₁ : ℂ) + (η₁ : ℂ) * Complex.I))
        (hermitianMDEBranch hF hs ((x₂ : ℂ) + (η₂ : ℂ) * Complex.I))
        (regularizedObservable 1
          (hermitianMDEBranch hF hs ((x₁ : ℂ) + (η₁ : ℂ) * Complex.I))
          (hermitianMDEBranch hF hs ((x₂ : ℂ) + (η₂ : ℂ) * Complex.I))ᴴ J) ≤
      Real.sqrt (thetaOneSTwoBound ‖(Real.sqrt s : ℂ)‖ ((s * c)⁻¹ + 1) (c / 2)
        ((2 * s)⁻¹) (c / 2)) ∧
    c / (2 * Real.pi) ≤
      cehDensityOf (hermitianMDEBranch hF hs ((x₁ : ℂ) + (η₁ : ℂ) * Complex.I)) ∧
    cehDensityOf (hermitianMDEBranch hF hs ((x₁ : ℂ) + (η₁ : ℂ) * Complex.I)) ≤
      ((s * c)⁻¹ + 1) / Real.pi ∧
    c / (2 * Real.pi) ≤
      cehDensityOf (hermitianMDEBranch hF hs ((x₂ : ℂ) + (η₂ : ℂ) * Complex.I)) ∧
    cehDensityOf (hermitianMDEBranch hF hs ((x₂ : ℂ) + (η₂ : ℂ) * Complex.I)) ≤
      ((s * c)⁻¹ + 1) / Real.pi := by
  set f := hermitianSpectrum hF with hfdef
  obtain ⟨hdatabd₁, -, -, hdens₁, -, hstab₁⟩ := hdata x₁ hx₁
  obtain ⟨hdatabd₂, -, -, hdens₂, -, hstab₂⟩ := hdata x₂ hx₂
  obtain ⟨hsol₁, hMb₁, hstabId₁⟩ :=
    boundary_matrix_scalar_identification hF hN hs hc hdatabd₁ hdens₁
  obtain ⟨hsol₂, -, hstabId₂⟩ :=
    boundary_matrix_scalar_identification hF hN hs hc hdatabd₂ hdens₂
  set m₁ := Conventions.normalizedTrace (Mb x₁) with hm₁def
  set m₂ := Conventions.normalizedTrace (Mb x₂) with hm₂def
  have hbx (x : ℝ) (hbd : Tendsto
      (fun η : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (Mb x))) :
      Tendsto (fun t : ℝ => upperBranch hN f hs ((x : ℂ) + (t : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Conventions.normalizedTrace (Mb x))) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp hbd
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hF hN hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hF hN hs (by simpa using htpos')]
  have hstab₁' : c ≤ ‖BlockBand.CEH.stabilityDenominator f s (x₁ : ℂ) m₁‖ := by
    rw [← hstabId₁]
    exact hstab₁
  have hstab₂' : c ≤ ‖BlockBand.CEH.stabilityDenominator f s (x₂ : ℂ) m₂‖ := by
    rw [← hstabId₂]
    exact hstab₂
  set z₁ : ℂ := (x₁ : ℂ) + (η₁ : ℂ) * Complex.I with hz₁def
  set z₂ : ℂ := (x₂ : ℂ) + (η₂ : ℂ) * Complex.I with hz₂def
  set q₁ := entry f s z₁ (upperBranch hN f hs z₁) with hq₁def
  set q₂ := entry f s z₂ (upperBranch hN f hs z₂) with hq₂def
  set q₀ := entry f s (x₁ : ℂ) m₁ with hq₀def
  have hv₁i (i : Fin N) : ‖q₁ i - q₀ i‖ ≤
      (η₁ + s * (8 * η₁ / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ :=
    norm_upperBranch_entry_sub_boundary_le hN f hs hc hsol₁ hdens₁ hstab₁'
      (hbx x₁ hdatabd₁) hη₁ hη₁H i
  have hv₂i (i : Fin N) : ‖q₂ i - entry f s (x₂ : ℂ) m₂ i‖ ≤
      (η₂ + s * (8 * η₂ / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ :=
    norm_upperBranch_entry_sub_boundary_le hN f hs hc hsol₂ hdens₂ hstab₂'
      (hbx x₂ hdatabd₂) hη₂ hη₂H i
  have hK : 0 ≤ K := (norm_nonneg (Mb' x₁)).trans (hdata x₁ hx₁).2.2.1
  have hmxy : ‖m₂ - m₁‖ ≤ K * |x₂ - x₁| := by
    rcases le_total x₁ x₂ with hxy | hyx
    · have hseg : Icc x₁ x₂ ⊆ Ioo (E₀ - r) (E₀ + r) := by
        intro t ht
        exact ⟨hx₁.1.trans_le ht.1, ht.2.trans_lt hx₂.2⟩
      simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using
        norm_normalizedTrace_sub_le_of_regularDerivative hN
          hxy hseg (fun t ht => (hdata t ht).2.1)
          (fun t ht => (hdata t ht).2.2.1)
    · rw [norm_sub_rev, abs_sub_comm]
      have hseg : Icc x₂ x₁ ⊆ Ioo (E₀ - r) (E₀ + r) := by
        intro t ht
        exact ⟨hx₂.1.trans_le ht.1, ht.2.trans_lt hx₁.2⟩
      simpa [abs_of_nonneg (sub_nonneg.mpr hyx)] using
        norm_normalizedTrace_sub_le_of_regularDerivative hN
          hyx hseg (fun t ht => (hdata t ht).2.1)
          (fun t ht => (hdata t ht).2.2.1)
  have hhoriz (i : Fin N) : ‖entry f s (x₂ : ℂ) m₂ i - q₀ i‖ ≤
      (1 + s * K) * |x₂ - x₁| * (s * c)⁻¹ ^ 2 :=
    norm_boundary_entry_sub_le_of_mean_modulus f hs hc hK hdens₁ hdens₂ hmxy i
  have hq₁ (i : Fin N) : ‖q₁ i - q₀ i‖ ≤ δ := (hv₁i i).trans hv₁
  have hq₂ (i : Fin N) : ‖q₂ i - q₀ i‖ ≤ δ := by
    calc ‖q₂ i - q₀ i‖ =
          ‖(q₂ i - entry f s (x₂ : ℂ) m₂ i) + (entry f s (x₂ : ℂ) m₂ i - q₀ i)‖ := by
            congr 1; ring
      _ ≤ ‖q₂ i - entry f s (x₂ : ℂ) m₂ i‖ + ‖entry f s (x₂ : ℂ) m₂ i - q₀ i‖ :=
            norm_add_le _ _
      _ ≤ _ := add_le_add (hv₂i i) (hhoriz i)
      _ ≤ δ := hv₂
  have hq₀ (i : Fin N) : ‖q₀ i‖ ≤ (s * c)⁻¹ := by
    have hh : s * c ≤ effectiveHeight s (x₁ : ℂ) m₁ := by
      simp only [effectiveHeight, Complex.ofReal_im, zero_add]
      exact mul_le_mul_of_nonneg_left hdens₁ hs.le
    exact (norm_entry_le_inv_effectiveHeight f
      (lt_of_lt_of_le (mul_pos hs hc) hh) i).trans
      (inv_anti₀ (by positivity) hh)
  have hδ0 : 0 ≤ δ := (norm_nonneg (q₁ ⟨0, hN⟩ - q₀ ⟨0, hN⟩)).trans (hq₁ ⟨0, hN⟩)
  have hward := scaledPairing_boundary_eq_one hN f hs hsol₁
  have hpairScalar := scaledPairing_gt_half_of_uniform_close hN hs
    q₀ q₁ q₂ (by positivity) hδ0 hward hq₀ hq₁ hq₂ hbudget
  have hpair : 1 / 2 < (s * NTrace
      (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)).re := by
    rw [NTrace_spectralLift_mul_conjTranspose]
    simpa [scaledPairing] using hpairScalar
  have havgq₀ : average q₀ = m₁ := by
    rw [← normalizedTrace_spectralLift hF q₀, ← hMb₁]
  have hq₀im : c ≤ (average q₀).im := by
    rw [havgq₀]
    exact hdens₁
  have havg₁ : c / 2 ≤ (average q₁).im :=
    average_im_half_margin_of_uniform_close hN q₁ q₀ hc.le hq₀im hq₁ hδc
  have havg₂ : c / 2 ≤ (average q₂).im :=
    average_im_half_margin_of_uniform_close hN q₂ q₀ hc.le hq₀im hq₂ hδc
  have htrace₁ : c / 2 ≤ |(NTrace (spectralLift hF q₁)).im| := by
    change c / 2 ≤ |(Conventions.normalizedTrace (spectralLift hF q₁)).im|
    rw [normalizedTrace_spectralLift hF]
    exact havg₁.trans (le_abs_self _)
  have htrace₂ : c / 2 ≤ |(NTrace (spectralLift hF q₂)).im| := by
    change c / 2 ≤ |(Conventions.normalizedTrace (spectralLift hF q₂)).im|
    rw [normalizedTrace_spectralLift hF]
    exact havg₂.trans (le_abs_self _)
  have hqNorm (q : Fin N → ℂ) (hq : ∀ i, ‖q i - q₀ i‖ ≤ δ) (i : Fin N) :
      ‖q i‖ ≤ (s * c)⁻¹ + 1 := by
    calc
      ‖q i‖ = ‖(q i - q₀ i) + q₀ i‖ := by congr 1; ring
      _ ≤ ‖q i - q₀ i‖ + ‖q₀ i‖ := norm_add_le _ _
      _ ≤ δ + (s * c)⁻¹ := add_le_add (hq i) (hq₀ i)
      _ ≤ (s * c)⁻¹ + 1 := by linarith
  have hpairNorm : (2 * s)⁻¹ ≤ ‖NTrace
      (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)‖ :=
    mixedPairing_norm_ge_inv_two_mul hs _ _ hpair
  have hq₀den : c ≤ ‖1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)‖ := by
    rw [← normalizedTrace_spectralLift_mul hF q₀ q₀, ← hMb₁]
    exact hstab₁
  have hden : c / 2 ≤ ‖stabilityDenominator (Real.sqrt s : ℂ)
      (NTrace (spectralLift hF q₁ * spectralLift hF q₂))‖ := by
    change c / 2 ≤ ‖stabilityDenominator (Real.sqrt s : ℂ)
      (Conventions.normalizedTrace (spectralLift hF q₁ * spectralLift hF q₂))‖
    rw [normalizedTrace_spectralLift_mul]
    unfold stabilityDenominator
    have hsqrt : ((Real.sqrt s : ℂ) ^ 2) = (s : ℂ) := by
      norm_cast
      exact Real.sq_sqrt hs.le
    rw [hsqrt]
    exact ordinaryDenominator_half_margin hN hs.le hc.le
      q₀ q₁ q₂ (by positivity) hδ0 hq₀ hq₁ hq₂ hq₀den hbudget'
  obtain ⟨hθ, hS⟩ := thetaOneCompactClosure hN hF hs q₁ q₂ J
    (by positivity) (by positivity) (by positivity) (by positivity)
    (hqNorm q₁ hq₁) (hqNorm q₂ hq₂) htrace₁ htrace₂ hJ hpair hpairNorm hden
  have hz₁ : 0 < z₁.im := by simpa [hz₁def] using hη₁
  have hz₂ : 0 < z₂.im := by simpa [hz₂def] using hη₂
  have hM₁ : hermitianMDEBranch hF hs z₁ = spectralLift hF q₁ :=
    hermitianMDEBranch_eq_spectralLift_upper hF hN hs hz₁
  have hM₂ : hermitianMDEBranch hF hs z₂ = spectralLift hF q₂ :=
    hermitianMDEBranch_eq_spectralLift_upper hF hN hs hz₂
  have hupper (q : Fin N → ℂ) (hq : ∀ i, ‖q i - q₀ i‖ ≤ δ) :
      (average q).im ≤ (s * c)⁻¹ + 1 := by
    have hL : ‖spectralLift hF q‖ ≤ (s * c)⁻¹ + 1 :=
      norm_spectralLift_le_of_forall hF q (by positivity) (hqNorm q hq)
    have htr := norm_normalizedTrace_le_localETHNorm hN (spectralLift hF q)
    have heq : Conventions.normalizedTrace (spectralLift hF q) = average q :=
      normalizedTrace_spectralLift hF q
    rw [heq] at htr
    exact (Complex.im_le_norm _).trans (htr.trans hL)
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hM₁, hM₂, gridPair_cehDensityOf_spectralLift, gridPair_cehDensityOf_spectralLift]
  refine ⟨hθ, hS, ?_, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) hpi]
    nlinarith
  · exact div_le_div_of_nonneg_right (hupper q₁ hq₁) hpi.le
  · rw [div_le_div_iff₀ (by positivity) hpi]
    nlinarith
  · exact div_le_div_of_nonneg_right (hupper q₂ hq₂) hpi.le

/-- `thetaOneSTwoBound` is monotone in its first argument and in `L`, antitone in `p`. -/
theorem convCond_thetaOneSTwoBound_le {l l' L L' cΓ p p' d : ℝ}
    (hl : 0 ≤ l) (hll : l ≤ l') (hL : 0 ≤ L) (hLL : L ≤ L') (hcΓ : 0 < cΓ)
    (hp : 0 < p) (hpp : p ≤ p') (hd : 0 < d) :
    thetaOneSTwoBound l L cΓ p' d ≤ thetaOneSTwoBound l' L' cΓ p d := by
  have hL' : 0 ≤ L' := hL.trans hLL
  have hp' : 0 < p' := hp.trans_le hpp
  unfold thetaOneSTwoBound
  gcongr

/-- The scalar conditions of the Theorem 4.2 conversion hold eventually in
`N`, uniformly in `s ∈ [sLo, sHi]`; the cutoff depends only on
`sLo, sHi, c, K, β, ξ, ε`. -/
theorem eventually_cehTwoResolventLaw_conversionConditions
    {sLo sHi c K β ξ ε : ℝ} (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hc : 0 < c)
    (hK : 0 ≤ K) (hβ : β < 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      canonicalMixedEntryRate N ξ β s c K ≤ 1 ∧
      canonicalMixedEntryRate N ξ β s c K ≤ c / 2 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) < 1 / 2 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) ≤ c / 2 ∧
      1 ≤ (N : ℝ) * (cehETHHeightLower N ξ s * (c / (2 * Real.pi))) ∧
      (((s * c)⁻¹ + 1) / Real.pi) ^ 2 *
          thetaOneSTwoBound ‖(Real.sqrt s : ℂ)‖ ((s * c)⁻¹ + 1) (c / 2)
            ((2 * s)⁻¹) (c / 2) *
          (2 * Real.pi ^ 2 + (N : ℝ) ^ (ε / 2)) < (N : ℝ) ^ ε := by
  have hsHi0 : 0 < sHi := lt_of_lt_of_le hsLo hsHi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt sLo := Real.sqrt_pos.mpr hsLo
  set κ := canonicalVerticalRateConstant sLo c with hκdef
  have hκ : 0 < κ := canonicalVerticalRateConstant_pos hsLo hc
  set Bh := (1 + sHi * K) * 2 * (sLo * c)⁻¹ ^ 2 with hBhdef
  have hBh : 0 < Bh := by positivity
  set M := κ + Bh with hMdef
  have hM : 0 < M := by positivity
  set m := min (1 / 4 : ℝ) (c / 2) with hmdef
  have hm : 0 < m := by positivity
  set t := min 1 (min (c / 2) (m / (2 / c + sHi))) with htdef
  have ht : 0 < t := by positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htc : t ≤ c / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htm : (2 / c + sHi) * t ≤ m := by
    have : t ≤ m / (2 / c + sHi) := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  have hm4 : m ≤ 1 / 4 := min_le_left _ _
  have hmc : m ≤ c / 2 := min_le_right _ _
  set B₀ := (((sLo * c)⁻¹ + 1) / Real.pi) ^ 2 *
    thetaOneSTwoBound (Real.sqrt sHi) ((sLo * c)⁻¹ + 1) (c / 2) ((2 * sHi)⁻¹) (c / 2)
    with hB₀def
  have hB₀ : 0 < B₀ := by
    rw [hB₀def]; unfold thetaOneSTwoBound
    have : 0 < Real.sqrt sHi := Real.sqrt_pos.mpr hsHi0
    positivity
  filter_upwards [eventually_ge_atTop 1,
    eventually_natCast_rpow_le_mul_rpow (a := ξ - 1) (b := 0) (by linarith)
      (by positivity : 0 < t / M),
    eventually_natCast_rpow_le_mul_rpow (a := β - 1) (b := 0) (by linarith)
      (by positivity : 0 < t / M),
    eventually_natCast_rpow_le_mul_rpow (a := 0) (b := ξ) hξ
      (by positivity : 0 < c * Real.sqrt sLo / 2),
    eventually_natCast_rpow_le_mul_rpow (a := ε / 2) (b := ε) (by linarith)
      (by positivity : 0 < 1 / (2 * B₀)),
    eventually_natCast_rpow_le_mul_rpow (a := 0) (b := ε) hε
      (by positivity : 0 < 1 / (8 * Real.pi ^ 2 * B₀))]
    with N hN1 hP hR hlow hE1 hE2
  have hN0 : 0 < N := by omega
  have hx : 0 < (N : ℝ) := by exact_mod_cast hN0
  rw [Real.rpow_zero, mul_one] at hP hR
  rw [Real.rpow_zero] at hlow hE2
  intro s hs hsU
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  set x := (N : ℝ) with hxdef
  have hP0 : 0 < x ^ (ξ - 1) := by positivity
  have hR0 : 0 < x ^ (β - 1) := by positivity
  have hκs := canonicalVerticalRateConstant_le_of_le hsLo hs hc
  have hδ0 : 0 ≤ canonicalMixedEntryRate N ξ β s c K := by
    rw [canonicalMixedEntryRate, canonicalVerticalEntryRate_eq hs0 hc,
      sourceHorizontalEntryRate]
    have := canonicalVerticalRateConstant_pos hs0 hc
    positivity
  have hδt : canonicalMixedEntryRate N ξ β s c K ≤ t := by
    rw [canonicalMixedEntryRate, canonicalVerticalEntryRate_eq hs0 hc,
      sourceHorizontalEntryRate]
    calc canonicalVerticalRateConstant s c * x ^ (ξ - 1) +
          (1 + s * K) * (2 * x ^ (β - 1)) * (s * c)⁻¹ ^ 2
        ≤ κ * x ^ (ξ - 1) + Bh * x ^ (β - 1) := by
          rw [hBhdef]
          have h1 : (1 + s * K) * (2 * x ^ (β - 1)) * (s * c)⁻¹ ^ 2 ≤
              (1 + sHi * K) * (2 * x ^ (β - 1)) * (sLo * c)⁻¹ ^ 2 := by gcongr
          have h2 : canonicalVerticalRateConstant s c * x ^ (ξ - 1) ≤
              κ * x ^ (ξ - 1) := by gcongr
          nlinarith
      _ ≤ κ * (t / M) + Bh * (t / M) := by gcongr
      _ = t := by rw [hMdef]; field_simp
  set δ := canonicalMixedEntryRate N ξ β s c K with hδdef
  have hbud : s * (2 * (s * c)⁻¹ * δ + δ ^ 2) ≤ m := by
    have heq : s * (2 * (s * c)⁻¹ * δ + δ ^ 2) = 2 / c * δ + s * δ ^ 2 := by
      field_simp
    rw [heq]
    have hδ2 : δ ^ 2 ≤ t := by nlinarith
    calc 2 / c * δ + s * δ ^ 2 ≤ 2 / c * t + sHi * t := by gcongr
      _ = (2 / c + sHi) * t := by ring
      _ ≤ m := htm
  refine ⟨ht1.trans' hδt, htc.trans' hδt, by linarith, hbud.trans hmc, ?_, ?_⟩
  · rw [cehETHGrid_heightLower_eq hN0]
    have hsplit : x * (Real.pi * Real.sqrt s * x ^ (ξ - 1) * (c / (2 * Real.pi))) =
        c * Real.sqrt s / 2 * x ^ ξ := by
      rw [Real.rpow_sub_one hx.ne']
      field_simp
    rw [hsplit]
    have hsqs : Real.sqrt sLo ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
    calc (1 : ℝ) ≤ c * Real.sqrt sLo / 2 * x ^ ξ := hlow
      _ ≤ c * Real.sqrt s / 2 * x ^ ξ := by gcongr
  · have hnorm : ‖(Real.sqrt s : ℂ)‖ = Real.sqrt s := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hL : (s * c)⁻¹ + 1 ≤ (sLo * c)⁻¹ + 1 := by gcongr
    have hB : (((s * c)⁻¹ + 1) / Real.pi) ^ 2 *
        thetaOneSTwoBound ‖(Real.sqrt s : ℂ)‖ ((s * c)⁻¹ + 1) (c / 2)
          ((2 * s)⁻¹) (c / 2) ≤ B₀ := by
      rw [hB₀def]
      gcongr
      · unfold thetaOneSTwoBound; positivity
      · exact convCond_thetaOneSTwoBound_le (norm_nonneg _)
          (by rw [hnorm]; exact Real.sqrt_le_sqrt hsU) (by positivity) hL
          (by positivity) (by positivity) (by gcongr) (by positivity)
    have hE0 : 0 < x ^ ε := by positivity
    calc _ ≤ B₀ * (2 * Real.pi ^ 2 + x ^ (ε / 2)) := by gcongr
      _ ≤ B₀ * (2 * Real.pi ^ 2 * (1 / (8 * Real.pi ^ 2 * B₀) * x ^ ε) +
            1 / (2 * B₀) * x ^ ε) := by
          gcongr B₀ * (?_ + ?_)
          · calc 2 * Real.pi ^ 2 = 2 * Real.pi ^ 2 * 1 := by ring
              _ ≤ _ := by gcongr
      _ = 3 / 4 * x ^ ε := by field_simp; ring
      _ < x ^ ε := by linarith

/-!
## From the CEH law to the fixed-point positive-chain bound
-/

/-- The positive chain minus its CEH deterministic approximation is the CEH
error of `cehTwoResolventLawError`. -/
theorem cehPositiveChain_sub_eq_lawError {N : ℕ} (s : ℝ) (Mf : ℂ → LocalETHMatrix N)
    (F J : LocalETHMatrix N) (z₁ z₂ : ℂ) (G : HermitianMatrix (Fin N)) :
    cehPositiveChain (F + G.1) z₁ z₂ (cehETHRegularizedObservable s Mf z₁ z₂ J) -
        NTrace (positiveDeterministicApprox (Real.sqrt s : ℂ) (Mf z₁)
          (cehETHRegularizedObservable s Mf z₁ z₂ J) (Mf z₂) *
          (cehETHRegularizedObservable s Mf z₁ z₂ J)ᴴ) =
      cehTwoResolventLawError s Mf F J z₁ z₂ G := by
  unfold cehPositiveChain cehTwoResolventLawError positiveChainError
  rw [NTrace_sub]

/-- The canonical upper height rate lies below the IFT cutoff once the
density-scale condition holds. -/
theorem canonicalHeightRate_lt_quantitativeIFTHeight
    {N : ℕ} (hN : 0 < N) {s c ξ : ℝ} (hc : 0 < c)
    (h2 : 1 < (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
      (c / (2 * Real.pi))) :
    canonicalHeightRate N ξ c < quantitativeIFTHeight s c := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [canonicalHeightRate, Real.rpow_sub_one hNr.ne']
  have hpow : 0 < (N : ℝ) ^ ξ := Real.rpow_pos_of_pos hNr ξ
  have h2'' : (N : ℝ) ^ ξ * (2 * Real.pi / c) <
      (N : ℝ) * quantitativeIFTHeight s c := by
    have := h2
    rw [show (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
        (c / (2 * Real.pi)) =
        ((N : ℝ) * quantitativeIFTHeight s c) / ((N : ℝ) ^ ξ * (2 * Real.pi / c)) by
      field_simp] at this
    exact (one_lt_div (by positivity)).1 this
  rw [show 2 * Real.pi / c * ((N : ℝ) ^ ξ / (N : ℝ)) =
      ((N : ℝ) ^ ξ * (2 * Real.pi / c)) / (N : ℝ) by ring]
  rw [div_lt_iff₀ hNr]
  linarith

/-- **Deterministic conversion at a grid pair.**  Under the explicit scalar
conditions, failure of the order-one positive-chain bound `N^ε` at a pair of
rectangular grid points forces failure of the CEH Theorem 4.2
estimate at exponent `ε/2` at the same pair.  This uses CEH Lemma 5.6 (fifth
bound), the `θ = 1` and `s₂` bounds on the rectangle, and the density
bounds; no probability. -/
theorem cehTwoResolventLawBad_of_positiveChainBad
    {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s) (F : HermitianMatrix (Fin N))
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F.1 Mf)
    {E₀ r c K β ξ ε : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hreg : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) {m : ℕ} (hm : 0 < m)
    (hR : (N : ℝ) ^ (β - 1) < r)
    (hHq : canonicalHeightRate N ξ c ≤ quantitativeIFTHeight s c)
    (hconv : canonicalMixedEntryRate N ξ β s c K ≤ 1 ∧
      canonicalMixedEntryRate N ξ β s c K ≤ c / 2 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) < 1 / 2 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) ≤ c / 2 ∧
      1 ≤ (N : ℝ) * (cehETHHeightLower N ξ s * (c / (2 * Real.pi))) ∧
      (((s * c)⁻¹ + 1) / Real.pi) ^ 2 *
          thetaOneSTwoBound ‖(Real.sqrt s : ℂ)‖ ((s * c)⁻¹ + 1) (c / 2)
            ((2 * s)⁻¹) (c / 2) *
          (2 * Real.pi ^ 2 + (N : ℝ) ^ (ε / 2)) < (N : ℝ) ^ ε)
    (a b : Fin (m + 1) × Fin (m + 1)) (G : HermitianMatrix (Fin N))
    (hbad : CEHFixedPointPositiveChainBad s ε Mf F.1 J
      (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) G) :
    CEHTwoResolventLawBad s (ε / 2) Mf F.1 J
      (cehETHGrid N E₀ β ξ s c m a) (cehETHGrid N E₀ β ξ s c m b) G := by
  obtain ⟨hδ1, hδc, hb1, hb2, hNl, hfin⟩ := hconv
  have hF : F.1.IsHermitian := F.2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch hF hs hMf hreg
  obtain ⟨Mb, Mb', hdata⟩ := hregC.boundary
  have hK : 0 ≤ K := by
    have hx₀ : E₀ ∈ Ioo (E₀ - r) (E₀ + r) := by constructor <;> linarith
    exact (norm_nonneg _).trans (hdata E₀ hx₀).2.2.1
  set Mc : ℂ → LocalETHMatrix N := hermitianMDEBranch hF hs with hMcdef
  set wa := cehETHGrid N E₀ β ξ s c m a
  set wb := cehETHGrid N E₀ β ξ s c m b
  have hma := cehETHGrid_mem (ξ := ξ) hN hs hF hr hc hregC hR hm a
  have hmb := cehETHGrid_mem (ξ := ξ) hN hs hF hr hc hregC hR hm b
  set lo := cehETHHeightLower N ξ s
  set H := canonicalHeightRate N ξ c
  set x₁ := wa.re
  set x₂ := wb.re
  set η₁ := wa.im
  set η₂ := wb.im
  have hwa : wa = (x₁ : ℂ) + (η₁ : ℂ) * Complex.I := (Complex.re_add_im wa).symm
  have hwb : wb = (x₂ : ℂ) + (η₂ : ℂ) * Complex.I := (Complex.re_add_im wb).symm
  have hη₁ : 0 < η₁ := hma.2.2.2.2.trans_le hma.2.2.1
  have hη₂ : 0 < η₂ := hmb.2.2.2.2.trans_le hmb.2.2.1
  -- vertical and horizontal budgets
  set V := canonicalVerticalEntryRate N ξ s c
  have hsrc : 0 ≤ sourceHorizontalEntryRate N β s c K := by
    unfold sourceHorizontalEntryRate; positivity
  have hmix : canonicalMixedEntryRate N ξ β s c K = V + sourceHorizontalEntryRate N β s c K :=
    rfl
  have hv₁ := (verticalModulus_le_canonicalVerticalEntryRate (N := N) (ξ := ξ) hs hc
    hma.2.2.2.1).trans (show V ≤ canonicalMixedEntryRate N ξ β s c K by
      rw [hmix]; linarith)
  have hdist : |x₂ - x₁| ≤ 2 * (N : ℝ) ^ (β - 1) := by
    have h1 := hma.1
    have h2 := hmb.1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hv₂ : (η₂ + s * (8 * η₂ / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ +
      (1 + s * K) * |x₂ - x₁| * (s * c)⁻¹ ^ 2 ≤ canonicalMixedEntryRate N ξ β s c K := by
    rw [hmix]
    gcongr
    · exact verticalModulus_le_canonicalVerticalEntryRate hs hc hmb.2.2.2.1
    · unfold sourceHorizontalEntryRate
      gcongr
  obtain ⟨htheta, hs2, hρ₁lo, hρ₁hi, hρ₂lo, hρ₂hi⟩ :=
    regularWindow_pair_thetaOne_sTwo_density hN hF hs hc hdata hma.2.1 hmb.2.1
      hη₁ (hma.2.2.2.1.trans hHq) hη₂ (hmb.2.2.2.1.trans hHq) hv₁ hv₂ hδ1 hδc hb1 hb2 J hJ
  simp only [← hwa, ← hwb] at htheta hs2 hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  -- canonicalize the branch at the two grid points
  have hMfa : Mf wa = Mc wa :=
    localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf hη₁.ne'
  have hMfb : Mf wb = Mc wb :=
    localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf hη₂.ne'
  have hA : cehETHRegularizedObservable s Mf wa wb J =
      regularizedObservable 1 (Mc wa) (Mc wb)ᴴ J := by
    unfold cehETHRegularizedObservable
    rw [hMfa, hMfb, htheta]
  set A := regularizedObservable 1 (Mc wa) (Mc wb)ᴴ J
  set S := sTwo 1 (Real.sqrt s : ℂ) (Mc wa) (Mc wb) A
  set ρ₁ := cehDensityOf (Mc wa)
  set ρ₂ := cehDensityOf (Mc wb)
  set T := thetaOneSTwoBound ‖(Real.sqrt s : ℂ)‖ ((s * c)⁻¹ + 1) (c / 2) ((2 * s)⁻¹) (c / 2)
  set L := (s * c)⁻¹ + 1
  have hT : 0 ≤ T := by
    unfold T thetaOneSTwoBound; positivity
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 ≤ T := by
    have := pow_le_pow_left₀ hS0 hs2 2
    rwa [Real.sq_sqrt hT] at this
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le (by positivity) hρ₁lo
  have hρ₂0 : 0 < ρ₂ := lt_of_lt_of_le (by positivity) hρ₂lo
  -- the fifth bound
  have h5 := lemma56_fifth_bound_hermitianMDEBranch hN hF hs hη₁ hη₂ J htheta
  -- the scale
  have hscale : cehTwoResolventLawScale s Mf wa wb J ≤ ρ₁ * ρ₂ * S ^ 2 := by
    unfold cehTwoResolventLawScale
    rw [hA, hMfa, hMfb, htheta]
    have hℓ : 1 ≤ (N : ℝ) * min (η₁ * ρ₁) (η₂ * ρ₂) := by
      refine le_trans hNl ?_
      gcongr
      refine le_min ?_ ?_
      · exact mul_le_mul hma.2.2.1 hρ₁lo (by positivity) hη₁.le
      · exact mul_le_mul hmb.2.2.1 hρ₂lo (by positivity) hη₂.le
    have hsq : 1 ≤ Real.sqrt ((N : ℝ) * min (η₁ * ρ₁) (η₂ * ρ₂)) :=
      Real.one_le_sqrt.2 hℓ
    exact div_le_self (by positivity) hsq
  by_contra hnot
  unfold CEHTwoResolventLawBad at hnot
  have herr : ‖cehTwoResolventLawError s Mf F.1 J wa wb G‖ ≤
      (N : ℝ) ^ (ε / 2) * (ρ₁ * ρ₂ * S ^ 2) :=
    (le_of_not_gt hnot).trans (by gcongr)
  unfold CEHFixedPointPositiveChainBad at hbad
  rw [← cehPositiveChain_sub_eq_lawError s Mf F.1 J wa wb G] at herr
  set P := cehPositiveChain (F.1 + G.1) wa wb (cehETHRegularizedObservable s Mf wa wb J)
  have hdet : ‖NTrace (positiveDeterministicApprox (Real.sqrt s : ℂ) (Mf wa)
      (cehETHRegularizedObservable s Mf wa wb J) (Mf wb) *
      (cehETHRegularizedObservable s Mf wa wb J)ᴴ)‖ ≤
      2 * Real.pi ^ 2 * ρ₁ * ρ₂ * S ^ 2 := by
    rw [hA, hMfa, hMfb]
    exact h5
  have hP : ‖P‖ ≤ ρ₁ * ρ₂ * S ^ 2 * (2 * Real.pi ^ 2 + (N : ℝ) ^ (ε / 2)) := by
    set Q := NTrace (positiveDeterministicApprox (Real.sqrt s : ℂ) (Mf wa)
      (cehETHRegularizedObservable s Mf wa wb J) (Mf wb) *
      (cehETHRegularizedObservable s Mf wa wb J)ᴴ)
    calc ‖P‖ = ‖Q + (P - Q)‖ := by congr 1; abel
      _ ≤ ‖Q‖ + ‖P - Q‖ := norm_add_le _ _
      _ ≤ 2 * Real.pi ^ 2 * ρ₁ * ρ₂ * S ^ 2 + (N : ℝ) ^ (ε / 2) * (ρ₁ * ρ₂ * S ^ 2) :=
        add_le_add hdet herr
      _ = _ := by ring
  have hbound : ρ₁ * ρ₂ * S ^ 2 * (2 * Real.pi ^ 2 + (N : ℝ) ^ (ε / 2)) ≤
      (L / Real.pi) ^ 2 * T * (2 * Real.pi ^ 2 + (N : ℝ) ^ (ε / 2)) := by
    have hρρ : ρ₁ * ρ₂ ≤ (L / Real.pi) ^ 2 := by
      rw [sq]; exact mul_le_mul hρ₁hi hρ₂hi hρ₂0.le (by positivity)
    gcongr
  linarith

/-- **Grid-pair tails from the CEH law.**  The CEH Theorem 4.2
law implies the grid-pair hypothesis of `measure_localETHWindowBad_le_of_gridTail`:
at every pair of points of the `N^4` rectangular grid, failure of the
order-one positive-chain bound `N^(δ-ξ)` has probability at most
`N^(-(D+20))`, eventually and uniformly. -/
theorem gridTail_of_twoResolventPositiveChainLaw
    (gue : LocalETHGUEFamily) (hlaw : CEHTwoResolventPositiveChainLaw gue)
    {κ C sLo sHi r c K β ξ δ D : ℝ} (hκ : 0 ≤ κ) (hC : 0 < C)
    (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hc : 0 < c) (hK : 0 < K)
    (hβ : β < 1) (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hξδ : ξ < δ) (hD : 0 < D) :
    ∃ Ng : ℕ, ∀ N : ℕ, Ng ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      ∀ a b : Fin (N ^ 4 + 1) × Fin (N ^ 4 + 1),
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | CEHFixedPointPositiveChainBad s (δ - ξ) Mf F.1 J
              (cehETHGrid N E₀ β ξ s c (N ^ 4) a)
              (cehETHGrid N E₀ β ξ s c (N ^ 4) b) G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-(D + 20))) := by
  have hε : 0 < δ - ξ := by linarith
  obtain ⟨Nlaw, hNlaw⟩ := hlaw κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK
    (ξ / 2) (2 * ξ) (by positivity) (by linarith) (by linarith)
    ((δ - ξ) / 2) (D + 20) (by positivity) (by linarith)
  obtain ⟨Ndet, hNdet⟩ := eventually_atTop.1
    (eventually_cehETHGridScalarConditions (δ := δ) (ε := δ - ξ) hsLo hsHi hr hc hK hβ
      hξ hξhalf hε (by linarith))
  obtain ⟨Nconv, hNconv⟩ := eventually_atTop.1
    (eventually_cehTwoResolventLaw_conversionConditions (β := β) (K := K) hsLo hsHi hc
      hK.le hβ hξ (by linarith) hε)
  refine ⟨max Nlaw (max Ndet Nconv), ?_⟩
  intro N hN s hs hsH F hFdef Mf hMf E₀ hreg J hJh hJ a b
  obtain ⟨hN4, hall⟩ := hNdet N (le_of_max_le_left (le_of_max_le_right hN))
  obtain ⟨hcond, hlo, hHup⟩ := hall s hs hsH
  have hconv := hNconv N (le_of_max_le_right (le_of_max_le_right hN)) s hs hsH
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  have hN0 : 0 < N := by omega
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch F.2 hs0 hMf hreg
  have hma := cehETHGrid_mem (ξ := ξ) hN0 hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) a
  have hmb := cehETHGrid_mem (ξ := ξ) hN0 hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) b
  have hHq := (canonicalHeightRate_lt_quantitativeIFTHeight hN0 hc hcond.2.1).le
  have hlit := hNlaw N (le_of_max_le_left hN) s hs hsH F hFdef Mf hMf E₀ hreg
    _ _ hma.2.1 hmb.2.1 (hlo.trans hma.2.2.1) (hma.2.2.2.1.trans hHup)
    (hlo.trans hmb.2.2.1) (hmb.2.2.2.1.trans hHup) J hJh hJ
  refine (measure_mono fun G hG => ?_).trans hlit
  exact cehTwoResolventLawBad_of_positiveChainBad hN0 hs0 F hMf hr hc hreg J hJ
    (by positivity : 0 < N ^ 4) hcond.1 hHq hconv a b G hG

/-- **CEH ETH extraction from the two-resolvent law.**

Source: Cipolloni–Erdős–Henheik, proof of Theorem 2.5 from Theorem 4.2
(positive-chain estimate (5.18)) and Lemma 5.6, specialized to the
external ETH theorem.  The only hypothesis is
`CEHTwoResolventPositiveChainLaw gue`, CEH Theorem 4.2 for the positive
two-resolvent chain at deterministic spectral parameters in the regular
window.  Every deterministic step is proved, including the fifth bound of CEH
Lemma 5.6 (`lemma56_fifth_bound_hermitianMDEBranch`), `θ = 1`, the `s₂` bound
and the density bounds on the rectangle
(`regularWindow_pair_thetaOne_sTwo_density`).  The conclusion is the
published `LocalETHRegularWindowBound gue`, with its exact quantifier order
and uniformities; the result holds for an arbitrary family `gue`. -/
theorem localETHRegularWindowBound_of_twoResolventPositiveChainLaw
    (gue : LocalETHGUEFamily) (hlaw : CEHTwoResolventPositiveChainLaw gue) :
    LocalETHRegularWindowBound gue := by
  intro κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK β hβ hβ2 ξ hξ hξβ δ D hδ hD
  set ξ' : ℝ := min ξ (δ / 4) with hξ'def
  have hξ'pos : 0 < ξ' := lt_min hξ (by positivity)
  have hξ'ξ : ξ' ≤ ξ := min_le_left _ _
  have hξ'δ : ξ' ≤ δ / 4 := min_le_right _ _
  have hβ1 : β < 1 := lt_of_le_of_lt hβ2 (by norm_num)
  exact CEH.localETHWindowBad_polynomialTail_of_auxiliaryLoss gue
    (ξ' := ξ') (δ' := δ / 2) hsLo hr hc hK hξ hξβ hβ2 hξ'pos.le hξ'ξ hδ (by linarith)
    (measure_localETHWindowBad_le_of_gridTail gue hsLo hsHi hr hc hK hβ1 hξ'pos
      (by linarith) (by linarith)
      (gridTail_of_twoResolventPositiveChainLaw gue hlaw hκ hC hsLo hsHi hr hc hK hβ1
        hξ'pos (by linarith) (by linarith) hD))

/-- The published conditional local-ETH input follows from the CEH
two-resolvent law alone. -/
theorem localETHInput_of_twoResolventPositiveChainLaw
    (gue : LocalETHGUEFamily) (hlaw : CEHTwoResolventPositiveChainLaw gue) :
    LocalETHInput gue :=
  ⟨localETHRegularWindowBound_of_twoResolventPositiveChainLaw gue hlaw⟩

/-!
## Relation to a global `Ψ₂ ≺ 1`

A global bound `Ψ₂ ≺ 1` for the CEH positive-chain control (5.18), in which both
spectral parameters satisfy `η₀ ≤ Im zᵢ` for one fixed `η₀ > 0`, does not suffice:
the law `CEHTwoResolventPositiveChainLaw` is needed at heights `N^(ξ-1) → 0`.  The
two lemmas below record that the global domain is eventually disjoint from the domain
the extraction uses, so no specialization of a global theorem gives
`CEHTwoResolventPositiveChainLaw`; that needs the CEH zig iteration.
-/

/-- Every fixed global height `η₀ > 0` eventually exceeds the upper end
`N^(ε₁-1)` of the local spectral domain of `CEHTwoResolventPositiveChainLaw`. -/
theorem eventually_lawHeight_lt_globalHeight {ε₁ η₀ : ℝ} (hε₁ : ε₁ < 1)
    (hη₀ : 0 < η₀) : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (ε₁ - 1) < η₀ := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (ε₁ - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hε₁)).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext N
    simp only [Function.comp_apply]
    congr 1
    ring
  exact hlim.eventually (Iio_mem_nhds hη₀)

/-- Consequently, for every fixed `η₀ > 0`, eventually in `N` no spectral parameter of
the local domain (and in particular no point of the extraction grid, whose heights lie
below `canonicalHeightRate N ξ c`) satisfies the global-regime condition
`η₀ ≤ Im z`. -/
theorem eventually_not_globalRegime {ξ c ε₁ η₀ : ℝ} (hξ : ξ < 1) (hε₁ : ε₁ < 1)
    (hη₀ : 0 < η₀) :
    ∀ᶠ N : ℕ in atTop,
      (∀ z : ℂ, z.im ≤ (N : ℝ) ^ (ε₁ - 1) → z.im < η₀) ∧
      canonicalHeightRate N ξ c < η₀ := by
  filter_upwards [eventually_lawHeight_lt_globalHeight hε₁ hη₀,
    (tendsto_canonicalHeightRate (c := c) hξ).eventually (Iio_mem_nhds hη₀)] with N h1 h2
  exact ⟨fun z hz => hz.trans_lt h1, h2⟩

end CEHNative.BlockBand.External.CEH
