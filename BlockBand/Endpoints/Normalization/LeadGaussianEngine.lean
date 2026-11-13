module

public import BlockBand.Endpoints.Normalization.LeadGaussianAlgebra
public import BlockBand.Endpoints.Normalization.PalmBridge
public import BlockBand.Endpoints.Clock.CovarianceStability

/-!
# The physical lead-profile theorem: Gaussian ratios followed by the covariance change

The Gaussian-ratio comparison holds against arbitrary positive reconstruction clocks. The stationary
scalar approximation changes its covariance to `c|z₀-Σ|^{-2}` with small relative Loewner error,
which preserves the ratio comparison.

**Main results.**
* Palm-side calculus (unconditional): `palmExpect_finCongr` (the `card = W` cast),
  `abs_palmExpect_sub_le` (`|Â[φ] - Â[ψ]| ≤ δ` when `|φ - ψ| ≤ δ`), `palmExpect_const_mul_sum`
  (linearity on finite averages), for bounded measurable tests.
* `palm_gaussian_cube_comparison` (the engine, over `Fin N`). Fixed first: the fresh constants
  `A, c₀, r₀, s₀, v₀` (`FreshConstants`), `m`, a continuous `ψ` on `[-1,1]^m`, `ε > 0`. There are
  `N₀` and `ω₀ ∈ (0, 1/2]` such that for `N ≥ N₀`, every `F` in `FreshClass F A c₀ E r₀ s₀ v₀`,
  every `Γ₀ = M₀M₀ᴴ` with `(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀` (`Γ = freshGamma F c₀ E`, `0 ≤ ω ≤ ω₀`), every
  `D ⪰ 0` with `Re Tr(Γ₀D) > 0` and `Re Tr(PD) ≥ 0` for all `P ⪰ 0`, every `B_j` sandwiched by
  `D`, every measurable default `d`:
  `|Â[ψ(ratioCube B D d v)] - E_g ψ(ratioCube B D d (M₀g))| ≤ 2ε`, `g ~ CN(0, I_N)`.
  No norm, rank or condition-number restriction on `D, B`. The hypothesis is
  `GaussianRatiosContract`; the covariance change is `clockCovarianceStability_cube`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks
open BlockBand.Endpoints.Clock
open scoped ComplexConjugate ComplexOrder

section PalmCalculus

variable {N : ℕ}

theorem palmExpect_finCongr {N' : ℕ} (h : N = N') (G : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ)
    (φ : (Fin N' → ℂ) → ℝ) :
    palmExpect (Matrix.reindex (finCongr h) (finCongr h) G) c E φ =
      palmExpect G c E (fun u => φ (fun i => u ((finCongr h).symm i))) := by
  subst h
  simp

theorem measurable_freshEigenvector_add (F : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => freshEigenvector (F + A0) ℓ :=
  measurable_pi_iff.mpr fun a => (measurable_rawOrderedColumnSelection _ a).comp
    (FixedOmega.measurable_matrix_add measurable_const measurable_id)

theorem integrable_palm_obs (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ) (ℓ : Fin N)
    (φ : (Fin N → ℂ) → ℝ) (hφ : Measurable φ) (M : ℝ) (hM : ∀ u, |φ u| ≤ M) :
    Integrable (fun A0 => palmWeight F c E ℓ A0 * φ (freshEigenvector (F + A0) ℓ))
      (freshTracelessLaw N c) :=
  integrable_palmWeight_mul F c E ℓ _ (hφ.comp (measurable_freshEigenvector_add F ℓ)) M
    (fun _ => hM _)

/-- `|Â[φ] - Â[ψ]| ≤ δ` for bounded measurable `φ, ψ` with `|φ - ψ| ≤ δ`. -/
theorem abs_palmExpect_sub_le (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ)
    (φ ψ : (Fin N → ℂ) → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) (M : ℝ)
    (hφM : ∀ u, |φ u| ≤ M) (hψM : ∀ u, |ψ u| ≤ M) (δ : ℝ) (hδ : ∀ u, |φ u - ψ u| ≤ δ) :
    |palmExpect F c E φ - palmExpect F c E ψ| ≤ δ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  unfold palmExpect
  rw [← sub_div, ← Finset.sum_sub_distrib]
  have hterm : ∀ ℓ : Fin N,
      |(∫ A0, palmWeight F c E ℓ A0 * φ (freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c) -
        ∫ A0, palmWeight F c E ℓ A0 * ψ (freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c| ≤
        δ * ∫ A0, palmWeight F c E ℓ A0 ∂freshTracelessLaw N c := by
    intro ℓ
    rw [← integral_sub (integrable_palm_obs F c E ℓ φ hφ M hφM)
      (integrable_palm_obs F c E ℓ ψ hψ M hψM), ← integral_const_mul]
    have hw := integrable_palmWeight_mul F c E ℓ (fun _ => δ) measurable_const |δ|
      (fun _ => le_refl _)
    have := norm_integral_le_of_norm_le (μ := freshTracelessLaw N c)
      (f := fun A0 => palmWeight F c E ℓ A0 * φ (freshEigenvector (F + A0) ℓ) -
        palmWeight F c E ℓ A0 * ψ (freshEigenvector (F + A0) ℓ))
      (g := fun A0 => δ * palmWeight F c E ℓ A0) (by simpa [mul_comm] using hw)
      (Filter.Eventually.of_forall fun A0 => by
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul,
          abs_of_nonneg (palmWeight_nonneg' F c E ℓ A0), mul_comm]
        exact mul_le_mul_of_nonneg_right (hδ _) (palmWeight_nonneg' F c E ℓ A0))
    simpa [Real.norm_eq_abs] using this
  have hsum : |∑ ℓ : Fin N,
      ((∫ A0, palmWeight F c E ℓ A0 * φ (freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c) -
        ∫ A0, palmWeight F c E ℓ A0 * ψ (freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c)| ≤
      δ * palmMass F c E := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [palmMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ _ => hterm ℓ
  rcases (palmMass_nonneg F c E).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, abs_zero]; exact hδ0
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    exact hsum

/-- Linearity of `Â` on finite averages of bounded measurable tests. -/
theorem palmExpect_const_mul_sum (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ) {S : Type*}
    [Fintype S] (a : ℝ) (f : S → (Fin N → ℂ) → ℝ) (hf : ∀ s, Measurable (f s)) (M : ℝ)
    (hM : ∀ s u, |f s u| ≤ M) :
    palmExpect F c E (fun u => a * ∑ s, f s u) = a * ∑ s, palmExpect F c E (f s) := by
  unfold palmExpect
  rw [← Finset.sum_div, mul_div_assoc']
  congr 1
  have hint : ∀ ℓ s, Integrable (fun A0 => palmWeight F c E ℓ A0 *
      f s (freshEigenvector (F + A0) ℓ)) (freshTracelessLaw N c) := fun ℓ s =>
    integrable_palm_obs F c E ℓ (f s) (hf s) M (hM s)
  have : ∀ ℓ : Fin N, (∫ A0, palmWeight F c E ℓ A0 *
      (a * ∑ s, f s (freshEigenvector (F + A0) ℓ)) ∂freshTracelessLaw N c) =
      a * ∑ s, ∫ A0, palmWeight F c E ℓ A0 * f s (freshEigenvector (F + A0) ℓ)
        ∂freshTracelessLaw N c := by
    intro ℓ
    rw [← integral_finsetSum _ fun s _ => hint ℓ s, ← integral_const_mul]
    congr 1; funext A0
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]

end PalmCalculus

section Engine

variable {N : ℕ}

/-- `Γ = freshGamma F c₀ E` has the explicit square root `√c₀ X⁻¹`, `X = F - E - c₀m`. -/
theorem freshGamma_sqrt (F : Matrix (Fin N) (Fin N) ℂ) {c₀ : ℝ} (hc : 0 ≤ c₀) (E : ℝ) :
    let X := F - ((E : ℂ) + (c₀ : ℂ) * freshDyson F c₀ E) • 1
    (((Real.sqrt c₀ : ℝ) : ℂ) • X⁻¹) * (((Real.sqrt c₀ : ℝ) : ℂ) • X⁻¹)ᴴ = freshGamma F c₀ E := by
  intro X
  rw [show freshGamma F c₀ E = (c₀ : ℂ) • (Xᴴ * X)⁻¹ from rfl]
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_inv_rev,
    conjTranspose_nonsing_inv]
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

theorem traceAgainst_sub_smul (P Q D : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) :
    traceAgainst (P - ((a : ℝ) : ℂ) • Q) D = traceAgainst P D - a * traceAgainst Q D := by
  unfold traceAgainst
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
    smul_eq_mul, Complex.re_ofReal_mul]

/-- **Gaussian ratios, then the covariance change**, from `GaussianRatiosContract`. -/
theorem palm_gaussian_cube_comparison (hGR : GaussianRatiosContract) (A c₀ r₀ s₀ v₀ : ℝ)
    (hfc : FreshConstants c₀ r₀ s₀ v₀) (m : ℕ) (ψ : C(Fin m → Set.Icc (-1 : ℝ) 1, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∃ ω₀ : ℝ, 0 < ω₀ ∧ ω₀ ≤ 1 / 2 ∧
    ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ (Γ₀ M₀ : Matrix (Fin N) (Fin N) ℂ), M₀ * M₀ᴴ = Γ₀ → ∀ ω : ℝ, 0 ≤ ω → ω ≤ ω₀ →
      (((1 + ω : ℝ) : ℂ) • Γ₀ - freshGamma F c₀ E).PosSemidef →
      (freshGamma F c₀ E - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef →
    ∀ (D : Matrix (Fin N) (Fin N) ℂ) (B : Fin m → Matrix (Fin N) (Fin N) ℂ), D.PosSemidef →
      (∀ j, IsSandwiched (B j) D) → 0 < traceAgainst Γ₀ D →
      (∀ P : Matrix (Fin N) (Fin N) ℂ, P.PosSemidef → 0 ≤ traceAgainst P D) →
    ∀ d : (Fin N → ℂ) → Fin m → ℝ, Measurable d →
      |palmExpect F c₀ E (fun v => ψ (ratioCube B D d v)) -
          ∫ g, ψ (ratioCube B D d (M₀ *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤ 2 * ε := by
  obtain ⟨N₀, hN₀⟩ := hGR A c₀ r₀ s₀ v₀ hfc m ψ ε hε
  obtain ⟨ω₁, hω₁, hcov⟩ := clockCovarianceStability_cube m ψ ε hε
  refine ⟨N₀, min ω₁ (1 / 2), lt_min hω₁ (by norm_num), min_le_right _ _, ?_⟩
  intro N hN hNpos F E hF Γ₀ M₀ hM₀ ω hω0 hω h1 h2 D B hD hB hT₀ hDtr d hd
  have hc : 0 ≤ c₀ := hfc.1.le
  set X := F - ((E : ℂ) + (c₀ : ℂ) * freshDyson F c₀ E) • 1 with hX
  set M : Matrix (Fin N) (Fin N) ℂ := ((Real.sqrt c₀ : ℝ) : ℂ) • X⁻¹ with hMdef
  have hM : M * Mᴴ = freshGamma F c₀ E := freshGamma_sqrt F hc E
  have hω1 : ω ≤ 1 / 2 := hω.trans (min_le_right _ _)
  have hT : 0 < traceAgainst (freshGamma F c₀ E) D := by
    have h := hDtr _ h2
    rw [traceAgainst_sub_smul] at h
    have : 0 < (1 - ω) * traceAgainst Γ₀ D := mul_pos (by linarith) hT₀
    linarith
  have hΓ₀ : Γ₀.PosSemidef := hM₀ ▸ posSemidef_self_mul_conjTranspose M₀
  have e1 := hN₀ N hN hNpos F E hF D B hD hB hT d hd M hM
  have e2 := hcov N Γ₀ (freshGamma F c₀ E) ω hω0 (hω.trans (min_le_left _ _)) hΓ₀ h1 h2 D B hD
    hB hT₀ M M₀ hM hM₀ d hd
  have := abs_sub_le (palmExpect F c₀ E (fun v => ψ (ratioCube B D d v)))
    (∫ g, ψ (ratioCube B D d (M *ᵥ g)) ∂circularVectorLaw (Fin N))
    (∫ g, ψ (ratioCube B D d (M₀ *ᵥ g)) ∂circularVectorLaw (Fin N))
  linarith

end Engine

end LeadGaussian

end BlockBand.Endpoints.Normalization
