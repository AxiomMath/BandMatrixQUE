module

public import BlockBand.Endpoints.Sine.SineEndpointFlow
public import BlockBand.Endpoints.Sine.SineEndpointCrossing
public import BlockBand.Endpoints.Sine.SineEndpointPairing
public import BlockBand.Endpoints.Sine.SineEndpointLimit
public import BlockBand.Endpoints.Sine.CrossingSineClosed
public import BlockBand.Endpoints.Sine.FlowAdmissionBridge
public import BlockBand.QUE.Fourier.PhysicalWeightedMass
public import BlockBand.Model.Construction.SpectralFiniteRealization
public import BlockBand.Internal.Contracts.CriticalEntire
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The original-ring sine endpoint

This file proves the sine endpoint theorem for the original ring: the Laplace functional of the
unfolded physical spectrum near a bulk energy approaches the sine Laplace functional at rate
`τ^{1/8}`, and the critical limits converge to the sine law as `τ ↓ 0`.

**Statement (`SineEndpointStatement`).**
* *Rate clause.* Fix `0 < b < 1/2`, a bulk energy `-2 < E < 2` and `T₀ > 0`; for every nonnegative
  smooth (`C^∞`) compactly supported `f` there is `C = C_f` (depending also on `b, E, T₀`) such
  that for every `0 < τ ≤ min(1, T₀)`, every critical sequence `W → ∞`, `n/W → τ`, and all exact
  finite realizations (`FiniteRealization`: the physical law `model.law` of the original ring with
  any ordered spectral realization, unfolded eigenvalues `u_α = Nρ(E)(λ_α - E)`):
  `limsup |E exp(-Σ_α f(u_α)) - L_sine(f)| ≤ C τ^{1/8}`, written `∀ ε > 0, ∀ᶠ j, · ≤ Cτ^{1/8} + ε`.
  `L_sine` is `sineLaplaceFunctional` (the Laplace functional characterizing `IsSineLaw`).
* *Consequence clause.* For every critical family and every sine law, the spectral projections
  of the critical limits converge to the sine law as `τ ↓ 0`.

**Proof.** Choose `R ⊇ supp f`, `T = R + 2`, `K = R + 2T + 3`, a smooth bump
`χ = 1` on `[-K, K]`, and let `A_W` be the integrated velocity error of the flow admission bound.
On `A_W ≤ ε` (`ε ≤ 1`) each branch through `[-R-1, R+1]` satisfies
`|u_α(t) - u_α(0) - t| ≤ ε` (`se_branch_ftc`, first-exit argument in `se_pairing`), crosses zero
once, and the crossing parameters (`se_crossingSum_eq`: every crossing is a branch crossing, with
multiplicity) pair with `{u_α(0)}` within `ε`. The Laplace functionals then differ by at most
`ω_f(ε)` times the count of `u_α(0)` in `[-R-1, R+1]` (`se_pointwise`); off the event they differ by
at most `1 ≤ A_W/ε` (Markov). Integration (`se_finite_bound`), the original counting bound
(`PhysicalBlockConditionalCount`, through `fa_count_lintegral_le`), the crossing sine lemma
(`crossingSine_of_contracts`) and the flow admission lemma give
`limsup ≤ C₁ ω_f(ε) + C₂ τ^{1/4}/ε` (`se_core`); `ε = τ^{1/8}` and `ω_f(ε) ≤ Lip(f) ε` give the rate.
Only the count of the physical configuration is needed: on the pairing event the crossings are
indexed by branches, so no separate bound on the crossing count is used. For the consequence, `se_core` with the uniform-continuity modulus of a continuous `f`
gives Laplace convergence for every nonnegative `f ∈ C_c`; unit intensity gives tightness, and the
Laplace functionals determine the law (`se_tendsto_sineLaw`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.ClocksCommonPort BlockBand.Internal.Contracts.CriticalEntire
open scoped ENNReal ContDiff

/-!
## 1. Elementary inequalities
-/

/-- `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0`. -/
theorem se_abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonpos (by linarith : a - b ≤ 0)]
  have h2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 : 1 - Real.exp (-(b - a)) ≤ b - a := by linarith [Real.add_one_le_exp (-(b - a))]
  have h4 : 0 ≤ 1 - Real.exp (-(b - a)) := by
    have : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have h5 : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    have : -a + -(b - a) = -b := by ring
    rw [mul_sub, mul_one, ← Real.exp_add, this]
  rw [h5]
  calc Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤ 1 * (1 - Real.exp (-(b - a))) :=
        mul_le_mul_of_nonneg_right h2 h4
    _ ≤ -(a - b) := by linarith

/-- `|e^{-a} - e^{-b}| ≤ 1` for `a, b ≥ 0`. -/
theorem se_abs_exp_neg_sub_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ 1 := by
  have h1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [abs_le]
  constructor <;> linarith [Real.exp_pos (-a), Real.exp_pos (-b)]

/-- A nonnegative bound on the support of a compactly supported test. -/
theorem se_support_bound (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, f x ≠ 0 → |x| ≤ R := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have := hR x (subset_tsupport _ hx)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-!
## 2. The pointwise comparison on the pairing event
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- `exp(-Σ_α f(u_α))`, `u_α = Nρ(λ_α - E)` (raw `H`, ranks with multiplicity). -/
def se_physIntegrand (E : ℝ) (f : ℝ → ℝ) (H : p.SiteMatrix) : ℝ :=
  Real.exp (-∑ α : Fin p.N, f (microCoord p E (physicalOrderedEigenvalue p H α)))

/-- `#{α : |u_α| ≤ L}`. -/
def se_count (E L : ℝ) (H : p.SiteMatrix) : ℕ :=
  (Finset.univ.filter fun α : Fin p.N =>
    |microCoord p E (physicalOrderedEigenvalue p H α)| ≤ L).card

theorem se_crossingScale_ne_zero {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E) :
    crossingScale p E ≠ 0 := by
  unfold crossingScale
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr p.W_pos.ne')) hρ.ne'

theorem se_microCoord_eq_zero_iff {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E) (e : ℝ) :
    microCoord p E e = 0 ↔ e = E := by
  unfold microCoord
  have hN : (0 : ℝ) < p.N := Nat.cast_pos.mpr p.N_pos
  have hne : (p.N : ℝ) * Parameters.semicircleDensity E ≠ 0 := mul_ne_zero hN.ne' hρ.ne'
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hne
    · linarith
  · intro h
    rw [h, sub_self, mul_zero]

/-- **The comparison at one matrix.** For Hermitian `H` with simple spectrum
and invertible exterior minor at `E`, with `R ⊇ supp f`, `T ≥ R + 2`, `K ≥ R + 2T + 3`, `χ = 1` on
`[-K, K]`, `0 < δ ≤ 1` and `M` a modulus of `f` at scale `δ`:
`|exp(-Σ_α f(u_α)) - exp(-Σ_j f(-t_j))| ≤ M · #{α : |u_α| ≤ R + 1} + δ⁻¹ A`,
`A = ∫_{-T}^T Σ_α χ(u_α(t))|v_α(t) - 1| dt`. -/
theorem se_pointwise (H : p.SiteMatrix) (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (E : ℝ) (hρ : 0 < Parameters.semicircleDensity E)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0)
    (f : CompactlySupportedContinuousMap ℝ ℝ) (hf0 : ∀ x, 0 ≤ f x) (χ : ℝ → ℝ)
    {R T K δ M : ℝ} (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x ∈ Icc (-K) K, χ x = 1)
    (hfR : ∀ x, f x ≠ 0 → |x| ≤ R) (hM : ∀ x y, |x - y| ≤ δ → |f x - f y| ≤ M)
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : R + 2 ≤ T) (hK : R + 2 * T + 3 ≤ K) :
    ENNReal.ofReal |se_physIntegrand p E f H - Real.exp (-crossingSum p i (reflectTest f) H E)| ≤
      ENNReal.ofReal M * (se_count p E (R + 1) H : ℝ≥0∞) +
        ENNReal.ofReal δ⁻¹ * ∫⁻ t in Icc (-T) T, fa_flowIntegrand p i E χ H t := by
  have hsc := se_crossingScale_ne_zero p hρ
  set A := ∫⁻ t in Icc (-T) T, fa_flowIntegrand p i E χ H t with hAdef
  have hphys0 : 0 ≤ ∑ α : Fin p.N, f (microCoord p E (physicalOrderedEigenvalue p H α)) :=
    Finset.sum_nonneg fun α _ => hf0 _
  have hcr0 : 0 ≤ crossingSum p i (reflectTest f) H E :=
    crossingSum_nonneg p i (reflectTest f) (fun x => hf0 _) H E
  by_cases hA : A ≤ ENNReal.ofReal δ
  · have hpair := se_pairing (se_branch p i H E) (se_speed p i H E) (se_rootSet p i H E) f χ
      (fun α => se_continuous_branch p i H hH E α)
      (fun α s t hst => se_branch_ftc p i H hH hsep E hρ α s t hst)
      (fun α r => se_speed_nonneg p i H E α r)
      (fun t => by
        rw [se_mem_rootSet p i H hH E hdet hsc t]
        simp only [se_branch, se_microCoord_eq_zero_iff p hρ])
      hχ0 hχ1
      (fun α => by
        refine le_trans (lintegral_mono fun r => ?_) hA
        unfold fa_flowIntegrand fa_obs
        exact Finset.single_le_sum (f := fun β : Fin p.N => ENNReal.ofReal
          (χ (microCoord p E (physicalOrderedEigenvalue p (pairFlow p i H E r) β)) *
            |(p.n : ℝ) / 2 * pairMass p i β (pairFlow p i H E r) - 1|))
          (fun _ _ => bot_le) (Finset.mem_univ α))
      hfR hM hR hδ.le hδ1 hT hK
    have hcross : crossingSum p i (reflectTest f) H E =
        ∑ α, ∑ t ∈ (se_rootSet p i H E).filter (fun t => se_branch p i H E α t = 0), f (-t) := by
      rw [se_crossingSum_eq p i H hH E hdet hsc]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hfil : (se_rootSet p i H E).filter
          (fun t => physicalOrderedEigenvalue p (pairFlow p i H E t) α = E) =
          (se_rootSet p i H E).filter (fun t => se_branch p i H E α t = 0) :=
        Finset.filter_congr fun t _ => (se_microCoord_eq_zero_iff p hρ _).symm
      rw [hfil]
      rfl
    have hphys : ∑ α : Fin p.N, f (microCoord p E (physicalOrderedEigenvalue p H α)) =
        ∑ α, f (se_branch p i H E α 0) := by
      simp only [se_branch, se_pairFlow_zero]
    have hcnt : ((Finset.univ.filter fun α => |se_branch p i H E α 0| ≤ R + 1).card : ℝ) =
        (se_count p E (R + 1) H : ℝ) := by
      simp only [se_branch, se_pairFlow_zero, se_count]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by simp [hδ.le]))
    have key : |se_physIntegrand p E f H - Real.exp (-crossingSum p i (reflectTest f) H E)| ≤
        M * (se_count p E (R + 1) H : ℝ) := by
      unfold se_physIntegrand
      refine (se_abs_exp_neg_sub_le hphys0 hcr0).trans ?_
      rw [hphys, hcross, ← hcnt]
      exact hpair
    calc ENNReal.ofReal
          |se_physIntegrand p E f H - Real.exp (-crossingSum p i (reflectTest f) H E)|
        ≤ ENNReal.ofReal (M * (se_count p E (R + 1) H : ℝ)) := ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal M * (se_count p E (R + 1) H : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hM0, ENNReal.ofReal_natCast]
      _ ≤ _ := le_self_add
  · rw [not_le] at hA
    have h1 : ENNReal.ofReal
        |se_physIntegrand p E f H - Real.exp (-crossingSum p i (reflectTest f) H E)| ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (se_abs_exp_neg_sub_le_one hphys0 hcr0)
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ⁻¹ * A := by
      calc (1 : ℝ≥0∞) = ENNReal.ofReal δ⁻¹ * ENNReal.ofReal δ := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), inv_mul_cancel₀ hδ.ne',
              ENNReal.ofReal_one]
        _ ≤ _ := by gcongr
    exact h1.trans (h2.trans le_add_self)

/-!
## 3. Integration at fixed `W`
-/

theorem se_measurable_physIntegrand (E : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (se_physIntegrand p E f) := by
  unfold se_physIntegrand
  refine Real.measurable_exp.comp (Measurable.neg (Finset.measurable_sum _ fun α _ => ?_))
  exact hf.measurable.comp
    ((fa_measurable_microCoord p E).comp (measurable_physicalOrderedEigenvalue p α))

/-- **Finite-`W` comparison** (by Markov's inequality): with the hypotheses of
`se_pointwise` on `f, χ, R, T, K, δ, M`, under the exact physical law,
`|E exp(-Σ_α f(u_α)) - E exp(-Σ_j f(-t_j))| ≤ M · E#{α : |u_α| ≤ R+1} + δ⁻¹ E A`. -/
theorem se_finite_bound (model : p.GaussianRingModel) (E : ℝ)
    (hρ : 0 < Parameters.semicircleDensity E)
    (f : CompactlySupportedContinuousMap ℝ ℝ) (hf0 : ∀ x, 0 ≤ f x) {χ : ℝ → ℝ}
    (hχc : Continuous χ) {R T K δ M : ℝ} (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x ∈ Icc (-K) K, χ x = 1)
    (hfR : ∀ x, f x ≠ 0 → |x| ≤ R) (hM : ∀ x y, |x - y| ≤ δ → |f x - f y| ≤ M)
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : R + 2 ≤ T) (hK : R + 2 * T + 3 ≤ K) :
    ENNReal.ofReal |(∫ H, se_physIntegrand p E f H ∂(model.law : Measure p.SiteMatrix)) -
        (crossingLaplace p model i E (reflectTest f)).toReal| ≤
      ENNReal.ofReal M *
          ∫⁻ H, (se_count p E (R + 1) H : ℝ≥0∞) ∂(model.law : Measure p.SiteMatrix) +
        ENNReal.ofReal δ⁻¹ * fa_velocityError p model i E T χ := by
  have hsc := se_crossingScale_ne_zero p hρ
  set μ := (model.law : Measure p.SiteMatrix) with hμ
  set Φ := se_physIntegrand p E f with hΦ
  set ψ : p.SiteMatrix → ℝ := fun H => (crossingProxy p i E (reflectTest f) H).toReal with hψ
  have hΦm : Measurable Φ := se_measurable_physIntegrand p E f.continuous
  have hψm : Measurable ψ := ENNReal.measurable_toReal.comp (measurable_crossingProxy p i E _)
  have hgood : ∀ᵐ H ∂μ, H.IsHermitian ∧ H.charpoly.Separable ∧
      (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0 := by
    filter_upwards [model.isPhysical.1, model.ae_charpoly_separable,
      ae_det_exteriorBlock_ne_zero p i model E] with H h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hψeq : ∀ᵐ H ∂μ, ψ H = Real.exp (-crossingSum p i (reflectTest f) H E) := by
    filter_upwards [hgood] with H hHg
    obtain ⟨hH, -, hdet⟩ := hHg
    simp only [ψ]
    rw [← crossingProxy_eq p i E (reflectTest f) H hH hdet hsc,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hΦb : ∀ H, 0 ≤ Φ H ∧ Φ H ≤ 1 := fun H =>
    ⟨(Real.exp_pos _).le,
      Real.exp_le_one_iff.2 (neg_nonpos.2 (Finset.sum_nonneg fun α _ => hf0 _))⟩
  have hψb : ∀ H, 0 ≤ ψ H ∧ ψ H ≤ 1 := fun H => by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have h := crossingProxy_le_one p i E (reflectTest f) (fun x => hf0 _) H
    have h' : (crossingProxy p i E (reflectTest f) H).toReal ≤ (1 : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono ENNReal.one_ne_top h
    simpa using h'
  have hΦi : Integrable Φ μ := (integrable_const (1 : ℝ)).mono' hΦm.aestronglyMeasurable
    (ae_of_all _ fun H => by rw [Real.norm_eq_abs, abs_of_nonneg (hΦb H).1]; exact (hΦb H).2)
  have hψi : Integrable ψ μ := (integrable_const (1 : ℝ)).mono' hψm.aestronglyMeasurable
    (ae_of_all _ fun H => by rw [Real.norm_eq_abs, abs_of_nonneg (hψb H).1]; exact (hψb H).2)
  have hcl : crossingLaplace p model i E (reflectTest f) = ENNReal.ofReal (∫ H, ψ H ∂μ) := by
    unfold crossingLaplace
    rw [ofReal_integral_eq_lintegral_ofReal hψi (ae_of_all _ fun H => (hψb H).1)]
    refine lintegral_congr_ae ?_
    filter_upwards [hψeq] with H h
    rw [h]
  have hclr : (crossingLaplace p model i E (reflectTest f)).toReal = ∫ H, ψ H ∂μ := by
    rw [hcl, ENNReal.toReal_ofReal (integral_nonneg fun H => (hψb H).1)]
  have hAm : Measurable fun H => ENNReal.ofReal δ⁻¹ *
      ∫⁻ t in Icc (-T) T, fa_flowIntegrand p i E χ H t :=
    ((fa_measurable_flowIntegrand p i E hχc).lintegral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Icc (-T) T))).const_mul _
  rw [hclr, ← integral_sub hΦi hψi]
  calc ENNReal.ofReal |∫ H, Φ H - ψ H ∂μ| ≤ ENNReal.ofReal (∫ H, |Φ H - ψ H| ∂μ) :=
        ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
    _ = ∫⁻ H, ENNReal.ofReal |Φ H - ψ H| ∂μ :=
        ofReal_integral_eq_lintegral_ofReal (hΦi.sub hψi).abs (ae_of_all _ fun _ => abs_nonneg _)
    _ ≤ ∫⁻ H, (ENNReal.ofReal M * (se_count p E (R + 1) H : ℝ≥0∞) +
          ENNReal.ofReal δ⁻¹ * ∫⁻ t in Icc (-T) T, fa_flowIntegrand p i E χ H t) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgood, hψeq] with H hHg hψH
        obtain ⟨hH, hsep, hdet⟩ := hHg
        rw [hψH]
        exact se_pointwise p i H hH hsep E hρ hdet f hf0 χ hχ0 hχ1 hfR hM hR hδ hδ1 hT hK
    _ = _ := by
        rw [lintegral_add_right _ hAm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl

end Pair

/-- **Counting for the original matrix in a microscopic window** (through
`PhysicalBlockConditionalCount`, `r = 1`, all blocks fresh): one `C > 0`; for every
admissible `p`, model, bulk `E` and `L ≥ 0`, `E #{α: |u_α| ≤ L} ≤ C/√c · 2L/ρ(E)`.
-/
theorem se_count_lintegral_le (hCount : PhysicalBlockConditionalCount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (model : p.GaussianRingModel) (E L : ℝ),
      0 < Parameters.semicircleDensity E → 0 ≤ L →
      ∫⁻ H, (se_count p E L H : ℝ≥0∞) ∂(model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (C / Real.sqrt p.c * (2 * L / Parameters.semicircleDensity E)) := by
  obtain ⟨C, hC, h⟩ := fa_count_lintegral_le hCount
  refine ⟨C, hC, fun p model E L hρ hL => ?_⟩
  have hN : (0 : ℝ) < p.N := Nat.cast_pos.mpr p.N_pos
  have hc : 0 < (p.N : ℝ) * Parameters.semicircleDensity E := mul_pos hN hρ
  set a := L / ((p.N : ℝ) * Parameters.semicircleDensity E) with ha
  have ha0 : 0 ≤ a := div_nonneg hL hc.le
  have hb := h p model 0 0 (E - a) (E + a) (by linarith)
  have hset : ∀ H : p.SiteMatrix, (se_count p E L H : ℝ≥0∞) =
      ((Finset.univ.filter fun α : Fin p.N =>
        physicalOrderedEigenvalue p (H + ((0 : ℝ) : ℂ) • pairProjector p 0) α ∈
          Icc (E - a) (E + a)).card : ℝ≥0∞) := by
    intro H
    simp only [Complex.ofReal_zero, zero_smul, add_zero, se_count]
    congr 2
    refine Finset.filter_congr fun α _ => ?_
    unfold microCoord
    rw [abs_mul, abs_of_pos hc, mem_Icc, ← le_div_iff₀' hc, ← ha, abs_le]
    constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
  rw [lintegral_congr fun H => hset H]
  refine hb.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  have hnw : ((p.n * p.W : ℕ) : ℝ) = p.N := by simp [Parameters.N]
  rw [hnw, ha]
  field_simp
  ring

/-!
## 4. The limsup bound with a modulus (core)
-/

/-- **Core estimate**, before the choice `δ = τ^{1/8}`. Fixed `0 < b < 1/2`, bulk `E`,
`T₀ > 0`, a nonnegative `f ∈ C_c(ℝ)` with `supp f ⊆ [-R, R]`; then `C₁, C₂ ≥ 0`; for every
`0 < δ ≤ 1`, every modulus `M` of `f` at scale `δ`, every `0 < τ ≤ T₀`, critical sequence and
models: `limsup_j |E exp(-Σ_α f(u_α)) - L_sine(f)| ≤ C₁ M + C₂ τ^{1/4}/δ`. -/
theorem se_core (hExt : ExternalSine) (hCo : CoareaContract) (hPair : PairRegularEventContract)
    (hCount : PhysicalBlockConditionalCount) (hFA : FlowAdmissionStatement) :
    ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
    ∀ R : ℝ, 0 ≤ R → (∀ x, f x ≠ 0 → |x| ≤ R) →
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ δ M : ℝ, 0 < δ → δ ≤ 1 → (∀ x y, |x - y| ≤ δ → |f x - f y| ≤ M) →
      ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ (s : CriticalSequence τ)
        (model : ∀ j, (s.parameters b hb hb' j).GaussianRingModel),
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
          |(∫ H, se_physIntegrand (s.parameters b hb hb' j) E f H
              ∂((model j).law : Measure (s.parameters b hb hb' j).SiteMatrix)) -
            sineLaplaceFunctional f| ≤ C₁ * M + C₂ * τ ^ (1 / 4 : ℝ) / δ + ε := by
  intro b hb hb' E hE1 hE2 T₀ hT₀ f hf0 R hR hfR
  have hρ := fa_rho_pos hE1 hE2
  set T : ℝ := R + 2 with hTdef
  set K : ℝ := R + 2 * T + 3 with hKdef
  have hK0 : 0 < K := by rw [hKdef, hTdef]; linarith
  let φ : ContDiffBump (0 : ℝ) := ⟨K, K + 1, hK0, by linarith⟩
  have hχ1 : ∀ x ∈ Icc (-K) K, φ x = 1 := fun x hx =>
    φ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact abs_le.2 ⟨hx.1, hx.2⟩)
  obtain ⟨Cfa, hCfa⟩ := hFA b hb hb' E hE1 hE2 T₀ hT₀ T K φ φ.contDiff φ.hasCompactSupport
    (fun x => φ.nonneg) hχ1
  obtain ⟨Cc, hCc, hcount⟩ := se_count_lintegral_le hCount
  refine ⟨Cc / Real.sqrt (1 - 2 * b) * (2 * (R + 1) / Parameters.semicircleDensity E),
    max Cfa 0, by positivity, le_max_right _ _, ?_⟩
  intro δ M hδ hδ1 hM τ hτ hτT s model ε hε
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by simp [hδ.le]))
  have hcross := crossingSine_of_contracts hExt hCo hPair τ s b E hb hb' hE1 hE2 model (fun _ => 0)
    (reflectTest f) (fun x => hf0 _)
  rw [sineLaplaceFunctional_reflect] at hcross
  have hcross' : Tendsto (fun j => (crossingLaplace (s.parameters b hb hb' j) (model j) 0 E
      (reflectTest f)).toReal) atTop (𝓝 (sineLaplaceFunctional f)) := by
    have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hcross
    rwa [ENNReal.toReal_ofReal (sineLaplaceFunctional_mem f hf0).1] at this
  have hev1 : ∀ᶠ j in atTop, |(crossingLaplace (s.parameters b hb hb' j) (model j) 0 E
      (reflectTest f)).toReal - sineLaplaceFunctional f| < ε / 2 := by
    filter_upwards [hcross'.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with j hj
    rwa [Real.dist_eq] at hj
  have hev2 := hCfa τ hτ hτT s model (fun _ => 0) (δ * ε / 2) (by positivity)
  filter_upwards [hev1, hev2] with j hj1 hj2
  have hfin := se_finite_bound (s.parameters b hb hb' j) 0 (model j) E hρ f hf0 φ.continuous
    (R := R) (T := T) (K := K) (δ := δ) (M := M) (fun x => φ.nonneg) hχ1 hfR hM hR hδ hδ1
    le_rfl le_rfl
  have hcnt := hcount (s.parameters b hb hb' j) (model j) E (R + 1) hρ (by linarith)
  have hC₂ : Cfa * τ ^ (1 / 4 : ℝ) + δ * ε / 2 ≤ max Cfa 0 * τ ^ (1 / 4 : ℝ) + δ * ε / 2 := by
    have : 0 ≤ τ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hτ.le _
    nlinarith [le_max_left Cfa 0]
  have hnn : 0 ≤ max Cfa 0 * τ ^ (1 / 4 : ℝ) + δ * ε / 2 := by
    have : 0 ≤ τ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hτ.le _
    have : 0 ≤ max Cfa 0 := le_max_right _ _
    positivity
  set C₁ := Cc / Real.sqrt (1 - 2 * b) * (2 * (R + 1) / Parameters.semicircleDensity E)
    with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hbound : ENNReal.ofReal |(∫ H, se_physIntegrand (s.parameters b hb hb' j) E f H
      ∂((model j).law : Measure (s.parameters b hb hb' j).SiteMatrix)) -
        (crossingLaplace (s.parameters b hb hb' j) (model j) 0 E (reflectTest f)).toReal| ≤
      ENNReal.ofReal (M * C₁ + δ⁻¹ * (max Cfa 0 * τ ^ (1 / 4 : ℝ) + δ * ε / 2)) := by
    refine hfin.trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg hM0 hC₁) (mul_nonneg (inv_nonneg.2 hδ.le) hnn),
      ENNReal.ofReal_mul hM0, ENNReal.ofReal_mul (inv_nonneg.2 hδ.le)]
    have hj2' := hj2.trans (ENNReal.ofReal_le_ofReal hC₂)
    gcongr
    exact hcnt
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hbound
  have heq : δ⁻¹ * (max Cfa 0 * τ ^ (1 / 4 : ℝ) + δ * ε / 2) =
      max Cfa 0 * τ ^ (1 / 4 : ℝ) / δ + ε / 2 := by
    field_simp
  rw [heq] at hbound
  calc |(∫ H, se_physIntegrand (s.parameters b hb hb' j) E f H
          ∂((model j).law : Measure (s.parameters b hb hb' j).SiteMatrix)) -
        sineLaplaceFunctional f|
      ≤ |(∫ H, se_physIntegrand (s.parameters b hb hb' j) E f H
          ∂((model j).law : Measure (s.parameters b hb hb' j).SiteMatrix)) -
          (crossingLaplace (s.parameters b hb hb' j) (model j) 0 E (reflectTest f)).toReal| +
        |(crossingLaplace (s.parameters b hb hb' j) (model j) 0 E (reflectTest f)).toReal -
          sineLaplaceFunctional f| := abs_sub_le _ _ _
    _ ≤ C₁ * M + max Cfa 0 * τ ^ (1 / 4 : ℝ) / δ + ε := by nlinarith [hbound, hj1]

/-!
## 5. Realizations and the main theorem
-/

/-- The Laplace functional of a finite realization is that of the canonical ordered spectrum. -/
theorem se_realization_integral {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (f : ℝ → ℝ) :
    ∫ H, Real.exp (-∑ α, f (R.spectral.unfoldedEigenvalue E H α))
        ∂(R.model.law : Measure p.SiteMatrix) =
      ∫ H, se_physIntegrand p E f H ∂(R.model.law : Measure p.SiteMatrix) := by
  refine integral_congr_ae ?_
  filter_upwards [BlockBand.QUE.Fourier.spectral_eigenvalue_eq_canonical_ae R.spectral] with H heig
  simp only [se_physIntegrand, Parameters.SpectralRealization.unfoldedEigenvalue, heig,
    microCoord]

/-- The rate clause of the sine endpoint theorem. Law:
the exact physical law of the original ring (`FiniteRealization`, every ordered spectral
realization; unfolding `u_α = Nρ(E)(λ_α - E)`). Fixed first: `0 < b < 1/2`, `-2 < E < 2`,
`T₀ > 0` (section setup) and a nonnegative `C^∞` compactly supported `f`; then
`C = C_f` (depending also on `b, E, T₀`); then every `0 < τ ≤ min(1, T₀)`, every critical sequence
(`W → ∞`, `n/W → τ`) and realizations:
`limsup_j |E exp(-Σ_α f(u_α)) - L_sine(f)| ≤ C τ^{1/8}`, written `∀ ε > 0, ∀ᶠ j, · ≤ Cτ^{1/8} + ε`.
`L_sine = sineLaplaceFunctional` (the sine-kernel Fredholm expansion, the Laplace functional
of every `IsSineLaw` law). -/
def SineEndpointRate : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ T₀ : ℝ, 0 < T₀ →
    ∀ f : CompactlySupportedContinuousMap ℝ ℝ, ContDiff ℝ ∞ (f : ℝ → ℝ) → (∀ x, 0 ≤ f x) →
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ min 1 T₀ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)), ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop,
          |(∫ H, Real.exp (-∑ α, f ((R j).spectral.unfoldedEigenvalue E H α))
              ∂((R j).model.law : Measure (s.parameters b hb hb' j).SiteMatrix)) -
            sineLaplaceFunctional f| ≤ C * τ ^ (1 / 8 : ℝ) + ε

/-- The consequence clause of the sine endpoint theorem: for every critical
family (`IsCriticalFamily`, the critical limit `𝒳_{τ,b,E}` of `endpoints`) and every law
satisfying `IsSineLaw`, `spectralProjectionLaw (family τ) → sineLaw` as `τ ↓ 0`. -/
def SineEndpointLimitClause : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
      ∀ sineLaw : ProbabilityMeasure (VaguePointMeasure ℝ), IsSineLaw sineLaw →
        Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ)) atBot (𝓝 sineLaw)

/-- **The sine endpoint theorem**: the rate clause and the consequence clause. -/
def SineEndpointStatement : Prop := SineEndpointRate ∧ SineEndpointLimitClause

/-- **The sine endpoint theorem, rate clause**, from `ExternalSine`, `CoareaContract`,
`PairRegularEventContract`, `PhysicalBlockConditionalCount` and `FlowAdmissionStatement`. -/
theorem sineEndpoint_rate (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hFA : FlowAdmissionStatement) : SineEndpointRate := by
  intro b hb hb' E hE1 hE2 T₀ hT₀ f hfs hf0
  obtain ⟨R, hR, hfR⟩ := se_support_bound f
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport f.hasCompactSupport hfs
    (by simp)
  obtain ⟨C₁, C₂, hC₁, hC₂, hcore⟩ :=
    se_core hExt hCo hPair hCount hFA b hb hb' E hE1 hE2 T₀ hT₀ f hf0 R hR hfR
  refine ⟨C₁ * L + C₂, fun τ hτ hτT s Rr ε hε => ?_⟩
  have hτ1 : τ ≤ 1 := hτT.trans (min_le_left _ _)
  have hτT₀ : τ ≤ T₀ := hτT.trans (min_le_right _ _)
  set δ := τ ^ (1 / 8 : ℝ) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hτ _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one hτ.le hτ1 (by norm_num)
  have hM : ∀ x y, |x - y| ≤ δ → |f x - f y| ≤ L * δ := fun x y hxy => by
    have := hL.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_left hxy L.2)
  have hpow : τ ^ (1 / 4 : ℝ) / δ = δ := by
    have h : τ ^ (1 / 4 : ℝ) = δ * δ := by
      rw [hδdef, ← Real.rpow_add hτ]
      norm_num
    rw [h, mul_div_assoc, div_self hδ.ne', mul_one]
  filter_upwards [hcore δ (L * δ) hδ hδ1 hM τ hτ hτT₀ s (fun j => (Rr j).model) ε hε]
    with j hj
  rw [se_realization_integral]
  rw [mul_div_assoc, hpow] at hj
  calc _ ≤ C₁ * (L * δ) + C₂ * δ + ε := hj
    _ = (C₁ * L + C₂) * τ ^ (1 / 8 : ℝ) + ε := by rw [hδdef]; ring

/-- **The consequence clause for every family with the critical convergence and unit
intensity**: if `family τ` is the limit of the physical marked
laws along every critical sequence and realization (the convergence clause of `IsCriticalFamily`
and of `IsJointRecoveryFamily`) and has unit spectral intensity, then
`spectralProjectionLaw (family τ) → sineLaw` as `τ ↓ 0`. -/
theorem sineEndpoint_tendsto (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hFA : FlowAdmissionStatement) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (hE1 : -2 < E) (hE2 : E < 2)
    (family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure)
    (hconv : ∀ (τ : PositiveRatio) (s : CriticalSequence τ.1)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
        Tendsto (fun j => (R j).markedLaw E) atTop (𝓝 (family τ)))
    (hint : ∀ τ, HasUnitSpectralIntensity (family τ))
    (sineLaw : ProbabilityMeasure (VaguePointMeasure ℝ)) (hsine : IsSineLaw sineLaw) :
    Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ)) atBot (𝓝 sineLaw) := by
  refine se_tendsto_sineLaw (fun g hg τ => se_moment_of_unitIntensity (hint τ) g hg) ?_
    sineLaw hsine
  intro f hf0
  obtain ⟨R, hR, hfR⟩ := se_support_bound f
  obtain ⟨C₁, C₂, hC₁, hC₂, hcore⟩ :=
    se_core hExt hCo hPair hCount hFA b hb hb' E hE1 hE2 1 one_pos f hf0 R hR hfR
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη' : 0 < η / (4 * (C₁ + 1)) := by positivity
  obtain ⟨δ₀, hδ₀, hunif⟩ :=
    Metric.uniformContinuous_iff.1 (CompactlySupportedContinuousMapClass.uniformContinuous f) _ hη'
  set δ := min (δ₀ / 2) 1 with hδdef
  have hδ : 0 < δ := lt_min (half_pos hδ₀) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hM : ∀ x y, |x - y| ≤ δ → |f x - f y| ≤ η / (4 * (C₁ + 1)) := fun x y h => by
    have h' : dist x y < δ₀ := by
      rw [Real.dist_eq]
      linarith [min_le_left (δ₀ / 2) 1]
    have := hunif h'
    rw [Real.dist_eq] at this
    exact this.le
  set θ : ℝ := η * δ / (4 * (C₂ + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  set τ₀ : ℝ := min 1 (θ ^ (4 : ℝ)) with hτ₀def
  have hτ₀ : 0 < τ₀ := lt_min one_pos (Real.rpow_pos_of_pos hθ _)
  filter_upwards [eventually_le_atBot (⟨τ₀, hτ₀⟩ : PositiveRatio)] with τ hτ
  have hττ₀ : τ.1 ≤ τ₀ := hτ
  have hτ1 : τ.1 ≤ 1 := hττ₀.trans (min_le_left _ _)
  have hτpow : τ.1 ^ (1 / 4 : ℝ) ≤ θ := by
    calc τ.1 ^ (1 / 4 : ℝ) ≤ (θ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow τ.2.le (hττ₀.trans (min_le_right _ _)) (by norm_num)
      _ = θ := by
          rw [← Real.rpow_mul hθ.le]
          norm_num
  set s := se_criticalSequence τ.1 τ.2
  let Rr : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j => constructFiniteRealization _
  have hlim := se_tendsto_spectralLaplace (hconv τ s Rr) f hf0
  simp_rw [se_spectralLaplace_markedLaw, se_realization_integral] at hlim
  have hbd : |(∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
      ∂(spectralProjectionLaw (family τ) : Measure (VaguePointMeasure ℝ))) -
        sineLaplaceFunctional f| ≤
      C₁ * (η / (4 * (C₁ + 1))) + C₂ * τ.1 ^ (1 / 4 : ℝ) / δ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev := hcore δ _ hδ hδ1 hM τ.1 τ.2 hτ1 s (fun j => (Rr j).model) ε hε
    exact le_of_tendsto ((hlim.sub_const (sineLaplaceFunctional f)).abs) hev
  have h1 : C₁ * (η / (4 * (C₁ + 1))) ≤ η / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : C₂ * τ.1 ^ (1 / 4 : ℝ) / δ ≤ η / 4 := by
    rw [div_le_iff₀ hδ]
    calc C₂ * τ.1 ^ (1 / 4 : ℝ) ≤ C₂ * θ := mul_le_mul_of_nonneg_left hτpow hC₂
      _ = η / 4 * δ * (C₂ / (C₂ + 1)) := by rw [hθdef]; field_simp
      _ ≤ η / 4 * δ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by positivity)]
          linarith
      _ = η / 4 * δ := mul_one _
  rw [Real.dist_eq]
  linarith

/-- **The sine endpoint theorem, both clauses**, from `ExternalSine`, `CoareaContract`,
`PairRegularEventContract`, `PhysicalBlockConditionalCount` and the flow admission statement
`FlowAdmissionStatement`.
-/
theorem sineEndpoint (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hFA : FlowAdmissionStatement) : SineEndpointStatement := by
  refine ⟨sineEndpoint_rate hExt hCo hPair hCount hFA, ?_⟩
  intro b hb hb' E hE1 hE2 family hfam sineLaw hsine
  obtain ⟨-, -, hconv, -, hint, -⟩ := hfam
  exact sineEndpoint_tendsto hExt hCo hPair hCount hFA b hb hb' E hE1 hE2 family hconv hint
    sineLaw hsine

/-- **The consequence clause for the critical limit of `JointRecoveryContract`**:
the unique joint-recovery family converges to the sine law as `τ ↓ 0`.
-/
theorem sineEndpoint_jointRecovery (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hFA : FlowAdmissionStatement) (hJR : JointRecoveryContract) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
      ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
        IsJointRecoveryFamily b E hb hb' family ∧
          ∀ sineLaw : ProbabilityMeasure (VaguePointMeasure ℝ), IsSineLaw sineLaw →
            Tendsto (fun τ : PositiveRatio => spectralProjectionLaw (family τ)) atBot
              (𝓝 sineLaw) := by
  intro b E hb hb' hE
  obtain ⟨F, hF, huniq⟩ := hJR b E hb hb' hE
  refine ⟨F, ⟨hF, fun sineLaw hsine => sineEndpoint_tendsto hExt hCo hPair hCount hFA b hb hb'
    E hE.1 hE.2 F hF.convergence hF.unitIntensity sineLaw hsine⟩, fun G hG => huniq G hG.1⟩

/-!
## 6. Composition with the local mass flatness theorem
-/

/-- **The sine endpoint theorem with flow admission supplied** by
`flowAdmission_of_localMassFlat`: from `ExternalSine`, `CoareaContract`,
`PairRegularEventContract`, `PhysicalBlockConditionalCount`, `Clocks.ExactPalmContract`,
`FaShiftedMassPalm` and the local mass flatness theorem (`LocalMassFlatStatement`).
-/
theorem sineEndpoint_of_localMassFlat (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hPalm : ExactPalmContract) (hShift : FaShiftedMassPalm)
    (hLMF : LocalMassFlatStatement) : SineEndpointStatement :=
  sineEndpoint hExt hCo hPair hCount (flowAdmission_of_localMassFlat hPalm hCo hShift hCount hLMF)

/-- **The sine endpoint theorem with local mass flatness supplied** by `localMassFlat`:
additionally from `NegativeClockContract`, `ClockSmallBallContract`, `CriticalDensity`,
`LmfTaggedFlat` and `LmfMicroscopicTagComparison`. -/
theorem sineEndpoint_of_localMassFlatInputs (hExt : ExternalSine) (hCo : CoareaContract)
    (hPair : PairRegularEventContract) (hCount : PhysicalBlockConditionalCount)
    (hPalm : ExactPalmContract) (hShift : FaShiftedMassPalm)
    (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract) (hDens : CriticalDensity)
    (hTag : LmfTaggedFlat) (hMicro : LmfMicroscopicTagComparison) : SineEndpointStatement :=
  sineEndpoint_of_localMassFlat hExt hCo hPair hCount hPalm hShift
    (localMassFlat hNeg hSmall hDens hTag hMicro)

end BlockBand.Endpoints
