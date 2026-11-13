module

public import BlockBand.QUE.Assembly.PhysicalAngularReduction
public import BlockBand.Model.Construction.SpectralPhysicalAE

/-!
# Elementary bounds for the cutoff removal in the angular estimate

* `IsAngularTest.bound_nonneg`, `IsAngularTest.lip_nonneg`: `M ≥ 0`, `L_φ ≥ 0` (phase invariance
  at `c = -1`).
* `abs_dysonCenter_le_one`: the clipped Dyson center lies in `[-1, 1]`.
* `ae_norm_integrand_le`: `|(v*Jv - j)φ(ψ_α)| ≤ 2M` almost surely under the pair law.
* `norm_integral_le_add_of_weight`: `‖∫ f‖ ≤ ‖∫ a f‖ + B μ(S)` if `‖f‖ ≤ B` a.e. and
  `‖1 - a‖ ≤ 1_S` (no measurability of `S` is needed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Assembly

open MeasureTheory BlockBand.Model.Construction BlockBand.QUE.PhysicalAngularReduction
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.QUE.Fourier
open scoped ENNReal

/-- A unit vector of `ℂ^ι` for nonempty `ι`. -/
theorem exists_unit {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∃ e : ι → ℂ, l2Norm e = 1 := by
  obtain ⟨k⟩ := (inferInstance : Nonempty ι)
  refine ⟨Pi.single k 1, ?_⟩
  unfold l2Norm
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem IsAngularTest.bound_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {φ : (ι → ℂ) → ℂ} {M L : ℝ} (h : IsAngularTest φ M L) : 0 ≤ M := by
  obtain ⟨e, he⟩ := exists_unit (ι := ι)
  exact (norm_nonneg _).trans (h.bound e he)

theorem l2Norm_neg {ι : Type} [Fintype ι] (x : ι → ℂ) : l2Norm (-x) = l2Norm x := by
  unfold l2Norm; simp

theorem IsAngularTest.lip_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {φ : (ι → ℂ) → ℂ} {M L : ℝ} (h : IsAngularTest φ M L) : 0 ≤ L := by
  obtain ⟨e, he⟩ := exists_unit (ι := ι)
  have hneg : l2Norm (-e) = 1 := by rw [l2Norm_neg, he]
  have h1 := h.lipschitz e (-e) he hneg
  have hph : φ ((-1 : ℂ) • e) = φ e := h.phase e (-1) (by simp)
  rw [neg_one_smul] at hph
  have h2 : l2Norm (e - -e) = 2 := by
    have hk : ∀ k, ‖(e - -e) k‖ ^ 2 = 4 * ‖e k‖ ^ 2 := fun k => by
      rw [Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add, ← two_mul, norm_mul]; norm_num; ring
    have he2 : (∑ k, ‖e k‖ ^ 2) = 1 := by
      have := he; unfold l2Norm at this
      have h0 : 0 ≤ ∑ k, ‖e k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
      nlinarith [Real.sq_sqrt h0]
    unfold l2Norm
    rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum, he2, mul_one]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hph, sub_self, norm_zero, h2] at h1
  linarith

theorem abs_centerFormula_le_one (p : Parameters) (i : ZMod p.n) (Hres : p.SiteMatrix) (E : ℝ)
    (ζ : ℂ) : |centerFormula p i Hres E ζ| ≤ 1 := by
  unfold centerFormula
  exact abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem abs_dysonCenter_le_one (p : Parameters) (i : ZMod p.n) (cst : CenterDomainConstants)
    (α : Fin p.N) (Hres : p.SiteMatrix) (E : ℝ) : |dysonCenter p i cst α Hres E| ≤ 1 := by
  unfold dysonCenter
  split_ifs
  · exact abs_centerFormula_le_one p i Hres E _
  · simp

/-- The eigenvector is a unit vector almost surely under the pair law. -/
theorem ae_l2Norm_eigenvector (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (X : PairExtension p model) :
    ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm,
      l2Norm (physicalOrderedEigenvector p (X.Hm ω) α) = 1 := by
  filter_upwards [BlockBand.QUE.PairResidual.ae_extendedPairMeasure p model α i X
    (physicalOrderedEigenvector_totalMass_ae p model)] with ω h
  unfold l2Norm; rw [h α, Real.sqrt_one]

/-- `|(v*Jv - j)φ(ψ_α)| ≤ 2M` almost surely, for any center `j` with `|j| ≤ 1`. -/
theorem ae_norm_integrand_le (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (X : PairExtension p model) (c : X.Ω → ℝ) (hc : ∀ ω, |c ω| ≤ 1)
    {φ : (p.Site → ℂ) → ℂ} {M L : ℝ} (hφ : IsAngularTest φ M L) :
    ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm,
      ‖((physicalPairContrast p α i (X.Hm ω) - c ω : ℝ) : ℂ) *
          φ (physicalOrderedEigenvector p (X.Hm ω) α)‖ ≤ 2 * M := by
  filter_upwards [ae_l2Norm_eigenvector p model α i X] with ω hω
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |physicalPairContrast p α i (X.Hm ω) - c ω| ≤ 2 := by
    have := BlockBand.QUE.PairResidual.abs_physicalPairContrast_le_one p α i (X.Hm ω)
    have := hc ω
    exact (abs_sub _ _).trans (by linarith)
  have hM := hφ.bound _ hω
  calc _ ≤ 2 * M := mul_le_mul h1 hM (norm_nonneg _) (by norm_num)
    _ = 2 * M := rfl

/-- **Removal of a bounded observable.** If `‖f‖ ≤ B` a.e., `f` and `a f` are integrable and
`‖1 - a‖ ≤ 1_S` pointwise, then `‖∫ f‖ ≤ ‖∫ a f‖ + B μ(S)`. -/
theorem norm_integral_le_add_of_weight {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℂ} {a : Ω → ℂ} {B : ℝ}
    (hf : Integrable f μ) (haf : Integrable (fun ω => a ω * f ω) μ)
    (hfB : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ B) (S : Set Ω) (ha : ∀ ω, ‖1 - a ω‖ ≤ S.indicator 1 ω) :
    ‖∫ ω, f ω ∂μ‖ ≤ ‖∫ ω, a ω * f ω ∂μ‖ + B * μ.real S := by
  set T := toMeasurable μ S
  have hT : MeasurableSet T := measurableSet_toMeasurable μ S
  have hST : S ⊆ T := subset_toMeasurable μ S
  have hdiff : ‖∫ ω, f ω ∂μ - ∫ ω, a ω * f ω ∂μ‖ ≤ B * μ.real S := by
    rw [← integral_sub hf haf]
    have hint : Integrable (fun ω => T.indicator (fun _ => B) ω) μ :=
      (integrable_const B).indicator hT
    refine (norm_integral_le_of_norm_le hint ?_).trans ?_
    · filter_upwards [hfB] with ω hω
      have h1 : f ω - a ω * f ω = (1 - a ω) * f ω := by ring
      rw [h1, norm_mul]
      by_cases hω' : ω ∈ T
      · rw [Set.indicator_of_mem hω']
        have := ha ω
        have h2 : S.indicator (1 : Ω → ℝ) ω ≤ 1 := by
          by_cases h : ω ∈ S <;> simp [h]
        calc ‖1 - a ω‖ * ‖f ω‖ ≤ 1 * B :=
              mul_le_mul (this.trans h2) hω (norm_nonneg _) zero_le_one
          _ = B := one_mul B
      · rw [Set.indicator_of_notMem hω']
        have hS : ω ∉ S := fun h => hω' (hST h)
        have := ha ω
        rw [Set.indicator_of_notMem hS] at this
        have h0 : ‖1 - a ω‖ = 0 := le_antisymm this (norm_nonneg _)
        rw [h0, zero_mul]
    · rw [integral_indicator hT, setIntegral_const, smul_eq_mul, mul_comm]
      unfold T
      rw [Measure.real, Measure.real, measure_toMeasurable]
  have := norm_sub_norm_le (∫ ω, f ω ∂μ) (∫ ω, a ω * f ω ∂μ)
  linarith

end BlockBand.Angular.Assembly
