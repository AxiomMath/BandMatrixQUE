module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyAtom
public import BlockBand.Endpoints.Normalization.VanishingBlockAtomTorus
public import BlockBand.Counting.PhysicalMarkedTightness
public import BlockBand.Model.Construction.VagueTranslation

/-!
# Vanishing block atoms: marked functionals and count moments

For a continuous compactly supported weight `w` and `m : ℕ` the mark test
`g_m(u,ν) = |w(u)| Q_m(ν)` (with the pair energy `pairEnergy`) is a compactly supported
continuous function on `ℝ × P(𝕋)` (`P(𝕋)` is compact), so `ξ ↦ ∫ g_m dξ` is continuous on the
marked point-measure space (its topology is the vague topology). At every finite level:

* `blockAtomStatistic ≤ E ∫ g_m dξ` under the exact physical law (`Σ_k p_k² ≤ Q_m(ν)`);
* `∫ g dξ ≤ C · #{α : |u_α| ≤ L}` whenever `0 ≤ g ≤ C 1{|u| ≤ L}`;
* the count moment `E #{α : |u_α| ≤ L}² ≤ 2 exp(2 L K (e - 1))`, `K = C_PSSS/(√c ρ(E))`
  (the counting theorem, through the exponential count bound, which uses only the PSSS input
  `SourceContract`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Counting BlockBand.External.PSSS
open BlockBand.Internal.Contracts.Clocks
open scoped ENNReal

/-- The functional `ξ ↦ ∫ g dξ` of a compactly supported continuous mark test. -/
def markedFunctional (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (ξ : MarkedPointMeasure) : ℝ :=
  ξ.marked.coordinate g

theorem continuous_markedFunctional (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) :
    Continuous (markedFunctional g) :=
  (continuous_vaguePointMeasure_coordinate g).comp continuous_induced_dom

theorem measurable_markedFunctional (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) :
    Measurable (markedFunctional g) :=
  (continuous_markedFunctional g).measurable

/-- Compact support of `x ↦ |w(x.1)| * h(x.2)` on `ℝ × P(𝕋)`. -/
theorem hasCompactSupport_markTest {w : ℝ → ℝ} (hws : HasCompactSupport w)
    (h : MassProfile → ℝ) :
    HasCompactSupport (fun x : MarkedSpectralSpace => |w x.1| * h x.2) := by
  apply HasCompactSupport.intro (K := tsupport w ×ˢ (Set.univ : Set MassProfile))
    (hws.isCompact.prod isCompact_univ)
  intro x hx
  have hx1 : x.1 ∉ tsupport w := by
    intro h1
    exact hx ⟨h1, Set.mem_univ _⟩
  simp [image_eq_zero_of_notMem_tsupport hx1]

/-- The mark test `g_m(u,ν) = |w(u)| Q_m(ν)`. -/
def atomMarkTest {w : ℝ → ℝ} (hw : Continuous w) (hws : HasCompactSupport w) (m : ℕ) :
    CompactlySupportedContinuousMap MarkedSpectralSpace ℝ where
  toFun x := |w x.1| * pairEnergy m x.2
  continuous_toFun :=
    (continuous_abs.comp (hw.comp continuous_fst)).mul ((continuous_pairEnergy m).comp continuous_snd)
  hasCompactSupport' := hasCompactSupport_markTest hws (pairEnergy m)

/-- The weight test `g(u,ν) = |w(u)|`, which dominates every `g_m`. -/
def weightMarkTest {w : ℝ → ℝ} (hw : Continuous w) (hws : HasCompactSupport w) :
    CompactlySupportedContinuousMap MarkedSpectralSpace ℝ where
  toFun x := |w x.1|
  continuous_toFun := continuous_abs.comp (hw.comp continuous_fst)
  hasCompactSupport' := by
    have h := hasCompactSupport_markTest hws (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    exact h

theorem atomMarkTest_apply {w : ℝ → ℝ} (hw : Continuous w) (hws : HasCompactSupport w) (m : ℕ)
    (x : MarkedSpectralSpace) : atomMarkTest hw hws m x = |w x.1| * pairEnergy m x.2 := rfl

theorem weightMarkTest_apply {w : ℝ → ℝ} (hw : Continuous w) (hws : HasCompactSupport w)
    (x : MarkedSpectralSpace) : weightMarkTest hw hws x = |w x.1| := rfl

theorem atomMarkTest_nonneg {w : ℝ → ℝ} (hw : Continuous w) (hws : HasCompactSupport w) (m : ℕ)
    (x : MarkedSpectralSpace) : 0 ≤ atomMarkTest hw hws m x :=
  mul_nonneg (abs_nonneg _) (pairEnergy_nonneg m _)

theorem atomMarkTest_le_weight {w : ℝ → ℝ} (hw : Continuous w) (hws : HasCompactSupport w)
    (m : ℕ) (x : MarkedSpectralSpace) : atomMarkTest hw hws m x ≤ weightMarkTest hw hws x := by
  rw [atomMarkTest_apply, weightMarkTest_apply]
  exact mul_le_of_le_one_right (abs_nonneg _) (pairEnergy_le_one m _)

/-- On every raw matrix the physical marked configuration integrates a mark test as the finite
sum over its canonical atoms. -/
theorem markedFunctional_config (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (p : Parameters) (E : ℝ) (H : p.SiteMatrix) :
    markedFunctional g (physicalOrderedMarkedConfig p E H) =
      ∑ α : Fin p.N, g (physicalCanonicalMarkedLocations p E H α) := by
  have : BorelSpace MarkedSpectralSpace := markedSpectralSpace_borelSpace
  unfold markedFunctional VaguePointMeasure.coordinate
  change (∫ x, g x ∂(finiteAtomicMeasure
      (physicalSpectralDataLocations p E (physicalSpectralData p H)))) = _
  rw [finiteAtomicMeasure_eq_sum_dirac,
    integral_finsetSum_measure (fun α _ => integrable_dirac (by simp))]
  simp only [integral_dirac]
  rfl

/-- If `0 ≤ g ≤ C 1{|u| ≤ L}`, then `∫ g dξ ≤ C · #{α : |u_α| ≤ L}` at every finite level. -/
theorem markedFunctional_config_le_count
    (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (C L : ℝ) (hgC : ∀ x, g x ≤ C) (hgL : ∀ x : MarkedSpectralSpace, L < |x.1| → g x = 0)
    (p : Parameters) (E : ℝ) (H : p.SiteMatrix) :
    markedFunctional g (physicalOrderedMarkedConfig p E H) ≤
      C * (physicalCanonicalLocalCount p E L H : ℝ) := by
  classical
  rw [markedFunctional_config]
  have hcount : (physicalCanonicalLocalCount p E L H : ℝ) =
      ∑ α : Fin p.N, if (physicalCanonicalMarkedLocations p E H α).1 ∈ Icc (-L) L
        then (1 : ℝ) else 0 := by
    simp [physicalCanonicalLocalCount, finiteSpectralCount, Finset.sum_boole]
  rw [hcount, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  by_cases hα : (physicalCanonicalMarkedLocations p E H α).1 ∈ Icc (-L) L
  · simp only [hα, ↓reduceIte, mul_one]
    exact hgC _
  · simp only [hα, ↓reduceIte, mul_zero]
    have : L < |(physicalCanonicalMarkedLocations p E H α).1| :=
      not_le.mp (fun h => hα (abs_le.mp h))
    exact (hgL _ this).le

/-- **Block atom versus the mark test:** on every Hermitian matrix with separable characteristic
polynomial, `Σ_α |w(u_α)| Σ_k p_{αk}² ≤ ∫ g_m dξ` for the physical marked configuration. -/
theorem blockAtomSum_le_markedFunctional {w : ℝ → ℝ} (hw : Continuous w)
    (hws : HasCompactSupport w) (m : ℕ) (p : Parameters) (E : ℝ) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) :
    ∑ α : Fin p.N, |w (microCoord p E (physicalOrderedEigenvalue p H α))| *
        ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2 ≤
      markedFunctional (atomMarkTest hw hws m) (physicalOrderedMarkedConfig p E H) := by
  rw [markedFunctional_config]
  apply Finset.sum_le_sum
  intro α _
  have hloc := physicalSpectralDataLocations_eq p E H ⟨hH, hsep⟩ α
  change _ ≤ atomMarkTest hw hws m
    (physicalSpectralDataLocations p E (physicalSpectralData p H) α)
  rw [hloc, atomMarkTest_apply]
  exact mul_le_mul_of_nonneg_left (sum_sq_blockMass_le_pairEnergy p H hH hsep α m)
    (abs_nonneg _)

/-- **Count moment** (the counting theorem, PSSS): `E #{α : |u_α| ≤ L}² ≤ 2 exp(2 L K (e - 1))`
under the exact physical law, with `K = physicalUnfoldedConstant source ρ(E)`. -/
theorem integral_localCount_sq_le (p : Parameters) (model : p.GaussianRingModel)
    (source : SourceContract.{0}) (E L : ℝ) (hE : -2 < E ∧ E < 2) (hL : 0 ≤ L) :
    (∫ H, (physicalCanonicalLocalCount p E L H : ℝ) ^ 2 ∂(model.law : Measure p.SiteMatrix)) ≤
      2 * Real.exp (2 * L * p.physicalUnfoldedConstant source (Parameters.semicircleDensity E) *
        (Real.exp 1 - 1)) := by
  have hrho := Parameters.semicircleDensity_pos hE
  have hmeas := measurable_physicalCanonicalLocalCount p E L
  have hbdd (H : p.SiteMatrix) : (physicalCanonicalLocalCount p E L H : ℝ) ≤ p.N := by
    have : physicalCanonicalLocalCount p E L H ≤ p.N := by
      unfold physicalCanonicalLocalCount finiteSpectralCount
      exact (Finset.card_le_univ _).trans (by simp)
    exact_mod_cast this
  have hexp_int : Integrable (fun H => Real.exp (physicalCanonicalLocalCount p E L H : ℝ))
      (model.law : Measure p.SiteMatrix) := by
    apply Integrable.of_bound
      ((measurable_from_nat.comp hmeas).exp.aestronglyMeasurable) (Real.exp p.N)
    filter_upwards with H
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hbdd H)
  have hsq_int : Integrable (fun H => (physicalCanonicalLocalCount p E L H : ℝ) ^ 2)
      (model.law : Measure p.SiteMatrix) := by
    apply Integrable.of_bound
      (((measurable_from_nat.comp hmeas).pow_const 2).aestronglyMeasurable) ((p.N : ℝ) ^ 2)
    filter_upwards with H
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hbdd H) 2
  have hpt (H : p.SiteMatrix) : (physicalCanonicalLocalCount p E L H : ℝ) ^ 2 ≤
      2 * Real.exp (physicalCanonicalLocalCount p E L H : ℝ) := by
    have := Real.quadratic_le_exp_of_nonneg
      (Nat.cast_nonneg (α := ℝ) (physicalCanonicalLocalCount p E L H))
    have h0 : (0 : ℝ) ≤ physicalCanonicalLocalCount p E L H := Nat.cast_nonneg _
    linarith
  have hae := physicalCanonicalLocalCount_eq_physical_ae p model E L
  have hexp : (∫ H, Real.exp (physicalCanonicalLocalCount p E L H : ℝ)
      ∂(model.law : Measure p.SiteMatrix)) ≤
      Real.exp (2 * L * p.physicalUnfoldedConstant source (Parameters.semicircleDensity E) *
        (Real.exp 1 - 1)) := by
    have h := model.physicalUnfoldedIntervalCount_exponentialBound source
      ⟨0, Matrix.isHermitian_zero⟩ E (Parameters.semicircleDensity E) hrho L 1 hL zero_le_one
    rw [integral_congr_ae (hae.mono fun H hH => by
      show Real.exp (physicalCanonicalLocalCount p E L H : ℝ) =
        Real.exp (1 * (p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E
          (Parameters.semicircleDensity E) (-L) L H : ℝ))
      rw [hH, one_mul])]
    exact h
  calc (∫ H, (physicalCanonicalLocalCount p E L H : ℝ) ^ 2 ∂(model.law : Measure p.SiteMatrix))
      ≤ ∫ H, 2 * Real.exp (physicalCanonicalLocalCount p E L H : ℝ)
          ∂(model.law : Measure p.SiteMatrix) :=
        integral_mono hsq_int (hexp_int.const_mul 2) hpt
    _ = 2 * ∫ H, Real.exp (physicalCanonicalLocalCount p E L H : ℝ)
          ∂(model.law : Measure p.SiteMatrix) := integral_const_mul _ _
    _ ≤ _ := by linarith

end BlockBand.Endpoints.Normalization
