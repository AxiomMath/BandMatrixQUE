module

public import BlockBand.SourceProcess.ClosingLeak.Bound
public import BlockBand.SourceProcess.Closing.Split
public import BlockBand.SourceProcess.Closing.Routes
public import BlockBand.SourceProcess.FullSource.DeltaHolds

/-!
# `ClosingLeakage` from `SmallChannelLeakage` and the tag moments

`abs_sampled_sub_closed_le`: at every `W`, if each injection's leaked mass satisfies
`∫⁻ (leakTerm_{il})^{1/2} ≤ δ`, then
`|sampledPhysTransform - closedSampledTransform| ≤ δ M Σ_{j,i} √a_{ji}`
(pointwise bound `abs_integrand_sub_le`, then `ℝ≥0∞` linearity).

`closingLeakage_of_smallChannelLeakage hS hFM`: `SmallChannelLeakage` (with
`ε' = Mδ²/2`, `δ = ε/(M(S+1))`, for every test `q_i`) and `FullSourceMomentsContract`
(only for integrability of the path leak) give `ClosingLeakage`. `closingLeakage_holds` replaces
`hFM` by the Gaussian inputs `hGA hLp hSR` (`FullSource.fullSourceMoments_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.Sampling BlockBand.SourceProcess.ClosingAux
open scoped ComplexOrder

variable {W : ℕ}

/-- **The closing error at one width.** -/
theorem abs_sampled_sub_closed_le (b E s T h : ℝ) {p J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) (M W : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hterm : ∀ il : Fin p × Fin M,
      ∫⁻ y, ENNReal.ofReal (Real.sqrt (leakTerm b E s T h q M W il y))
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) ≤ ENNReal.ofReal δ) :
    |sampledPhysTransform b E T q a M W - closedSampledTransform b E s T h q a M W| ≤
      δ * M * ∑ j, ∑ i, Real.sqrt (a j i) := by
  have := isProbabilityMeasure_sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ hq M
  set μ := (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw
  have hphys : sampledPhysTransform b E T q a M W = ∫ y, physIntegrand b E T q a M W y.1 ∂μ := by
    rw [sampledPhysTransform_eq, integral_fun_fst]; simp
  have hI1 : Integrable (fun y => physIntegrand b E T q a M W y.1) μ :=
    (integrable_sampledIntegrand b E W ⌊(W : ℝ) * T⌋₊ hq ha M _).comp_fst phaseLaw
  have hI2 := integrable_closedIntegrand b E s T h hq ha M W
  have hS0 : 0 ≤ δ * M * ∑ j, ∑ i, Real.sqrt (a j i) :=
    mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  rw [hphys, closedSampledTransform_eq, ← integral_sub hI1 hI2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hg : Integrable (fun y => |physIntegrand b E T q a M W y.1 -
      closedIntegrand b E s T h q a M W y|) μ := (hI1.sub hI2).abs
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => abs_nonneg _)
    hg.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hS0 ?_
  have hmL : ∀ il, Measurable fun y => ENNReal.ofReal (Real.sqrt (leakTerm b E s T h q M W il y)) :=
    fun il => ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp (measurable_leakTerm b E s T h q M W il))
  calc ∫⁻ y, ENNReal.ofReal |physIntegrand b E T q a M W y.1 - closedIntegrand b E s T h q a M W y| ∂μ
      ≤ ∫⁻ y, ∑ j, ∑ il : Fin p × Fin M, ENNReal.ofReal (Real.sqrt (a j il.1)) *
          ENNReal.ofReal (Real.sqrt (leakTerm b E s T h q M W il y)) ∂μ := by
        refine lintegral_mono fun y => ?_
        refine (ENNReal.ofReal_le_ofReal (abs_integrand_sub_le b E s T h hq ha M W y)).trans
          (le_of_eq ?_)
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun il _ =>
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun il _ =>
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
        exact Finset.sum_congr rfl fun il _ => ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ = ∑ j, ∑ il : Fin p × Fin M, ENNReal.ofReal (Real.sqrt (a j il.1)) *
          ∫⁻ y, ENNReal.ofReal (Real.sqrt (leakTerm b E s T h q M W il y)) ∂μ := by
        rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun il _ =>
          (hmL il).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ fun il _ => (hmL il).const_mul _]
        exact Finset.sum_congr rfl fun il _ => lintegral_const_mul _ (hmL il)
    _ ≤ ∑ j, ∑ il : Fin p × Fin M, ENNReal.ofReal (Real.sqrt (a j il.1)) * ENNReal.ofReal δ :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun il _ =>
          mul_le_mul_right (hterm il) _
    _ = ENNReal.ofReal (∑ j, ∑ il : Fin p × Fin M, Real.sqrt (a j il.1) * δ) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => Finset.sum_nonneg fun il _ =>
          mul_nonneg (Real.sqrt_nonneg _) hδ]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun il _ => mul_nonneg (Real.sqrt_nonneg _) hδ]
        exact Finset.sum_congr rfl fun il _ => (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
    _ = ENNReal.ofReal (δ * M * ∑ j, ∑ i, Real.sqrt (a j i)) := by
        congr 1
        simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- **`ClosingLeakage` from `SmallChannelLeakage`** and the tag moments (integrability only). -/
theorem closingLeakage_of_smallChannelLeakage (hS : SmallChannelLeakage)
    (hFM : FullSourceMomentsContract) : ClosingLeakage := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq J a ha M hM ε hε
  have hq0 : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  have hT : 0 < T := hs.trans hsT
  set S := ∑ j, ∑ i, Real.sqrt (a j i)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set δ := ε / (M * (S + 1))
  have hδ : 0 < δ := by positivity
  have hε' : 0 < (M : ℝ) * δ ^ 2 / 2 := by positivity
  have hsmall := eventually_all.2 fun i => hS b hb0 hb E hE1 hE2 s T hs hsT (q i) (hq i) _ hε'
  filter_upwards [hsmall, Ioo_mem_nhdsGT zero_lt_one] with h hh hh01
  filter_upwards [eventually_all.2 hh,
    eventually_lintegral_leakTerm hb0 hb hE1 hE2 hs hsT hh01.1 hh01.2 hq0 hM,
    eventually_all.2 fun i => eventually_integrable_leak hFM hb0 hb hE1 hE2 (s := s) (h := h) hT
      (hq0 i)] with W hWε hWL hWI
  refine (abs_sampled_sub_closed_le b E s T h hq0 ha M W hδ.le fun il =>
    lintegral_sqrt_leakTerm_le hq0 hM il hδ.le (hWL il) (hWI il.1) (hWε il.1)).trans ?_
  have e : δ * M * S = ε * (S / (S + 1)) := by
    simp only [δ]; field_simp
  rw [e]
  exact mul_le_of_le_one_right hε.le ((div_le_one (by linarith)).2 (by linarith))

/-- **`ClosingLeakage` from `SmallChannelLeakage` and the Gaussian inputs.** -/
theorem closingLeakage_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) (hS : SmallChannelLeakage) : ClosingLeakage :=
  closingLeakage_of_smallChannelLeakage hS (FullSource.fullSourceMoments_holds hGA hLp hSR)

end BlockBand.SourceProcess.ClosingLeak
