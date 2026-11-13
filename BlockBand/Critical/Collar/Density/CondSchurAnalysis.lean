module

public import BlockBand.Critical.Collar.Density.CondSchurPencil
public import BlockBand.DeterminantScore.PointwiseJacobi

/-!
# Conditional Schur identity: Analysis

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

Elementary analysis: continuity of the matrix inverse on the invertible locus, Cauchy-kernel
interval integrals `∫_{[a₁,a₂]} P_ε(x - μ) → 1_{[a₁,a₂]}(μ)` (`μ ∉ {a₁,a₂}`), finiteness of the
real poles `{x : det(D - x) = 0}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_eq_im_inv cauchyKernel_nonneg
  continuous_cauchyKernel measurable_cauchyKernel)
open scoped ComplexConjugate ComplexOrder

/-!
## Elementary analytic facts
-/

theorem continuousOn_inv_of_isUnit_det {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℂ} (hM : Continuous M) {K : Set X}
    (hK : ∀ p ∈ K, IsUnit (M p).det) : ContinuousOn (fun p => (M p)⁻¹) K := by
  have h : (fun p => (M p)⁻¹) = fun p => (M p).det⁻¹ • (M p).adjugate := by
    funext p; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((hM.matrix_det.continuousOn).inv₀ fun p hp => (hK p hp).ne_zero).smul
    hM.matrix_adjugate.continuousOn

theorem continuous_inv_of_isUnit_det {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℂ} (hM : Continuous M)
    (hK : ∀ p, IsUnit (M p).det) : Continuous (fun p => (M p)⁻¹) := by
  rw [← continuousOn_univ]
  exact continuousOn_inv_of_isUnit_det hM fun p _ => hK p

theorem cauchyKernel_le {ε : ℝ} (hε : 0 < ε) (y : ℝ) : cauchyKernel ε y ≤ (Real.pi * ε)⁻¹ := by
  unfold cauchyKernel
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg y, Real.pi_pos, sq_nonneg ε]

theorem setIntegral_cauchyKernel_Icc {ε : ℝ} (hε : 0 < ε) {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) (μ : ℝ) :
    ∫ x in Set.Icc a₁ a₂, cauchyKernel ε (x - μ) =
      Real.pi⁻¹ * (Real.arctan ((a₂ - μ) / ε) - Real.arctan ((a₁ - μ) / ε)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => Real.pi⁻¹ * Real.arctan ((x - μ) / ε))
      (cauchyKernel ε (x - μ)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x - μ) / ε) (1 / ε) x := by
      have := ((hasDerivAt_id x).sub_const μ).div_const ε
      simpa using this
    have h2 := ((Real.hasDerivAt_arctan ((x - μ) / ε)).comp x h1).const_mul Real.pi⁻¹
    refine h2.congr_deriv ?_
    unfold cauchyKernel
    have hp : 0 < Real.pi := Real.pi_pos
    field_simp
    ring
  have hc : Continuous fun x => cauchyKernel ε (x - μ) :=
    (continuous_cauchyKernel hε).comp (continuous_id.sub continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hc.intervalIntegrable _ _)]
  ring

theorem setIntegral_cauchyKernel_Icc_mem {ε : ℝ} (hε : 0 < ε) {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂)
    (μ : ℝ) : 0 ≤ ∫ x in Set.Icc a₁ a₂, cauchyKernel ε (x - μ) ∧
      ∫ x in Set.Icc a₁ a₂, cauchyKernel ε (x - μ) ≤ 1 := by
  rw [setIntegral_cauchyKernel_Icc hε ha]
  have hmono : Real.arctan ((a₁ - μ) / ε) ≤ Real.arctan ((a₂ - μ) / ε) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right (by linarith) hε.le)
  have h1 := Real.arctan_lt_pi_div_two ((a₂ - μ) / ε)
  have h2 := Real.neg_pi_div_two_lt_arctan ((a₁ - μ) / ε)
  have hp := Real.pi_pos
  constructor
  · exact mul_nonneg (inv_nonneg.2 hp.le) (by linarith)
  · rw [inv_mul_le_iff₀ hp]; linarith

theorem tendsto_arctan_div_nhdsGT {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0)
      (𝓝 (if 0 < c then Real.pi / 2 else -(Real.pi / 2))) := by
  have hinv := tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  simp_rw [div_eq_mul_inv]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · simp only [not_lt.2 hneg.le, ite_false]
    exact (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (hinv.const_mul_atTop_of_neg hneg)
  · simp only [hpos, ite_true]
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (hinv.const_mul_atTop hpos)

/-- `∫_{[a₁,a₂]} P_ε(x - μ) dx → 1_{[a₁,a₂]}(μ)` for `μ ∉ {a₁, a₂}`. -/
theorem tendsto_setIntegral_cauchyKernel_Icc {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) {μ : ℝ}
    (h₁ : μ ≠ a₁) (h₂ : μ ≠ a₂) :
    Tendsto (fun ε => ∫ x in Set.Icc a₁ a₂, cauchyKernel ε (x - μ)) (𝓝[>] 0)
      (𝓝 ((Set.Icc a₁ a₂).indicator (1 : ℝ → ℝ) μ)) := by
  have heq : (fun ε => ∫ x in Set.Icc a₁ a₂, cauchyKernel ε (x - μ)) =ᶠ[𝓝[>] 0]
      fun ε => Real.pi⁻¹ * (Real.arctan ((a₂ - μ) / ε) - Real.arctan ((a₁ - μ) / ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact setIntegral_cauchyKernel_Icc hε ha μ
  refine Tendsto.congr' heq.symm ?_
  have hc₂ : a₂ - μ ≠ 0 := sub_ne_zero.2 (Ne.symm h₂)
  have hc₁ : a₁ - μ ≠ 0 := sub_ne_zero.2 (Ne.symm h₁)
  have hl := ((tendsto_arctan_div_nhdsGT hc₂).sub (tendsto_arctan_div_nhdsGT hc₁)).const_mul
    Real.pi⁻¹
  convert hl using 2
  have hp := Real.pi_pos.ne'
  by_cases hm : μ ∈ Set.Icc a₁ a₂
  · have hlt₁ : a₁ < μ := lt_of_le_of_ne hm.1 (Ne.symm h₁)
    have hlt₂ : μ < a₂ := lt_of_le_of_ne hm.2 h₂
    rw [Set.indicator_of_mem hm]
    simp only [show 0 < a₂ - μ by linarith, show ¬ (0 < a₁ - μ) by linarith, ite_true, ite_false,
      Pi.one_apply]
    field_simp; ring
  · rw [Set.indicator_of_notMem hm]
    rcases not_and_or.1 hm with hle | hle
    · rw [not_le] at hle
      simp only [show 0 < a₂ - μ by linarith, show 0 < a₁ - μ by linarith, ite_true]
      ring
    · rw [not_le] at hle
      simp only [show ¬ (0 < a₂ - μ) by linarith, show ¬ (0 < a₁ - μ) by linarith, ite_false]
      ring

theorem finite_setOf_det_sub_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) : {x : ℝ | (D - (x : ℂ) • (1 : Matrix ι ι ℂ)).det = 0}.Finite := by
  have hp : D.charpoly ≠ 0 := (charpoly_monic D).ne_zero
  have hsub : {x : ℝ | (D - (x : ℂ) • (1 : Matrix ι ι ℂ)).det = 0} ⊆
      (fun x : ℝ => (x : ℂ)) ⁻¹' {z : ℂ | D.charpoly.IsRoot z} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot, eval_charpoly] at hx ⊢
    have : scalar ι (x : ℂ) - D = -(D - (x : ℂ) • 1) := by
      rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
    rw [this, det_neg, hx, mul_zero]
  exact ((Polynomial.finite_setOfPred_isRoot hp).preimage
    (fun a _ b _ h => Complex.ofReal_injective h)).subset hsub

end BlockBand.Critical.Collar.Density
