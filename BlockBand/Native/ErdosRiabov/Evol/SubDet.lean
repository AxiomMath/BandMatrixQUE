module

public import BlockBand.Native.ErdosRiabov.VS.ResolventItoVS
public import BlockBand.SourceProcess.Stochastic.Bridges.Product

/-!
# Subtracting a deterministic absolutely continuous process

Subtracting a deterministic absolutely continuous process from a continuous semimartingale keeps
the semimartingale property and the bracket and subtracts the density from the drift; applied to
the chains minus their deterministic approximations, stopped at time `1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal Matrix

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [IsProbabilityMeasure Q] in
theorem isStronglyProgressive_deterministic {f : ℝ≥0 → ℝ} (hf : Measurable f) :
    IsStronglyProgressive 𝓖 (fun t (_ : Ω) (_ : Fin 1) => f t) := fun _ =>
  ((measurable_pi_iff.2 fun _ => hf).stronglyMeasurable).comp_measurable
    (measurable_subtype_coe.comp measurable_fst)

/-- The row `[1, -1]` on the joined coordinates `Fin (1 + 1)`. -/
def diffRow : Matrix (Fin 1) (Fin (1 + 1)) ℝ :=
  Matrix.of fun _ l => Sum.elim (fun _ => (1 : ℝ)) (fun _ => -1) (finSumFinEquiv.symm l)

theorem diffRow_mulVec (u v : Fin 1 → ℝ) :
    diffRow *ᵥ concatCoord u v + 0 = fun _ => u 0 - v 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, diffRow, Matrix.of_apply, Pi.add_apply,
    Pi.zero_apply, add_zero]
  rw [← finSumFinEquiv.sum_comp]
  simp [concatCoord, Fintype.sum_sum_type]
  ring

/-- **Subtracting a deterministic absolutely continuous process** keeps the semimartingale
property, subtracts the density from the drift and keeps the bracket. -/
theorem sub_deterministic {Y β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    {g gd : ℝ≥0 → ℝ} (hgd : Measurable gd)
    (hint : ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => gd s.toNNReal) (Ioc 0 t))
    (hg : ∀ t, g t = g 0 + ∫ s in Ioc (0 : ℝ) t, gd s.toNNReal) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω _ => Y t ω 0 - g t) (fun t ω _ => β t ω 0 - gd t)
      α := by
  have hgc : Continuous g := by
    rw [show g = fun (t : ℝ≥0) => g 0 + ∫ s in Ioc (0 : ℝ) t, gd s.toNNReal from funext hg]
    exact continuous_const.add (continuous_setIntegral_Ioc hint)
  have H2 := H.concat_ac (v := fun t (_ : Ω) (_ : Fin 1) => g t)
    (vd := fun t (_ : Ω) (_ : Fin 1) => gd t) (isStronglyProgressive_deterministic hgc.measurable)
    (isStronglyProgressive_deterministic hgd) (ae_of_all _ fun _ t _ => ⟨hint t, hg t⟩)
  have H3 := H2.affine diffRow 0
  have e1 : (fun t ω => diffRow *ᵥ concatCoord (Y t ω) (fun _ : Fin 1 => g t) + 0) =
      fun t ω (_ : Fin 1) => Y t ω 0 - g t := by
    funext t ω
    rw [diffRow_mulVec]
  have e2 : (fun t ω => diffRow *ᵥ concatCoord (β t ω) (fun _ : Fin 1 => gd t)) =
      fun t ω (_ : Fin 1) => β t ω 0 - gd t := by
    funext t ω
    have := diffRow_mulVec (β t ω) (fun _ : Fin 1 => gd t)
    rw [add_zero] at this
    rw [this]
  rw [e1, e2] at H3
  convert H3 using 1
  funext t ω
  refine Matrix.ext fun i j => ?_
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type]
  have h0 : (finSumFinEquiv.symm (0 : Fin (1 + 1)) : Fin 1 ⊕ Fin 1) = Sum.inl 0 := by decide
  have h1 : (finSumFinEquiv.symm (1 : Fin (1 + 1)) : Fin 1 ⊕ Fin 1) = Sum.inr 0 := by decide
  simp [diffRow, concatCov, h0, h1]

end Generic

/-!
### Chains minus a stopped deterministic function
-/

/-- Projection of `ℝ` onto `[0,1]`. -/
def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

theorem clamp01_mem (s : ℝ) : clamp01 s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clamp01_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : clamp01 s = s := by
  unfold clamp01
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01
  fun_prop

/-- The density of `t ↦ F(t ∧ 1)`: `F'(t)` for `t ≤ 1`, `0` afterwards. -/
def frozenDeriv (F' : ℝ → ℝ) (t : ℝ≥0) : ℝ := if (t : ℝ) ≤ 1 then F' (clamp01 t) else 0

theorem frozenDeriv_of_le {F' : ℝ → ℝ} {t : ℝ≥0} (ht : (t : ℝ) ≤ 1) :
    frozenDeriv F' t = F' t := by
  rw [frozenDeriv, ite_eq_left ht]
  show F' (clamp01 (t : ℝ)) = F' t
  rw [clamp01_of_mem ⟨NNReal.coe_nonneg t, ht⟩]

/-- `F(t ∧ 1) = F(0) + ∫_0^t frozenDeriv F'` and the density is Borel and locally integrable. -/
theorem frozen_ftc {F F' : ℝ → ℝ} (hF : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' s) s)
    (hF' : ContinuousOn F' (Icc 0 1)) :
    Measurable (frozenDeriv F') ∧
      (∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => frozenDeriv F' s.toNNReal) (Ioc 0 t)) ∧
      ∀ t : ℝ≥0, F (min (t : ℝ) 1) =
        F (min ((0 : ℝ≥0) : ℝ) 1) + ∫ s in Ioc (0 : ℝ) t, frozenDeriv F' s.toNNReal := by
  have hc : Continuous fun s : ℝ => F' (clamp01 s) :=
    hF'.comp_continuous continuous_clamp01 clamp01_mem
  set h : ℝ → ℝ := (Iic (1 : ℝ)).indicator fun s => F' (clamp01 s) with hh
  have heq : ∀ t : ℝ≥0, EqOn (fun s : ℝ => frozenDeriv F' s.toNNReal) h (Ioc 0 t) := by
    intro t s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1.le
    simp only [frozenDeriv, Real.coe_toNNReal _ hs0, hh, indicator, mem_Iic]
  refine ⟨?_, fun t => ?_, fun t => ?_⟩
  · unfold frozenDeriv
    exact Measurable.ite (measurableSet_le NNReal.continuous_coe.measurable measurable_const)
      (hc.measurable.comp NNReal.continuous_coe.measurable) measurable_const
  · have hi : IntegrableOn (fun s : ℝ => F' (clamp01 s)) (Ioc (0 : ℝ) (t : ℝ)) :=
      hc.integrableOn_Ioc
    exact (hi.indicator measurableSet_Iic).congr_fun (heq t).symm measurableSet_Ioc
  · rw [setIntegral_congr_fun measurableSet_Ioc (heq t), hh,
      setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic]
    have ht1 : (0 : ℝ) ≤ (t : ℝ) ⊓ 1 := le_inf t.2 zero_le_one
    have hcongr : EqOn (fun s => F' (clamp01 s)) F' (Ioc 0 ((t : ℝ) ⊓ 1)) := fun s hs => by
      show F' (clamp01 s) = F' s
      rw [clamp01_of_mem ⟨hs.1.le, hs.2.trans inf_le_right⟩]
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, ← intervalIntegral.integral_of_le ht1]
    have hsub : uIcc (0 : ℝ) ((t : ℝ) ⊓ 1) ⊆ Icc 0 1 := by
      rw [uIcc_of_le ht1]
      exact Icc_subset_Icc le_rfl inf_le_right
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hF s (hsub hs))
      ((hF'.mono hsub).intervalIntegrable)]
    simp only [NNReal.coe_zero, min_eq_left zero_le_one]
    change F (min (t : ℝ) 1) = F 0 + (F (min (t : ℝ) 1) - F 0)
    ring

variable {p : BlockBand.Parameters} {k : ℕ}

open BlockBand.Native.ErdosRiabov.Stochastic BlockBand.Native.ErdosRiabov.VS in

/-- **Chain minus a fixed deterministic function**: `f(t, Y_t - Y_0) - F(t ∧ 1)` is a
continuous semimartingale with drift `chainDrift - frozenDeriv F'` and the chain bracket.
-/
theorem chain_sub_ito (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] {z m : ℂ}
    (hz : 0 < z.im) (hm : 0 < m.im) (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p)
    {F F' : ℝ → ℝ} (hF : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' s) s)
    (hF' : ContinuousOn F' (Icc 0 1)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec z m σ) B K
        ((t : ℝ), vsNoise p t x) - F (min (t : ℝ) 1))
      (fun t x _ => chainDrift 0 (vsPatternSpec z m σ) B K t (vsNoise p t x) -
        frozenDeriv F' t)
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        chainBracket 0 (vsPatternSpec z m σ) B K t (vsNoise p t x)) := by
  obtain ⟨hmeas, hint, hg⟩ := frozen_ftc hF hF'
  exact sub_deterministic (resolventChain_ito_vs μ Matrix.isHermitian_zero hz hm σ B K)
    (g := fun t : ℝ≥0 => F (min (t : ℝ) 1)) hmeas hint hg

end BlockBand.Native.ErdosRiabov.Evol
