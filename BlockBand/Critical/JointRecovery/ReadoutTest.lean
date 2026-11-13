module

public import BlockBand.Internal.Contracts.CriticalEntire
public import BlockBand.Critical.JointRecovery.Extraction
public import BlockBand.Model.Construction.MarkedStateTopology

/-!
# Readout tests on the marked space

`readoutTest q f = f ∘ profileReadout q` on `ℝ × P(𝕋)`, and continuity of the marked integrals
`ξ ↦ ∫ g dξ.marked` on `MarkedPointMeasure`; `markedLaplaceBCF g` is the bounded continuous
Laplace integrand `ξ ↦ exp(-∫ g dξ.marked)` for `g ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set MeasureTheory
open BlockBand.Internal.Contracts.CriticalEntire
open scoped BoundedContinuousFunction

/-- `ν ↦ ∫ φ dν` is continuous on `P(𝕋)` for continuous `φ`. -/
theorem continuous_integral_massProfile (φ : C(Torus, ℝ)) :
    Continuous fun ν : MassProfile => ∫ r, φ r ∂(ν : Measure Torus) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact φ)

theorem continuous_profileReadout {k : ℕ} (q : Fin k → C(Torus, ℝ)) :
    Continuous (profileReadout q) := by
  unfold profileReadout
  refine continuous_fst.prodMk (continuous_pi fun a => ?_)
  exact Complex.continuous_ofReal.comp
    ((continuous_integral_massProfile (fullProfile q a)).comp continuous_snd)

/-- The readout test `f ∘ profileReadout q` on `ℝ × P(𝕋)`. -/
def readoutTest {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) :
    CompactlySupportedContinuousMap MarkedSpectralSpace ℝ where
  toFun z := f (profileReadout q z)
  continuous_toFun := f.continuous.comp (continuous_profileReadout q)
  hasCompactSupport' := by
    obtain ⟨A, -, hA⟩ := exists_abs_fst_bound f
    refine HasCompactSupport.intro' (K := Icc (-A) A ×ˢ univ)
      (isCompact_Icc.prod isCompact_univ) (isClosed_Icc.prod isClosed_univ) ?_
    intro z hz
    by_contra hne
    exact hz ⟨abs_le.mp (hA _ hne), mem_univ _⟩

@[simp] theorem readoutTest_apply {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) (z : MarkedSpectralSpace) :
    readoutTest q f z = f (profileReadout q z) := rfl

/-- Integration of a compactly supported test against the marked measure is continuous on
`MarkedPointMeasure`. -/
theorem continuous_markedIntegral (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) :
    Continuous fun ξ : MarkedPointMeasure => ∫ z, g z ∂ξ.marked.measure := by
  have h1 : Continuous fun ξ : MarkedPointMeasure => ξ.marked := continuous_induced_dom
  have h2 : Continuous fun η : VaguePointMeasure MarkedSpectralSpace => η.coordinate g := by
    have h0 : Continuous fun η : VaguePointMeasure MarkedSpectralSpace =>
        fun f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ => η.coordinate f :=
      continuous_induced_dom
    exact (continuous_apply g).comp h0
  exact h2.comp h1

/-- The marked Laplace integrand `ξ ↦ exp(-∫ g dξ.marked)` as a bounded continuous function,
`g ≥ 0`. -/
def markedLaplaceBCF (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (hg : ∀ z, 0 ≤ g z) : MarkedPointMeasure →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ξ => Real.exp (-∫ z, g z ∂ξ.marked.measure),
      Real.continuous_exp.comp (continuous_markedIntegral g).neg⟩ 2 (by
      intro ξ η
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : 0 ≤ ∫ z, g z ∂ξ.marked.measure := integral_nonneg hg
      have h2 : 0 ≤ ∫ z, g z ∂η.marked.measure := integral_nonneg hg
      have e1 : Real.exp (-∫ z, g z ∂ξ.marked.measure) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have e2 : Real.exp (-∫ z, g z ∂η.marked.measure) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have p1 := Real.exp_pos (-∫ z, g z ∂ξ.marked.measure)
      have p2 := Real.exp_pos (-∫ z, g z ∂η.marked.measure)
      rw [abs_le]; constructor <;> linarith)

@[simp] theorem markedLaplaceBCF_apply (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ)
    (hg : ∀ z, 0 ≤ g z) (ξ : MarkedPointMeasure) :
    markedLaplaceBCF g hg ξ = Real.exp (-∫ z, g z ∂ξ.marked.measure) := rfl

theorem readoutTest_nonneg {k : ℕ} (q : Fin k → C(Torus, ℝ))
    {f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∀ z, 0 ≤ readoutTest q f z := fun _ => hf _

theorem readoutLaplace_eq_integral {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (law : ProbabilityMeasure MarkedPointMeasure)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z) :
    readoutLaplace q law f =
      ∫ ξ, markedLaplaceBCF (readoutTest q f) (readoutTest_nonneg q hf) ξ ∂(law : Measure MarkedPointMeasure) :=
  rfl

end BlockBand.Critical.JointRecovery
