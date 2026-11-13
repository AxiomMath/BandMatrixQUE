module

public import BlockBand.Internal.Contracts.WindowAngular
public import BlockBand.Model.Construction.PhysicalCanonicalLaw
public import BlockBand.Model.Construction.MarkedStateTopology
public import BlockBand.Model.Construction.SpectralMarkSingleton

/-!
# Marked mark-functionals: finite identity and Fatou under weak convergence

For a continuous compactly supported `f ≥ 0` on `ℝ × P(𝕋)` (the mark space `P(𝕋)` is compact),
`ξ ↦ ∫ f dξ.marked` is a vague coordinate, hence continuous on the marked state.

* `lintegral_ofReal_marked`: `∫⁻ ofReal f dξ = ofReal (∫ f dξ)` for every marked point measure.
* `lintegral_le_liminf_of_tendsto`: Fatou for nonnegative continuous functionals along weakly
  converging probability laws on any topological space with measurable opens (truncation and
  monotone convergence; no metrizability).
* `lintegral_markedLaw_eq`: the exact finite identity
  `E_{R.markedLaw E} ∫⁻ ofReal f dξ = E Σ_α ofReal f(Nρ(E)(λ_α-E), ν_α)` under the physical law
  of every realization, with the raw ordered eigenvalues and profiles.
* `markedLimit_lintegral_le`: if the finite expectations along a critical subsequence are
  eventually bounded by `c + r_j` with `r_j → 0`, the limit expectation is at most `c`.

Dependencies: the marked law (`FiniteRealization.markedLaw`), the adopted identification
`finiteRealization_markedLaw_eq_canonical`, `physicalOrderedMarkedConfig_ae`, and the adopted
mark-space facts `massProfile_opensMeasurableSpace`, `massProfile_measurableSingletonClass`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal NNReal

attribute [local instance] massProfile_opensMeasurableSpace
attribute [local instance] massProfile_measurableSingletonClass

/-- A continuous compactly supported real test on the marked space, as a vague test. -/
def markedTest (f : MarkedSpectralSpace → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f) :
    CompactlySupportedContinuousMap MarkedSpectralSpace ℝ :=
  ⟨⟨f, hf⟩, hfs⟩

/-- `ξ ↦ ∫ f dξ.marked` is continuous on the marked state (vague coordinate). -/
theorem continuous_markedIntegral {f : MarkedSpectralSpace → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) :
    Continuous (fun ξ : MarkedPointMeasure => ∫ x, f x ∂ξ.marked.measure) := by
  have h0 : Continuous (fun ξ : VaguePointMeasure MarkedSpectralSpace =>
      fun g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ => ξ.coordinate g) :=
    continuous_induced_dom
  have h1 : Continuous (fun ξ : VaguePointMeasure MarkedSpectralSpace =>
      ξ.coordinate (markedTest f hf hfs)) :=
    (continuous_apply (markedTest f hf hfs)).comp h0
  have h2 : Continuous (fun ξ : MarkedPointMeasure => ξ.marked) := continuous_induced_dom
  exact h1.comp h2

/-- Compactly supported continuous tests are integrable for every marked point measure. -/
theorem integrable_marked (ξ : MarkedPointMeasure) {f : MarkedSpectralSpace → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) : Integrable f ξ.marked.measure :=
  hf.integrable_of_hasCompactSupport hfs

/-- Lower and Bochner integrals of a nonnegative compactly supported continuous test agree. -/
theorem lintegral_ofReal_marked (ξ : MarkedPointMeasure) {f : MarkedSpectralSpace → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (h0 : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ξ.marked.measure =
      ENNReal.ofReal (∫ x, f x ∂ξ.marked.measure) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_marked ξ hf hfs)
    (Eventually.of_forall h0)).symm

/-- The marked mark-functional `ξ ↦ ∫⁻ ofReal f dξ.marked` is Borel measurable. -/
theorem measurable_markedLIntegral {f : MarkedSpectralSpace → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (h0 : ∀ x, 0 ≤ f x) :
    Measurable (fun ξ : MarkedPointMeasure =>
      ∫⁻ x, ENNReal.ofReal (f x) ∂ξ.marked.measure) := by
  have he : (fun ξ : MarkedPointMeasure => ∫⁻ x, ENNReal.ofReal (f x) ∂ξ.marked.measure) =
      fun ξ => ENNReal.ofReal (∫ x, f x ∂ξ.marked.measure) := by
    funext ξ; exact lintegral_ofReal_marked ξ hf hfs h0
  rw [he]
  exact ENNReal.measurable_ofReal.comp (continuous_markedIntegral hf hfs).measurable

/-- Truncation of a real continuous function as a bounded continuous `ℝ≥0` function. -/
def truncNN {Ω : Type*} [TopologicalSpace Ω] (g : Ω → ℝ) (hg : Continuous g) (K : ℕ) :
    BoundedContinuousFunction Ω ℝ≥0 :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ω => min (Real.toNNReal (g ω)) (K : ℝ≥0),
      (continuous_real_toNNReal.comp hg).min continuous_const⟩ (K : ℝ)
    (by
      intro x y
      change dist (min (Real.toNNReal (g x)) (K : ℝ≥0)) (min (Real.toNNReal (g y)) (K : ℝ≥0))
        ≤ (K : ℝ)
      rw [NNReal.dist_eq]
      have hx0 : (0 : ℝ) ≤ ((min (Real.toNNReal (g x)) (K : ℝ≥0) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      have hy0 : (0 : ℝ) ≤ ((min (Real.toNNReal (g y)) (K : ℝ≥0) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      have hx1 : ((min (Real.toNNReal (g x)) (K : ℝ≥0) : ℝ≥0) : ℝ) ≤ K := by
        exact_mod_cast min_le_right _ _
      have hy1 : ((min (Real.toNNReal (g y)) (K : ℝ≥0) : ℝ≥0) : ℝ) ≤ K := by
        exact_mod_cast min_le_right _ _
      rw [abs_le]; constructor <;> linarith)

theorem truncNN_apply {Ω : Type*} [TopologicalSpace Ω] (g : Ω → ℝ) (hg : Continuous g)
    (K : ℕ) (ω : Ω) : truncNN g hg K ω = min (Real.toNNReal (g ω)) (K : ℝ≥0) := rfl

/-- **Fatou under weak convergence.** For a continuous real `g`, the lower integral of
`ofReal ∘ g` under a weak limit is at most the `liminf` of the lower integrals. Any
topological space with measurable opens; no metrizability or tightness is used. -/
theorem lintegral_le_liminf_of_tendsto {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {P : ProbabilityMeasure Ω} {Ps : ℕ → ProbabilityMeasure Ω}
    (h : Tendsto Ps atTop (𝓝 P)) {g : Ω → ℝ} (hg : Continuous g) :
    ∫⁻ ω, ENNReal.ofReal (g ω) ∂(P : Measure Ω) ≤
      liminf (fun j => ∫⁻ ω, ENNReal.ofReal (g ω) ∂(Ps j : Measure Ω)) atTop := by
  have hsup : ∀ ω, ENNReal.ofReal (g ω) = ⨆ K : ℕ, ((truncNN g hg K ω : ℝ≥0) : ℝ≥0∞) := by
    intro ω
    calc ENNReal.ofReal (g ω) = (((g ω).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
      _ = (((g ω).toNNReal : ℝ≥0) : ℝ≥0∞) ⊓ ⨆ K : ℕ, (K : ℝ≥0∞) := by
        rw [ENNReal.iSup_natCast, inf_top_eq]
      _ = ⨆ K : ℕ, (((g ω).toNNReal : ℝ≥0) : ℝ≥0∞) ⊓ (K : ℝ≥0∞) := inf_iSup_eq _ _
      _ = _ := by
        congr 1
  have hmono : Monotone (fun K : ℕ => fun ω => ((truncNN g hg K ω : ℝ≥0) : ℝ≥0∞)) := by
    intro K L hKL ω
    simp only [truncNN_apply]
    exact ENNReal.coe_le_coe.mpr (min_le_min le_rfl (by exact_mod_cast hKL))
  have hmeas : ∀ K : ℕ, Measurable (fun ω => ((truncNN g hg K ω : ℝ≥0) : ℝ≥0∞)) :=
    fun K => ENNReal.continuous_coe.measurable.comp (truncNN g hg K).continuous.measurable
  simp_rw [hsup]
  rw [lintegral_iSup hmeas hmono]
  refine iSup_le fun K => ?_
  have ht := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp h) (truncNN g hg K)
  rw [← ht.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun j => lintegral_mono fun ω => ?_)
    (by isBoundedDefault) (by isBoundedDefault)
  exact le_iSup (fun K : ℕ => ((truncNN g hg K ω : ℝ≥0) : ℝ≥0∞)) K

variable {p : Parameters}

/-- **Finite identity.** Under the marked law of every realization, the expectation of a
nonnegative compactly supported continuous mark-functional is the physical expectation of the
finite sum over all ranks, with raw ordered eigenvalues `λ_α`, unfolding `N ρ(E)(λ_α - E)` and
the ordered profiles. -/
theorem lintegral_markedLaw_eq (R : FiniteRealization p) (E : ℝ) {f : MarkedSpectralSpace → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (h0 : ∀ x, 0 ≤ f x) :
    ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (f x) ∂ξ.marked.measure ∂(R.markedLaw E : Measure MarkedPointMeasure) =
      ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal
          (f ((p.N : ℝ) * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E),
            physicalOrderedProfile p H α))
        ∂(R.model.law : Measure p.SiteMatrix) := by
  rw [finiteRealization_markedLaw_eq_canonical]
  unfold Parameters.GaussianRingModel.canonicalPhysicalMarkedLaw
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map (measurable_markedLIntegral hf hfs h0)
    (measurable_physicalOrderedMarkedConfig p E)]
  apply lintegral_congr_ae
  filter_upwards [physicalOrderedMarkedConfig_ae p R.model E] with H hH
  rw [hH, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro α _
  exact lintegral_dirac _ _

/-- **Passage to a critical marked limit.** Let `P` be a weak limit along a strictly increasing
subsequence `φ` of the marked laws of a critical sequence. If the finite physical expectations
of `Σ_α f(u_α, ν_α)` are eventually at most `c + r_j` with `r_j → 0`, then
`E_P ∫⁻ ofReal f dξ.marked ≤ ofReal c`. -/
theorem markedLimit_lintegral_le {τ b E : ℝ} {hb : 0 < b} {hb' : b < 1 / 2}
    (s : CriticalSequence τ) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
    (φ : ℕ → ℕ) (P : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j => (R (φ j)).markedLaw E) atTop (𝓝 P))
    {f : MarkedSpectralSpace → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (h0 : ∀ x, 0 ≤ f x) (c : ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ᶠ j in atTop,
      ∫⁻ H, ∑ α : Fin (s.parameters b hb hb' (φ j)).N, ENNReal.ofReal
          (f (((s.parameters b hb hb' (φ j)).N : ℝ) * Parameters.semicircleDensity E *
              (physicalOrderedEigenvalue (s.parameters b hb hb' (φ j)) H α - E),
            physicalOrderedProfile (s.parameters b hb hb' (φ j)) H α))
        ∂((R (φ j)).model.law : Measure _) ≤ ENNReal.ofReal (c + r j)) :
    ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (f x) ∂ξ.marked.measure ∂(P : Measure MarkedPointMeasure) ≤
      ENNReal.ofReal c := by
  have hfun : (fun ξ : MarkedPointMeasure => ∫⁻ x, ENNReal.ofReal (f x) ∂ξ.marked.measure) =
      fun ξ => ENNReal.ofReal (∫ x, f x ∂ξ.marked.measure) := by
    funext ξ; exact lintegral_ofReal_marked ξ hf hfs h0
  have hF := lintegral_le_liminf_of_tendsto hlim (continuous_markedIntegral hf hfs)
  rw [hfun]
  refine hF.trans ?_
  have hlimr : Tendsto (fun j => ENNReal.ofReal (c + r j)) atTop (𝓝 (ENNReal.ofReal c)) := by
    have := (ENNReal.continuous_ofReal.tendsto (c + 0)).comp (tendsto_const_nhds.add hr)
    simpa [Function.comp_def] using this
  rw [← hlimr.liminf_eq]
  refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [hbound] with j hj
  refine le_trans (le_of_eq ?_) hj
  rw [← hfun]
  exact lintegral_markedLaw_eq (R (φ j)) E hf hfs h0

end BlockBand.Window.SmallCritical
