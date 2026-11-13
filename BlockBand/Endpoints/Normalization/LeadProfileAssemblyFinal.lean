module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyInterfaces
public import BlockBand.Layers.GinibreTails
public import BlockBand.Layers.RingDecomposition
public import BlockBand.Counting.DiagonalGaussianWick
public import BlockBand.Coarea.GUELaw

/-!
# The physical lead-profile theorem: the assembly

**Main result.**
`physicalLeadProfile_of_steps (hPalm : OneBlockPalmContract) (hNorm : OneBlockNormalizerContract)
(hLGS : LeadGaussianStep) (hLCP : LeadCommonPortStep) (hAR : LeadAngularRegularity)
(hLM : LeadSideMeasurability) : PhysicalLeadProfileContract`.

Inputs:
  - `LeadAngularRegularity`: joint measurability of `(e, ω) ↦ leadAngularAverage`, the bound
    `|leadAngularAverage| ≤ ‖Φ‖`, and the a.s. representation
    `Σ_ℓ 𝒜⁰_ℓ[Ψ] = Z₀ · leadAngularAverage` (i.e. `Σ_ℓ 𝒜⁰_ℓ[Ψ] = 0` where `Z₀ = 0`) under every
    one-block splitting law;
  - `LeadSideMeasurability`: measurability in the energy of `leadLeadSide` and
    `gaussianLeadSide`.

**Proof.** For a window `w` (`IsWindow`): the window comparison
(`physicalOneMark_window_comparison`, error `(‖Φ‖+1)ε₁`), then `LeadGaussianStep`, then `LeadCommonPortStep` on the support of `w`, where
`e(u) = E + u/(Nρ(E)) ∈ bulkInterval ((2-|E|)/2)` once `N ≥ W` is large, and
`τ/2 ≤ n/W ≤ τ + 1` eventually. A nonnegative continuous compactly supported `w` is `c · window`
(`c = ∫ w`; `w = 0` if `c = 0`), and both one-mark sides are homogeneous. A general `w` is
`w⁺ - w⁻`; both sides are additive (bounded measurable integrands).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped BoundedContinuousFunction

/-!
## The two regularity interfaces
-/

/-- Step 2a regularity of the concrete angular average. -/
def LeadAngularRegularity : Prop :=
  ∀ (p : Parameters)
    (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ),
    IsBlockFrame p 0 U → ∀ Φ : MassProfile →ᵇ ℝ,
      Measurable (Function.uncurry fun e ω => leadAngularAverage p U Φ ω e) ∧
      (∀ e ω, |leadAngularAverage p U Φ ω e| ≤ ‖Φ‖) ∧
      ∀ (model : p.GaussianRingModel) (Pω : Measure (BlockState p 0)),
        IsBlockSplitting p 0 model Pω → ∀ᵐ ω ∂Pω, ∀ e,
          ∑ ℓ ∈ Finset.range p.W,
              blockSectorFiberReal p 0 U ω e ℓ (leadReconObservable p Φ 0 ω e) =
            (blockNormalizer p 0 U ω e).toReal * leadAngularAverage p U Φ ω e

/-- Measurability in the energy of the two lead sides. -/
def LeadSideMeasurability : Prop :=
  ∀ (p : Parameters) (Φ : MassProfile →ᵇ ℝ),
    Measurable (leadLeadSide p Φ) ∧ Measurable (gaussianLeadSide p Φ)

/-!
## Bounds
-/

theorem abs_integral_avg_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (Φ : MassProfile →ᵇ ℝ) (f : X → ℕ → MassProfile) :
    |∫ x, (n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, Φ (f x J) ∂μ| ≤ ‖Φ‖ := by
  have hb : ∀ x, ‖(n : ℝ)⁻¹ * ∑ J ∈ Finset.range n, Φ (f x J)‖ ≤ ‖Φ‖ := by
    intro x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hn')]
    calc (n : ℝ)⁻¹ * |∑ J ∈ Finset.range n, Φ (f x J)|
        ≤ (n : ℝ)⁻¹ * ∑ _J ∈ Finset.range n, ‖Φ‖ := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J _ => ?_)
          rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
      _ = ‖Φ‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hn'.ne', one_mul]
  have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
  simpa [Real.norm_eq_abs] using this

theorem abs_leadLeadSide_le (p : Parameters) (Φ : MassProfile →ᵇ ℝ) (e : ℝ) :
    |leadLeadSide p Φ e| ≤ ‖Φ‖ := by
  have : IsProbabilityMeasure (growthPathLaw p.W p.b) := by unfold growthPathLaw; infer_instance
  exact abs_integral_avg_le _ p.n Φ _

theorem abs_gaussianLeadSide_le (p : Parameters) (Φ : MassProfile →ᵇ ℝ) (e : ℝ) :
    |gaussianLeadSide p Φ e| ≤ ‖Φ‖ := by
  have : IsProbabilityMeasure (growthPathLaw p.W p.b) := by unfold growthPathLaw; infer_instance
  have : IsProbabilityMeasure (leadGaussianLaw p) := by unfold leadGaussianLaw; infer_instance
  exact abs_integral_avg_le _ p.n Φ _

theorem measurable_microEnergy (p : Parameters) (E : ℝ) : Measurable (microEnergy p E) := by
  unfold microEnergy
  exact measurable_const.add (measurable_id.div_const _)

/-- `u ↦ w(u) S(e(u))` is integrable for an integrable `w` and a bounded measurable side. -/
theorem integrable_weight_mul_side (p : Parameters) (E : ℝ) {w : ℝ → ℝ}
    (hw : Integrable w volume) {S : ℝ → ℝ} (hS : Measurable S) (C : ℝ) (hC : ∀ e, |S e| ≤ C) :
    Integrable (fun u => w u * S (microEnergy p E u)) volume := by
  have := hw.bdd_mul (f := fun u => S (microEnergy p E u)) (c := C)
    (hS.comp (measurable_microEnergy p E)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hC _)
  simpa only [mul_comm] using this

/-!
## Linearity of the two one-mark sides
-/

section Linear

variable {p : Parameters}

theorem physicalOneMark_const_mul (R : FiniteRealization p) (E c : ℝ) (w : ℝ → ℝ)
    (Φ : MassProfile →ᵇ ℝ) :
    physicalOneMark R E (fun x => c * w x) Φ = c * physicalOneMark R E w Φ := by
  unfold physicalOneMark
  rw [← integral_const_mul]
  congr 1; funext H
  rw [← integral_const_mul]
  congr 1; funext x
  ring

theorem leadOneMark_const_mul (E c : ℝ) (w : ℝ → ℝ) (Φ : MassProfile →ᵇ ℝ) :
    leadOneMark p E (fun x => c * w x) Φ = c * leadOneMark p E w Φ := by
  rw [leadOneMark_eq, leadOneMark_eq, ← integral_const_mul]
  congr 1; funext u
  ring

theorem physicalOneMark_zero (R : FiniteRealization p) (E : ℝ) (Φ : MassProfile →ᵇ ℝ) :
    physicalOneMark R E (fun _ => 0) Φ = 0 := by
  simp [physicalOneMark]

theorem leadOneMark_zero (E : ℝ) (Φ : MassProfile →ᵇ ℝ) :
    leadOneMark p E (fun _ => 0) Φ = 0 := by
  simp [leadOneMark]

theorem integrable_canonical_oneMark (R : FiniteRealization p) (E : ℝ) {w : ℝ → ℝ}
    (hw : Measurable w) (M : ℝ) (hM : ∀ x, |w x| ≤ M) (Φ : MassProfile →ᵇ ℝ) :
    Integrable (fun H => ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
        Φ (physicalOrderedProfile p H α)) (R.model.law : Measure p.SiteMatrix) := by
  refine integrable_finsetSum _ fun α _ => ?_
  have hm : Measurable (fun H => w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      Φ (physicalOrderedProfile p H α)) :=
    (hw.comp ((measurable_microCoord (p := p) E).comp
      (measurable_physicalOrderedEigenvalue p α))).mul
      ((measurable_massProfile_bcf Φ).comp (measurable_physicalOrderedProfile p α))
  refine (integrable_const (M * ‖Φ‖)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun H => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hM _) (by rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _)
    (abs_nonneg _) ((abs_nonneg _).trans (hM 0))

theorem physicalOneMark_sub (R : FiniteRealization p) (E : ℝ) {w₁ w₂ : ℝ → ℝ}
    (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (M : ℝ) (hM₁ : ∀ x, |w₁ x| ≤ M)
    (hM₂ : ∀ x, |w₂ x| ≤ M) (Φ : MassProfile →ᵇ ℝ) :
    physicalOneMark R E (fun x => w₁ x - w₂ x) Φ =
      physicalOneMark R E w₁ Φ - physicalOneMark R E w₂ Φ := by
  have hM' : ∀ x, |w₁ x - w₂ x| ≤ M + M := fun x =>
    (abs_sub _ _).trans (add_le_add (hM₁ x) (hM₂ x))
  rw [physicalOneMark_eq_canonical R E (fun x => w₁ x - w₂ x) (hw₁.sub hw₂) Φ,
    physicalOneMark_eq_canonical R E _ hw₁ Φ, physicalOneMark_eq_canonical R E _ hw₂ Φ,
    ← integral_sub (integrable_canonical_oneMark R E hw₁ M hM₁ Φ)
      (integrable_canonical_oneMark R E hw₂ M hM₂ Φ)]
  congr 1; funext H
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

theorem leadOneMark_sub (hLM : LeadSideMeasurability) (E : ℝ) {w₁ w₂ : ℝ → ℝ}
    (hw₁ : Integrable w₁ volume) (hw₂ : Integrable w₂ volume) (Φ : MassProfile →ᵇ ℝ) :
    leadOneMark p E (fun x => w₁ x - w₂ x) Φ = leadOneMark p E w₁ Φ - leadOneMark p E w₂ Φ := by
  rw [leadOneMark_eq, leadOneMark_eq, leadOneMark_eq, ← integral_sub
    (integrable_weight_mul_side p E hw₁ (hLM p Φ).1 _ (abs_leadLeadSide_le p Φ))
    (integrable_weight_mul_side p E hw₂ (hLM p Φ).1 _ (abs_leadLeadSide_le p Φ))]
  congr 1; funext u
  ring

end Linear

/-!
## The window case
-/

theorem bulk_of_near {E κ e : ℝ} (hκ : κ = (2 - |E|) / 2) (h : |e - E| ≤ κ) :
    e ∈ bulkInterval κ := by
  have := abs_le.mp h
  have hE := abs_le.mp (le_refl |E|)
  constructor <;> cases abs_cases E <;> linarith

/-- **The window case.** -/
theorem physicalLeadProfile_window (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hLGS : LeadGaussianStep) (hLCP : LeadCommonPortStep)
    (hAR : LeadAngularRegularity) (hLM : LeadSideMeasurability)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ) (h1 : -2 < E) (h2 : E < 2)
    (w : ℝ → ℝ) (hw : IsWindow w) (Φ : MassProfile →ᵇ ℝ) (τ : ℝ) (hτ : 0 < τ)
    (s : CriticalSequence τ) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    Tendsto (fun j => physicalOneMark (R j) E w Φ - leadOneMark (s.parameters b hb hb' j) E w Φ)
      atTop (𝓝 0) := by
  -- splitting laws and frames
  choose Pω hPω using fun j => hPalm.splitting_exists (s.parameters b hb hb' j) (R j).model 0
  choose U hU using fun j => hPalm.frame_exists (s.parameters b hb hb' j) 0
  have hD := hLGS b hb hb' E h1 h2 w hw Φ τ hτ s R Pω hPω U hU
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := ‖Φ‖ + 1 with hMdef
  have hM : 0 < M := by positivity
  set ε' : ℝ := ε / 4 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨W₀, hW₀⟩ := physicalOneMark_window_comparison hPalm hNorm b hb hb' E h1 h2 (τ + 1) w
    hw Φ M hM (ε' / M) (by positivity)
  set κ : ℝ := (2 - |E|) / 2 with hκ
  have hκ0 : 0 < κ := by
    have : |E| < 2 := abs_lt.mpr ⟨h1, h2⟩
    rw [hκ]; linarith
  obtain ⟨W₁, hW₁⟩ := hLCP b hb hb' κ (τ / 2) (τ + 1) hκ0 (by positivity) Φ ε' hε'0
  obtain ⟨Mw, Rw, -, -, hRw⟩ := exists_bound_support_of_compact hw.1 hw.2.1
  have hρ := semicircleDensity_pos h1 h2
  -- eventual conditions
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hD ε' hε'0
  have hratio := s.ratio_tendsto
  have hev1 : ∀ᶠ j in atTop, τ / 2 < (s.n j : ℝ) / s.W j ∧ (s.n j : ℝ) / s.W j < τ + 1 :=
    (hratio.eventually (Ioo_mem_nhds (by linarith) (by linarith))).mono fun j hj => hj
  have hev2 : ∀ᶠ j in atTop,
      max (max W₀ W₁) (⌈|Rw| / (κ * Parameters.semicircleDensity E)⌉₊) ≤ s.W j :=
    s.width_tendsto.eventually_ge_atTop _
  obtain ⟨N₂, hN₂⟩ := (hev1.and hev2).exists_forall_of_atTop
  refine ⟨max N₁ N₂, fun j hj => ?_⟩
  obtain ⟨⟨hr1, hr2⟩, hWj⟩ := hN₂ j (le_of_max_le_right hj)
  have hWpos : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hW0 : W₀ ≤ (s.parameters b hb hb' j).W := (le_max_left _ _).trans ((le_max_left _ _).trans hWj)
  have hW1 : W₁ ≤ (s.parameters b hb hb' j).W := (le_max_right _ _).trans ((le_max_left _ _).trans hWj)
  have hnT : ((s.parameters b hb hb' j).n : ℝ) ≤ (τ + 1) * (s.parameters b hb hb' j).W := by
    have := (div_lt_iff₀ hWpos).mp hr2
    exact this.le
  have hnτ : τ / 2 * (s.parameters b hb hb' j).W ≤ ((s.parameters b hb hb' j).n : ℝ) := ((lt_div_iff₀ hWpos).mp hr1).le
  -- (1) the window comparison
  obtain ⟨hAm, hAb, hArep⟩ := hAR (s.parameters b hb hb' j) (U j) (hU j) Φ
  have e1 := hW₀ (s.parameters b hb hb' j) rfl hW0 hnT (R j) (Pω j) (hPω j) (U j) (hU j)
    (fun e ω => leadAngularAverage (s.parameters b hb hb' j) (U j) Φ ω e) hAm
    (fun e ω => (hAb e ω).trans (by rw [hMdef]; linarith)) (hArep (R j).model (Pω j) (hPω j))
  rw [mul_div_cancel₀ _ hM.ne'] at e1
  -- (2) the Gaussian step
  have e2 := hN₁ j (le_of_max_le_left hj)
  rw [Real.dist_eq, sub_zero] at e2
  -- (3) the common-port step on the support of `w`
  have hG := (hLM (s.parameters b hb hb' j) Φ).2
  have hL := (hLM (s.parameters b hb hb' j) Φ).1
  have hwint : Integrable w volume := hw.1.integrable_of_hasCompactSupport hw.2.1
  have e3 : |(∫ u, w u * gaussianLeadSide (s.parameters b hb hb' j) Φ (microEnergy (s.parameters b hb hb' j) E u)) -
      leadOneMark (s.parameters b hb hb' j) E w Φ| ≤ ε' := by
    rw [leadOneMark_eq, ← integral_sub
      (integrable_weight_mul_side (s.parameters b hb hb' j) E hwint hG _ (abs_gaussianLeadSide_le (s.parameters b hb hb' j) Φ))
      (integrable_weight_mul_side (s.parameters b hb hb' j) E hwint hL _ (abs_leadLeadSide_le (s.parameters b hb hb' j) Φ))]
    have hpt : ∀ u, ‖w u * gaussianLeadSide (s.parameters b hb hb' j) Φ (microEnergy (s.parameters b hb hb' j) E u) -
        w u * leadLeadSide (s.parameters b hb hb' j) Φ (microEnergy (s.parameters b hb hb' j) E u)‖ ≤ ε' * w u := by
      intro u
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.2.2.1 u), mul_comm]
      by_cases hu : Rw < |u|
      · rw [hRw u hu]; simp
      · push Not at hu
        refine mul_le_mul_of_nonneg_right ?_ (hw.2.2.1 u)
        apply hW₁ (s.parameters b hb hb' j) rfl hW1 hnτ hnT
        apply bulk_of_near hκ
        have hN : ((s.parameters b hb hb' j).W : ℝ) ≤ (s.parameters b hb hb' j).N := by
          change ((s.W j : ℕ) : ℝ) ≤ ((s.n j * s.W j : ℕ) : ℝ)
          have : 1 ≤ s.n j := by have := s.n_ge_four j; omega
          exact_mod_cast Nat.le_mul_of_pos_left _ this
        have hNpos : (0 : ℝ) < (s.parameters b hb hb' j).N := lt_of_lt_of_le hWpos hN
        have hceil : |Rw| / (κ * Parameters.semicircleDensity E) ≤ (s.parameters b hb hb' j).W := by
          have := Nat.le_ceil (|Rw| / (κ * Parameters.semicircleDensity E))
          have h' : ((⌈|Rw| / (κ * Parameters.semicircleDensity E)⌉₊ : ℕ) : ℝ) ≤ s.W j := by
            exact_mod_cast (le_max_right _ _).trans hWj
          change _ ≤ ((s.W j : ℕ) : ℝ)
          linarith
        unfold microEnergy
        rw [add_sub_cancel_left, abs_div, abs_of_pos (mul_pos hNpos hρ)]
        rw [div_le_iff₀ (mul_pos hNpos hρ)]
        have hk : |Rw| ≤ κ * Parameters.semicircleDensity E * (s.parameters b hb hb' j).W := by
          rw [div_le_iff₀ (mul_pos hκ0 hρ)] at hceil; linarith
        calc |u| ≤ |Rw| := hu.trans (le_abs_self _)
          _ ≤ κ * Parameters.semicircleDensity E * (s.parameters b hb hb' j).W := hk
          _ ≤ κ * ((s.parameters b hb hb' j).N * Parameters.semicircleDensity E) := by
              have := mul_le_mul_of_nonneg_left hN (mul_pos hκ0 hρ).le
              nlinarith
    have := norm_integral_le_of_norm_le (g := fun u => ε' * w u) (hwint.const_mul ε')
      (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul, hw.2.2.2, mul_one, Real.norm_eq_abs] at this
    exact this
  rw [Real.dist_eq, sub_zero]
  have : |physicalOneMark (R j) E w Φ - leadOneMark (s.parameters b hb hb' j) E w Φ| ≤ ε' + ε' + ε' := by
    have := abs_sub_le (physicalOneMark (R j) E w Φ)
      (∫ x, leadAngularAverage (s.parameters b hb hb' j) (U j) Φ x.2 (microEnergy (s.parameters b hb hb' j) E x.1)
        ∂priorWindowMeasure (Pω j) w) (leadOneMark (s.parameters b hb hb' j) E w Φ)
    have := abs_sub_le (∫ x, leadAngularAverage (s.parameters b hb hb' j) (U j) Φ x.2 (microEnergy (s.parameters b hb hb' j) E x.1)
        ∂priorWindowMeasure (Pω j) w)
      (∫ u, w u * gaussianLeadSide (s.parameters b hb hb' j) Φ (microEnergy (s.parameters b hb hb' j) E u)) (leadOneMark (s.parameters b hb hb' j) E w Φ)
    linarith
  linarith

/-!
## Nonnegative and signed weights
-/

theorem physicalLeadProfile_nonneg (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hLGS : LeadGaussianStep) (hLCP : LeadCommonPortStep)
    (hAR : LeadAngularRegularity) (hLM : LeadSideMeasurability)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ) (h1 : -2 < E) (h2 : E < 2)
    (w : ℝ → ℝ) (hc : Continuous w) (hs : HasCompactSupport w) (h0 : ∀ x, 0 ≤ w x)
    (Φ : MassProfile →ᵇ ℝ) (τ : ℝ) (hτ : 0 < τ)
    (s : CriticalSequence τ) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    Tendsto (fun j => physicalOneMark (R j) E w Φ - leadOneMark (s.parameters b hb hb' j) E w Φ)
      atTop (𝓝 0) := by
  have hint : Integrable w volume := hc.integrable_of_hasCompactSupport hs
  set c := ∫ x, w x with hcdef
  by_cases hc0 : c = 0
  · have hae : w =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg h0 hint).mp hc0
    have hw0 : w = fun _ => 0 := (hc.ae_eq_iff_eq volume continuous_const).mp hae
    subst hw0
    simp only [physicalOneMark_zero, leadOneMark_zero, sub_zero]
    exact tendsto_const_nhds
  have hcpos : 0 < c := lt_of_le_of_ne (integral_nonneg h0) (Ne.symm hc0)
  have hwin : IsWindow (fun x => w x / c) := by
    refine ⟨hc.div_const c, hs.mono fun x hx => ?_, fun x => div_nonneg (h0 x) hcpos.le, ?_⟩
    · simp only [Function.mem_support] at hx ⊢; intro h; apply hx; simp [h]
    rw [integral_div, ← hcdef, div_self hc0]
  have hwc : w = fun x => c * (w x / c) := by funext x; field_simp
  have := (physicalLeadProfile_window hPalm hNorm hLGS hLCP hAR hLM b hb hb' E h1 h2 _ hwin Φ τ
    hτ s R).const_mul c
  rw [mul_zero] at this
  rw [hwc]
  refine this.congr fun j => ?_
  rw [physicalOneMark_const_mul, leadOneMark_const_mul, mul_sub]

/-- **The physical lead-profile theorem** (`PhysicalLeadProfileContract`), from
`OneBlockPalmContract`, `OneBlockNormalizerContract`, `LeadGaussianStep`, `LeadCommonPortStep`,
`LeadAngularRegularity` and `LeadSideMeasurability`. -/
theorem physicalLeadProfile_of_steps (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (hLGS : LeadGaussianStep) (hLCP : LeadCommonPortStep)
    (hAR : LeadAngularRegularity) (hLM : LeadSideMeasurability) :
    PhysicalLeadProfileContract := by
  intro b hb hb' E h1 h2 w hsmooth hs Φ τ hτ s R
  have hc : Continuous w := hsmooth.continuous
  set wp : ℝ → ℝ := fun x => max (w x) 0
  set wm : ℝ → ℝ := fun x => max (-w x) 0
  have hcp : Continuous wp := hc.max continuous_const
  have hcm : Continuous wm := hc.neg.max continuous_const
  have hsp : HasCompactSupport wp := hs.mono fun x hx => by
    simp only [wp, Function.mem_support] at hx ⊢; intro h; apply hx; simp [h]
  have hsm : HasCompactSupport wm := hs.mono fun x hx => by
    simp only [wm, Function.mem_support] at hx ⊢; intro h; apply hx; simp [h]
  have hpm : w = fun x => wp x - wm x := by
    funext x; simp only [wp, wm]
    rcases le_total 0 (w x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  obtain ⟨Mp, -, -, hMp, -⟩ := exists_bound_support_of_compact hcp hsp
  obtain ⟨Mm, -, -, hMm, -⟩ := exists_bound_support_of_compact hcm hsm
  have tp := physicalLeadProfile_nonneg hPalm hNorm hLGS hLCP hAR hLM b hb hb' E h1 h2 wp hcp hsp
    (fun x => le_max_right _ _) Φ τ hτ s R
  have tm := physicalLeadProfile_nonneg hPalm hNorm hLGS hLCP hAR hLM b hb hb' E h1 h2 wm hcm hsm
    (fun x => le_max_right _ _) Φ τ hτ s R
  have := tp.sub tm
  rw [sub_zero] at this
  rw [hpm]
  refine this.congr fun j => ?_
  have hMp' : ∀ x, |wp x| ≤ max Mp Mm := fun x => (hMp x).trans (le_max_left _ _)
  have hMm' : ∀ x, |wm x| ≤ max Mp Mm := fun x => (hMm x).trans (le_max_right _ _)
  rw [physicalOneMark_sub (R j) E hcp.measurable hcm.measurable _ hMp' hMm' Φ,
    leadOneMark_sub hLM E (hcp.integrable_of_hasCompactSupport hsp)
      (hcm.integrable_of_hasCompactSupport hsm) Φ]
  ring

end BlockBand.Endpoints.Normalization
