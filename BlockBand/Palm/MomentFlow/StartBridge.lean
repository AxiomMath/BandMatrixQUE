module

public import BlockBand.Palm.MomentFlow.BridgeODE
public import BlockBand.Palm.MomentFlow.StartShift

/-!
# The moment-generator bridge from the start time `a`

* `MomentIdentity F a s c q`, `GapCover F a s U`: the two inputs of the generator pipeline (the
  integrated conditional identity and the almost sure covering by gap events), as propositions.
  They are **proved** below, never assumed in a final theorem.
* `momentGeneratorBridge_of`: the generator pipeline with these two inputs
  in place of `DysonBrownianMotion N` (the proofs are those of `identity_clamped`, `identity_version`,
  `incV_ae_zero`, `psiV_ae_eq`, `momentGeneratorBridge`, with the two inputs substituted).
* `momentIdentity_of_lt`, `gapCover_of_lt`: the inputs for `s > a` (from `DysonBrownianMotion N`).
* `momentIdentity_start`, `gapCover_start`: the inputs for `s = a > 0`, transported from the flow
  with base variance `a/2` through the restart map (law preservation and intertwining after
  time `a`).
* **`momentGeneratorBridge_start`**: consuming only `DysonBrownianMotion N`, for Hermitian `F`,
  `0 < a ≤ c`, `q`, `r`: a version `Φ` with `Φ σ ξ =ᵐ condMoment F a c q σ ξ`
  (`= E[mono(X(σ),ξ) | pathSigma F a a c]`) for `σ ∈ [a, c]`, `ξ` in the `r`-sector, solving
  `IsMomentFlowSolution (flowRate F a ω) r a c` along almost every path.
* `condExp_comp_measurePreserving`: conditional expectations commute with a measure-preserving map
  (`E_ν[f | m] ∘ T = E_μ[f ∘ T | T⁻¹ m]` a.s.), and `comap_restartMap_pathSigma`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-!
## The two inputs of the pipeline
-/

/-- The integrated conditional identity on `[s, c]` (conclusion of `integrated_moment_identity`). -/
def MomentIdentity (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (q : Fin N → ℂ) : Prop :=
  ∀ (ξ : Occ N) {u : ℝ≥0}, s + u ≤ c → ∀ {δ : ℝ}, 0 < δ → ∀ {Λ : FlowSample N → ℝ},
    Measurable[pathSigma F a s c] Λ → (∃ C, ∀ ω, |Λ ω| ≤ C) →
    Integrable (fun ω => (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        momentIncrement F a q ξ s u ω) (flowLaw N a) ∧
      ∫ ω, (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        momentIncrement F a q ξ s u ω ∂flowLaw N a = 0

/-- Almost surely `ω.1` is Hermitian and some rational gap event on `[s, s+U]` holds. -/
def GapCover (F : Matrix (Fin N) (Fin N) ℂ) (a s : ℝ) (U : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian ∧ ∃ δ : ℚ, 0 < δ ∧ ω ∈ gapGood F a δ s U

/-!
## The pipeline with abstract inputs
-/

theorem identity_clamped_of {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (q : Fin N → ℂ) (hId : MomentIdentity F a s c q) (ζ : Occ N) {U : ℝ≥0}
    (hsc : s + U ≤ c) {u : ℝ≥0} (hu : u ≤ U) {δ : ℝ} (hδ : 0 < δ) {Λ : FlowSample N → ℝ}
    (hΛ : Measurable[pathSigma F a s c] Λ) {C : ℝ} (hΛb : ∀ ω, |Λ ω| ≤ C) :
    Integrable (fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        incC F a s U (Ycl F a q) ζ u ω) (flowLaw N a) ∧
      ∫ ω, (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        incC F a s U (Ycl F a q) ζ u ω ∂flowLaw N a = 0 := by
  set Λ' : FlowSample N → ℝ := fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω
  have hΛ' : Measurable[pathSigma F a s c] Λ' :=
    (measurable_const.indicator (measurableSet_gapGood F a δ hsc)).mul hΛ
  have hΛ'b : ∃ C', ∀ ω, |Λ' ω| ≤ C' := by
    refine ⟨max C 0, fun ω => ?_⟩
    simp only [Λ']
    by_cases h : ω ∈ gapGood F a δ s U
    · rw [Set.indicator_of_mem h, one_mul]; exact (hΛb _).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem h, zero_mul, abs_zero]; exact le_max_right _ _
  have huc : s + (u : ℝ) ≤ c := le_trans (by gcongr) hsc
  have key := hId ζ huc hδ hΛ' hΛ'b
  have hHerm : ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian := by
    filter_upwards [hermProj_ae_eq (N := N) a] with ω hω
    rw [← hω]; exact hermPart_isHermitian _
  have hae : (fun ω => (gapGood F a δ s u).indicator (fun _ => (1 : ℝ)) ω * Λ' ω *
      momentIncrement F a q ζ s u ω) =ᵐ[flowLaw N a]
      fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
        incC F a s U (Ycl F a q) ζ u ω := by
    filter_upwards [hHerm] with ω hH
    by_cases hω : ω ∈ gapGood F a δ s U
    · simp only [Λ', Set.indicator_of_mem hω, Set.indicator_of_mem (gapGood_mono hu hω), one_mul]
      rw [momentIncrement_eq_incC hF hδ q ζ hu hω hH]
    · simp [Λ', hω]
  exact ⟨key.1.congr hae, (integral_congr_ae hae).symm.trans key.2⟩

theorem identity_version_of {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (q : Fin N → ℂ) (hId : MomentIdentity F a s c q) (ζ : Occ N) {U : ℝ≥0}
    (hsc : s + U ≤ c) {u : ℝ≥0} (hu : u ≤ U) {δ : ℝ} (hδ : 0 < δ) {Λ : FlowSample N → ℝ}
    (hΛ : Measurable[pathSigma F a s c] Λ) {C : ℝ} (hΛb : ∀ ω, |Λ ω| ≤ C) :
    ∫ ω, (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω *
      incC F a s U (Vver F a s c q) ζ u ω ∂flowLaw N a = 0 := by
  set g : FlowSample N → ℝ := fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω * Λ ω
  have hg : GapWeight F a s c δ U (max C 0) g := by
    refine ⟨(measurable_const.indicator (measurableSet_gapGood F a δ hsc)).mul hΛ,
      fun ω => ?_, fun ω hω => by simp [g, hω]⟩
    simp only [g]
    by_cases h : ω ∈ gapGood F a δ s U
    · rw [Set.indicator_of_mem h, one_mul]; exact (hΛb _).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem h, zero_mul, abs_zero]; exact le_max_right _ _
  have hYm : ∀ ζ, Measurable fun p : ℝ × FlowSample N => Ycl F a q ζ p.1 p.2 :=
    fun ζ => measurable_clampedMoment_uncurry F a q ζ
  have hYb : ∀ ζ σ ω, |Ycl F a q ζ σ ω| ≤ momentLevel q ζ :=
    fun ζ σ ω => abs_clampedMoment_le F a q ζ σ ω
  have hVm : ∀ ζ, Measurable fun p : ℝ × FlowSample N => Vver F a s c q ζ p.1 p.2 :=
    fun ζ => measurable_momentVersion F a s c q ζ
  have hVb : ∀ ζ σ ω, |Vver F a s c q ζ σ ω| ≤ momentLevel q ζ :=
    fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω
  have hgb : ∀ ω, |g ω| ≤ max C 0 := hg.bound
  have key := (identity_clamped_of hF q hId ζ hsc hu hδ hΛ hΛb).2
  change ∫ ω, g ω * incC F a s U (Ycl F a q) ζ u ω ∂flowLaw N a = 0 at key
  change ∫ ω, g ω * incC F a s U (Vver F a s c q) ζ u ω ∂flowLaw N a = 0
  rw [(integrable_weight_mul_incC hF hδ hg q hYm hYb ζ u).2.2] at key
  rw [(integrable_weight_mul_incC hF hδ hg q hVm hVb ζ u).2.2,
    (integral_weight_mul_integral_genC hF hδ hg q hVm hVb ζ u).2]
  rw [(integral_weight_mul_integral_genC hF hδ hg q hYm hYb ζ u).2] at key
  rw [← integral_mul_Ycl_eq F a s c q ζ _ hg.meas hgb,
    ← integral_mul_Ycl_eq F a s c q ζ _ hg.meas hgb]
  have hr : ∀ r, ∫ ω, g ω * genC F a s U (Vver F a s c q) ζ r ω ∂flowLaw N a =
      ∫ ω, g ω * genC F a s U (Ycl F a q) ζ r ω ∂flowLaw N a :=
    fun r => (integral_weight_mul_genC_eq hF hδ hsc hg q ζ r).symm
  simp_rw [hr]
  exact key

theorem incV_ae_zero_of {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (q : Fin N → ℂ) (hId : MomentIdentity F a s c q) (ζ : Occ N) {U : ℝ≥0}
    (hsc : s + U ≤ c) {u : ℝ≥0} (hu : u ≤ U) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂flowLaw N a, ω ∈ gapGood F a δ s U → incC F a s U (Vver F a s c q) ζ u ω = 0 := by
  set D : FlowSample N → ℝ := fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω *
    incC F a s U (Vver F a s c q) ζ u ω
  have hDm : Measurable[pathSigma F a s c] D :=
    (measurable_const.indicator (measurableSet_gapGood F a δ hsc)).mul
      (measurable_incV_pathSigma hF q ζ hsc u)
  have hgw : GapWeight F a s c δ U 1 (fun ω => (gapGood F a δ s U).indicator (fun _ => (1 : ℝ)) ω) := by
    refine ⟨measurable_const.indicator (measurableSet_gapGood F a δ hsc), fun ω => ?_,
      fun ω hω => by simp [hω]⟩
    by_cases h : ω ∈ gapGood F a δ s U <;> simp [h]
  have hDint : Integrable D (flowLaw N a) := by
    have h := integrable_weight_mul_incC hF hδ hgw q (fun ζ => measurable_momentVersion F a s c q ζ)
      (fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω) ζ u
    have h3 := (integral_weight_mul_integral_genC hF hδ hgw q
      (fun ζ => measurable_momentVersion F a s c q ζ)
      (fun ζ σ ω => abs_momentVersion_le F a s c q ζ σ ω) ζ u).1
    refine ((h.1.sub h.2.1).sub h3).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [D, incC, Pi.sub_apply]; ring
  have hD0 : D =ᵐ[flowLaw N a] 0 := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (pathSigma_le F a s c)
      (fun A _ _ => hDint.integrableOn) (fun A _ _ => integrableOn_zero) (fun A hA _ => ?_)
      hDm.aestronglyMeasurable stronglyMeasurable_zero.aestronglyMeasurable
    rw [Pi.zero_def, integral_zero, ← integral_indicator ((pathSigma_le F a s c) A hA)]
    have hΛ : Measurable[pathSigma F a s c] (A.indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hA
    have h := identity_version_of hF q hId ζ hsc hu hδ hΛ (C := 1)
      (fun ω => by by_cases h : ω ∈ A <;> simp [h])
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans h
    simp only [D]
    by_cases h : ω ∈ A <;> simp [h]
  filter_upwards [hD0] with ω hω hB
  simpa [D, hB] using hω

theorem psiV_ae_eq_of {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (q : Fin N → ℂ) (hId : MomentIdentity F a s c q) (ζ : Occ N)
    {U : ℝ≥0} (hsc : s + U ≤ c) (hGap : GapCover F a s U) {σ : ℝ} (hσ : σ ∈ Icc s (s + U)) :
    psiV F a s c q U ζ σ =ᵐ[flowLaw N a] Vver F a s c q ζ σ := by
  set u : ℝ≥0 := Real.toNNReal (σ - s)
  have hu' : (u : ℝ) = σ - s := Real.coe_toNNReal _ (by linarith [hσ.1])
  have hu : u ≤ U := by
    rw [← NNReal.coe_le_coe, hu']; linarith [hσ.2]
  have hall : ∀ᵐ ω ∂flowLaw N a, ∀ δ : ℚ, 0 < δ → ω ∈ gapGood F a δ s U →
      incC F a s U (Vver F a s c q) ζ u ω = 0 := by
    rw [ae_all_iff]
    intro δ
    by_cases hδ : (0 : ℚ) < δ
    · filter_upwards [incV_ae_zero_of hF q hId ζ hsc hu (δ := δ) (by exact_mod_cast hδ)] with
        ω hω _ hB using hω hB
    · exact Filter.Eventually.of_forall fun ω h => absurd h hδ
  filter_upwards [hall, hGap.mono fun _ h => h.2] with ω hω hex
  obtain ⟨δ, hδ, hB⟩ := hex
  have h0 := hω δ hδ hB
  simp only [incC, hu'] at h0
  simp only [psiV]
  rw [show s + (σ - s) = σ by ring] at h0
  linarith

theorem momentGeneratorBridge_of (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) {a s c : ℝ} (hsc : s ≤ c) (q : Fin N → ℂ)
    (hId : MomentIdentity F a s c q) (hGap : GapCover F a s (Real.toNNReal (c - s))) (r : ℕ) :
    ∃ Φ : ℝ → Occ N → FlowSample N → ℝ,
      (∀ σ ∈ Icc s c, ∀ ξ ∈ sector N r,
        Φ σ ξ =ᵐ[flowLaw N a]
          (flowLaw N a)[fun ω => momentMonomial (fun k => flowOverlap F a q σ k ω) ξ |
            pathSigma F a s c]) ∧
      ∀ᵐ ω ∂flowLaw N a, IsMomentFlowSolution (flowRate F a ω) r s c (fun σ ξ => Φ σ ξ ω) := by
  set U : ℝ≥0 := Real.toNNReal (c - s)
  have hU : (U : ℝ) = c - s := Real.coe_toNNReal _ (by linarith)
  have hsU : s + (U : ℝ) = c := by rw [hU]; ring
  have hscU : s + (U : ℝ) ≤ c := hsU.le
  refine ⟨fun σ ξ ω => psiV F a s c q U ξ σ ω, ?_, ?_⟩
  · -- the version property
    intro σ hσ ξ _
    have hσ' : σ ∈ Icc s (s + U) := by rw [hsU]; exact hσ
    refine (psiV_ae_eq_of hF q hId ξ hscU hGap hσ').trans
      ((momentVersion_ae_eq F a s c q ξ σ).trans (condExp_congr_ae ?_))
    filter_upwards [hGap] with ω hω
    obtain ⟨hH, δ, hδ, hB⟩ := hω
    have hs := simple_of_gapGood hF (by exact_mod_cast hδ) hB hH (v := σ - s)
      (by linarith [hσ.1]) (by rw [hU]; linarith [hσ.2])
    rw [show s + (σ - s) = σ by ring] at hs
    exact clampedMoment_eq q ξ (flowMatrix_isHermitian hF a hH _) hs
  · -- the ODE along almost every path
    have hE2 : ∀ ζ ∈ sector N r, ∀ᵐ ω ∂flowLaw N a,
        ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) U)),
          Vver F a s c q ζ (s + v) ω = psiV F a s c q U ζ (s + v) ω := by
      intro ζ _
      have hmeas : MeasurableSet {x : ℝ × FlowSample N |
          Vver F a s c q ζ (s + x.1) x.2 = psiV F a s c q U ζ (s + x.1) x.2} := by
        have hsh : Measurable (fun x : ℝ × FlowSample N => (s + x.1, x.2)) :=
          ((measurable_const_add s).comp measurable_fst).prodMk measurable_snd
        have h1 : Measurable (fun x : ℝ × FlowSample N => Vver F a s c q ζ (s + x.1) x.2) := by
          have := (measurable_momentVersion F a s c q ζ).comp hsh
          simpa only [Function.comp_def] using this
        have h2 : Measurable (fun x : ℝ × FlowSample N => psiV F a s c q U ζ (s + x.1) x.2) := by
          have := (measurable_psiV F a s c q U ζ).comp hsh
          simpa only [Function.comp_def] using this
        exact measurableSet_eq_fun h1 h2
      refine (Measure.ae_ae_comm (μ := volume.restrict (Icc (0 : ℝ) U)) (ν := flowLaw N a)
        (p := fun v ω => Vver F a s c q ζ (s + v) ω = psiV F a s c q U ζ (s + v) ω) hmeas).1 ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc fun v hv => ?_
      exact (psiV_ae_eq_of hF q hId ζ hscU hGap ⟨by linarith [hv.1], by linarith [hv.2]⟩).symm
    have hE2' : ∀ᵐ ω ∂flowLaw N a, ∀ ζ ∈ sector N r,
        ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) U)),
          Vver F a s c q ζ (s + v) ω = psiV F a s c q U ζ (s + v) ω :=
      (Filter.eventually_all_finset _).2 hE2
    filter_upwards [hE2', hGap.mono fun _ h => h.2] with ω hω hex
    obtain ⟨δ, hδq, hB⟩ := hex
    have hδ : (0 : ℝ) < δ := by exact_mod_cast hδq
    intro ξ hξ
    refine ⟨continuousOn_psiV hF hδ q hB ξ c, fun σ hσ => ?_⟩
    -- the integral equation with `Ψ` in the integrand
    have hint : ∀ σ' ∈ Icc s c, psiV F a s c q U ξ σ' ω = Vver F a s c q ξ s ω +
        ∫ r in (0 : ℝ)..(σ' - s), genC F a s U (psiV F a s c q U) ξ r ω := by
      intro σ' hσ'
      rw [psiV_eq_primitive q U ξ hσ'.1 ω]
      congr 1
      rw [intervalIntegral.integral_of_le (by linarith [hσ'.1]),
        intervalIntegral.integral_of_le (by linarith [hσ'.1])]
      have hsub : Ioc (0 : ℝ) (σ' - s) ⊆ Icc 0 U :=
        fun r hr => ⟨hr.1.le, by rw [hU]; linarith [hr.2, hσ'.2]⟩
      have hae : ∀ᵐ v ∂(volume.restrict (Ioc (0 : ℝ) (σ' - s))),
          genC F a s U (Vver F a s c q) ξ v ω = genC F a s U (psiV F a s c q U) ξ v ω := by
        have h := ae_restrict_of_ae_restrict_of_subset hsub
          ((Filter.eventually_all_finset (sector N r)).2 fun ζ hζ => hω ζ hζ)
        filter_upwards [h] with v hv
        unfold genC
        exact momentGenerator_congr_sector _ (fun ζ hζ => hv ζ hζ) hξ
      exact setIntegral_congr_ae measurableSet_Ioc ((ae_restrict_iff' measurableSet_Ioc).1 hae)
    -- FTC at `σ - s ∈ (0, U)`
    have hx : σ - s ∈ Ioo (0 : ℝ) U := ⟨by linarith [hσ.1], by rw [hU]; linarith [hσ.2]⟩
    have hcont := continuousOn_genC_psiV hF hδ q hB ξ U (c := c)
    have hderiv : HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, genC F a s U (psiV F a s c q U) ξ r ω)
        (genC F a s U (psiV F a s c q U) ξ (σ - s) ω) (σ - s) := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · refine (hcont.mono ?_).intervalIntegrable
        rw [uIcc_of_le hx.1.le]
        exact Icc_subset_Icc le_rfl hx.2.le
      · exact (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo _ hx
      · exact hcont.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hcomp := (hderiv.comp σ ((hasDerivAt_id σ).sub_const s)).const_add
      (Vver F a s c q ξ s ω)
    simp only [Function.comp_def, id, mul_one] at hcomp
    have hev : (fun σ' => psiV F a s c q U ξ σ' ω) =ᶠ[𝓝 σ] fun σ' =>
        Vver F a s c q ξ s ω + ∫ r in (0 : ℝ)..(σ' - s),
          genC F a s U (psiV F a s c q U) ξ r ω := by
      filter_upwards [Ioo_mem_nhds hσ.1 hσ.2] with σ' hσ'
      exact hint σ' (Ioo_subset_Icc_self hσ')
    have hval : genC F a s U (psiV F a s c q U) ξ (σ - s) ω =
        momentGenerator (flowRate F a ω σ) (fun ζ => psiV F a s c q U ζ σ ω) ξ := by
      unfold genC
      rw [rateC_eq (Ioo_subset_Icc_self hx), show s + (σ - s) = σ by ring]
    rw [← hval]
    exact hcomp.congr_of_eventuallyEq hev

/-!
## The inputs after the start (`s > a`)
-/

theorem momentIdentity_of_lt (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s c : ℝ} (has : a < s) (q : Fin N → ℂ) : MomentIdentity F a s c q :=
  fun ξ _ huc _ hδ _ hΛ hΛb => integrated_moment_identity hDBM hF has q ξ huc hδ hΛ hΛb

theorem gapCover_of_lt (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a s : ℝ} (has : a < s) (U : ℝ≥0) : GapCover F a s U := by
  filter_upwards [ae_simple hDBM hF a, ae_exists_gapGood hDBM hF has U] with ω h1 h2
  exact ⟨h1.1, h2⟩

/-!
## Transport through the restart map
-/

theorem gapGood_restartMap {F : Matrix (Fin N) (Fin N) ℂ} {a' a δ : ℝ} (ha : a' ≤ a)
    (u : ℝ≥0) (ω : FlowSample N) :
    restartMap a' a ω ∈ gapGood F a δ a u ↔ ω ∈ gapGood F a' δ a u := by
  simp only [gapGood, Set.mem_ofPred_eq]
  refine forall_congr' fun v => forall_congr' fun hv => ?_
  simp only [flowEigenvalue_restartMap F ha (by linarith : a ≤ a + (v : ℝ))]

theorem momentIncrement_restartMap (F : Matrix (Fin N) (Fin N) ℂ) {a' a : ℝ} (ha : a' ≤ a)
    (q : Fin N → ℂ) (ξ : Occ N) (u : ℝ≥0) (ω : FlowSample N) :
    momentIncrement F a q ξ a u (restartMap a' a ω) = momentIncrement F a' q ξ a u ω := by
  unfold momentIncrement
  have hu : a ≤ a + (u : ℝ) := by linarith [u.2]
  simp only [flowOverlap_restartMap F ha hu, flowOverlap_restartMap F ha le_rfl]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr' : a ≤ a + r := by linarith [hr.1]
  simp only [flowMomentGenerator, flowRate_restartMap F ha hr', flowOverlap_restartMap F ha hr']

/-- Pull-back of the path σ-algebra: `T⁻¹ 𝓛_a ≤ 𝓛_{a'}` on `[a, c]`. -/
theorem comap_restartMap_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) {a' a c : ℝ} (ha : a' ≤ a) :
    MeasurableSpace.comap (restartMap a' a) (pathSigma F a a c) ≤ pathSigma F a' a c := by
  unfold pathSigma
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun σ hσ => iSup_le fun k => ?_
  have e : ((fun ω => flowEigenvalue F a ω σ k) ∘ restartMap a' a) =
      fun ω => flowEigenvalue F a' ω σ k := by
    funext ω; exact flowEigenvalue_restartMap F ha hσ.1 ω k
  rw [e]
  exact (measurable_flowEigenvalue_pathSigma F a' a c hσ k).comap_le

theorem measurable_momentIncrement (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (q : Fin N → ℂ)
    (ξ : Occ N) (s : ℝ) (u : ℝ≥0) : Measurable (momentIncrement F a q ξ s u) := by
  have hX : ∀ σ, Measurable (fun ω => momentMonomial (fun k => flowOverlap F a q σ k ω) ξ) :=
    fun σ => (measurable_momentMonomial ξ).comp
      (Measurable.of_eval fun k => measurable_flowOverlap F a q σ k)
  have hsh : Measurable (fun p : ℝ × FlowSample N => (s + p.1, p.2)) :=
    ((measurable_const_add s).comp measurable_fst).prodMk measurable_snd
  have hlam : ∀ k, Measurable (fun p : ℝ × FlowSample N => flowEigenvalue F a p.2 (s + p.1) k) :=
    fun k => by
      have := (measurable_flowEigenvalue_uncurry F a k).comp hsh
      simpa only [Function.comp_def] using this
  have hrate : ∀ i j, Measurable (fun p : ℝ × FlowSample N => flowRate F a p.2 (s + p.1) i j) :=
    fun i j => by
      unfold flowRate
      exact (measurable_const.mul (((hlam i).sub (hlam j)).pow_const 2)).inv
  have hov : ∀ ζ, Measurable (fun p : ℝ × FlowSample N =>
      momentMonomial (fun k => flowOverlap F a q (s + p.1) k p.2) ζ) := fun ζ => by
    refine (measurable_momentMonomial ζ).comp (Measurable.of_eval fun k => ?_)
    have := (measurable_flowOverlap_uncurry F a q k).comp hsh
    simpa only [Function.comp_def] using this
  have hG := measurable_momentGenerator_param (c := fun p : ℝ × FlowSample N =>
      flowRate F a p.2 (s + p.1))
    (f := fun p ζ => momentMonomial (fun k => flowOverlap F a q (s + p.1) k p.2) ζ) hrate hov ξ
  have hI := measurable_setIntegral_prod hG (Ioc 0 u)
  unfold momentIncrement
  exact ((hX _).sub (hX _)).sub hI

/-- **The integrated identity from the start time** `a > 0`, from the flow with base `a/2`. -/
theorem momentIdentity_start (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (q : Fin N → ℂ) : MomentIdentity F a a c q := by
  intro ξ u huc δ hδ Λ hΛ hΛb
  have ha' : a / 2 ≤ a := by linarith
  have hT := measurePreserving_restartMap (N := N) (by linarith : (0 : ℝ) ≤ a / 2) ha'
  set I : FlowSample N → ℝ := fun ω => (gapGood F a δ a u).indicator (fun _ => (1 : ℝ)) ω *
    Λ ω * momentIncrement F a q ξ a u ω
  have hIm : Measurable I :=
    ((measurable_const.indicator (pathSigma_le F a a c _
      (measurableSet_gapGood F a δ huc))).mul (hΛ.mono (pathSigma_le F a a c) le_rfl)).mul
      (measurable_momentIncrement F a q ξ a u)
  have hΛT : Measurable[pathSigma F (a / 2) a c] (fun ω => Λ (restartMap (a / 2) a ω)) :=
    (hΛ.comp (comap_measurable (restartMap (a / 2) a))).mono
      (comap_restartMap_pathSigma F ha') le_rfl
  have hΛTb : ∃ C, ∀ ω, |Λ (restartMap (a / 2) a ω)| ≤ C := by
    obtain ⟨C, hC⟩ := hΛb; exact ⟨C, fun ω => hC _⟩
  have key := integrated_moment_identity hDBM hF (by linarith : a / 2 < a) q ξ huc hδ hΛT hΛTb
  have hcomp : (fun ω => I (restartMap (a / 2) a ω)) = fun ω =>
      (gapGood F (a / 2) δ a u).indicator (fun _ => (1 : ℝ)) ω * Λ (restartMap (a / 2) a ω) *
        momentIncrement F (a / 2) q ξ a u ω := by
    funext ω
    simp only [I, momentIncrement_restartMap F ha']
    congr 2
    by_cases h : ω ∈ gapGood F (a / 2) δ a u
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((gapGood_restartMap ha' u ω).2 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
        (fun h' => h ((gapGood_restartMap ha' u ω).1 h'))]
  rw [← hT.map_eq]
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure hIm.aestronglyMeasurable hT.measurable.aemeasurable]
    change Integrable (fun ω => I (restartMap (a / 2) a ω)) _
    rw [hcomp]; exact key.1
  · rw [integral_map hT.measurable.aemeasurable hIm.aestronglyMeasurable]
    change ∫ ω, I (restartMap (a / 2) a ω) ∂_ = 0
    rw [hcomp]; exact key.2

theorem gapCover_start (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (U : ℝ≥0) (hU : a + U ≤ c) :
    GapCover F a a U := by
  have ha' : a / 2 ≤ a := by linarith
  have hT := measurePreserving_restartMap (N := N) (by linarith : (0 : ℝ) ≤ a / 2) ha'
  have hS : MeasurableSet {ω : FlowSample N | ω.1.IsHermitian ∧
      ∃ δ : ℚ, 0 < δ ∧ ω ∈ gapGood F a δ a U} := by
    refine (measurable_fst BlockBand.Model.Construction.measurableSet_isHermitian).inter ?_
    have e : {ω : FlowSample N | ∃ δ : ℚ, 0 < δ ∧ ω ∈ gapGood F a δ a U} =
        ⋃ δ : ℚ, ⋃ (_ : 0 < δ), gapGood F a δ a U := by ext ω; simp
    change MeasurableSet {ω : FlowSample N | ∃ δ : ℚ, 0 < δ ∧ ω ∈ gapGood F a δ a U}
    rw [e]
    exact MeasurableSet.iUnion fun δ => MeasurableSet.iUnion fun _ =>
      pathSigma_le F a a c _ (measurableSet_gapGood F a δ hU)
  unfold GapCover
  rw [← hT.map_eq, ae_map_iff hT.measurable.aemeasurable hS]
  filter_upwards [gapCover_of_lt hDBM hF (by linarith : a / 2 < a) U] with ω hω
  obtain ⟨hH, δ, hδ, hB⟩ := hω
  exact ⟨hH.add (hermitianBrownian_isHermitian _ _), δ, hδ, (gapGood_restartMap ha' U ω).2 hB⟩

/-- **Moment-generator bridge from the start time.** Assuming only `DysonBrownianMotion N`: for
Hermitian `F` and `0 < a ≤ c`, a version of
`condMoment F a c q σ ξ = E[mono(X(σ), ξ) | pathSigma F a a c]` solves the moment flow on `[a, c]`
along almost every path. -/
theorem momentGeneratorBridge_start (hDBM : DysonBrownianMotion N) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (q : Fin N → ℂ) (r : ℕ) :
    ∃ Φ : ℝ → Occ N → FlowSample N → ℝ,
      (∀ σ ∈ Icc a c, ∀ ξ ∈ sector N r, Φ σ ξ =ᵐ[flowLaw N a] condMoment F a c q σ ξ) ∧
      ∀ᵐ ω ∂flowLaw N a, IsMomentFlowSolution (flowRate F a ω) r a c (fun σ ξ => Φ σ ξ ω) := by
  have hU : a + (Real.toNNReal (c - a) : ℝ) ≤ c := by
    rw [Real.coe_toNNReal _ (by linarith)]; linarith
  exact momentGeneratorBridge_of F hF hac q (momentIdentity_start hDBM hF ha q)
    (gapCover_start hDBM hF ha _ hU) r

/-!
## Conditional expectations and measure-preserving maps
-/

/-- `E_ν[f | m] ∘ T = E_μ[f ∘ T | T⁻¹ m]` almost surely, for measure-preserving `T`. -/
theorem condExp_comp_measurePreserving {α β : Type*} {m : MeasurableSpace β}
    [mα : MeasurableSpace α] [mβ : MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {T : α → β} (hT : MeasurePreserving T μ ν)
    (hm : m ≤ mβ) {f : β → ℝ} (hf : Integrable f ν) :
    (fun x => (ν[f | m]) (T x)) =ᵐ[μ] μ[fun x => f (T x) | m.comap T] := by
  have hm' : m.comap T ≤ mα := (MeasurableSpace.comap_mono hm).trans hT.measurable.comap_le
  have hfT : Integrable (fun x => f (T x)) μ := hT.integrable_comp_of_integrable hf
  have hgT : Integrable (fun x => (ν[f | m]) (T x)) μ :=
    hT.integrable_comp_of_integrable integrable_condExp
  refine ae_eq_condExp_of_forall_setIntegral_eq hm' hfT (fun _ _ _ => hgT.integrableOn)
    (fun s hs _ => ?_) ?_
  · obtain ⟨A, hA, rfl⟩ := hs
    rw [← hT.map_eq] at hf ⊢
    have hAβ := hm A hA
    rw [← setIntegral_map hAβ (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
        hT.measurable.aemeasurable,
      ← setIntegral_map hAβ hf.aestronglyMeasurable hT.measurable.aemeasurable]
    rw [hT.map_eq] at hf ⊢
    exact setIntegral_condExp hm hf hA
  · exact (stronglyMeasurable_condExp.comp_measurable (comap_measurable T)).aestronglyMeasurable

end BlockBand.Palm.MomentFlow
