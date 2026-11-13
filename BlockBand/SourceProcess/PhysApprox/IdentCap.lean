module

public import BlockBand.SourceProcess.PhysApprox.Assembly
public import BlockBand.SourceProcess.ClosedIdent.Main
public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability
public import BlockBand.SourceProcess.ComplexCapLimit.Main
public import BlockBand.SourceProcess.PhysApprox.Meas

/-!
# Cap removal: the closed identification from the capped one

This file proves `TargetT6`: the capped identification `ComplexCappedClosedIdentification` gives
the closed identification `ComplexClosedIdentification`. It is the complex analogue of
`ClosedIdent.closedIdentification_of_capped`. With `ε/3` each,
`|closed − v| ≤ |closed − capped| + |capped − restricted| + |restricted − v|`:

* first term: `|closed − capped| ≤ ‖Φ‖ P_W(more than K retained modes at s)`
  (`abs_closed_sub_capped_le`), small by `TransmissionLawContract`;
* middle term: the hypothesis `ComplexCappedClosedIdentification`;
* last term: the two model-side facts (cap tail and entrance tail).

Results: `abs_closed_sub_capped_le`; `complexClosedIdentification_of_capped_of` (from
`TransmissionLawContract`, integrability, the two model-side facts and
`ComplexCappedClosedIdentification`); `complexModelRestrictTail_holds`,
`complexEntranceCapTail_holds`; `targetT6_of_integrable`; **`targetT6_holds : TargetT6`** (no
hypotheses beyond those of `TargetT6`).

Measures: `probedPathLaw W np b ⊗ phaseLaw` (physical), `growthPathLaw W b` (cap event), the
model's `Q` (model side). Domain `ComplexSourceLawDomain b E τ m T`, `0 < s < min τ_j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-!
## The two model-side facts
-/

/-- **Model side of the cap removal** (`ComplexCapLimit.integrable_final` +
`ComplexCapLimit.abs_setIntegral_compl_le`; `complexModelRestrictTail_holds`): in every complex
finite model at `(h, K)`, the final value and its restriction to `{t_K ≤ h²}` differ by at most
`‖Φ‖ P(t_K > h²)`. -/
def ComplexModelRestrictTail : Prop :=
  ∀ (b E s : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (h : ℝ) (K : ℕ)
    (entrance : Measure (Measure unitInterval)) (Ω : Type) (mΩ : MeasurableSpace Ω)
    (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω) (tseq : Ω → ℕ → ℝ)
    (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc →
    ∀ (T : ℝ) (Φ : BoundedContinuousFunction (SourceData np) ℝ),
      |∫ ω, Φ (modelSourceData (srcSignature K (Fin np)) (Kc (T - s).toNNReal ω)
          (G (T - s).toNNReal ω)) ∂Q - restrictedModelExpectation K h s T Q tseq G Kc Φ| ≤
        ‖Φ‖ * (entrance (capSet K h)ᶜ).toReal

/-- **Entrance tail** (`ComplexCapLimit.tendsto_capSet_compl`; `complexEntranceCapTail_holds`): if
some complex finite model with entrance `entrance` exists at some cap `K₀` and `h > 0`, then
`entrance (capSet K h)ᶜ = P(t_K > h²) → 0` as `K → ∞`. -/
def ComplexEntranceCapTail : Prop :=
  ∀ (b E s : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (h : ℝ) (K₀ : ℕ)
    (entrance : Measure (Measure unitInterval)) (Ω : Type) (mΩ : MeasurableSpace Ω)
    (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω) (tseq : Ω → ℕ → ℝ)
    (G : ℝ≥0 → Ω → GramState (SrcCol K₀ (Fin np))) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K₀ entrance 𝓖 Q tseq G Kc → 0 < h →
      Tendsto (fun K : ℕ => (entrance (capSet K h)ᶜ).toReal) atTop (𝓝 0)

/-!
## Physical side
-/

/-- `Φ ∘ closedSourceData` is integrable under `probedPathLaw ⊗ phaseLaw` (the type of
`integrable_closedIntegrand`; `closedIntegrandIntegrable_holds`). -/
def ClosedIntegrandIntegrable : Prop :=
  ∀ {np : ℕ} (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ),
    Integrable (fun y : ProbedPath W np × ℝ =>
      Φ (closedSourceData b E s T h τ m W (phase y.2) y.1))
      ((probedPathLaw W np b).prod phaseLaw)

/-- The cap event `physCapEventC` is `ClosedIdent.physCapEvent`. -/
theorem physCapEventC_eq : physCapEventC = ClosedIdent.physCapEvent := rfl

/-- The path coordinate of `probedPathLaw ⊗ phaseLaw` has law `growthPathLaw`. -/
theorem probedPhase_preimage_path {W np : ℕ} (b : ℝ) (A : Set (GrowthPath W)) :
    ((probedPathLaw W np b).prod phaseLaw) ((fun y : ProbedPath W np × ℝ => y.1.1) ⁻¹' A) =
      growthPathLaw W b A := by
  have e : (fun y : ProbedPath W np × ℝ => y.1.1) ⁻¹' A = (A ×ˢ univ) ×ˢ univ := by
    ext y; simp
  rw [e, Measure.prod_prod, probedPathLaw, Measure.prod_prod, measure_univ, measure_univ,
    mul_one, mul_one]

/-- `|∫ f − ∫_A f| ≤ C ν(Aᶜ)` for an integrable `f` bounded by `C`. -/
theorem abs_integral_sub_indicator_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Integrable f ν) {C : ℝ} (hC : ∀ y, |f y| ≤ C)
    {A : Set α} (hA : MeasurableSet A) :
    |∫ y, f y ∂ν - ∫ y, A.indicator f y ∂ν| ≤ C * ν.real Aᶜ := by
  rw [← integral_sub hf (hf.indicator hA)]
  have e : (fun y => f y - A.indicator f y) = Aᶜ.indicator f := by
    funext y
    by_cases hy : y ∈ A
    · simp [Set.indicator_of_mem hy, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hy)]
    · simp [Set.indicator_of_notMem hy, Set.indicator_of_mem (Set.mem_compl hy)]
  rw [e, ← Real.norm_eq_abs]
  calc ‖∫ y, Aᶜ.indicator f y ∂ν‖ ≤ ∫ y, Aᶜ.indicator (fun _ => C) y ∂ν :=
        norm_integral_le_of_norm_le ((integrable_const C).indicator hA.compl)
          (ae_of_all _ fun y => by
            by_cases hy : y ∈ Aᶜ
            · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Real.norm_eq_abs]
              exact hC y
            · simp [Set.indicator_of_notMem hy])
    _ = C * ν.real Aᶜ := by rw [integral_indicator_const _ hA.compl, smul_eq_mul, mul_comm]

/-- **`|closed − capped| ≤ ‖Φ‖ P_W(more than K retained modes at s)`.** -/
theorem abs_closed_sub_capped_le (hI : ClosedIntegrandIntegrable) {b E s T h : ℝ} {np : ℕ}
    {τ m : Fin np → ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (K W : ℕ) :
    |closedPhysExpectation b E s T h τ m Φ W - cappedClosedPhysExpectation b E s T h τ m Φ K W| ≤
      ‖Φ‖ * (growthPathLaw W b (physCapEventC b E s h K W)ᶜ).toReal := by
  have hfi := hI b E s T h τ m W Φ
  have hSM := ClosedIdent.measurableSet_physCapEventM b E s h K W
  have hπ : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.fst
  have hpre : MeasurableSet ((fun y : ProbedPath W np × ℝ => y.1.1) ⁻¹'
      ClosedIdent.physCapEventM b E s h K W) := hπ hSM
  have hqmp : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      ((probedPathLaw W np b).prod phaseLaw) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
      (ν := Measure.pi fun _ : Fin np => CoareaPalm.circularVectorLaw (Fin W))).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b) (ν := phaseLaw))
  have hind : ∀ᵐ y ∂((probedPathLaw W np b).prod phaseLaw),
      (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 =
        (ClosedIdent.physCapEventM b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 :=
    hqmp.ae (indicator_ae_eq_of_ae_eq_set (ClosedIdent.physCapEvent_ae_eq hb hE1 hE2 s h K))
  have hcap : cappedClosedPhysExpectation b E s T h τ m Φ K W =
      ∫ y, ((fun y : ProbedPath W np × ℝ => y.1.1) ⁻¹'
        ClosedIdent.physCapEventM b E s h K W).indicator
          (fun y => Φ (closedSourceData b E s T h τ m W (phase y.2) y.1)) y
        ∂((probedPathLaw W np b).prod phaseLaw) := by
    unfold cappedClosedPhysExpectation
    refine integral_congr_ae (hind.mono fun y hy => ?_)
    dsimp only
    rw [hy]
    by_cases hyA : y.1.1 ∈ ClosedIdent.physCapEventM b E s h K W
    · rw [Set.indicator_of_mem hyA, Set.indicator_of_mem (show y ∈ (fun y : ProbedPath W np × ℝ =>
        y.1.1) ⁻¹' ClosedIdent.physCapEventM b E s h K W from hyA), one_mul]
    · rw [Set.indicator_of_notMem hyA, Set.indicator_of_notMem (show y ∉ (fun y :
        ProbedPath W np × ℝ => y.1.1) ⁻¹' ClosedIdent.physCapEventM b E s h K W from hyA),
        zero_mul]
  rw [hcap]
  refine (abs_integral_sub_indicator_le hfi (C := ‖Φ‖)
    (fun y => by rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _) hpre).trans_eq ?_
  rw [physCapEventC_eq, measureReal_def, ← Set.preimage_compl, probedPhase_preimage_path,
    ← measure_congr (ClosedIdent.physCapEvent_ae_eq hb hE1 hE2 s h K).compl]

/-!
## `TargetT6`
-/

/-- **`ComplexClosedIdentification` from `ComplexCappedClosedIdentification`**, given
`TransmissionLawContract`, integrability and the two model-side facts. -/
theorem complexClosedIdentification_of_capped_of (hTL : TransmissionLawContract)
    (hI : ClosedIntegrandIntegrable) (hR : ComplexModelRestrictTail)
    (hTail : ComplexEntranceCapTail)
    (hC : ComplexCappedClosedIdentification) : ComplexClosedIdentification := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ ε hε
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := id hD
  have hε3 : 0 < ε / 3 := by linarith
  have hb1 : b < 1 := by linarith
  have hfreq := hC b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ (ε / 3) hε3
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine (hfreq.and_eventually hpos).mono fun h ⟨hK, hh⟩ => ?_
  by_cases hex : ∃ (K₀ : ℕ) (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 m')
      (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K₀ (Fin np)))
      (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
      IsFiniteComplexSourceModel b E s τ m h K₀ (entranceLaw P μ s) 𝓖 Q tseq G Kc
  swap
  · refine Frequently.of_forall fun K v hv => ?_
    obtain ⟨Ω', m', 𝓖, Q, tseq, G, Kc, hMod⟩ := hv.1
    exact absurd ⟨K, Ω', m', 𝓖, Q, tseq, G, Kc, hMod⟩ hex
  obtain ⟨K₀, Ω₀, m₀, 𝓖₀, Q₀, tseq₀, G₀, Kc₀, hM₀⟩ := hex
  have hN : 0 < ‖Φ‖ + 1 := by positivity
  have hmt : ∀ᶠ K : ℕ in atTop,
      (entranceLaw P μ s (capSet K h)ᶜ).toReal ≤ ε / 3 / (‖Φ‖ + 1) :=
    ((tendsto_order.1 (hTail b E s np τ m h K₀ _ Ω₀ m₀ 𝓖₀ Q₀ tseq₀ G₀ Kc₀ hM₀ hh)).2 _
      (by positivity)).mono fun _ h => h.le
  have hpt := ClosedIdent.eventually_physCapEvent_compl_le hTL hb0 hb hE1 hE2 hs hh
    (η := ε / 3 / (‖Φ‖ + 1)) (by positivity)
  have hscale : ∀ x : ℝ, 0 ≤ x → x ≤ ε / 3 / (‖Φ‖ + 1) → ‖Φ‖ * x ≤ ε / 3 := by
    intro x hx0 hx
    have h1 : ‖Φ‖ * x ≤ (‖Φ‖ + 1) * x := by nlinarith [norm_nonneg Φ]
    have h2 : (‖Φ‖ + 1) * x ≤ ε / 3 := by rwa [le_div_iff₀ hN, mul_comm] at hx
    linarith
  refine ((hK.and_eventually hmt).and_eventually hpt).mono ?_
  rintro K ⟨⟨hKp, hKm⟩, hKph⟩ v hv
  obtain ⟨Ω', m', 𝓖, Q, tseq, G, Kc, hMod⟩ := hv.1
  have e := hv.2 Ω' m' 𝓖 Q tseq G Kc hMod
  have hmod := hR b E s np τ m h K _ Ω' m' 𝓖 Q tseq G Kc hMod T Φ
  rw [e] at hmod
  have hmod' := hscale _ ENNReal.toReal_nonneg hKm
  filter_upwards [hKp Ω' m' 𝓖 Q tseq G Kc hMod, hKph] with W h1 h2
  have hphys := abs_closed_sub_capped_le hI (s := s) (T := T) (h := h) (τ := τ) (m := m) hb1 hE1 hE2
    Φ K W
  have hphys' : ‖Φ‖ * (growthPathLaw W b (physCapEventC b E s h K W)ᶜ).toReal ≤ ε / 3 :=
    hscale _ ENNReal.toReal_nonneg h2
  have h3 := abs_sub_le (closedPhysExpectation b E s T h τ m Φ W)
    (cappedClosedPhysExpectation b E s T h τ m Φ K W) v
  have h4 := abs_sub_le (cappedClosedPhysExpectation b E s T h τ m Φ K W)
    (restrictedModelExpectation K h s T Q tseq G Kc Φ) v
  rw [abs_sub_comm v] at hmod
  linarith

/-- `TargetT6` from integrability and the two model-side facts. -/
theorem targetT6_of_gaps (hI : ClosedIntegrandIntegrable) (hR : ComplexModelRestrictTail)
    (hTail : ComplexEntranceCapTail) : TargetT6 := fun hMT hGA _ hLp hP hC =>
  complexClosedIdentification_of_capped_of
    (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP) hI hR hTail hC

/-- **The model-side cap tail holds** (`ComplexCapLimit`). -/
theorem complexModelRestrictTail_holds : ComplexModelRestrictTail := by
  intro b E s np τ m h K entrance Ω mΩ 𝓖 Q tseq G Kc hM T Φ
  have := hM.prob
  have hA := 𝓖.le 0 _ (ComplexCapLimit.cmeasurableSet_entEvent hM (measurableSet_capSet K h))
  have hsplit := integral_add_compl hA (ComplexCapLimit.integrable_final hM Φ (T - s).toNNReal)
  have b1 := ComplexCapLimit.abs_setIntegral_compl_le (K := K) hM Φ (T - s).toNNReal
  unfold restrictedModelExpectation
  rw [← hsplit, add_sub_cancel_left]
  exact b1

/-- **The entrance tail holds** (`ComplexCapLimit.tendsto_capSet_compl`). -/
theorem complexEntranceCapTail_holds : ComplexEntranceCapTail :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM hh => ComplexCapLimit.tendsto_capSet_compl hM hh

/-- `TargetT6` given the integrability of the closed integrand. -/
theorem targetT6_of_integrable (hI : ClosedIntegrandIntegrable) : TargetT6 :=
  targetT6_of_gaps hI complexModelRestrictTail_holds complexEntranceCapTail_holds

/-- The closed integrand is integrable. -/
theorem closedIntegrandIntegrable_holds : ClosedIntegrandIntegrable :=
  fun b E s T h τ m W Φ => integrable_closedIntegrand b E s T h τ m W Φ

/-- **`TargetT6` holds.** -/
theorem targetT6_holds : TargetT6 :=
  targetT6_of_integrable closedIntegrandIntegrable_holds

end BlockBand.SourceProcess.PhysApprox
