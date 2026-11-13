module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramPassLim
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramAddFunCap
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalDefs

/-!
# `CapIdentGramGen` from the local Gram estimate

Measures: `closedLaw b W np`, the conditioned laws `Fdd.condL`, the candidate's `Q`.

* **`tendsto_pUnst_large`**: `GramPassLocalLarge` and the hypotheses give `pUnst → 0` (the stop tail
  level `R` is raised to `max R R₀`; its exit event only shrinks; `C_H` does not depend on `R`).
* `ae_condL_of`, `integral_condL`: from the closed law on the cap event to `condL`.
* **`isTestedMartOff_genProc`**: under `CapIdentPremise`, for every generator pair, the
  candidate's generator process has tested increments off the birth times: integrability from
  the a.s. bound; the tested identity from `tendsto_genProc_test` (`fddConvOff_augProc`
  twice, on the cap bridge `fddConvOff_of_isCapFddLimitAll`) at the two
  times, real and imaginary parts, and `E_{condL}[φ (pM_t − pM_a)] = pUnst / P_W(cap) → 0`.
* **`capIdentGramGen_of_large : GramPassLocalLarge → CapIdentGramGen`**, hence
  **`capIdentGram_of_large : GramPassLocalLarge → CapIdentGram`** (`capIdentGram_of_gen`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

variable {K np : ℕ}

/-!
## Removal of the stop with the large-level estimate
-/

/-- **The unstopped tested increments tend to `0`** (from `GramPassLocalLarge`). -/
theorem tendsto_pUnst_large (hloc : GramPassLocalLarge) (hTL : TransmissionLawContract)
    (hS : ComplexClosedSummed) (hT : ComplexClosedTight) (hK : ComplexKStoppedMomentMax)
    (hL : ComplexClosedLindeberg) {b E : ℝ} {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) {χ : ℝ → ℝ} (h3 : ContDiff ℝ 3 χ)
    (hcs : HasCompactSupport χ) {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ}
    (hp : IsGenPair χ b E F Λ) {a t : ℝ≥0} (hat : a ≤ t) (ha : a ∉ birthTimes s τ)
    (ht : t ∉ birthTimes s τ) {r : ℕ} (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0)
    (hu : ∀ l, u l ≤ a) (hub : ∀ l, u l ∉ birthTimes s τ)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) :
    Tendsto (fun W => pUnst χ b E s h τ m W (Vs W) F Λ i u φ a t) atTop (𝓝 0) := by
  obtain ⟨hχc, hFc, hΛc, Rχ, hR, hFv, hΛv⟩ := hp.data h3 hcs
  obtain ⟨C, hC0, hC⟩ := exists_uniform_bound (b := b) (E := E) (s := s) (τ := τ) (m := m)
    hχc hR hFc hΛc hFv hΛv t
  obtain ⟨⟨_, hb, hE1, hE2, -⟩, hs, -, -, -, hVs⟩ := id hD
  have hb1 : b < 1 := by linarith
  obtain ⟨R₀, hR₀⟩ := hloc hTL hS hT hK hL b E np τ m T s h K Vs hD χ h3 hcs F Λ hp
  set TH := max T (s + t + 1)
  have hD' := Fdd.frameDomain_mono hD (le_max_left T (s + t + 1))
  have hTH : s + t ≤ TH := (by linarith : s + t ≤ s + t + 1).trans (le_max_right _ _)
  have hfe := complexClosedFeasible_holds b E np τ m T s h K Vs hD
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B := 2 * C * ‖φ‖ + 1
  have hB : 0 < B := by positivity
  obtain ⟨R, hRt⟩ := StopTail.complexClosedStopTail_of hS hL b E np τ m TH s h K Vs hD'
    (ε / (2 * B)) (by positivity)
  have hst := hR₀ (max R R₀) (le_max_right _ _) a t hat ha ht r i u hu hub φ
  filter_upwards [hRt, hfe, hVs, Metric.tendsto_nhds.1 hst (ε / 2) (half_pos hε),
    eventually_ge_atTop 1] with W hW1 hW2 hW3 hW4 hW5
  have hV : Measurable (Vs W) :=
    hW3.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have key := norm_pUnst_sub_le hb1 hE1 hE2 hs.le hW5 hV hχc hFc hΛc hC0 hat
    (fun y hy v hv => hC _ _ y hy v hv) hW2 (max R R₀) TH hTH i u φ
  have hmono : closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i,
      closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * TH⌋₊ ∧
        max R R₀ ≤ ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re} ≤
      ENNReal.ofReal (ε / (2 * B)) := by
    refine (measure_mono fun y hy => ?_).trans hW1
    obtain ⟨hy1, i', h1, h2, h3'⟩ := hy
    exact ⟨hy1, i', h1, h2, (le_max_left _ _).trans h3'⟩
  have hmeas := ENNReal.toReal_le_of_le_ofReal (by positivity) hmono
  rw [dist_zero_right] at hW4 ⊢
  have h2 : 2 * C * ‖φ‖ * (ε / (2 * B)) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg φ]
  calc ‖pUnst χ b E s h τ m W (Vs W) F Λ i u φ a t‖ ≤
        ‖pStopSum χ b E s h τ m W (Vs W) F Λ (max R R₀) i u φ a t‖ +
          ‖pUnst χ b E s h τ m W (Vs W) F Λ i u φ a t -
            pStopSum χ b E s h τ m W (Vs W) F Λ (max R R₀) i u φ a t‖ := norm_le_insert' _ _
    _ < ε / 2 + 2 * C * ‖φ‖ * (ε / (2 * B)) := by
        refine add_lt_add_of_lt_of_le hW4 (key.trans ?_)
        exact mul_le_mul_of_nonneg_left hmeas (by positivity)
    _ ≤ ε := by linarith

/-!
## The conditioned law
-/

theorem ae_condL_of {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {s h : ℝ} {W : ℕ}
    {P : ProbedPath W np × ℝ → Prop}
    (hP : ∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W → P y) :
    ∀ᵐ y ∂Fdd.condL b E s h K W np, P y := by
  have h1 : ∀ᵐ y ∂closedLaw b W np, y ∈ Fdd.capM b E s h K W np → P y := by
    filter_upwards [hP, (Fdd.capC_ae_eq (K := K) (W := W) (np := np) hb hE1 hE2 s h).mem_iff]
      with y hy hiff hm
    exact hy (hiff.2 hm)
  have h2 : ∀ᵐ y ∂(closedLaw b W np).restrict (Fdd.capM b E s h K W np), P y :=
    (ae_restrict_iff' (Fdd.measurableSet_capM b E s h K W np)).2 h1
  unfold Fdd.condL ProbabilityTheory.cond
  exact Measure.ae_smul_measure h2 _

theorem integral_condL {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ) {W : ℕ}
    (g : ProbedPath W np × ℝ → ℂ) :
    ∫ y, g y ∂Fdd.condL b E s h K W np =
      ((growthPathLaw W b (physCapEventC b E s h K W))⁻¹).toReal •
        ∫ y, (capS b E s h K W np).indicator g y ∂closedLaw b W np := by
  unfold Fdd.condL ProbabilityTheory.cond
  rw [integral_smul_measure, ← integral_indicator (Fdd.measurableSet_capM b E s h K W np),
    Fdd.closedLaw_capM hb hE1 hE2]
  congr 1
  exact integral_congr_ae (indicator_ae_eq_of_ae_eq_set (Fdd.capC_ae_eq hb hE1 hE2 s h)).symm

/-!
## Real and imaginary parts
-/

theorem re_integral_smul {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℝ}
    {g : Ω → ℂ} (hg : Integrable (fun ω => f ω • g ω) ν) :
    (∫ ω, f ω • g ω ∂ν).re = ∫ ω, f ω * (g ω).re ∂ν := by
  have h := (Complex.reCLM.integral_comp_comm hg).symm
  simpa [Complex.smul_re] using h

theorem im_integral_smul {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℝ}
    {g : Ω → ℂ} (hg : Integrable (fun ω => f ω • g ω) ν) :
    (∫ ω, f ω • g ω ∂ν).im = ∫ ω, f ω * (g ω).im ∂ν := by
  have h := (Complex.imCLM.integral_comp_comm hg).symm
  simpa [Complex.smul_im] using h

/-- `Re`/`Im` of a tested increment are differences of real tested values. -/
theorem sel_integral_smul_sub {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℝ}
    {g1 g2 : Ω → ℂ} (h1 : Integrable (fun ω => f ω • g1 ω) ν)
    (h2 : Integrable (fun ω => f ω • g2 ω) ν) :
    (∫ ω, f ω • (g1 ω - g2 ω) ∂ν).re =
        (∫ ω, f ω * (g1 ω).re ∂ν) - ∫ ω, f ω * (g2 ω).re ∂ν ∧
      (∫ ω, f ω • (g1 ω - g2 ω) ∂ν).im =
        (∫ ω, f ω * (g1 ω).im ∂ν) - ∫ ω, f ω * (g2 ω).im ∂ν := by
  have e : (fun ω => f ω • (g1 ω - g2 ω)) = fun ω => f ω • g1 ω - f ω • g2 ω := by
    funext ω; exact smul_sub _ _ _
  rw [e, integral_sub h1 h2, Complex.sub_re, Complex.sub_im, re_integral_smul h1,
    re_integral_smul h2, im_integral_smul h1, im_integral_smul h2]
  exact ⟨rfl, rfl⟩

/-!
## The tested identities of the candidate
-/

theorem zero_notMem_birthTimes {s : ℝ} {τ : Fin np → ℝ} (hsτ : ∀ j, s < τ j) :
    (0 : ℝ≥0) ∉ birthTimes s τ := fun ⟨j, hj⟩ => by
  have := hsτ j
  simp only [NNReal.coe_zero, add_zero] at hj
  linarith

/-- **The candidate's generator processes have tested increments off the birth times.** -/
theorem isTestedMartOff_genProc (hloc : GramPassLocalLarge) (hTL : TransmissionLawContract)
    (hS : ComplexClosedSummed) (hT : ComplexClosedTight) (hK : ComplexKStoppedMomentMax)
    (hL : ComplexClosedLindeberg) {b E : ℝ} {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    {φs : ℕ → ℕ} {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
    {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}
    (hP : CapIdentPremise b E τ m T s h K Vs P μ φs Q tseq G Kc) {χ : ℝ → ℝ}
    (h3 : ContDiff ℝ 3 χ) (hcs : HasCompactSupport χ) {F : ZSt K np → ℂ}
    {Λ : GSt K np × ZSt K np → ℂ} (hp : IsGenPair χ b E F Λ) :
    IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
      (genProc χ b E s τ m G F Λ) := by
  obtain ⟨hD, hlim, hA, hne, hφ, hCLD, hfdd⟩ := hP
  obtain ⟨hQ, htm, hGm, hKm, hc, hkc⟩ := id hCLD
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, hm, -⟩, hs, hsτ, hh0, -, hVs⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  have hcapW := eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh0 hA hne
  have hfeQ := ae_feasible_all hD hφ hfdd hobs (hφ.eventually hcapW) hc
  obtain ⟨hχc, hFc, hΛc, Rχ, hR, hFv, hΛv⟩ := hp.data h3 hcs
  have h0 := zero_notMem_birthTimes hsτ
  -- joint measurability of the candidate's Gram process
  have hY : StronglyMeasurable (Function.uncurry fun u ω => G u ω - gramJ b s τ m u) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc
      fun u => (hGm u).sub stronglyMeasurable_const
  have hGs : StronglyMeasurable (Function.uncurry G) := by
    have h := hY.add ((sm_gramJ (K := K) b s τ m).comp_measurable
      (measurable_fst (α := ℝ≥0) (β := Ω')))
    convert h using 1
    funext p
    simp [Function.uncurry]
  have hMm : ∀ v, StronglyMeasurable (genProc χ b E s τ m G F Λ v) := fun v =>
    (sm_genProc (b := b) (E := E) (s := s) (τ := τ) (m := m) hGs hχc hFc hΛc).comp_measurable
      (measurable_const.prodMk measurable_id)
  have hint : ∀ v, Integrable (genProc χ b E s τ m G F Λ v) Q := fun v => by
    obtain ⟨C, hC⟩ := exists_bound_genProc (b := b) (E := E) (s := s) (τ := τ) (m := m) hfeQ hχc
      hR hFc hΛc hFv hΛv v
    exact Integrable.of_bound (hMm v).aestronglyMeasurable C (hC.mono fun ω hω => hω v le_rfl)
  refine ⟨hint, fun a t hat ha ht r i u hu hub φ => ?_⟩
  -- a tail of the subsequence with admissible frames, nonzero cap mass and feasibility
  have hevW : ∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W) ∧
      growthPathLaw W b (physCapEventC b E s h K W) ≠ 0 ∧
      (∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W → ∀ j, closeLen s W ≤ j →
        GramFeasible (srcSignature K (Fin np)) (b3ClosedGramAt b E s h τ m W j (Vs W) y)) :=
    hVs.and (hcapW.and (complexClosedFeasible_holds b E np τ m T s h K Vs hD))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hφ.eventually hevW)
  set Wn : ℕ → ℕ := fun n => φs (n + N0)
  have hWn : Tendsto Wn atTop atTop := hφ.comp (tendsto_add_atTop_nat N0)
  have hgood : ∀ n, IsTimeSFrame b E s h K (Wn n) (Vs (Wn n)) ∧
      growthPathLaw (Wn n) b (physCapEventC b E s h K (Wn n)) ≠ 0 ∧
      (∀ᵐ y ∂closedLaw b (Wn n) np, y.1.1 ∈ physCapEventC b E s h K (Wn n) →
        ∀ j, closeLen s (Wn n) ≤ j → GramFeasible (srcSignature K (Fin np))
          (b3ClosedGramAt b E s h τ m (Wn n) j (Vs (Wn n)) y)) :=
    fun n => hN0 _ (Nat.le_add_left _ _)
  have hV : ∀ n, Measurable (Vs (Wn n)) := fun n =>
    (hgood n).1.1.mono (BlockBand.Transmission.Generator.growthSigma_le (Wn n) _) le_rfl
  have hμ : ∀ n, IsProbabilityMeasure (Fdd.condL b E s h K (Wn n) np) := fun n =>
    Fdd.isProbabilityMeasure_condL hb1 hE1 hE2 (hgood n).2.1
  have hF0 := AddFun.fddConvOff_of_isCapFddLimitAll hb1 hE1 hE2 hfdd
  have hF : AddFun.FddConvOff (birthTimes s τ) (fun n => Fdd.condL b E s h K (Wn n) np)
      (fun n => b3ObsAll b E s h τ m (Wn n) (Vs (Wn n))) Q (complexObs tseq G Kc) :=
    fun ι _ i u hu ψ => (tendsto_add_atTop_iff_nat (f := fun n =>
      ∫ ω, ψ (fun l => b3ObsAll b E s h τ m (φs n) (Vs (φs n)) (i l) (u l) ω)
        ∂Fdd.condL b E s h K (φs n) np) N0).2 (hF0 ι i u hu ψ)
  have hfeN : ∀ n, ∀ᵐ y ∂Fdd.condL b E s h K (Wn n) np,
      ∀ v, GramFeasible (srcSignature K (Fin np)) (pG b E s h τ m (Wn n) (Vs (Wn n)) v y) :=
    fun n => ae_condL_of hb1 hE1 hE2 ((hgood n).2.2.mono fun y hy hcap v =>
      hy hcap _ (Nat.floor_mono (mul_le_mul_of_nonneg_left (by
        have : (0 : ℝ) ≤ v := v.2
        linarith) (Nat.cast_nonneg _))))
  have hXm : ∀ n l, Measurable (Function.uncurry (b3ObsAll b E s h τ m (Wn n) (Vs (Wn n)) l)) :=
    fun n l => AddFun.measurable_uncurry_b3ObsAll (hV n) l
  have hYm := AddFun.measurable_uncurry_complexObs hCLD
  -- the four limits
  have hlim4 : ∀ v : ℝ≥0, v ∉ birthTimes s τ → ∀ sel : ℂ → ℝ, Continuous sel →
      (∀ w, |sel w| ≤ ‖w‖) → Tendsto (fun n => ∫ y,
        φ (fun l => b3ObsAll b E s h τ m (Wn n) (Vs (Wn n)) (i l) (u l) y) *
          sel (genProc χ b E s τ m (pG b E s h τ m (Wn n) (Vs (Wn n))) F Λ v y)
            ∂Fdd.condL b E s h K (Wn n) np) atTop
        (𝓝 (∫ ω, φ (fun l => complexObs tseq G Kc (i l) (u l) ω) *
          sel (genProc χ b E s τ m G F Λ v ω) ∂Q)) :=
    fun v hv sel hsel hselb => tendsto_genProc_test h0 hμ (fun n e u y => rfl) hXm hfeN
      (fun e u ω => rfl) hYm hfeQ hc hF hχc hR hFc hΛc hFv hΛv i u hub φ hv hsel hselb
  -- integrability of the tested values
  obtain ⟨Cq, hCq⟩ := exists_bound_genProc (b := b) (E := E) (s := s) (τ := τ) (m := m) hfeQ hχc
    hR hFc hΛc hFv hΛv t
  obtain ⟨Cn, hCn0, hCn⟩ := exists_uniform_bound (b := b) (E := E) (s := s) (τ := τ) (m := m)
    hχc hR hFc hΛc hFv hΛv t
  have hφQ : Measurable fun ω => φ (fun l => complexObs tseq G Kc (i l) (u l) ω) :=
    φ.continuous.measurable.comp (Measurable.of_eval fun l => hobs (i l) (u l))
  have hiQ : ∀ v ≤ t, Integrable (fun ω => φ (fun l => complexObs tseq G Kc (i l) (u l) ω) •
      genProc χ b E s τ m G F Λ v ω) Q := fun v hv => by
    refine Integrable.of_bound (hφQ.stronglyMeasurable.smul (hMm v)).aestronglyMeasurable
      (‖φ‖ * Cq) (hCq.mono fun ω hω => ?_)
    rw [norm_smul]
    exact mul_le_mul (φ.norm_coe_le_norm _) (hω v hv) (norm_nonneg _) (norm_nonneg _)
  have hiN : ∀ n, ∀ v ≤ t, Integrable (fun y =>
      φ (fun l => b3ObsAll b E s h τ m (Wn n) (Vs (Wn n)) (i l) (u l) y) •
        genProc χ b E s τ m (pG b E s h τ m (Wn n) (Vs (Wn n))) F Λ v y)
      (Fdd.condL b E s h K (Wn n) np) := fun n v hv => by
    have hφm := measurable_pTest (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m) (hV n)
      i u φ
    have hMn := sm_pM (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m) (hV n) hχc hFc hΛc v
    refine Integrable.of_bound (hφm.stronglyMeasurable.smul hMn).aestronglyMeasurable
      (‖φ‖ * Cn) ((hfeN n).mono fun y hy => ?_)
    rw [norm_smul]
    exact mul_le_mul (φ.norm_coe_le_norm _) (hCn _ _ y hy v hv) (norm_nonneg _) (norm_nonneg _)
  -- the prelimit tested increments vanish in the limit
  have hpU := (tendsto_pUnst_large hloc hTL hS hT hK hL hD h3 hcs hp hat ha ht i u hu hub
    φ).comp hWn
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  have hcap : Tendsto (fun n => (growthPathLaw (Wn n) b (physCapEventC b E s h K (Wn n))).toReal)
      atTop (𝓝 (entranceLaw P μ s (capSet K h)).toReal) :=
    (CapCond.tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh0 K (hA K)).comp hWn
  have hpA : (entranceLaw P μ s (capSet K h)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hne (measure_ne_top _ _)).ne'
  have hD0 : Tendsto (fun n => ∫ y,
      φ (fun l => b3ObsAll b E s h τ m (Wn n) (Vs (Wn n)) (i l) (u l) y) •
        (genProc χ b E s τ m (pG b E s h τ m (Wn n) (Vs (Wn n))) F Λ t y -
          genProc χ b E s τ m (pG b E s h τ m (Wn n) (Vs (Wn n))) F Λ a y)
        ∂Fdd.condL b E s h K (Wn n) np) atTop (𝓝 0) := by
    have h1 := (hcap.inv₀ hpA).smul hpU
    rw [smul_zero] at h1
    refine h1.congr fun n => ?_
    rw [integral_condL hb1 hE1 hE2 s h, ENNReal.toReal_inv]
    rfl
  have hsplit := fun n => sel_integral_smul_sub (hiN n t le_rfl) (hiN n a hat)
  have hre : (∫ ω, φ (fun l => complexObs tseq G Kc (i l) (u l) ω) *
        (genProc χ b E s τ m G F Λ t ω).re ∂Q) -
      ∫ ω, φ (fun l => complexObs tseq G Kc (i l) (u l) ω) *
        (genProc χ b E s τ m G F Λ a ω).re ∂Q = 0 := by
    refine tendsto_nhds_unique (((hlim4 t ht _ Complex.continuous_re Complex.abs_re_le_norm).sub
      (hlim4 a ha _ Complex.continuous_re Complex.abs_re_le_norm)).congr fun n => ?_)
      ((Complex.continuous_re.tendsto 0).comp hD0)
    exact ((hsplit n).1).symm
  have him : (∫ ω, φ (fun l => complexObs tseq G Kc (i l) (u l) ω) *
        (genProc χ b E s τ m G F Λ t ω).im ∂Q) -
      ∫ ω, φ (fun l => complexObs tseq G Kc (i l) (u l) ω) *
        (genProc χ b E s τ m G F Λ a ω).im ∂Q = 0 := by
    refine tendsto_nhds_unique (((hlim4 t ht _ Complex.continuous_im Complex.abs_im_le_norm).sub
      (hlim4 a ha _ Complex.continuous_im Complex.abs_im_le_norm)).congr fun n => ?_)
      ((Complex.continuous_im.tendsto 0).comp hD0)
    exact ((hsplit n).2).symm
  have hQs := sel_integral_smul_sub (hiQ t le_rfl) (hiQ a hat)
  refine Complex.ext ?_ ?_
  · rw [hQs.1, hre, Complex.zero_re]
  · rw [hQs.2, him, Complex.zero_im]

/-!
## The generator identification
-/

/-- **`CapIdentGramGen` from the local estimate at large levels.** -/
theorem capIdentGramGen_of_large (hloc : GramPassLocalLarge) : CapIdentGramGen := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP χ h3 hcs
  exact ⟨fun e => isTestedMartOff_genProc hloc hTL hS hT hK hL hP h3 hcs (Or.inl ⟨e, rfl, rfl⟩),
    fun e e' => isTestedMartOff_genProc hloc hTL hS hT hK hL hP h3 hcs
      (Or.inr ⟨e, e', rfl, rfl⟩)⟩

/-- **`CapIdentGram` from the local estimate at large levels** (`capIdentGram_of_gen`). -/
theorem capIdentGram_of_large (hloc : GramPassLocalLarge) : CapIdentGram :=
  capIdentGram_of_gen (capIdentGramGen_of_large hloc)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
