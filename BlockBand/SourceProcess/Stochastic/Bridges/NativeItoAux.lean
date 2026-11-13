module
public import BlockBand.SourceProcess.Stochastic.Ito
public import BlockBand.SourceProcess.Stochastic.Integral.BracketMartingale
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.Pathwise
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Itô processes as semimartingales: martingale transfer and coordinates (bridge 3b)

Sample space `Ω = DriverSample S κ`, law `P = driverLaw μ`, raw filtration
`F = commonWienerFiltration S κ`, null augmentation `G = driverAugmented μ = F_t ∨ N`.

* `martingale_driverAugmented_of_raw`: a raw `F`-martingale is a `G`-martingale under `P`
  (augmented events are raw events up to `P`-null sets, `exists_raw_ae_eq`).
* `hasMartingaleModification_of_raw`: a real process which, on every horizon `T`, agrees a.s.
  at every time `u ≤ T` with some raw `F`-martingale has a `G`-martingale modification.
* `stoppedProcess_smCompensated_ae_eq`: for an Itô process in `Fin d → ℝ`, an augmented
  stopping time `τ` whose stopped coordinate integrands are integrands, and `u ≤ T`,
  the stopped compensated coordinate `(Y^i − Y^i_0 − ∫ b^i)_{u∧τ}` is a.s. the continuous raw
  martingale `nativeAdaptedLimit` of the stopped integrand `σ^i 1{s ≤ τ}` (horizon `T`).
* `stoppedProcess_bracket_ae_eq`: the stopped product `N^i N^j − ∫ ∑_a σ_a^i σ_a^j` agrees a.s.
  at `u ≤ T` with the raw bracket martingale of `bracket_martingale`.
-/

namespace BlockBand.SourceProcess.Stochastic.Bridges
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]

/-- A raw-filtration martingale is a martingale for the null-augmented filtration
`F_t ∨ N` (measure `driverLaw μ`). -/
theorem martingale_driverAugmented_of_raw {M : ℝ≥0 → DriverSample S κ → ℝ}
    (hM : Martingale M (commonWienerFiltration S κ) (driverLaw (κ := κ) μ)) :
    Martingale M (driverAugmented (κ := κ) μ) (driverLaw (κ := κ) μ) := by
  have hm (t : ℝ≥0) : StronglyMeasurable[driverAugmented (κ := κ) μ t] (M t) :=
    (hM.stronglyMeasurable t).mono (le_augmentedFiltration _ _ t)
  refine ⟨hm, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((driverAugmented (κ := κ) μ).le s)
    (hM.integrable t) (fun _ _ _ => (hM.integrable s).integrableOn) (fun A hA _ => ?_)
    (hm s).aestronglyMeasurable).symm
  obtain ⟨B, hB, hAB⟩ := exists_raw_ae_eq μ hA
  rw [setIntegral_congr_set hAB, setIntegral_congr_set hAB]
  exact hM.setIntegral_eq hst hB

/-- **Raw-to-augmented modification.** If on every horizon `T` the real process `Y` agrees
a.s. at each time `u ≤ T` with a raw `F`-martingale, then `Y` has a martingale modification
for the augmented filtration `F_t ∨ N` under `driverLaw μ`. -/
theorem hasMartingaleModification_of_raw {Y : ℝ≥0 → DriverSample S κ → ℝ}
    (hY : ∀ T : ℝ≥0, ∃ N : ℝ≥0 → DriverSample S κ → ℝ,
      Martingale N (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) ∧
      ∀ u ≤ T, Y u =ᵐ[driverLaw (κ := κ) μ] N u) :
    HasMartingaleModification (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ) Y := by
  choose N hN hNY using hY
  refine exists_martingale_modification (fun t => ?_) (fun t => ?_) ?_
  · exact ((hN t).integrable t).congr (hNY t t le_rfl).symm
  · exact ⟨N t t, ((hN t).stronglyMeasurable t).mono (le_augmentedFiltration _ _ t),
      hNY t t le_rfl⟩
  · intro s t hst A hA
    obtain ⟨B, hB, hAB⟩ := exists_raw_ae_eq μ hA
    rw [setIntegral_congr_set hAB, setIntegral_congr_set hAB,
      integral_congr_ae (ae_restrict_of_ae (hNY t t le_rfl)),
      integral_congr_ae (ae_restrict_of_ae (hNY t s hst))]
    exact ((hN t).setIntegral_eq hst hB).symm

/-- Integrals of equal integrands coincide (proof irrelevance). -/
theorem nativeIntegralOf_congr {T : ℝ≥0} {g g' : κ → ℝ × DriverSample S κ → ℝ} (h : g = g')
    (hg : NativeIntegrand μ T g) (hg' : NativeIntegrand μ T g') :
    nativeIntegralOf hg = nativeIntegralOf hg' := by
  subst h
  rfl

omit [MeasurableSpace S] [Fintype κ] in
/-- Stopping a `τ`-stopped integrand at the constant `u ∧ ⊤ = u` stops it at `u ∧ τ`. -/
theorem stopIntegrand_min_top (u : ℝ≥0) (τ : DriverSample S κ → WithTop ℝ≥0)
    (g : κ → ℝ × DriverSample S κ → ℝ) :
    stopIntegrand (fun _ => min (u : WithTop ℝ≥0) ⊤) (stopIntegrand τ g) =
      stopIntegrand (fun x => min (u : WithTop ℝ≥0) (τ x)) g := by
  funext a p
  simp only [stopIntegrand, min_top_right, le_min_iff]
  split_ifs <;> simp_all

omit [IsProbabilityMeasure μ] in
/-- The constant time `⊤` is an augmented stopping time. -/
theorem isStoppingTime_top_aug :
    IsStoppingTime (driverAugmented (κ := κ) μ) (fun _ : DriverSample S κ => (⊤ : WithTop ℝ≥0)) :=
  fun i => by
    simp only [top_le_iff, WithTop.coe_ne_top, Set.ofPred_false]
    exact @MeasurableSet.empty _ (driverAugmented (κ := κ) μ i)

section Coordinates
variable {d : ℕ}

/-- The coordinate functional `v ↦ v i` on `Fin d → ℝ`. -/
abbrev coordFun (i : Fin d) : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

/-- **Drift clause, one horizon.** For an Itô process in `Fin d → ℝ` and an augmented
stopping time `τ` whose stopped `i`-th integrand `σ^i 1{s ≤ τ}` is an integrand on
`(0,T]`, the stopped compensated coordinate `(Y^i − Y^i_0 − ∫_0^· b^i)_{u∧τ}` equals a.s. the
continuous raw martingale `nativeAdaptedLimit` of that integrand at every `u ≤ T`. -/
theorem stoppedProcess_smCompensated_ae_eq {X b : ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ} (h : IsNativeItoProcess μ X b σ)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (i : Fin d) {T : ℝ≥0}
    (hG : NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand (coordFun i) σ)))
    {u : ℝ≥0} (hu : u ≤ T) :
    stoppedProcess (smCompensated X b i) τ u =ᵐ[driverLaw (κ := κ) μ]
      nativeAdaptedLimit μ T hG.family u := by
  obtain ⟨hs, hid⟩ := h.identity (coordFun i) τ hτ T hG u hu
  obtain ⟨hs', hlim⟩ := nativeAdaptedLimit_stopped hG (isStoppingTime_top_aug (μ := μ)) u
  have heq := nativeIntegralOf_congr (stopIntegrand_min_top u τ _) hs' hs
  filter_upwards [hid, hlim, h.drift_integrable] with x h1 h2 h3
  have htop : stoppedProcess (nativeAdaptedLimit μ T hG.family) (fun _ => ⊤) u x =
      nativeAdaptedLimit μ T hG.family u x := by
    rw [stoppedProcess_eq_stopTime, stopTime_top]
  rw [← htop, h2, heq, ← h1]
  have hd : stoppedDrift τ b u x = ∫ v in Ioc (0 : ℝ) (stopTime (τ x) u), b v.toNNReal x :=
    setIntegral_switch (fun v => b v.toNNReal x) (τ x) u
  simp only [stoppedProcess_eq_stopTime, smCompensated, hd,
    ← ContinuousLinearMap.integral_comp_comm (coordFun i) (h3 _)]
  rfl

/-- **Bracket clause, one horizon.** If `N` is the raw bracket martingale of the stopped
coordinate integrands `σ^i 1{s ≤ τ}`, `σ^j 1{s ≤ τ}` on `(0,T]` (`bracket_martingale`), then
the stopped compensated product `(N^i N^j − ∫_0^· ∑_a σ_a^i σ_a^j)_{u∧τ}` equals `N_u` a.s.
for every `u ≤ T`. -/
theorem stoppedProcess_bracket_ae_eq {X b : ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ} (h : IsNativeItoProcess μ X b σ)
    {τ : DriverSample S κ → WithTop ℝ≥0} (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (i j : Fin d) {T : ℝ≥0}
    (hGi : NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand (coordFun i) σ)))
    (hGj : NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand (coordFun j) σ)))
    {N : ℝ≥0 → DriverSample S κ → ℝ}
    (hNe : ∀ t, N t =ᵐ[driverLaw (κ := κ) μ] fun x =>
      nativeAdaptedLimit μ T hGi.family t x * nativeAdaptedLimit μ T hGj.family t x -
        bracketDrift T (stopIntegrand τ (functionalIntegrand (coordFun i) σ))
          (stopIntegrand τ (functionalIntegrand (coordFun j) σ)) t x)
    {u : ℝ≥0} (hu : u ≤ T) :
    stoppedProcess (fun t ω => smCompensated X b i t ω * smCompensated X b j t ω -
        ∫ s in Ioc (0 : ℝ) t, ∑ a, σ a s.toNNReal ω i * σ a s.toNNReal ω j) τ u
      =ᵐ[driverLaw (κ := κ) μ] N u := by
  filter_upwards [hNe u, stoppedProcess_smCompensated_ae_eq h hτ i hGi hu,
    stoppedProcess_smCompensated_ae_eq h hτ j hGj hu] with x h1 h2 h3
  rw [h1, ← h2, ← h3, bracketDrift_stopIntegrand, min_eq_left hu,
    setIntegral_switch (fun s => ∑ c, functionalIntegrand (coordFun i) σ c (s, x) *
      functionalIntegrand (coordFun j) σ c (s, x)) (τ x) u]
  rfl

end Coordinates

end BlockBand.SourceProcess.Stochastic.Bridges
