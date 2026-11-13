module

public import BlockBand.Transmission.DualBoundary.UniqueSplit

/-!
# Uniqueness at a boundary start: the conditional post-`s` law as a coupled lift

Setting: a one-pair boundary realization `h` on `(Ω, P, 𝓖)` (`Ω : Type`), a deterministic
`s > 0`, `A = postSet(s)`; `W = (X_s 0, Y_s 0)` (`readW`); on `LΩ (ℝ² × ℝ²)` the coupled starts
`cStart₁/₂`.
* `liftSecPt z = σ(z)`, continuous at every `z` with `z 0 + z 1 ≠ 0`; `secStart = σ` on `𝒞₁`.
* `readW_mem`, `readW_eq`: on `A`, `W ∈ 𝒞₁` and `W = Z̄_s`; `map_readW_compl`: the law
  `μ = (P[|A]).map W` is carried by `𝒞₁`.
* **`map_readW_le`**: `μ(‖σ̃(z) − σ₀‖ ≥ ε) ≤ 2 P(‖σ(Z̄_s) − σ₀‖ ≥ ε)` when `P(A) ≥ 1/2`
  (`σ̃ = secStart`); `LP_cStart₁/₂`: the coupled starts have marginals `μ₁`, `μ₂`.
* **`integral_cond_eq_lift`**: `E[g(Z̄_{s+·}|_I) | A] = E_{LP} g(liftZbar F|_I)` for every lifted
  family `F` whose projected start has law `μ` (Markov property and `map_zbar_post_eq_lift`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.DualLift BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

/-- The section `σ(z) = liftSection (z 0) (z 1)` (no chamber correction). -/
def liftSecPt (z : Fin 2 → ℝ) : Fin 6 → ℝ := liftSection (z 0) (z 1)

theorem measurable_liftSecPt : Measurable liftSecPt := measurable_liftSection_pt

theorem secStart_of_mem {z : Fin 2 → ℝ} (hz : z ∈ flatChamber 1) : secStart z = liftSecPt z := by
  simp [secStart, toChamber, hz, liftSecPt]

theorem continuousAt_liftSecPt {z : Fin 2 → ℝ} (hz : z 0 + z 1 ≠ 0) :
    ContinuousAt liftSecPt z := by
  refine continuousAt_pi.2 fun i => ?_
  have h0 : Continuous fun z : Fin 2 → ℝ => z 0 := continuous_apply 0
  have h1 : Continuous fun z : Fin 2 → ℝ => z 1 := continuous_apply 1
  fin_cases i
  · exact (Real.continuous_sqrt.comp h0).continuousAt
  · exact continuousAt_const
  · exact (continuous_const.mul (Real.continuous_sqrt.comp
      (h1.mul (continuous_const.sub h1)))).continuousAt
  · exact continuousAt_const
  · exact (continuous_const.sub (continuous_const.mul h1)).continuousAt
  · exact continuousAt_const.div (h0.add h1).continuousAt hz

/-- The coordinates `(X_s 0, Y_s 0)`. -/
def readW {Ω : Type*} (X Y : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ≥0) (ω : Ω) : Fin 2 → ℝ :=
  ![X s ω 0, Y s ω 0]

section Real

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {s : ℝ≥0}

theorem measurable_readW (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (s : ℝ≥0) :
    Measurable (readW X Y s) := by
  have hX := ((h.adapted s).2.1.mono (𝓖.le s) le_rfl)
  have hY := ((h.adapted s).2.2.mono (𝓖.le s) le_rfl)
  have hX0 : Measurable fun ω => X s ω 0 := (measurable_pi_apply 0).comp hX
  have hY0 : Measurable fun ω => Y s ω 0 := (measurable_pi_apply 0).comp hY
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact hX0
  · exact hY0

theorem readW_eq {ω : Ω} (hω : ω ∈ postSet P N X Y s) : readW X Y s ω = zbarTr N X Y ω s := by
  rw [zbarTr_apply, hω.2]
  funext i; fin_cases i <;> simp [readW, truncDualCoord]

theorem readW_mem (hs : 0 < s) {ω : Ω} (hω : ω ∈ postSet P N X Y s) :
    readW X Y s ω ∈ flatChamber 1 := by
  obtain ⟨-, hP⟩ := good_of_notMem_badSet hω.1
  obtain ⟨a, b, c⟩ := chamber_one hP hs hω.2
  exact DualEntrance.mem_flatChamber_one (by simpa [readW] using a) (by simpa [readW] using b)
    (by simpa [readW] using c)

theorem measurableSet_postSet (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (s : ℝ≥0) :
    MeasurableSet (postSet P N X Y s) :=
  (augmentedFiltration 𝓖 P).le s _ (measurableSet_postSet_aug h s)

/-- The conditional law of `W` is carried by `𝒞₁`. -/
theorem map_readW_compl (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hs : 0 < s) :
    ((P[|postSet P N X Y s]).map (readW X Y s)) (flatChamber 1)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_readW h s) (isOpen_flatChamber 1).measurableSet.compl,
    cond_apply (measurableSet_postSet h s)]
  have : postSet P N X Y s ∩ readW X Y s ⁻¹' (flatChamber 1)ᶜ = ∅ := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and, not_not]
    exact fun hω => readW_mem hs hω
  rw [this, measure_empty, mul_zero]

/-- **The conditional start law puts small mass far from `σ₀`.** -/
theorem map_readW_le (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hs : 0 < s)
    (hA : 2⁻¹ ≤ P (postSet P N X Y s)) (σ₀ : Fin 6 → ℝ) (ε : ℝ) :
    ((P[|postSet P N X Y s]).map (readW X Y s)) {z | ε ≤ ‖secStart z - σ₀‖} ≤
      2 * P {ω | ε ≤ dist (liftSecPt (zbarTr N X Y ω s)) σ₀} := by
  have hE : MeasurableSet {z : Fin 2 → ℝ | ε ≤ ‖secStart z - σ₀‖} :=
    measurableSet_le measurable_const (measurable_secStart.sub_const σ₀).norm
  rw [Measure.map_apply (measurable_readW h s) hE, cond_apply (measurableSet_postSet h s)]
  have hinv : (P (postSet P N X Y s))⁻¹ ≤ 2 := ENNReal.inv_le_iff_inv_le.2 hA
  refine mul_le_mul' hinv (measure_mono fun ω hω => ?_)
  obtain ⟨hωA, hωE⟩ := hω
  change ε ≤ ‖secStart (readW X Y s ω) - σ₀‖ at hωE
  change ε ≤ dist (liftSecPt (zbarTr N X Y ω s)) σ₀
  rw [secStart_of_mem (readW_mem hs hωA), readW_eq hωA] at hωE
  rwa [dist_eq_norm]

end Real

theorem LP_cStart₁ {μ₁ μ₂ : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (σ₀ : Fin 6 → ℝ) (ε : ℝ) :
    LP (μ₁.prod μ₂) {ω | ε ≤ ‖cStart₁ ω - σ₀‖} = μ₁ {z | ε ≤ ‖secStart z - σ₀‖} := by
  have hE : MeasurableSet {z : Fin 2 → ℝ | ε ≤ ‖secStart z - σ₀‖} :=
    measurableSet_le measurable_const (measurable_secStart.sub_const σ₀).norm
  have e : {ω : LΩ CS | ε ≤ ‖cStart₁ ω - σ₀‖} =
      (fun ω : LΩ CS => ω.1.1) ⁻¹' {z | ε ≤ ‖secStart z - σ₀‖} := rfl
  rw [e, ← Measure.map_apply (f := fun ω : LΩ CS => ω.1.1) (measurable_fst.comp measurable_fst) hE]
  have e2 : (fun ω : LΩ CS => ω.1.1) = Prod.fst ∘ fun ω : LΩ CS => ω.1 := rfl
  rw [e2, ← Measure.map_map measurable_fst measurable_fst, map_fst_LP, Measure.map_fst_prod]
  simp

theorem LP_cStart₂ {μ₁ μ₂ : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (σ₀ : Fin 6 → ℝ) (ε : ℝ) :
    LP (μ₁.prod μ₂) {ω | ε ≤ ‖cStart₂ ω - σ₀‖} = μ₂ {z | ε ≤ ‖secStart z - σ₀‖} := by
  have hE : MeasurableSet {z : Fin 2 → ℝ | ε ≤ ‖secStart z - σ₀‖} :=
    measurableSet_le measurable_const (measurable_secStart.sub_const σ₀).norm
  have e : {ω : LΩ CS | ε ≤ ‖cStart₂ ω - σ₀‖} =
      (fun ω : LΩ CS => ω.1.2) ⁻¹' {z | ε ≤ ‖secStart z - σ₀‖} := rfl
  rw [e, ← Measure.map_apply (f := fun ω : LΩ CS => ω.1.2) (measurable_snd.comp measurable_fst) hE]
  have e2 : (fun ω : LΩ CS => ω.1.2) = Prod.snd ∘ fun ω : LΩ CS => ω.1 := rfl
  rw [e2, ← Measure.map_map measurable_snd measurable_fst, map_fst_LP, Measure.map_snd_prod]
  simp

theorem measurable_liftZbarPath {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S}
    [IsProbabilityMeasure μ] {ξ : LΩ S → Fin 6 → ℝ} (F : DualLift.LiftFamily μ D0 ξ)
    (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) :
    Measurable fun ω u => DualFeller.liftZbar F u ω := by
  refine measurable_pi_iff.2 fun u => ?_
  have hN := (F.measurable_N₂ hD0 hξ u).mono ((L𝓖 μ).le u) le_rfl
  have hZ := (F.measurable_Z₂ hD0 hξ u).mono ((L𝓖 μ).le u) le_rfl
  unfold DualFeller.liftZbar
  exact Measurable.ite (hN (measurableSet_singleton 1)) hZ measurable_const

/-- **The conditional post-`s` test is a lift test.** -/
theorem integral_cond_eq_lift {D0 : ℝ} (hD0 : 0 < D0) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {x y : ℝ}
    {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : P (postSet P N X Y s) ≠ 0)
    {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
    {ξ : LΩ S → Fin 6 → ℝ} (hξ : IsLiftStart μ ξ) (hin : ∀ ω, liftProj (ξ ω) ∈ flatChamber 1)
    (hlaw : (LP μ).map (fun ω => liftProj (ξ ω)) =
      (P[|postSet P N X Y s]).map (readW X Y s))
    (F : DualLift.LiftFamily μ D0 ξ) (I : Finset ℝ≥0) {g : (I → Fin 2 → ℝ) → ℝ}
    (hg : Measurable g) :
    ∫ ω, g (I.restrict (shiftZ N X Y s ω)) ∂P[|postSet P N X Y s] =
      ∫ ω, g (I.restrict (fun u => DualFeller.liftZbar F u ω)) ∂LP μ := by
  have := h.prob
  have hpost := markov_at h hs (measurableSet_postSet_aug h s) subset_rfl hA0
  have hm1 : Measurable fun ω =>
      zbarPath (dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω) :=
    measurable_zbarPath.comp hpost.measurable_dualState
  have hG : Measurable fun γ : ℝ≥0 → Fin 2 → ℝ => g (I.restrict γ) :=
    hg.comp (Finset.measurable_restrict I)
  have hae := (cond_absolutelyContinuous (μ := P) (s := postSet P N X Y s)).ae_le
    (ae_zbarPath_post h s)
  calc ∫ ω, g (I.restrict (shiftZ N X Y s ω)) ∂P[|postSet P N X Y s]
      = ∫ ω, g (I.restrict (zbarPath (dualState (postN P N X Y s) (postC P N X Y s X)
          (postC P N X Y s Y) ω))) ∂P[|postSet P N X Y s] := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with ω hω
        rw [hω]
    _ = ∫ γ, g (I.restrict γ) ∂((P[|postSet P N X Y s]).map fun ω =>
          zbarPath (dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω)) :=
        (integral_map hm1.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ γ, g (I.restrict γ) ∂((LP μ).map fun ω u => DualFeller.liftZbar F u ω) := by
        rw [map_zbar_post_eq_lift hD0 h hs hA0 hξ hin hlaw F]
    _ = _ := integral_map (measurable_liftZbarPath F hD0 hξ).aemeasurable hG.aestronglyMeasurable

end BlockBand.Transmission.DualBoundary
