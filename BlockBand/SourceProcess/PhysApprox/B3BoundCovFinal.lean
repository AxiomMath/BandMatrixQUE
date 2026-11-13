module

public import BlockBand.SourceProcess.PhysApprox.B3BoundCovMeanK
public import BlockBand.SourceProcess.PhysApprox.B3BoundJetDecay
public import BlockBand.SourceProcess.PhysApprox.B3CovRepCond
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormJointCov

/-!
# `ComplexClosedSummed` from jet and decay inputs at orders `p ≤ 4`

Assembly of the covariance side with the bounded jet and decay statements `ClosedErrLpLe`,
`B3ClosedContrDecayLe`:

* `covErrMoments2_of_errLpLe : ClosedErrLpLe P e → 4 ≤ P → CovErrMoments2 e` (the order `p = 4`),
  hence `covErrMoments2_b3CovErr_of_jets` through `closedErrLpLe_of_jets`;
* `b3_stepBound_of_layer_decay2Le`, `kStepDrift_of_decay2Le`, `gramSumStepDrift_of_decay2Le`: the
  restated drift bounds with the decay `B3ClosedContrDecayLe 4` (used at `p = 2`);
* **`complexClosedSummed_of_near2_le`**: the same with the mixed pairs from
  `covLayerHypKG_of_near` (estimates `FreshDeltaQuadCov`, `B3ClosedChainNearPin`; the chain
  estimate is its first component, `b3ClosedChainPin_of_near`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedSum
open scoped ENNReal

/-!
## The moment at `p = 4` from the bounded jets
-/

/-- **`ClosedErrLpLe P e ⇒ CovErrMoments2 e`** for `P ≥ 4` (the order `p = 4`). -/
theorem covErrMoments2_of_errLpLe {e : CovField} {P : ℝ} (h : ClosedErrLpLe P e) (hP : 4 ≤ P) :
    CovErrMoments2 e := by
  intro b E np τ m T s h' K Vs hFD R
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R 4 (by norm_num) hP
  refine ⟨C, hC, hev.mono fun W hW j hj => ?_⟩
  have := hW j hj
  rwa [ENNReal.ofReal_ofNat] at this

/-- **`CovErrMoments2 b3CovErr` from the three closed jet statements at the orders `≤ P`.** -/
theorem covErrMoments2_b3CovErr_of_jets {P : ℝ} (h0 : ClosedJet0LpLe P) (h1 : ClosedJet1LpLe P)
    (hg : ClosedCondLpLe P) (hP : 4 ≤ P) : CovErrMoments2 b3CovErr :=
  covErrMoments2_of_errLpLe (closedErrLpLe_of_jets h0 h1 hg) hP

/-!
## The restated drift bounds with the decay at orders `≤ 4`
-/

/-- The per-step `SummedStep` bound from the restated layer structure and the decay at `p = 2`. -/
theorem b3_stepBound_of_layer_decay2Le (hD : B3ClosedContrDecayLe 4) {b E : ℝ} {np : ℕ}
    {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ) (P : CIdx K np → Prop)
    (hL : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      B3LayerMeanAt2 b E s h τ m R W j (Vs W) C c) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ c, P c →
      genDriftStep b E s h τ m R W j (Vs W) c ≤
        ENNReal.ofReal (C / W * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) := by
  obtain ⟨CL, hCL, hevL⟩ := hL
  obtain ⟨C₂, ρ, hC₂, hρ0, hρ1, hevD⟩ :=
    hD b E np τ m T s h K Vs hF R 2 (by norm_num) (by norm_num)
  set N : ℝ := (Fintype.card (ContrIdx K np) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨CL * (CL * N * C₂ + CL ^ 2 + 1), ρ, by positivity, hρ0, hρ1, ?_⟩
  filter_upwards [hevL, hevD, eventually_ge_atTop 1] with W hWL hWD hW1 j hj c hc
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hr : 0 ≤ genStepRate ρ s τ W j := genStepRate_nonneg hρ0 s τ W j
  have hQ : ∀ x : ContrIdx K np, eLpNorm (b3ContrAlive b E s h τ m R W j (Vs W) x) 2
      (closedLaw b W np) ≤ ENNReal.ofReal (C₂ * (genStepRate ρ s τ W j + 1 / Real.sqrt W)) :=
    fun x => by
      have := hWD j hj'.1.1 hj'.1.2.le x.1 x.2.1 x.2.2
      rwa [ENNReal.ofReal_ofNat] at this
  refine (b3_driftStep_le_of_layer2 b E s h τ m R j hCL (by positivity) (hWL j hj c hc)
    hQ).trans (ENNReal.ofReal_le_ofReal ?_)
  exact decay_step_arith2 hCL hr hW1

/-- **`KStepDrift`** from `B3ClosedContrDecayLe 4` and the restated `𝒦` mean structure. -/
theorem kStepDrift_of_decay2Le (hD : B3ClosedContrDecayLe 4) (hK : B3ClosedKLayerMean2) :
    KStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decay2Le hD hF R
    (fun c => ∃ ij : Fin np × Fin np, c = Sum.inr ij)
    (by
      obtain ⟨C, hC, hev⟩ := hK b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨ij, hij⟩ => hij ▸ hW j hj ij⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj ij => hW j hj _ ⟨ij, rfl⟩⟩

/-- **`GramSumStepDrift`** from `B3ClosedContrDecayLe 4` and the restated Gram mean structure. -/
theorem gramSumStepDrift_of_decay2Le (hD : B3ClosedContrDecayLe 4)
    (hG : B3ClosedGramLayerMean2) : GramSumStepDrift := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, ρ, hC, hρ0, hρ1, hev⟩ := b3_stepBound_of_layer_decay2Le hD hF R
    (fun c => ∃ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np), c = Sum.inl e)
    (by
      obtain ⟨C, hC, hev⟩ := hG b E np τ m T s h K Vs hF R
      exact ⟨C, hC, hev.mono fun W hW j hj c ⟨e, he⟩ => he ▸ hW j hj e⟩)
  exact ⟨C, ρ, hC, hρ0, hρ1, hev.mono fun W hW j hj e => hW j hj _ ⟨e, rfl⟩⟩

/-!
## `ComplexClosedSummed` at orders `≤ 4`
-/

/-- **`ComplexClosedSummed` through the closed chain, every moment of order `≤ 4`.** -/
theorem complexClosedSummed_of_chain2_le (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hB : GenReqBirth)
    (hCh : B3ClosedChainPin) (h0 : ClosedJet0LpLe 4) (h1 : ClosedJet1LpLe 4)
    (hKG : CovLayerHypKG b3CovErr b3CovZ) (hD : B3ClosedContrDecayLe 4) :
    ComplexClosedSummed := by
  have hE : CovErrMoments2 b3CovErr := covErrMoments2_b3CovErr_of_jets h0 h1
    (closedCondLpLe_of (closedCondLp_of_chain hCh) 4) le_rfl
  exact complexClosedSummed_of_layer2
    (gramSumStepDrift_of_decay2Le hD (b3ClosedGramLayerMean2_of_chain hGA hLp hP hCh hE)) hB
    (kStepDrift_of_decay2Le hD (b3ClosedKLayerMean2_of_jet hGA hLp h0 (by norm_num)))
    (covLayerHyp2_of_chain hGA hLp hP hCh (covLayerHypKG2_of_bdd hKG covErrBdd_b3CovErr))
    (conjLayerHyp2_holds hGA hLp hP) hE (covDecayHyp_b3CovZ_of_le hD)

/-- The chain estimate is the first component of the near-rows chain estimate. -/
theorem b3ClosedChainPin_of_near (hN : B3ClosedChainNearPin) : B3ClosedChainPin := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, hC, hev⟩ := hN b E np τ m T s h K Vs hF R
  exact ⟨C, hC, hev.mono fun W hW j hj => (hW j hj).imp fun _ hX => hX.1⟩

/-- **`ComplexClosedSummed` at orders `≤ 4`, with the mixed pairs from
`covLayerHypKG_of_near`.** -/
theorem complexClosedSummed_of_near2_le (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hB : GenReqBirth)
    (hQ : ClosedForm.FreshDeltaQuadCov) (hN : B3ClosedChainNearPin) (h0 : ClosedJet0LpLe 4)
    (h1 : ClosedJet1LpLe 4) (hD : B3ClosedContrDecayLe 4) : ComplexClosedSummed :=
  complexClosedSummed_of_chain2_le hGA hLp hP hB (b3ClosedChainPin_of_near hN) h0 h1
    (covLayerHypKG_of_near hGA hLp hP hQ hN) hD

end BlockBand.SourceProcess.PhysApprox.B3
