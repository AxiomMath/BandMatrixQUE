module

public import BlockBand.SourceProcess.PhysApprox.B3LimObs
public import BlockBand.SourceProcess.PhysApprox.B3CurMain
public import BlockBand.SourceProcess.PhysApprox.B3Bridge

/-!
# The limit passage reduced to `ComplexCapFdd` and `ComplexCapIdent`

* `rebuild`: the source data `(𝒦, M_pr, B_pr, (M𝖣M)_pr)` from the coordinates `CIdx`;
  `continuous_rebuild`, `rebuild_cEntry`.
* **`ae_closedSourceData_eq`** (deterministic algebra, a.s.): on the cap event, at the final
  length `⌊WT⌋`, the closed source data equal `modelSourceData` of the closed process
  (`closedSourceData_eq_model` for coordinates 0–2, `closedSourceData_three_eq` with the almost-sure
  hypotheses of `complexClosedCurrent_holds` for coordinate 3).
* **`tendsto_condClosed_of_fdd`** (the final value): along a conditioned fdd limit, the
  conditioned closed expectations converge to the value of the candidate at `T − s`.
* `chooseFrame`: an admissible time-`s` frame from `ExistsTimeSFrame`.
* **`complexCapSubseq_of`**: `ExistsTimeSFrame → ComplexCapFdd → ComplexCapIdent →
  ComplexCapSubseq`.
* `TargetCapFdd`, `TargetCapIdent`: the two propositions from the hypotheses of `TargetCapCond'`
  (and `ComplexClosedFeasible` for the identification).
* **`targetCapCond'_of_targets`**: `TargetCapFdd → TargetCapIdent → ComplexClosedFeasible →
  TargetCapCond'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-!
## Source data from the coordinates
-/

/-- The source data `(𝒦, M_pr, B_pr, (M𝖣M)_pr)` from the coordinates `CIdx`. -/
def rebuild {K np : ℕ} (x : CIdx K np → ℂ) : SourceData np :=
  modelSourceData (srcSignature K (Fin np)) (Matrix.of fun i j => x (Sum.inr (i, j)))
    (Matrix.of fun k l => x (Sum.inl (0, k, l)), Matrix.of fun k l => x (Sum.inl (1, k, l)))

theorem continuous_rebuild {K np : ℕ} : Continuous (rebuild (K := K) (np := np)) := by
  have hK : Continuous fun x : CIdx K np → ℂ =>
      (Matrix.of fun i j => x (Sum.inr (i, j)) : Matrix (Fin np) (Fin np) ℂ) :=
    continuous_matrix fun _ _ => continuous_apply _
  have hM : Continuous fun x : CIdx K np → ℂ =>
      (Matrix.of fun k l => x (Sum.inl (0, k, l)) :
        Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) :=
    continuous_matrix fun _ _ => continuous_apply _
  have hB : Continuous fun x : CIdx K np → ℂ =>
      (Matrix.of fun k l => x (Sum.inl (1, k, l)) :
        Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) :=
    continuous_matrix fun _ _ => continuous_apply _
  have hpb : ∀ {f : (CIdx K np → ℂ) → Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ},
      Continuous f → Continuous fun x => probeBlock (f x) := fun hf =>
    continuous_matrix fun _ _ => hf.matrix_elem _ _
  exact hK.matrixVecCons ((hpb hM).matrixVecCons ((hpb hB).matrixVecCons
    ((hpb ((hM.matrix_mul continuous_const).matrix_mul hM)).matrixVecCons continuous_const)))

theorem rebuild_cEntry {K np : ℕ} (G : GramState (SrcCol K (Fin np)))
    (Kc : Matrix (Fin np) (Fin np) ℂ) :
    rebuild (fun c => cEntry c G Kc) = modelSourceData (srcSignature K (Fin np)) Kc G := by
  have hG : (Matrix.of fun k l => cEntry (Sum.inl (0, k, l) : CIdx K np) G Kc,
      Matrix.of fun k l => cEntry (Sum.inl (1, k, l) : CIdx K np) G Kc) = G :=
    Prod.ext (by ext k l; simp [cEntry, gramEntry]) (by ext k l; simp [cEntry, gramEntry])
  have hK : (Matrix.of fun i j => cEntry (Sum.inr (i, j) : CIdx K np) G Kc) = Kc := by
    ext i j; simp [cEntry]
  rw [rebuild, hG, hK]

/-- The embedding of the coordinates into the observables of `complexObs`. -/
def cToL {K np : ℕ} : CIdx K np → LIdx K np
  | Sum.inl e => Sum.inl e
  | Sum.inr ij => Sum.inr (Sum.inr ij)

theorem complexObs_cToL {Ω' : Type*} {K np : ℕ} (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) (u : ℝ≥0) (ω : Ω') (c : CIdx K np) :
    complexObs tseq G Kc (cToL c) u ω = cEntry c (G u ω) (Kc u ω) := by
  rcases c with e | ij <;> rfl

theorem b3Obs_cToL (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (u : ℝ≥0)
    (y : ProbedPath W np × ℝ) (c : CIdx K np) :
    b3Obs b E s T h τ m W Vs (cToL c) u y =
      cEntry c (b3ClosedGramAt b E s h τ m W (limLen s T W u) Vs y)
        (b3ClosedKAt b E s h τ m W (limLen s T W u) y) := by
  rcases c with e | ij <;> rfl

theorem limLen_final {s T : ℝ} (hsT : s < T) (W : ℕ) :
    limLen s T W (T - s).toNNReal = ⌊(W : ℝ) * T⌋₊ := by
  rw [limLen, Real.coe_toNNReal _ (sub_nonneg.2 hsT.le), add_sub_cancel, max_eq_right hsT.le,
    min_self]

/-!
## The final value
-/

/-- **On the cap event the closed source data are the model source data of the closed process
at `⌊WT⌋`**, almost surely, for every probe sample and phase (`s < T`, admissible frame,
`1 ≤ n_s`). -/
theorem ae_closedSourceData_eq {b E s T h : ℝ} {np K W : ℕ} (τ m : Fin np → ℝ)
    (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hsT : s < T) (hh0 : 0 < h)
    (hh1 : h < 1) (hW : 1 ≤ W) (hsW : 1 ≤ closeLen s W)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ ω ∂growthPathLaw W b, ω ∈ physCapEventC b E s h K W →
      ∀ (g : Fin np → Fin W → ℂ) (θ : ℝ),
        closedSourceData b E s T h τ m W (phase θ) (ω, g) =
          modelSourceData (srcSignature K (Fin np))
            (b3ClosedKAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ ((ω, g), θ))
            (b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs ((ω, g), θ)) := by
  have hh : h ^ 2 < 1 := by nlinarith
  have hn : closeLen s W ≤ ⌊(W : ℝ) * T⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg W))
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ae_farOut_succ hb0 hb hE1 hE2 hW,
    ae_closedCol_transport_disc (s := s) (h := h) hb0 hb hE1 hE2 hW hh,
    ae_isUnit_closingResolvent (h := h) hb0 hb hE1 hE2 hW hh (closeLen s W),
    ae_hlt (s := s) hb hE1 hE2 hW, B3Cur.ae_cap_tseq hb hE1 hE2 hW s h K, hV.2]
    with ω hU hF hT hR hL hC hVω hcap g θ
  funext r
  by_cases hr : r = 3
  · subst hr
    exact B3Cur.closedSourceData_three_eq τ m T Vs (ω, g) hn hsW (fun j => (hU j).1) hF hT hR
      (hC hcap) (hL K h) hh hVω.1 hVω.2 θ
  · exact closedSourceData_eq_model T Vs ((ω, g), θ) r hr

/-- The test of the final source data, as a test of the coordinates. -/
def finalTest {K np : ℕ} (Φ : BoundedContinuousFunction (SourceData np) ℝ) :
    BoundedContinuousFunction (CIdx K np → ℂ) ℝ :=
  Φ.compContinuous ⟨rebuild, continuous_rebuild⟩

/-- **Eventually the conditioned test of the final coordinates is the conditioned closed
expectation.** -/
theorem eventually_condObsTest_eq {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) (Φ : BoundedContinuousFunction (SourceData np) ℝ) :
    ∀ᶠ W in atTop, condObsTest b E s T h τ m W (Vs W) cToL (fun _ => (T - s).toNNReal)
      (finalTest Φ) = condClosedPhysExpectation b E s T h τ m Φ K W := by
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, hτT⟩, hs, hsτ, hh0, hh1, hVs⟩ := hD
  unfold condObsTest condClosedPhysExpectation cappedClosedPhysExpectation
  rcases Nat.eq_zero_or_pos np with hnp | hnp
  · subst hnp
    refine Eventually.of_forall fun W => ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact congrArg _ (congrArg Φ (Subsingleton.elim _ _))
  have hsT : s < T := (hsτ ⟨0, hnp⟩).trans (hτT ⟨0, hnp⟩)
  filter_upwards [eventually_ge_atTop 1, B3Cur.eventually_one_le_closeLen hs, hVs]
    with W hW hsW hV
  congr 1
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
    (ν := Measure.pi fun _ : Fin np =>
      BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W))).ae
    (ae_closedSourceData_eq τ m hb0 hb hE1 hE2 hsT hh0 hh1 hW hsW hV)
  have h2 := (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b)
    (ν := phaseLaw)).ae h1
  refine integral_congr_ae (h2.mono fun y hy => ?_)
  dsimp only
  by_cases hc : y.1.1 ∈ physCapEventC b E s h K W
  · rw [Set.indicator_of_mem hc, one_mul, one_mul]
    have e := hy hc y.1.2 y.2
    have hy' : ((y.1.1, y.1.2), y.2) = y := rfl
    rw [hy'] at e
    rw [e]
    change Φ (rebuild fun l => b3Obs b E s T h τ m W (Vs W) (cToL l) (T - s).toNNReal y) = _
    simp_rw [b3Obs_cToL, limLen_final hsT]
    rw [rebuild_cEntry]
  · rw [Set.indicator_of_notMem hc, zero_mul, zero_mul]

/-- **The final value along a conditioned fdd limit.** -/
theorem tendsto_condClosed_of_fdd {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
    {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}
    (hF : IsCapFddLimit b E s T h τ m K Vs φ Q tseq G Kc)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) :
    Tendsto (fun n => condClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop
      (𝓝 (modelExpectation K s T Q G Kc Φ)) := by
  have hτT := hD.1.2.2.2.2.2.2.2
  have hsτ := hD.2.2.1
  have hu : s + ((T - s).toNNReal : ℝ) ≤ max s T := by
    rw [Real.coe_toNNReal']
    rcases le_total s T with h1 | h1
    · rw [max_eq_left (sub_nonneg.2 h1)]; simp [h1]
    · rw [max_eq_right (sub_nonpos.2 h1)]; simp
  have hbirth : ∀ j, s + ((T - s).toNNReal : ℝ) ≠ τ j := fun j => by
    have hsT : s < T := (hsτ j).trans (hτT j)
    rw [Real.coe_toNNReal _ (sub_nonneg.2 hsT.le), add_sub_cancel]
    exact (hτT j).ne'
  have h1 := hF (CIdx K np) cToL (fun _ => (T - s).toNNReal) (fun _ => hu) (fun _ j => hbirth j)
    (finalTest Φ)
  have e : ∫ ω, finalTest Φ (fun l => complexObs tseq G Kc (cToL l) (T - s).toNNReal ω) ∂Q =
      modelExpectation K s T Q G Kc Φ := by
    unfold modelExpectation
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change Φ (rebuild fun l => complexObs tseq G Kc (cToL l) (T - s).toNNReal ω) = _
    simp_rw [complexObs_cToL]
    rw [rebuild_cEntry]
  rw [e] at h1
  exact h1.congr' ((hφ.eventually (eventually_condObsTest_eq hD Φ)).mono fun n hn => hn)

/-!
## The passage
-/

open scoped Classical in
/-- An admissible time-`s` frame at every `W` for which one exists (`0` otherwise). -/
def chooseFrame (b E s h : ℝ) (K W : ℕ) : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ :=
  if hx : ∃ Vs, IsTimeSFrame b E s h K W Vs then Classical.choose hx else 0

theorem frameDomain_chooseFrame (hEx : ExistsTimeSFrame) {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ}
    {T s h : ℝ} {K : ℕ} (hD : ComplexSourceLawDomain b E τ m T) (hs : 0 < s) (hτ : ∀ j, s < τ j)
    (hh0 : 0 < h) (hh1 : h < 1) : FrameDomain b E τ m T s h K (chooseFrame b E s h K) := by
  refine ⟨hD, hs, hτ, hh0, hh1, ?_⟩
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hD
  filter_upwards [hEx b hb0 hb E hE1 hE2 s hs h hh0 hh1 K] with W hW
  unfold chooseFrame
  split_ifs
  exact Classical.choose_spec hW

/-- **The subsequence form from the two propositions.** -/
theorem complexCapSubseq_of (hEx : ExistsTimeSFrame) (hFd : ComplexCapFdd)
    (hId : ComplexCapIdent) : ComplexCapSubseq := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ h hh0 hh1 hA K hne φ hφ
  have hFD := frameDomain_chooseFrame (K := K) hEx hD hs hτ hh0 hh1
  obtain ⟨ψ, hψ, Ω', mΩ', Q, tseq, G, Kc, hdat, hfdd⟩ :=
    hFd b E np τ m T s h K _ hFD Ω mΩ P μ hlim hA hne φ hφ
  have hφψ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  obtain ⟨Ω'', m'', Q'', t'', G'', K'', hM, heq⟩ :=
    hId b E np τ m T s h K _ hFD Ω mΩ P μ hlim hA hne _ hφψ Ω' mΩ' Q tseq G Kc hdat hfdd
  refine ⟨ψ, hψ, Ω'', m'', Q'', t'', G'', K'', hM, ?_⟩
  rw [heq Φ]
  exact tendsto_condClosed_of_fdd hFD hφψ hfdd Φ

/-- **Prokhorov on the cap event from the estimates** (the estimates of `TargetCapCond'` that
control the finite-`W` coordinates). -/
def TargetCapFdd : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg → ComplexCapFdd

/-- **Identification of the limit points from the estimates** and the finite-`W`
feasibility `ComplexClosedFeasible`. -/
def TargetCapIdent : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg → ComplexClosedFeasible → ComplexCapIdent

/-- **`TargetCapCond'` from the two targets and `ComplexClosedFeasible`.** -/
theorem targetCapCond'_of_targets (hFd : TargetCapFdd) (hId : TargetCapIdent)
    (hF : ComplexClosedFeasible) : TargetCapCond' :=
  targetCapCond'_of_subseq (fun hTL hEx hS hT hK _ hL hF' =>
    complexCapSubseq_of hEx (hFd hTL hS hT hK hL) (hId hTL hS hT hK hL hF')) hF

end BlockBand.SourceProcess.PhysApprox.B3
