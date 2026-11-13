module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLevel

/-!
# Good levels are co-countable

* `rightLevel σ L ω = ⨅_{L' > L} σ_{L'}(ω)`; `IsGoodLevel Q σ L`.
* **`countable_not_isGoodLevel`** (abstract): if `σ` is nondecreasing in the level and each
  `{σ_L < q}` is `Q`-null-measurable, all but countably many levels are good. Proof: for each
  rational `q ≥ 0`, `L ↦ Q(σ_L < q)` is antitone, hence continuous off a countable set
  (`Antitone.countable_not_continuousAt`); at a continuity point,
  `Q(inf_{L'>L} σ_{L'} < q) = lim_n Q(σ_{L+1/(n+1)} < q) = Q(σ_L < q)`, and the first event is
  contained in the second; over all rational `q` this gives `σ_L = inf_{L'>L} σ_{L'}` a.s.
* `exists_good_ge`: good levels are cofinal (the complement of a countable set of reals is
  dense).
* `IsAEStop.nullMeasurableSet_lt`: the sets `{σ < q}` of an a.s. stopping time are null-measurable.
* **Hypothesis `CapIdentGramGood`**: the Gram identities at `σ_L` for every good trace level `L`.
* **Hypothesis `CapIdentKDoubleGood`**: the `𝒦` identities at `σ_L ∧ ρ_M` for every good trace level
  `L` and every good `𝒦` level `M`.
* **`capIdentGramCofinal_of_good`**, **`capIdentKDoubleCofinal_of_good`**, hence
  `capIdentGram_of_good`, `capIdentKDouble_of_good`, `targetCapIdentAll_of_good`,
  `targetCapCond'_of_good`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

/-!
## Good levels (abstract)
-/

section Abstract

variable {Ω : Type*}

/-- The right limit in the level: `inf_{L' > L} σ_{L'}`. -/
def rightLevel (σ : ℝ → Ω → WithTop ℝ≥0) (L : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (L' : ℝ) (_ : L < L'), σ L' ω

/-- **A good level**: a.s. the stop is right-continuous in the level at `L`. -/
def IsGoodLevel [MeasurableSpace Ω] (Q : Measure Ω) (σ : ℝ → Ω → WithTop ℝ≥0) (L : ℝ) : Prop :=
  ∀ᵐ ω ∂Q, σ L ω = rightLevel σ L ω

variable {σ : ℝ → Ω → WithTop ℝ≥0}

theorem le_rightLevel (hmono : ∀ L L', L ≤ L' → ∀ ω, σ L ω ≤ σ L' ω) (L : ℝ) (ω : Ω) :
    σ L ω ≤ rightLevel σ L ω :=
  le_iInf₂ fun L' hL' => hmono L L' hL'.le ω

theorem rightLevel_lt_iff (hmono : ∀ L L', L ≤ L' → ∀ ω, σ L ω ≤ σ L' ω) (L : ℝ) (ω : Ω)
    (q : WithTop ℝ≥0) :
    rightLevel σ L ω < q ↔ ∃ n : ℕ, σ (L + 1 / ((n : ℝ) + 1)) ω < q := by
  constructor
  · intro h
    obtain ⟨L', hL'⟩ := iInf_lt_iff.1 h
    obtain ⟨hLL', hlt⟩ := iInf_lt_iff.1 hL'
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hLL')
    exact ⟨n, lt_of_le_of_lt (hmono _ _ (by linarith) ω) hlt⟩
  · rintro ⟨n, hn⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    exact lt_of_le_of_lt (iInf₂_le _ (by linarith)) hn

/-- Rational thresholds `q ≥ 0` separate a strict inequality in `WithTop ℝ≥0`. -/
theorem exists_rat_sep {a c : WithTop ℝ≥0} (h : a < c) :
    ∃ q : ℚ, a < ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0) ∧
      ¬ c < ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0) := by
  have ha : a ≠ ⊤ := ne_top_of_lt h
  lift a to ℝ≥0 using ha
  cases c with
  | top =>
      obtain ⟨q, hq⟩ := exists_rat_gt (a : ℝ)
      refine ⟨q, WithTop.coe_lt_coe.2 (Real.lt_toNNReal_iff_coe_lt.2 hq), ?_⟩
      exact not_lt.2 le_top
  | coe c =>
      have hac : (a : ℝ) < c := by exact_mod_cast WithTop.coe_lt_coe.1 h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hac
      refine ⟨q, WithTop.coe_lt_coe.2 (Real.lt_toNNReal_iff_coe_lt.2 hq1), ?_⟩
      refine not_lt.2 (WithTop.coe_le_coe.2 ?_)
      exact (Real.toNNReal_le_iff_le_coe).2 hq2.le

variable [MeasurableSpace Ω] {Q : Measure Ω}

/-- The rational threshold function `L ↦ Q(σ_L < q)`. -/
def levelMass (Q : Measure Ω) (σ : ℝ → Ω → WithTop ℝ≥0) (q : ℚ) (L : ℝ) : ℝ≥0∞ :=
  Q {ω | σ L ω < ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0)}

theorem antitone_levelMass (hmono : ∀ L L', L ≤ L' → ∀ ω, σ L ω ≤ σ L' ω) (q : ℚ) :
    Antitone (levelMass Q σ q) := fun L L' hLL' =>
  measure_mono fun ω hω => lt_of_le_of_lt (hmono L L' hLL' ω) hω

/-- At a continuity point of `L ↦ Q(σ_L < q)`, `{inf_{L'>L} σ_{L'} < q} = {σ_L < q}` a.e. -/
theorem ae_eq_rightLevel_lt [IsFiniteMeasure Q] (hmono : ∀ L L', L ≤ L' → ∀ ω, σ L ω ≤ σ L' ω)
    (hmeas : ∀ (L : ℝ) (q : ℝ≥0), NullMeasurableSet {ω | σ L ω < (q : WithTop ℝ≥0)} Q)
    {q : ℚ} {L : ℝ} (hcont : ContinuousAt (levelMass Q σ q) L) :
    {ω | rightLevel σ L ω < ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[Q]
      {ω | σ L ω < ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0)} := by
  set qq : WithTop ℝ≥0 := ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0)
  set A : ℕ → Set Ω := fun n => {ω | σ (L + 1 / ((n : ℝ) + 1)) ω < qq}
  have hA : Monotone A := fun n n' hnn' ω hω => by
    refine lt_of_le_of_lt (hmono _ _ ?_ ω) hω
    have h1 : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnn' 1
    have h2 : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) h1
    linarith
  have hU : {ω | rightLevel σ L ω < qq} = ⋃ n, A n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, A]
    exact rightLevel_lt_iff hmono L ω qq
  have hlim1 := tendsto_measure_iUnion_atTop (μ := Q) hA
  have hpt : Tendsto (fun n : ℕ => L + 1 / ((n : ℝ) + 1)) atTop (𝓝 L) := by
    simpa using tendsto_const_nhds (x := L) |>.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim2 : Tendsto (fun n => Q (A n)) atTop (𝓝 (levelMass Q σ q L)) :=
    hcont.tendsto.comp hpt
  have heq : Q (⋃ n, A n) = Q {ω | σ L ω < qq} := tendsto_nhds_unique hlim1 hlim2
  have hsub : {ω | rightLevel σ L ω < qq} ⊆ {ω | σ L ω < qq} := fun ω hω =>
    lt_of_le_of_lt (le_rightLevel hmono L ω) hω
  have hnm : NullMeasurableSet {ω | rightLevel σ L ω < qq} Q := by
    rw [hU]
    exact NullMeasurableSet.iUnion fun n => hmeas _ _
  refine ae_eq_of_subset_of_measure_ge hsub ?_ hnm (measure_ne_top _ _)
  rw [hU, heq]

/-- **All but countably many levels are good.** -/
theorem countable_not_isGoodLevel [IsFiniteMeasure Q]
    (hmono : ∀ L L', L ≤ L' → ∀ ω, σ L ω ≤ σ L' ω)
    (hmeas : ∀ (L : ℝ) (q : ℝ≥0), NullMeasurableSet {ω | σ L ω < (q : WithTop ℝ≥0)} Q) :
    {L | ¬ IsGoodLevel Q σ L}.Countable := by
  refine (Set.countable_iUnion fun q : ℚ =>
    (antitone_levelMass (Q := Q) hmono q).countable_not_continuousAt).mono ?_
  intro L hL
  simp only [mem_ofPred_eq] at hL
  simp only [mem_iUnion, mem_ofPred_eq]
  by_contra hall
  push Not at hall
  apply hL
  have hae : ∀ᵐ ω ∂Q, ∀ q : ℚ,
      (ω ∈ {ω | rightLevel σ L ω < ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0)} ↔
        ω ∈ {ω | σ L ω < ((Real.toNNReal q : ℝ≥0) : WithTop ℝ≥0)}) :=
    ae_all_iff.2 fun q => (ae_eq_rightLevel_lt hmono hmeas (hall q)).mem_iff
  filter_upwards [hae] with ω hω
  refine le_antisymm (le_rightLevel hmono L ω) (not_lt.1 fun hlt => ?_)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_sep hlt
  exact hq2 ((hω q).2 hq1)

/-- **Good levels are cofinal.** -/
theorem exists_good_ge [IsFiniteMeasure Q] (hmono : ∀ L L', L ≤ L' → ∀ ω, σ L ω ≤ σ L' ω)
    (hmeas : ∀ (L : ℝ) (q : ℝ≥0), NullMeasurableSet {ω | σ L ω < (q : WithTop ℝ≥0)} Q)
    (L : ℝ) : ∃ L' : ℝ, L ≤ L' ∧ IsGoodLevel Q σ L' := by
  obtain ⟨z, hz, hzI⟩ := ((countable_not_isGoodLevel hmono hmeas).dense_compl ℝ).exists_between
    (lt_add_one L)
  refine ⟨z, hzI.1.le, ?_⟩
  simpa using hz

/-- The sets `{σ < q}` of an a.s. stopping time are null-measurable. -/
theorem IsAEStop.nullMeasurableSet_lt {I : Type*} {obs : I → ℝ≥0 → Ω → ℂ}
    {hobs : ∀ i u, Measurable (obs i u)} {τ : Ω → WithTop ℝ≥0} (h : IsAEStop Q obs hobs τ)
    (q : ℝ≥0) : NullMeasurableSet {ω | τ ω < (q : WithTop ℝ≥0)} Q := by
  obtain ⟨ρ, hρ, hρe⟩ := h
  have hm : MeasurableSet {ω | ρ ω < (q : WithTop ℝ≥0)} :=
    (pastFiltration obs hobs).le q _ (hρ.measurableSet_lt q)
  refine hm.nullMeasurableSet.congr ?_
  filter_upwards [hρe] with ω hω
  rw [hω]

end Abstract

/-!
## The hypotheses at good levels
-/

/-- **Hypothesis `CapIdentGramGood`** ( at good levels): under the premises of
`CapIdentGram`, the Gram coordinate identities of the limit at the trace stop `σ_L` for every
level `L` at which `L ↦ σ_L` is a.s. right-continuous. -/
def CapIdentGramGood : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ L : ℝ, IsGoodLevel Q (gramTraceStop G) L →
      IsGramCoordTestedAt b E s τ m Q tseq G Kc (gramTraceStop G L)

/-- **Hypothesis `CapIdentKDoubleGood`** ( at good levels): under the premises of
`CapIdentKDouble` and the Gram identities, the `𝒦` coordinate identities at `σ_L ∧ ρ_M` for
every good trace level `L` and every good `𝒦` level `M`. -/
def CapIdentKDoubleGood : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    IsGramCoordTested b E s τ m Q tseq G Kc (gramTraceStop G) →
    ∀ L M : ℝ, IsGoodLevel Q (gramTraceStop G) L → IsGoodLevel Q (kLevelStop E s τ m Kc) M →
      IsKCoordTestedAt b E s τ m Q tseq G Kc
        (fun ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω))

/-- **The Gram cofinal hypothesis from the good-level hypothesis.** -/
theorem capIdentGramCofinal_of_good (hpin : CapIdentGramGood) : CapIdentGramCofinal := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP L
  have hgood := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  obtain ⟨hD, -, -, -, -, ⟨hQ, htm, hGm, hKm, hc, -⟩, -⟩ := hP
  obtain ⟨⟨-, hb, -, -, -, -, hm, -⟩, -⟩ := hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  obtain ⟨L', hLL', hL'⟩ := exists_good_ge (Q := Q) (σ := gramTraceStop G)
    (fun L L' h ω => gramTraceStop_mono h ω)
    (fun L q => (isAEStop_gramTraceStop (Q := Q) hobs hc hb1 hm L).nullMeasurableSet_lt q) L
  exact ⟨L', hLL', hgood L' hL'⟩

/-- **The `𝒦` cofinal hypothesis from the good-level hypothesis.** -/
theorem capIdentKDoubleCofinal_of_good (hpin : CapIdentKDoubleGood) : CapIdentKDoubleCofinal := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr L M
  have hgood := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr
  obtain ⟨hD, -, -, -, -, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, -⟩ := hP
  obtain ⟨⟨-, hb, -, -, -, -, hm, -⟩, -⟩ := hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  obtain ⟨L', hLL', hL'⟩ := exists_good_ge (Q := Q) (σ := gramTraceStop G)
    (fun L L' h ω => gramTraceStop_mono h ω)
    (fun L q => (isAEStop_gramTraceStop (Q := Q) hobs hc hb1 hm L).nullMeasurableSet_lt q) L
  obtain ⟨M', hMM', hM'⟩ := exists_good_ge (Q := Q) (σ := kLevelStop E s τ m Kc)
    (fun M M' h ω => kLevelStop_mono h ω)
    (fun M q => (isAEStop_kLevelStop (Q := Q) hobs hkc M).nullMeasurableSet_lt q) M
  exact ⟨L', M', hLL', hMM', hgood L' M' hL' hM'⟩

theorem capIdentGram_of_good (hpin : CapIdentGramGood) : CapIdentGram :=
  capIdentGram_of_cofinal (capIdentGramCofinal_of_good hpin)

theorem capIdentKDouble_of_good (hpin : CapIdentKDoubleGood) : CapIdentKDouble :=
  capIdentKDouble_of_cofinal (capIdentKDoubleCofinal_of_good hpin)

/-- **`TargetCapIdentAll` from the entrance, the two good-level hypotheses and the `𝒦` stop.** -/
theorem targetCapIdentAll_of_good (hEnt : CapIdentEntrance) (hGr : CapIdentGramGood)
    (hKD : CapIdentKDoubleGood) (hKS : CapIdentKStop) : TargetCapIdentAll :=
  targetCapIdentAll_of_pins hEnt (capIdentGram_of_good hGr) (capIdentKDouble_of_good hKD) hKS

/-- **`TargetCapCond'` from the entrance, the two good-level hypotheses and the `𝒦` stop.** -/
theorem targetCapCond'_of_good (hEnt : CapIdentEntrance) (hGr : CapIdentGramGood)
    (hKD : CapIdentKDoubleGood) (hKS : CapIdentKStop) : TargetCapCond' :=
  targetCapCond'_of_identPins hEnt (capIdentGram_of_good hGr) (capIdentKDouble_of_good hKD) hKS

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram
