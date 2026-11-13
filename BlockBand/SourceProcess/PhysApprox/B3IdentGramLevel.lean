module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Main
public import BlockBand.SourceProcess.PhysApprox.B3Reduce
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import BlockBand.SourceProcess.Stochastic.SDE.NativeExit

/-!
# The stopped identities from a cofinal set of levels

The weak limit passage gives the stopped tested identities only at levels where the stop is a.s.
continuous in the level. This file shows that a cofinal set of levels suffices: the
identities at a larger level `L' ≥ L` give those at `L`, by optional stopping. Measure: an
arbitrary probability measure `Q` on `Ω`; filtration: the raw natural filtration
`pastFiltration (complexObs tseq G Kc)` of the candidate's observables. The stops are not
stopping times of it; they agree a.s. with stopping times (`exists_stop_ae_eq_traceStop`
through `exists_stop_complexObs`; `exists_stoppingTime_ae_eq_hitTime` for the `𝒦` level stop).
The every-`ω` continuity of `G − gramJ` and `Kc − kJ` (`IsCapLimitData`) is what makes the
coordinates adapted and their paths continuous.

* **`isTestedMart_stopped_of_le`** (abstract): with `X` adapted and continuous for every `ω`,
  `σ ≤ σ'` a.s. and both a.s. stopping times, tested identities of `X^{σ'}` give those of
  `X^σ` (via `exists_stopped_mart_of_stoppedTested`, `exists_martingale_stopped_C` and
  `isTestedMart_of_martingale`).
* `IsAEStop`; `isAEStop_gramTraceStop`, `isAEStop_kLevelStop`, `IsAEStop.min`.
* Adaptedness and every-`ω` continuity of `cComp c`, `cBr c c'`, `kBr` for every coordinate.
* `IsGramCoordTestedAt`, `IsKCoordTestedAt`: the coordinate identities at one stop;
  **`IsGramCoordTestedAt.of_le`**, **`IsKCoordTestedAt.of_le`**.
* **`CapIdentGramCofinal`**, stated as a hypothesis: under `CapIdentPremise`, for every `L` some
  `L' ≥ L` has the Gram identities at `σ_{L'}`. **`capIdentGram_of_cofinal :
  CapIdentGramCofinal → CapIdentGram`**.
* **`CapIdentKDoubleCofinal`**, stated as a hypothesis: under `CapIdentPremise` and the Gram
  identities, for every `L`, `M` some `L' ≥ L`, `M' ≥ M` have the `𝒦` identities at
  `σ_{L'} ∧ ρ_{M'}`. **`capIdentKDouble_of_cofinal : CapIdentKDoubleCofinal → CapIdentKDouble`**.
* `targetCapIdentAll_of_cofinal`, `targetCapCond'_of_cofinal`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2 BlockBand.SourceProcess.BornUnique
open scoped NNReal ENNReal ComplexConjugate

/-! ## A smaller stop from a larger one (abstract) -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {obs : I → ℝ≥0 → Ω → ℂ}

/-- `σ` agrees a.s. with a stopping time of the raw natural filtration of `obs`. -/
def IsAEStop (Q : Measure Ω) (obs : I → ℝ≥0 → Ω → ℂ) (hobs : ∀ i u, Measurable (obs i u))
    (σ : Ω → WithTop ℝ≥0) : Prop :=
  ∃ ρ : Ω → WithTop ℝ≥0, IsStoppingTime (pastFiltration obs hobs) ρ ∧ ∀ᵐ ω ∂Q, ρ ω = σ ω

theorem IsAEStop.min {Q : Measure Ω} {hobs : ∀ i u, Measurable (obs i u)}
    {σ σ' : Ω → WithTop ℝ≥0} (h : IsAEStop Q obs hobs σ) (h' : IsAEStop Q obs hobs σ') :
    IsAEStop Q obs hobs fun ω => Min.min (σ ω) (σ' ω) := by
  obtain ⟨ρ, hρ, hρe⟩ := h
  obtain ⟨ρ', hρ', hρ'e⟩ := h'
  refine ⟨fun ω => Min.min (ρ ω) (ρ' ω), hρ.min hρ', ?_⟩
  filter_upwards [hρe, hρ'e] with ω h1 h2
  rw [h1, h2]

/-- **Tested identities at a larger a.s. stopping time give them at a smaller one.** -/
theorem isTestedMart_stopped_of_le (hobs : ∀ i u, Measurable (obs i u)) {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℂ}
    (had : ∀ t, StronglyMeasurable[pastSigma obs t] (X t))
    (hcont : ∀ ω, Continuous fun t => X t ω) {σ σ' : Ω → WithTop ℝ≥0}
    (hσ : IsAEStop Q obs hobs σ) (hσ' : IsAEStop Q obs hobs σ') (hle : ∀ᵐ ω ∂Q, σ ω ≤ σ' ω)
    (hX : IsTestedMart Q obs (stoppedProcess X σ')) :
    IsTestedMart Q obs (stoppedProcess X σ) := by
  obtain ⟨ρ, hρ, hρe⟩ := hσ
  obtain ⟨ρ', hρ', hρ'e⟩ := hσ'
  obtain ⟨N, hN, hNe⟩ := exists_stopped_mart_of_stoppedTested hobs had hcont hρ' hρ'e hX
  obtain ⟨M, hM, hMe⟩ := exists_martingale_stopped_C hN
    (fun t => (hNe t).trans (stoppedProcess_ae_eq X hρ'e t).symm)
    (ae_of_all _ fun ω => NativeSDE.continuous_stoppedProcess (hcont ω) ρ') hρ
  refine isTestedMart_of_martingale (𝓖 := pastFiltration obs hobs) (obs₀ := obs)
    (fun i u => (measurable_obs_past obs i le_rfl).stronglyMeasurable)
    (fun _ _ => EventuallyEq.rfl) hM fun t => (hMe t).trans ?_
  rw [stoppedProcess_stoppedProcess]
  refine stoppedProcess_ae_eq X ?_ t
  filter_upwards [hρe, hρ'e, hle] with ω h1 h2 h3
  simp only [Pi.inf_apply, h1, h2, inf_eq_left.2 h3]

end Abstract

/-! ## The stops of the candidate -/

variable {Ω : Type*} {K np : ℕ} {b E s : ℝ} {τ m : Fin np → ℝ}
  {tseq : Ω → ℕ → ℝ} {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
  {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

theorem gramTraceStop_mono {L L' : ℝ} (hLL' : L ≤ L') (ω : Ω) :
    gramTraceStop G L ω ≤ gramTraceStop G L' ω :=
  le_iInf₂ fun t ht => iInf₂_le t (hLL'.trans ht)

theorem kLevelStop_mono {M M' : ℝ} (hMM' : M ≤ M') (ω : Ω) :
    kLevelStop E s τ m Kc M ω ≤ kLevelStop E s τ m Kc M' ω :=
  le_iInf₂ fun t ht => iInf₂_le t (hMM'.trans ht)

section Stops

variable [MeasurableSpace Ω]

theorem isAEStop_gramTraceStop {Q : Measure Ω} (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u) (hb : b < 1) (hm : ∀ j, 0 ≤ m j)
    (L : ℝ) : IsAEStop Q (complexObs tseq G Kc) hobs (gramTraceStop G L) :=
  exists_stop_complexObs hobs hc hb hm L

/-- **The `𝒦` level stop agrees a.s. with a stopping time** (a hitting time of `[M, ∞)` by a
process continuous for every `ω`). -/
theorem isAEStop_kLevelStop {Q : Measure Ω} (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u) (M : ℝ) :
    IsAEStop Q (complexObs tseq G Kc) hobs (kLevelStop E s τ m Kc M) := by
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => ∑ i, ∑ j, ‖(Kc t ω - kJ E s τ m t) i j‖ with hY_def
  have hY : ∀ t, Measurable[pastFiltration (complexObs tseq G Kc) hobs t] (Y t) := fun t => by
    have hf : Continuous fun A : Matrix (Fin np) (Fin np) ℂ =>
        ∑ i, ∑ j, ‖(A - kJ E s τ m t) i j‖ :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_norm.comp ((continuous_id.sub continuous_const).matrix_elem i j)
    exact (hf.comp_stronglyMeasurable
      (stronglyMeasurable_Kc_pastC (tseq := tseq) (G := G) (Kc := Kc) t)).measurable
  have hYc : ∀ ω, Continuous fun t => Y t ω := fun ω =>
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_norm.comp ((hkc ω).matrix_elem i j)
  obtain ⟨ρ, hρ, -, hρe⟩ := Semimartingale.exists_stoppingTime_ae_eq_hitTime (Q := Q) hY
    (ae_of_all _ hYc) (isClosed_Ici (a := M))
  exact ⟨ρ, hρ, hρe⟩

end Stops

/-! ## Adaptedness and continuity of the coordinates -/

theorem continuous_cEntry_pair (c : CIdx K np) :
    Continuous fun p : GramState (SrcCol K (Fin np)) × Matrix (Fin np) (Fin np) ℂ =>
      cEntry c p.1 p.2 := by
  rcases c with e | ij
  · exact (ClosedLimit.continuous_gramEntry e).comp continuous_fst
  · exact continuous_snd.matrix_elem ij.1 ij.2

theorem continuous_cDrift (c : CIdx K np) : Continuous (cDrift b E c) := by
  rcases c with e | ij
  · exact ClosedLimit.continuous_gramDriftEntry _ _ e
  · exact continuous_const

theorem continuous_snd_entry (x y : SrcCol K (Fin np)) :
    Continuous fun g : GramState (SrcCol K (Fin np)) => g.2 x y :=
  continuous_snd.matrix_elem x y

theorem continuous_kGramCov (ij : Fin np × Fin np)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) : Continuous (kGramCov b E ij e) := by
  unfold kGramCov
  refine continuous_if_const _ (fun _ => ?_) (fun _ => ?_)
  · exact (continuous_const.mul (continuous_snd_entry _ _)).mul
      (ComplexUnique.continuous_gramC0_entry (srcSignature K (Fin np)) _ _)
  · exact (continuous_const.mul (continuous_snd_entry _ _)).mul
      (ComplexUnique.continuous_gramC1H_entry (srcSignature K (Fin np)) _ _)

theorem continuous_cCov (c c' : CIdx K np) : Continuous (cCov b E c c') := by
  rcases c with e | ij <;> rcases c' with e' | kl
  · exact ClosedLimit.continuous_gramCovEntry _ _ e e'
  · exact continuous_kGramCov kl e
  · exact continuous_kGramCov ij e'
  · exact continuous_const

theorem continuous_kConjCov (ij kl : Fin np × Fin np) :
    Continuous (kConjCov (K := K) b E ij kl) :=
  (continuous_const.mul (continuous_snd_entry _ _)).mul
    (ComplexUnique.continuous_gramC0_entry (srcSignature K (Fin np)) _ _)

section Coord

variable (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
  (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
include hc

theorem stronglyMeasurable_cComp (c : CIdx K np) (t : ℝ≥0) :
    StronglyMeasurable[pastSigma (complexObs tseq G Kc) t] (cComp b E s τ m G Kc c t) := by
  have hG : ∀ u, StronglyMeasurable[pastSigma (complexObs tseq G Kc) u] (G u) :=
    stronglyMeasurable_G_pastC
  have hc' : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω := hc
  have hβ : ∀ i : Fin np, Measurable[pastSigma (complexObs tseq G Kc) 0]
      (fun _ : Ω => τ i - s) := fun _ => measurable_const
  have h0 : ∀ u, u ≤ t → StronglyMeasurable[pastSigma (complexObs tseq G Kc) t]
      (fun ω => cEntry c (G u ω - gramJ b s τ m u) (Kc u ω - kJ E s τ m u)) := fun u hu =>
    (continuous_cEntry_pair c).comp_stronglyMeasurable
      ((((hG u).sub stronglyMeasurable_const).prodMk
        ((stronglyMeasurable_Kc_pastC u).sub stronglyMeasurable_const)).mono
          (pastSigma_mono _ hu))
  exact ((h0 t le_rfl).sub (h0 0 zero_le)).sub
    (stronglyMeasurable_integral_past (continuous_cDrift c) t hG hβ hc')

include hkc in
theorem continuous_cComp (c : CIdx K np) (ω : Ω) :
    Continuous fun t => cComp b E s τ m G Kc c t ω := by
  have hc' : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω := hc
  exact (((continuous_cEntry_pair c).comp ((hc ω).prodMk (hkc ω))).sub continuous_const).sub
    (continuous_integral_born (continuous_cDrift c) hc' ω)

theorem stronglyMeasurable_cBr (c c' : CIdx K np) (t : ℝ≥0) :
    StronglyMeasurable[pastSigma (complexObs tseq G Kc) t] (cBr b E s τ m G Kc c c' t) := by
  have hc' : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω := hc
  exact ((stronglyMeasurable_cComp hc c t).mul (stronglyMeasurable_cComp hc c' t)).sub
    (stronglyMeasurable_integral_past (continuous_cCov c c') t stronglyMeasurable_G_pastC
      (fun _ => measurable_const) hc')

include hkc in
theorem continuous_cBr (c c' : CIdx K np) (ω : Ω) :
    Continuous fun t => cBr b E s τ m G Kc c c' t ω := by
  have hc' : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω := hc
  exact ((continuous_cComp hc hkc c ω).mul (continuous_cComp hc hkc c' ω)).sub
    (continuous_integral_born (continuous_cCov c c') hc' ω)

theorem stronglyMeasurable_kBr (ij kl : Fin np × Fin np) (t : ℝ≥0) :
    StronglyMeasurable[pastSigma (complexObs tseq G Kc) t] (kBr b E s τ m G Kc ij kl t) := by
  have hc' : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω := hc
  exact ((stronglyMeasurable_cComp hc (Sum.inr ij) t).mul
    (Complex.continuous_conj.comp_stronglyMeasurable
      (stronglyMeasurable_cComp hc (Sum.inr kl) t))).sub
    (stronglyMeasurable_integral_past (continuous_kConjCov ij kl) t stronglyMeasurable_G_pastC
      (fun _ => measurable_const) hc')

include hkc in
theorem continuous_kBr (ij kl : Fin np × Fin np) (ω : Ω) :
    Continuous fun t => kBr b E s τ m G Kc ij kl t ω := by
  have hc' : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω := hc
  exact ((continuous_cComp hc hkc (Sum.inr ij) ω).mul
    (Complex.continuous_conj.comp (continuous_cComp hc hkc (Sum.inr kl) ω))).sub
    (continuous_integral_born (continuous_kConjCov ij kl) hc' ω)

end Coord

variable [MeasurableSpace Ω]

/-! ## The coordinate identities at one stop -/

/-- **The Gram coordinate identities at one stop `σ`.** -/
structure IsGramCoordTestedAt (b E s : ℝ) (τ m : Fin np → ℝ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (σ : Ω → WithTop ℝ≥0) : Prop where
  drift : ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
    IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess (cComp b E s τ m G Kc (Sum.inl e)) σ)
  bracket : ∀ e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
    IsTestedMart Q (complexObs tseq G Kc)
      (stoppedProcess (cBr b E s τ m G Kc (Sum.inl e) (Sum.inl e')) σ)

/-- **The `𝒦`-involving coordinate identities at one stop `σ`.** -/
structure IsKCoordTestedAt (b E s : ℝ) (τ m : Fin np → ℝ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (σ : Ω → WithTop ℝ≥0) : Prop where
  drift : ∀ ij : Fin np × Fin np, IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (cComp b E s τ m G Kc (Sum.inr ij)) σ)
  bracketK : ∀ ij kl : Fin np × Fin np, IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (cBr b E s τ m G Kc (Sum.inr ij) (Sum.inr kl)) σ)
  bracketG : ∀ (ij : Fin np × Fin np) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    IsTestedMart Q (complexObs tseq G Kc)
      (stoppedProcess (cBr b E s τ m G Kc (Sum.inr ij) (Sum.inl e)) σ)
  conjBr : ∀ ij kl : Fin np × Fin np, IsTestedMart Q (complexObs tseq G Kc)
    (stoppedProcess (kBr b E s τ m G Kc ij kl) σ)

section Le

variable {Q : Measure Ω} [IsProbabilityMeasure Q]
  (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
  (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
  (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
  {σ σ' : Ω → WithTop ℝ≥0}

include hc hkc

/-- **The Gram identities at a larger a.s. stopping time give them at a smaller one.** -/
theorem IsGramCoordTestedAt.of_le (hσ : IsAEStop Q (complexObs tseq G Kc) hobs σ)
    (hσ' : IsAEStop Q (complexObs tseq G Kc) hobs σ') (hle : ∀ᵐ ω ∂Q, σ ω ≤ σ' ω)
    (h : IsGramCoordTestedAt b E s τ m Q tseq G Kc σ') :
    IsGramCoordTestedAt b E s τ m Q tseq G Kc σ :=
  ⟨fun e => isTestedMart_stopped_of_le hobs (stronglyMeasurable_cComp hc _)
      (continuous_cComp hc hkc _) hσ hσ' hle (h.drift e),
    fun e e' => isTestedMart_stopped_of_le hobs (stronglyMeasurable_cBr hc _ _)
      (continuous_cBr hc hkc _ _) hσ hσ' hle (h.bracket e e')⟩

/-- **The `𝒦` identities at a larger a.s. stopping time give them at a smaller one.** -/
theorem IsKCoordTestedAt.of_le (hσ : IsAEStop Q (complexObs tseq G Kc) hobs σ)
    (hσ' : IsAEStop Q (complexObs tseq G Kc) hobs σ') (hle : ∀ᵐ ω ∂Q, σ ω ≤ σ' ω)
    (h : IsKCoordTestedAt b E s τ m Q tseq G Kc σ') :
    IsKCoordTestedAt b E s τ m Q tseq G Kc σ :=
  ⟨fun ij => isTestedMart_stopped_of_le hobs (stronglyMeasurable_cComp hc _)
      (continuous_cComp hc hkc _) hσ hσ' hle (h.drift ij),
    fun ij kl => isTestedMart_stopped_of_le hobs (stronglyMeasurable_cBr hc _ _)
      (continuous_cBr hc hkc _ _) hσ hσ' hle (h.bracketK ij kl),
    fun ij e => isTestedMart_stopped_of_le hobs (stronglyMeasurable_cBr hc _ _)
      (continuous_cBr hc hkc _ _) hσ hσ' hle (h.bracketG ij e),
    fun ij kl => isTestedMart_stopped_of_le hobs (stronglyMeasurable_kBr hc _ _)
      (continuous_kBr hc hkc _ _) hσ hσ' hle (h.conjBr ij kl)⟩

end Le

/-! ## The cofinal hypotheses and the reductions -/

/-- **The cofinal hypothesis `CapIdentGramCofinal`** (the Gram identities at a cofinal set of
levels): under the
premises of `CapIdentGram`, for every level `L` some level `L' ≥ L` has the Gram coordinate
identities of the limit at the trace stop `σ_{L'}`. -/
def CapIdentGramCofinal : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ L : ℝ, ∃ L' : ℝ, L ≤ L' ∧ IsGramCoordTestedAt b E s τ m Q tseq G Kc (gramTraceStop G L')

/-- **The cofinal hypothesis `CapIdentKDoubleCofinal`** (the `𝒦` identities at a cofinal set of
levels): under the
premises of `CapIdentKDouble` and the Gram identities, for every Gram level `L` and `𝒦` level
`M` some `L' ≥ L` and `M' ≥ M` have the `𝒦` coordinate identities at `σ_{L'} ∧ ρ_{M'}`. -/
def CapIdentKDoubleCofinal : Prop :=
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
    ∀ (L : ℝ) (M : ℕ), ∃ L' M' : ℝ, L ≤ L' ∧ (M : ℝ) ≤ M' ∧
      IsKCoordTestedAt b E s τ m Q tseq G Kc
        (fun ω => min (gramTraceStop G L' ω) (kLevelStop E s τ m Kc M' ω))

/-- **`CapIdentGram` from `CapIdentGramCofinal`.** -/
theorem capIdentGram_of_cofinal (hpin : CapIdentGramCofinal) : CapIdentGram := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  have hcof := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  obtain ⟨hD, -, -, -, -, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, -⟩ := hP
  obtain ⟨⟨-, hb, -, -, -, -, hm, -⟩, -⟩ := hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  have hlev : ∀ L, IsGramCoordTestedAt b E s τ m Q tseq G Kc (gramTraceStop G L) := fun L => by
    obtain ⟨L', hLL', hL'⟩ := hcof L
    exact hL'.of_le hobs hc hkc (isAEStop_gramTraceStop hobs hc hb1 hm L)
      (isAEStop_gramTraceStop hobs hc hb1 hm L') (ae_of_all _ (gramTraceStop_mono hLL'))
  exact ⟨fun L e => (hlev L).drift e, fun L e e' => (hlev L).bracket e e'⟩

/-- **`CapIdentKDouble` from `CapIdentKDoubleCofinal`.** -/
theorem capIdentKDouble_of_cofinal (hpin : CapIdentKDoubleCofinal) : CapIdentKDouble := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr M
  have hcof := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr
  obtain ⟨hD, -, -, -, -, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, -⟩ := hP
  obtain ⟨⟨-, hb, -, -, -, -, hm, -⟩, -⟩ := hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  have hlev : ∀ L, IsKCoordTestedAt b E s τ m Q tseq G Kc
      (fun ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω)) := fun L => by
    obtain ⟨L', M', hLL', hMM', hL'⟩ := hcof L M
    exact hL'.of_le hobs hc hkc
      ((isAEStop_gramTraceStop hobs hc hb1 hm L).min (isAEStop_kLevelStop hobs hkc _))
      ((isAEStop_gramTraceStop hobs hc hb1 hm L').min (isAEStop_kLevelStop hobs hkc _))
      (ae_of_all _ fun ω => min_le_min (gramTraceStop_mono hLL' ω) (kLevelStop_mono hMM' ω))
  exact ⟨fun L ij => (hlev L).drift ij, fun L ij kl => (hlev L).bracketK ij kl,
    fun L ij e => (hlev L).bracketG ij e, fun L ij kl => (hlev L).conjBr ij kl⟩

/-- **`TargetCapIdentAll` from the entrance, the two cofinal hypotheses and the `𝒦` stop.** -/
theorem targetCapIdentAll_of_cofinal (hEnt : CapIdentEntrance) (hGr : CapIdentGramCofinal)
    (hKD : CapIdentKDoubleCofinal) (hKS : CapIdentKStop) : TargetCapIdentAll :=
  targetCapIdentAll_of_pins hEnt (capIdentGram_of_cofinal hGr) (capIdentKDouble_of_cofinal hKD)
    hKS

/-- **`TargetCapCond'` from the entrance, the two cofinal hypotheses and the `𝒦` stop.** -/
theorem targetCapCond'_of_cofinal (hEnt : CapIdentEntrance) (hGr : CapIdentGramCofinal)
    (hKD : CapIdentKDoubleCofinal) (hKS : CapIdentKStop) : TargetCapCond' :=
  targetCapCond'_of_identPins hEnt (capIdentGram_of_cofinal hGr) (capIdentKDouble_of_cofinal hKD)
    hKS

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram
