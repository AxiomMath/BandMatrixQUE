module

public import BlockBand.Transmission.Dual.GSeqP1

/-!
# Atomlessness of the level-one lifetime on the sequence space, reduced to its analytic input

Level 1, exhaustion `W = boxExh 1 n₀`.
* **`measure_lt_sinf`** (the survival identity): for every `B1Family` `F` from `z`, every
  level-1 base solution `Z` from `z` and `u < t₀`,
  `Q¹(u < ρ_∞ ∧ t₀) = E⁰[h(Z_u)] / h(z)` (`h = flatH 1 = 1/(x+y)`, lintegral form). Proof:
  the local Doob identity (`lemma1H` with `H₁`) at horizon `u` for the cylinder `{w(u) ∈ W n}`,
  which is `{u < τ_{W n}}` on both sides (`stop_mem_iff`), then `n → ∞` (radius consistency on
  the left; every base path leaves no box before `u` for `n` large on the right).
* `HLeftCont D₀`: **the analytic input**: for every start, some level-1 base solution has
  `u ↦ E⁰[h(Z_u)]` left-continuous on `(0, ∞)`.
* **`a3Seq_of_hLeftCont`**: `HLeftCont D₀ → A3Seq D₀`; **`gSeq_all_of_hLeftCont`**: then the
  boundary classification holds at every level on the sequence space.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stop_mem_iff stopTime_of_lt
  exitTimeFrom_attained stoppedProcess_eq_stopTime)
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {D0 : ℝ}

theorem flatO_one_subset : flatO 1 ⊆ flatChamber 1 := fun w hw =>
  ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun i => by
    have := hw (Fin.castAdd 1 i)
    unfold slotSet coordMap at this; rw [Fin.append_left] at this; exact this, fun i => by
    have := hw (Fin.natAdd 1 i)
    unfold slotSet coordMap at this; rw [Fin.append_right] at this; exact this⟩

theorem exitTimeFrom_mono' {d : ℕ} {Ω : Type*} {V V' : Set (Fin d → ℝ)} (h : V ⊆ V')
    (Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) : exitTimeFrom V Y ω ≤ exitTimeFrom V' Y ω :=
  le_iInf₂ fun t ht => iInf₂_le t fun h' => ht (h h')

/-- **The survival identity** `Q¹(u < ρ_∞ ∧ t₀) = E⁰[h(Z_u)] / h(z)` on the sequence space. -/
theorem measure_lt_sinf (hD0 : 0 < D0) {z : Fin (1 + 1) → ℝ} {n₀ : ℕ} (hz : z ∈ flatBox 1 n₀)
    (F : B1Family D0 1 z) {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, boxExh 1 n₀ n ⊆ chartQ 1 '' Metric.ball 0 (r n)) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z : ℝ≥0 → Ω → Fin (1 + 1) → ℝ}
    (hZ : IsBaseSol D0 1 P 𝓖 Z z) {t₀ u : ℝ≥0} (hu : u < t₀) :
    Pq 1 {ω | u < sinf (boxExh 1 n₀) t₀ (F.stopSeq (boxExh 1 n₀) t₀ r ω)} =
      (∫⁻ ω, ENNReal.ofReal (flatH 1 (Z u ω)) ∂P) / ENNReal.ofReal (flatH 1 z) := by
  set W := boxExh 1 n₀
  have hE := isExh_boxExh 1 n₀
  have hz' : z ∈ flatChamber 1 := (hE.dom 0).2.2 (subset_closure hz)
  have hzn : ∀ n, z ∈ W n := fun n => hE.mono (Nat.zero_le n) hz
  have hc0 : 0 < flatH 1 z := cauchyH_pos hz'
  set A : ℕ → Set (Ωq 1) := fun n => {ω | (u : WithTop ℝ≥0) < exitTimeFrom (W n) (F.Yf (r n)) ω}
  set S : ℕ → Set Ω := fun n => {ω | (u : WithTop ℝ≥0) < exitTimeFrom (W n) Z ω}
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (flatH 1 (Z u ω))
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    𝓖.le u _ ((isStoppingTime_exit hZ (hE.isOpen n)).measurableSet_gt u)
  -- step 1: each level, by the local Doob identity at horizon `u`
  have h1 : ∀ n, Pq 1 (A n) = (∫⁻ ω in S n, f ω ∂P) * (ENNReal.ofReal (flatH 1 z))⁻¹ := by
    intro n
    have hY := isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 (r n)) (hball n)
    have hB : MeasurableSet {w : ℝ≥0 → Fin (1 + 1) → ℝ | w u ∈ W n} :=
      measurable_pi_apply u (hE.isOpen n).measurableSet
    have key := lemma1H hD0 (isHTransform_cauchyH D0) hZ (hE.dom n) (hzn n) hY
      (F.map_Yf_zero hz' (r n)) u hB
    have eA : {ω | (fun t => stoppedProcess (F.Yf (r n)) (exitTimeFrom (W n) (F.Yf (r n)))
        (min t u) ω) ∈ {w : ℝ≥0 → Fin (1 + 1) → ℝ | w u ∈ W n}} = A n := by
      ext ω
      simp only [mem_ofPred_eq, min_self, A]
      exact stop_mem_iff (hE.isOpen n) (F.continuous_Yf (r n) ω) u
    have eS : {ω | (fun t => stopZ (W n) Z (min t u) ω) ∈ {w : ℝ≥0 → Fin (1 + 1) → ℝ | w u ∈ W n}}
        = S n := by
      ext ω
      simp only [mem_ofPred_eq, min_self, S, stopZ]
      exact stop_mem_iff (hE.isOpen n) (hZ.cont ω) u
    rw [eA, eS] at key
    have hdens : ∀ ω ∈ S n, densH (flatH 1) (W n) Z z u ω = flatH 1 (Z u ω) / flatH 1 z :=
      fun ω hω => by
        simp only [densH, stopZ, stoppedProcess_eq_stopTime, stopTime_of_lt hω]
    rw [← ofReal_measureReal (μ := Pq 1), key, ofReal_integral_eq_lintegral_ofReal
      (integrable_densH (isHTransform_cauchyH D0) hZ (hE.dom n) (hzn n) u).integrableOn
      ((ae_restrict_iff' (hSm n)).2 (Eventually.of_forall fun ω hω => by
        rw [hdens ω hω]
        exact div_nonneg (cauchyH_pos (flatO_one_subset (hZ.mem u ω))).le hc0.le))]
    rw [← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc0).ne')]
    refine setLIntegral_congr_fun (hSm n) fun ω hω => ?_
    rw [hdens ω hω, ENNReal.ofReal_div_of_pos hc0, div_eq_mul_inv]
  -- step 2: the left side over `n`
  have h2 : {ω | u < sinf W t₀ (F.stopSeq W t₀ r ω)} = ⋃ n, A n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, A]
    have e : ∀ n, u < srho W t₀ (F.stopSeq W t₀ r ω) n ↔
        (u : WithTop ℝ≥0) < exitTimeFrom (W n) (F.Yf (r n)) ω := fun n => by
      rw [← WithTop.coe_lt_coe, coe_srho]
      show _ < min (pexit (W n) (pstop (W n) t₀ (F.cpath (r n) ω))) _ ↔ _
      rw [min_pexit_pstop (hE.isOpen n), lt_min_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, WithTop.coe_lt_coe.2 hu⟩⟩
    constructor
    · intro h; obtain ⟨n, hn⟩ := exists_lt_srho h; exact ⟨n, (e n).1 hn⟩
    · rintro ⟨n, hn⟩; exact ((e n).2 hn).trans_le (srho_le_sinf _ n)
  have hAm : ∀ n, ∀ᵐ ω ∂Pq 1, ∀ k, k ≤ n → ω ∈ A k → ω ∈ A n := fun n => by
    filter_upwards [F.ae_isConsAt hD0] with ω hc k hk hω
    have hn := F.isNested_stopSeq (t₀ := t₀) hE.isOpen hE.mono hr hball hc
    have hmono := hn.srho_mono hE.isOpen hE.mono hk
    have e : ∀ m, (srho W t₀ (F.stopSeq W t₀ r ω) m : WithTop ℝ≥0) =
        min (exitTimeFrom (W m) (F.Yf (r m)) ω) t₀ := fun m => by
      rw [coe_srho]; exact min_pexit_pstop (hE.isOpen m) _
    have hk' : (u : WithTop ℝ≥0) < srho W t₀ (F.stopSeq W t₀ r ω) k := by
      rw [e]; exact lt_min hω (WithTop.coe_lt_coe.2 hu)
    have := hk'.trans_le (WithTop.coe_le_coe.2 hmono)
    rw [e] at this
    exact (lt_min_iff.1 this).1
  have hacc : ∀ n, Pq 1 (accumulate A n) = Pq 1 (A n) := fun n => by
    refine measure_congr ?_
    filter_upwards [hAm n] with ω hω
    refine propext ⟨fun h => ?_, fun h => mem_accumulate.2 ⟨n, le_rfl, h⟩⟩
    obtain ⟨k, hk, hωk⟩ := mem_accumulate.1 h
    exact hω k hk hωk
  -- step 3: the right side over `n`
  have hcover : ⋃ n, S n = univ := by
    refine eq_univ_of_forall fun ω => mem_iUnion.2 ?_
    have hK : IsCompact ((fun t => Z t ω) '' Icc 0 u) := isCompact_Icc.image (hZ.cont ω)
    obtain ⟨m, hm⟩ := hK.elim_directed_cover W hE.isOpen (fun w hw => by
      obtain ⟨t, -, rfl⟩ := hw
      exact mem_iUnion.2 (hE.cover _ (flatO_one_subset (hZ.mem t ω)))) hE.mono.directed_le
    refine ⟨m, ?_⟩
    rcases exitTimeFrom_attained (hE.isOpen m) (hZ.cont ω) with h | ⟨s₀, h, hs⟩
    · show (u : WithTop ℝ≥0) < exitTimeFrom (W m) Z ω
      rw [h]; exact WithTop.coe_lt_top u
    · show (u : WithTop ℝ≥0) < exitTimeFrom (W m) Z ω
      rw [h, WithTop.coe_lt_coe]
      by_contra hle
      exact hs (hm ⟨s₀, ⟨zero_le, not_lt.1 hle⟩, rfl⟩)
  have h3 : ⨆ n, ∫⁻ ω in S n, f ω ∂P = ∫⁻ ω, f ω ∂P := by
    have hd : Directed (· ⊆ ·) S := (Monotone.directed_le fun m n hmn ω hω =>
      lt_of_lt_of_le hω (exitTimeFrom_mono' (hE.mono hmn) Z ω))
    rw [← setLIntegral_iUnion_of_directed f hd, hcover, Measure.restrict_univ]
  rw [h2, measure_iUnion_eq_iSup_accumulate]
  simp_rw [hacc, h1]
  rw [← ENNReal.iSup_mul, h3, div_eq_mul_inv]

/-- **The analytic input of the atomlessness of the lifetime**: for every start in `𝒞₁`, some
level-1 base solution has `u ↦ E⁰[h(Z_u)]` left-continuous on `(0, ∞)`. It is proved in
`hLeftCont_holds`. -/
def HLeftCont (D0 : ℝ) : Prop :=
  ∀ z ∈ flatChamber 1, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (_ : IsProbabilityMeasure P) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (Z : ℝ≥0 → Ω → Fin (1 + 1) → ℝ), IsBaseSol D0 1 P 𝓖 Z z ∧
      ∀ u : ℝ≥0, 0 < u → Tendsto (fun s => ∫⁻ ω, ENNReal.ofReal (flatH 1 (Z s ω)) ∂P) (𝓝[<] u)
        (𝓝 (∫⁻ ω, ENNReal.ofReal (flatH 1 (Z u ω)) ∂P))

/-- The level-1 `ρ_∞` is positive (the start lies in `W 0`). -/
theorem sinf_pos {z : Fin (1 + 1) → ℝ} {n₀ : ℕ} (hz : z ∈ flatBox 1 n₀) (F : B1Family D0 1 z)
    (r : ℕ → ℕ) {t₀ : ℝ≥0} (ht₀ : 0 < t₀) (ω : Ωq 1) :
    0 < sinf (boxExh 1 n₀) t₀ (F.stopSeq (boxExh 1 n₀) t₀ r ω) := by
  have hE := isExh_boxExh 1 n₀
  have hz' : z ∈ flatChamber 1 := (hE.dom 0).2.2 (subset_closure hz)
  refine lt_of_lt_of_le ?_ (srho_le_sinf _ 0)
  rw [← WithTop.coe_lt_coe, coe_srho, WithTop.coe_zero]
  show 0 < min (pexit (boxExh 1 n₀ 0) (pstop (boxExh 1 n₀ 0) t₀ (F.cpath (r 0) ω))) _
  rw [min_pexit_pstop (hE.isOpen 0), lt_min_iff]
  refine ⟨?_, WithTop.coe_lt_coe.2 ht₀⟩
  rcases exitTimeFrom_attained (hE.isOpen 0) (Y := cev (1 + 1)) (ω := F.cpath (r 0) ω)
    (F.cpath (r 0) ω).2 with h | ⟨s₀, h, hs⟩
  · rw [pexit, h]; exact WithTop.coe_lt_top 0
  · rw [pexit, h, WithTop.coe_pos]
    refine lt_of_le_of_ne zero_le fun h0 => hs ?_
    rw [← h0]
    show F.Yf (r 0) 0 ω ∈ boxExh 1 n₀ 0
    rw [F.Yf_zero hz']; exact hz

/-- **The level-one lifetime is atomless on the sequence space**, from its analytic input. -/
theorem a3Seq_of_hLeftCont (hD0 : 0 < D0) (hH : HLeftCont D0) : A3Seq D0 := by
  intro z n₀ hz F r hr hball t₀ u hu
  have hE := isExh_boxExh 1 n₀
  have hz' : z ∈ flatChamber 1 := (hE.dom 0).2.2 (subset_closure hz)
  obtain ⟨Ω, _, P, _, 𝓖, Z, hZ, hcont⟩ := hH z hz'
  set g : Ωq 1 → ℝ≥0 := fun ω => sinf (boxExh 1 n₀) t₀ (F.stopSeq (boxExh 1 n₀) t₀ r ω)
  have hg : Measurable g := (measurable_sinf hE.isOpen).comp (F.measurable_stopSeq hE.isOpen r)
  set φ : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (flatH 1 (Z s ω)) ∂P
  set c := ENNReal.ofReal (flatH 1 z)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.2 (cauchyH_pos hz')).ne'
  have hid : ∀ s, s < t₀ → Pq 1 {ω | s < g ω} = φ s / c := fun s hs =>
    measure_lt_sinf hD0 hz F hr hball hZ hs
  have hms : ∀ s : ℝ≥0, MeasurableSet {ω | s < g ω} := fun s => measurableSet_lt measurable_const hg
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | hpos
  · subst h0
    have he : {ω | g ω = 0} = ∅ :=
      eq_empty_of_forall_notMem fun ω h => (sinf_pos hz F r hu ω).ne' h
    rw [show {ω | sinf (boxExh 1 n₀) t₀ (F.stopSeq (boxExh 1 n₀) t₀ r ω) = 0} = {ω | g ω = 0}
      from rfl, he, measure_empty]
  · have hfin : φ u / c ≠ ⊤ := by rw [← hid u hu]; exact measure_ne_top _ _
    have h1 : Tendsto (fun s => φ s / c) (𝓝[<] u) (𝓝 (φ u / c)) :=
      ENNReal.Tendsto.div_const (hcont u hpos) (Or.inr hc)
    have hT : Tendsto (fun s => φ s / c - φ u / c) (𝓝[<] u) (𝓝 0) := by
      have := ENNReal.Tendsto.sub h1 (tendsto_const_nhds (x := φ u / c)) (Or.inl hfin)
      rwa [tsub_self] at this
    have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
    refine le_antisymm (ge_of_tendsto hT ?_) bot_le
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s < u := hs
    have hsub : {ω | u < g ω} ⊆ {ω | s < g ω} := fun ω h => hs'.trans h
    calc Pq 1 {ω | g ω = u} ≤ Pq 1 ({ω | s < g ω} \ {ω | u < g ω}) := by
          refine measure_mono fun ω h => ⟨?_, ?_⟩
          · show s < g ω
            rw [show g ω = u from h]; exact hs'
          · show ¬u < g ω
            rw [show g ω = u from h]; exact lt_irrefl u
      _ = Pq 1 {ω | s < g ω} - Pq 1 {ω | u < g ω} :=
          measure_sdiff hsub (hms u).nullMeasurableSet (measure_ne_top _ _)
      _ = φ s / c - φ u / c := by rw [hid s (hs'.trans hu), hid u hu]

/-- **The boundary classification at every level** on the sequence space, from the analytic
input of the atomlessness of the lifetime. -/
theorem gSeq_all_of_hLeftCont (hD0 : 0 < D0) (hH : HLeftCont D0) : ∀ q, GSeq D0 q :=
  gSeq_all_of_A3 hD0 (a3Seq_of_hLeftCont hD0 hH)

end BlockBand.Transmission.Dual.G
