module

public import BlockBand.Transmission.Dual.GDomB1
public import BlockBand.Transmission.Dual.GJLemmaC

/-!
# The collision bound over the whole exhaustion, on the sequence space

For a closed set `A` and an increasing sequence `W` of open sets, `hitSet W t₀ A n` is the event
(on `ℕ → CPath d`) that the `n`-th stopped path enters `A` strictly before `τ_{W_n} ∧ t₀`:
`{ŵ | τ_A(ŵ n) < τ_{W_n}(ŵ n) ∧ t₀}` (`τ_A = pexit Aᶜ`, measurable).
* `exists_hit_of_pstop`: if `pstop W t₀ v` enters `A` before its truncated exit, then `v` itself
  is in `A` at some `s < t₀ ∧ τ_W(v)`;
* `hitSet_mono`: on a nested pair `ŵ k = pstop (W k) t₀ (ŵ n)`, `k ≤ n`, a hit at level `k` is a
  hit at level `n` (so the events increase along stop sequences);
* **`lemmaC_seq`**: for a `B1Family` `F` of level `q` from `z ∉ A` and the law
  `μ = law(F.stopSeq W t₀ r)`, if `H_q ≤ M` on `A ∩ 𝒞_q` then `μ(⋃ₙ hitSet W t₀ A n) ≤ M/H_q(z)`
  (the collision bound for every `n`, `lemmaC_hit` with `W' = W_n \ A`, and the increasing
  union).
With `A = B_δ(η, K)` (the closed gap set of `exists_cauchyH_le_of_gap`) and `M = C δ` this is the
bound used to show that collisions at positive height are null.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime exitTimeFrom_attained
  mem_of_lt_exitTimeFrom)
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {d : ℕ} {t₀ : ℝ≥0}

theorem pstop_apply_of_le {W : Set (Fin d → ℝ)} {w : CPath d} {u : ℝ≥0}
    (hu : (u : WithTop ℝ≥0) ≤ min (pexit W w) t₀) : (pstop W t₀ w).1 u = w.1 u := by
  have hut : u ≤ t₀ := WithTop.coe_le_coe.1 (hu.trans (min_le_right _ _))
  show w.1 (stopTime (pexit W w) (min u t₀)) = w.1 u
  rw [min_eq_left hut, stopTime_of_le (hu.trans (min_le_left _ _))]

theorem min_pexit_pstop {W : Set (Fin d → ℝ)} (hW : IsOpen W) (w : CPath d) :
    min (pexit W (pstop W t₀ w)) t₀ = min (pexit W w) t₀ :=
  min_pexit_congr hW t₀ fun _ hu => pstop_apply_of_le hu

/-- The event that the `n`-th path enters `A` before its truncated exit from `W n`. -/
def hitSet (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) (A : Set (Fin d → ℝ)) (n : ℕ) :
    Set (ℕ → CPath d) :=
  {ŵ | pexit Aᶜ (ŵ n) < min (pexit (W n) (ŵ n)) (t₀ : WithTop ℝ≥0)}

theorem measurableSet_hitSet {W : ℕ → Set (Fin d → ℝ)} (hW : ∀ n, IsOpen (W n))
    {A : Set (Fin d → ℝ)} (hA : IsClosed A) (n : ℕ) : MeasurableSet (hitSet W t₀ A n) :=
  measurableSet_lt ((measurable_pexit hA.isOpen_compl).comp (measurable_pi_apply n))
    (((measurable_pexit (hW n)).comp (measurable_pi_apply n)).min measurable_const)

/-- A hit of `pstop W t₀ v` is a hit of `v` before `τ_W(v) ∧ t₀`. -/
theorem exists_hit_of_pstop {W A : Set (Fin d → ℝ)} (hW : IsOpen W) (hA : IsClosed A)
    {v : CPath d} (h : pexit Aᶜ (pstop W t₀ v) < min (pexit W (pstop W t₀ v)) t₀) :
    ∃ s : ℝ≥0, (s : WithTop ℝ≥0) < min (pexit W v) t₀ ∧ v.1 s ∈ A := by
  rw [min_pexit_pstop hW] at h
  rcases exitTimeFrom_attained hA.isOpen_compl (Y := cev d) (ω := pstop W t₀ v)
      (pstop W t₀ v).2 with h1 | ⟨s, h1, h2⟩
  · exact absurd h (by rw [pexit, h1]; exact not_lt.2 le_top)
  · have hs : (s : WithTop ℝ≥0) < min (pexit W v) t₀ := by rw [← show pexit Aᶜ _ = s from h1]; exact h
    refine ⟨s, hs, ?_⟩
    have := not_not.1 h2
    simp only [cev] at this
    rwa [pstop_apply_of_le hs.le] at this

/-- **Hits increase along a nested pair.** -/
theorem hitSet_mono {W : ℕ → Set (Fin d → ℝ)} (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W)
    {A : Set (Fin d → ℝ)} (hA : IsClosed A) {ŵ : ℕ → CPath d} {k n : ℕ} (hkn : k ≤ n)
    (hrel : ŵ k = pstop (W k) t₀ (ŵ n)) (h : ŵ ∈ hitSet W t₀ A k) : ŵ ∈ hitSet W t₀ A n := by
  simp only [hitSet, mem_ofPred_eq, hrel] at h
  obtain ⟨s, hs, hsA⟩ := exists_hit_of_pstop (hW k) hA h
  have hle : pexit Aᶜ (ŵ n) ≤ s := iInf₂_le s fun h' => h' hsA
  refine lt_of_le_of_lt hle (lt_of_lt_of_le hs (min_le_min ?_ le_rfl))
  exact le_iInf₂ fun t ht => iInf₂_le t fun h' => ht (hmono hkn h')

variable {q : ℕ} {D0 : ℝ}

/-- **The collision bound over the exhaustion** (sequence-space form). -/
theorem lemmaC_seq (hD0 : 0 < D0) {z : Fin (q + q) → ℝ} {W : ℕ → Set (Fin (q + q) → ℝ)}
    (hW : ∀ n, IsInteriorDomain (W n) (flatChamber q)) (hmono : Monotone W) (hz : z ∈ W 0)
    (F : B1Family D0 q z) {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) (t₀ : ℝ≥0)
    {A : Set (Fin (q + q) → ℝ)} (hA : IsClosed A) (hzA : z ∉ A) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ A ∩ flatChamber q, flatH q w ≤ M) :
    (Pq q).map (F.stopSeq W t₀ r) (⋃ n, hitSet W t₀ A n) ≤ ENNReal.ofReal (M / flatH q z) := by
  have hWo : ∀ n, IsOpen (W n) := fun n => (hW n).1
  have hz' : z ∈ flatChamber q := (hW 0).2.2 (subset_closure hz)
  have hzn : ∀ n, z ∈ W n := fun n => hmono (Nat.zero_le n) hz
  obtain ⟨Ω, _, P, _, 𝓖, Z, hZ⟩ := exists_baseSol hD0 q z (flatChamber_subset_flatO _ hz')
  have hs := F.isStopSeq_stopSeq (t₀ := t₀) hD0 hWo hmono hr hball
  rw [Measure.map_apply (F.measurable_stopSeq hWo r)
    (MeasurableSet.iUnion fun n => measurableSet_hitSet hWo hA n), preimage_iUnion,
    measure_iUnion_eq_iSup_accumulate]
  refine iSup_le fun n => ?_
  have hae : ∀ᵐ ω ∂Pq q, ∀ k, k ≤ n →
      F.stopSeq W t₀ r ω k = pstop (W k) t₀ (F.stopSeq W t₀ r ω n) := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : k ≤ n
    · filter_upwards [hs k n hk] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hk
  refine (measure_mono_ae (t := F.stopSeq W t₀ r ⁻¹' hitSet W t₀ A n) ?_).trans ?_
  · filter_upwards [hae] with ω hω hmem
    obtain ⟨k, hk, hmk⟩ := mem_accumulate.1 hmem
    exact hitSet_mono hWo hmono hA hk (hω k hk) hmk
  -- the `n`-th level: `lemmaC_hit` with `W' = W n \ A`
  have hWA : IsInteriorDomain (W n \ A) (flatChamber q) :=
    ⟨(hWo n).sdiff hA, (hW n).2.1.of_isClosed_subset isClosed_closure
      (closure_mono sdiff_subset), (closure_mono sdiff_subset).trans (hW n).2.2⟩
  have hMP : IsMPSolutionOn (Pq q) (𝓖q q) (flatDrift D0 q) (flatDiff D0 q) (W n \ A)
      (F.Yf (r n)) :=
    isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 (r n)) (sdiff_subset.trans (hball n))
  have H := lemmaC_hit hD0 hZ hWA ⟨hzn n, hzA⟩ hMP (F.map_Yf_zero hz' (r n))
    (F.continuous_Yf (r n)) t₀ hA.measurableSet hM0 fun w hw =>
      hM w ⟨hw.1, (hW n).2.2 (closure_mono sdiff_subset hw.2)⟩
  refine (measure_mono fun ω hω => ?_).trans ((ofReal_measureReal (μ := Pq q)).symm.le.trans
    (ENNReal.ofReal_le_ofReal H))
  obtain ⟨s, hs, hsA⟩ := exists_hit_of_pstop (hWo n) hA hω
  exact ⟨s, WithTop.coe_le_coe.1 (hs.le.trans (min_le_right _ _)), lt_of_lt_of_le hs
    (min_le_left _ _), hsA⟩

end BlockBand.Transmission.Dual.G
