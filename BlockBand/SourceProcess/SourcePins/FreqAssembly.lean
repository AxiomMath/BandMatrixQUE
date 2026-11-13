module

public import BlockBand.SourceProcess.SourceProcessLaw.Assembly
public import BlockBand.SourceProcess.SourcePins.Freq

/-!
# The source process limit with the frequently-form approximation

`limit_of_freq`: under the transmission law, the entrance, model, cap-removal and cutoff-removal
hypotheses, `PhysicalSamplingWeak` and `PhysicalApproximationFreq`, the source transform converges
and its limit is the iterated cutoff limit of finite source model values.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal NNReal

/-- **The field `SourceProcessContract.limit`** from the hypotheses, with
`PhysicalApproximationFreq`. -/
theorem limit_of_freq (hTL : TransmissionLawContract) (hA1 : EntranceAtomic) (hA2 : SeqExtraction)
    (hB1 : ModelExists) (hB2 : ModelUnique) (hC : CapRemoval) (hD : CutoffRemoval)
    (hE1 : PhysicalSamplingWeak) (hE2 : PhysicalApproximationFreq) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
      ∃ L : ℝ, Tendsto (fun W => sourceTransform b E T q a W) atTop (𝓝 L) ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ ∧
          ∃ Φ : ℕ → ℝ → ℕ → ℝ,
            (∀ K h M, 0 < h → 0 < M →
              FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a (Φ K h M)) ∧
            IteratedCutoffLimit Φ L := by
  intro b hb0 hb E hE1' hE2' s T hs hsT p q hq J a ha
  obtain ⟨Ω, m, P, μ, hlim, -⟩ := hTL.law b hb0 hb E hE1' hE2' _ isAbsorptionProfile_zero'
  have hent := entrance_sequence hA1 hA2 hb0 hb hE1' hE2' hlim hs
  have hv := fun (K : ℕ) {h : ℝ} {M : ℕ} (hh : 0 < h) (hM : 0 < M) =>
    modelValue_exists hB1 hB2 hb0 hb hE1' hE2' hs hsT hq hent a K hh hM
  -- the model values
  let Φ : ℕ → ℝ → ℕ → ℝ := fun K h M =>
    if hh : 0 < h ∧ 0 < M then Classical.choose (hv K hh.1 hh.2) else 0
  have hΦ : ∀ K h M, 0 < h → 0 < M →
      FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a (Φ K h M) := by
    intro K h M hh hM
    simp only [Φ, dite_eq_left (And.intro hh hM)]
    exact Classical.choose_spec (hv K hh hM)
  -- the cap-free values
  have hcap := fun {h : ℝ} {M : ℕ} (hh : 0 < h) (hM : 0 < M) =>
    hC b hb0 hb E hE1' hE2' Ω m P μ hlim s T hs hsT p q hq J a ha h M hh hM (fun K => Φ K h M)
      fun K => hΦ K h M hh hM
  let Λ : ℝ → ℕ → ℝ := fun h M =>
    if hh : 0 < h ∧ 0 < M then Classical.choose (hcap hh.1 hh.2) else 0
  have hΛ : ∀ h M, 0 < h → 0 < M → Tendsto (fun K => Φ K h M) atTop (𝓝 (Λ h M)) := by
    intro h M hh hM
    simp only [Λ, dite_eq_left (And.intro hh hM)]
    exact Classical.choose_spec (hcap hh hM)
  -- the cutoff-free values
  have hcut := fun {M : ℕ} (hM : 0 < M) =>
    hD b hb0 hb E hE1' hE2' Ω m P μ hlim s T hs hsT p q hq J a ha M hM (fun K h => Φ K h M)
      (fun h => Λ h M) (fun K h hh => hΦ K h M hh hM) (fun h hh => hΛ h M hh hM)
  let Λ' : ℕ → ℝ := fun M => if hM : 0 < M then Classical.choose (hcut hM) else 0
  have hΛ' : ∀ M, 0 < M → Tendsto (fun h => Λ h M) (𝓝[>] 0) (𝓝 (Λ' M)) := by
    intro M hM
    simp only [Λ', dite_eq_left hM]
    exact Classical.choose_spec (hcut hM)
  -- the physical sampled transforms converge to `Λ'(M)`
  have hphys : ∀ M, 0 < M →
      Tendsto (fun W => sampledPhysTransform b E T q a M W) atTop (𝓝 (Λ' M)) := by
    intro M hM
    refine tendsto_of_iterated_freq (Φ := fun K h => Φ K h M) (fun h hh => hΛ h M hh hM)
      (hΛ' M hM) fun ε hε => ?_
    refine ((hE2 b hb0 hb E hE1' hE2' Ω m P μ hlim s T hs hsT p q hq J a ha M hM ε
      hε).and_eventually self_mem_nhdsWithin).mono fun h ⟨hK, hpos⟩ => ?_
    exact hK.mono fun K hK' => hK' _ (hΦ K h M hpos hM)
  -- sampling error `C/M`
  obtain ⟨e, he, hCM⟩ := hE1 b hb0 hb E hE1' hE2' s T hs hsT p q hq J a ha
  obtain ⟨L, hL, hLM⟩ := exists_limit_of_approx (F := atTop)
    (x := fun W => sourceTransform b E T q a W) (y := fun M W => sampledPhysTransform b E T q a M W)
    (lam := Λ') (e := e) he
    ((eventually_gt_atTop 0).mono hphys) ((eventually_gt_atTop 0).mono hCM)
  exact ⟨L, hL, Ω, m, P, μ, hlim, Φ, hΦ, Λ, Λ', hΛ, hΛ', hLM⟩

/-- **The field `SourceProcessContract.restore`** from `limit` and `EarlySources`. -/
theorem restore_of_freq (hTL : TransmissionLawContract) (hA1 : EntranceAtomic) (hA2 : SeqExtraction)
    (hB1 : ModelExists) (hB2 : ModelUnique) (hC : CapRemoval) (hD : CutoffRemoval)
    (hE1 : PhysicalSamplingWeak) (hE2 : PhysicalApproximationFreq) (hES : EarlySources) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ T : ℝ, 0 < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest 0 T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
      ∃ L : ℝ, Tendsto (fun W => sourceTransform b E T q a W) atTop (𝓝 L) ∧
        ∃ Ls : ℝ → ℝ, (∀ s, 0 < s → s < T →
            Tendsto (fun W => sourceTransform b E T (fun i => Set.indicator (Set.Icc s T) (q i))
              a W) atTop (𝓝 (Ls s))) ∧
          Tendsto Ls (𝓝[>] 0) (𝓝 L) := by
  intro b hb0 hb E hE1' hE2' T hT p q hq J a ha
  have hlim := fun {s : ℝ} (hs : 0 < s) (hsT : s < T) =>
    (limit_of_freq hTL hA1 hA2 hB1 hB2 hC hD hE1 hE2 b hb0 hb E hE1' hE2' s T hs hsT p
      (fun i => Set.indicator (Set.Icc s T) (q i))
      (fun i => isSourceTest_truncate (hq i) hs.le) J a ha)
  let Ls : ℝ → ℝ := fun s => if hs : 0 < s ∧ s < T then Classical.choose (hlim hs.1 hs.2) else 0
  have hLs : ∀ s, 0 < s → s < T →
      Tendsto (fun W => sourceTransform b E T (fun i => Set.indicator (Set.Icc s T) (q i))
        a W) atTop (𝓝 (Ls s)) := by
    intro s hs hsT
    simp only [Ls, dite_eq_left (And.intro hs hsT)]
    exact (Classical.choose_spec (hlim hs hsT)).1
  obtain ⟨C, hCs⟩ := hES b hb0 hb E hE1' hE2' T hT p q hq J a ha
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < T :=
    Eventually.and self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hT))
  have he : Tendsto (fun s : ℝ => C * s) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul C
    simpa using this
  obtain ⟨L, hL, hLs'⟩ := exists_limit_of_approx (F := 𝓝[>] (0 : ℝ))
    (x := fun W => sourceTransform b E T q a W)
    (y := fun s W => sourceTransform b E T (fun i => Set.indicator (Set.Icc s T) (q i)) a W)
    (lam := Ls) (e := fun s => C * s) he (hev.mono fun s hs => hLs s hs.1 hs.2)
    (hev.mono fun s hs => hCs s hs.1 hs.2)
  exact ⟨L, hL, Ls, hLs, hLs'⟩

/-- **The source process theorem `SourceProcessContract`** from `TransmissionLawContract`, the
hypotheses `EntranceAtomic`, `SeqExtraction`, `ModelExists`, `ModelUnique`, `CapRemoval`,
`CutoffRemoval`, `PhysicalSamplingWeak`, `PhysicalApproximationFreq`, `EarlySources` and
`RankFreeCoupling`. -/
theorem sourceProcessContract_of_freq (hTL : TransmissionLawContract) (hA1 : EntranceAtomic)
    (hA2 : SeqExtraction) (hB1 : ModelExists) (hB2 : ModelUnique) (hC : CapRemoval)
    (hD : CutoffRemoval) (hE1 : PhysicalSamplingWeak) (hE2 : PhysicalApproximationFreq)
    (hES : EarlySources) (hRF : RankFreeCoupling) : SourceProcessContract where
  limit := limit_of_freq hTL hA1 hA2 hB1 hB2 hC hD hE1 hE2
  restore := restore_of_freq hTL hA1 hA2 hB1 hB2 hC hD hE1 hE2 hES
  rankFreeCoupling := hRF

end BlockBand.SourceProcess.SourcePins
