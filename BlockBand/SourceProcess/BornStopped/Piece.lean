module

public import BlockBand.SourceProcess.BornStopped.Agree
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorCond
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AssemblyLaw
public import BlockBand.SourceProcess.BornUnique.Stopped

/-!
# One piece: a born solution conditioned on a `𝓖₀`-event without births in `(0, r]`

* `martingale_min`: a martingale stopped at a deterministic time is a martingale.
* `isGramHorizonSolution_tilde`: conditioned on a `𝓖₀`-event `E` of positive mass on which no
  birth lies in `(0, r]`, `tildeG = (G - J) + J(0)` solves the Gram martingale problem up to
  the horizon `r` (`IsGramHorizonSolution`). The clauses are those of `G` stopped at `r`, and
  conditioning on `𝓖₀`-events keeps them (`martingale_cond`).
* `piece_law`: with `GramHorizonLaw`, if `(z, (G - J)(0))` has the same law for two born
  solutions with births `b(z)`, then for every measurable `S` without births in `(0, r]`, the
  conditional laws of `tildeG(r)` given `{z ∈ S}` agree.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

section Mart

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- A martingale stopped at the deterministic time `r` is a martingale. -/
theorem martingale_min [IsFiniteMeasure Q] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {N : ℝ≥0 → Ω → E} (hN : Martingale N 𝓖 Q) (r : ℝ≥0) :
    Martingale (fun t => N (min t r)) 𝓖 Q := by
  refine ⟨fun t => (hN.1 (min t r)).mono (𝓖.mono (min_le_left _ _)), fun s t hst => ?_⟩
  by_cases hs : r ≤ s
  · have h1 : min t r = r := min_eq_right (hs.trans hst)
    have h2 : min s r = r := min_eq_right hs
    simp only [h1, h2]
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (𝓖.le s)
      ((hN.1 r).mono (𝓖.mono hs)) (hN.integrable r))
  · have hsr : s ≤ r := (le_of_not_ge hs)
    have h2 : min s r = s := min_eq_left hsr
    simp only [h2]
    exact hN.condExp_ae_eq (le_min hst hsr)

end Mart

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] {D0 : ℝ} {D : Matrix c c ℂ}
  {j : F → GramState c}

/-- **The conditioned birth-free part solves the Gram problem up to `r`.** -/
theorem isGramHorizonSolution_tilde {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {β : Ω → F → ℝ} {G : ℝ≥0 → Ω → GramState c}
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G)
    {E : Set Ω} (hE : MeasurableSet[𝓖 0] E) (hE0 : Q E ≠ 0) {r : ℝ≥0}
    (hr : ∀ ω ∈ E, ∀ f, β ω f ≤ 0 ∨ (r : ℝ) < β ω f) :
    IsGramHorizonSolution (Q[|E]) 𝓖 D0 D r (tildeG j β G) where
  adapted t := ((hG.adapted t).sub ((hG.jump t).mono (𝓖.mono (zero_le (a := t))))).add
    ((hG.jump 0).mono (𝓖.mono (zero_le (a := t))))
  continuous := ae_cond_of_ae (by
    filter_upwards [hG.continuous] with ω h
    exact h.add continuous_const) E
  feasible := by
    filter_upwards [ae_cond_of_ae hG.feasible E, ae_cond_mem (𝓖.le 0 _ hE)] with ω h hω t ht
    rw [tildeG_eq (hr ω hω) ht]
    exact h t
  drift K e := by
    obtain ⟨N, hN, hNX⟩ := hG.drift K e
    refine ⟨fun t => N (min t r), martingale_cond (martingale_min hN r) hE hE0, fun t => ?_⟩
    filter_upwards [ae_cond_of_ae (hNX (min t r)) E, ae_cond_mem (𝓖.le 0 _ hE)] with ω h hω
    rw [h]
    exact stopped_min_eq (fun u hu => bornCompensated_eq (hr ω hω) e hu)
      (min_gramTraceStop_eq (hr ω hω) K) t
  bracket K e e' := by
    obtain ⟨N, hN, hNX⟩ := hG.bracket K e e'
    refine ⟨fun t => N (min t r), martingale_cond (martingale_min hN r) hE hE0, fun t => ?_⟩
    filter_upwards [ae_cond_of_ae (hNX (min t r)) E, ae_cond_mem (𝓖.le 0 _ hE)] with ω h hω
    rw [h]
    refine stopped_min_eq (fun u hu => ?_) (min_gramTraceStop_eq (hr ω hω) K) t
    rw [bornCompensated_eq (hr ω hω) e hu, bornCompensated_eq (hr ω hω) e' hu,
      setIntegral_tildeG_eq (hr ω hω) (gramCovEntry D0 D e e') hu]

section Law

variable {Z : Type} [MeasurableSpace Z] {b : Z → F → ℝ}
  {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω}
  {z : Ω → Z} {G : ℝ≥0 → Ω → GramState c}
  {Ω' : Type} {m' : MeasurableSpace Ω'} {𝓖' : Filtration ℝ≥0 m'} {Q' : Measure Ω'}
  {z' : Ω' → Z} {G' : ℝ≥0 → Ω' → GramState c}

/-- `ω ↦ (z, (G - J)(0))` is measurable. -/
theorem measurable_startPair (hz : Measurable[𝓖 0] z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G) :
    Measurable fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  exact (hz.mono (𝓖.le 0) le_rfl).prodMk
    ((measurable_G hG 0).sub (measurable_of_stronglyMeasurable_gram (𝓖.le 0) (hG.jump 0)))

omit [DecidableEq c] in
/-- The map `(x, g) ↦ g + J_{b(x)}(0)` is measurable. -/
theorem measurable_addJump0 (hb : Measurable b) :
    Measurable fun p : Z × GramState c => p.2 + birthSum j (b p.1) ((0 : ℝ≥0) : ℝ) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  exact measurable_snd.add ((measurable_birthSum j _).comp (hb.comp measurable_fst))

omit [Fintype c] [DecidableEq c] [MeasurableSpace Z] in
theorem preimage_startPair (S : Set Z) (y : Ω → GramState c) :
    (fun ω => (z ω, y ω)) ⁻¹' (S ×ˢ Set.univ) = z ⁻¹' S := by
  ext ω; simp

/-- The events `{z ∈ S}` have equal masses for the two solutions. -/
theorem mass_eq (hz : Measurable[𝓖 0] z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G)
    (hz' : Measurable[𝓖' 0] z')
    (hG' : IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (b (z' ω)) (t : ℝ)) G')
    (h0 : Q.map (fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω)) =
      Q'.map (fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' 0 ω)))
    {S : Set Z} (hS : MeasurableSet S) : Q (z ⁻¹' S) = Q' (z' ⁻¹' S) := by
  have h := mass_eq_of_map_eq (measurable_startPair hz hG) (measurable_startPair hz' hG') h0
    (hS.prod MeasurableSet.univ)
  rwa [preimage_startPair, preimage_startPair] at h

/-- **Conditional laws on one piece without births in `(0, r]`.** -/
theorem piece_law (hH : GramHorizonLaw) (hD0 : 0 < D0) (hD : IsSignature D) (hb : Measurable b)
    [IsProbabilityMeasure Q] (hz : Measurable[𝓖 0] z)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (b (z ω)) (t : ℝ)) G)
    [IsProbabilityMeasure Q'] (hz' : Measurable[𝓖' 0] z')
    (hG' : IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (b (z' ω)) (t : ℝ)) G')
    (h0 : Q.map (fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω)) =
      Q'.map (fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' 0 ω)))
    {S : Set Z} (hS : MeasurableSet S) (hS0 : Q (z ⁻¹' S) ≠ 0) {r : ℝ≥0}
    (hr : ∀ x ∈ S, ∀ f, b x f ≤ 0 ∨ (r : ℝ) < b x f) :
    (Q[|z ⁻¹' S]).map (tildeG j (fun ω => b (z ω)) G r) =
      (Q'[|z' ⁻¹' S]).map (tildeG j (fun ω => b (z' ω)) G' r) := by
  have hS0' : Q' (z' ⁻¹' S) ≠ 0 := by rwa [← mass_eq hz hG hz' hG' h0 hS]
  have hf := measurable_startPair hz hG
  have hf' := measurable_startPair hz' hG'
  have hc := cond_map_eq_of_map_eq hf hf' h0 (hS.prod MeasurableSet.univ)
  rw [preimage_startPair, preimage_startPair] at hc
  have hinit : (Q[|z ⁻¹' S]).map (tildeG j (fun ω => b (z ω)) G 0) =
      (Q'[|z' ⁻¹' S]).map (tildeG j (fun ω => b (z' ω)) G' 0) := by
    have e : tildeG j (fun ω => b (z ω)) G 0 =
        (fun p : Z × GramState c => p.2 + birthSum j (b p.1) ((0 : ℝ≥0) : ℝ)) ∘
          fun ω => (z ω, bornCont j (fun ω => b (z ω)) G 0 ω) := rfl
    have e' : tildeG j (fun ω => b (z' ω)) G' 0 =
        (fun p : Z × GramState c => p.2 + birthSum j (b p.1) ((0 : ℝ≥0) : ℝ)) ∘
          fun ω => (z' ω, bornCont j (fun ω => b (z' ω)) G' 0 ω) := rfl
    rw [e, e', ← Measure.map_map (measurable_addJump0 hb) hf,
      ← Measure.map_map (measurable_addJump0 hb) hf', hc]
  exact hH c D0 D hD0 hD r Ω m 𝓖 (Q[|z ⁻¹' S]) _ (cond_isProbabilityMeasure hS0)
    (isGramHorizonSolution_tilde hG (hz hS) hS0 fun ω hω => hr _ hω) Ω' m' 𝓖' (Q'[|z' ⁻¹' S]) _
    (cond_isProbabilityMeasure hS0') (isGramHorizonSolution_tilde hG' (hz' hS) hS0'
      fun ω hω => hr _ hω) hinit

end Law

end BlockBand.SourceProcess.BornStopped
