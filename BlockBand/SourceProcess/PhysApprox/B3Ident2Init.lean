module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Closed
public import BlockBand.SourceProcess.PhysApprox.B3Assembly2
public import BlockBand.SourceProcess.ComplexUniqueSegment.Extract

/-!
# The initial Gram state of the limit

Measure: the candidate's `Q`; at finite `W` the conditioned closed law. Domain: `FrameDomain`.

* `extK`, `initialGram_eq_extK`: `initialGram K π t h` depends only on `t_0, …, t_{K−1}`.
* `continuousAt_initialFrame`, `continuousAt_initialGram`: the initial frame is continuous in
  `(t_0, …, t_{K−1})` at every point with `t_k ≠ h²` (the cutoff indicator is locally constant).
* **`ae_tseq_ne`**: if `seqTraceMeasure ∘ tseq` has law `ρ[|A]`, `tseq` is a.s. a transmission
  sequence and `ρ` has no atom of any `t_k` at `h²` (`CapCond.NoAtom`), then a.s. no `tseq k` is
  `h²` (`seqExtract_seqTraceMeasure`).
* **`ae_initial_of_fddAll`**: if a.s. no `tseq k` is `h²`, the limit Gram state at time `0` is
  `initialGram K (Fin np) tseq h`, almost surely. At finite `W` the closed Gram state at `n_s` is
  `initialGram` of `physTseq` (`ae_b3ClosedGramAt_start_adm`, admissible frame), so the
  observables lie in the graph of `t ↦ initialGram t`; the limit lies in its closure
  (`ae_mem_of_fddAll`), and the closure meets the continuity set only in the graph.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CapLimit BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal

/-- The sequence `(r_0, …, r_{K−1}, 0, 0, …)`. -/
def extK (K : ℕ) (r : Fin K → ℝ) (n : ℕ) : ℝ := if hn : n < K then r ⟨n, hn⟩ else 0

theorem extK_val {K : ℕ} (r : Fin K → ℝ) (k : Fin K) : extK K r k.val = r k := by
  simp [extK, k.isLt]

theorem initialGram_eq_extK {K : ℕ} {π : Type*} (t : ℕ → ℝ) (h : ℝ) :
    initialGram K π t h = initialGram K π (extK K fun k => t k.val) h := by
  unfold initialGram
  congr 1
  funext x c
  rcases c with ⟨k, σ⟩ | p
  · simp only [initialFrame, extK_val]
  · rfl

theorem continuous_modeEntry (σ a : Fin 2) :
    Continuous fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector t σ a := by
  have h1 : Continuous fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))
  have hp : Continuous fun t : ℝ => ((Real.sqrt (1 + Real.sqrt t) / Real.sqrt 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      ((Real.continuous_sqrt.comp (continuous_const.add Real.continuous_sqrt)).div_const _)
  have hm : Continuous fun t : ℝ => ((Real.sqrt (1 - Real.sqrt t) / Real.sqrt 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      ((Real.continuous_sqrt.comp (continuous_const.sub Real.continuous_sqrt)).div_const _)
  refine h1.mul ?_
  unfold modeVector
  split_ifs
  · fin_cases a
    · simpa using hm
    · simpa using hp
  · fin_cases a
    · simpa using hp
    · refine hm.neg.congr fun t => ?_
      simp

theorem continuousAt_initialFrame {K : ℕ} {π : Type*} {h : ℝ} {r₀ : Fin K → ℝ}
    (hr : ∀ k, r₀ k ≠ h ^ 2) :
    ContinuousAt (fun r : Fin K → ℝ => initialFrame K π (extK K r) h) r₀ := by
  refine continuousAt_pi.2 fun x => continuousAt_pi.2 fun c => ?_
  rcases c with ⟨k, σ⟩ | p
  · have e : ∀ r : Fin K → ℝ, initialFrame K π (extK K r) h x (Sum.inl (k, σ)) =
        if x.1 = k ∧ h ^ 2 < r k then
          (((r k) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (r k) σ x.2 else 0 := fun r => by
      simp only [initialFrame, extK_val]
    simp only [e]
    have hcont : Continuous fun r : Fin K → ℝ =>
        (((r k) ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (r k) σ x.2 :=
      (continuous_modeEntry σ x.2).comp (continuous_apply k)
    rcases lt_or_gt_of_ne (hr k) with hlt | hgt
    · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      filter_upwards [(continuous_apply k).continuousAt.eventually (gt_mem_nhds hlt)] with r hrk
      split_ifs with hc
      · exact absurd hc.2 (not_lt.2 hrk.le)
      · rfl
    · by_cases hx : x.1 = k
      · refine hcont.continuousAt.congr ?_
        filter_upwards [(continuous_apply k).continuousAt.eventually (lt_mem_nhds hgt)]
          with r hrk
        split_ifs with hc
        · rfl
        · exact absurd ⟨hx, hrk⟩ hc
      · refine (continuousAt_const (y := (0 : ℂ))).congr (Eventually.of_forall fun r => ?_)
        dsimp only
        split_ifs with hc
        · exact absurd hc.1 hx
        · rfl
  · exact continuousAt_const

theorem continuousAt_initialGram {K np : ℕ} {h : ℝ} {r₀ : Fin K → ℝ}
    (hr : ∀ k, r₀ k ≠ h ^ 2) :
    ContinuousAt (fun r : Fin K → ℝ => initialGram K (Fin np) (extK K r) h) r₀ :=
  (ComplexUniqueSegment.continuous_gramPair' (modeProjection K)).continuousAt.comp
    (continuousAt_initialFrame hr)

/-- **No limit entrance coordinate is `h²`**, almost surely. -/
theorem ae_tseq_ne {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
    {ρ : Measure (Measure unitInterval)} {h : ℝ} {A : Set (Measure unitInterval)}
    (htm : Measurable tseq) (hseq : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω))
    (hlaw : Q.map (fun ω => seqTraceMeasure (tseq ω)) = ρ[|A]) (hA : CapCond.NoAtom ρ h) :
    ∀ᵐ ω ∂Q, ∀ k, tseq ω k ≠ h ^ 2 := by
  rw [ae_all_iff]
  intro k
  have hm : Measurable fun ω => seqTraceMeasure (tseq ω) := measurable_seqTraceMeasure.comp htm
  have h0 : Q ((fun ω => seqTraceMeasure (tseq ω)) ⁻¹' {ν | seqExtract ν k = h ^ 2}) = 0 := by
    rw [← Measure.map_apply hm (CapCond.measurableSet_extract_eq k _), hlaw]
    exact cond_absolutelyContinuous (hA k)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hseq] with ω hω hs heq
  apply hω
  show seqExtract (seqTraceMeasure (tseq ω)) k = h ^ 2
  rw [seqExtract_seqTraceMeasure hs]
  exact heq

/-- The labels of the start observables: Gram entries and the first `K` entrance coordinates. -/
abbrev IIdx (K np : ℕ) := (Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) ⊕ Fin K

/-- Their embedding into the observables of `complexObs`. -/
def iToL {K np : ℕ} : IIdx K np → LIdx K np :=
  Sum.elim (fun e => Sum.inl e) fun k => Sum.inr (Sum.inl k.val)

/-- The defect from the graph of `t ↦ initialGram t`. -/
def initDefect (K np : ℕ) (h : ℝ) (z : IIdx K np → ℂ) :
    Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np) → ℂ := fun e =>
  z (Sum.inl e) - gramEntry e (initialGram K (Fin np) (extK K fun k => (z (Sum.inr k)).re) h)

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ}
  {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {φ : ℕ → ℕ}
  {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
  {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}

/-- **The initial Gram state of the limit.** -/
theorem ae_initial_of_fddAll [IsProbabilityMeasure Q] {T : ℝ}
    (hD : FrameDomain b E τ m T s h K Vs) (hφ : Tendsto φ atTop atTop)
    (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc)
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0)
    (hne : ∀ᵐ ω ∂Q, ∀ k, tseq ω k ≠ h ^ 2) :
    ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin np) (tseq ω) h := by
  obtain ⟨⟨-, hb, hE1, hE2, -⟩, -, hτ, -, -, hVs⟩ := id hD
  have hb1 : b < 1 := by linarith
  set S : Set (IIdx K np → ℂ) := {z | initDefect K np h z = 0}
  have hu : ∀ (_ : IIdx K np) j, s + ((0 : ℝ≥0) : ℝ) ≠ τ j := fun _ j => by
    rw [NNReal.coe_zero, add_zero]; exact (hτ j).ne
  have hW : ∀ᶠ n in atTop, ∀ᵐ y ∂closedLaw b (φ n) np,
      y.1.1 ∈ physCapEventC b E s h K (φ n) →
        (fun l => b3ObsAll b E s h τ m (φ n) (Vs (φ n)) (iToL l) 0 y) ∈ closure S := by
    filter_upwards [hφ.eventually (hVs.and (eventually_ge_atTop 1))] with n hn
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw (φ n) b)
      (ν := Measure.pi fun _ : Fin np =>
        BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin (φ n)))).ae
      (ae_b3ClosedGramAt_start_adm (m := m) hb hE1 hE2 hn.2 hτ hn.1)
    have h2 := (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw (φ n) np b)
      (ν := phaseLaw)).ae h1
    refine h2.mono fun y hy _ => subset_closure ?_
    have e0 : limLenAll s (φ n) 0 = closeLen s (φ n) := by simp [limLenAll, closeLen]
    have hy' := hy y.1.2 y.2
    have hyy : ((y.1.1, y.1.2), y.2) = y := rfl
    rw [hyy] at hy'
    funext e
    simp only [initDefect, iToL, Sum.elim_inl, Sum.elim_inr, b3ObsAll, e0, hy',
      Complex.ofReal_re, Pi.zero_apply]
    rw [← initialGram_eq_extK, sub_self]
  have hmem := ae_mem_of_fddAll hb1 hE1 hE2 hF hobs hcap iToL (fun _ => 0) hu isClosed_closure hW
  filter_upwards [hmem, hne] with ω hω hne'
  set X : IIdx K np → ℂ := fun l => complexObs tseq G Kc (iToL l) 0 ω
  have hre : (fun k : Fin K => (X (Sum.inr k)).re) = fun k => tseq ω k.val := by
    funext k
    simp [X, iToL, complexObs]
  have hDc : ContinuousAt (initDefect K np h) X := by
    refine continuousAt_pi.2 fun e => (continuous_apply _).continuousAt.sub
      ((ClosedLimit.continuous_gramEntry e).continuousAt.comp ?_)
    have hr : ∀ k : Fin K, (fun k : Fin K => (X (Sum.inr k)).re) k ≠ h ^ 2 := fun k => by
      rw [hre]; exact hne' k.val
    have hf : ContinuousAt (fun z : IIdx K np → ℂ => fun k : Fin K => (z (Sum.inr k)).re) X :=
      (continuous_pi fun k : Fin K =>
        Complex.continuous_re.comp (continuous_apply (Sum.inr k))).continuousAt
    have hg : ContinuousAt (fun r : Fin K → ℝ => initialGram K (Fin np) (extK K r) h)
        ((fun z : IIdx K np → ℂ => fun k : Fin K => (z (Sum.inr k)).re) X) :=
      continuousAt_initialGram hr
    have h3 := hg.comp hf
    exact h3
  have h0 : initDefect K np h X = 0 := by
    have hcl := mem_closure_image hDc hω
    have hsub : initDefect K np h '' S ⊆ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hz
    exact closure_minimal hsub isClosed_singleton hcl
  have he : ∀ e, gramEntry e (G 0 ω) = gramEntry e (initialGram K (Fin np) (tseq ω) h) := by
    intro e
    have h1 := congrFun h0 e
    simp only [initDefect, Pi.zero_apply, sub_eq_zero] at h1
    rw [hre, ← initialGram_eq_extK] at h1
    exact h1
  rw [← gramOfEntries_gramEntry (G 0 ω),
    ← gramOfEntries_gramEntry (initialGram K (Fin np) (tseq ω) h)]
  exact congrArg gramOfEntries (funext he)

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
