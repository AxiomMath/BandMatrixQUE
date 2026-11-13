module

public import BlockBand.LocalWindow.ProofPartOneLocal
public import BlockBand.LocalWindow.ProofPartOneMeasurable
public import BlockBand.LocalWindow.ProofCertificateTransfer

/-!
# The averaged local law on a grid, conditional on `ω`

A union bound over a finite energy grid for the failure of the averaged local law of the fresh
pair block, conditionally on the exterior data, for part (i) of the physical local-window lemma.

## Main results

* `prod_inter_le_of_section`: conditional Fubini for a measurable set intersected with an
  arbitrary (possibly non-measurable) good set of first coordinates.
* `PoissonBad`: the failure of `dηv₀ - d^δ ≤ Σ P_η ≤ dη/v₀ + d^δ`, `Σ P_{Lη} ≤ dLη/v₀ + d^δ`
  (deterministic thresholds, so the bad set does not involve the random root `m`);
  `measurableSet_poissonBad`.
* `HasRegularRoot`: a root `m = ⟨(F - z - s m)⁻¹⟩` with `v₀ ≤ Im m ≤ v₀⁻¹` (the output of
  `ProofCertificate.poleCertificate_regular`).
* **`gue_poissonBad_le`**: for fixed `F`, `GUE_d(s/d){PoissonBad(F + G - e)} ≤ 2 d^{-D}` (two
  applications of `gue_poisson_bad_le`, heights `η` and `Lη`).
* `measure_univ_of_isPairSplitting`, `measurable_truncA` (via `measurable_truncF`).
* `LocalGood`, `LocalBadEvent`; **`splitLaw_localBad_le`**:
  `splitLaw(LocalBadEvent) ≤ |Es| · 2 d^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartOne

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.LawBridge
open BlockBand.LocalWindow.ProofCertificate BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section Fubini

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **Conditional Fubini with an arbitrary good set.** If `S ⊆ X × Y` is measurable and every
section `S_x`, `x ∈ Good`, has `ν`-measure `≤ a`, then `(μ ⊗ ν)(S ∩ Good × Y) ≤ a μ(X)`.
`Good` need not be measurable (it is enlarged to the measurable `{x | ν(S_x) ≤ a}`). -/
theorem prod_inter_le_of_section (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {S : Set (X × Y)} (hS : MeasurableSet S) {Good : Set X} {a : ℝ≥0∞}
    (h : ∀ x ∈ Good, ν (Prod.mk x ⁻¹' S) ≤ a) :
    μ.prod ν {z | z ∈ S ∧ z.1 ∈ Good} ≤ a * μ Set.univ := by
  set f : X → ℝ≥0∞ := fun x => ν (Prod.mk x ⁻¹' S)
  have hf : Measurable f := measurable_measure_prodMk_left hS
  set G' : Set X := {x | f x ≤ a}
  have hG' : MeasurableSet G' := measurableSet_le hf measurable_const
  have hS' : MeasurableSet (S ∩ Prod.fst ⁻¹' G') := hS.inter (measurable_fst hG')
  calc μ.prod ν {z | z ∈ S ∧ z.1 ∈ Good} ≤ μ.prod ν (S ∩ Prod.fst ⁻¹' G') :=
        measure_mono fun z hz => ⟨hz.1, h _ hz.2⟩
    _ = ∫⁻ x, ν (Prod.mk x ⁻¹' (S ∩ Prod.fst ⁻¹' G')) ∂μ := Measure.prod_apply hS'
    _ ≤ ∫⁻ _, a ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ G'
        · exact (measure_mono Set.inter_subset_left).trans hx
        · have : Prod.mk x ⁻¹' (S ∩ Prod.fst ⁻¹' G') = ∅ := by
            ext y; simp [hx]
          rw [this, measure_empty]; exact bot_le
    _ = a * μ Set.univ := lintegral_const a

end Fubini

section Bad

/-- The **Poisson-bad event** at one energy (deterministic thresholds):
with `d = 2W`, the measurable Poisson sums `Σ P_η`, `Σ P_{Lη}` of a matrix `A` violate
`d η v₀ - d^δ ≤ Σ P_η ≤ d η/v₀ + d^δ` or `Σ P_{Lη} ≤ d Lη/v₀ + d^δ`. -/
def PoissonBad {ι : Type} [Fintype ι] [DecidableEq ι] (d δ v₀ η L : ℝ) (A : Matrix ι ι ℂ) :
    Prop :=
  BlockBand.Window.Count.spectralSum (poissonWeight η) A < d * η * v₀ - d ^ δ ∨
    d * η / v₀ + d ^ δ < BlockBand.Window.Count.spectralSum (poissonWeight η) A ∨
    d * (L * η) / v₀ + d ^ δ < BlockBand.Window.Count.spectralSum (poissonWeight (L * η)) A

theorem measurableSet_poissonBad {ι : Type} [Fintype ι] [DecidableEq ι] (d δ v₀ η L : ℝ) :
    MeasurableSet {A : Matrix ι ι ℂ | PoissonBad d δ v₀ η L A} := by
  have h1 := BlockBand.Window.Count.measurable_spectralSum (ι := ι) (measurable_poissonWeight η)
  have h2 := BlockBand.Window.Count.measurable_spectralSum (ι := ι)
    (measurable_poissonWeight (L * η))
  exact (measurableSet_lt h1 measurable_const).union
    ((measurableSet_lt measurable_const h1).union (measurableSet_lt measurable_const h2))

/-- The root hypothesis at one height: a positive root `m = ⟨(F - z - s m)⁻¹⟩`,
`z = e + iη`, with `v₀ ≤ Im m ≤ v₀⁻¹` (the conclusion of `poleCertificate_regular`). -/
def HasRegularRoot {ι : Type} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ) (s v₀ e η : ℝ) :
    Prop :=
  ∃ m : ℂ, m = BlockBand.Palm.certificateMatrixTrace F ((e : ℂ) + Complex.I * η + s * m) ∧
    v₀ ≤ m.im ∧ m.im ≤ v₀⁻¹

theorem isHermitian_add_sub_smul {ι : Type} [Fintype ι] [DecidableEq ι] {F G : Matrix ι ι ℂ}
    (hF : F.IsHermitian) (hG : G.IsHermitian) (e : ℝ) :
    (F + G - (e : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian :=
  (hF.add hG).sub (by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal])

/-- **The averaged local law at one energy, both heights, deterministic thresholds.** Fixed `A, C`
and `ε, δ, D > 0` first; then `N₀`; for every `p`, pair `i` with `d = 2W ≥ N₀`, `s > 0`, Hermitian
`F` with `s^{-1/2}‖F‖ ≤ C d^A`, real `e`, `η > 0`, `L ≥ 1`, `v₀ > 0` with regular roots
(`v₀ ≤ Im m ≤ v₀⁻¹`) at heights `η` and `Lη`, the domain condition `d^ε ≤ d η v₀/π` and
`|e + iη|, |e + iLη| ≤ √s d^{A + 1/ε}`:
`GUE_d(s/d){G : PoissonBad d δ v₀ η L (F + G - e)} ≤ 2 d^{-D}`. Hypotheses:
`PairGUELawBridgeStatement`, `ExternalLocalGUE` and `MDEBranchIdentification` (through
`gue_poisson_bad_le`). -/
theorem gue_poissonBad_le (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (A C ε δ D : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W → ∀ s : ℝ, 0 < s →
      ∀ F : PairMatrix p i, F.IsHermitian →
        (Real.sqrt s)⁻¹ * ‖F‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
        ∀ e η L v₀ : ℝ, 0 < η → 1 ≤ L → 0 < v₀ →
          HasRegularRoot F s v₀ e η → HasRegularRoot F s v₀ e (L * η) →
          ((2 * p.W : ℕ) : ℝ) ^ ε ≤ ((2 * p.W : ℕ) : ℝ) * η * (v₀ / Real.pi) →
          ‖(e : ℂ) + Complex.I * η‖ ≤ Real.sqrt s * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / ε) →
          ‖(e : ℂ) + Complex.I * ((L * η : ℝ) : ℂ)‖ ≤
            Real.sqrt s * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / ε) →
          gueMeasure (PairSite p i) (pairTime p s)
              {G | PoissonBad ((2 * p.W : ℕ) : ℝ) δ v₀ η L (F + G - (e : ℂ) • 1)} ≤
            2 * ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀, h⟩ := gue_poisson_bad_le hBridge hELG hMDE A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun p i hN s hs F hF hFn e η L v₀ hη hL hv₀ hr1 hr2 hdom hz1 hz2 => ?_⟩
  set d : ℝ := ((2 * p.W : ℕ) : ℝ) with hd_def
  have hd : 0 < d := by
    have := p.W_pos
    rw [hd_def]; exact_mod_cast (by omega : 0 < 2 * p.W)
  obtain ⟨m, hm, hm1, hm2⟩ := hr1
  obtain ⟨m', hm', hm1', hm2'⟩ := hr2
  have hLη : 0 < L * η := mul_pos (by linarith) hη
  have hpi := Real.pi_pos
  have hdom1 : d ^ ε ≤ d * η * (m.im / Real.pi) :=
    hdom.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hm1 hpi.le)
      (mul_pos hd hη).le)
  have hdom2 : d ^ ε ≤ d * (L * η) * (m'.im / Real.pi) := by
    refine hdom.trans (mul_le_mul (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left hη.le hL) hd.le) (div_le_div_of_nonneg_right hm1' hpi.le)
      (div_nonneg hv₀.le hpi.le) (mul_pos hd hLη).le)
  have hb1 := h p i hN s hs F hF hFn e η hη m (hv₀.trans_le hm1) hm hdom1 hz1
  have hb2 := h p i hN s hs F hF hFn e (L * η) hLη m' (hv₀.trans_le hm1') hm' hdom2 hz2
  set μ := gueMeasure (PairSite p i) (pairTime p s)
  have hnull : μ {G | ¬ G.IsHermitian} = 0 := by
    have := BlockBand.Angular.PairCoareaBridge.ae_gueMeasure_isHermitian (PairSite p i)
      (pairTime p s)
    rwa [ae_iff] at this
  have hsub : {G : PairMatrix p i | PoissonBad d δ v₀ η L (F + G - (e : ℂ) • 1)} ⊆
      ({G | d ^ δ < |spectralSum (F + G - (e : ℂ) • 1) (poissonWeight η) - d * η * m.im|} ∪
        {G | d ^ δ < |spectralSum (F + G - (e : ℂ) • 1) (poissonWeight (L * η)) -
          d * (L * η) * m'.im|}) ∪ {G | ¬ G.IsHermitian} := by
    intro G hG
    by_cases hG' : G.IsHermitian
    · have hA := isHermitian_add_sub_smul hF hG' e
      simp only [Set.mem_union, Set.mem_ofPred_eq, PoissonBad] at hG ⊢
      left
      rw [← spectralSum_eq_count hA, ← spectralSum_eq_count hA] at hG
      have e1 : d * η * v₀ ≤ d * η * m.im := mul_le_mul_of_nonneg_left hm1 (mul_pos hd hη).le
      have e2 : d * η * m.im ≤ d * η / v₀ := by
        rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hm2 (mul_pos hd hη).le
      have e3 : d * (L * η) * m'.im ≤ d * (L * η) / v₀ := by
        rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hm2' (mul_pos hd hLη).le
      have hdδ : 0 < d ^ δ := Real.rpow_pos_of_pos hd δ
      rcases hG with hG | hG | hG
      · left
        rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
      · left
        rw [abs_of_pos (by linarith)]; linarith
      · right
        rw [abs_of_pos (by linarith)]; linarith
    · right; exact hG'
  calc μ {G | PoissonBad d δ v₀ η L (F + G - (e : ℂ) • 1)}
      ≤ μ ((_ ∪ _) ∪ {G | ¬ G.IsHermitian}) := measure_mono hsub
    _ ≤ μ (_ ∪ _) + μ {G | ¬ G.IsHermitian} := measure_union_le _ _
    _ ≤ (ENNReal.ofReal (d ^ (-D)) + ENNReal.ofReal (d ^ (-D))) + 0 := by
        rw [hnull]
        exact add_le_add ((measure_union_le _ _).trans (add_le_add hb1 hb2)) le_rfl
    _ = 2 * ENNReal.ofReal (d ^ (-D)) := by rw [add_zero, two_mul]

end Bad

section Grid

variable (p : Parameters) (i : ZMod p.n)

/-- Under an exact pair splitting, `Pω` has total mass one. -/
theorem measure_univ_of_isPairSplitting {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (h : IsPairSplitting p i model s Pω) : Pω Set.univ = 1 := by
  have hprob : IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p s)) := by
    unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
    infer_instance
  have h1 := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) h
  rw [Measure.map_apply (BlockBand.Angular.PairCoareaBridge.measurable_assemble p i)
    MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod] at h1
  simpa using h1

/-- `x ↦ F̂_{ω}(e) + G - e` is measurable on the split space (`ε₀ > 0`). -/
theorem measurable_truncA {ε₀ : ℝ} (hε₀ : 0 < ε₀) (e : ℝ) :
    Measurable (fun x : SplitState p i × PairMatrix p i =>
      truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e + x.2 - (e : ℂ) • (1 : PairMatrix p i)) := by
  have h1 : Measurable (fun x : SplitState p i × PairMatrix p i =>
      truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e) := (measurable_truncF hε₀ e).comp measurable_fst
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply]
  exact (((measurable_pi_apply b).comp ((measurable_pi_apply a).comp h1)).add
    ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd))).sub
    measurable_const

/-- The good exterior states at a grid energy `e`: `V` Hermitian, `s^{-1/2}‖F̂(e)‖ ≤ C d^A`,
regular roots at heights `η` and `Lη` (from the norm event and the pole certificate). -/
def LocalGood (ε₀ A C v₀ η L e : ℝ) : Set (SplitState p i) :=
  {om | om.2.2.IsHermitian ∧
    (Real.sqrt (splitS p))⁻¹ * ‖truncF ε₀ om.1 om.2.1 om.2.2 e‖ ≤
      C * ((2 * p.W : ℕ) : ℝ) ^ A ∧
    HasRegularRoot (truncF ε₀ om.1 om.2.1 om.2.2 e) (splitS p) v₀ e η ∧
    HasRegularRoot (truncF ε₀ om.1 om.2.1 om.2.2 e) (splitS p) v₀ e (L * η)}

/-- The **averaged local-law failure event on a grid**: some grid energy
`e ∈ Es` at which the exterior state is good but the fresh block is Poisson-bad. -/
def LocalBadEvent (ε₀ A C v₀ η L δ : ℝ) (Es : Finset ℝ) : Set (SplitState p i × PairMatrix p i) :=
  {x | ∃ e ∈ Es, x.1 ∈ LocalGood p i ε₀ A C v₀ η L e ∧
    PoissonBad ((2 * p.W : ℕ) : ℝ) δ v₀ η L
      (truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e + x.2 - (e : ℂ) • 1)}

end Grid

/-- **The averaged local law on a grid, conditional on `ω`** (conditional Fubini under
`splitLaw = Pω ⊗ GUE_d(s/d)`). Fixed `A, C` and `ε, δ, D > 0` first; then `N₀`; for every `p`,
model, pair `i`, splitting law `Pω` at `s = splitS p` with `d = 2W ≥ N₀`, `ε₀ > 0`, finite grid
`Es`, `η > 0`, `L ≥ 1`, `v₀ > 0` with `d^ε ≤ d η v₀/π` and
`|e + iη|, |e + iLη| ≤ √s d^{A + 1/ε}` on `Es`: `splitLaw(LocalBadEvent) ≤ |Es| · 2 d^{-D}`.
Hypotheses: `PairGUELawBridgeStatement`, `ExternalLocalGUE` and `MDEBranchIdentification`. The
bad set is measurable (`measurable_truncF`), so no measurability hypothesis is needed. -/
theorem splitLaw_localBad_le (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (A C ε δ D : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      N₀ ≤ 2 * p.W → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ (Es : Finset ℝ) (η L v₀ : ℝ), 0 < η → 1 ≤ L →
        0 < v₀ → ((2 * p.W : ℕ) : ℝ) ^ ε ≤ ((2 * p.W : ℕ) : ℝ) * η * (v₀ / Real.pi) →
        (∀ e ∈ Es, ‖(e : ℂ) + Complex.I * η‖ ≤
            Real.sqrt (splitS p) * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / ε) ∧
          ‖(e : ℂ) + Complex.I * ((L * η : ℝ) : ℂ)‖ ≤
            Real.sqrt (splitS p) * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / ε)) →
        splitLaw p i Pω (LocalBadEvent p i ε₀ A C v₀ η L δ Es) ≤
          Es.card * (2 * ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D))) := by
  obtain ⟨N₀, hN₀, h⟩ := gue_poissonBad_le hBridge hELG hMDE A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun p model i Pω hPω hN ε₀ hε₀ Es η L v₀ hη hL hv₀ hdom hz => ?_⟩
  set a : ℝ≥0∞ := 2 * ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D))
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsub : LocalBadEvent p i ε₀ A C v₀ η L δ Es ⊆ ⋃ e ∈ Es,
      {x | x ∈ (fun x : SplitState p i × PairMatrix p i =>
          truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e + x.2 - (e : ℂ) • (1 : PairMatrix p i)) ⁻¹'
            {B | PoissonBad ((2 * p.W : ℕ) : ℝ) δ v₀ η L B} ∧
        x.1 ∈ LocalGood p i ε₀ A C v₀ η L e} := by
    rintro x ⟨e, he, hg, hb⟩
    exact Set.mem_biUnion he ⟨hb, hg⟩
  have hone : ∀ e ∈ Es, splitLaw p i Pω {x | x ∈ (fun x : SplitState p i × PairMatrix p i =>
          truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e + x.2 - (e : ℂ) • (1 : PairMatrix p i)) ⁻¹'
            {B | PoissonBad ((2 * p.W : ℕ) : ℝ) δ v₀ η L B} ∧
        x.1 ∈ LocalGood p i ε₀ A C v₀ η L e} ≤ a := by
    intro e he
    have hS := (measurable_truncA p i hε₀ e) (measurableSet_poissonBad ((2 * p.W : ℕ) : ℝ) δ v₀ η L)
    have := prod_inter_le_of_section Pω (gueMeasure (PairSite p i) (pairTime p (splitS p))) hS
      (Good := LocalGood p i ε₀ A C v₀ η L e) (a := a) (fun om hom => by
        obtain ⟨hV, hn, hr1, hr2⟩ := hom
        exact h p i hN (splitS p) hs _ (isHermitian_truncF ε₀ om.1 om.2.1 hV e) hn e η L v₀
          hη hL hv₀ hr1 hr2 hdom (hz e he).1 (hz e he).2)
    rwa [measure_univ_of_isPairSplitting p i hPω, mul_one] at this
  calc splitLaw p i Pω (LocalBadEvent p i ε₀ A C v₀ η L δ Es)
      ≤ ∑ e ∈ Es, splitLaw p i Pω {x | x ∈ (fun x : SplitState p i × PairMatrix p i =>
          truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e + x.2 - (e : ℂ) • (1 : PairMatrix p i)) ⁻¹'
            {B | PoissonBad ((2 * p.W : ℕ) : ℝ) δ v₀ η L B} ∧
        x.1 ∈ LocalGood p i ε₀ A C v₀ η L e} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _e ∈ Es, a := Finset.sum_le_sum hone
    _ = Es.card * a := by rw [Finset.sum_const, nsmul_eq_mul]

end BlockBand.LocalWindow.ProofPartOne
