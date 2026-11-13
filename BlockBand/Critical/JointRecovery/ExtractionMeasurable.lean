module

public import BlockBand.Critical.JointRecovery.Extraction
public import BlockBand.Critical.JointRecovery.MappingTheorem

/-!
# Borel measurability of the root/derivative extraction

Real-rootedness and simplicity of the real zeros of the energy axis are Borel conditions, so the
set `goodEntire` (`F(0) ≠ 0`, real-rooted axis, simple real zeros) is Borel; the extraction test,
set to `0` off the good pairs, is Borel measurable (`measurable_extractionTest`) and lies in
`[0, 1]` for nonnegative tests.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set Metric MeasureTheory
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction
open BlockBand.Internal.Contracts.CriticalEntire

variable {m : ℕ}

/-- Projection along a compact factor of a closed set is closed. -/
theorem isClosed_exists_mem_of_isCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) {P : X × Y → Prop} (hP : IsClosed {p | P p}) :
    IsClosed {x | ∃ y ∈ K, P (x, y)} := by
  have := isCompact_iff_compactSpace.mp hK
  have hS : IsClosed {q : X × K | P (q.1, q.2)} :=
    hP.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have himg := isClosedMap_fst_of_compactSpace _ hS
  convert himg using 1
  ext x
  constructor
  · rintro ⟨y, hy, hP⟩; exact ⟨(x, ⟨y, hy⟩), hP, rfl⟩
  · rintro ⟨⟨x', ⟨y, hy⟩⟩, hP, rfl⟩; exact ⟨y, hy, hP⟩

theorem continuous_axis_eval :
    Continuous fun p : EntireFunction (m + 1) × ℂ => axis p.1 p.2 :=
  EntireFunction.continuous_eval.comp
    (continuous_fst.prodMk (continuous_energySource.comp continuous_snd))

theorem continuous_axis_deriv :
    Continuous fun p : EntireFunction (m + 1) × ℂ => deriv (axis p.1) p.2 := by
  simp_rw [deriv_axis]
  exact (continuous_partialDerivValue 0).comp
    (continuous_fst.prodMk (continuous_energySource.comp continuous_snd))

/-- Compact pieces of the nonreal half-planes. -/
def nonrealPiece (n : ℕ) : Set ℂ := closedBall 0 n ∩ {w | 1 / ((n : ℝ) + 1) ≤ |w.im|}

theorem isCompact_nonrealPiece (n : ℕ) : IsCompact (nonrealPiece n) :=
  (isCompact_closedBall 0 n).inter_right
    (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))

/-- Compact pieces of the real axis. -/
def realPiece (n : ℕ) : Set ℂ := closedBall 0 n ∩ {w | w.im = 0}

theorem isCompact_realPiece (n : ℕ) : IsCompact (realPiece n) :=
  (isCompact_closedBall 0 n).inter_right (isClosed_eq Complex.continuous_im continuous_const)

/-- Real-rootedness is the complement of countably many closed conditions. -/
theorem setOf_realRooted_eq :
    {F : EntireFunction (m + 1) | RealRooted F} =
      (⋃ n : ℕ, {F | ∃ w ∈ nonrealPiece n, axis F w = 0})ᶜ := by
  ext F
  rw [mem_compl_iff, mem_iUnion]
  constructor
  · rintro h ⟨n, w, ⟨_, hw⟩, hz⟩
    have him : w.im = 0 := h w hz
    have hw' : 1 / ((n : ℝ) + 1) ≤ |w.im| := hw
    rw [him, abs_zero] at hw'
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h w hz
    by_contra him
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖w‖ (1 / |w.im|))
    apply h
    refine ⟨n, w, ⟨mem_closedBall.mpr ?_, ?_⟩, hz⟩
    · rw [dist_zero_right]; exact (le_max_left _ _).trans hn
    · have hpos : 0 < |w.im| := abs_pos.mpr him
      show 1 / ((n : ℝ) + 1) ≤ |w.im|
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / |w.im| ≤ n := (le_max_right _ _).trans hn
      rw [div_le_iff₀ hpos] at h1
      nlinarith

/-- Simplicity of real zeros is the complement of countably many closed conditions. -/
theorem setOf_simpleRealZeros_eq :
    {F : EntireFunction (m + 1) | SimpleRealZeros F} =
      (⋃ n : ℕ, {F | ∃ w ∈ realPiece n, axis F w = 0 ∧ deriv (axis F) w = 0})ᶜ := by
  ext F
  rw [mem_compl_iff, mem_iUnion]
  constructor
  · rintro h ⟨n, w, ⟨_, hw⟩, hz, hd⟩
    have hw0 : w.im = 0 := hw
    have hw' : ((w.re : ℝ) : ℂ) = w := Complex.ext rfl (by simp [hw0])
    exact (h : SimpleRealZeros F) w.re (by rw [hw']; exact hz) (by rw [hw']; exact hd)
  · intro h x hz hd
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact h ⟨n, x, ⟨mem_closedBall.mpr (by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hn),
      show ((x : ℂ)).im = 0 by simp⟩, hz, hd⟩

/-- The real-rooted entire functions form a Borel set. -/
theorem measurableSet_realRooted :
    MeasurableSet {F : EntireFunction (m + 1) | RealRooted F} := by
  rw [setOf_realRooted_eq]
  refine (MeasurableSet.iUnion fun n => ?_).compl
  exact (isClosed_exists_mem_of_isCompact (isCompact_nonrealPiece n)
    (P := fun p : EntireFunction (m + 1) × ℂ => axis p.1 p.2 = 0)
    (isClosed_eq continuous_axis_eval continuous_const)).measurableSet

/-- The entire functions with simple real axis zeros form a Borel set. -/
theorem measurableSet_simpleRealZeros :
    MeasurableSet {F : EntireFunction (m + 1) | SimpleRealZeros F} := by
  rw [setOf_simpleRealZeros_eq]
  refine (MeasurableSet.iUnion fun n => ?_).compl
  exact (isClosed_exists_mem_of_isCompact (isCompact_realPiece n)
    (P := fun p : EntireFunction (m + 1) × ℂ => axis p.1 p.2 = 0 ∧ deriv (axis p.1) p.2 = 0)
    ((isClosed_eq continuous_axis_eval continuous_const).inter
      (isClosed_eq continuous_axis_deriv continuous_const))).measurableSet

/-- Entire functions on which the extraction is continuous: `F(0) ≠ 0`, real-rooted axis,
simple real zeros. -/
def goodEntire (m : ℕ) : Set (EntireFunction (m + 1)) :=
  {F | F 0 ≠ 0} ∩ {F | RealRooted F} ∩ {F | SimpleRealZeros F}

/-- `goodEntire` is Borel. -/
theorem measurableSet_goodEntire : MeasurableSet (goodEntire m) :=
  (((isClosed_eq (continuous_eval_const 0) continuous_const).isOpen_compl.measurableSet).inter
    measurableSet_realRooted).inter measurableSet_simpleRealZeros

/-- Pairs `(t, F)` with `t > 0` and `F` good. -/
def goodPairs (m : ℕ) : Set (ℝ × EntireFunction (m + 1)) := Ioi 0 ×ˢ goodEntire m

/-- `goodPairs` is Borel. -/
theorem measurableSet_goodPairs : MeasurableSet (goodPairs m) :=
  measurableSet_Ioi.prod measurableSet_goodEntire

/-- The extraction integrand on good pairs, `0` elsewhere (Borel by continuity on a Borel
set). -/
def extractionTest (E : ℝ) (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ) :
    ℝ × EntireFunction (m + 1) → ℝ := by
  classical
  exact (goodPairs m).piecewise (fun p => extractionValue E p.1 f p.2) (fun _ => 0)

theorem extractionTest_of_mem {E : ℝ} {f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ}
    {p : ℝ × EntireFunction (m + 1)} (hp : p ∈ goodPairs m) :
    extractionTest E f p = extractionValue E p.1 f p.2 := by
  classical
  unfold extractionTest
  exact piecewise_eq_of_mem _ _ _ hp

/-- Continuity of the extraction integrand within the real-rooted pairs, at good pairs. -/
theorem continuousWithinAt_extractionValue {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    {p : ℝ × EntireFunction (m + 1)} (hp : p.1 > 0 ∧ p.2 0 ≠ 0 ∧ SimpleRealZeros p.2) :
    ContinuousWithinAt (fun q : ℝ × EntireFunction (m + 1) => extractionValue E q.1 f q.2)
      (univ ×ˢ {G | RealRooted G}) p := by
  have h := continuousWithinAt_extractionSum hρ hp.1 f hp.2.1 hp.2.2
  exact (Real.continuous_exp.continuousAt.comp_continuousWithinAt h.neg)

theorem goodPairs_subset : goodPairs m ⊆ univ ×ˢ {G : EntireFunction (m + 1) | RealRooted G} :=
  fun _ hp => ⟨mem_univ _, hp.2.1.2⟩

/-- **Borel measurability of the extraction test.** -/
theorem measurable_extractionTest {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ) :
    Measurable (extractionTest (m := m) E f) := by
  classical
  unfold extractionTest
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_goodPairs
  intro p hp
  exact (continuousWithinAt_extractionValue hρ f ⟨hp.1, hp.2.1.1, hp.2.2⟩).mono goodPairs_subset

/-- The extraction test is continuous within `goodPairs` at every good pair. -/
theorem continuousWithinAt_extractionTest {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    {p : ℝ × EntireFunction (m + 1)} (hp : p.1 > 0 ∧ p.2 0 ≠ 0 ∧ SimpleRealZeros p.2) :
    ContinuousWithinAt (extractionTest E f) (goodPairs m) p := by
  by_cases hmem : p ∈ goodPairs m
  · refine ((continuousWithinAt_extractionValue hρ f hp).mono goodPairs_subset).congr
      (fun q hq => extractionTest_of_mem hq) (extractionTest_of_mem hmem)
  · -- `p` has `F(0) ≠ 0` and simple zeros but is not real-rooted: it is not in the closure
    have hnot : ¬ RealRooted p.2 := fun h => hmem ⟨hp.1, ⟨⟨hp.2.1, h⟩, hp.2.2⟩⟩
    have hbot : 𝓝[goodPairs m] p = ⊥ := by
      rw [← notMem_closure_iff_nhdsWithin_eq_bot]
      intro hcl
      rcases (𝓝[goodPairs m] p).eq_or_neBot with h | h
      · exact (mem_closure_iff_nhdsWithin_neBot.mp hcl).ne h
      · exact hnot (realRooted_of_tendsto (l := 𝓝[goodPairs m] p)
          ((continuous_snd.tendsto p).mono_left nhdsWithin_le_nhds)
          ((eventually_mem_nhdsWithin).mono fun q hq => hq.2.1.2) hp.2.1)
    rw [ContinuousWithinAt, hbot]
    exact tendsto_bot

/-- For nonnegative tests the extraction test lies in `[0,1]`. -/
theorem abs_extractionTest_le_one {E : ℝ}
    {f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ} (hf : ∀ z, 0 ≤ f z)
    (p : ℝ × EntireFunction (m + 1)) : |extractionTest E f p| ≤ 1 := by
  classical
  unfold extractionTest
  by_cases hp : p ∈ goodPairs m
  · rw [piecewise_eq_of_mem _ _ _ hp, extractionValue, abs_of_pos (Real.exp_pos _),
      Real.exp_le_one_iff, neg_nonpos]
    exact tsum_nonneg fun _ => hf _
  · rw [piecewise_eq_of_notMem _ _ _ hp, abs_zero]; exact zero_le_one

end BlockBand.Critical.JointRecovery
