module
public import BlockBand.Model.Construction.MarkedStateTopology

/-!
Countable compact-test reduction for vague measures.
Fixed-support approximation controls integrals by a cutoff coordinate; no
uniform bound on all locally finite configurations is assumed.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open MeasureTheory Set TopologicalSpace Filter
open scoped Topology NNReal ENNReal
variable (X : Type*) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem exists_stateCutoff (n : ℕ) :
    ∃ f : CompactlySupportedContinuousMap X ℝ,
      Set.EqOn f 1 ((CompactExhaustion.choice X) n) ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨f, h1, _, hs, hb⟩ := exists_continuous_one_zero_of_isCompact
    ((CompactExhaustion.choice X).isCompact n) isClosed_empty (by simp)
  exact ⟨⟨f, hs⟩, h1, hb⟩

def stateCutoff (n : ℕ) : CompactlySupportedContinuousMap X ℝ :=
  (exists_stateCutoff X n).choose

omit [MeasurableSpace X] [BorelSpace X] in
theorem stateCutoff_eq_one (n : ℕ) :
    Set.EqOn (stateCutoff X n) 1 ((CompactExhaustion.choice X) n) :=
  (exists_stateCutoff X n).choose_spec.1

omit [MeasurableSpace X] [BorelSpace X] in
theorem stateCutoff_mem_unitInterval (n : ℕ) (x : X) :
    stateCutoff X n x ∈ Set.Icc (0 : ℝ) 1 :=
  (exists_stateCutoff X n).choose_spec.2 x

def stateCountableTest (nm : ℕ × Option ℕ) : CompactlySupportedContinuousMap X ℝ :=
  match nm.2 with
  | none => stateCutoff X nm.1
  | some m =>
    { toFun := fun x => stateCutoff X nm.1 x * denseSeq C(X, ℝ) m x
      continuous_toFun := (stateCutoff X nm.1).continuous.mul (denseSeq C(X, ℝ) m).continuous
      hasCompactSupport' := (stateCutoff X nm.1).hasCompactSupport.mul_right }

omit [MeasurableSpace X] [BorelSpace X] [T2Space X] in
/-- A single countable family approximates every continuous map on every compact set. -/
theorem stateDenseSeq_approx (f : C(X, ℝ)) (K : Set X) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ x ∈ K, |denseSeq C(X, ℝ) m x - f x| < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ho : IsOpen {g : C(X, ℝ) | dist (g.restrict K) (f.restrict K) < ε} :=
    isOpen_lt ((ContinuousMap.continuous_restrict K).dist continuous_const) continuous_const
  have hf : f ∈ {g : C(X, ℝ) | dist (g.restrict K) (f.restrict K) < ε} := by
    simpa using hε
  obtain ⟨m, hg⟩ := (denseRange_denseSeq C(X, ℝ)).exists_mem_open ho ⟨f, hf⟩
  refine ⟨m, ?_⟩
  intro x hx
  have h := (ContinuousMap.dist_lt_iff hε).mp hg ⟨x,hx⟩
  simpa [Real.dist_eq] using h

omit [MeasurableSpace X] [BorelSpace X] in
/-- The cutoff family dominates the support of every compact test. -/
theorem exists_stateCutoff_eq_one (f : CompactlySupportedContinuousMap X ℝ) :
    ∃ n : ℕ, ∀ x ∈ tsupport f, stateCutoff X n x = 1 := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice X).exists_superset_of_isCompact f.hasCompactSupport
  exact ⟨n, fun x hx => stateCutoff_eq_one X n (hn hx)⟩

/-- Approximation error is controlled by the cutoff mass, uniformly
for every individual locally finite measure, without a global mass cap. -/
theorem stateCountableTest_integral_error (f : CompactlySupportedContinuousMap X ℝ)
    (n m : ℕ) (ε : ℝ) (_hε : 0 < ε)
    (hf : ∀ x ∈ tsupport f, stateCutoff X n x = 1)
    (ha : ∀ x ∈ tsupport (stateCutoff X n), |denseSeq C(X, ℝ) m x - f x| < ε)
    (ξ : VaguePointMeasure X) :
    |ξ.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate f| ≤
      ε * ξ.coordinate (stateCutoff X n) := by
  have hi (g : CompactlySupportedContinuousMap X ℝ) : Integrable g ξ.measure :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  rw [VaguePointMeasure.coordinate, VaguePointMeasure.coordinate, ← integral_sub (hi _) (hi _)]
  have hh : ∀ x, |stateCountableTest X (n, some m) x - f x| ≤ ε * stateCutoff X n x := by
    intro x
    have hprod : f x = stateCutoff X n x * f x := by
      by_cases h : f x = 0
      · simp [h]
      · rw [hf x (subset_tsupport f h), one_mul]
    rw [hprod]
    change |stateCutoff X n x * denseSeq C(X, ℝ) m x - stateCutoff X n x * f x| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (stateCutoff_mem_unitInterval X n x).1]
    by_cases hx : stateCutoff X n x = 0
    · simp [hx]
    · exact (mul_le_mul_of_nonneg_left (ha x (subset_tsupport _ hx)).le
        (stateCutoff_mem_unitInterval X n x).1).trans_eq (mul_comm _ _)
  have h := norm_integral_le_of_norm_le
    (f := fun x => stateCountableTest X (n, some m) x - f x)
    ((hi (stateCutoff X n)).const_mul ε)
    (ae_of_all ξ.measure (fun x => by simpa [Real.norm_eq_abs] using hh x))
  simpa [Real.norm_eq_abs, integral_const_mul, VaguePointMeasure.coordinate] using h

def stateCountableCoordinate (ξ : VaguePointMeasure X) (nm : ℕ × Option ℕ) : ℝ :=
  ξ.coordinate (stateCountableTest X nm)

/-- Every defining compact coordinate is continuous in the countable initial topology. -/
theorem continuous_coordinate_countableInitial (f : CompactlySupportedContinuousMap X ℝ) :
    @Continuous (VaguePointMeasure X) ℝ
      (TopologicalSpace.induced (stateCountableCoordinate X) Pi.topologicalSpace) inferInstance
      (fun ξ => ξ.coordinate f) := by
  let : TopologicalSpace (VaguePointMeasure X) :=
    TopologicalSpace.induced (stateCountableCoordinate X) Pi.topologicalSpace
  have hc (nm : ℕ × Option ℕ) : Continuous (fun ξ : VaguePointMeasure X =>
      ξ.coordinate (stateCountableTest X nm)) := by
    change Continuous (fun ξ : VaguePointMeasure X => stateCountableCoordinate X ξ nm)
    exact (continuous_apply nm).comp
      (continuous_induced_dom : Continuous (stateCountableCoordinate X))
  rw [continuous_iff_continuousAt]
  intro ξ
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨n, hn⟩ := exists_stateCutoff_eq_one X f
  have hnonneg : 0 ≤ ξ.coordinate (stateCutoff X n) :=
    integral_nonneg (fun x => (stateCutoff_mem_unitInterval X n x).1)
  let M : ℝ := ξ.coordinate (stateCutoff X n) + 1
  have hM : 0 < M := by dsimp [M]; linarith
  let δ := ε / (4 * M)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨m, hm⟩ := stateDenseSeq_approx X f.toContinuousMap
    (tsupport (stateCutoff X n)) (stateCutoff X n).hasCompactSupport δ hδ
  have hmass : ∀ᶠ η : VaguePointMeasure X in 𝓝 ξ,
      η.coordinate (stateCutoff X n) < M :=
    (hc (n, none)).continuousAt.eventually (gt_mem_nhds (by
      change ξ.coordinate (stateCutoff X n) < M
      dsimp [M]
      linarith))
  have hnear : ∀ᶠ η : VaguePointMeasure X in 𝓝 ξ,
      |η.coordinate (stateCountableTest X (n, some m)) -
        ξ.coordinate (stateCountableTest X (n, some m))| < ε / 2 := by
    have h := ((hc (n, some m)).tendsto ξ).eventually
      (Metric.ball_mem_nhds _ (half_pos hε))
    simpa [Metric.mem_ball, Real.dist_eq] using h
  filter_upwards [hmass, hnear] with η hη hnear
  have heη := stateCountableTest_integral_error X f n m δ hδ hn hm η
  have heξ := stateCountableTest_integral_error X f n m δ hδ hn hm ξ
  have hsum : |(η.coordinate f - η.coordinate (stateCountableTest X (n, some m))) +
      (η.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate (stateCountableTest X (n, some m))) +
      (ξ.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate f)| ≤
      |η.coordinate f - η.coordinate (stateCountableTest X (n, some m))| +
      |η.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate (stateCountableTest X (n, some m))| +
      |ξ.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate f| := by
    have h1 := abs_add_le (η.coordinate f - η.coordinate (stateCountableTest X (n, some m)))
      (η.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate (stateCountableTest X (n, some m)))
    have h2 := abs_add_le
      ((η.coordinate f - η.coordinate (stateCountableTest X (n, some m))) +
        (η.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate (stateCountableTest X (n, some m))))
      (ξ.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate f)
    linarith
  rw [abs_sub_comm] at heη
  have hδM : δ * M = ε / 4 := by dsimp [δ]; field_simp
  have hboundη : δ * η.coordinate (stateCutoff X n) < ε/4 := by
    rw [← hδM]; exact mul_lt_mul_of_pos_left hη hδ
  have hboundξ : δ * ξ.coordinate (stateCutoff X n) < ε/4 := by
    rw [← hδM]; apply mul_lt_mul_of_pos_left _ hδ; dsimp [M]; linarith
  rw [Real.dist_eq]
  have he : η.coordinate f - ξ.coordinate f =
      (η.coordinate f - η.coordinate (stateCountableTest X (n, some m))) +
      (η.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate (stateCountableTest X (n, some m))) +
      (ξ.coordinate (stateCountableTest X (n, some m)) - ξ.coordinate f) := by ring
  rw [he]
  linarith

/-- The entire vague topology equals this countable compact-test topology. -/
theorem vaguePointMeasure_countable_isInducing :
    Topology.IsInducing (stateCountableCoordinate X) := by
  constructor
  apply le_antisymm
  · exact (continuous_pi (fun nm => continuous_vaguePointMeasure_coordinate
      (stateCountableTest X nm))).le_induced
  · have h : @Continuous (VaguePointMeasure X) (VaguePointMeasure X)
        (TopologicalSpace.induced (stateCountableCoordinate X) Pi.topologicalSpace) inferInstance id := by
      let : TopologicalSpace (VaguePointMeasure X) :=
        TopologicalSpace.induced (stateCountableCoordinate X) Pi.topologicalSpace
      rw [continuous_induced_rng]
      exact continuous_pi (fun f => continuous_coordinate_countableInitial X f)
    simpa only [induced_id] using h.le_induced

theorem vaguePointMeasure_pseudoMetrizableSpace : PseudoMetrizableSpace (VaguePointMeasure X) :=
  (vaguePointMeasure_countable_isInducing X).pseudoMetrizableSpace

theorem vaguePointMeasure_secondCountableTopology : SecondCountableTopology (VaguePointMeasure X) :=
  (vaguePointMeasure_countable_isInducing X).secondCountableTopology

theorem vaguePointMeasure_hasOuterApproxClosed : HasOuterApproxClosed (VaguePointMeasure X) := by
  have := vaguePointMeasure_pseudoMetrizableSpace X
  infer_instance

end BlockBand.Model.Construction
