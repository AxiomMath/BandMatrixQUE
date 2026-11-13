module

public import BlockBand.Coarea.Native.BlockBand.Counting.VagueRationalWindowTopology
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalUnfoldedRestrictionExponential

/-!
# Physical Gaussian-ring counting sequences

This module places a varying sequence of `GaussianRing.Law`s, whose parameter
and sample-space types may vary with the index, in the common ambient
`VagueRationalWindowState`.  The unconditional physical multi-block estimates give
coordinate exponential moments and the first-moment tails needed for a diagonal
compact-containment argument.  The constants retain the paper's normalization
`(C / sqrt cᵢ) / ρᵢ`; explicit uniform positive lower bounds on `sqrt cᵢ` and `ρᵢ`
then give tightness and a weakly convergent subsequence.

Measurability of the sharp finite local-window encoding is recorded explicitly.  This
is the boundary-measurability obligation already isolated by the physical
finite-state construction, not a replacement of the physical law by a BlockGUE law.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace GaussianRing

/-- A varying sequence of physical Gaussian-ring ensembles in one common
unfolded vague state space.  Both the physical parameter type and the sample type of
`model i` are allowed to vary with `i`.

The scale assumption is the paper's normalization `nᵢ Wᵢ ≤ Lᵢ`.  The last four
fields are precisely the uniform positive lower assumptions used for tightness. -/
structure PhysicalGaussianRingCountingSequence (input : PSSSInput.{0}) where
  params : ℕ → Params
  model : ∀ i, Law.{0} (params i)
  energy : ℕ → ℝ
  scale : ℕ → ℝ
  density : ℕ → ℝ
  scale_pos : ∀ i, 0 < scale i
  density_pos : ∀ i, 0 < density i
  dimension_le_scale : ∀ i,
    ((params i).n * (params i).W : ℝ) ≤ scale i
  state_measurable : ∀ i, Measurable
    ((model i).physicalUnfoldedVagueState (energy i) (scale i) (density i))
  sqrtCoupling_lower : ℝ
  sqrtCoupling_lower_pos : 0 < sqrtCoupling_lower
  sqrtCoupling_lower_le : ∀ i,
    sqrtCoupling_lower ≤ Real.sqrt (params i).c
  density_lower : ℝ
  density_lower_pos : 0 < density_lower
  density_lower_le : ∀ i, density_lower ≤ density i

/-- The physical unfolded vague state at the `i`th index. -/
def PhysicalGaussianRingCountingSequence.state
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) : (seq.model i).Ω → VagueRationalWindowState :=
  (seq.model i).physicalUnfoldedVagueState
    (seq.energy i) (seq.scale i) (seq.density i)

/-- The physical state map is measurable by the explicit sharp-window obligation in
the sequence data. -/
theorem PhysicalGaussianRingCountingSequence.measurable_state
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) : Measurable (seq.state i) :=
  seq.state_measurable i

/-- Pushforward of the physical Gaussian-ring sample law into the common vague
state space. -/
def PhysicalGaussianRingCountingSequence.law
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) : ProbabilityMeasure VagueRationalWindowState :=
  (seq.model i).physicalUnfoldedVagueLaw
    (seq.energy i) (seq.scale i) (seq.density i) (seq.state_measurable i)

/-- Coordinate mass of a physical unfolded state is exactly the symmetric
physical unfolded eigenvalue count. -/
theorem PhysicalGaussianRingCountingSequence.state_coordinate_mass
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) (ω : (seq.model i).Ω) (n : ℕ) :
    ((seq.state i ω) n).mass =
      (seq.model i).physicalUnfoldedIntervalCount
        (seq.energy i) (seq.scale i) (seq.density i) n ω := by
  rw [state, Law.physicalUnfoldedVagueState]
  change ((finiteMarkedRationalWindowPointState
    ((seq.model i).physicalUnfoldedFiniteConfiguration
      (seq.energy i) (seq.scale i) (seq.density i) ω)).window n).mass = _
  rw [finiteMarkedRationalWindowPointState_window_mass_eq_localCount]
  exact_mod_cast finiteMarkedLocalCount_physicalUnfolded_eq
    (seq.model i) (seq.energy i) (seq.scale i) (seq.density i)
    (seq.scale_pos i) (seq.density_pos i) ω (n : ℝ)

/-- The exact index-dependent unfolded mean bound.  Its intensity is
`(C / sqrt cᵢ) / ρᵢ`, with no uniform relaxation. -/
theorem PhysicalGaussianRingCountingSequence.physical_count_mean_le
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input)
    (i n : ℕ) :
    ∫ ω, ((seq.model i).physicalUnfoldedIntervalCount
      (seq.energy i) (seq.scale i) (seq.density i) n ω : ℝ)
        ∂(seq.model i).P ≤
      2 * (n : ℝ) *
        (physicalMultiBlockCountingConstant input (seq.params i) /
          seq.density i) := by
  let a := seq.energy i - n / (seq.scale i * seq.density i)
  let b := seq.energy i + n / (seq.scale i * seq.density i)
  have hs : 0 < seq.scale i * seq.density i :=
    mul_pos (seq.scale_pos i) (seq.density_pos i)
  have hab : a ≤ b := by
    dsimp [a, b]
    have hn : 0 ≤ (n : ℝ) / (seq.scale i * seq.density i) :=
      div_nonneg (Nat.cast_nonneg n) hs.le
    linarith
  have h := (seq.model i).physicalIntervalCount_factorial
    input hab 1 (by norm_num)
  change (∫ ω, ((((seq.model i).physicalIntervalCount a b ω).descFactorial 1 : ℕ) : ℝ)
      ∂(seq.model i).P) ≤ _ at h
  have hcount : (fun ω => ((seq.model i).physicalUnfoldedIntervalCount
      (seq.energy i) (seq.scale i) (seq.density i) n ω : ℝ)) =
      fun ω => ((((seq.model i).physicalIntervalCount a b ω).descFactorial 1 : ℕ) : ℝ) := by
    funext ω
    simp [Law.physicalUnfoldedIntervalCount, a, b]
  rw [hcount]
  calc
    (∫ ω, ((((seq.model i).physicalIntervalCount a b ω).descFactorial 1 : ℕ) : ℝ)
        ∂(seq.model i).P) ≤
        physicalMultiBlockCountingConstant input (seq.params i) *
          ((seq.params i).n * (seq.params i).W : ℝ) * (b - a) := by
      simpa using h
    _ ≤ 2 * (n : ℝ) *
        (physicalMultiBlockCountingConstant input (seq.params i) /
          seq.density i) := by
      have hK : 0 ≤ physicalMultiBlockCountingConstant input (seq.params i) := by
        exact div_nonneg input.C_nonneg (Real.sqrt_nonneg _)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [show b - a = 2 * (n : ℝ) /
          (seq.scale i * seq.density i) by
        dsimp [a, b]
        ring]
      calc
        _ ≤ physicalMultiBlockCountingConstant input (seq.params i) *
            seq.scale i *
              (2 * (n : ℝ) / (seq.scale i * seq.density i)) := by
          apply mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (seq.dimension_le_scale i) hK)
          exact div_nonneg (mul_nonneg (by norm_num) hn) hs.le
        _ = 2 * (n : ℝ) *
            (physicalMultiBlockCountingConstant input (seq.params i) /
              seq.density i) := by
          field_simp [ne_of_gt (seq.scale_pos i), ne_of_gt (seq.density_pos i)]

/-- The unconditional physical exponential estimate, retained with its exact
index-dependent constant `(C / sqrt cᵢ) / ρᵢ`. -/
theorem PhysicalGaussianRingCountingSequence.physical_count_exponential_le
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    ∫ ω, Real.exp (t * ((seq.model i).physicalUnfoldedIntervalCount
      (seq.energy i) (seq.scale i) (seq.density i) R ω : ℝ))
        ∂(seq.model i).P ≤
      Real.exp (2 * R *
        (physicalMultiBlockCountingConstant input (seq.params i) /
          seq.density i) * (Real.exp t - 1)) :=
  (seq.model i).physicalUnfoldedIntervalCount_exponential input
    (seq.energy i) (seq.scale i) (seq.density i) R t
    (seq.scale_pos i) (seq.density_pos i) hR
    (seq.dimension_le_scale i) ht

/-- Evaluation of a measurable vague event under the physical law is evaluation
of its preimage on the corresponding physical sample space. -/
theorem PhysicalGaussianRingCountingSequence.law_apply
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) {S : Set VagueRationalWindowState} (hS : MeasurableSet S) :
    (seq.law i : Measure VagueRationalWindowState) S =
      (seq.model i).P ((seq.state i) ⁻¹' S) := by
  change Measure.map (seq.state i) (seq.model i).P S = _
  exact Measure.map_apply (seq.measurable_state i) hS

/-- Markov tail for one coordinate of the physical law, with the exact
index-dependent `C / sqrt(cᵢ) / ρᵢ` normalization. -/
theorem PhysicalGaussianRingCountingSequence.coordinate_mass_tail_exact
    [OpensMeasurableSpace VagueRationalWindowState]
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input)
    (i n : ℕ) (R : ℝ) (hR : 0 < R) :
    (seq.law i : Measure VagueRationalWindowState)
        {ν | ENNReal.ofReal R < ((ν n).mass : ENNReal)} ≤
      ENNReal.ofReal ((2 * (n : ℝ) *
        (physicalMultiBlockCountingConstant input (seq.params i) /
          seq.density i)) / R) := by
  let E : Set VagueRationalWindowState :=
    {ν | ENNReal.ofReal R < ((ν n).mass : ENNReal)}
  have hE : MeasurableSet E := by
    unfold E
    have hof : ENNReal.ofReal R = (Real.toNNReal R : ENNReal) := rfl
    rw [hof]
    convert measurableSet_vagueRationalWindowState_mass_gt (Real.toNNReal R) n using 1
    ext ν
    exact_mod_cast Iff.rfl
  rw [seq.law_apply i hE]
  have hevent : (seq.state i) ⁻¹' E =
      {ω | R < ((seq.model i).physicalUnfoldedIntervalCount
        (seq.energy i) (seq.scale i) (seq.density i) n ω : ℝ)} := by
    ext ω
    simp only [E, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [seq.state_coordinate_mass i ω n, ENNReal.ofReal_lt_coe_iff hR.le]
    exact_mod_cast Iff.rfl
  rw [hevent]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    ENNReal.ofReal_ne_top).mp
  have hquot : 0 ≤ (2 * (n : ℝ) *
      (physicalMultiBlockCountingConstant input (seq.params i) /
        seq.density i)) / R := by
    unfold physicalMultiBlockCountingConstant
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (div_nonneg
          (div_nonneg input.C_nonneg (Real.sqrt_nonneg _))
          (seq.density_pos i).le)) hR.le
  rw [ENNReal.toReal_ofReal hquot]
  change (seq.model i).P.real {ω | R <
      ((seq.model i).physicalUnfoldedIntervalCount
        (seq.energy i) (seq.scale i) (seq.density i) n ω : ℝ)} ≤ _
  let N : (seq.model i).Ω → ℝ := fun ω =>
    ((seq.model i).physicalUnfoldedIntervalCount
      (seq.energy i) (seq.scale i) (seq.density i) n ω : ℝ)
  have hNint : Integrable N (seq.model i).P := by
    let a := seq.energy i - n / (seq.scale i * seq.density i)
    let b := seq.energy i + n / (seq.scale i * seq.density i)
    have hs : 0 < seq.scale i * seq.density i :=
      mul_pos (seq.scale_pos i) (seq.density_pos i)
    have hab : a ≤ b := by
      dsimp [a, b]
      have hn : 0 ≤ (n : ℝ) / (seq.scale i * seq.density i) :=
        div_nonneg (Nat.cast_nonneg n) hs.le
      linarith
    simpa [N, Law.physicalUnfoldedIntervalCount, a, b] using
      (seq.model i).physicalIntervalCount_factorialIntegrable input hab 1
  have hmarkov : R * (seq.model i).P.real {ω | R ≤ N ω} ≤
      ∫ ω, N ω ∂(seq.model i).P :=
    mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _) hNint R
  have hsubset : {ω | R < N ω} ⊆ {ω | R ≤ N ω} :=
    by
      intro ω hω
      change R < N ω at hω
      change R ≤ N ω
      exact le_of_lt hω
  have hprob : (seq.model i).P.real {ω | R < N ω} ≤
      (seq.model i).P.real {ω | R ≤ N ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
  apply (le_div_iff₀ hR).2
  calc
    (seq.model i).P.real {ω | R < N ω} * R ≤
        (seq.model i).P.real {ω | R ≤ N ω} * R :=
      mul_le_mul_of_nonneg_right hprob hR.le
    _ ≤ ∫ ω, N ω ∂(seq.model i).P := by
      simpa [mul_comm] using hmarkov
    _ ≤ 2 * (n : ℝ) *
        (physicalMultiBlockCountingConstant input (seq.params i) /
          seq.density i) := seq.physical_count_mean_le input i n

/-- Uniform unfolded mean bound following from the explicit lower bounds on
`sqrt cᵢ` and `ρᵢ`. -/
def PhysicalGaussianRingCountingSequence.uniformMeanBound
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (n : ℕ) : ℝ :=
  2 * (n : ℝ) * ((input.C / seq.sqrtCoupling_lower) / seq.density_lower)

/-- The exact physical mean constant is bounded by the uniform sequence constant. -/
theorem PhysicalGaussianRingCountingSequence.exactMean_le_uniformMean
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input)
    (i n : ℕ) :
    2 * (n : ℝ) *
        (physicalMultiBlockCountingConstant input (seq.params i) /
          seq.density i) ≤ seq.uniformMeanBound n := by
  have hC : 0 ≤ input.C := input.C_nonneg
  have hsqrt : 0 < Real.sqrt (seq.params i).c :=
    Real.sqrt_pos.2 (seq.params i).c_pos
  have hfirst : input.C / Real.sqrt (seq.params i).c ≤
      input.C / seq.sqrtCoupling_lower :=
    div_le_div_of_nonneg_left hC seq.sqrtCoupling_lower_pos
      (seq.sqrtCoupling_lower_le i)
  have hsecond : (input.C / Real.sqrt (seq.params i).c) / seq.density i ≤
      (input.C / seq.sqrtCoupling_lower) / seq.density_lower := by
    calc
      _ ≤ (input.C / seq.sqrtCoupling_lower) / seq.density i :=
        div_le_div_of_nonneg_right hfirst (seq.density_pos i).le
      _ ≤ (input.C / seq.sqrtCoupling_lower) / seq.density_lower :=
        div_le_div_of_nonneg_left
          (div_nonneg hC seq.sqrtCoupling_lower_pos.le)
          seq.density_lower_pos (seq.density_lower_le i)
  exact mul_le_mul_of_nonneg_left hsecond
    (mul_nonneg (by norm_num) (Nat.cast_nonneg n))

/-- Explicit diagonal mass cap based on the uniform physical mean bound. -/
def PhysicalGaussianRingCountingSequence.massCap
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (m n : ℕ) : NNReal :=
  Real.toNNReal (((2 : ℝ) ^ (n + 1) * (m + 1)) *
    (seq.uniformMeanBound n + 1))

/-- The physical diagonal cap is strictly positive. -/
theorem PhysicalGaussianRingCountingSequence.massCap_pos
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (m n : ℕ) : 0 < seq.massCap m n := by
  rw [PhysicalGaussianRingCountingSequence.massCap, Real.toNNReal_pos]
  have hB : 0 ≤ seq.uniformMeanBound n := by
    unfold uniformMeanBound
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (div_nonneg (div_nonneg input.C_nonneg seq.sqrtCoupling_lower_pos.le)
        seq.density_lower_pos.le)
  exact mul_pos (mul_pos (pow_pos (by norm_num) _) (by positivity)) (by linarith)

/-- Uniform summable coordinate tail for the physical vague laws. -/
theorem PhysicalGaussianRingCountingSequence.mass_tail
    [OpensMeasurableSpace VagueRationalWindowState]
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input)
    (i m n : ℕ) :
    (seq.law i : Measure VagueRationalWindowState)
      {ν | (seq.massCap m n : ENNReal) < ((ν n).mass : ENNReal)} ≤
        psssRationalWindowTailSchedule m n := by
  let B := seq.uniformMeanBound n
  let F : ℝ := (2 : ℝ) ^ (n + 1) * (m + 1)
  let R : ℝ := F * (B + 1)
  have hB : 0 ≤ B := by
    unfold B uniformMeanBound
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (div_nonneg (div_nonneg input.C_nonneg seq.sqrtCoupling_lower_pos.le)
        seq.density_lower_pos.le)
  have hF : 0 < F := by unfold F; positivity
  have hR : 0 < R := by unfold R; exact mul_pos hF (by linarith)
  have hbase := seq.coordinate_mass_tail_exact input i n R hR
  have hcap : (seq.massCap m n : ENNReal) = ENNReal.ofReal R := by
    unfold massCap R F B
    rfl
  rw [hcap]
  refine hbase.trans ?_
  rw [ENNReal.ofReal_le_iff_le_toReal (by
    unfold psssRationalWindowTailSchedule
    finiteness)]
  have hexact := seq.exactMean_le_uniformMean input i n
  have hratio :
      (2 * (n : ℝ) *
        (physicalMultiBlockCountingConstant input (seq.params i) /
          seq.density i)) / R ≤ 1 / F := by
    apply (div_le_div_of_nonneg_right hexact hR.le).trans
    rw [div_le_div_iff₀ hR hF]
    unfold R
    nlinarith
  have hsched : ENNReal.toReal (psssRationalWindowTailSchedule m n) = 1 / F := by
    unfold psssRationalWindowTailSchedule F
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    norm_num
    rw [one_div, inv_pow]
    ring
  rw [hsched]
  exact hratio

/-- Every coordinate of a finite local-window encoding is supported in its defining
compact marked spectral window. -/
theorem finiteMarkedLocalWindowEncoding_window_compl_eq_zero
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit) (n : ℕ) :
    (finiteMarkedLocalWindowEncoding x n : Measure _)
      (markedSpectralWindow Unit n)ᶜ = 0 := by
  unfold finiteMarkedLocalWindowEncoding
  change ((finiteMarkedCountingMeasure x : Measure _).restrict
    (markedSpectralWindow Unit n)) (markedSpectralWindow Unit n)ᶜ = 0
  rw [Measure.restrict_apply
    (measurableSet_markedSpectralWindow Unit n).compl]
  simp

/-- Outside a vague diagonal compact set, a finite physical state must violate
one of the coordinate mass caps; it cannot violate the support condition. -/
theorem PhysicalGaussianRingCountingSequence.preimage_compl_vagueCompactSet_subset
    {input : PSSSInput.{0}} (seq : PhysicalGaussianRingCountingSequence input)
    (i : ℕ) (C : ℕ → NNReal) :
    (seq.state i) ⁻¹' (vagueRationalWindowCompactSet C)ᶜ ⊆
      ⋃ n, {ω | (C n : ENNReal) < (((seq.state i ω) n).mass : ENNReal)} := by
  intro ω hω
  by_contra htail
  apply hω
  unfold vagueRationalWindowCompactSet
  rw [mem_localWindowCompactContainment_iff]
  intro n
  constructor
  · have hn : ¬ (C n : ENNReal) < (((seq.state i ω) n).mass : ENNReal) := by
      intro hlt
      apply htail
      exact Set.mem_iUnion.2 ⟨n, hlt⟩
    exact_mod_cast le_of_not_gt hn
  · unfold state Law.physicalUnfoldedVagueState
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa using finiteMarkedLocalWindowEncoding_window_compl_eq_zero
      ((seq.model i).physicalUnfoldedFiniteConfiguration
        (seq.energy i) (seq.scale i) (seq.density i) ω) n

/-- Summable physical coordinate tails bound the complement of the ambient diagonal
compact-containment set. -/
theorem PhysicalGaussianRingCountingSequence.measure_compl_vagueCompactSet_le
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input)
    (i m : ℕ) :
    (seq.law i : Measure VagueRationalWindowState)
      (vagueRationalWindowCompactSet (seq.massCap m))ᶜ ≤
        ∑' n, psssRationalWindowTailSchedule m n := by
  let K := vagueRationalWindowCompactSet (seq.massCap m)
  have hK : MeasurableSet K :=
    (isCompact_vagueRationalWindowCompactSet (seq.massCap m)).measurableSet
  rw [seq.law_apply i hK.compl]
  calc
    (seq.model i).P ((seq.state i) ⁻¹' Kᶜ) ≤
        (seq.model i).P (⋃ n,
          {ω | (seq.massCap m n : ENNReal) <
            (((seq.state i ω) n).mass : ENNReal)}) :=
      measure_mono (seq.preimage_compl_vagueCompactSet_subset i (seq.massCap m))
    _ ≤ ∑' n, (seq.model i).P
          {ω | (seq.massCap m n : ENNReal) <
            (((seq.state i ω) n).mass : ENNReal)} := measure_iUnion_le _
    _ = ∑' n, (seq.law i : Measure VagueRationalWindowState)
          {ν | (seq.massCap m n : ENNReal) < ((ν n).mass : ENNReal)} := by
      congr 1
      funext n
      symm
      apply seq.law_apply i
      have hof : (seq.massCap m n : ENNReal) =
          (seq.massCap m n : NNReal) := rfl
      rw [hof]
      convert measurableSet_vagueRationalWindowState_mass_gt (seq.massCap m n) n using 1
      ext ν
      exact_mod_cast Iff.rfl
    _ ≤ ∑' n, psssRationalWindowTailSchedule m n :=
      ENNReal.tsum_le_tsum fun n => seq.mass_tail input i m n

/-- The family of physical Gaussian-ring vague laws is tight. -/
theorem PhysicalGaussianRingCountingSequence.isTight_law
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input) :
    IsTightMeasureSet
      (Set.range (ProbabilityMeasure.toMeasure ∘ seq.law)) := by
  apply isTightMeasureSet_range_of_compact_exhaustion seq.law
    (fun m => vagueRationalWindowCompactSet (seq.massCap m))
    (fun m => isCompact_vagueRationalWindowCompactSet _)
    (fun m => ∑' n, psssRationalWindowTailSchedule m n)
    tendsto_tsum_psssRationalWindowTailSchedule
  intro i m
  exact seq.measure_compl_vagueCompactSet_le input i m

/-- Prokhorov gives a weakly convergent subsequence of the physical
Gaussian-ring laws in the common ambient vague state space. -/
theorem PhysicalGaussianRingCountingSequence.exists_weak_subsequence
    [OpensMeasurableSpace VagueRationalWindowState]
    [BorelSpace VagueRationalWindowState]
    [T2Space VagueRationalWindowState]
    [FirstCountableTopology (ProbabilityMeasure VagueRationalWindowState)]
    (input : PSSSInput.{0}) (seq : PhysicalGaussianRingCountingSequence input) :
    ∃ μ : ProbabilityMeasure VagueRationalWindowState,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (seq.law ∘ φ) atTop (𝓝 μ) := by
  apply exists_weaklyConvergent_subsequence_of_isTight seq.law
  exact seq.isTight_law input

end GaussianRing
end CoareaNative.BlockBand
