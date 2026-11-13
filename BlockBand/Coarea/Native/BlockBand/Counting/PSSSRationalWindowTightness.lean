module

public import BlockBand.Coarea.Native.BlockBand.Counting.RationalWindowPointState
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# PSSS tails for the rational-window point state

This module turns the PSSS first factorial-moment estimate into the summable
diagonal coordinate tails required by `RationalWindowPointState`.  The
finite unfolded BlockGUE state is used at every index.  Measurability of the
map into the bundled state is recorded explicitly, since sharp restriction is
not measurable for free on a boundary-charging ambient space.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

universe u

/-- The mass of the `n`th coordinate of a finite rational-window state is the
number of labels whose spectral coordinate lies in `[-n,n]`. -/
theorem finiteMarkedRationalWindowPointState_window_mass_eq_localCount
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit) (n : ℕ) :
    ((finiteMarkedRationalWindowPointState x).window n).mass =
      finiteMarkedLocalCount (Set.Icc (-(n : ℝ)) (n : ℝ)) x := by
  rw [show ((finiteMarkedRationalWindowPointState x).window n) =
      (finiteMarkedCountingMeasure x).restrict (markedSpectralWindow Unit n) from rfl]
  rw [finiteMarkedCountingMeasure_restrict_mass_eq_card _
    (measurableSet_markedSpectralWindow Unit n)]
  unfold finiteMarkedLocalCount markedSpectralWindow
  norm_cast
  congr 1; simp

/-- For an unfolded BlockGUE sample, coordinate mass is exactly the existing
symmetric unfolded interval count. -/
theorem BlockGUE.unfoldedRationalWindowPointState_window_mass
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ)
    (ω : M.Ω) (n : ℕ) :
    ((BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ ω).window n).mass =
      BlockGUE.unfoldedIntervalCount M A₀ e L ρ n ω := by
  rw [BlockGUE.unfoldedRationalWindowPointState,
    finiteMarkedRationalWindowPointState_window_mass_eq_localCount]
  exact_mod_cast BlockGUE.finiteMarkedLocalCount_Icc_eq_unfoldedIntervalCount
    M A₀ e L ρ n hL hρ ω

/-- The law of the unfolded rational-window state, given the
necessary measurability of the bundled state map. -/
def BlockGUE.unfoldedRationalWindowPointStateLaw
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ)
    (_hmeas : Measurable
      (BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ)) :
    ProbabilityMeasure RationalWindowPointState :=
  (BlockGUE.sampleProbability M).map
    (BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ)

/-- Evaluation of a measurable event under the unfolded rational-window law
is evaluation of its preimage on the BlockGUE sample space. -/
theorem BlockGUE.unfoldedRationalWindowPointStateLaw_apply
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ)
    (hmeas : Measurable
      (BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ))
    {S : Set RationalWindowPointState} (hS : MeasurableSet S) :
    (BlockGUE.unfoldedRationalWindowPointStateLaw M A₀ e L ρ hmeas : Measure _) S =
      M.P ((BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ) ⁻¹' S) := by
  change Measure.map
    (BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ) M.P S = _
  exact Measure.map_apply hmeas hS

/-- A varying sequence of finite BlockGUE models, all unfolded into the common
rational-window point-state space. -/
structure PSSSRationalWindowSequence (input : PSSSInput.{u}) where
  k : ℕ → ℕ
  d : ∀ i, Fin (k i) → ℕ
  hd : ∀ i j, 0 < d i j
  model : ∀ i, BlockGUE.Law.{u} (d i) (hd i)
  deformation : ∀ i, HermitianMatrix (BlockGUE.Index (d i))
  energy : ℕ → ℝ
  scale : ℕ → ℝ
  density : ℕ → ℝ
  scale_pos : ∀ i, 0 < scale i
  density_pos : ∀ i, 0 < density i
  dimension_le_scale : ∀ i,
    (Fintype.card (BlockGUE.Index (d i)) : ℝ) ≤ scale i
  state_measurable : ∀ i, Measurable
    (BlockGUE.unfoldedRationalWindowPointState
      (model i) (deformation i) (energy i) (scale i) (density i))
  density_lower : ℝ
  density_lower_pos : 0 < density_lower
  density_lower_le : ∀ i, density_lower ≤ density i

/-- The sequence of unfolded rational-window laws. -/
def PSSSRationalWindowSequence.law
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (i : ℕ) : ProbabilityMeasure RationalWindowPointState :=
  BlockGUE.unfoldedRationalWindowPointStateLaw
    (seq.model i) (seq.deformation i) (seq.energy i)
    (seq.scale i) (seq.density i) (seq.state_measurable i)

/-- Coordinate mass superlevel events are Borel in the product weak topology. -/
theorem measurableSet_rationalWindowPointState_mass_gt
    [OpensMeasurableSpace RationalWindowPointState]
    (a : NNReal) (n : ℕ) :
    MeasurableSet {ν : RationalWindowPointState | a < (ν.window n).mass} := by
  exact (isOpen_lt continuous_const
    (FiniteMeasure.continuous_mass.comp
      (continuous_localPointMeasureStateSpace_window n))).measurableSet

/-- PSSS Markov bound transported to one coordinate of the common-state
law. -/
theorem psss_unfoldedRationalWindowPointState_mass_tail
    [OpensMeasurableSpace RationalWindowPointState]
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ)
    (hmeas : Measurable
      (BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ))
    (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (BlockGUE.unfoldedRationalWindowPointStateLaw M A₀ e L ρ hmeas : Measure _)
        {ν : RationalWindowPointState |
          ENNReal.ofReal R < ((ν.window n).mass : ENNReal)} ≤
      ENNReal.ofReal
        (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
          ((e + n / (L * ρ)) - (e - n / (L * ρ))) / R) := by
  let E : Set RationalWindowPointState :=
    {ν | ENNReal.ofReal R < ((ν.window n).mass : ENNReal)}
  have hE : MeasurableSet E := by
    unfold E
    have hof : ENNReal.ofReal R = (Real.toNNReal R : ENNReal) := rfl
    rw [hof]
    convert measurableSet_rationalWindowPointState_mass_gt (Real.toNNReal R) n using 1
    ext ν
    exact_mod_cast Iff.rfl
  rw [BlockGUE.unfoldedRationalWindowPointStateLaw_apply
    M A₀ e L ρ hmeas hE]
  have hevent :
      (BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ) ⁻¹' E =
        {ω | R < (BlockGUE.unfoldedIntervalCount M A₀ e L ρ n ω : ℝ)} := by
    ext ω
    simp only [E, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [BlockGUE.unfoldedRationalWindowPointState_window_mass
      M A₀ e L ρ hL hρ ω n]
    rw [ENNReal.ofReal_lt_coe_iff hR.le]
    exact_mod_cast Iff.rfl
  rw [hevent]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.ofReal_ne_top)).mp
  have hwidth : 0 ≤ (e + n / (L * ρ)) - (e - n / (L * ρ)) := by
    have hq : 0 < L * ρ := mul_pos hL hρ
    have hn : 0 ≤ (n : ℝ) / (L * ρ) := div_nonneg (Nat.cast_nonneg n) hq.le
    linarith
  rw [ENNReal.toReal_ofReal
    (div_nonneg (mul_nonneg (mul_nonneg input.C_nonneg (Nat.cast_nonneg _)) hwidth) hR.le)]
  change M.P.real {ω | R <
    (BlockGUE.unfoldedIntervalCount M A₀ e L ρ n ω : ℝ)} ≤ _
  have hmarkov := psss_count_tail input hd M A₀
    (e - n / (L * ρ)) (e + n / (L * ρ)) R (by
      have hq : 0 < L * ρ := mul_pos hL hρ
      have hn : 0 ≤ (n : ℝ) / (L * ρ) := div_nonneg (Nat.cast_nonneg n) hq.le
      linarith)
  have hsubset :
      {ω | R < (BlockGUE.unfoldedIntervalCount M A₀ e L ρ n ω : ℝ)} ⊆
      {ω | R ≤ (BlockGUE.intervalCount M A₀
        (Set.Icc (e - n / (L * ρ)) (e + n / (L * ρ))) ω : ℝ)} := by
    intro ω hω
    change R < (BlockGUE.intervalCount M A₀
      (Set.Icc (e - n / (L * ρ)) (e + n / (L * ρ))) ω : ℝ) at hω
    change R ≤ (BlockGUE.intervalCount M A₀
      (Set.Icc (e - n / (L * ρ)) (e + n / (L * ρ))) ω : ℝ)
    exact hω.le
  have hprob : M.P.real {ω | R <
      (BlockGUE.unfoldedIntervalCount M A₀ e L ρ n ω : ℝ)} ≤
      M.P.real {ω | R ≤ (BlockGUE.intervalCount M A₀
        (Set.Icc (e - n / (L * ρ)) (e + n / (L * ρ))) ω : ℝ)} := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
  apply (le_div_iff₀ hR).2
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left hprob hR.le).trans hmarkov

/-- Uniform PSSS first-moment bound for the unfolded window `[-n,n]`. -/
def psssRationalWindowMeanBound
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (n : ℕ) : ℝ := 2 * input.C * n / seq.density_lower

/-- Explicit diagonal mass threshold: the local first-moment bound plus one,
amplified by `2^(n+1) (m+1)`. -/
def psssRationalWindowMassCap
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (m n : ℕ) : NNReal :=
  Real.toNNReal (((2 : ℝ) ^ (n + 1) * (m + 1)) *
    (psssRationalWindowMeanBound seq n + 1))

/-- The summable tail schedule paired with `psssRationalWindowMassCap`. -/
def psssRationalWindowTailSchedule (m n : ℕ) : ENNReal :=
  ((2 : ENNReal)⁻¹) ^ (n + 1) * ((m + 1 : ℕ) : ENNReal)⁻¹

/-- The diagonal tail schedule sums to `1/(m+1)`. -/
theorem tsum_psssRationalWindowTailSchedule (m : ℕ) :
    ∑' n, psssRationalWindowTailSchedule m n =
      ((m + 1 : ℕ) : ENNReal)⁻¹ := by
  simp only [psssRationalWindowTailSchedule]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_add_one]
  simp only [ENNReal.one_sub_inv_two, inv_inv]
  rw [ENNReal.inv_mul_cancel] <;> norm_num

/-- The total diagonal error tends to zero. -/
theorem tendsto_tsum_psssRationalWindowTailSchedule :
    Tendsto (fun m => ∑' n, psssRationalWindowTailSchedule m n)
      atTop (𝓝 0) := by
  simp_rw [tsum_psssRationalWindowTailSchedule]
  convert ENNReal.tendsto_inv_nat_nhds_zero.comp
    (tendsto_add_atTop_nat 1) using 1
  ext m
  simp

/-- The physical PSSS first-moment numerator is bounded uniformly by the
unfolded mean bound. -/
theorem PSSSRationalWindowSequence.physicalNumerator_le_meanBound
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (i n : ℕ) :
    input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) *
        ((seq.energy i + n / (seq.scale i * seq.density i)) -
          (seq.energy i - n / (seq.scale i * seq.density i))) ≤
      psssRationalWindowMeanBound seq n := by
  have hC := input.C_nonneg
  have hL := seq.scale_pos i
  have hρ := seq.density_pos i
  have hρ₀ := seq.density_lower_pos
  have hdim := seq.dimension_le_scale i
  have hρle := seq.density_lower_le i
  unfold psssRationalWindowMeanBound
  have hq : 0 < seq.scale i * seq.density i := mul_pos hL hρ
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcard : 0 ≤ (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) := Nat.cast_nonneg _
  calc
    input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) *
        ((seq.energy i + n / (seq.scale i * seq.density i)) -
          (seq.energy i - n / (seq.scale i * seq.density i))) =
        2 * input.C * n *
          ((Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) / seq.scale i) /
          seq.density i := by field_simp; ring
    _ ≤ (2 * input.C * n * 1) / seq.density i := by
      have hr : (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) /
          seq.scale i ≤ 1 := (div_le_one hL).2 hdim
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr
          (mul_nonneg (mul_nonneg (by norm_num) hC) hn)) hρ.le
    _ = 2 * input.C * n / seq.density i := by ring
    _ ≤ 2 * input.C * n / seq.density_lower := by
      exact div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hC) hn)
        hρ₀ hρle

/-- The explicit diagonal cap is strictly positive. -/
theorem psssRationalWindowMassCap_pos
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (m n : ℕ) : 0 < psssRationalWindowMassCap seq m n := by
  rw [psssRationalWindowMassCap, Real.toNNReal_pos]
  have hB : 0 ≤ psssRationalWindowMeanBound seq n := by
    unfold psssRationalWindowMeanBound
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) input.C_nonneg) (Nat.cast_nonneg n))
      seq.density_lower_pos.le
  exact mul_pos (mul_pos (pow_pos (by norm_num) _) (by positivity)) (by linarith)

/-- PSSS supplies the explicit summable coordinate tail required by the
diagonal compactness theorem. -/
theorem PSSSRationalWindowSequence.mass_tail
    [OpensMeasurableSpace RationalWindowPointState]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (i m n : ℕ) :
    (seq.law i : Measure _)
        {ν : RationalWindowPointState |
          (psssRationalWindowMassCap seq m n : ENNReal) <
            ((ν.window n).mass : ENNReal)} ≤
      psssRationalWindowTailSchedule m n := by
  let B := psssRationalWindowMeanBound seq n
  let F : ℝ := (2 : ℝ) ^ (n + 1) * (m + 1)
  let R : ℝ := F * (B + 1)
  have hB : 0 ≤ B := by
    unfold B psssRationalWindowMeanBound
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) input.C_nonneg) (Nat.cast_nonneg n))
      seq.density_lower_pos.le
  have hF : 0 < F := by unfold F; positivity
  have hR : 0 < R := by unfold R; exact mul_pos hF (by linarith)
  have hbase := psss_unfoldedRationalWindowPointState_mass_tail input
    (seq.hd i) (seq.model i) (seq.deformation i) (seq.energy i)
    (seq.scale i) (seq.density i) (seq.scale_pos i) (seq.density_pos i)
    (seq.state_measurable i) n R hR
  have hcap : (psssRationalWindowMassCap seq m n : ENNReal) =
      ENNReal.ofReal R := by
    unfold psssRationalWindowMassCap R F B
    rfl
  rw [hcap]
  refine hbase.trans ?_
  rw [ENNReal.ofReal_le_iff_le_toReal (by
    unfold psssRationalWindowTailSchedule
    finiteness)]
  have hnum := seq.physicalNumerator_le_meanBound i n
  have hratio :
      input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) *
          ((seq.energy i + n / (seq.scale i * seq.density i)) -
            (seq.energy i - n / (seq.scale i * seq.density i))) / R ≤
        1 / F := by
    apply (div_le_div_of_nonneg_right hnum hR.le).trans
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

/-- PSSS local first moments alone now produce a weak subsequence of
the unfolded rational-window laws.  The only remaining topology-specific
inputs are the boundary-continuity interfaces already isolated for the bundled
state space. -/
theorem PSSSRationalWindowSequence.exists_weak_subsequence
    [OpensMeasurableSpace RationalWindowPointState]
    [T2Space RationalWindowPointState]
    [BorelSpace RationalWindowPointState]
    [FirstCountableTopology (ProbabilityMeasure RationalWindowPointState)]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input)
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Unit))
    (hmass : LocalRestrictionMassMapsContinuous
      rationalWindowDeterminingFamily) :
    ∃ μ : ProbabilityMeasure RationalWindowPointState,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (seq.law ∘ φ) atTop (𝓝 μ) := by
  apply exists_weaklyConvergent_subsequence_rationalWindowPointState
    seq.law hsharp hmass (psssRationalWindowMassCap seq)
    psssRationalWindowTailSchedule
    tendsto_tsum_psssRationalWindowTailSchedule
  intro i m n
  exact seq.mass_tail i m n

/-- Paper-facing package: a weak subsequence together with the PSSS
factorial, unfolded exponential, and second-factorial close-pair inputs which
hold uniformly along the entire sequence. -/
def PSSSRationalWindowTightnessConclusion
    [TopologicalSpace RationalWindowPointState]
    [TopologicalSpace (ProbabilityMeasure RationalWindowPointState)]
    {input : PSSSInput.{u}} (seq : PSSSRationalWindowSequence input) : Prop :=
  (∃ μ : ProbabilityMeasure RationalWindowPointState,
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (seq.law ∘ φ) atTop (𝓝 μ)) ∧
  (∀ i (a b : ℝ), a ≤ b → ∀ r : ℕ, 1 ≤ r →
    ∫ ω, ((BlockGUE.intervalCount (seq.model i) (seq.deformation i)
      (Set.Icc a b) ω).descFactorial r : ℝ) ∂(seq.model i).P ≤
      (input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) * (b - a)) ^ r) ∧
  (∀ i (R t : ℝ), 0 ≤ R → 0 ≤ t →
    ∫ ω, Real.exp (t *
      (BlockGUE.unfoldedIntervalCount (seq.model i) (seq.deformation i)
        (seq.energy i) (seq.scale i) (seq.density i) R ω : ℝ))
        ∂(seq.model i).P ≤
      Real.exp (2 * R * (input.C / seq.density i) * (Real.exp t - 1))) ∧
  (∀ i (a b : ℝ), a ≤ b →
    ∫ ω, ((BlockGUE.intervalCount (seq.model i) (seq.deformation i)
      (Set.Icc a b) ω).descFactorial 2 : ℝ) ∂(seq.model i).P ≤
      (input.C * (Fintype.card (BlockGUE.Index (seq.d i)) : ℝ) * (b - a)) ^ 2)

/-- Assemble the weak subsequence and all finite-matrix PSSS counting inputs. -/
theorem psssRationalWindowTightness
    [OpensMeasurableSpace RationalWindowPointState]
    [T2Space RationalWindowPointState]
    [BorelSpace RationalWindowPointState]
    [FirstCountableTopology (ProbabilityMeasure RationalWindowPointState)]
    (input : PSSSInput.{u}) (seq : PSSSRationalWindowSequence input)
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Unit))
    (hmass : LocalRestrictionMassMapsContinuous
      rationalWindowDeterminingFamily) :
    PSSSRationalWindowTightnessConclusion seq := by
  refine ⟨seq.exists_weak_subsequence hsharp hmass, ?_, ?_, ?_⟩
  · intro i a b hab r hr
    exact psss_factorialCount input (seq.hd i) (seq.model i)
      (seq.deformation i) a b hab r hr
  · intro i R t hR ht
    exact psss_unfoldedCountExponential input (seq.hd i) (seq.model i)
      (seq.deformation i) (seq.energy i) (seq.scale i) (seq.density i)
      R t (seq.scale_pos i) (seq.density_pos i) hR
      (seq.dimension_le_scale i) ht
  · intro i a b hab
    exact psss_closePairCount input (seq.hd i) (seq.model i)
      (seq.deformation i) a b hab

end CoareaNative.BlockBand
