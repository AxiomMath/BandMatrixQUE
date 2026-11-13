module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockMomentBounds
public import BlockBand.Coarea.Native.BlockBand.Counting.PaperCountingUnitMarks

/-!
# Physical unfolded exponential bounds for local restriction laws

This module connects the unconditional Gaussian-ring unfolded exponential estimate to
the `NNReal` local-restriction mass laws used in the weak-limit closure.  The encoding
is the finite ordered spectrum of `normalizedPhysicalMatrix`, with physical
energy restored by `sqrt c` before unfolding.  Endpoint sets are clipped to the local
coordinate window; their masses are therefore dominated by the symmetric coordinate
count to which the physical exponential theorem applies.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open Matrix MeasureTheory
open scoped ENNReal NNReal
namespace GaussianRing
local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Unfolded physical spectrum, expressed using the normalized/reindexed matrix.
Multiplication by `sqrt c` restores the paper's physical energy before unfolding. -/
def Law.physicalUnfoldedFiniteConfiguration {p : Params} (M : Law p)
    (e L ρ : ℝ) (ω : M.Ω) :
    FiniteMarkedConfiguration (Fintype.card (BlockGUE.Index (physicalBlockSizes p))) Unit :=
  fun i =>
    (L * ρ * (Real.sqrt p.c *
      orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e), ())

/-- The unfolded physical finite configuration is measurable. -/
theorem Law.measurable_physicalUnfoldedFiniteConfiguration
    {p : Params} (M : Law p) (e L ρ : ℝ) :
    Measurable (M.physicalUnfoldedFiniteConfiguration e L ρ) := by
  rw [measurable_pi_iff]
  intro i
  apply Measurable.prodMk
  · exact (measurable_const.mul measurable_const).mul
      ((measurable_const.mul
        ((measurable_orderedEigenvalue i).comp
          M.measurable_normalizedPhysicalMatrix)).sub measurable_const)
  · exact measurable_const

/-- Ambient vague-state encoding of the finite physical spectrum. -/
def Law.physicalUnfoldedVagueState {p : Params} (M : Law p)
    (e L ρ : ℝ) (ω : M.Ω) : VagueRationalWindowState :=
  finiteMarkedLocalWindowEncoding
    (M.physicalUnfoldedFiniteConfiguration e L ρ ω)

/-- Pushforward law of the physical vague-state encoding.  As in
`PSSSRationalWindowSequence`, measurability of the sharp local-window encoding is an
explicit input. -/
def Law.physicalUnfoldedVagueLaw {p : Params} (M : Law p)
    (e L ρ : ℝ) (_hmeas : Measurable (M.physicalUnfoldedVagueState e L ρ)) :
    ProbabilityMeasure VagueRationalWindowState :=
  ProbabilityMeasure.map
    (⟨M.P, inferInstance⟩ : ProbabilityMeasure M.Ω)
    (M.physicalUnfoldedVagueState e L ρ)

/-- Real-endpoint determining sets, clipped to the `n`th local coordinate. -/
def physicalEndpointRestrictionSets
    (n : ℕ) (q : ℝ × ℝ) : Set (MarkedSpectralSpace Unit) :=
  Set.Icc (max (-(n : ℝ)) q.1) (min (n : ℝ) q.2) ×ˢ Set.univ

/-- Physical endpoint restriction sets are Borel. -/
theorem measurableSet_physicalEndpointRestrictionSets (n : ℕ) (q : ℝ × ℝ) :
    MeasurableSet (physicalEndpointRestrictionSets n q) :=
  measurableSet_Icc.prod MeasurableSet.univ

/-- Every endpoint restriction lies in its ambient local coordinate window. -/
theorem physicalEndpointRestrictionSets_subset_window (n : ℕ) (q : ℝ × ℝ) :
    physicalEndpointRestrictionSets n q ⊆ markedSpectralWindow Unit n := by
  rintro ⟨x, u⟩ ⟨hx, -⟩
  exact ⟨⟨le_trans (le_max_left _ _) hx.1,
    le_trans hx.2 (min_le_left _ _)⟩, Set.mem_univ u⟩

/-- Exact identification of a local restriction mass with the finite label count. -/
theorem localRestrictionMass_physicalUnfoldedVagueState
    {p : Params} (M : Law p) (e L ρ : ℝ) (ω : M.Ω)
    (n : ℕ) (a b : ℝ) :
    localRestrictionMass physicalEndpointRestrictionSets n (a, b)
        (M.physicalUnfoldedVagueState e L ρ ω) =
      finiteMarkedLocalCount
        (Set.Icc (max (-(n : ℝ)) a) (min (n : ℝ) b))
        (M.physicalUnfoldedFiniteConfiguration e L ρ ω) := by
  unfold localRestrictionMass Law.physicalUnfoldedVagueState
  let x := M.physicalUnfoldedFiniteConfiguration e L ρ ω
  have hmass :
      (((finiteMarkedCountingMeasure x).restrict
        (markedSpectralWindow Unit n)).restrict
        (physicalEndpointRestrictionSets n (a, b))).mass =
      ((finiteMarkedCountingMeasure x).restrict
        (physicalEndpointRestrictionSets n (a, b))).mass := by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
    change ((((finiteMarkedCountingMeasure x : Measure _).restrict
      (markedSpectralWindow Unit n)).restrict
      (physicalEndpointRestrictionSets n (a, b))) Set.univ) =
      ((finiteMarkedCountingMeasure x : Measure _).restrict
      (physicalEndpointRestrictionSets n (a, b))) Set.univ
    rw [Measure.restrict_restrict_of_subset
      (physicalEndpointRestrictionSets_subset_window n (a, b))]
  change (((finiteMarkedCountingMeasure x).restrict
    (markedSpectralWindow Unit n)).restrict
    (physicalEndpointRestrictionSets n (a, b))).mass = _
  rw [hmass]
  rw [finiteMarkedCountingMeasure_restrict_mass_eq_card _
    (measurableSet_physicalEndpointRestrictionSets n (a, b))]
  unfold finiteMarkedLocalCount physicalEndpointRestrictionSets
  norm_cast
  congr 1
  ext i
  simp [x]

/-- A clipped endpoint restriction count is bounded by the full symmetric local count. -/
theorem localRestrictionMass_physicalUnfoldedVagueState_le_symmetric
    {p : Params} (M : Law p) (e L ρ : ℝ) (ω : M.Ω)
    (n : ℕ) (a b : ℝ) :
    localRestrictionMass physicalEndpointRestrictionSets n (a, b)
        (M.physicalUnfoldedVagueState e L ρ ω) ≤
      finiteMarkedLocalCount (Set.Icc (-(n : ℝ)) (n : ℝ))
        (M.physicalUnfoldedFiniteConfiguration e L ρ ω) := by
  rw [localRestrictionMass_physicalUnfoldedVagueState]
  exact_mod_cast Finset.card_le_card (by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
    intro hi
    exact ⟨le_trans (le_max_left _ _) hi.1,
      le_trans hi.2 (min_le_left _ _)⟩)

/-- The symmetric local count is exactly the unconditional physical unfolded count. -/
theorem finiteMarkedLocalCount_physicalUnfolded_eq
    {p : Params} (M : Law p) (e L ρ : ℝ)
    (hL : 0 < L) (hρ : 0 < ρ) (ω : M.Ω) (R : ℝ) :
    finiteMarkedLocalCount (Set.Icc (-R) R)
        (M.physicalUnfoldedFiniteConfiguration e L ρ ω) =
      M.physicalUnfoldedIntervalCount e L ρ R ω := by
  unfold finiteMarkedLocalCount Law.physicalUnfoldedFiniteConfiguration
    Law.physicalUnfoldedIntervalCount Law.physicalIntervalCount
    Law.normalizedPhysicalIntervalCount eigenCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
  have hs : 0 < L * ρ := mul_pos hL hρ
  have hc : 0 < Real.sqrt p.c := Real.sqrt_pos.2 p.c_pos
  constructor
  · rintro ⟨ha, hb⟩
    have ha' : -R / (L * ρ) ≤
        Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e := by
      apply (div_le_iff₀ hs).2
      simpa [mul_comm] using ha
    have hb' : Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e ≤
        R / (L * ρ) := by
      apply (le_div_iff₀ hs).2
      simpa [mul_comm] using hb
    constructor
    · apply (div_le_iff₀ hc).2
      calc
        e - R / (L * ρ) ≤ Real.sqrt p.c *
            orderedEigenvalue (M.normalizedPhysicalMatrix ω) i := by
          convert add_le_add_right ha' e using 1
          all_goals ring
        _ = orderedEigenvalue (M.normalizedPhysicalMatrix ω) i *
            Real.sqrt p.c := mul_comm _ _
    · apply (le_div_iff₀ hc).2
      calc
        orderedEigenvalue (M.normalizedPhysicalMatrix ω) i * Real.sqrt p.c =
            Real.sqrt p.c *
              orderedEigenvalue (M.normalizedPhysicalMatrix ω) i := mul_comm _ _
        _ ≤ e + R / (L * ρ) := by
          convert add_le_add_right hb' e using 1
          all_goals ring
  · rintro ⟨ha, hb⟩
    have ha' : e - R / (L * ρ) ≤
        Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) i :=
      by simpa [mul_comm] using (div_le_iff₀ hc).1 ha
    have hb' : Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) i ≤
        e + R / (L * ρ) := by
      simpa [mul_comm] using (le_div_iff₀ hc).1 hb
    constructor
    · have hz :
          -R / (L * ρ) ≤
            Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e := by
          convert sub_le_sub_right ha' e using 1
          all_goals ring
      have := (div_le_iff₀ hs).1 hz
      simpa [mul_comm] using this
    · have hz :
          Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) i - e ≤
            R / (L * ρ) := by
          convert sub_le_sub_right hb' e using 1
          all_goals ring
      have := (le_div_iff₀ hs).1 hz
      simpa [mul_comm] using this

/-- Integration against the endpoint restriction-mass law is expectation on the
original physical sample space. -/
theorem integral_physicalUnfoldedRestrictionMassLaw
    {p : Params} (M : Law p) (e L ρ : ℝ)
    (hstate : Measurable (M.physicalUnfoldedVagueState e L ρ))
    (n : ℕ) (a b : ℝ) (f : NNReal → ℝ) (hf : Measurable f) :
    ∫ x, f x ∂(localRestrictionMassLaw
      (M.physicalUnfoldedVagueLaw e L ρ hstate)
      physicalEndpointRestrictionSets n (a, b) : Measure NNReal) =
    ∫ ω, f (localRestrictionMass physicalEndpointRestrictionSets n (a, b)
      (M.physicalUnfoldedVagueState e L ρ ω)) ∂M.P := by
  have hmass := measurable_localRestrictionMass physicalEndpointRestrictionSets
    measurableSet_physicalEndpointRestrictionSets n (a, b)
  change (∫ x, f x ∂Measure.map
      (localRestrictionMass physicalEndpointRestrictionSets n (a, b))
      (Measure.map (M.physicalUnfoldedVagueState e L ρ) M.P)) = _
  rw [integral_map hmass.aemeasurable hf.aestronglyMeasurable]
  exact integral_map hstate.aemeasurable
    (hf.comp hmass).aestronglyMeasurable

/-- The physical endpoint-restriction mass laws satisfy exactly the
integrability and uniform exponential bound fields used by
`NaturalRestrictionLawClosureInput.toPaperCountingWeakExponentialUIInput`.
The bound depends only on the local coordinate radius `n`, not on the clipped
endpoints. -/
theorem physicalUnfoldedRestrictionMass_exp_integrable_and_le
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    (e L ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ)
    (hdim : (p.n * p.W : ℝ) ≤ L)
    (hstate : Measurable (M.physicalUnfoldedVagueState e L ρ))
    (n : ℕ) (a b t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x : NNReal => Real.exp (t * (x : ℝ)))
        (localRestrictionMassLaw (M.physicalUnfoldedVagueLaw e L ρ hstate)
          physicalEndpointRestrictionSets n (a, b) : Measure NNReal) ∧
      ∫ x : NNReal, Real.exp (t * (x : ℝ))
          ∂(localRestrictionMassLaw (M.physicalUnfoldedVagueLaw e L ρ hstate)
            physicalEndpointRestrictionSets n (a, b) : Measure NNReal) ≤
        Real.exp (2 * (n : ℝ) *
          (physicalMultiBlockCountingConstant input p / ρ) *
          (Real.exp t - 1)) := by
  let mass : M.Ω → NNReal := fun ω =>
    localRestrictionMass physicalEndpointRestrictionSets n (a, b)
      (M.physicalUnfoldedVagueState e L ρ ω)
  let sym : M.Ω → ℕ := fun ω =>
    finiteMarkedLocalCount (Set.Icc (-(n : ℝ)) (n : ℝ))
      (M.physicalUnfoldedFiniteConfiguration e L ρ ω)
  have hmassMeas : Measurable mass :=
    (measurable_localRestrictionMass physicalEndpointRestrictionSets
      measurableSet_physicalEndpointRestrictionSets n (a, b)).comp hstate
  have hsymMeas : Measurable sym :=
    (measurable_finiteMarkedLocalCount _ measurableSet_Icc).comp
      (M.measurable_physicalUnfoldedFiniteConfiguration e L ρ)
  have hmass_le (ω : M.Ω) : (mass ω : ℝ) ≤ sym ω := by
    have h := localRestrictionMass_physicalUnfoldedVagueState_le_symmetric
      M e L ρ ω n a b
    change (localRestrictionMass physicalEndpointRestrictionSets n (a, b)
      (M.physicalUnfoldedVagueState e L ρ ω) : ℝ) ≤
      (finiteMarkedLocalCount (Set.Icc (-(n : ℝ)) (n : ℝ))
        (M.physicalUnfoldedFiniteConfiguration e L ρ ω) : ℝ)
    exact_mod_cast h
  have hsym_card (ω : M.Ω) : sym ω ≤ p.n * p.W := by
    dsimp [sym]
    unfold finiteMarkedLocalCount
    rw [← card_physicalBlockIndex p]
    simpa using Finset.card_filter_le (Finset.univ :
      Finset (Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p)))))
      (fun i => (M.physicalUnfoldedFiniteConfiguration e L ρ ω i).1 ∈
        Set.Icc (-(n : ℝ)) (n : ℝ))
  have hcoe : Measurable (fun x : NNReal => (x : ℝ)) :=
    NNReal.continuous_coe.measurable
  have hbase : Integrable (fun ω => Real.exp (t * (mass ω : ℝ))) M.P := by
    apply Integrable.of_bound
      ((Real.measurable_exp.comp
        (measurable_const.mul (hcoe.comp hmassMeas))).aestronglyMeasurable)
      (Real.exp (t * (p.n * p.W : ℝ)))
    filter_upwards with ω
    change |Real.exp (t * (mass ω : ℝ))| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ht
    exact le_trans (hmass_le ω) (by exact_mod_cast hsym_card ω)
  have hsymInt : Integrable (fun ω => Real.exp (t * (sym ω : ℝ))) M.P := by
    apply Integrable.of_bound
      ((Real.measurable_exp.comp
        (measurable_const.mul (measurable_from_nat.comp hsymMeas))).aestronglyMeasurable)
      (Real.exp (t * (p.n * p.W : ℝ)))
    filter_upwards with ω
    change |Real.exp (t * (sym ω : ℝ))| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsym_card ω) ht
  constructor
  · change Integrable (fun x : NNReal => Real.exp (t * (x : ℝ)))
      (Measure.map (localRestrictionMass physicalEndpointRestrictionSets n (a, b))
        (Measure.map (M.physicalUnfoldedVagueState e L ρ) M.P))
    apply (integrable_map_measure
      (Real.measurable_exp.comp
        (measurable_const.mul hcoe)).aestronglyMeasurable
      (measurable_localRestrictionMass physicalEndpointRestrictionSets
        measurableSet_physicalEndpointRestrictionSets n (a, b)).aemeasurable).2
    apply (integrable_map_measure
      ((Real.measurable_exp.comp
        (measurable_const.mul hcoe)).comp
        (measurable_localRestrictionMass physicalEndpointRestrictionSets
          measurableSet_physicalEndpointRestrictionSets n (a, b))).aestronglyMeasurable
      hstate.aemeasurable).2
    convert hbase using 1
    funext ω
    rfl
  · rw [integral_physicalUnfoldedRestrictionMassLaw M e L ρ hstate n a b
      (fun x : NNReal => Real.exp (t * (x : ℝ)))
      (Real.measurable_exp.comp (measurable_const.mul hcoe))]
    calc
      (∫ ω, Real.exp (t * (mass ω : ℝ)) ∂M.P) ≤
          ∫ ω, Real.exp (t * (sym ω : ℝ)) ∂M.P := by
        apply integral_mono hbase hsymInt
        intro ω
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hmass_le ω) ht)
      _ = ∫ ω, Real.exp (t *
          (M.physicalUnfoldedIntervalCount e L ρ n ω : ℝ)) ∂M.P := by
        apply integral_congr_ae
        filter_upwards with ω
        congr 2
        simpa [sym] using finiteMarkedLocalCount_physicalUnfolded_eq M
          e L ρ hL hρ ω (n : ℝ)
      _ ≤ Real.exp (2 * (n : ℝ) *
          (physicalMultiBlockCountingConstant input p / ρ) *
          (Real.exp t - 1)) :=
        M.physicalUnfoldedIntervalCount_exponential input e L ρ n t
          hL hρ (Nat.cast_nonneg n) hdim ht

end GaussianRing
end CoareaNative.BlockBand
