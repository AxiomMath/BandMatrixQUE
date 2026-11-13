module

public import BlockBand.Internal.Contracts.TransmissionLaws
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# The trace-measure sets `S_R`

For `0 < p ≤ 1` and `R`, `atomSet p R` is the set of finite measures `ν` on `[0,1]` that agree,
on test functions vanishing on `[0,x]` (`x > 0`), with `Σ_i t_i δ_{t_i}` for a sequence `t`
(`PBound`: antitone, in `[0,1]`, `Σ t_i^p ≤ R`). By `le_of_cutIdx_le`, `t_i ≤ x` for
`i ≥ cutIdx p R x = ⌈R/x^p⌉`, so the agreement is written with the finite sum over `i < cutIdx`.
This is the set `{cδ₀ + Σ t_iδ_{t_i} : Σ t_i^p ≤ R}`.

* `integral_seqTraceMeasure_cut`: the trace measure of a `PBound` sequence satisfies the cut
  formula.

Proved in a sibling module:
* `restrict_ppos_eq`: two finite measures that agree on all such tests agree on `(0,1]`.
* `exists_seq_of_mem_atomSet`: a measure in `atomSet p R` without mass at `0` is the trace measure
  of a transmission sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The positive part `(0,1]` of `[0,1]`. -/
def ppos : Set unitInterval := {y | 0 < (y : ℝ)}

/-- The cut index `⌈R / x^p⌉`. -/
def cutIdx (p R x : ℝ) : ℕ := ⌈R / x ^ p⌉₊

/-- An antitone sequence in `[0,1]` with `Σ t_i^p ≤ R`. -/
def PBound (p R : ℝ) (t : ℕ → ℝ) : Prop :=
  Antitone t ∧ (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ ∀ n, ∑ i ∈ Finset.range n, t i ^ p ≤ R

/-- `ν` agrees with `Σ t_iδ_{t_i}` on tests vanishing on some `[0,x]`, `x > 0`. -/
def AgreeCut (p R : ℝ) (ν : FiniteMeasure unitInterval) (t : ℕ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → ∀ f : unitInterval →ᵇ ℝ, (∀ y : unitInterval, (y : ℝ) ≤ x → f y = 0) →
    ∫ y, f y ∂(ν : Measure unitInterval) =
      ∑ i ∈ Finset.range (cutIdx p R x), t i * f (toUnit (t i))

/-- The set `S_R = {cδ₀ + Σ t_iδ_{t_i} : Σ t_i^p ≤ R}`. -/
def atomSet (p R : ℝ) : Set (FiniteMeasure unitInterval) :=
  {ν | ∃ t : ℕ → ℝ, PBound p R t ∧ AgreeCut p R ν t}

theorem measurableSet_ppos : MeasurableSet ppos :=
  measurableSet_lt measurable_const continuous_subtype_val.measurable

theorem coe_toUnit_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : (toUnit x : ℝ) = x := by
  simp [toUnit, Set.projIcc_of_mem _ ⟨h0, h1⟩]

theorem continuous_toUnit : Continuous toUnit :=
  (continuous_projIcc : Continuous (Set.projIcc (0 : ℝ) 1 zero_le_one))

/-- Beyond the cut index the sequence is below `x`. -/
theorem le_of_cutIdx_le {p R x : ℝ} {t : ℕ → ℝ} (hp : 0 < p) (hx : 0 < x) (ht : PBound p R t)
    {i : ℕ} (hi : cutIdx p R x ≤ i) : t i ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  have hsum : ∑ _j ∈ Finset.range (i + 1), x ^ p < ∑ j ∈ Finset.range (i + 1), t j ^ p :=
    Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun j hj => Real.rpow_lt_rpow hx.le
      (lt_of_lt_of_le hlt (ht.1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))) hp
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hR := ht.2.2 (i + 1)
  have hc : R / x ^ p ≤ i := (Nat.le_ceil _).trans (by exact_mod_cast hi)
  rw [div_le_iff₀ hxp] at hc
  push_cast at hsum
  nlinarith

theorem le_rpow_of_mem {p y : ℝ} (hp1 : p ≤ 1) (h0 : 0 ≤ y) (h1 : y ≤ 1) : y ≤ y ^ p := by
  rcases h0.eq_or_lt with rfl | hy
  · exact (Real.rpow_nonneg le_rfl p)
  · simpa using Real.rpow_le_rpow_of_exponent_ge hy h1 hp1

theorem summable_of_pBound {p R : ℝ} {t : ℕ → ℝ} (hp1 : p ≤ 1) (ht : PBound p R t) :
    Summable t :=
  summable_of_sum_range_le (fun i => (ht.2.1 i).1) fun n =>
    (Finset.sum_le_sum fun i _ => le_rpow_of_mem hp1 (ht.2.1 i).1 (ht.2.1 i).2).trans (ht.2.2 n)

theorem seqTraceMeasure_univ {t : ℕ → ℝ} (h0 : ∀ i, 0 ≤ t i) (hs : Summable t) :
    seqTraceMeasure t univ = ENNReal.ofReal (∑' i, t i) := by
  rw [seqTraceMeasure, Measure.sum_apply _ MeasurableSet.univ, ENNReal.ofReal_tsum_of_nonneg h0 hs]
  simp

theorem isFiniteMeasure_seqTraceMeasure {t : ℕ → ℝ} (h0 : ∀ i, 0 ≤ t i) (hs : Summable t) :
    IsFiniteMeasure (seqTraceMeasure t) :=
  ⟨by rw [seqTraceMeasure_univ h0 hs]; exact ENNReal.ofReal_lt_top⟩

theorem seqTraceMeasure_zero {t : ℕ → ℝ} (h0 : ∀ i, 0 ≤ t i) :
    seqTraceMeasure t {0} = 0 := by
  rw [seqTraceMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  refine ENNReal.tsum_eq_zero.2 fun i => ?_
  rcases (h0 i).eq_or_lt with h | h
  · simp [← h]
  · have : toUnit (t i) ∉ ({0} : Set unitInterval) := by
      intro hm
      have := congrArg Subtype.val (Set.mem_singleton_iff.1 hm)
      simp only [toUnit, Set.coe_projIcc, Set.Icc.coe_zero] at this
      have : min 1 (t i) ≤ 0 := by rw [← this]; exact le_max_right _ _
      rcases min_le_iff.1 this with h' | h' <;> linarith
    simp [Measure.dirac_apply' _ (measurableSet_singleton _), this]

/-- **The cut formula** for the trace measure of a `PBound` sequence. -/
theorem integral_seqTraceMeasure_cut {p R x : ℝ} {t : ℕ → ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hx : 0 < x) (ht : PBound p R t) (f : unitInterval →ᵇ ℝ)
    (hf : ∀ y : unitInterval, (y : ℝ) ≤ x → f y = 0) :
    ∫ y, f y ∂seqTraceMeasure t = ∑ i ∈ Finset.range (cutIdx p R x), t i * f (toUnit (t i)) := by
  have h0 : ∀ i, 0 ≤ t i := fun i => (ht.2.1 i).1
  have := isFiniteMeasure_seqTraceMeasure h0 (summable_of_pBound hp1 ht)
  have hi : Integrable f (seqTraceMeasure t) := f.integrable _
  rw [seqTraceMeasure] at hi ⊢
  rw [integral_sum_measure hi]
  have hterm : ∀ i, ∫ y, f y ∂(ENNReal.ofReal (t i) • Measure.dirac (toUnit (t i))) =
      t i * f (toUnit (t i)) := by
    intro i
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (h0 i), smul_eq_mul]
  simp_rw [hterm]
  refine tsum_eq_sum fun i hi => ?_
  have hle := le_of_cutIdx_le hp hx ht (not_lt.1 (fun h => hi (Finset.mem_range.2 h)))
  rw [hf _ (by rw [coe_toUnit_of_mem (h0 i) (ht.2.1 i).2]; exact hle), mul_zero]

end BlockBand.SourceProcess.SourcePins
