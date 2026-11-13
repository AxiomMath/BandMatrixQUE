module
public import BlockBand.Counting.PhysicalMarkedTightnessFinite
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tightness from uniform local first moments

A family of natural-valued counts with a common finite first-moment bound admits uniform
caps outside events of small probability.  Applied to the shell counts, this gives
vague tightness of a family of finite marked samples from uniform local first moments.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set
open scoped Topology ENNReal NNReal

/-- Uniform tails for a family of natural-valued counts with one finite common
first-moment bound. Domains and measures may vary with the family index. -/
theorem exists_uniform_natural_count_cap {I : Type*} {Ω : I → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) (count : ∀ i, Ω i → ℕ)
    (hmeas : ∀ i, Measurable (count i)) (L : ℝ≥0∞) (hL : L ≠ ∞)
    (hbound : ∀ i, (∫⁻ x, (count i x : ℝ≥0∞) ∂μ i) ≤ L)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ cap : ℕ, ∀ i, μ i {x | cap < count i x} ≤ (δ : ℝ≥0∞) := by
  have hd0 : (δ : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.mpr hδ).ne'
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hL hd0)
  refine ⟨n, fun i => ?_⟩
  have hn0 : ((n+1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hnt : ((n+1 : ℕ) : ℝ≥0∞) ≠ ∞ := by simp
  have hratio : L / ((n+1 : ℕ) : ℝ≥0∞) ≤ δ := by
    apply (ENNReal.div_le_iff hn0 hnt).mpr
    have hnat : (n : ℝ≥0∞) ≤ ((n+1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_succ n
    have hh := (ENNReal.div_le_iff hd0 ENNReal.coe_ne_top).mp (hn.le.trans hnat)
    simpa only [mul_comm] using hh
  have hset : {x | n < count i x} ⊆ {x | ((n+1 : ℕ) : ℝ≥0∞) ≤ (count i x : ℝ≥0∞)} := by
    intro x hx
    exact_mod_cast Nat.succ_le_of_lt hx
  have hm : AEMeasurable (fun x => (count i x : ℝ≥0∞)) (μ i) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (hmeas i) |>.aemeasurable
  exact (measure_mono hset).trans
    ((meas_ge_le_lintegral_div hm hn0 hnt).trans
      ((ENNReal.div_le_div_right (hbound i) _).trans hratio))

/-- Uniform vague tightness of finite indexed marked samples from uniform local first
moments.  The measure family and sample dimensions may vary; counts retain
multiplicities. -/
theorem finiteMarkedFamily_isTight {I : Type*} {Ω : I → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) (d : I → ℕ)
    (locations : ∀ i, Ω i → Fin (d i) → MarkedSpectralSpace)
    (sample : ∀ i, Ω i → MarkedPointMeasure)
    (hsample : ∀ i, Measurable (sample i))
    (hsample_eq : ∀ i x, sample i x =
      BlockBand.Model.Construction.finiteAtomicMarkedPointMeasure (locations i x))
    (count : ∀ i, ℕ → Ω i → ℕ) (hmeas : ∀ i j, Measurable (count i j))
    (hcontrol : ∀ i x j, (finiteMarkedShellLabels (locations i x) j).card ≤ count i j x)
    (L : ℕ → ℝ≥0∞) (hL : ∀ j, L j ≠ ∞)
    (hbound : ∀ i j, (∫⁻ x, (count i j x : ℝ≥0∞) ∂μ i) ≤ L j) :
    IsTightMeasureSet (Set.range (fun i => Measure.map (sample i) (μ i))) := by
  classical
  let : T2Space MarkedPointMeasure :=
    BlockBand.Model.Construction.markedPointMeasure_t2Space
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  have hcap : ∀ j, ∃ cap : ℕ, ∀ i, μ i {x | cap < count i j x} ≤ (δ j : ℝ≥0∞) := by
    intro j
    exact exists_uniform_natural_count_cap μ (fun i => count i j) (fun i => hmeas i j)
      (L j) (hL j) (fun i => hbound i j) (δ j) (hδ j)
  choose caps hcaps using hcap
  let K := markedShellCompactSet caps
  have hK : IsCompact K := isCompact_markedShellCompactSet caps
  refine ⟨K, hK, ?_⟩
  rintro ν ⟨i, rfl⟩
  rw [Measure.map_apply (hsample i) hK.isClosed.measurableSet.compl]
  have hsub : sample i ⁻¹' Kᶜ ⊆ ⋃ j, {x | caps j < count i j x} := by
    intro x hx
    by_contra hh
    have hall : ∀ j, count i j x ≤ caps j := by
      intro j
      apply le_of_not_gt
      intro hj
      exact hh (Set.mem_iUnion.mpr ⟨j, hj⟩)
    have hin : sample i x ∈ K := by
      rw [hsample_eq i x]
      exact finiteAtomicMarked_mem_markedShellCompactSet (locations i x) caps
        (fun j => (hcontrol i x j).trans (hall j))
    exact hx hin
  exact (measure_mono hsub).trans
    ((measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum (fun j => hcaps j i)).trans hsum.le))

end BlockBand.Counting
