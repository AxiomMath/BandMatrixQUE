module

public import BlockBand.RankLocation.CyclicMassTransport
public import BlockBand.RankLocation.OrderedCountInversion

/-!
# Count and deterministic-rank moment transport

All integer moments and `L^p` seminorms of the centred strict count `N(E) - m` and of the
displacement `λ_i - e` of a fixed rank are the same under the block-mass and pair-mass laws as
under the original law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.RankLocation.MassTransport

open MeasureTheory
open scoped BigOperators ENNReal

/-- The strict counts (with multiplicities) are measurable on the space of ordered spectra. -/
theorem measurable_countBelow {N : ℕ} (E : ℝ) :
    Measurable (fun v : Fin N → ℝ => BlockBand.RankLocation.countBelow v E) := by
  have heq : (fun v : Fin N → ℝ => BlockBand.RankLocation.countBelow v E) =
      fun v => ∑ j : Fin N, {w : Fin N → ℝ | w j < E}.indicator
        (fun _ => (1 : ℕ)) v := by
    funext v
    simp only [BlockBand.RankLocation.countBelow, Finset.card_eq_sum_ones,
      Finset.sum_filter, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator
    (measurableSet_lt (measurable_pi_apply j) measurable_const)

/-- The real cast of the strict count is measurable. -/
theorem measurable_countBelow_real {N : ℕ} (E : ℝ) :
    Measurable (fun v : Fin N → ℝ => (BlockBand.RankLocation.countBelow v E : ℝ)) :=
  measurable_from_nat.comp (measurable_countBelow E)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ} [NeZero n]
variable {N : ℕ}

/-- Every integer moment of the centred count transfers to a block-mass law (deterministic `E` and
centring `m`). -/
theorem count_moment_blockMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (E m : ℝ) (q : ℕ) (k : ZMod n) :
    (∫⁻ ω, ENNReal.ofReal |(BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m| ^ q
      ∂blockMassMeasure S k) =
      ∫⁻ ω, ENNReal.ofReal |(BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m| ^ q ∂μ := by
  apply lintegral_blockMassMeasure_eq
  · exact (ENNReal.measurable_ofReal.comp
      (((measurable_countBelow_real E).comp hX).sub measurable_const).abs).pow_const q
  · intro s
    filter_upwards [hXinv s] with ω hω
    rw [hω]

/-- Pair-law counterpart for all integer moments of the centred count. -/
theorem count_moment_pairMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (E m : ℝ) (q : ℕ) (k l : ZMod n) :
    (∫⁻ ω, ENNReal.ofReal |(BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m| ^ q
      ∂pairMassMeasure S k l) =
      ∫⁻ ω, ENNReal.ofReal |(BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m| ^ q ∂μ := by
  apply lintegral_pairMassMeasure_eq
  · exact (ENNReal.measurable_ofReal.comp
      (((measurable_countBelow_real E).comp hX).sub measurable_const).abs).pow_const q
  · intro s
    filter_upwards [hXinv s] with ω hω
    rw [hω]

/-- All integer moments of the displacement of the fixed rank `i` (one-based rank `i.val + 1`)
from the reference energy `e` are unchanged under the block-mass law. -/
theorem rank_moment_blockMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (i : Fin N) (e : ℝ) (q : ℕ) (k : ZMod n) :
    (∫⁻ ω, ENNReal.ofReal |X ω i - e| ^ q ∂blockMassMeasure S k) =
      ∫⁻ ω, ENNReal.ofReal |X ω i - e| ^ q ∂μ := by
  apply lintegral_blockMassMeasure_eq
  · exact (ENNReal.measurable_ofReal.comp
      ((measurable_pi_apply i).comp hX |>.sub measurable_const).abs).pow_const q
  · intro s
    filter_upwards [hXinv s] with ω hω
    rw [hω]

/-- The pair law preserves the same prescribed-rank displacement moment. -/
theorem rank_moment_pairMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (i : Fin N) (e : ℝ) (q : ℕ) (k l : ZMod n) :
    (∫⁻ ω, ENNReal.ofReal |X ω i - e| ^ q ∂pairMassMeasure S k l) =
      ∫⁻ ω, ENNReal.ofReal |X ω i - e| ^ q ∂μ := by
  apply lintegral_pairMassMeasure_eq
  · exact (ENNReal.measurable_ofReal.comp
      ((measurable_pi_apply i).comp hX |>.sub measurable_const).abs).pow_const q
  · intro s
    filter_upwards [hXinv s] with ω hω
    rw [hω]

/-- Equality of the count seminorms at every extended order `p`, so count bounds transfer with the
same constant. -/
theorem count_eLpNorm_blockMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (E m : ℝ) (p : ℝ≥0∞) (k : ZMod n) :
    eLpNorm (fun ω => (BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m) p
      (blockMassMeasure S k) =
      eLpNorm (fun ω => (BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m) p μ :=
  eLpNorm_comp_blockMassMeasure_eq S X hX hXinv
    (fun v => (BlockBand.RankLocation.countBelow v E : ℝ) - m)
    ((measurable_countBelow_real E).sub measurable_const) p k

/-- Pair-law equality of the count seminorms. -/
theorem count_eLpNorm_pairMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (E m : ℝ) (p : ℝ≥0∞) (k l : ZMod n) :
    eLpNorm (fun ω => (BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m) p
      (pairMassMeasure S k l) =
      eLpNorm (fun ω => (BlockBand.RankLocation.countBelow (X ω) E : ℝ) - m) p μ :=
  eLpNorm_comp_pairMassMeasure_eq S X hX hXinv
    (fun v => (BlockBand.RankLocation.countBelow v E : ℝ) - m)
    ((measurable_countBelow_real E).sub measurable_const) p k l

/-- Prescribed-rank displacement seminorm equality under block bias. -/
theorem rank_eLpNorm_blockMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (i : Fin N) (e : ℝ) (p : ℝ≥0∞) (k : ZMod n) :
    eLpNorm (fun ω => X ω i - e) p (blockMassMeasure S k) =
      eLpNorm (fun ω => X ω i - e) p μ :=
  eLpNorm_comp_blockMassMeasure_eq S X hX hXinv
    (fun v => v i - e) ((measurable_pi_apply i).sub measurable_const) p k

/-- Prescribed-rank displacement seminorm equality under pair bias. -/
theorem rank_eLpNorm_pairMassMeasure_eq
    (S : CyclicMassSymmetry μ n) (X : Ω → Fin N → ℝ) (hX : Measurable X)
    (hXinv : ∀ s, ∀ᵐ ω ∂μ, X (S.shift s ω) = X ω)
    (i : Fin N) (e : ℝ) (p : ℝ≥0∞) (k l : ZMod n) :
    eLpNorm (fun ω => X ω i - e) p (pairMassMeasure S k l) =
      eLpNorm (fun ω => X ω i - e) p μ :=
  eLpNorm_comp_pairMassMeasure_eq S X hX hXinv
    (fun v => v i - e) ((measurable_pi_apply i).sub measurable_const) p k l

end BlockBand.RankLocation.MassTransport
