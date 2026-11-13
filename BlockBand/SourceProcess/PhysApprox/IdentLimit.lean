module

public import BlockBand.SourceProcess.PhysApprox.Assembly
public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability
public import BlockBand.SourceProcess.ComplexCapLimit.Compare
public import BlockBand.SourceProcess.ComplexSplit.Holds

/-!
# Limit points give convergence

This file proves `TargetT7`: `ComplexClosedLimitIdentification` gives
`ComplexCappedClosedIdentification`. It is the complex analogue of
`ClosedIdent.cappedClosedIdentification_of_limits`. The capped closed expectations lie in
`[-‖Φ‖, ‖Φ‖]` (`abs_cappedClosedPhysExpectation_le`), so every subsequence has a convergent further
subsequence; by `ComplexClosedLimitIdentification` its limit is the restricted value of some
complex finite model at `(h, K)`; by restricted uniqueness that value is the same in every model,
so the whole sequence converges to it (`tendsto_of_subseq_tendsto`).

Results: `abs_cappedClosedPhysExpectation_le`; `complexCappedClosedIdentification_of_limits_of`;
`complexRestrictedUniqueness_holds`; **`targetT7_holds : TargetT7`** (no hypotheses).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.CapLimit
open scoped NNReal

/-- **Restricted uniqueness** (`ComplexCapLimit.setIntegral_capSet_eq` at `K' = K` with
`ComplexSplit.complexFiniteUniqueness_holds`; proved below as `complexRestrictedUniqueness_holds`):
on the domain, for `h > 0`, two complex finite models at the same `(h, K)` and entrance have the
same value restricted to `{t_K ≤ h²}`. -/
def ComplexRestrictedUniqueness : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ h : ℝ, 0 < h → ∀ (K : ℕ)
    (entrance : Measure (Measure unitInterval)) (Φ : BoundedContinuousFunction (SourceData np) ℝ)
    (Ω : Type) (mΩ : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc →
  ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 mΩ') (Q' : Measure Ω')
    (tseq' : Ω' → ℕ → ℝ) (G' : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc' : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖' Q' tseq' G' Kc' →
    restrictedModelExpectation K h s T Q tseq G Kc Φ =
      restrictedModelExpectation K h s T Q' tseq' G' Kc' Φ

/-- The capped closed expectation lies in `[-‖Φ‖, ‖Φ‖]`. -/
theorem abs_cappedClosedPhysExpectation_le {b E s T h : ℝ} {np : ℕ} {τ m : Fin np → ℝ}
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (K W : ℕ) :
    |cappedClosedPhysExpectation b E s T h τ m Φ K W| ≤ ‖Φ‖ := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖Φ‖) (ae_of_all _ fun y => ?_)).trans_eq
    (by rw [probReal_univ, mul_one])
  by_cases hy : y.1.1 ∈ physCapEventC b E s h K W
  · rw [Set.indicator_of_mem hy, one_mul]; exact Φ.norm_coe_le_norm _
  · rw [Set.indicator_of_notMem hy, zero_mul, norm_zero]; exact norm_nonneg _

/-- **`ComplexCappedClosedIdentification` from `ComplexClosedLimitIdentification`**, given
restricted uniqueness. -/
theorem complexCappedClosedIdentification_of_limits_of (hU : ComplexRestrictedUniqueness)
    (hL : ComplexClosedLimitIdentification) : ComplexCappedClosedIdentification := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ ε hε
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  refine ((hL b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ).and_eventually hpos).mono
    fun h ⟨hK, hh⟩ => hK.mono fun K hKL => ?_
  intro Ω' mΩ' 𝓖 Q tseq G Kc hMod
  set c := restrictedModelExpectation K h s T Q tseq G Kc Φ
  set x : ℕ → ℝ := fun W => cappedClosedPhysExpectation b E s T h τ m Φ K W
  have hx : Tendsto x atTop (𝓝 c) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨L, -, φ, hφ, hφL⟩ := tendsto_subseq_of_bounded (x := fun n => x (ns n))
      (Metric.isBounded_Icc (-‖Φ‖) ‖Φ‖) fun n =>
        abs_le.1 (abs_cappedClosedPhysExpectation_le (b := b) (E := E) (s := s) (T := T)
          (h := h) (τ := τ) (m := m) Φ K (ns n))
    obtain ⟨Ω₁, m₁, 𝓖₁, Q₁, tseq₁, G₁, Kc₁, hM₁, hval⟩ :=
      hKL (fun n => ns (φ n)) (hns.comp hφ.tendsto_atTop) L hφL
    have heq := hU b E np τ m T hD s hs hτ h hh K _ Φ Ω' mΩ' 𝓖 Q tseq G Kc hMod Ω₁ m₁ 𝓖₁ Q₁
      tseq₁ G₁ Kc₁ hM₁
    refine ⟨φ, ?_⟩
    have : c = L := heq.trans hval
    rw [this]
    exact hφL
  filter_upwards [(tendsto_order.1 hx).1 _ (show c - ε < c by linarith),
    (tendsto_order.1 hx).2 _ (show c < c + ε by linarith)] with W h1 h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- `TargetT7` from restricted uniqueness. -/
theorem targetT7_of_gap (hU : ComplexRestrictedUniqueness) : TargetT7 :=
  complexCappedClosedIdentification_of_limits_of hU

/-- **Restricted uniqueness holds** (from `ComplexCapLimit.setIntegral_capSet_eq`). -/
theorem complexRestrictedUniqueness_holds : ComplexRestrictedUniqueness := by
  intro b E np τ m T hD s hs hτ h hh K entrance Φ Ω mΩ 𝓖 Q tseq G Kc hM Ω' mΩ' 𝓖' Q' tseq' G'
    Kc' hM'
  exact ComplexCapLimit.setIntegral_capSet_eq (T := T) ComplexSplit.complexFiniteUniqueness_holds hD
    hs hτ hh Φ le_rfl hM hM'

/-- **`TargetT7` holds** (no hypotheses). -/
theorem targetT7_holds : TargetT7 :=
  targetT7_of_gap complexRestrictedUniqueness_holds

end BlockBand.SourceProcess.PhysApprox
