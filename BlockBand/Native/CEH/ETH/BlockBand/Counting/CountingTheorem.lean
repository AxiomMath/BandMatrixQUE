module

public import BlockBand.Native.CEH.ETH.BlockBand.Counting.ScaledExponential
public import BlockBand.Native.CEH.ETH.BlockBand.Counting.MarkedProcessTightness

/-!
# The counting theorem package

The finite-matrix conclusions are the exact PSSS falling-factorial estimate,
the unfolded exponential count estimate, and the ordered close-pair bound

`8 𝕂² R a + 16 𝕂² a²`,  where `𝕂 = input.C / ρ`.

The marked-process conclusions are conditional on a weakly convergent
family of laws on a common configuration space.  Openness of finite-window
count and close-pair events, their comparison with the matrix observables,
and closedness of the mark-validity condition are explicit fields of
`CountingTheoremInput`.  Thus the theorem proves the consequences for every
supplied subsequential limit but does not assert tightness, Prokhorov, or the
existence of such a subsequence.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory Filter
open scoped Topology

universe u v w

/-- Rescaled spectral location used in the unfolded point
process: `L ρ (λ - e)`. -/
def BlockGUE.unfoldedLocation
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (ω : M.Ω)
    (i : Fin (Fintype.card (BlockGUE.Index d))) : ℝ :=
  L * ρ * (orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e)

/-- Explicit inputs not already supplied by the PSSS interface.

The three `pair...` fields relate physical and unfolded windows, as needed to apply the abstract
real-line grid. The remaining fields describe a particular weakly convergent family of marked
configuration laws. The configuration type `X` is abstract; a concrete vague marked-measure
topology must satisfy the stated openness and comparison properties. -/
structure CountingTheoremInput
    (psss : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (X : Type v) (α : Type w)
    [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (l : Filter α) [NeBot l] where
  /-- Bulk energy used for unfolding. -/
  e : ℝ
  /-- Size parameter. -/
  L : ℝ
  /-- Positive unfolding density. -/
  ρ : ℝ
  L_pos : 0 < L
  ρ_pos : 0 < ρ
  dimension_le : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L
  pairIntegrable : ∀ (R a : ℝ), 0 ≤ R → 0 < a →
    Integrable
      (fun ω => ((closePairIndices
        (BlockGUE.unfoldedLocation M A₀ e L ρ ω) R a).card : ℝ)) M.P
  pairWindowIntegrable : ∀ (R a : ℝ) (_hR : 0 ≤ R) (_ha : 0 < a)
      (j : Fin (closePairGridSize R a)),
    Integrable
      (fun ω => ((closePairGridWindow
        (BlockGUE.unfoldedLocation M A₀ e L ρ ω) R a j).card.descFactorial 2 : ℝ))
      M.P
  pairWindowMoment : ∀ (R a : ℝ) (_hR : 0 ≤ R) (_ha : 0 < a)
      (j : Fin (closePairGridSize R a)),
    ∫ ω, ((closePairGridWindow
      (BlockGUE.unfoldedLocation M A₀ e L ρ ω) R a j).card.descFactorial 2 : ℝ) ∂M.P
      ≤ (2 * (psss.C / ρ) * a) ^ 2
  approximatingLaw : α → ProbabilityMeasure X
  limitLaw : ProbabilityMeasure X
  weakLimit : Tendsto approximatingLaw l (𝓝 limitLaw)
  /-- Counts on a countable compact-window exhaustion of the marked space. -/
  localCount : ℕ → X → ENNReal
  localCountOpen : ∀ j m : ℕ,
    IsOpen {x | (m : ENNReal) ≤ localCount j x}
  localTailConstant : ℕ → ENNReal
  localTailConstant_ne_top : ∀ j, localTailConstant j ≠ ⊤
  localCountTail : ∀ n j (m : ℕ),
    (approximatingLaw n : Measure X)
      {x | (m : ENNReal) ≤ localCount j x} ≤
        localTailConstant j / (m : ENNReal)
  /-- Radius of the `j`th compact spectral window. -/
  windowRadius : ℕ → ℝ
  windowRadius_nonneg : ∀ j, 0 ≤ windowRadius j
  /-- Open event of a close pair in window `j` at resolution `a`. -/
  limitClosePair : ℕ → ℝ → Set X
  limitClosePairOpen : ∀ j a, 0 < a → IsOpen (limitClosePair j a)
  limitCollision : ℕ → Set X
  collision_subset_closePair : ∀ j a, 0 < a →
    limitCollision j ⊆ limitClosePair j a
  limitClosePairBound : ∀ n j a, 0 < a →
    (approximatingLaw n : Measure X) (limitClosePair j a) ≤
      ENNReal.ofReal
        (8 * (psss.C / ρ) ^ 2 * windowRadius j * a +
          16 * (psss.C / ρ) ^ 2 * a ^ 2)
  validMarks : Set X
  validMarks_closed : IsClosed validMarks
  approximatingMarks_valid : ∀ n,
    (approximatingLaw n : Measure X) validMarksᶜ = 0

/-- Bundled quantitative and weak-limit conclusions of the counting theorem. -/
structure CountingTheoremConclusion
    (psss : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (X : Type v) (α : Type w)
    [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (l : Filter α) [NeBot l]
    (cfg : CountingTheoremInput psss hd M A₀ X α l) where
  factorialCount : ∀ (a b : ℝ), a ≤ b → ∀ r : ℕ, 1 ≤ r →
    ∫ ω, ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ) ∂M.P
      ≤ (psss.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ r
  unfoldedExponential : ∀ (R t : ℝ), 0 ≤ R → 0 ≤ t →
    ∫ ω, Real.exp
      (t * (BlockGUE.unfoldedIntervalCount M A₀ cfg.e cfg.L cfg.ρ R ω : ℝ)) ∂M.P
      ≤ Real.exp (2 * R * (psss.C / cfg.ρ) * (Real.exp t - 1))
  closePairExpectation : ∀ (R a : ℝ), 0 ≤ R → 0 < a →
    ∫ ω, ((closePairIndices
      (BlockGUE.unfoldedLocation M A₀ cfg.e cfg.L cfg.ρ ω) R a).card : ℝ) ∂M.P
      ≤ 8 * (psss.C / cfg.ρ) ^ 2 * R * a +
        16 * (psss.C / cfg.ρ) ^ 2 * a ^ 2
  closePairProbability : ∀ (R a : ℝ), 0 ≤ R → 0 < a →
    M.P (closePairEvent
      (fun ω => BlockGUE.unfoldedLocation M A₀ cfg.e cfg.L cfg.ρ ω) R a) ≤
      ENNReal.ofReal
        (8 * (psss.C / cfg.ρ) ^ 2 * R * a +
          16 * (psss.C / cfg.ρ) ^ 2 * a ^ 2)
  limitLocalCountTail : ∀ j (m : ℕ),
    (cfg.limitLaw : Measure X)
      {x | (m : ENNReal) ≤ cfg.localCount j x} ≤
        cfg.localTailConstant j / (m : ENNReal)
  limitLocallyFinite :
    ∀ᵐ x ∂(cfg.limitLaw : Measure X), ∀ j, cfg.localCount j x ≠ ⊤
  limitClosePairProbability : ∀ (j : ℕ) (a : ℝ), 0 < a →
    (cfg.limitLaw : Measure X) (cfg.limitClosePair j a) ≤
      ENNReal.ofReal
        (8 * (psss.C / cfg.ρ) ^ 2 * cfg.windowRadius j * a +
          16 * (psss.C / cfg.ρ) ^ 2 * a ^ 2)
  limitCollisionFree : ∀ j,
    (cfg.limitLaw : Measure X) (cfg.limitCollision j) = 0
  limitMarksValid :
    (cfg.limitLaw : Measure X) cfg.validMarksᶜ = 0

/-- The counting theorem. It derives every quantitative statement from the PSSS and grid APIs, and
every limiting statement from an explicitly supplied weak limit and its
finite-window topology/comparison hypotheses. -/
theorem countingTheorem
    (psss : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (X : Type v) (α : Type w)
    [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (l : Filter α) [NeBot l]
    (cfg : CountingTheoremInput psss hd M A₀ X α l) :
    CountingTheoremConclusion psss hd M A₀ X α l cfg := by
  refine
    { factorialCount := ?_
      unfoldedExponential := ?_
      closePairExpectation := ?_
      closePairProbability := ?_
      limitLocalCountTail := ?_
      limitLocallyFinite := ?_
      limitClosePairProbability := ?_
      limitCollisionFree := ?_
      limitMarksValid := ?_ }
  · intro a b hab r hr
    exact psss_factorialCount psss hd M A₀ a b hab r hr
  · intro R t hR ht
    exact psss_unfoldedCountExponential psss hd M A₀
      cfg.e cfg.L cfg.ρ R t cfg.L_pos cfg.ρ_pos hR cfg.dimension_le ht
  · intro R a hR ha
    exact integral_closePairIndices_le_manuscript M.P
      (fun ω => BlockGUE.unfoldedLocation M A₀ cfg.e cfg.L cfg.ρ ω)
      hR ha (cfg.pairIntegrable R a hR ha)
      (cfg.pairWindowIntegrable R a hR ha)
      (cfg.pairWindowMoment R a hR ha)
  · intro R a hR ha
    exact measure_closePairEvent_le_manuscript M.P
      (fun ω => BlockGUE.unfoldedLocation M A₀ cfg.e cfg.L cfg.ρ ω)
      hR ha (cfg.pairIntegrable R a hR ha)
      (cfg.pairWindowIntegrable R a hR ha)
      (cfg.pairWindowMoment R a hR ha)
  · intro j m
    exact limit_localCount_tail_le cfg.weakLimit (cfg.localCount j)
      (cfg.localCountOpen j) (cfg.localTailConstant j)
      (fun n m => cfg.localCountTail n j m) m
  · apply ae_localFinite_on_countable_exhaustion
    intro j
    exact measure_infiniteLocalCount_eq_zero cfg.weakLimit
      (cfg.localCount j) (cfg.localCountOpen j)
      (cfg.localTailConstant j) (cfg.localTailConstant_ne_top j)
      (fun n m => cfg.localCountTail n j m)
  · intro j a ha
    exact limit_closePairEvent_le_manuscript cfg.weakLimit
      (cfg.limitClosePair j) (cfg.limitClosePairOpen j) ha
      (fun n => cfg.limitClosePairBound n j a ha)
  · intro j
    let scale : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
    apply measure_limitCollision_eq_zero cfg.weakLimit
      (cfg.limitClosePair j) (cfg.limitCollision j)
      (cfg.limitClosePairOpen j) (cfg.collision_subset_closePair j)
      scale (R := cfg.windowRadius j) (K := psss.C / cfg.ρ)
    · intro n
      dsimp [scale]
      positivity
    · have hscale : Tendsto
          (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [scale, div_eq_mul_inv] using hscale
    · intro n i
      exact cfg.limitClosePairBound i j (scale n) (by
        dsimp [scale]
        positivity)
  · exact measure_compl_closed_eq_zero_of_tendsto cfg.weakLimit
      cfg.validMarks cfg.validMarks_closed cfg.approximatingMarks_valid

end CEHNative.BlockBand
