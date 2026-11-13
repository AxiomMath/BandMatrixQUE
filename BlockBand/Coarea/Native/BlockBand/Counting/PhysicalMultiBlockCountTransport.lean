module

public import BlockBand.Coarea.Native.BlockBand.Counting.IndependentRandomBackgroundFactorial
public import BlockBand.Coarea.Native.BlockBand.Model.GaussianRing
public import Mathlib.Probability.IdentDistrib

/-!
# Joint multi-block transport for physical Gaussian-ring counts

The physical diagonal blocks have amplitude `sqrt p.c` relative to the normalized
multi-block GUE law used by PSSS.  This module isolates the exact remaining joint-law
statement: after dividing spectral coordinates by `sqrt p.c`, the physical count has
the law of a normalized multi-block GUE with an independent random Hermitian
background.

The interface is deliberately explicit.  It does not manufacture the simultaneous
multi-block disintegration from `GaussianRing.Law`; a future constructor must prove its
`IdentDistrib` field from upper-coordinate independence.  Once supplied, all
falling-factorial and unfolded exponential estimates transfer with the physical
constant `K_b = input.C / sqrt p.c`.  No absorber occurs because eigenvalue counts
require a Hermitian matrix.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GaussianRing

universe u

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Constant physical block sizes, indexed in the normalized PSSS convention. -/
def physicalBlockSizes (p : Params) : Fin p.n → ℕ := fun _ => p.W

/-- Every physical block size is positive. -/
theorem physicalBlockSizes_pos (p : Params) :
    ∀ j, 0 < physicalBlockSizes p j := fun _ => p.W_pos

/-- The normalized joint block index has the physical dimension `nW`. -/
theorem card_physicalBlockIndex (p : Params) :
    Fintype.card (BlockGUE.Index (physicalBlockSizes p)) = p.n * p.W := by
  rw [blockGUE_dimension]
  simp [physicalBlockSizes]

/-- Exact joint-law input needed to transport PSSS estimates to a physical count.

`N a b ω` is the desired physical eigenvalue count in `[a,b]`.  The normalized model
has `n` independent width-`W` GUE blocks and a random Hermitian deformation on the
auxiliary space `Ξ`.  The product law `ν.prod G.P` encodes independence of the entire
background from the joint GUE family.  `count_identDistrib` includes both the spectral
scaling by `sqrt p.c` and any required reindexing of physical sites.

The dimension bound is stated pointwise because the exponential expansion is finite.
For a matrix eigenvalue count it follows immediately from the matrix dimension. -/
structure PhysicalMultiBlockCountTransport
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (p : Params)
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ) : Prop where
  measurable_background : Measurable A₀
  count_identDistrib : ∀ a b,
    IdentDistrib (N a b)
      (BlockGUE.randomBackgroundIntervalCount G A₀
        (a / Real.sqrt p.c) (b / Real.sqrt p.c))
      μ (ν.prod G.P)
  count_le_dimension : ∀ a b ω, N a b ω ≤ p.n * p.W

/-- Falling-factorial transforms preserve the physical/normalized count law. -/
theorem PhysicalMultiBlockCountTransport.factorial_identDistrib
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {p : Params}
    {G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p)}
    {A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p))}
    {N : ℝ → ℝ → Ω → ℕ}
    (h : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    (a b : ℝ) (r : ℕ) :
    IdentDistrib (fun ω => ((N a b ω).descFactorial r : ℝ))
      (fun z => ((BlockGUE.randomBackgroundIntervalCount G A₀
        (a / Real.sqrt p.c) (b / Real.sqrt p.c) z).descFactorial r : ℝ))
      μ (ν.prod G.P) := by
  have hu : Measurable (fun n : ℕ => ((n.descFactorial r : ℕ) : ℝ)) := by
    have hdesc : Measurable (fun n : ℕ => n.descFactorial r) := measurable_from_nat
    have hcast : Measurable (fun n : ℕ => (n : ℝ)) := measurable_from_nat
    exact hcast.comp hdesc
  simpa [Function.comp_def] using (h.count_identDistrib a b).comp hu

/-- Physical falling factorials are integrable after joint-law transport. -/
theorem PhysicalMultiBlockCountTransport.factorialIntegrable
    (input : PSSSInput.{u})
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    {p : Params}
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (h : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    {a b : ℝ} (hab : a ≤ b) (r : ℕ) :
    Integrable (fun ω => ((N a b ω).descFactorial r : ℝ)) μ := by
  have hs : 0 < Real.sqrt p.c := Real.sqrt_pos.2 p.c_pos
  have hab' : a / Real.sqrt p.c ≤ b / Real.sqrt p.c :=
    div_le_div_of_nonneg_right hab hs.le
  have hrhs := psss_randomBackground_factorialIntegrable input
    (physicalBlockSizes_pos p) G ν A₀ h.measurable_background
    (a / Real.sqrt p.c) (b / Real.sqrt p.c) hab' r
  exact (h.factorial_identDistrib a b r).integrable_iff.mpr hrhs

/-- **Physical all-order factorial estimate from the joint transport.**  The exact
constant is `K_b = input.C / sqrt p.c`. -/
theorem PhysicalMultiBlockCountTransport.factorialCount
    (input : PSSSInput.{u})
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    {p : Params}
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (h : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    {a b : ℝ} (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    ∫ ω, ((N a b ω).descFactorial r : ℝ) ∂μ ≤
      ((input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) * (b - a)) ^ r := by
  have hs : 0 < Real.sqrt p.c := Real.sqrt_pos.2 p.c_pos
  have hab' : a / Real.sqrt p.c ≤ b / Real.sqrt p.c :=
    div_le_div_of_nonneg_right hab hs.le
  have hbound := psss_randomBackground_factorialCount input
    (physicalBlockSizes_pos p) G ν A₀ h.measurable_background
    (a / Real.sqrt p.c) (b / Real.sqrt p.c) hab' r hr
  have heq := (h.factorial_identDistrib a b r).integral_eq
  rw [heq]
  calc
    (∫ z, ((BlockGUE.randomBackgroundIntervalCount G A₀
        (a / Real.sqrt p.c) (b / Real.sqrt p.c) z).descFactorial r : ℝ)
        ∂(ν.prod G.P)) ≤
      (input.C * (Fintype.card (BlockGUE.Index (physicalBlockSizes p)) : ℝ) *
        (b / Real.sqrt p.c - a / Real.sqrt p.c)) ^ r := hbound
    _ = ((input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) * (b - a)) ^ r := by
      rw [card_physicalBlockIndex]
      push_cast
      congr 1
      field_simp [ne_of_gt hs]

/-- Physical exponential count estimate obtained from the transported factorial family. -/
theorem PhysicalMultiBlockCountTransport.countExponential
    (input : PSSSInput.{u})
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {p : Params}
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (h : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    let q := (input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) * (b - a)
    ∫ ω, Real.exp (t * (N a b ω : ℝ)) ∂μ ≤
      Real.exp (q * (Real.exp t - 1)) := by
  dsimp only
  let D := p.n * p.W
  let q := (input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) * (b - a)
  have hs : 0 < Real.sqrt p.c := Real.sqrt_pos.2 p.c_pos
  have hq : 0 ≤ q := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg input.C_nonneg hs.le)
        (mul_nonneg (Nat.cast_nonneg p.n) (Nat.cast_nonneg p.W)))
      (sub_nonneg.mpr hab)
  apply integral_exp_count_le_of_factorialMoments μ (N a b) D q t
  · exact h.count_le_dimension a b
  · exact hq
  · exact ht
  · intro r hrange
    exact h.factorialIntegrable input μ ν G A₀ N hab r
  · intro r hrange
    cases r with
    | zero => simp
    | succ r =>
        simpa [q, D] using h.factorialCount input μ ν G A₀ N hab (r + 1)
          (Nat.succ_le_succ (Nat.zero_le r))

/-- Physical unfolded count associated with a transported interval-count family. -/
def transportedUnfoldedIntervalCount
    {Ω : Type u} (N : ℝ → ℝ → Ω → ℕ)
    (e L ρ R : ℝ) (ω : Ω) : ℕ :=
  N (e - R / (L * ρ)) (e + R / (L * ρ)) ω

/-- **Physical unfolded exponential estimate.**  The output constant is exactly
`K_b / ρ`, where `K_b = input.C / sqrt p.c`. -/
theorem PhysicalMultiBlockCountTransport.unfoldedCountExponential
    (input : PSSSInput.{u})
    {Ω Ξ : Type u} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {p : Params}
    (G : BlockGUE.Law.{u} (physicalBlockSizes p) (physicalBlockSizes_pos p))
    (A₀ : Ξ → HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)))
    (N : ℝ → ℝ → Ω → ℕ)
    (h : PhysicalMultiBlockCountTransport μ ν p G A₀ N)
    (e L ρ R t : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hdim : (p.n * p.W : ℝ) ≤ L) (ht : 0 ≤ t) :
    ∫ ω, Real.exp (t *
      (transportedUnfoldedIntervalCount N e L ρ R ω : ℝ)) ∂μ ≤
      Real.exp (2 * R * ((input.C / Real.sqrt p.c) / ρ) *
        (Real.exp t - 1)) := by
  let a := e - R / (L * ρ)
  let b := e + R / (L * ρ)
  have hLρ : 0 < L * ρ := mul_pos hL hρ
  have hab : a ≤ b := by
    dsimp [a, b]
    have : 0 ≤ R / (L * ρ) := div_nonneg hR hLρ.le
    linarith
  have hbase := h.countExponential input μ ν G A₀ N hab ht
  change (∫ ω, Real.exp (t * (N a b ω : ℝ)) ∂μ) ≤ _
  calc
    (∫ ω, Real.exp (t * (N a b ω : ℝ)) ∂μ) ≤
      Real.exp (((input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) * (b - a)) *
        (Real.exp t - 1)) := hbase
    _ ≤ Real.exp (2 * R * ((input.C / Real.sqrt p.c) / ρ) *
        (Real.exp t - 1)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _
        (sub_nonneg.mpr (Real.one_le_exp ht))
      have hKnonneg : 0 ≤ input.C / Real.sqrt p.c :=
        div_nonneg input.C_nonneg (Real.sqrt_nonneg _)
      have hKdim : (input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) ≤
          (input.C / Real.sqrt p.c) * L :=
        mul_le_mul_of_nonneg_left hdim hKnonneg
      have hwidth : b - a = 2 * R / (L * ρ) := by
        dsimp [a, b]
        ring
      rw [hwidth]
      calc
        (input.C / Real.sqrt p.c) * (p.n * p.W : ℝ) *
            (2 * R / (L * ρ)) ≤
          ((input.C / Real.sqrt p.c) * L) * (2 * R / (L * ρ)) := by
            exact mul_le_mul_of_nonneg_right hKdim
              (div_nonneg (mul_nonneg (by norm_num) hR) hLρ.le)
        _ = 2 * R * ((input.C / Real.sqrt p.c) / ρ) := by field_simp

end GaussianRing
end CoareaNative.BlockBand
