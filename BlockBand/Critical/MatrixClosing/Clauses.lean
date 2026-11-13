module

public import BlockBand.Critical.MatrixClosing.CollarFunction
public import BlockBand.Critical.Herglotz.Statement

/-!
# Matrix closing: the three hypotheses of the Herglotz tail lemma for the collar

* `OldSequence b κ r`: deterministic old data along which the proof argues: widths
  `W_n → ∞`, energies in `bulkInterval κ`, Hermitian `X_n` with `d(X_n) → 0`, orthonormal frames.
* `OldSequence.collarFns`: the collar functions `F_{W_n}`.
* One clause per hypothesis of the Herglotz tail lemma, each the corresponding field of
  `Herglotz.HerglotzTailHypotheses` for `F_{W_n}` under `collarLaw`: `CollarPolesClause` (poles),
  `CollarMeanClause` (mean), `CollarBoundaryClause` (boundary). They are the three steps of the
  proof of the matrix closing theorem. `CollarMeanClause` is proved in
  `Mean.collarMeanClause_of_inputs` and `CollarBoundaryClause` in
  `Boundary.collarBoundaryClause_of_exactBoundaryMean`. `CollarPolesClause` is false at frame rank
  `r = 0`; the rank-wise `Poles.CollarPolesAt r` for `r ≥ 1` is used
  instead (`Poles.matrixClosing_of_clauses_pos`).
* `herglotzTailHypotheses_of_clauses`: the clauses and the joint measurability
  (`measurable_collarFunction_eval`) give `HerglotzTailHypotheses`.
* `instBorelSpaceMatrixFamily`: the product Borel structure on `Fin k → Matrix (Fin r) (Fin r) ℂ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz

/-- The product Borel structure on finite families of matrices. -/
instance instBorelSpaceMatrixFamily (k r : ℕ) : BorelSpace (Fin k → Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (BorelSpace (Fin k → Fin r → Fin r → ℂ))

/-- An admissible sequence of deterministic old data along which the matrix closing theorem is
proved (its sequential uniformity is proved by contradiction along a violating old deterministic
sequence): widths `W_n → ∞`, energies in `bulkInterval κ`, lossless (Hermitian) old
reactions with `d(X_n) → 0`, orthonormal frames. -/
structure OldSequence (b κ : ℝ) (r : ℕ) where
  W : ℕ → ℕ
  e : ℕ → ℝ
  X : ∀ n, Matrix (Fin 2 × Fin (W n)) (Fin 2 × Fin (W n)) ℂ
  J : ∀ n, Matrix (Fin 2 × Fin (W n)) (Fin r) ℂ
  W_pos : ∀ n, 0 < W n
  tendsto_W : Tendsto W atTop atTop
  e_mem : ∀ n, e n ∈ bulkInterval κ
  X_herm : ∀ n, (X n).IsHermitian
  tendsto_d : Tendsto (fun n => matchedDistance b (e n) (X n)) atTop (𝓝 0)
  J_frame : ∀ n, (J n)ᴴ * J n = 1

variable {b κ : ℝ} {r : ℕ}

/-- The collar functions `F_{W_n}` along an old sequence. -/
def OldSequence.collarFns (S : OldSequence b κ r) :
    ∀ n, CollarSample (S.W n) → AtomicHerglotz r :=
  fun n ω => collarFunction b (S.e n) (S.X n) (S.J n) ω

/-!
## The three hypotheses of the Herglotz tail lemma for the collar
-/

/-- **Hypothesis 1 for the collar** (the local atoms): along every admissible old
sequence, the marked poles and residues of `F_{W_n}` converge jointly in law to those of the
canonical Cauchy series (field `poles` of `HerglotzTailHypotheses`), for every decorated sine
process `Ξ`. -/
def CollarPolesClause : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (r : ℕ) (S : OldSequence b κ r)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))), IsDecoratedSineProcess r P' Ξ →
    ∀ (m : ℕ) (f : Fin m → CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ),
      TendstoInDistribution (fun N ω k => (S.collarFns N ω).atomSum (f k)) atTop
        (fun ω k => ∫ p, f k (p.1, canonicalResidue p.2) ∂(Ξ ω).measure)
        (fun N => collarLaw (S.W N) b) P'

/-- **Hypothesis 2 for the collar** (the mean of the whole spectrum): along every
admissible old sequence, `E Im F_{W_n}(iY) → I_r` for every `Y > 0` (field `mean` of
`HerglotzTailHypotheses`). -/
def CollarMeanClause : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (r : ℕ) (S : OldSequence b κ r),
    ∀ Y : ℝ, 0 < Y → ∀ i j : Fin r,
      Tendsto (fun N => ∫ ω, CoareaNative.BlockBand.matrixImaginaryPart
          ((S.collarFns N ω).eval ((Y : ℂ) * Complex.I)) i j ∂collarLaw (S.W N) b)
        atTop (𝓝 ((1 : Matrix (Fin r) (Fin r) ℂ) i j))

/-- **Hypothesis 3 for the collar** (the Cauchy boundary law): along every admissible
old sequence, for every real `x` and `v ∈ ℂ^r`, `v*F_{W_n}(x)v` converges in law to the Cauchy law
of center `0` and scale `‖v‖²` (field `boundary` of `HerglotzTailHypotheses`). -/
def CollarBoundaryClause : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (r : ℕ) (S : OldSequence b κ r),
    ∀ (x : ℝ) (v : Fin r → ℂ),
      TendstoInDistribution (fun N ω => ((S.collarFns N ω).quadForm v x).re) atTop id
        (fun N => collarLaw (S.W N) b) (ProbabilityTheory.cauchyMeasure 0 (euclidSqNorm v))

/-- The three clauses give the hypotheses of the Herglotz tail lemma for `F_{W_n}` (joint
measurability: `measurable_collarFunction_eval`). -/
theorem herglotzTailHypotheses_of_clauses (h1 : CollarPolesClause) (h2 : CollarMeanClause)
    (h3 : CollarBoundaryClause) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {r : ℕ} (S : OldSequence b κ r) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (hΞ : IsDecoratedSineProcess r P' Ξ) :
    HerglotzTailHypotheses r (fun N => collarLaw (S.W N) b) S.collarFns P' Ξ where
  measurable_eval N i j := measurable_collarFunction_eval b (S.e N) (S.X N) (S.J N) i j
  poles := h1 b hb0 hb κ hκ r S Ω' P' Ξ hΞ
  mean := h2 b hb0 hb κ hκ r S
  boundary := h3 b hb0 hb κ hκ r S

end BlockBand.Critical.MatrixClosing
