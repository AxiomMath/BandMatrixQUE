module
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.DefectLyapunov
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The trace martingale `Tr M = ‖V‖²`

Nonexplosion step of the finite Gram law (local strong uniqueness and the nonnegative trace
martingale `Tr M` give nonexplosion). Deterministic content, on the
constraint set `TwoProjection P D V`:

* `trace_gram_drift_eq_zero`: the Itô drift of `Tr M` vanishes;
* `trace_gram_bracket`: `∑_a (d Tr M)_a² = D₀ Tr(B C₀)` (from the MM bracket);
* `trace_gram_noise_le`: every noise coefficient of `Tr M` is at most
  `√D₀ (card c) Naux · Tr M` in modulus — a bound uniform in `V` (no radius), because the
  constraint forces `‖P'‖²_F = Naux` (`frob_sq_gramProjection`).
Frobenius norm throughout; `Tr M = ‖V‖²` (`sourceGram_trace`).
-/

namespace BlockBand.SourceProcess.Stochastic.SourceAlgebra
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

omit [DecidableEq ι] in
/-- `‖A‖²_F = Tr(AᴴA)`. -/
theorem frob_sq_eq_trace {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ((‖A‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A).trace := by
  rw [frob_sq]
  push_cast
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.star_def,
    Complex.conj_mul']
  exact Finset.sum_comm

omit [DecidableEq ι] in
/-- `Tr M = ‖V‖²`. -/
theorem sourceGram_trace (V : Matrix ι c ℂ) : (sourceGram V).trace = ((‖V‖ ^ 2 : ℝ) : ℂ) := by
  rw [frob_sq_eq_trace, sourceGram]

omit [DecidableEq ι] in
/-- Under the constraint, `‖P'‖²_F = Naux`. -/
theorem frob_sq_gramProjection {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux) (hV : TwoProjection P D V) :
    ‖gramProjection P V D‖ ^ 2 = Naux := by
  have h := frob_sq_eq_trace (gramProjection P V D)
  rw [hV.1, hV.2.1, hV.2.2, hP.2.2] at h
  exact_mod_cast h

omit [DecidableEq ι] [Fintype c] in
/-- `‖P‖²_F = Naux`. -/
theorem frob_sq_nearProjection {Naux : ℕ} {P : Matrix ι ι ℂ} (hP : IsNearProjection P Naux) :
    ‖P‖ ^ 2 = Naux := by
  have h := frob_sq_eq_trace P
  rw [hP.1, hP.2.1, hP.2.2] at h
  exact_mod_cast h

/-- **The trace `Tr M` has zero Itô drift** under the constraint. -/
theorem trace_gram_drift_eq_zero {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) : (quadDrift D0 Naux P 1 D V).trace = 0 := by
  rw [gram_drift_M hD0 hP hV, trace_zero]

/-- **Quadratic variation of `Tr M`**: `∑_a (d Tr M)_a² = D₀ Tr(B C₀)` under the constraint. -/
theorem trace_gram_bracket {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) :
    ∑ a, (gramNoise D0 P D a V).1.trace * (gramNoise D0 P D a V).1.trace =
      (D0 : ℂ) * (nearGram P V * gramC0 (sourceGram V) (nearGram P V) D).trace := by
  simp only [Matrix.trace, Matrix.diag, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := SourceNoise ι))]
  simp only [gram_bracket_MM hD0 hP hV, crossedBracket, Finset.mul_sum, Matrix.mul_apply,
    Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

/-- **Noise of `Tr M` is bounded by `C · Tr M`** under the constraint, uniformly in `V`:
`|(d Tr M)_a| ≤ √D₀ (card c) Naux ‖V‖²`. -/
theorem trace_gram_noise_le (D0 : ℝ) {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux) (hV : TwoProjection P D V)
    (a : SourceNoise ι) :
    ‖(gramNoise D0 P D a V).1.trace‖ ≤ Real.sqrt D0 * Fintype.card c * Naux * ‖V‖ ^ 2 := by
  have hPp : ‖gramProjection P V D‖ = Real.sqrt Naux := by
    rw [← frob_sq_gramProjection hP hV, Real.sqrt_sq (norm_nonneg _)]
  have hPn : ‖P‖ = Real.sqrt Naux := by
    rw [← frob_sq_nearProjection hP, Real.sqrt_sq (norm_nonneg _)]
  have hσ : ‖sourceDiffusion D0 P D a V‖ ≤ Real.sqrt D0 / 2 * Naux * ‖V‖ := by
    rw [sourceDiffusion_eq, sourceNoiseMatrix, Matrix.smul_mul, norm_smul, norm_sourceWeight]
    calc Real.sqrt D0 / 2 * ‖gramProjection P V D * sourceUnit a * P * V‖
        ≤ Real.sqrt D0 / 2 * (‖gramProjection P V D‖ * ‖sourceUnit a‖ * ‖P‖ * ‖V‖) := by
          gcongr; exact frob_mul4_le _ _ _ _
      _ = Real.sqrt D0 / 2 * Naux * ‖V‖ := by
          rw [hPp, hPn, sourceUnit, frob_single, mul_one, ← sq,
            Real.sq_sqrt (Nat.cast_nonneg _)]
          ring
  set σ := sourceDiffusion D0 P D a V
  have hn : (0 : ℝ) ≤ Fintype.card c := Nat.cast_nonneg _
  calc ‖(gramNoise D0 P D a V).1.trace‖ = ‖(σᴴ * V).trace + (Vᴴ * σ).trace‖ := by
        rw [gramNoise, gramVariation, trace_add]
    _ ≤ Fintype.card c * (‖σ‖ * ‖V‖) + Fintype.card c * (‖V‖ * ‖σ‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (frob_trace_le _).trans ?_
          gcongr
          exact (frobenius_norm_mul _ _).trans (by rw [frobenius_norm_conjTranspose])
        · refine (frob_trace_le _).trans ?_
          gcongr
          exact (frobenius_norm_mul _ _).trans (by rw [frobenius_norm_conjTranspose])
    _ ≤ Fintype.card c * ((Real.sqrt D0 / 2 * Naux * ‖V‖) * ‖V‖) +
          Fintype.card c * (‖V‖ * (Real.sqrt D0 / 2 * Naux * ‖V‖)) := by gcongr
    _ = Real.sqrt D0 * Fintype.card c * Naux * ‖V‖ ^ 2 := by ring

end BlockBand.SourceProcess.Stochastic.SourceAlgebra
