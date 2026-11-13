module

public import BlockBand.External.ErdosRiabov.Control

/-!
# The `k = 1` observables and controls of Erdős–Riabov

arXiv:2506.06441v1, Definition 3.1 and (3.17)–(3.18).
Every diagonal complex observable is encoded by its unrestricted diagonal.
The triple norm is the infimum (equivalently, the minimum in the paper) of the sum of
nonnegative coefficients majorizing `|A_qq|` by `Σ_i a_i S_iq`. A feasible
majorant is constructed for every `A`, so the infimum is never over the empty set.
Vector norms are Euclidean Hilbert norms, not the sup norm on a finite function type.
`Υ_uv` retains every coordinate weight. The resolvent is `(H - zI)⁻¹`, and `Tr` is the
unnormalized trace. No ring law or change of resolvent sign is involved.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.External.ErdosRiabov

open MeasureTheory
open scoped BigOperators

/-- Euclidean complex vectors, with their Hilbert norm. -/
abbrev Vector (N : ℕ) := EuclideanSpace ℂ (Fin N)

/-- The coefficient majorant of (3.8) for an arbitrary diagonal observable. -/
def ObservableMajorant {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → ℂ) (a : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∀ q, ‖A q‖ ≤ ∑ i, a i * S i q)

/-- The triple norm of the paper: the infimum of the total feasible majorant mass.
For a stochastic profile the feasible set is nonempty and bounded
below. Finite-dimensional LP compactness makes this the minimum of the paper;
only its value is used for `k = 1`, so no choice of minimizer is needed. -/
def observableNorm {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → ℂ) : ℝ :=
  sInf {t : ℝ | ∃ a : Fin N → ℝ, ObservableMajorant S A a ∧ t = ∑ i, a i}

/-- Every diagonal test has a feasible majorant, without a norm cutoff. -/
theorem observableMajorant_const {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ} (hS : NativeProfile p N W S)
    (A : Fin N → ℂ) :
    ObservableMajorant S A (fun _ => ∑ q, ‖A q‖) := by
  constructor
  · intro i
    exact Finset.sum_nonneg (fun q _ => norm_nonneg (A q))
  · intro q
    rw [← Finset.mul_sum, hS.columnStochastic q, mul_one]
    exact Finset.single_le_sum (fun i _ => norm_nonneg (A i)) (Finset.mem_univ q)

/-- Summing the diagonal majorization retains the exact unnormalized mass. -/
theorem sum_norm_le_majorant_mass {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ} (hS : NativeProfile p N W S)
    {A : Fin N → ℂ} {a : Fin N → ℝ} (ha : ObservableMajorant S A a) :
    (∑ q, ‖A q‖) ≤ ∑ i, a i := by
  calc
    (∑ q, ‖A q‖) ≤ ∑ q, ∑ i, a i * S i q :=
      Finset.sum_le_sum (fun q _ => ha.2 q)
    _ = ∑ i, a i := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hS.rowStochastic, mul_one]

/-- The triple norm bounds `Σ |A_qq|`; in particular it is nonnegative. -/
theorem sum_norm_le_observableNorm {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ} (hS : NativeProfile p N W S)
    (A : Fin N → ℂ) : (∑ q, ‖A q‖) ≤ observableNorm S A := by
  unfold observableNorm
  apply le_csInf
  · exact ⟨∑ i : Fin N, ∑ q, ‖A q‖,
      (fun _ => ∑ q, ‖A q‖), observableMajorant_const hS A, rfl⟩
  · intro t ht
    obtain ⟨a, ha, rfl⟩ := ht
    exact sum_norm_le_majorant_mass hS ha

/-- Definition (3.9), with arbitrary deterministic Euclidean vectors. -/
def vectorControl {N : ℕ} (Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (η : ℝ) (u v : Vector N) : ℝ :=
  ∑ i, ∑ j, ‖u i‖ ^ 2 * Upsilon η i j * ‖v j‖ ^ 2

/-- The `k = 1` isotropic control is nonnegative on the interval. -/
theorem vectorControl_nonneg {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ}
    {Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ}
    (hU : AdmissibleControl p N W S Upsilon) {η : ℝ}
    (hη : ControlHeight p N η) (u v : Vector N) :
    0 ≤ vectorControl Upsilon η u v := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (hU.entrywisePositive η hη i j).le)
    (sq_nonneg _)

/-- The resolvent `(H - z)⁻¹`, with the sign convention of the paper. -/
def resolvent {p : ModelParameters} {N W : ℕ} (L : NativeLaw p N W)
    (z : ℂ) (ω : L.Ω) : Matrix (Fin N) (Fin N) ℂ :=
  (L.matrix ω - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- The error `G - mI`, for the matrix `NativeLaw.matrix` and the concrete branch of `m`. -/
def resolventError {p : ModelParameters} {N W : ℕ} (L : NativeLaw p N W)
    (z : ℂ) (ω : L.Ω) : Matrix (Fin N) (Fin N) ℂ :=
  resolvent L z ω - semicircleM z • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- The matrix pairing `u* R v`, with conjugation on `u`. -/
def matrixPairing {N : ℕ} (R : Matrix (Fin N) (Fin N) ℂ)
    (u v : Vector N) : ℂ :=
  ∑ i, star (u i) * (∑ j, R i j * v j)

/-- The isotropic bad event for stochastic domination (1.9). -/
def isotropicBad {p : ModelParameters} {N W : ℕ} (L : NativeLaw p N W)
    (Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (u v : Vector N) (ξ : ℝ) : Set L.Ω :=
  {ω | (N : ℝ) ^ ξ * Real.sqrt (vectorControl Upsilon |z.im| u v) <
    ‖matrixPairing (resolventError L z ω) u v‖}

/-- The averaged bad event: the trace is unnormalized and `A` is any diagonal. -/
def averagedBad {p : ModelParameters} {N W : ℕ} (L : NativeLaw p N W)
    (z : ℂ) (A : Fin N → ℂ) (ξ : ℝ) : Set L.Ω :=
  {ω | (N : ℝ) ^ ξ * (observableNorm L.S A /
      (localizationLength N W |z.im| * |z.im|)) <
    ‖Matrix.trace (resolventError L z ω * Matrix.diagonal A)‖}

/-- The deterministic isotropic `M`-bound from (3.18), for every nonreal `z`. -/
theorem semicircle_isotropic_bound {N : ℕ} {z : ℂ} (hz : z.im ≠ 0)
    (u v : Vector N) :
    ‖semicircleM z * inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [norm_mul]
  calc
    ‖semicircleM z‖ * ‖inner ℂ u v‖ ≤ 1 * ‖inner ℂ u v‖ :=
      mul_le_mul_of_nonneg_right (norm_semicircleM_lt_one hz).le (norm_nonneg _)
    _ ≤ ‖u‖ * ‖v‖ := by simpa only [one_mul] using norm_inner_le_norm u v

/-- The deterministic averaged `M`-bound (3.18) with the triple norm. -/
theorem semicircle_averaged_bound {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ} (hS : NativeProfile p N W S)
    {z : ℂ} (hz : z.im ≠ 0) (A : Fin N → ℂ) :
    ‖semicircleM z * ∑ q, A q‖ ≤ observableNorm S A := by
  rw [norm_mul]
  calc
    ‖semicircleM z‖ * ‖∑ q, A q‖ ≤ 1 * ‖∑ q, A q‖ :=
      mul_le_mul_of_nonneg_right (norm_semicircleM_lt_one hz).le (norm_nonneg _)
    _ ≤ ∑ q, ‖A q‖ := by simpa only [one_mul] using norm_sum_le Finset.univ A
    _ ≤ observableNorm S A := sum_norm_le_observableNorm hS A

end BlockBand.External.ErdosRiabov
