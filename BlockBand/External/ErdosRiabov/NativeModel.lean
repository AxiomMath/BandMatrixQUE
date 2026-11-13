module

public import Mathlib

/-!
# The generic band-matrix model of Erdős–Riabov (Definition 2.1)

arXiv:2506.06441v1, Definition 2.1, (2.1)–(2.4), and Definition 2.9. The model constants are
fixed before `N, W`, the variance profile `S` and the law. `H_{ab} = √S_{ab} h_{ab}` under the
given probability measure. The upper-triangular standardized entries are independent, centered,
of variance one, with every moment uniformly bounded. Both the real symmetric and the complex
Hermitian classes are included. The complex second-moment condition is off diagonal, as the
factor `δ_{a≠b}` in (5.3) of the paper makes explicit; imposing it on the real diagonal entries
would contradict (2.4). No Gaussian, ring, spatial decay, local law or remote Schatten hypothesis
is part of this model. All random variables are measurable;
finite moments have ordinary Bochner integrability, not default-zero semantics.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.External.ErdosRiabov

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The real or complex symmetry class. -/
inductive SymmetryClass where
  | realSymmetric
  | complexHermitian
  deriving DecidableEq

/-- Definition 2.9 parameters, fixed uniformly before N,W and all deterministic
model and control data. `δ₀ < ζ₀` is the scale choice stated in the paper. -/
structure ModelParameters where
  zeta0 : ℝ
  delta0 : ℝ
  kappa : ℝ
  C0 : ℝ
  CW : ℝ
  C1 : ℝ
  C2 : ℝ
  c2 : ℝ
  DPrime : ℝ
  momentBound : ℕ → ℝ
  zeta0_pos : 0 < zeta0
  delta0_pos : 0 < delta0
  delta0_lt_zeta0 : delta0 < zeta0
  kappa_pos : 0 < kappa
  C0_ge_one : 1 ≤ C0
  CW_pos : 0 < CW
  C1_ge_one : 1 ≤ C1
  C2_pos : 0 < C2
  c2_pos : 0 < c2
  DPrime_pos : 0 < DPrime

/-- Definition 2.1's full deterministic profile hypotheses, including the
bandwidth lower bound, with `Fin N` indexing of the cycle. -/
structure NativeProfile (p : ModelParameters) (N W : ℕ)
    (S : Matrix (Fin N) (Fin N) ℝ) : Prop where
  N_pos : 0 < N
  W_pos : 0 < W
  W_le_N : W ≤ N
  bandwidth : (N : ℝ) ^ (1 + p.zeta0) ≤ (W : ℝ) ^ 2
  symmetric : ∀ i j, S i j = S j i
  nonnegative : ∀ i j, 0 ≤ S i j
  columnStochastic : ∀ j, ∑ i, S i j = 1
  flat : ∀ i j, S i j ≤ p.CW / (W : ℝ)

/-- Row stochasticity follows from the column normalization of the profile. -/
theorem NativeProfile.rowStochastic {p : ModelParameters} {N W : ℕ}
    {S : Matrix (Fin N) (Fin N) ℝ} (hS : NativeProfile p N W S) (i : Fin N) :
    ∑ j, S i j = 1 := by
  simpa only [hS.symmetric i] using hS.columnStochastic i

/-- The upper coordinate index `{(a, b) : a ≤ b}`. -/
def UpperPair (N : ℕ) := {q : Fin N × Fin N // q.1 ≤ q.2}

/-- A probability model with all moments of Definition 2.1 explicit.
This structure contains no spectral, control, concentration or desired-output field. -/
structure NativeLaw (p : ModelParameters) (N W : ℕ) where
  Ω : Type*
  mΩ : MeasurableSpace Ω
  P : @Measure Ω mΩ
  probability : IsProbabilityMeasure P
  symmetry : SymmetryClass
  S : Matrix (Fin N) (Fin N) ℝ
  profile : NativeProfile p N W S
  h : Ω → Matrix (Fin N) (Fin N) ℂ
  hermitian : ∀ ω, (h ω).IsHermitian
  measurable_entry : ∀ i j, @Measurable Ω ℂ mΩ Complex.measurableSpace (fun ω => h ω i j)
  upper_independent :
    @iIndepFun Ω (UpperPair N) mΩ (fun _ => ℂ) (fun _ => Complex.measurableSpace)
      (fun q ω => h ω q.1.1 q.1.2) P
  entry_integrable : ∀ i j, Integrable (fun ω => h ω i j) P
  mean_zero : ∀ i j, (∫ ω, h ω i j ∂P) = 0
  moment_integrable : ∀ (r : ℕ) i j, Integrable (fun ω => ‖h ω i j‖ ^ r) P
  variance_one : ∀ i j, (∫ ω, ‖h ω i j‖ ^ 2 ∂P) = 1
  moment_bound : ∀ (r : ℕ) i j, (∫ ω, ‖h ω i j‖ ^ r ∂P) ≤ p.momentBound r
  real_entries : symmetry = .realSymmetric → ∀ ω i j, (h ω i j).im = 0
  offdiag_square_integrable : symmetry = .complexHermitian →
    ∀ i j, i ≠ j → Integrable (fun ω => (h ω i j) ^ 2) P
  offdiag_square_zero : symmetry = .complexHermitian →
    ∀ i j, i ≠ j → (∫ ω, (h ω i j) ^ 2 ∂P) = 0

instance {p : ModelParameters} {N W : ℕ} (L : NativeLaw p N W) :
    MeasurableSpace L.Ω := L.mΩ

instance {p : ModelParameters} {N W : ℕ} (L : NativeLaw p N W) :
    IsProbabilityMeasure L.P := L.probability

/-- The matrix `H_{ab} = √S_{ab} h_{ab}`. -/
def NativeLaw.matrix {p : ModelParameters} {N W : ℕ} (L : NativeLaw p N W)
    (ω : L.Ω) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (Real.sqrt (L.S i j) : ℂ) * L.h ω i j

/-- The entries of the matrix, as in (2.4) of the paper. -/
theorem NativeLaw.matrix_apply {p : ModelParameters} {N W : ℕ}
    (L : NativeLaw p N W) (ω : L.Ω) (i j : Fin N) :
    L.matrix ω i j = (Real.sqrt (L.S i j) : ℂ) * L.h ω i j := rfl

end BlockBand.External.ErdosRiabov
