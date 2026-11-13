module

public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.ResolventIdentities
public import BlockBand.Native.CEH.ETH.BlockBand.Coarea.HermitianCoordinates
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Normalized finite-dimensional Ornstein–Uhlenbeck infrastructure

This file contains the unconditional, finite-dimensional part of the
Ornstein–Uhlenbeck argument used in the CEH input.  The normalization is

`H_t = exp (-t/2) F + exp (-t/2) X + sqrt (1-exp (-t)) Y`.

Thus a centered variance-`1/N` Hermitian Gaussian coordinate stays at variance
`1/N`; the deterministic deformation is damped by `exp (-t/2)`.  We do not
state a local law or hide one in a structure.  The probability-specific input
needed to identify `X,Y` as independent GUE coordinates remains visible at the
point where it is used; the coefficient algebra, deterministic resolvent increments, stopping wrappers, and finite
Cauchy estimates below are proved identities.  No equality-in-law or continuous-time
stochastic-calculus theorem is claimed here.

The resolvent expansion is a deterministic finite-increment identity, including
its cubic remainder.  It is not a continuous-time Itô formula or a martingale
estimate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

/-- Drift coefficient for the normalized Hermitian OU flow. -/
def ouDecay (t : ℝ) : ℝ := Real.exp (-t / 2)

/-- Fresh-noise coefficient for the normalized Hermitian OU flow. -/
def ouNoise (t : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-t))

/-- The OU drift coefficient is strictly positive. -/
theorem ouDecay_pos (t : ℝ) : 0 < ouDecay t := by
  exact Real.exp_pos _

/-- The fresh-noise variance is nonnegative for forward time. -/
theorem ouNoise_rad_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-t) := by
  rw [sub_nonneg]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

/-- The two coefficients split unit variance. -/
theorem ouDecay_sq_add_ouNoise_sq {t : ℝ} (ht : 0 ≤ t) :
    ouDecay t ^ 2 + ouNoise t ^ 2 = 1 := by
  rw [ouDecay, ouNoise, Real.sq_sqrt (ouNoise_rad_nonneg ht)]
  have he : Real.exp (-t / 2) * Real.exp (-t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [pow_two, he]
  ring

/-- Semigroup law for the drift coefficient. -/
theorem ouDecay_add (s t : ℝ) :
    ouDecay (s + t) = ouDecay s * ouDecay t := by
  simp only [ouDecay]
  rw [show -(s + t) / 2 = -s / 2 + -t / 2 by ring, Real.exp_add]

/-- Entrywise normalized Hermitian OU interpolation with deterministic
initial deformation `F` and independent centered coordinates `X,Y`. -/
def hermitianOU {n : ℕ} (t : ℝ)
    (F X Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (ouDecay t : ℂ) • (F + X) + (ouNoise t : ℂ) • Y

/-- The defining OU formula holds entry by entry. -/
theorem hermitianOU_apply {n : ℕ} (t : ℝ)
    (F X Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    hermitianOU t F X Y i j =
      ouDecay t * (F i j + X i j) + ouNoise t * Y i j := by
  simp [hermitianOU]
  ring

/-- The interpolation preserves Hermitian symmetry. -/
theorem hermitianOU_isHermitian {n : ℕ} {t : ℝ}
    {F X Y : Matrix (Fin n) (Fin n) ℂ}
    (hF : F.IsHermitian) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (hermitianOU t F X Y).IsHermitian := by
  exact (hF.add hX).smul (RCLike.conj_ofReal _)
    |>.add (hY.smul (RCLike.conj_ofReal _))

/-- Scalar version of the OU coordinate, useful for real and imaginary GUE
coordinates separately. -/
def scalarOU (t f x y : ℝ) : ℝ :=
  ouDecay t * (f + x) + ouNoise t * y

/-- Centered OU covariance calculation.  This is the exact calculation behind
GUE stationarity: equal input variances and zero cross covariance give the
same centered second moment. -/
theorem scalarOU_centered_second_moment {t v x₂ y₂ xy : ℝ}
    (ht : 0 ≤ t) (hx : x₂ = v) (hy : y₂ = v) (hxy : xy = 0) :
    ouDecay t ^ 2 * x₂ + 2 * ouDecay t * ouNoise t * xy +
        ouNoise t ^ 2 * y₂ = v := by
  subst x₂
  subst y₂
  subst xy
  rw [mul_zero, add_zero]
  rw [← add_mul, ouDecay_sq_add_ouNoise_sq ht, one_mul]

/-- Variance `1/N` is stationary in every normalized diagonal GUE coordinate. -/
theorem normalized_diagonal_variance_stationary {n : ℕ} (_hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) :
    ouDecay t ^ 2 * (1 / (n : ℝ)) +
        ouNoise t ^ 2 * (1 / (n : ℝ)) = 1 / (n : ℝ) := by
  have h := ouDecay_sq_add_ouNoise_sq ht
  calc
    _ = (ouDecay t ^ 2 + ouNoise t ^ 2) * (1 / (n : ℝ)) := by ring
    _ = _ := by rw [h, one_mul]

/-- Variance `1/(2N)` is stationary in each real/imaginary off-diagonal GUE
coordinate. -/
theorem normalized_offDiagonal_variance_stationary {n : ℕ} (_hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) :
    ouDecay t ^ 2 * (1 / (2 * (n : ℝ))) +
        ouNoise t ^ 2 * (1 / (2 * (n : ℝ))) = 1 / (2 * (n : ℝ)) := by
  have h := ouDecay_sq_add_ouNoise_sq ht
  calc
    _ = (ouDecay t ^ 2 + ouNoise t ^ 2) * (1 / (2 * (n : ℝ))) := by ring
    _ = _ := by rw [h, one_mul]

/-- Measurable coordinate maps preserve independence.  This is the exact
independence transport used after applying the deterministic OU coefficients. -/
theorem indepFun_ou_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (a b : ℝ) :
    IndepFun (fun ω => a * X ω) (fun ω => b * Y ω) P := by
  simpa [Function.comp_def] using
    hXY.comp (measurable_const_mul a) (measurable_const_mul b)

/-- Deterministic deformation does not affect independence from fresh noise. -/
theorem indepFun_ou_deformation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (a b f : ℝ) :
    IndepFun (fun ω => a * (f + X ω)) (fun ω => b * Y ω) P := by
  have hm : Measurable (fun x : ℝ => a * (f + x)) := by fun_prop
  simpa [Function.comp_def] using
    hXY.comp hm (measurable_const_mul b)

/-!
## Exact matrix Itô / resolvent increment formula
-/

/-- Exact first resolvent increment under a Hermitian matrix perturbation. -/
theorem matrixResolvent_add_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    CEHNative.BlockBand.matrixResolvent (A + D) z -
        CEHNative.BlockBand.matrixResolvent A z =
      CEHNative.BlockBand.matrixResolvent (A + D) z * D *
        CEHNative.BlockBand.matrixResolvent A z := by
  unfold CEHNative.BlockBand.matrixResolvent
  rw [Matrix.inv_sub_inv]
  · congr 2
    abel
  · constructor
    · exact fun _ => CEHNative.BlockBand.isUnit_resolventPencil A hA hz
    · exact fun _ => CEHNative.BlockBand.isUnit_resolventPencil
        (A + D) (hA.add hD) hz

/-- Exact second-order resolvent expansion.  The last term is the cubic Itô
remainder; there is no omitted `o(dt)` term. -/
theorem matrixResolvent_secondOrder_increment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    let G := CEHNative.BlockBand.matrixResolvent A z
    let G' := CEHNative.BlockBand.matrixResolvent (A + D) z
    G' - G = G * D * G + G' * D * G * D * G := by
  dsimp
  have h₁ := matrixResolvent_add_sub A D hA hD hz
  have h₂ := matrixResolvent_add_sub A D hA hD hz
  calc
    _ = CEHNative.BlockBand.matrixResolvent (A + D) z * D *
          CEHNative.BlockBand.matrixResolvent A z := h₁
    _ = CEHNative.BlockBand.matrixResolvent A z * D *
          CEHNative.BlockBand.matrixResolvent A z +
        (CEHNative.BlockBand.matrixResolvent (A + D) z -
          CEHNative.BlockBand.matrixResolvent A z) * D *
          CEHNative.BlockBand.matrixResolvent A z := by
      rw [show CEHNative.BlockBand.matrixResolvent (A + D) z =
          CEHNative.BlockBand.matrixResolvent A z +
            (CEHNative.BlockBand.matrixResolvent (A + D) z -
              CEHNative.BlockBand.matrixResolvent A z) by abel]
      noncomm_ring
    _ = _ := by rw [h₂]

/-- Entrywise form of the exact deterministic second-order resolvent increment. -/
theorem matrixResolvent_secondOrder_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i j : ι) :
    let G := CEHNative.BlockBand.matrixResolvent A z
    let G' := CEHNative.BlockBand.matrixResolvent (A + D) z
    G' i j - G i j = (G * D * G) i j + (G' * D * G * D * G) i j := by
  have h := matrixResolvent_secondOrder_increment A D hA hD hz
  simpa [Matrix.sub_apply] using congrFun₂ h i j

/-!
## Affine comparison flow with fixed `m`
-/

/-- Explicit semigroup for the auxiliary affine equation `ż = -z/2 + m` with constant `m`.
This is not the CEH time-dependent characteristic, whose drift contains the
MDE trace with its coupling and opposite sign.
-/
def frozenAffineFlow (t : ℝ) (z m : ℂ) : ℂ :=
  (Real.exp (-t / 2) : ℂ) * z + (2 : ℂ) * (1 - Real.exp (-t / 2)) * m

/-- The auxiliary affine flow starts at `z`. -/
theorem frozenAffineFlow_zero (z m : ℂ) : frozenAffineFlow 0 z m = z := by
  simp [frozenAffineFlow]

/-- Semigroup identity for the auxiliary affine flow. -/
theorem frozenAffineFlow_add (s t : ℝ) (z m : ℂ) :
    frozenAffineFlow (s + t) z m =
      frozenAffineFlow s (frozenAffineFlow t z m) m := by
  simp only [frozenAffineFlow]
  rw [show -(s + t) / 2 = -s / 2 + -t / 2 by ring, Real.exp_add]
  push_cast
  ring

/-!
## Stopping-time measurability
-/

/-- A hitting time of a measurable target by an adapted discrete process is a
stopping time.  This wrapper fixes the precise measurability needed in CEH. -/
theorem isStoppingTime_hittingBtwn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration ℕ mΩ) {f : ℕ → Ω → ℝ}
    (hf : Adapted 𝓕 f) {S : Set ℝ} (hS : MeasurableSet S) (a b : ℕ) :
    IsStoppingTime 𝓕 (fun ω => (hittingBtwn f S a b ω : ℕ)) :=
  hf.isStoppingTime_hittingBtwn hS

/-- The decision event of a stopping time is measurable with the information
available at that time. -/
theorem stoppingTime_event_measurable
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Preorder ι]
    (𝓕 : Filtration ι mΩ) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) (i : ι) :
    MeasurableSet[𝓕 i] {ω | τ ω ≤ i} :=
  hτ i

/-!
## Quadratic variation and finite-dimensional Cauchy bounds
-/

/-- Pathwise quadratic variation of finitely many real increments. -/
def finiteQuadraticVariation {κ : Type*} (s : Finset κ) (d : κ → ℝ) : ℝ :=
  ∑ k ∈ s, (d k) ^ 2

/-- Quadratic variation is nonnegative. -/
theorem finiteQuadraticVariation_nonneg {κ : Type*} (s : Finset κ) (d : κ → ℝ) :
    0 ≤ finiteQuadraticVariation s d := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Finite-dimensional deterministic Cauchy estimate for a scalar sum.
No martingale, expectation, or BDG theorem is used. -/
theorem finite_cauchy_l2 {κ : Type*} (s : Finset κ)
    (a d : κ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k ∈ s, |a k| ≤ K) :
    (∑ k ∈ s, a k * d k) ^ 2 ≤
      (s.card : ℝ) * K ^ 2 * finiteQuadraticVariation s d := by
  have hcs :
      (∑ k ∈ s, a k * d k) ^ 2 ≤
        (∑ k ∈ s, (a k * d k) ^ 2) * (s.card : ℝ) := by
    simpa using
      (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (r := fun k => a k * d k)
        (f := fun k => (a k * d k) ^ 2) (g := fun _ => (1 : ℝ))
        (fun _ _ => sq_nonneg _) (fun _ _ => zero_le_one)
        (fun k hk => by simp))
  calc
    (∑ k ∈ s, a k * d k) ^ 2 ≤
        (∑ k ∈ s, (a k * d k) ^ 2) * (s.card : ℝ) := hcs
    _ ≤ ((∑ k ∈ s, K ^ 2 * d k ^ 2) * (s.card : ℝ)) := by
      gcongr with k hk
      have hs : (a k) ^ 2 ≤ K ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hK).2 (ha k hk)
      nlinarith [sq_nonneg (d k)]
    _ = (s.card : ℝ) * K ^ 2 * finiteQuadraticVariation s d := by
      simp only [finiteQuadraticVariation]
      have hfactor :
          (∑ k ∈ s, K ^ 2 * d k ^ 2) =
            K ^ 2 * ∑ k ∈ s, d k ^ 2 := by
        rw [Finset.mul_sum]
      calc
        (∑ k ∈ s, K ^ 2 * d k ^ 2) * (s.card : ℝ) =
            (s.card : ℝ) * (∑ k ∈ s, K ^ 2 * d k ^ 2) := mul_comm _ _
        _ = (s.card : ℝ) * (K ^ 2 * ∑ k ∈ s, d k ^ 2) := by rw [hfactor]
        _ = (s.card : ℝ) * K ^ 2 * ∑ k ∈ s, d k ^ 2 := by ring

/-- Coordinatewise finite-dimensional Cauchy estimate: summing the scalar estimates costs
exactly the displayed finite dimension and no hidden infinite-dimensional
constant. -/
theorem finite_coordinate_cauchy {κ ι : Type*} [Fintype ι]
    (s : Finset κ) (a d : ι → κ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ i k, k ∈ s → |a i k| ≤ K) :
    (∑ i, (∑ k ∈ s, a i k * d i k) ^ 2) ≤
      (s.card : ℝ) * K ^ 2 * ∑ i, finiteQuadraticVariation s (d i) := by
  calc
    _ ≤ ∑ i, ((s.card : ℝ) * K ^ 2 * finiteQuadraticVariation s (d i)) := by
      gcongr with i
      exact finite_cauchy_l2 s (a i) (d i) hK (ha i)
    _ = _ := by rw [← Finset.mul_sum]

end CEHNative.BlockBand.CEH
