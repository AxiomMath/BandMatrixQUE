module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularCalc
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The angular generator is the overlap part of the joint Itô generator

`angularGenerator_eq`: for a `C²` function `f` of the overlaps, the angular generator equals
`Df(X)[b] + ½ ∑ a_ij ∂_i∂_j f(X)` with the overlap drift `ovlDrift` and the overlap covariance
`ovlCov`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open Filter Topology
open scoped NNReal ContDiff
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- Overlap drift `b_i = ∑_{j≠i} c_ij (X_j - X_i)`. -/
def ovlDrift (N : ℕ) (lam X : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, dysonCoupling N lam i j * (X j - X i)

/-- Overlap covariance of `dysonStateCov`. -/
def ovlCov (N : ℕ) (lam X : Fin N → ℝ) (i j : Fin N) : ℝ :=
  if i = j then 2 * ∑ m ∈ Finset.univ.erase i, dysonCoupling N lam i m * X i * X m
  else -2 * dysonCoupling N lam i j * X i * X j

theorem coupling_symm (lam : Fin N → ℝ) (i j : Fin N) :
    dysonCoupling N lam i j = dysonCoupling N lam j i := by
  unfold dysonCoupling; ring

/-- `∑_i ∑_{j>i} S_ij = ½ ∑_i ∑_{j≠i} S_ij` for symmetric `S`. -/
theorem sum_lt_eq_half {S : Fin N → Fin N → ℝ} (hS : ∀ i j, S i j = S j i) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), S i j =
      (1 / 2 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.erase i, S i j := by
  simp only [Finset.sum_filter, ← Finset.filter_ne', Finset.sum_filter]
  have h1 : ∀ i, ∑ j, (if j ≠ i then S i j else 0) =
      ∑ j, (if i < j then S i j else 0) + ∑ j, (if j < i then S i j else 0) := by
    intro i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne, not_lt.2 h.le]
  have h2 : ∑ i, ∑ j, (if j < i then S i j else 0) = ∑ i, ∑ j, (if i < j then S i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hS]
  simp_rw [h1, Finset.sum_add_distrib, h2]
  ring

theorem fderiv2_sub_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {X : E} (hs : IsSymmSndFDerivAt ℝ f X) (u v : E) :
    fderiv ℝ (fderiv ℝ f) X (u - v) (u - v) =
      fderiv ℝ (fderiv ℝ f) X u u + fderiv ℝ (fderiv ℝ f) X v v -
        2 * fderiv ℝ (fderiv ℝ f) X u v := by
  simp only [map_sub, FunLike.coe_sub, Pi.sub_apply]
  rw [hs v u]; ring

/-- **Generator identity.** For `C²` `f`, the angular generator is the overlap block of the
Itô generator: `𝒜 f(X) = Df(X)[b] + ½ ∑ a_ij ∂_i∂_j f(X)`. -/
theorem angularGenerator_eq {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (lam X : Fin N → ℝ) :
    angularGenerator N lam f X = fderiv ℝ f X (ovlDrift N lam X) + (1 / 2 : ℝ) *
      ∑ i, ∑ j, ovlCov N lam X i j * fderiv ℝ (fderiv ℝ f) X (Pi.single i 1) (Pi.single j 1) := by
  have hs : IsSymmSndFDerivAt ℝ f X := (hf.contDiffAt).isSymmSndFDerivAt (by simp)
  set d1 : Fin N → ℝ := fun i => fderiv ℝ f X (Pi.single i 1)
  set d2 : Fin N → Fin N → ℝ := fun i j => fderiv ℝ (fderiv ℝ f) X (Pi.single i 1) (Pi.single j 1)
  have hd2 : ∀ i j, d2 i j = d2 j i := fun i j => hs _ _
  set c : Fin N → Fin N → ℝ := dysonCoupling N lam
  have hc : ∀ i j, c i j = c j i := coupling_symm lam
  set S : Fin N → Fin N → ℝ := fun i j =>
    c i j * (X i * X j * (d2 i i + d2 j j - 2 * d2 i j) + (X j - X i) * (d1 i - d1 j))
  have hSs : ∀ i j, S i j = S j i := fun i j => by
    simp only [S]; rw [hc i j, hd2 i j]; ring
  have hA : angularGenerator N lam f X = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), S i j := by
    unfold angularGenerator
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [S, d1, d2, c]
    rw [fderiv2_sub_sub hs, map_sub]
  rw [hA, sum_lt_eq_half hSs, clm_apply_eq_sum (fderiv ℝ f X)]
  simp only [ovlDrift, ovlCov]
  simp only [← Finset.filter_ne', Finset.sum_filter]
  change (1 / 2 * ∑ x, ∑ a, if a ≠ x then S x a else 0) =
    ∑ x, (∑ a, if a ≠ x then c x a * (X a - X x) else 0) * d1 x + 1 / 2 * ∑ x, ∑ x_1,
      (if x = x_1 then 2 * ∑ a, (if a ≠ x then c x a * X x * X a else 0)
        else -2 * c x x_1 * X x * X x_1) * d2 x x_1
  set A := ∑ i, ∑ j, (if j ≠ i then c i j * X i * X j * d2 i i else 0)
  set B := ∑ i, ∑ j, (if j ≠ i then c i j * X i * X j * d2 i j else 0)
  set C := ∑ i, ∑ j, (if j ≠ i then c i j * (X j - X i) * d1 i else 0)
  have swap : ∀ F : Fin N → Fin N → ℝ, ∑ i, ∑ j, (if j ≠ i then F j i else 0) =
      ∑ i, ∑ j, (if j ≠ i then F i j else 0) := fun F => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  have hL : ∑ i, ∑ j, (if j ≠ i then S i j else 0) = 2 * A - 2 * B + 2 * C := by
    have e : ∀ i j, (if j ≠ i then S i j else 0) =
        (if j ≠ i then c i j * X i * X j * d2 i i else 0) +
        (if j ≠ i then c j i * X j * X i * d2 j j else 0) -
        2 * (if j ≠ i then c i j * X i * X j * d2 i j else 0) +
        (if j ≠ i then c i j * (X j - X i) * d1 i else 0) +
        (if j ≠ i then c j i * (X i - X j) * d1 j else 0) := fun i j => by
      split_ifs
      · simp only [S]; rw [hc j i]; ring
      · ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [swap (fun i j => c i j * X i * X j * d2 i i),
      swap (fun i j => c i j * (X j - X i) * d1 i)]
    ring
  have split : ∀ (i : Fin N) (P : ℝ) (Q g : Fin N → ℝ),
      ∑ j, (if i = j then P else Q j) * g j = P * g i + ∑ j, (if j ≠ i then Q j * g j else 0) := by
    intro i P Q g
    calc ∑ j, (if i = j then P else Q j) * g j =
        ∑ j, ((if i = j then P * g i else 0) + (if j ≠ i then Q j * g j else 0)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases h : i = j
          · subst h; simp
          · simp [h, Ne.symm h]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq]; simp
  have hR1 : ∑ x, (∑ a, if a ≠ x then c x a * (X a - X x) else 0) * d1 x = C := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> ring
  have hR2 : ∑ x, ∑ x_1, (if x = x_1 then 2 * ∑ a, (if a ≠ x then c x a * X x * X a else 0)
        else -2 * c x x_1 * X x * X x_1) * d2 x x_1 = 2 * A - 2 * B := by
    simp only [split]
    have e : 2 * A - 2 * B = ∑ x, (2 * ∑ j, (if j ≠ x then c x j * X x * X j * d2 x x else 0) -
        2 * ∑ j, (if j ≠ x then c x j * X x * X j * d2 x j else 0)) := by
      simp only [A, B, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hL, hR1, hR2]; ring

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
