module

public import BlockBand.Native.ErdosRiabov.Split.MTermsStatement
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# Deterministic `M`-terms: basic infrastructure

Infrastructure for the proofs of the `Split` statements on the deterministic `M`-terms (the
recursive definition of Erdős–Riabov, arXiv 2506.06441v1, at profile `σ S`). It proves no `Split`
statement itself; it supplies the lemmas used for the explicit short chains, the zero-time values,
cyclicity, the Ward identity and the derivative.

Setting: `n : ℕ`, a profile `S : Matrix (Fin n) (Fin n) ℝ` with `ProfileHyp S` (nonnegative,
symmetric, row sums `1`), a scale `σ ∈ [0,1]`, spectral data `m : ℕ → ℂ` with `‖m i‖ < 1`, diagonal
observables `A : ℕ → Fin n → ℂ`. Each hypothesis is assumed only by the lemmas that need it.

Main declarations.
* Stability operator `K = stabOp σ S a = (1 - σ a S)⁻¹` for `‖a‖ < 1`:
  `isUnit_one_sub_smul_profileC` (strict diagonal dominance + Gershgorin),
  `stabOp_mulVec_one_sub`, `one_sub_mulVec_stabOp`, `stabOp_mulVec_eq_iff`,
  `stabOp_mulVec_sub_one` (`K - 1 = σ a S K`), `stabOp_mulVec_sub_one'` (`K - 1 = σ a K S`),
  `stabOp_mul_profileC_comm` (`K S = S K`, no hypotheses), the symmetry lemmas
  `profileC_transpose`, `stabOp_transpose`, `dotProduct_stabOp_mulVec`,
  `dotProduct_selfEnergy`, `dotProduct_mul_assoc`, the constant vectors
  `selfEnergy_const`, `stabOp_mulVec_const`, and the `σ`-derivative
  `hasDerivAt_stabOp_mulVec` (`d/dσ K v = K (a S (K v))`; also the vector form
  `hasDerivAt_stabOp_mulVec_pi` and the varying-vector form
  `hasDerivAt_stabOp_mulVec_of_hasDerivAt`).
* Chains: `chainTilde_of_le`, `chainTilde_self`, `chainTilde_of_lt`,
  `one_sub_mulVec_chainTilde`, `chainTilde_one_step`, `chainTilde_recursion2`
  (the second form of the recursion), `chainTilde_congr` (locality), `chainTilde_shift`, and for
  `chainM`:
  `chainM_eq_smul`, `chainM_self`, `chainM_of_gt`, `chainM_congr`, `chainM_shift`.

Proof: Gershgorin (`Matrix.det_ne_zero_of_sum_row_lt_diag`) gives invertibility of
`1 - c S` for `‖c‖ < 1`; the operator identities are matrix-inverse algebra. The derivative is
proved from the resolvent identity `K_s - K_σ = (s - σ) K_s (a S) K_σ` and continuity of the matrix
inverse at a unit (`continuousAt_matrix_inv`), via the slope characterisation of `HasDerivAt`.
The chain lemmas unfold `chainTilde_eq` and use strong induction on `k - j`.

Inputs: Mathlib; `BlockBand.Native.ErdosRiabov.Split.MTermsStatement` (definitions and
`chainTilde_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MTerms

open BlockBand.Native.ErdosRiabov.Split Matrix Finset Filter
open scoped Topology

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} {σ : ℝ} {m : ℕ → ℂ} {A : ℕ → Fin n → ℂ}

/-!
### Profile and invertibility
-/

/-- Entries of the complexified profile. -/
theorem profileC_apply (S : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    profileC S a b = (S a b : ℂ) := rfl

/-- Strict diagonal dominance: for `‖c‖ < 1`, `det (1 - c S) ≠ 0`, since
`|1 - c S_aa| ≥ 1 - |c| S_aa > |c| ∑_{b ≠ a} S_ab = |c| (1 - S_aa)`. -/
theorem det_one_sub_smul_profileC_ne_zero (hS : ProfileHyp S) {c : ℂ} (hc : ‖c‖ < 1) :
    (1 - c • profileC S).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  have hoff : ∀ j ∈ univ.erase k, ‖(1 - c • profileC S) k j‖ = ‖c‖ * S k j := by
    intro j hj
    have hkj : k ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [Matrix.sub_apply, one_apply_ne hkj, Matrix.smul_apply, profileC_apply, zero_sub, norm_neg, smul_eq_mul,
      norm_mul, Complex.norm_of_nonneg (hS.nonneg k j)]
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum]
  have hrow : ∑ j ∈ univ.erase k, S k j = 1 - S k k := by
    rw [← hS.rowSum k, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    ring
  have hdiag : 1 - ‖c‖ * S k k ≤ ‖(1 - c • profileC S) k k‖ := by
    rw [Matrix.sub_apply, one_apply_eq, Matrix.smul_apply, profileC_apply, smul_eq_mul]
    calc 1 - ‖c‖ * S k k = ‖(1 : ℂ)‖ - ‖c * (S k k : ℂ)‖ := by
          rw [norm_one, norm_mul, Complex.norm_of_nonneg (hS.nonneg k k)]
      _ ≤ ‖(1 : ℂ) - c * (S k k : ℂ)‖ := norm_sub_norm_le _ _
  rw [hrow]
  have h0 : 0 ≤ S k k := hS.nonneg k k
  nlinarith [norm_nonneg c]

/-- `det (1 - c S)` is a unit for `‖c‖ < 1`. -/
theorem isUnit_det_one_sub_smul_profileC (hS : ProfileHyp S) {c : ℂ} (hc : ‖c‖ < 1) :
    IsUnit (1 - c • profileC S).det :=
  isUnit_iff_ne_zero.mpr (det_one_sub_smul_profileC_ne_zero hS hc)

/-- `1 - c S` is invertible for `‖c‖ < 1`. -/
theorem isUnit_one_sub_smul_profileC (hS : ProfileHyp S) {c : ℂ} (hc : ‖c‖ < 1) :
    IsUnit (1 - c • profileC S) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_one_sub_smul_profileC hS hc)

/-- `‖σ a‖ < 1` for `σ ∈ [0,1]`, `‖a‖ < 1`. -/
theorem norm_sigma_mul_lt_one (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ} (ha : ‖a‖ < 1) :
    ‖(σ : ℂ) * a‖ < 1 := by
  rw [norm_mul, Complex.norm_of_nonneg hσ.1]
  nlinarith [norm_nonneg a, hσ.1, hσ.2]

/-- `‖a b‖ < 1` for `‖a‖ < 1`, `‖b‖ < 1`. -/
theorem norm_mul_lt_one_of_lt_one {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg a, norm_nonneg b]

/-!
### The stability operator
-/

/-- `det (1 - σ a S)` is a unit for `σ ∈ [0,1]`, `‖a‖ < 1`. -/
theorem isUnit_det_stab (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) : IsUnit (1 - ((σ : ℂ) * a) • profileC S).det :=
  isUnit_det_one_sub_smul_profileC hS (norm_sigma_mul_lt_one hσ ha)

/-- `K (1 - σ a S) = 1`. -/
theorem stabOp_mul_one_sub (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) : stabOp σ S a * (1 - ((σ : ℂ) * a) • profileC S) = 1 :=
  nonsing_inv_mul _ (isUnit_det_stab hS hσ ha)

/-- `(1 - σ a S) K = 1`. -/
theorem one_sub_mul_stabOp (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) : (1 - ((σ : ℂ) * a) • profileC S) * stabOp σ S a = 1 :=
  mul_nonsing_inv _ (isUnit_det_stab hS hσ ha)

/-- `K ((1 - σ a S) v) = v`. -/
theorem stabOp_mulVec_one_sub (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (v : Fin n → ℂ) :
    stabOp σ S a *ᵥ ((1 - ((σ : ℂ) * a) • profileC S) *ᵥ v) = v := by
  rw [mulVec_mulVec, stabOp_mul_one_sub hS hσ ha, one_mulVec]

/-- `(1 - σ a S) (K v) = v`. -/
theorem one_sub_mulVec_stabOp (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (v : Fin n → ℂ) :
    (1 - ((σ : ℂ) * a) • profileC S) *ᵥ (stabOp σ S a *ᵥ v) = v := by
  rw [mulVec_mulVec, one_sub_mul_stabOp hS hσ ha, one_mulVec]

/-- `K v = w ↔ v = (1 - σ a S) w`. -/
theorem stabOp_mulVec_eq_iff (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (v w : Fin n → ℂ) :
    stabOp σ S a *ᵥ v = w ↔ v = (1 - ((σ : ℂ) * a) • profileC S) *ᵥ w := by
  constructor
  · rintro rfl
    exact (one_sub_mulVec_stabOp hS hσ ha v).symm
  · rintro rfl
    exact stabOp_mulVec_one_sub hS hσ ha w

/-- `K v - v = σ a S (K v)` (i.e. `K - 1 = σ a S K`). -/
theorem stabOp_mulVec_sub_one (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (v : Fin n → ℂ) :
    stabOp σ S a *ᵥ v - v = ((σ : ℂ) * a) • (profileC S *ᵥ (stabOp σ S a *ᵥ v)) := by
  have h := one_sub_mulVec_stabOp hS hσ ha v
  rw [sub_mulVec, one_mulVec, smul_mulVec] at h
  calc stabOp σ S a *ᵥ v - v
      = stabOp σ S a *ᵥ v -
          (stabOp σ S a *ᵥ v - ((σ : ℂ) * a) • (profileC S *ᵥ (stabOp σ S a *ᵥ v))) := by
        rw [h]
    _ = _ := sub_sub_cancel _ _

/-- `K S = S K` (no hypotheses: if `1 - σ a S` is singular, both sides are `0`). -/
theorem stabOp_mul_profileC_comm (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (a : ℂ) :
    stabOp σ S a * profileC S = profileC S * stabOp σ S a := by
  unfold stabOp
  set M := 1 - ((σ : ℂ) * a) • profileC S with hM
  have hc : M * profileC S = profileC S * M := by
    rw [hM, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  by_cases h : IsUnit M.det
  · calc M⁻¹ * profileC S = M⁻¹ * profileC S * (M * M⁻¹) := by
          rw [mul_nonsing_inv _ h, mul_one]
      _ = M⁻¹ * (M * profileC S) * M⁻¹ := by
          rw [hc]
          simp only [mul_assoc]
      _ = profileC S * M⁻¹ := by
          rw [← mul_assoc, nonsing_inv_mul _ h, one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ h, zero_mul, mul_zero]

/-- `K (S v) = S (K v)`. -/
theorem stabOp_mulVec_profileC_mulVec (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (a : ℂ)
    (v : Fin n → ℂ) :
    stabOp σ S a *ᵥ (profileC S *ᵥ v) = profileC S *ᵥ (stabOp σ S a *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, stabOp_mul_profileC_comm]

/-- `K v - v = σ a K (S v)` (i.e. `K - 1 = σ a K S`). -/
theorem stabOp_mulVec_sub_one' (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (v : Fin n → ℂ) :
    stabOp σ S a *ᵥ v - v = ((σ : ℂ) * a) • (stabOp σ S a *ᵥ (profileC S *ᵥ v)) := by
  rw [stabOp_mulVec_profileC_mulVec, stabOp_mulVec_sub_one hS hσ ha]

/-!
### Symmetry for the bilinear pairing `⬝ᵥ`
-/

/-- `Sᵀ = S` for the complexified profile. -/
theorem profileC_transpose (hS : ProfileHyp S) : (profileC S)ᵀ = profileC S := by
  ext a b
  rw [transpose_apply, profileC_apply, profileC_apply, hS.symm b a]

/-- `Kᵀ = K`. -/
theorem stabOp_transpose (hS : ProfileHyp S) (σ : ℝ) (a : ℂ) :
    (stabOp σ S a)ᵀ = stabOp σ S a := by
  unfold stabOp
  rw [transpose_nonsing_inv, transpose_sub, transpose_one, transpose_smul, profileC_transpose hS]

/-- `(K u) ⬝ᵥ v = u ⬝ᵥ (K v)`. -/
theorem dotProduct_stabOp_mulVec (hS : ProfileHyp S) (σ : ℝ) (a : ℂ) (u v : Fin n → ℂ) :
    (stabOp σ S a *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (stabOp σ S a *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, stabOp_transpose hS]

/-- `S[u] ⬝ᵥ v = u ⬝ᵥ S[v]`. -/
theorem dotProduct_selfEnergy (hS : ProfileHyp S) (u v : Fin n → ℂ) :
    selfEnergy S u ⬝ᵥ v = u ⬝ᵥ selfEnergy S v := by
  unfold selfEnergy
  rw [dotProduct_mulVec, ← mulVec_transpose, profileC_transpose hS]

/-- `(u * v) ⬝ᵥ w = u ⬝ᵥ (v * w)` (pointwise products). -/
theorem dotProduct_mul_assoc (u v w : Fin n → ℂ) : (u * v) ⬝ᵥ w = u ⬝ᵥ (v * w) := by
  simp only [dotProduct, Pi.mul_apply, mul_assoc]

/-!
### Constant vectors
-/

/-- `S` fixes constant vectors (row sums `1`). -/
theorem profileC_mulVec_const (hS : ProfileHyp S) (c : ℂ) :
    profileC S *ᵥ (fun _ => c) = fun _ => c := by
  funext x
  simp only [mulVec, dotProduct, profileC_apply]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hS.rowSum x, Complex.ofReal_one, one_mul]

/-- `S[c] = c` for constant `c`. -/
theorem selfEnergy_const (hS : ProfileHyp S) (c : ℂ) :
    selfEnergy S (fun _ => c) = fun _ => c :=
  profileC_mulVec_const hS c

/-- `1 - σ a ≠ 0` for `σ ∈ [0,1]`, `‖a‖ < 1`. -/
theorem one_sub_sigma_mul_ne_zero (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ} (ha : ‖a‖ < 1) :
    (1 : ℂ) - (σ : ℂ) * a ≠ 0 := by
  intro h
  have h1 : (σ : ℂ) * a = 1 := by linear_combination -h
  have h2 := norm_sigma_mul_lt_one hσ ha
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- `K c = c / (1 - σ a)` for constant `c`. -/
theorem stabOp_mulVec_const (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (c : ℂ) :
    stabOp σ S a *ᵥ (fun _ => c) = fun _ => c / (1 - (σ : ℂ) * a) := by
  have hne := one_sub_sigma_mul_ne_zero hσ ha
  rw [stabOp_mulVec_eq_iff hS hσ ha, sub_mulVec, one_mulVec, smul_mulVec,
    profileC_mulVec_const hS]
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-!
### Derivative in `σ`
-/

/-- `s ↦ 1 - s a S` is continuous. -/
theorem continuous_one_sub_smul_profileC (S : Matrix (Fin n) (Fin n) ℝ) (a : ℂ) :
    Continuous fun s : ℝ => (1 : Matrix (Fin n) (Fin n) ℂ) - ((s : ℂ) * a) • profileC S := by
  fun_prop

/-- `s ↦ K_s = stabOp s S a` is continuous at `σ`. -/
theorem continuousAt_stabOp (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) : ContinuousAt (fun s : ℝ => stabOp s S a) σ := by
  have hinv : ContinuousAt Inv.inv (1 - ((σ : ℂ) * a) • profileC S) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (det_one_sub_smul_profileC_ne_zero hS (norm_sigma_mul_lt_one hσ ha))
  exact hinv.comp (f := fun s : ℝ => (1 : Matrix (Fin n) (Fin n) ℂ) - ((s : ℂ) * a) • profileC S)
    (continuous_one_sub_smul_profileC S a).continuousAt

/-- `1 - s a S` is invertible for `s` near `σ`. -/
theorem eventually_isUnit_det (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) : ∀ᶠ s : ℝ in 𝓝 σ, IsUnit (1 - ((s : ℂ) * a) • profileC S).det := by
  have hdet : ContinuousAt (fun s : ℝ => (1 - ((s : ℂ) * a) • profileC S).det) σ :=
    (continuous_one_sub_smul_profileC S a).matrix_det.continuousAt
  exact (hdet.eventually_ne
    (det_one_sub_smul_profileC_ne_zero hS (norm_sigma_mul_lt_one hσ ha))).mono
    fun _ hs => isUnit_iff_ne_zero.mpr hs

/-- Resolvent identity: `K_s w - K_σ w = (s - σ) K_s (a S (K_σ w))` when `1 - s a S` is
invertible. -/
theorem stabOp_mulVec_sub_stabOp_mulVec (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    {a : ℂ} (ha : ‖a‖ < 1) {s : ℝ} (hs : IsUnit (1 - ((s : ℂ) * a) • profileC S).det)
    (w : Fin n → ℂ) :
    stabOp s S a *ᵥ w - stabOp σ S a *ᵥ w =
      (s - σ) • (stabOp s S a *ᵥ (a • (profileC S *ᵥ (stabOp σ S a *ᵥ w)))) := by
  set u := stabOp σ S a *ᵥ w with hu
  have hw : w = (1 - ((σ : ℂ) * a) • profileC S) *ᵥ u :=
    (stabOp_mulVec_eq_iff hS hσ ha w u).mp rfl
  have hsplit : (1 - ((σ : ℂ) * a) • profileC S) =
      (1 - ((s : ℂ) * a) • profileC S) + (((s : ℂ) - σ) * a) • profileC S := by
    rw [sub_mul, sub_smul]
    abel
  have hKs : stabOp s S a *ᵥ ((1 - ((s : ℂ) * a) • profileC S) *ᵥ u) = u := by
    rw [mulVec_mulVec, stabOp, nonsing_inv_mul _ hs, one_mulVec]
  have hreal : (((s : ℂ) - σ) * a) • (profileC S *ᵥ u) = (s - σ) • (a • (profileC S *ᵥ u)) := by
    rw [mul_smul, ← Complex.ofReal_sub, Complex.coe_smul]
  calc stabOp s S a *ᵥ w - u
      = stabOp s S a *ᵥ ((1 - ((s : ℂ) * a) • profileC S) *ᵥ u +
          (((s : ℂ) - σ) * a) • (profileC S *ᵥ u)) - u := by
        rw [← smul_mulVec, ← add_mulVec, ← hsplit, ← hw]
    _ = _ := by
        rw [mulVec_add, hKs, hreal, mulVec_smul, add_sub_cancel_left]

/-- Derivative of `s ↦ K_s v(s)` at `σ` for a differentiable vector `v`:
`K_σ v' + K_σ (a S (K_σ v(σ)))`. -/
theorem hasDerivAt_stabOp_mulVec_of_hasDerivAt (hS : ProfileHyp S)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ} (ha : ‖a‖ < 1) {v : ℝ → Fin n → ℂ}
    {v' : Fin n → ℂ} (hv : HasDerivAt v v' σ) :
    HasDerivAt (fun s => stabOp s S a *ᵥ v s)
      (stabOp σ S a *ᵥ v' + stabOp σ S a *ᵥ (a • (profileC S *ᵥ (stabOp σ S a *ᵥ v σ)))) σ := by
  rw [hasDerivAt_iff_tendsto_slope] at hv ⊢
  set w := a • (profileC S *ᵥ (stabOp σ S a *ᵥ v σ)) with hw
  have heq : (fun s => stabOp s S a *ᵥ slope v σ s + stabOp s S a *ᵥ w) =ᶠ[𝓝[≠] σ]
      slope (fun s => stabOp s S a *ᵥ v s) σ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_isUnit_det hS hσ ha)]
      with s hs hdet
    have hsσ : s - σ ≠ 0 := sub_ne_zero.mpr hs
    have hres := stabOp_mulVec_sub_stabOp_mulVec hS hσ ha hdet (v σ)
    have hsplit : stabOp s S a *ᵥ v s - stabOp σ S a *ᵥ v σ =
        stabOp s S a *ᵥ (v s - v σ) + (s - σ) • (stabOp s S a *ᵥ w) := by
      rw [mulVec_sub, hw, ← hres]
      abel
    rw [slope_def_module, slope_def_module, hsplit, smul_add, smul_smul, inv_mul_cancel₀ hsσ,
      one_smul, mulVec_smul]
  refine Tendsto.congr' heq ?_
  have hK : Tendsto (fun s => stabOp s S a) (𝓝[≠] σ) (𝓝 (stabOp σ S a)) :=
    (continuousAt_stabOp hS hσ ha).tendsto.mono_left nhdsWithin_le_nhds
  have hmv : Continuous fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => p.1 *ᵥ p.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  have h1 := (hmv.tendsto (stabOp σ S a, v')).comp (hK.prodMk_nhds hv)
  have h2 := (hmv.tendsto (stabOp σ S a, w)).comp (hK.prodMk_nhds tendsto_const_nhds)
  exact h1.add h2

/-- Vector form: `d/dσ (K_σ v) = K_σ (a S (K_σ v))`. -/
theorem hasDerivAt_stabOp_mulVec_pi (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (v : Fin n → ℂ) :
    HasDerivAt (fun s : ℝ => stabOp s S a *ᵥ v)
      (stabOp σ S a *ᵥ (a • (profileC S *ᵥ (stabOp σ S a *ᵥ v)))) σ := by
  have h := hasDerivAt_stabOp_mulVec_of_hasDerivAt hS hσ ha (hasDerivAt_const σ v)
  rwa [mulVec_zero, zero_add] at h

/-- Coordinate form: `d/dσ (K_σ v)_x = (K_σ (a S (K_σ v)))_x`. -/
theorem hasDerivAt_stabOp_mulVec (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) (v : Fin n → ℂ) (x : Fin n) :
    HasDerivAt (fun s : ℝ => (stabOp s S a *ᵥ v) x)
      ((stabOp σ S a *ᵥ (a • (profileC S *ᵥ (stabOp σ S a *ᵥ v)))) x) σ :=
  hasDerivAt_pi.mp (hasDerivAt_stabOp_mulVec_pi hS hσ ha v) x

/-!
### Chains `chainTilde`
-/

/-- `M̃_{[j,k]} = 1` for `k ≤ j`. -/
theorem chainTilde_of_le {j k : ℕ} (h : k ≤ j) : chainTilde σ S m A j k = fun _ => 1 := by
  rw [chainTilde_eq, ite_eq_right (by omega)]

/-- `M̃_{[j,j]} = 1`. -/
theorem chainTilde_self (j : ℕ) : chainTilde σ S m A j j = fun _ => 1 :=
  chainTilde_of_le le_rfl

/-- The defining recursion of `M̃_{[j,k]}` for `j < k`. -/
theorem chainTilde_of_lt {j k : ℕ} (h : j < k) :
    chainTilde σ S m A j k =
      stabOp σ S (m j * m k) *ᵥ
        (A j * chainTilde σ S m A (j + 1) k +
          ∑ i ∈ Finset.Ioo j k,
            ((σ : ℂ) * m j * m i) •
              (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i k)) := by
  rw [chainTilde_eq, ite_eq_left h]

/-- `(1 - σ m_j m_k S) M̃_{[j,k]} = A_j M̃_{[j+1,k]} + ∑_i σ m_j m_i S[M̃_{[j,i]}] M̃_{[i,k]}`,
under `‖m_j m_k‖ < 1`. -/
theorem one_sub_mulVec_chainTilde' (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    {j k : ℕ} (hjk : ‖m j * m k‖ < 1) (h : j < k) :
    (1 - ((σ : ℂ) * (m j * m k)) • profileC S) *ᵥ chainTilde σ S m A j k =
      A j * chainTilde σ S m A (j + 1) k +
        ∑ i ∈ Finset.Ioo j k,
          ((σ : ℂ) * m j * m i) •
            (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i k) := by
  rw [chainTilde_of_lt h, one_sub_mulVec_stabOp hS hσ hjk]

/-- `(1 - σ m_j m_k S) M̃_{[j,k]} = A_j M̃_{[j+1,k]} + ∑_i σ m_j m_i S[M̃_{[j,i]}] M̃_{[i,k]}`. -/
theorem one_sub_mulVec_chainTilde (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) {j k : ℕ} (h : j < k) :
    (1 - ((σ : ℂ) * (m j * m k)) • profileC S) *ᵥ chainTilde σ S m A j k =
      A j * chainTilde σ S m A (j + 1) k +
        ∑ i ∈ Finset.Ioo j k,
          ((σ : ℂ) * m j * m i) •
            (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i k) :=
  one_sub_mulVec_chainTilde' hS hσ (norm_mul_lt_one_of_lt_one (hm j) (hm k)) h

/-- `M̃_{[j,j+1]} = K_{j,j+1} A_j` (no hypotheses). -/
theorem chainTilde_one_step (j : ℕ) :
    chainTilde σ S m A j (j + 1) = stabOp σ S (m j * m (j + 1)) *ᵥ A j := by
  rw [chainTilde_of_lt (Nat.lt_succ_self j), chainTilde_self,
    Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Ioo] at hi; omega)]
  have h1 : (fun _ : Fin n => (1 : ℂ)) = 1 := rfl
  rw [h1, mul_one, add_zero]

/-- Second form of the recursion: for `j + 2 ≤ k`,
`M̃_{[j,k]} = K_{jk} (M̃_{[j,j+1]} M̃_{[j+1,k]} + ∑_{j+1<i<k} σ m_j m_i S[M̃_{[j,i]}] M̃_{[i,k]})`.
-/
theorem chainTilde_recursion2 (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) {j k : ℕ} (h : j + 2 ≤ k) :
    chainTilde σ S m A j k =
      stabOp σ S (m j * m k) *ᵥ
        (chainTilde σ S m A j (j + 1) * chainTilde σ S m A (j + 1) k +
          ∑ i ∈ Finset.Ioo (j + 1) k,
            ((σ : ℂ) * m j * m i) •
              (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i k)) := by
  rw [chainTilde_of_lt (by omega : j < k)]
  have hIoo : Finset.Ioo j k = insert (j + 1) (Finset.Ioo (j + 1) k) := by
    rw [Finset.Ioo_insert_left (by omega), Finset.Ico_add_one_left_eq_Ioo]
  rw [hIoo, Finset.sum_insert Finset.left_notMem_Ioo, ← add_assoc, chainTilde_one_step]
  have hK := stabOp_mulVec_sub_one hS hσ (norm_mul_lt_one_of_lt_one (hm j) (hm (j + 1))) (A j)
  congr 2
  rw [← smul_mul_assoc, ← add_mul]
  congr 1
  rw [selfEnergy, mul_assoc, ← hK]
  abel

/-- Locality: `M̃_{[j,k]}` depends only on `m_j, …, m_k` and `A_j, …, A_{k-1}`. -/
theorem chainTilde_congr {m m' : ℕ → ℂ} {A A' : ℕ → Fin n → ℂ} {j k : ℕ}
    (hm : ∀ i, j ≤ i → i ≤ k → m i = m' i) (hA : ∀ i, j ≤ i → i < k → A i = A' i) :
    chainTilde σ S m A j k = chainTilde σ S m' A' j k := by
  induction hd : k - j using Nat.strong_induction_on generalizing j k with
  | _ d ih =>
  rcases lt_or_ge j k with h | h
  · have hstep : chainTilde σ S m A (j + 1) k = chainTilde σ S m' A' (j + 1) k :=
      ih (k - (j + 1)) (by omega) (fun i hi1 hi2 => hm i (by omega) hi2)
        (fun i hi1 hi2 => hA i (by omega) hi2) rfl
    rw [chainTilde_of_lt h, chainTilde_of_lt h, hm j le_rfl h.le, hm k h.le le_rfl,
      hA j le_rfl h, hstep]
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Ioo] at hi
    rw [hm i (by omega) (by omega),
      ih (i - j) (by omega) (fun p hp1 hp2 => hm p hp1 (by omega))
        (fun p hp1 hp2 => hA p hp1 (by omega)) rfl,
      ih (k - i) (by omega) (fun p hp1 hp2 => hm p (by omega) hp2)
        (fun p hp1 hp2 => hA p (by omega) hp2) rfl]
  · rw [chainTilde_of_le h, chainTilde_of_le h]

/-- Shift invariance: `M̃_{[j,k]}` of the shifted data equals `M̃_{[j+c,k+c]}`. -/
theorem chainTilde_shift (c j k : ℕ) :
    chainTilde σ S (fun p => m (p + c)) (fun p => A (p + c)) j k =
      chainTilde σ S m A (j + c) (k + c) := by
  induction hd : k - j using Nat.strong_induction_on generalizing j k with
  | _ d ih =>
  rcases lt_or_ge j k with h | h
  · rw [chainTilde_of_lt h, chainTilde_of_lt (by omega : j + c < k + c),
      ih (k - (j + 1)) (by omega) (j + 1) k rfl, show j + 1 + c = j + c + 1 by omega]
    congr 2
    rw [← Finset.map_add_right_Ioo j k c, Finset.sum_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Ioo] at hi
    simp only [addRightEmbedding_apply]
    rw [ih (i - j) (by omega) j i rfl, ih (k - i) (by omega) i k rfl]
  · rw [chainTilde_of_le h, chainTilde_of_le (by omega)]

/-!
### Chains `chainM`
-/

/-- `M_{[j,k]} = (∏_{i=j}^k m_i) M̃_{[j,k]}` (definitional). -/
theorem chainM_eq_smul (j k : ℕ) :
    chainM σ S m A j k = (∏ i ∈ Finset.Icc j k, m i) • chainTilde σ S m A j k := rfl

/-- `M_{[j,j]} = m_j`. -/
theorem chainM_self (j : ℕ) : chainM σ S m A j j = fun _ => m j := by
  rw [chainM_eq_smul, chainTilde_self, Finset.Icc_self, Finset.prod_singleton]
  funext x
  simp

/-- `M_{[j,k]} = 1` for `k < j` (empty product, `M̃ = 1`). -/
theorem chainM_of_gt {j k : ℕ} (h : k < j) : chainM σ S m A j k = fun _ => 1 := by
  rw [chainM_eq_smul, chainTilde_of_le h.le, Finset.Icc_eq_empty (by omega), Finset.prod_empty,
    one_smul]

/-- Locality for `chainM`. -/
theorem chainM_congr {m m' : ℕ → ℂ} {A A' : ℕ → Fin n → ℂ} {j k : ℕ}
    (hm : ∀ i, j ≤ i → i ≤ k → m i = m' i) (hA : ∀ i, j ≤ i → i < k → A i = A' i) :
    chainM σ S m A j k = chainM σ S m' A' j k := by
  rw [chainM_eq_smul, chainM_eq_smul, chainTilde_congr hm hA,
    Finset.prod_congr rfl fun i hi => hm i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2]

/-- Shift invariance for `chainM`. -/
theorem chainM_shift (c j k : ℕ) :
    chainM σ S (fun p => m (p + c)) (fun p => A (p + c)) j k =
      chainM σ S m A (j + c) (k + c) := by
  rw [chainM_eq_smul, chainM_eq_smul, chainTilde_shift, ← Finset.map_add_right_Icc,
    Finset.prod_map]
  rfl

end BlockBand.Native.ErdosRiabov.MTerms
