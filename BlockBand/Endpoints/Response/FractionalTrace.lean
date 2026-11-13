module

public import BlockBand.Internal.Contracts.Endpoints
public import BlockBand.Model.Construction.OrderedEigenvalues
public import BlockBand.Counting.SpectralScaling
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Deterministic fractional-trace (Schatten) toolkit

All statements are about `TransmissionPath.fracTrace p T`
(`Σ_{z ∈ roots charpoly T} (max (re z) 0)^p`) and `Endpoints.smallChannelPower a r A`
(the same sum restricted to roots with `re z ≤ a`), on an arbitrary finite index type.

## Main results

- `smallChannelPower_le_rpow_mul_fracTrace`: the small-channel bound
  `Σ_{λ_i ≤ a} λ_i^r ≤ a^(r-p) Σ_{λ_i ≤ a} λ_i^p ≤ a^(r-p) Tr A^p` for `0 ≤ a`, `0 < r`, `p ≤ r`
  (any matrix; no Hermitian hypothesis is needed).
- eigenvalue forms: `fracTrace_eq_sum_eigenvalues`, `smallChannelPower_eq_sum_eigenvalues`.
- basic facts: `fracTrace_nonneg`, `fracTrace_smul` (`Tr (cA)^p = c^p Tr A^p`, `c ≥ 0`),
  `fracTrace_mul_comm`, `fracTrace_unitary_conj`, `fracTrace_reindex`,
  `eigenvalues_le_trace` (`λ_max ≤ Tr A`), the discarded power sum bound
  `sum_eigenvalues_rpow_le_of_card_le` (`Σ_{i∈S} λ_i^p ≤ m^(1-p) (Σ_{i∈S} λ_i)^p`, `#S ≤ m`),
  `fracTrace_le_card_rpow_mul_trace_rpow` (`H_p ≤ W^(1-p) γ^p`) and
  `fracTrace_le_rank_rpow_mul_trace_rpow`.
- monotonicity: `fracTrace_mono` (`A ≤ B` in Loewner order ⇒ `Tr A^p ≤ Tr B^p`, `p ≥ 0`;
  via Weyl monotonicity of sorted eigenvalues) and the congruence bound
  `fracTrace_conjTranspose_mul_mul_le` (`L Lᴴ ≤ K² I` ⇒ `Tr (Lᴴ A L)^p ≤ K^(2p) Tr A^p`,
  i.e. `H_{p,+} ≤ ‖L‖^{2p} H_p`), and its operator-norm form
  `fracTrace_conjTranspose_mul_mul_le_of_norm_le` (`‖L‖ ≤ K`, Euclidean operator norm
  `Matrix.Norms.L2Operator`), through `posSemidef_sq_smul_one_sub_of_norm_le`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix
open scoped ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Endpoints

/-!
## Scalar inequalities
-/

/-- For `0 ≤ x ≤ a`, `0 < r` and `p ≤ r`: `x^r ≤ a^(r-p) x^p`. -/
theorem rpow_le_rpow_sub_mul_rpow {x a p r : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) (hr : 0 < r)
    (hpr : p ≤ r) : x ^ r ≤ a ^ (r - p) * x ^ p := by
  rcases hx.eq_or_lt with rfl | hx0
  · rw [Real.zero_rpow hr.ne']
    exact mul_nonneg (Real.rpow_nonneg (hx.trans hxa) _) (Real.rpow_nonneg le_rfl _)
  · have hsplit : x ^ r = x ^ (r - p) * x ^ p := by
      rw [← Real.rpow_add hx0]; ring_nf
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxa (sub_nonneg.mpr hpr))
      (Real.rpow_nonneg hx _)

/-- Scalar concavity (discarded power sum): for nonnegative `x` on a finite set `s` and
`0 < p ≤ 1`, `Σ_{i∈s} x_i^p ≤ (#s)^(1-p) (Σ_{i∈s} x_i)^p`. -/
theorem sum_rpow_le_card_rpow_mul_sum_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑ i ∈ s, x i ^ p ≤ (s.card : ℝ) ^ (1 - p) * (∑ i ∈ s, x i) ^ p := by
  have hq : 1 ≤ 1 / p := by rw [le_div_iff₀ hp]; linarith
  have hy : ∀ i ∈ s, 0 ≤ x i ^ p := fun i hi => Real.rpow_nonneg (hx i hi) p
  have key := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := s) (f := fun i => x i ^ p)
    hq hy
  have hpow : ∀ i ∈ s, (x i ^ p) ^ (1 / p) = x i := by
    intro i hi
    rw [← Real.rpow_mul (hx i hi), mul_one_div_cancel hp.ne', Real.rpow_one]
  rw [Finset.sum_congr rfl hpow] at key
  have hS : 0 ≤ ∑ i ∈ s, x i ^ p := Finset.sum_nonneg hy
  have hc : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  -- raise `key` to the power `p`
  have key' := Real.rpow_le_rpow (Real.rpow_nonneg hS _) key hp.le
  rw [← Real.rpow_mul hS, one_div_mul_cancel hp.ne', Real.rpow_one,
    Real.mul_rpow (Real.rpow_nonneg hc _) (Finset.sum_nonneg hx), ← Real.rpow_mul hc] at key'
  have he : (1 / p - 1) * p = 1 - p := by field_simp
  rwa [he] at key'

/-- The discarded power sum with an upper bound `m` on the number of indices. -/
theorem sum_rpow_le_of_card_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {m : ℝ} (hm : (s.card : ℝ) ≤ m) :
    ∑ i ∈ s, x i ^ p ≤ m ^ (1 - p) * (∑ i ∈ s, x i) ^ p :=
  (sum_rpow_le_card_rpow_mul_sum_rpow s x hx hp hp1).trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hm (by linarith))
      (Real.rpow_nonneg (Finset.sum_nonneg hx) _))

/-!
## Multiset-level facts (any square complex matrix)
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Tr T^p ≥ 0` for every matrix `T` and every real `p`. -/
theorem fracTrace_nonneg (p : ℝ) (T : Matrix n n ℂ) : 0 ≤ fracTrace p T :=
  Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Real.rpow_nonneg (le_max_right _ _) p

/-- `Σ_{λ_i ≤ a} λ_i^r ≥ 0`. -/
theorem smallChannelPower_nonneg (a r : ℝ) (T : Matrix n n ℂ) : 0 ≤ smallChannelPower a r T :=
  Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Real.rpow_nonneg (le_max_right _ _) r

/-- The small-channel sum is at most the full fractional trace. -/
theorem smallChannelPower_le_fracTrace (a p : ℝ) (T : Matrix n n ℂ) :
    smallChannelPower a p T ≤ fracTrace p T := by
  classical
  unfold smallChannelPower fracTrace
  conv_rhs => rw [← Multiset.filter_add_not (fun z : ℂ => z.re ≤ a) T.charpoly.roots]
  rw [Multiset.map_add, Multiset.sum_add]
  refine le_add_of_le_of_nonneg (le_of_eq ?_) (Multiset.sum_nonneg fun x hx => ?_)
  · congr 2
  · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Real.rpow_nonneg (le_max_right _ _) p

/-- First inequality of the small-channel bound: for `0 ≤ a`, `0 < r` and `p ≤ r`,
`Σ_{λ_i ≤ a} λ_i^r ≤ a^(r-p) Σ_{λ_i ≤ a} λ_i^p`. -/
theorem smallChannelPower_le_rpow_mul_smallChannelPower {a p r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (hpr : p ≤ r) (T : Matrix n n ℂ) :
    smallChannelPower a r T ≤ a ^ (r - p) * smallChannelPower a p T := by
  unfold smallChannelPower
  rw [← Multiset.sum_map_mul_left]
  refine Multiset.sum_map_le_sum_map _ _ fun z hz => ?_
  have hza : z.re ≤ a := (Multiset.mem_filter.mp hz).2
  exact rpow_le_rpow_sub_mul_rpow (le_max_right _ _) (max_le hza ha) hr hpr

/-- The small-channel bound, pointwise: for every square complex matrix `A`, `0 ≤ a`, `0 < r` and
`p ≤ r`, `Σ_{λ_i(A) ≤ a} λ_i(A)^r ≤ a^(r-p) Tr A^p`. -/
theorem smallChannelPower_le_rpow_mul_fracTrace {a p r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (hpr : p ≤ r) (A : Matrix n n ℂ) :
    smallChannelPower a r A ≤ a ^ (r - p) * fracTrace p A :=
  (smallChannelPower_le_rpow_mul_smallChannelPower ha hr hpr A).trans
    (mul_le_mul_of_nonneg_left (smallChannelPower_le_fracTrace a p A)
      (Real.rpow_nonneg ha _))

/-- `Tr (XY)^p = Tr (YX)^p` (equal characteristic polynomials). -/
theorem fracTrace_mul_comm (p : ℝ) (X Y : Matrix n n ℂ) :
    fracTrace p (X * Y) = fracTrace p (Y * X) := by
  unfold fracTrace; rw [charpoly_mul_comm]

/-- Unitary conjugation invariance: `Tr (U A U*)^p = Tr A^p`. -/
theorem fracTrace_unitary_conj (p : ℝ) (A : Matrix n n ℂ) {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : fracTrace p (U * A * star U) = fracTrace p A := by
  rw [Matrix.mul_assoc, fracTrace_mul_comm, Matrix.mul_assoc,
    (Matrix.mem_unitaryGroup_iff'.mp hU), Matrix.mul_one]

/-- Reindexing invariance: `Tr (reindex e e A)^p = Tr A^p`. -/
theorem fracTrace_reindex {m : Type*} [Fintype m] [DecidableEq m] (p : ℝ) (e : n ≃ m)
    (A : Matrix n n ℂ) : fracTrace p (reindex e e A) = fracTrace p A := by
  unfold fracTrace; rw [charpoly_reindex]

/-!
## Eigenvalue forms (Hermitian matrices)
-/

/-- For Hermitian `A`, `Tr A^p = Σ_i (max λ_i 0)^p` (Mathlib's eigenvalue enumeration). -/
theorem fracTrace_eq_sum_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) (p : ℝ) :
    fracTrace p A = ∑ i, (max (hA.eigenvalues i) 0) ^ p := by
  unfold fracTrace
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  rfl

/-- For Hermitian `A`, `Tr A^p = Σ_k (max λ_k^↓ 0)^p` over the decreasingly sorted
eigenvalues `eigenvalues₀`. -/
theorem fracTrace_eq_sum_eigenvalues₀ {A : Matrix n n ℂ} (hA : A.IsHermitian) (p : ℝ) :
    fracTrace p A = ∑ k, (max (hA.eigenvalues₀ k) 0) ^ p := by
  unfold fracTrace
  rw [hA.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
  rfl

/-- For positive-semidefinite `A`, `Tr A^p = Σ_i λ_i^p`. -/
theorem fracTrace_eq_sum_eigenvalues_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (p : ℝ) : fracTrace p A = ∑ i, hA.isHermitian.eigenvalues i ^ p := by
  rw [fracTrace_eq_sum_eigenvalues hA.isHermitian]
  exact Finset.sum_congr rfl fun i _ => by rw [max_eq_left (hA.eigenvalues_nonneg i)]

/-- For Hermitian `A`, `Σ_{λ_i ≤ a} λ_i^r = Σ_{i : λ_i ≤ a} (max λ_i 0)^r`. -/
theorem smallChannelPower_eq_sum_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) (a r : ℝ) :
    smallChannelPower a r A =
      ∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≤ a), (max (hA.eigenvalues i) 0) ^ r := by
  classical
  unfold smallChannelPower
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.map_map, Finset.sum,
    Finset.filter_val]
  congr 1

/-- Homogeneity: for Hermitian `A` and `c ≥ 0`, `Tr (cA)^p = c^p Tr A^p` (every real `p`). -/
theorem fracTrace_smul {A : Matrix n n ℂ} (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (p : ℝ) :
    fracTrace p ((c : ℂ) • A) = c ^ p * fracTrace p A := by
  unfold fracTrace
  rw [BlockBand.Counting.roots_positiveScale hA c, hA.roots_charpoly_eq_eigenvalues,
    Multiset.map_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Complex.ofReal_re]
  rw [← Real.mul_rpow hc (le_max_right _ _), mul_max_of_nonneg _ _ hc, mul_zero]
  simp

/-!
## Trace bounds (positive-semidefinite matrices)
-/

/-- For Hermitian `A`, `(Tr A).re = Σ_i λ_i`. -/
theorem trace_re_eq_sum_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.trace.re = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp

/-- For PSD `A`, every eigenvalue is at most the trace: `λ_max(A) ≤ Tr A`. -/
theorem eigenvalues_le_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) :
    hA.isHermitian.eigenvalues i ≤ A.trace.re := by
  rw [trace_re_eq_sum_eigenvalues hA.isHermitian]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- For PSD `A` and any set `S` of eigen-indices, `Σ_{i∈S} λ_i ≤ Tr A`. -/
theorem sum_eigenvalues_le_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) (S : Finset n) :
    ∑ i ∈ S, hA.isHermitian.eigenvalues i ≤ A.trace.re := by
  rw [trace_re_eq_sum_eigenvalues hA.isHermitian]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun j _ _ => hA.eigenvalues_nonneg j

/-- Discarded power sum: for PSD `A`, `0 < p ≤ 1` and a set `S` of at most `m` eigen-indices,
`Σ_{i∈S} λ_i^p ≤ m^(1-p) (Σ_{i∈S} λ_i)^p ≤ m^(1-p) (Tr A)^p`. -/
theorem sum_eigenvalues_rpow_le_of_card_le {A : Matrix n n ℂ} (hA : A.PosSemidef) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (S : Finset n) {m : ℝ} (hm : (S.card : ℝ) ≤ m) :
    ∑ i ∈ S, hA.isHermitian.eigenvalues i ^ p ≤
        m ^ (1 - p) * (∑ i ∈ S, hA.isHermitian.eigenvalues i) ^ p ∧
      m ^ (1 - p) * (∑ i ∈ S, hA.isHermitian.eigenvalues i) ^ p ≤
        m ^ (1 - p) * A.trace.re ^ p := by
  have hx : ∀ i ∈ S, 0 ≤ hA.isHermitian.eigenvalues i := fun i _ => hA.eigenvalues_nonneg i
  refine ⟨sum_rpow_le_of_card_le S _ hx hp hp1 hm, ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Finset.sum_nonneg hx) (sum_eigenvalues_le_trace hA S) hp.le)
    (Real.rpow_nonneg ((Nat.cast_nonneg _).trans hm) _)

/-- Scalar concavity bound `H_p ≤ W^(1-p) γ^p`: for PSD `A` on an index type of cardinality `W`
and `0 < p ≤ 1`, `Tr A^p ≤ W^(1-p) (Tr A)^p`. -/
theorem fracTrace_le_card_rpow_mul_trace_rpow {A : Matrix n n ℂ} (hA : A.PosSemidef) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    fracTrace p A ≤ (Fintype.card n : ℝ) ^ (1 - p) * A.trace.re ^ p := by
  rw [fracTrace_eq_sum_eigenvalues_of_posSemidef hA, trace_re_eq_sum_eigenvalues hA.isHermitian]
  exact sum_rpow_le_card_rpow_mul_sum_rpow Finset.univ _ (fun i _ => hA.eigenvalues_nonneg i)
    hp hp1

/-- Rank form of scalar concavity: for PSD `A` and `0 < p ≤ 1`,
`Tr A^p ≤ (rank A)^(1-p) (Tr A)^p`. -/
theorem fracTrace_le_rank_rpow_mul_trace_rpow {A : Matrix n n ℂ} (hA : A.PosSemidef) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    fracTrace p A ≤ (A.rank : ℝ) ^ (1 - p) * A.trace.re ^ p := by
  classical
  set ev := hA.isHermitian.eigenvalues
  set S := Finset.univ.filter fun i => ev i ≠ 0
  have hx : ∀ i ∈ S, 0 ≤ ev i := fun i _ => hA.eigenvalues_nonneg i
  have hpow : ∑ i ∈ S, ev i ^ p = ∑ i, ev i ^ p :=
    Finset.sum_filter_of_ne fun i _ h hi => h (by rw [hi, Real.zero_rpow hp.ne'])
  have hsum : ∑ i ∈ S, ev i = ∑ i, ev i :=
    Finset.sum_filter_of_ne fun i _ h => h
  have hrank : (A.rank : ℝ) = (S.card : ℝ) := by
    rw [hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  rw [fracTrace_eq_sum_eigenvalues_of_posSemidef hA, trace_re_eq_sum_eigenvalues hA.isHermitian,
    hrank, ← hpow, ← hsum]
  exact sum_rpow_le_card_rpow_mul_sum_rpow S ev hx hp hp1

/-!
## Loewner monotonicity and the congruence bound
-/

/-- Weyl monotonicity: `A ≤ B` (Loewner) ⇒ `λ_k^↓(A) ≤ λ_k^↓(B)` for every sorted index. -/
theorem eigenvalues₀_le_of_posSemidef_sub {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  simp only [Matrix.IsHermitian.eigenvalues₀]
  refine LinearMap.IsSymmetric.eigenvalue_mono _ _ _ (fun x => ?_) k
  have h := (Matrix.isPositive_toEuclideanLin_iff.mpr hAB).re_inner_nonneg_left x
  rw [map_sub, LinearMap.sub_apply, inner_sub_left, map_sub] at h
  linarith

/-- Trace monotonicity: for Hermitian `A ≤ B` (Loewner order, `B - A` PSD) and `p ≥ 0`,
`Tr A^p ≤ Tr B^p`. (For `0 < p ≤ 1` this is the trace form of operator monotonicity of
`x ↦ x^p`; the trace inequality holds for every `p ≥ 0` by Weyl monotonicity.) -/
theorem fracTrace_mono {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) {p : ℝ} (hp : 0 ≤ p) : fracTrace p A ≤ fracTrace p B := by
  rw [fracTrace_eq_sum_eigenvalues₀ hA, fracTrace_eq_sum_eigenvalues₀ hB]
  exact Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (le_max_right _ _)
    (max_le_max_right 0 (eigenvalues₀_le_of_posSemidef_sub hA hB hAB k)) hp

open scoped MatrixOrder in
/-- Congruence bound `H_{p,+} ≤ ‖L‖^{2p} H_p`: for PSD `A`, `p ≥ 0`, `K ≥ 0` and any `L` with
`L Lᴴ ≤ K² I` (equivalently `‖L‖_{op} ≤ K`), `Tr (Lᴴ A L)^p ≤ K^(2p) Tr A^p`. -/
theorem fracTrace_conjTranspose_mul_mul_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (L : Matrix n n ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hL : ((((K ^ 2 : ℝ)) : ℂ) • (1 : Matrix n n ℂ) - L * Lᴴ).PosSemidef) {p : ℝ}
    (hp : 0 ≤ p) : fracTrace p (Lᴴ * A * L) ≤ K ^ (2 * p) * fracTrace p A := by
  obtain ⟨X, hX, -, hXX⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hA.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
  have hXh : Xᴴ = X := hX.star_eq
  -- `Lᴴ A L = (X L)ᴴ (X L)` and `Tr ((X L)ᴴ (X L))^p = Tr (X (L Lᴴ) X)^p`
  have h1 : fracTrace p (Lᴴ * A * L) = fracTrace p (X * (L * Lᴴ) * X) := by
    rw [← hXX, show Lᴴ * (X * X) * L = (Lᴴ * X) * (X * L) by simp only [Matrix.mul_assoc],
      fracTrace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : fracTrace p (X * ((((K ^ 2 : ℝ)) : ℂ) • (1 : Matrix n n ℂ)) * X) =
      K ^ (2 * p) * fracTrace p A := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hXX,
      fracTrace_smul hA.isHermitian (sq_nonneg K), ← Real.rpow_natCast, ← Real.rpow_mul hK]
    norm_num
  have hP : (X * (L * Lᴴ) * X).PosSemidef := by
    simpa only [hXh] using (posSemidef_self_mul_conjTranspose L).mul_mul_conjTranspose_same X
  have hQ : (X * ((((K ^ 2 : ℝ)) : ℂ) • (1 : Matrix n n ℂ)) * X).PosSemidef := by
    have := (hL.add (posSemidef_self_mul_conjTranspose L)).mul_mul_conjTranspose_same X
    simpa only [hXh, sub_add_cancel] using this
  have hsub : (X * ((((K ^ 2 : ℝ)) : ℂ) • (1 : Matrix n n ℂ)) * X - X * (L * Lᴴ) * X).PosSemidef := by
    have := hL.mul_mul_conjTranspose_same X
    simpa only [hXh, Matrix.mul_sub, Matrix.sub_mul] using this
  rw [h1, ← h2]
  exact fracTrace_mono hP.isHermitian hQ.isHermitian hsub hp

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- `‖L‖ ≤ K` (Euclidean operator norm) gives `L Lᴴ ≤ K² I` in Loewner order. -/
theorem posSemidef_sq_smul_one_sub_of_norm_le (L : Matrix n n ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hL : ‖L‖ ≤ K) : ((((K ^ 2 : ℝ)) : ℂ) • (1 : Matrix n n ℂ) - L * Lᴴ).PosSemidef := by
  have hsa : IsSelfAdjoint (L * Lᴴ) := (posSemidef_self_mul_conjTranspose L).isHermitian
  have h1 := IsSelfAdjoint.le_algebraMap_norm_self (L * Lᴴ) hsa
  have hn : ‖L * Lᴴ‖ = ‖L‖ * ‖L‖ := by
    have := l2_opNorm_conjTranspose_mul_self Lᴴ
    rwa [conjTranspose_conjTranspose, l2_opNorm_conjTranspose] at this
  have h2 : algebraMap ℝ (Matrix n n ℂ) ‖L * Lᴴ‖ ≤ algebraMap ℝ (Matrix n n ℂ) (K ^ 2) := by
    rw [hn]
    rcases isEmpty_or_nonempty n with hn0 | hn0
    · exact le_of_eq (Subsingleton.elim _ _)
    · exact algebraMap_le_algebraMap.mpr (by nlinarith [norm_nonneg L])
  have h3 := h1.trans h2
  rw [Matrix.le_iff] at h3
  convert h3 using 2
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply]

open scoped Matrix.Norms.L2Operator in
/-- Congruence bound, operator-norm form `H_{p,+} ≤ ‖L‖^{2p} H_p`: for PSD `A`, `p ≥ 0` and
`‖L‖ ≤ K` (Euclidean operator norm), `Tr (Lᴴ A L)^p ≤ K^(2p) Tr A^p`. -/
theorem fracTrace_conjTranspose_mul_mul_le_of_norm_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (L : Matrix n n ℂ) {K : ℝ} (hK : 0 ≤ K) (hL : ‖L‖ ≤ K) {p : ℝ} (hp : 0 ≤ p) :
    fracTrace p (Lᴴ * A * L) ≤ K ^ (2 * p) * fracTrace p A :=
  fracTrace_conjTranspose_mul_mul_le hA L hK (posSemidef_sq_smul_one_sub_of_norm_le L hK hL) hp

end BlockBand.Endpoints
