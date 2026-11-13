module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Round

/-!
# `GUENormTail`, deterministic part: a `1/4`-net of the complex unit ball

* `opNorm_le_of_net`: if `S` is a finite set of vectors of norm `≤ 2` such that every `x` with
  `‖x‖ ≤ 1` is within `1/4` of `S`, and `Re⟪s', T s⟫ ≤ M` for all `s, s' ∈ S`, then
  `‖T‖ ≤ 4M` (for any continuous linear `T` on a complex inner product space).
* `exists_net`: for `0 < |ι|`, `EuclideanSpace ℂ ι` has such a net with `|S| ≤ 2^{14|ι|}`
  (coordinate grid of mesh `δ = 1/(4√|ι|)`; the count uses the exponential Markov weight
  `2^{10|ι| - Σ_j |k_j|}` on the grid indices, so no volume argument is needed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GUENormTail

open scoped InnerProductSpace ComplexConjugate

section Deterministic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Operator norm from a net**: `‖T‖ ≤ 4 max_{s,s' ∈ S} Re⟪s', T s⟫`. -/
theorem opNorm_le_of_net (T : E →L[ℂ] E) (S : Finset E) (hS2 : ∀ s ∈ S, ‖s‖ ≤ 2)
    (hcov : ∀ x : E, ‖x‖ ≤ 1 → ∃ s ∈ S, ‖x - s‖ ≤ 1 / 4) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s ∈ S, ∀ s' ∈ S, (⟪s', T s⟫_ℂ).re ≤ M) : ‖T‖ ≤ 4 * M := by
  have key : ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → (⟪y, T x⟫_ℂ).re ≤ M + 3 / 4 * ‖T‖ := by
    intro x y hx hy
    obtain ⟨s, hs, hxs⟩ := hcov x hx
    obtain ⟨s', hs', hys⟩ := hcov y hy
    have hid : ⟪y, T x⟫_ℂ = ⟪s', T s⟫_ℂ + ⟪y - s', T x⟫_ℂ + ⟪s', T (x - s)⟫_ℂ := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : (⟪y - s', T x⟫_ℂ).re ≤ 1 / 4 * ‖T‖ := by
      have := re_inner_le_norm (𝕜 := ℂ) (y - s') (T x)
      have hTx : ‖T x‖ ≤ ‖T‖ := (T.le_opNorm x).trans (by nlinarith [norm_nonneg T])
      simp only [RCLike.re_to_complex] at this
      nlinarith [norm_nonneg (y - s'), norm_nonneg (T x)]
    have h2 : (⟪s', T (x - s)⟫_ℂ).re ≤ 2 / 4 * ‖T‖ := by
      have := re_inner_le_norm (𝕜 := ℂ) s' (T (x - s))
      have hT : ‖T (x - s)‖ ≤ ‖T‖ * (1 / 4) :=
        (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxs (norm_nonneg T))
      simp only [RCLike.re_to_complex] at this
      nlinarith [norm_nonneg s', norm_nonneg (T (x - s)), hS2 s' hs', norm_nonneg T]
    rw [hid, Complex.add_re, Complex.add_re]
    linarith [hM s hs s' hs']
  have unit : ∀ x : E, ‖x‖ = 1 → ‖T x‖ ≤ M + 3 / 4 * ‖T‖ := by
    intro x hx
    by_cases h0 : T x = 0
    · rw [h0, norm_zero]
      positivity
    have hn : 0 < ‖T x‖ := norm_pos_iff.2 h0
    set y : E := ((‖T x‖⁻¹ : ℝ) : ℂ) • T x
    have hy : ‖y‖ = 1 := by
      simp only [y, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hre : (⟪y, T x⟫_ℂ).re = ‖T x‖ := by
      simp only [y, inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
      have := inner_self_eq_norm_sq (𝕜 := ℂ) (T x)
      simp only [RCLike.re_to_complex] at this
      rw [this]
      field_simp
    rw [← hre]
    exact key x y hx.le hy.le
  have hT : ‖T‖ ≤ M + 3 / 4 * ‖T‖ := T.opNorm_le_of_unit_norm (by positivity) unit
  linarith

end Deterministic

section Net

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An integer encoded as a sign and a magnitude. -/
def toIntBN (p : Bool × ℕ) : ℤ := if p.1 then -(p.2 : ℤ) else p.2

/-- The sign–magnitude code of an integer. -/
def ofIntBN (z : ℤ) : Bool × ℕ := (decide (z < 0), z.natAbs)

theorem toIntBN_ofIntBN (z : ℤ) : toIntBN (ofIntBN z) = z := by
  unfold toIntBN ofIntBN
  by_cases h : z < 0
  · simp only [h, decide_true, ↓reduceIte, Int.natCast_natAbs, abs_of_neg h, neg_neg]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Int.natCast_natAbs,
      abs_of_nonneg (not_lt.1 h)]

/-- The grid vector `δ (k_{a,0} + i k_{a,1})_a`. -/
def gridVec (δ : ℝ) (k : ι × Fin 2 → Bool × ℕ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun a =>
    ((δ * (toIntBN (k (a, 0)) : ℝ) : ℝ) : ℂ) + ((δ * (toIntBN (k (a, 1)) : ℝ) : ℝ) : ℂ) * Complex.I

/-- Grid indices with `Σ_j |k_j| ≤ 10 n`. -/
def gridIdx (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) : Finset (ι × Fin 2 → Bool × ℕ) :=
  (Fintype.piFinset fun _ => (Finset.univ : Finset Bool) ×ˢ Finset.range (10 * n + 1)).filter
    fun k => ∑ j, (k j).2 ≤ 10 * n

theorem card_gridIdx_le (n : ℕ) :
    ((gridIdx ι n).card : ℝ) ≤ 2 ^ (10 * n) * 4 ^ (2 * Fintype.card ι) := by
  set f : (ι × Fin 2 → Bool × ℕ) → ℝ := fun k => ∏ j, (1 / 2 : ℝ) ^ (k j).2
  have hf0 : ∀ k, 0 ≤ f k := fun k => Finset.prod_nonneg fun j _ => by positivity
  have hone : ∀ k ∈ gridIdx ι n, (1 : ℝ) ≤ 2 ^ (10 * n) * f k := by
    intro k hk
    have hk' : ∑ j, (k j).2 ≤ 10 * n := (Finset.mem_filter.1 hk).2
    simp only [f, Finset.prod_pow_eq_pow_sum]
    calc (1 : ℝ) = 2 ^ (10 * n) * (1 / 2) ^ (10 * n) := by
          rw [← mul_pow]; norm_num
      _ ≤ 2 ^ (10 * n) * (1 / 2) ^ (∑ j, (k j).2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk')
            (by positivity)
  have hsum : ∑ k ∈ Fintype.piFinset fun _ : ι × Fin 2 =>
      (Finset.univ : Finset Bool) ×ˢ Finset.range (10 * n + 1), f k = ∏ _j : ι × Fin 2,
      ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.range (10 * n + 1), (1 / 2 : ℝ) ^ p.2 :=
    (Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool) ×ˢ Finset.range (10 * n + 1))
      (fun _ p => (1 / 2 : ℝ) ^ p.2)).symm
  have hcoord : ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.range (10 * n + 1),
      (1 / 2 : ℝ) ^ p.2 ≤ 4 := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    have := sum_geometric_two_le (10 * n + 1)
    push_cast
    linarith
  calc ((gridIdx ι n).card : ℝ) = ∑ _k ∈ gridIdx ι n, (1 : ℝ) := by simp
    _ ≤ ∑ k ∈ gridIdx ι n, 2 ^ (10 * n) * f k := Finset.sum_le_sum hone
    _ ≤ ∑ k ∈ Fintype.piFinset fun _ : ι × Fin 2 =>
          (Finset.univ : Finset Bool) ×ˢ Finset.range (10 * n + 1), 2 ^ (10 * n) * f k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => mul_nonneg (by positivity) (hf0 k)
    _ = 2 ^ (10 * n) * ∏ _j : ι × Fin 2,
        ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.range (10 * n + 1), (1 / 2 : ℝ) ^ p.2 := by
        rw [← Finset.mul_sum, hsum]
    _ ≤ 2 ^ (10 * n) * ∏ _j : ι × Fin 2, (4 : ℝ) := by
        gcongr with j
        · exact fun j _ => Finset.sum_nonneg fun p _ => by positivity
    _ = 2 ^ (10 * n) * 4 ^ (2 * Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, mul_comm 2]

/-- The real coordinates `(Re x_a, Im x_a)` of `x`. -/
def realCoord (x : EuclideanSpace ℂ ι) (j : ι × Fin 2) : ℝ :=
  if j.2 = 0 then (x j.1).re else (x j.1).im

/-- The rounded grid index of `x`. -/
def roundIdx (δ : ℝ) (x : EuclideanSpace ℂ ι) (j : ι × Fin 2) : Bool × ℕ :=
  ofIntBN (round (realCoord x j / δ))

omit [DecidableEq ι] in
theorem sum_realCoord_sq (x : EuclideanSpace ℂ ι) :
    ∑ j, realCoord x j ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
  simp only [realCoord, Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
  ring

omit [DecidableEq ι] in
theorem norm_sub_gridVec_sq (δ : ℝ) (x : EuclideanSpace ℂ ι) (k : ι × Fin 2 → Bool × ℕ) :
    ‖x - gridVec δ k‖ ^ 2 = ∑ j, (realCoord x j - δ * toIntBN (k j)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
  simp only [realCoord, gridVec, Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, PiLp.sub_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **A `1/4`-net of the unit ball of `ℂ^ι`** of size `≤ 2^{14|ι|}`, made of vectors of
norm `≤ 2`. -/
theorem exists_net (hn : 0 < Fintype.card ι) :
    ∃ S : Finset (EuclideanSpace ℂ ι), (S.card : ℝ) ≤ 2 ^ (14 * Fintype.card ι) ∧
      (∀ s ∈ S, ‖s‖ ≤ 2) ∧ ∀ x : EuclideanSpace ℂ ι, ‖x‖ ≤ 1 → ∃ s ∈ S, ‖x - s‖ ≤ 1 / 4 := by
  classical
  set n := Fintype.card ι
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := 1 / (4 * Real.sqrt n)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hnR.le
  have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hδ : 0 < δ := by positivity
  have hδ2 : δ ^ 2 * (16 * n) = 1 := by
    simp only [δ, div_pow, mul_pow, hsq]
    field_simp
    norm_num
  refine ⟨((gridIdx ι n).image (gridVec δ)).filter fun s => ‖s‖ ≤ 2, ?_, ?_, ?_⟩
  · calc (((gridIdx ι n).image (gridVec δ)).filter fun s => ‖s‖ ≤ 2).card
        ≤ (((gridIdx ι n).image (gridVec δ)).card : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
      _ ≤ (gridIdx ι n).card := by exact_mod_cast Finset.card_image_le
      _ ≤ 2 ^ (10 * n) * 4 ^ (2 * n) := card_gridIdx_le n
      _ = 2 ^ (14 * n) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          ring_nf
  · intro s hs
    exact (Finset.mem_filter.1 hs).2
  · intro x hx
    set k := roundIdx δ x
    have hkj : ∀ j, (toIntBN (k j) : ℝ) = round (realCoord x j / δ) := fun j => by
      simp only [k, roundIdx, toIntBN_ofIntBN]
    have herr : ∀ j, (realCoord x j - δ * toIntBN (k j)) ^ 2 ≤ δ ^ 2 / 4 := by
      intro j
      rw [hkj]
      have h := abs_sub_round (realCoord x j / δ)
      have e : realCoord x j - δ * round (realCoord x j / δ) =
          δ * (realCoord x j / δ - round (realCoord x j / δ)) := by
        rw [mul_sub, mul_div_cancel₀ _ hδ.ne']
      rw [e, mul_pow]
      have : (realCoord x j / δ - round (realCoord x j / δ)) ^ 2 ≤ (1 / 2) ^ 2 :=
        sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
      nlinarith [sq_nonneg δ]
    have hdist : ‖x - gridVec δ k‖ ≤ 1 / 4 := by
      have h2 : ‖x - gridVec δ k‖ ^ 2 ≤ (1 / 4) ^ 2 := by
        rw [norm_sub_gridVec_sq]
        calc ∑ j, (realCoord x j - δ * toIntBN (k j)) ^ 2 ≤ ∑ _j : ι × Fin 2, δ ^ 2 / 4 :=
              Finset.sum_le_sum fun j _ => herr j
          _ = 2 * n * (δ ^ 2 / 4) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
                nsmul_eq_mul]
              push_cast
              ring
          _ ≤ (1 / 4) ^ 2 := by nlinarith
      nlinarith [norm_nonneg (x - gridVec δ k)]
    have hmem : k ∈ gridIdx ι n := by
      have hmag : ∀ j, ((k j).2 : ℝ) ≤ 1 + realCoord x j ^ 2 * (8 * n) := by
        intro j
        have h1 : ((k j).2 : ℝ) = |(round (realCoord x j / δ) : ℝ)| := by
          simp only [k, roundIdx, ofIntBN]
          rw [Nat.cast_natAbs]
          push_cast
          rfl
        rw [h1]
        have h := abs_sub_round (realCoord x j / δ)
        have h3 : |(round (realCoord x j / δ) : ℝ)| ≤ |realCoord x j / δ| + 1 / 2 := by
          have := abs_sub_abs_le_abs_sub (round (realCoord x j / δ) : ℝ) (realCoord x j / δ)
          rw [abs_sub_comm] at this
          linarith
        have h4 : |realCoord x j / δ| ≤ 1 / 2 + realCoord x j ^ 2 * (8 * n) := by
          have e : (realCoord x j / δ) ^ 2 = realCoord x j ^ 2 * (16 * n) := by
            field_simp
            nlinarith [hδ2]
          nlinarith [sq_abs (realCoord x j / δ), abs_nonneg (realCoord x j / δ),
            sq_nonneg (|realCoord x j / δ| - 1)]
        linarith
      have hS : ((∑ j, (k j).2 : ℕ) : ℝ) ≤ 10 * n := by
        push_cast
        calc ∑ j, ((k j).2 : ℝ) ≤ ∑ j, (1 + realCoord x j ^ 2 * (8 * n)) :=
              Finset.sum_le_sum fun j _ => hmag j
          _ = 2 * n + ‖x‖ ^ 2 * (8 * n) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_realCoord_sq, Finset.sum_const,
                Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
          _ ≤ 10 * n := by
              have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
              nlinarith [mul_le_mul_of_nonneg_right hx2 (by positivity : (0 : ℝ) ≤ 8 * n)]
      have hS' : ∑ j, (k j).2 ≤ 10 * n := by exact_mod_cast hS
      refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j => ?_, hS'⟩
      refine Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_range.2 ?_⟩
      have := Finset.single_le_sum (f := fun j => (k j).2) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j)
      omega
    refine ⟨gridVec δ k, Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hmem, ?_⟩, hdist⟩
    calc ‖gridVec δ k‖ = ‖x - (x - gridVec δ k)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - gridVec δ k‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith

end Net

end BlockBand.DeterminantScore.GUENormTail
