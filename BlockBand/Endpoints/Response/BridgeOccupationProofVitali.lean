module

public import BlockBand.Endpoints.Response.BridgeOccupationDefs
public import Mathlib.Data.Rat.Denumerable

/-!
# A strictly positive function with zero Lebesgue integral (Vitali construction)

For a function `f : α → ℝ≥0∞` that is **not** measurable, Mathlib's `∫⁻ f` is the supremum of the
integrals of measurable minorants. This file constructs `bopPhi : ℝ × ℝ → ℝ`, strictly positive
everywhere, with `∫⁻ ofReal (bopPhi z) dz = 0` (`bop_lintegral_phi`), hence with zero integral
over every set.

**Construction.** `bopRep x ∈ [0,1)` is a chosen representative of the class of `x` in `ℝ/ℚ`
(a Vitali selector), and `x = bopRep x + bopIdx x` with `bopIdx x ∈ ℚ`. Put
`bopPhi z = 1 / (e (bopIdx z.1) + 1)` with `e = Denumerable.eqv ℚ : ℚ ≃ ℕ`. Its superlevel sets `{bopPhi ≥ 1/(n+1)}` lie in
`{z | bopIdx z.1 ∈ F}` for finite `F ⊆ ℚ`. Every measurable subset of such a set is null
(`bop_null_of_idx_mem`, `bop_null_of_idx_mem_prod`): for a measurable `E ⊆ ℝ` with indices in
`F`, the translates `E + kη`, `k = 0, …, K`, by a rational step `η` smaller than every nonzero
difference in `F` divided by `K + 1`, are pairwise disjoint (two points of distinct translates
would be rationally equivalent, so their difference would be a nonzero difference of indices) and
lie in a fixed bounded interval; so `(K+1) vol E` is bounded for all `K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal

/-- Rational equivalence on `ℝ`. -/
def bopRatSetoid : Setoid ℝ where
  r x y := ∃ q : ℚ, x - y = q
  iseqv := ⟨fun x => ⟨0, by simp⟩, fun {x y} h => by
    obtain ⟨q, hq⟩ := h
    exact ⟨-q, by push_cast; linarith⟩, fun {x y z} h h' => by
    obtain ⟨q, hq⟩ := h
    obtain ⟨q', hq'⟩ := h'
    exact ⟨q + q', by push_cast; linarith⟩⟩

/-- A Vitali selector: a representative in `[0, 1)` of the class of `x` in `ℝ / ℚ`. -/
def bopRep (x : ℝ) : ℝ := Int.fract (Quotient.out (Quotient.mk bopRatSetoid x))

theorem bop_rep_mem (x : ℝ) : bopRep x ∈ Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem bop_sub_rep_rat (x : ℝ) : ∃ q : ℚ, x - bopRep x = q := by
  have h : bopRatSetoid (Quotient.out (Quotient.mk bopRatSetoid x)) x := Quotient.mk_out x
  obtain ⟨q, hq⟩ := h
  refine ⟨-q + ⌊Quotient.out (Quotient.mk bopRatSetoid x)⌋, ?_⟩
  unfold bopRep
  rw [Int.fract]
  push_cast
  linarith

theorem bop_rep_eq {x y : ℝ} (h : ∃ q : ℚ, x - y = q) : bopRep x = bopRep y := by
  unfold bopRep
  rw [Quotient.sound (show bopRatSetoid x y from h)]

/-- The rational index `x - bopRep x`. -/
def bopIdx (x : ℝ) : ℚ := Classical.choose (bop_sub_rep_rat x)

theorem bop_eq_rep_add_idx (x : ℝ) : x = bopRep x + bopIdx x := by
  have := Classical.choose_spec (bop_sub_rep_rat x)
  rw [bopIdx]
  linarith

/-- A positive rational lower bound for the nonzero differences in a finite set of rationals. -/
theorem bop_exists_gap (F : Finset ℚ) :
    ∃ m : ℚ, 0 < m ∧ ∀ q ∈ F, ∀ q' ∈ F, q ≠ q' → m ≤ |q - q'| := by
  set S : ℚ := ∑ q ∈ F, ∑ q' ∈ F, |q - q'|⁻¹ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hS1 : (0 : ℚ) < 1 + S := by linarith
  refine ⟨1 / (1 + S), one_div_pos.2 hS1, fun q hq q' hq' hne => ?_⟩
  have hd : 0 < |q - q'| := abs_pos.2 (sub_ne_zero.2 hne)
  have h1 : |q - q'|⁻¹ ≤ S := by
    have ha : |q - q'|⁻¹ ≤ ∑ b ∈ F, |q - b|⁻¹ :=
      Finset.single_le_sum (f := fun b => |q - b|⁻¹) (fun _ _ => by positivity) hq'
    have hb : ∑ b ∈ F, |q - b|⁻¹ ≤ S :=
      Finset.single_le_sum (f := fun a => ∑ b ∈ F, |a - b|⁻¹)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hq
    exact ha.trans hb
  rw [div_le_iff₀ hS1]
  calc (1 : ℚ) = |q - q'| * |q - q'|⁻¹ := (mul_inv_cancel₀ hd.ne').symm
    _ ≤ |q - q'| * S := mul_le_mul_of_nonneg_left h1 hd.le
    _ ≤ |q - q'| * (1 + S) := mul_le_mul_of_nonneg_left (by linarith) hd.le

/-- **Every measurable set of reals whose indices lie in a finite set is null.** -/
theorem bop_null_of_idx_mem {E : Set ℝ} (hE : MeasurableSet E) (F : Finset ℚ)
    (hsub : ∀ x ∈ E, bopIdx x ∈ F) : volume E = 0 := by
  -- a bound on the indices
  set M : ℝ := ∑ q ∈ F, |(q : ℝ)| with hM
  have hMq : ∀ q ∈ F, |(q : ℝ)| ≤ M := fun q hq =>
    Finset.single_le_sum (f := fun q : ℚ => |(q : ℝ)|) (fun _ _ => abs_nonneg _) hq
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hEbd : ∀ x ∈ E, -M ≤ x ∧ x ≤ M + 1 := by
    intro x hx
    have h1 := bop_eq_rep_add_idx x
    have h2 := bop_rep_mem x
    have h3 := abs_le.1 (hMq _ (hsub x hx))
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  obtain ⟨m, hm0, hm⟩ := bop_exists_gap F
  -- the translates
  have hbound : ∀ K : ℕ, ((K : ℝ≥0∞) + 1) * volume E ≤ ENNReal.ofReal (2 * M + 1 + m) := by
    intro K
    set η : ℚ := m / (K + 1) with hη
    have hη0 : 0 < η := by positivity
    have hKη : (K : ℚ) * η < m := by
      rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    set Tr : ℕ → Set ℝ := fun k => (fun x => x + (-((k : ℝ) * η))) ⁻¹' E with hTr
    have hTm : ∀ k, MeasurableSet (Tr k) := fun k =>
      hE.preimage (measurable_id.add measurable_const)
    have hTvol : ∀ k, volume (Tr k) = volume E := fun k =>
      measure_preimage_add_right volume _ E
    have hdisj : PairwiseDisjoint (↑(Finset.range (K + 1))) Tr := by
      intro j hj k hk hjk
      rw [Function.onFun, Set.disjoint_left]
      intro x hxj hxk
      simp only [hTr, mem_preimage] at hxj hxk
      set e1 := x + -((j : ℝ) * η)
      set e2 := x + -((k : ℝ) * η)
      have hrat : e1 - e2 = (((k : ℚ) - j) * η : ℚ) := by
        simp only [e1, e2]; push_cast; ring
      have hrep : bopRep e1 = bopRep e2 := bop_rep_eq ⟨_, hrat⟩
      have hidx : (((k : ℚ) - j) * η : ℚ) = bopIdx e1 - bopIdx e2 := by
        have h1 := bop_eq_rep_add_idx e1
        have h2 := bop_eq_rep_add_idx e2
        have : ((((k : ℚ) - j) * η : ℚ) : ℝ) = ((bopIdx e1 - bopIdx e2 : ℚ) : ℝ) := by
          rw [← hrat]; push_cast; linarith
        exact_mod_cast this
      have hjk' : (j : ℚ) ≠ k := by exact_mod_cast hjk
      have hj' : (j : ℚ) ≤ K := by
        have := Finset.mem_range.1 hj; exact_mod_cast Nat.lt_succ_iff.1 this
      have hk' : (k : ℚ) ≤ K := by
        have := Finset.mem_range.1 hk; exact_mod_cast Nat.lt_succ_iff.1 this
      by_cases hq : bopIdx e1 = bopIdx e2
      · rw [hq, sub_self] at hidx
        rcases mul_eq_zero.1 hidx with h | h
        · exact hjk' (by linarith)
        · exact hη0.ne' h
      · have := hm _ (hsub e1 hxj) _ (hsub e2 hxk) hq
        rw [← hidx, abs_mul, abs_of_pos hη0] at this
        have hab : |(k : ℚ) - j| ≤ K := by
          rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℚ) ≤ j),
            (Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
        nlinarith
    have hU : (⋃ k ∈ Finset.range (K + 1), Tr k) ⊆ Icc (-M) (M + 1 + m) := by
      intro x hx
      simp only [mem_iUnion, Finset.mem_range] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      have hb := hEbd _ hxk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) * η := by positivity
      have hkm : (k : ℝ) * η ≤ m := by
        have : (k : ℚ) * η ≤ m := by
          have : (k : ℚ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 hk
          nlinarith
        exact_mod_cast this
      constructor <;> linarith [hb.1, hb.2]
    calc ((K : ℝ≥0∞) + 1) * volume E
        = ∑ k ∈ Finset.range (K + 1), volume (Tr k) := by
          simp only [hTvol, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ = volume (⋃ k ∈ Finset.range (K + 1), Tr k) :=
          (measure_biUnion_finset hdisj fun k _ => hTm k).symm
      _ ≤ volume (Icc (-M) (M + 1 + m)) := measure_mono hU
      _ = ENNReal.ofReal (2 * M + 1 + m) := by rw [Real.volume_Icc]; congr 1; ring
  by_contra h0
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt h0 (ENNReal.ofReal_ne_top (r := 2 * M + 1 + m))
  have := hbound n
  have : (n : ℝ≥0∞) * volume E ≤ ((n : ℝ≥0∞) + 1) * volume E := by gcongr; exact le_self_add
  exact absurd (hn.trans_le (this.trans (hbound n))) (lt_irrefl _)

/-- The two-dimensional version: measurable subsets of `{z | bopIdx z.1 ∈ F}` are null. -/
theorem bop_null_of_idx_mem_prod {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (F : Finset ℚ)
    (hsub : ∀ z ∈ E, bopIdx z.1 ∈ F) : volume E = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hE]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun y => ?_)
  exact bop_null_of_idx_mem (hE.preimage (measurable_id.prodMk measurable_const)) F
    fun x hx => hsub (x, y) hx

/-- **The strictly positive function** `1 / (e (bopIdx z.1) + 1)`, `e = Denumerable.eqv ℚ`. -/
def bopPhi (z : ℝ × ℝ) : ℝ := 1 / ((Denumerable.eqv ℚ (bopIdx z.1) : ℝ) + 1)

theorem bop_phi_pos (z : ℝ × ℝ) : 0 < bopPhi z := by
  unfold bopPhi; positivity

/-- **`∫⁻ ofReal (bopPhi z) dz = 0`** although `bopPhi > 0` everywhere. -/
theorem bop_lintegral_phi : ∫⁻ z, ENNReal.ofReal (bopPhi z) = 0 := by
  obtain ⟨g, hg, hgle, heq⟩ := exists_measurable_le_lintegral_eq volume
    (fun z : ℝ × ℝ => ENNReal.ofReal (bopPhi z))
  rw [heq, lintegral_eq_zero_iff hg]
  rw [Filter.EventuallyEq, ae_iff]
  have hsub : {z | ¬ g z = (0 : ℝ × ℝ → ℝ≥0∞) z} ⊆
      ⋃ n : ℕ, {z | ((n : ℝ≥0∞))⁻¹ < g z} := by
    intro z hz
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := g z) hz
    exact mem_iUnion.2 ⟨n, hn⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
  refine bop_null_of_idx_mem_prod (measurableSet_lt measurable_const hg)
    ((Finset.range (n + 1)).image (Denumerable.eqv ℚ).symm) fun z hz => ?_
  have h1 : ((n : ℝ≥0∞))⁻¹ < ENNReal.ofReal (bopPhi z) := lt_of_lt_of_le hz (hgle z)
  have h2 : ENNReal.ofReal (bopPhi z) = ((Denumerable.eqv ℚ (bopIdx z.1) : ℝ≥0∞) + 1)⁻¹ := by
    unfold bopPhi
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [h2, ENNReal.inv_lt_inv] at h1
  have h3 : Denumerable.eqv ℚ (bopIdx z.1) + 1 < n := by exact_mod_cast h1
  refine Finset.mem_image.2 ⟨Denumerable.eqv ℚ (bopIdx z.1), Finset.mem_range.2 (by omega), ?_⟩
  exact (Denumerable.eqv ℚ).symm_apply_apply (bopIdx z.1)

/-- Zero integral of `bopPhi` over every set. -/
theorem bop_setLIntegral_phi (B : Set (ℝ × ℝ)) : ∫⁻ z in B, ENNReal.ofReal (bopPhi z) = 0 :=
  le_antisymm ((lintegral_mono' Measure.restrict_le_self le_rfl).trans bop_lintegral_phi.le)
    bot_le

end BlockBand.Endpoints
