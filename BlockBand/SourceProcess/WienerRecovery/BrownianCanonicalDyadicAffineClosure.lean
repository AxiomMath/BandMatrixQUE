module

public import BlockBand.SourceProcess.WienerRecovery.BrownianCanonicalDyadicInterpolantFacts
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Affine closure for the canonical Brownian dyadic interpolants

This module translates the normalized nodal-hat identity into the physical dyadic
mesh on `[0,T]`.  For `T>0`, the fixed canonical interpolant is shown to obey the
exact affine formula on every mesh edge.  The proof is deterministic and finite at
fixed level `n`; no probability statement or limit is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped NNReal Topology BigOperators

namespace BrownianCanonicalDyadicAffineClosure

open BrownianDyadicChainingClosure
open BrownianDyadicInterpolationCorrection
open BrownianDyadicCompactExtension
open BrownianCanonicalDyadicInterpolant
open BrownianCanonicalDyadicInterpolantFacts
open ScalarWienerMeasureConstruction

private theorem normalized_mem_unit_edge
    (T : NNReal) (hT : 0 < T) (n : ℕ) (k : Fin (2 ^ n))
    (t : Set.Icc (0 : NNReal) T)
    (hleft : dyadicLeft T n k ≤ t.1)
    (hright : t.1 ≤ dyadicRight T n k) :
    (k.1 : ℝ) ≤ (2 ^ n : ℝ) * (t.1 : ℝ) / (T : ℝ) ∧
      (2 ^ n : ℝ) * (t.1 : ℝ) / (T : ℝ) ≤ (k.1 + 1 : ℕ) := by
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hlr : (T : ℝ) * (k.1 : ℝ) / ((2 : ℝ) ^ n) ≤ (t.1 : ℝ) := by
    exact_mod_cast hleft
  have hrr : (t.1 : ℝ) ≤ (T : ℝ) * ((k.1 : ℝ) + 1) / ((2 : ℝ) ^ n) := by
    exact_mod_cast hright
  constructor
  · rw [le_div_iff₀ hTr]
    have hlr' := (div_le_iff₀ hp).mp hlr
    nlinarith
  · rw [div_le_iff₀ hTr]
    have hrr' := (le_div_iff₀ hp).mp hrr
    convert hrr' using 1 <;> norm_num <;> ring

/-- On each physical level-`n` dyadic edge, the canonical nodal-hat interpolant is
exactly the affine interpolation of the two raw endpoint coordinates.  The binders
`T,hT,ω,n,k,t` are fixed in that order, and no limit or probabilistic uniformity is
asserted. -/
theorem canonicalRawDyadicInterpolant_apply_eq_affine
    (T : NNReal) (hT : 0 < T) (ω : BrownianRawPath) (n : ℕ)
    (k : Fin (2 ^ n)) (t : Set.Icc (0 : NNReal) T)
    (hleft : dyadicLeft T n k ≤ t.1)
    (hright : t.1 ≤ dyadicRight T n k) :
    canonicalRawDyadicInterpolant T ω n t =
      (((dyadicRight T n k : NNReal) : ℝ) - (t.1 : ℝ)) /
          (((dyadicRight T n k : NNReal) : ℝ) -
            ((dyadicLeft T n k : NNReal) : ℝ)) *
          rawCoordinateProcess (dyadicLeft T n k) ω +
        ((t.1 : ℝ) - ((dyadicLeft T n k : NNReal) : ℝ)) /
          (((dyadicRight T n k : NNReal) : ℝ) -
            ((dyadicLeft T n k : NNReal) : ℝ)) *
          rawCoordinateProcess (dyadicRight T n k) ω := by
  let x : ℝ := (2 ^ n : ℝ) * (t.1 : ℝ) / (T : ℝ)
  obtain ⟨hx0, hx1⟩ := normalized_mem_unit_edge T hT n k t hleft hright
  have hsum := sum_dyadicLinearHat_smul_eq_affine n k.1 k.2 x hx0 hx1
    (fun j => rawCoordinateProcess (T * (j : NNReal) / (2 ^ n : ℕ)) ω)
  rw [show canonicalRawDyadicInterpolant T ω n t =
      ∑ j : Fin (2 ^ n + 1),
        dyadicLinearHat j.1 x *
          rawCoordinateProcess (T * (j.1 : NNReal) / (2 ^ n : ℕ)) ω by
      simp [canonicalRawDyadicInterpolant, dyadicHat, dyadicLinearHat, dyadicNode, x,
        smul_eq_mul, mul_comm]]
  rw [show (∑ j : Fin (2 ^ n + 1),
        dyadicLinearHat j.1 x *
          rawCoordinateProcess (T * (j.1 : NNReal) / (2 ^ n : ℕ)) ω) =
      ((k.1 + 1 : ℕ) - x) *
          rawCoordinateProcess (T * (k.1 : NNReal) / (2 ^ n : ℕ)) ω +
        (x - k.1) *
          rawCoordinateProcess (T * ((k.1 + 1 : ℕ) : NNReal) /
            (2 ^ n : ℕ)) ω by simpa [smul_eq_mul] using hsum]
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp only [dyadicLeft, dyadicRight, x]
  norm_num
  field_simp
  ring

/-- For positive horizon, the fixed canonical nodal-hat construction satisfies the
exact raw-coordinate piecewise-linear specification at every level.  This is the
Kronecker/affine field of `BrownianCanonicalDyadicInterpolationFacts`; the statement is
pathwise at fixed `ω,n` and takes no limit. -/
theorem isRawDyadicPiecewiseLinear_canonicalRawDyadicInterpolant
    (T : NNReal) (hT : 0 < T) (ω : BrownianRawPath) (n : ℕ) :
    IsRawDyadicPiecewiseLinearInterpolant T ω n
      (canonicalRawDyadicInterpolant T ω n) := by
  have hp : (0 : NNReal) < (2 ^ n : ℕ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro k t ht
    have ha := canonicalRawDyadicInterpolant_apply_eq_affine T hT ω n k t
      (by exact le_of_eq ht.symm)
      (by rw [ht]; exact le_of_lt (by
        simp only [dyadicLeft, dyadicRight]
        apply div_lt_div_of_pos_right _ hp
        exact mul_lt_mul_of_pos_left (by exact_mod_cast Nat.lt_succ_self k.1) hT))
    rw [ha, ht]
    have hLR : dyadicLeft T n k < dyadicRight T n k := by
      simp only [dyadicLeft, dyadicRight]
      apply div_lt_div_of_pos_right _ hp
      exact mul_lt_mul_of_pos_left (by exact_mod_cast Nat.lt_succ_self k.1) hT
    have hne : (((dyadicRight T n k : NNReal) : ℝ) -
        ((dyadicLeft T n k : NNReal) : ℝ)) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (by exact_mod_cast hLR))
    field_simp
    ring
  · intro k t ht
    have ha := canonicalRawDyadicInterpolant_apply_eq_affine T hT ω n k t
      (by rw [ht]; exact le_of_lt (by
        simp only [dyadicLeft, dyadicRight]
        apply div_lt_div_of_pos_right _ hp
        exact mul_lt_mul_of_pos_left (by exact_mod_cast Nat.lt_succ_self k.1) hT))
      (by exact le_of_eq ht)
    rw [ha, ht]
    have hLR : dyadicLeft T n k < dyadicRight T n k := by
      simp only [dyadicLeft, dyadicRight]
      apply div_lt_div_of_pos_right _ hp
      exact mul_lt_mul_of_pos_left (by exact_mod_cast Nat.lt_succ_self k.1) hT
    have hne : (((dyadicRight T n k : NNReal) : ℝ) -
        ((dyadicLeft T n k : NNReal) : ℝ)) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (by exact_mod_cast hLR))
    field_simp
    ring
  · exact fun k t hl hr =>
      canonicalRawDyadicInterpolant_apply_eq_affine T hT ω n k t hl hr

private theorem exists_fin_unit_edge (n : ℕ) (x : ℝ)
    (hx0 : 0 ≤ x) (hxN : x ≤ (2 ^ n : ℕ)) :
    ∃ k : Fin (2 ^ n), (k.1 : ℝ) ≤ x ∧ x ≤ (k.1 + 1 : ℕ) := by
  by_cases htop : x = (2 ^ n : ℕ)
  · have hpow : 0 < 2 ^ n := by positivity
    let k : Fin (2 ^ n) := ⟨2 ^ n - 1, Nat.sub_lt hpow Nat.zero_lt_one⟩
    refine ⟨k, ?_, ?_⟩
    · rw [htop]
      simp [k]
    · rw [htop]
      change ((2 ^ n : ℕ) : ℝ) ≤ (((2 ^ n - 1) + 1 : ℕ) : ℝ)
      have hm : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
      exact_mod_cast (le_of_eq (Nat.sub_add_cancel hm).symm)
  · have hxlt : x < (2 ^ n : ℕ) := lt_of_le_of_ne hxN htop
    have hklt : ⌊x⌋₊ < 2 ^ n := (Nat.floor_lt hx0).2 hxlt
    let k : Fin (2 ^ n) := ⟨⌊x⌋₊, hklt⟩
    refine ⟨k, Nat.floor_le hx0, le_of_lt ?_⟩
    simpa [k] using (Nat.lt_succ_floor x)

/-- Every point of a positive compact horizon belongs to a level-`n` physical
dyadic edge.  The point and level are fixed before the edge is chosen; the statement
is deterministic and has no limiting quantifier. -/
theorem exists_dyadicEdge_mem
    (T : NNReal) (hT : 0 < T) (n : ℕ) (t : Set.Icc (0 : NNReal) T) :
    ∃ k : Fin (2 ^ n),
      dyadicLeft T n k ≤ t.1 ∧ t.1 ≤ dyadicRight T n k := by
  let x : ℝ := (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ)
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hx0 : 0 ≤ x := by positivity
  have hxN : x ≤ (2 ^ n : ℕ) := by
    rw [show ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n by norm_num]
    rw [div_le_iff₀ hTr]
    have ht : (t.1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast t.2.2
    nlinarith [show 0 ≤ (2 : ℝ) ^ n by positivity]
  obtain ⟨k, hk0, hk1⟩ := exists_fin_unit_edge n x hx0 hxN
  refine ⟨k, ?_, ?_⟩
  · exact_mod_cast (show (T : ℝ) * (k.1 : ℝ) / ((2 : ℝ) ^ n) ≤
        (t.1 : ℝ) by
      have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      rw [div_le_iff₀ hp]
      rw [le_div_iff₀ hTr] at hk0
      nlinarith)
  · exact_mod_cast (show (t.1 : ℝ) ≤
        (T : ℝ) * ((k.1 : ℝ) + 1) / ((2 : ℝ) ^ n) by
      have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      rw [le_div_iff₀ hp]
      rw [div_le_iff₀ hTr] at hk1
      convert hk1 using 1 <;> norm_num <;> ring)

/-- The raw dyadic affine specification determines at most one compact path on a
positive horizon.  Edge coverage is proved here, so the uniqueness field of
`BrownianRawDyadicInterpolationData` is a theorem. -/
theorem eq_of_isRawDyadicPiecewiseLinearInterpolant
    (T : NNReal) (hT : 0 < T) (ω : BrownianRawPath) (n : ℕ)
    {f g : CompactPath T}
    (hf : IsRawDyadicPiecewiseLinearInterpolant T ω n f)
    (hg : IsRawDyadicPiecewiseLinearInterpolant T ω n g) : f = g := by
  ext t
  obtain ⟨k, hl, hr⟩ := exists_dyadicEdge_mem T hT n t
  rw [hf.2.2 k t hl hr, hg.2.2 k t hl hr]

/-- Consequently, any compact path satisfying the raw dyadic affine specification
is the fixed canonical nodal-hat interpolant. -/
theorem eq_canonicalRawDyadicInterpolant_of_isRawDyadicPiecewiseLinear
    (T : NNReal) (hT : 0 < T) (ω : BrownianRawPath) (n : ℕ)
    (f : CompactPath T)
    (hf : IsRawDyadicPiecewiseLinearInterpolant T ω n f) :
    f = canonicalRawDyadicInterpolant T ω n :=
  eq_of_isRawDyadicPiecewiseLinearInterpolant T hT ω n hf
    (isRawDyadicPiecewiseLinear_canonicalRawDyadicInterpolant T hT ω n)

end BrownianCanonicalDyadicAffineClosure
end BlockBand.SourceProcess.WienerRecovery.CEH
