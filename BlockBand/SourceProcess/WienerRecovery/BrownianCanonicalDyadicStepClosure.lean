module

public import BlockBand.SourceProcess.WienerRecovery.BrownianCanonicalDyadicAffineClosure

/-!
# Uniform step bound for canonical Brownian dyadic interpolants

This module proves the deterministic `n → n+1` sup-norm estimate for the fixed
canonical nodal-hat interpolants.  A large refinement step is forced by a large
level-`n+1` raw dyadic edge increment.  All statements are pathwise at fixed finite
level; no probability estimate or limit is taken.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped NNReal Topology BigOperators
open Filter

namespace BrownianCanonicalDyadicStepClosure

open BrownianDyadicChainingClosure
open BrownianDyadicInterpolationCorrection
open BrownianDyadicCompactExtension
open BrownianCanonicalDyadicInterpolant
open BrownianCanonicalDyadicInterpolantFacts
open BrownianCanonicalDyadicAffineClosure
open BrownianDyadicGaussianEnvelope
open ScalarWienerMeasureConstruction

private theorem normalized_mem_unit_edge_step
    (T : NNReal) (hT : 0 < T) (n : ℕ) (k : Fin (2 ^ n))
    (t : Set.Icc (0 : NNReal) T)
    (hleft : dyadicLeft T n k ≤ t.1)
    (hright : t.1 ≤ dyadicRight T n k) :
    (k.1 : ℝ) ≤ (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ) ∧
      (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ) ≤ (k.1 + 1 : ℕ) := by
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

private theorem canonical_apply_eq_normalized
    (T : NNReal) (hT : 0 < T) (ω : BrownianRawPath) (n : ℕ)
    (k : Fin (2 ^ n)) (t : Set.Icc (0 : NNReal) T)
    (hl : dyadicLeft T n k ≤ t.1) (hr : t.1 ≤ dyadicRight T n k) :
    let x : ℝ := (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ)
    canonicalRawDyadicInterpolant T ω n t =
      ((k.1 + 1 : ℕ) - x) *
          rawCoordinateProcess (dyadicLeft T n k) ω +
        (x - k.1) * rawCoordinateProcess (dyadicRight T n k) ω := by
  dsimp
  let x : ℝ := (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ)
  have hx := normalized_mem_unit_edge_step T hT n k t hl hr
  have hs := sum_dyadicLinearHat_smul_eq_affine n k.1 k.2 x hx.1 hx.2
    (fun j => rawCoordinateProcess (T * (j : NNReal) / (2 ^ n : ℕ)) ω)
  simpa [canonicalRawDyadicInterpolant, dyadicHat, dyadicLinearHat, dyadicNode,
    dyadicLeft, dyadicRight, x, smul_eq_mul, mul_comm] using hs

private theorem not_mem_badLevel_imp
    {Ω : Type*} (B : NNReal → Ω → ℝ) (T : NNReal) (ε : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (hω : ω ∉ dyadicBadLevel B T ε n) :
    ∀ k : Fin (2 ^ n),
      |B (dyadicLeft T n k) ω - B (dyadicRight T n k) ω| < ε n := by
  intro k
  have hk : ω ∉ {ω | ε n ≤
      |B (dyadicLeft T n k) ω - B (dyadicRight T n k) ω|} := by
    intro hm
    exact hω (Set.mem_iUnion.2 ⟨k, hm⟩)
  simpa only [Set.mem_ofPred_eq, not_le] using hk

private theorem abs_affine_refinement_left_lt
    {A B C u ε : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hAB : |A - B| < ε) (hBC : |B - C| < ε) :
    |((1 - 2 * u) * A + (2 * u) * B) - ((1 - u) * A + u * C)| < ε := by
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hAB
  calc
    _ = |u| * |(B - A) + (B - C)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ u * (|B - A| + |B - C|) := by
      rw [abs_of_nonneg hu0]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hu0
    _ < ε := by
      rw [abs_sub_comm B A]
      nlinarith [abs_nonneg (A - B), abs_nonneg (B - C)]

private theorem abs_affine_refinement_right_lt
    {A B C u ε : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 1)
    (hAB : |A - B| < ε) (hBC : |B - C| < ε) :
    |((2 - 2 * u) * B + (2 * u - 1) * C) -
        ((1 - u) * A + u * C)| < ε := by
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hAB
  calc
    _ = |1 - u| * |(B - A) + (B - C)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (1 - u) * (|B - A| + |B - C|) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hu1)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _)
        (sub_nonneg.mpr hu1)
    _ < ε := by
      rw [abs_sub_comm B A]
      nlinarith [abs_nonneg (A - B), abs_nonneg (B - C)]

private theorem dyadicLeft_succ_even (T : NNReal) (n : ℕ) (k : Fin (2 ^ n)) :
    dyadicLeft T n.succ ⟨2 * k.1, by simp [pow_succ]; omega⟩ =
      dyadicLeft T n k := by
  apply NNReal.eq
  simp [dyadicLeft, pow_succ]
  ring

private theorem dyadicRight_succ_odd (T : NNReal) (n : ℕ) (k : Fin (2 ^ n)) :
    dyadicRight T n.succ ⟨2 * k.1 + 1, by simp [pow_succ]; omega⟩ =
      dyadicRight T n k := by
  apply NNReal.eq
  simp [dyadicRight, pow_succ]
  ring

private theorem dyadicRight_succ_even_eq_left_succ_odd
    (T : NNReal) (n : ℕ) (k : Fin (2 ^ n)) :
    dyadicRight T n.succ ⟨2 * k.1, by simp [pow_succ]; omega⟩ =
      dyadicLeft T n.succ ⟨2 * k.1 + 1, by simp [pow_succ]; omega⟩ := by
  apply NNReal.eq
  simp [dyadicLeft, dyadicRight]

private theorem le_midpoint_iff
    (T : NNReal) (hT : 0 < T) (n : ℕ) (k : Fin (2 ^ n))
    (t : Set.Icc (0 : NNReal) T) :
    t.1 ≤ dyadicRight T n.succ ⟨2 * k.1, by simp [pow_succ]; omega⟩ ↔
      (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ) - k.1 ≤ 1 / 2 := by
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  constructor
  · intro h
    have hr : (t.1 : ℝ) ≤ (T : ℝ) * ((2 * k.1 : ℕ) + 1) /
        ((2 : ℝ) ^ n.succ) := by exact_mod_cast h
    norm_num [pow_succ] at hr ⊢
    field_simp [hTr.ne'] at hr ⊢
    nlinarith
  · intro h
    apply_mod_cast (show (t.1 : ℝ) ≤ (T : ℝ) * ((2 * k.1 : ℕ) + 1) /
        ((2 : ℝ) ^ n.succ) by
      norm_num [pow_succ] at h ⊢
      field_simp [hTr.ne'] at h ⊢
      nlinarith)

private theorem midpoint_le_iff
    (T : NNReal) (hT : 0 < T) (n : ℕ) (k : Fin (2 ^ n))
    (t : Set.Icc (0 : NNReal) T) :
    dyadicLeft T n.succ ⟨2 * k.1 + 1, by simp [pow_succ]; omega⟩ ≤ t.1 ↔
      1 / 2 ≤ (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ) - k.1 := by
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  constructor
  · intro h
    have hr : (T : ℝ) * ((2 * k.1 + 1 : ℕ) : ℝ) /
        ((2 : ℝ) ^ n.succ) ≤ (t.1 : ℝ) := by exact_mod_cast h
    norm_num [pow_succ] at hr ⊢
    field_simp [hTr.ne'] at hr ⊢
    nlinarith
  · intro h
    apply_mod_cast (show (T : ℝ) * ((2 * k.1 + 1 : ℕ) : ℝ) /
        ((2 : ℝ) ^ n.succ) ≤ (t.1 : ℝ) by
      norm_num [pow_succ] at h ⊢
      field_simp [hTr.ne'] at h ⊢
      nlinarith)

private theorem pointwise_dist_lt_of_not_mem_badLevel
    (T : NNReal) (hT : 0 < T) (ω : BrownianRawPath) (n : ℕ)
    (hgood : ω ∉ dyadicBadLevel rawCoordinateProcess T
      (compactDyadicModulus T) n.succ)
    (t : Set.Icc (0 : NNReal) T) :
    dist (canonicalRawDyadicInterpolant T ω n t)
        (canonicalRawDyadicInterpolant T ω n.succ t) <
      compactDyadicModulus T n.succ := by
  obtain ⟨k, hl, hr⟩ := exists_dyadicEdge_mem T hT n t
  let x : ℝ := (2 : ℝ) ^ n * (t.1 : ℝ) / (T : ℝ)
  let u : ℝ := x - k.1
  have hu0 : 0 ≤ u := by
    exact sub_nonneg.mpr
      (normalized_mem_unit_edge_step T hT n k t hl hr).1
  have hu1 : u ≤ 1 := by
    have := (normalized_mem_unit_edge_step T hT n k t hl hr).2
    norm_num at this ⊢
    linarith
  let q0 : Fin (2 ^ n.succ) := ⟨2 * k.1, by simp [pow_succ]; omega⟩
  let q1 : Fin (2 ^ n.succ) := ⟨2 * k.1 + 1, by simp [pow_succ]; omega⟩
  have hinc := not_mem_badLevel_imp rawCoordinateProcess T
    (compactDyadicModulus T) n.succ ω hgood
  have hAB := hinc q0
  have hBC := hinc q1
  rw [show dyadicLeft T n.succ q0 = dyadicLeft T n k by
        simpa [q0] using dyadicLeft_succ_even T n k] at hAB
  rw [show dyadicLeft T n.succ q1 = dyadicRight T n.succ q0 by
        simpa [q0, q1] using (dyadicRight_succ_even_eq_left_succ_odd T n k).symm,
      show dyadicRight T n.succ q1 = dyadicRight T n k by
        simpa [q1] using dyadicRight_succ_odd T n k] at hBC
  by_cases hhalf : u ≤ 1 / 2
  · have hlf : dyadicLeft T n.succ q0 ≤ t.1 := by
      rw [show dyadicLeft T n.succ q0 = dyadicLeft T n k by
        simpa [q0] using dyadicLeft_succ_even T n k]
      exact hl
    have hrf : t.1 ≤ dyadicRight T n.succ q0 := by
      exact (le_midpoint_iff T hT n k t).2 hhalf
    rw [canonical_apply_eq_normalized T hT ω n k t hl hr,
      canonical_apply_eq_normalized T hT ω n.succ q0 t hlf hrf]
    rw [show dyadicLeft T n.succ q0 = dyadicLeft T n k by
          simpa [q0] using dyadicLeft_succ_even T n k]
    rw [dist_comm, Real.dist_eq]
    have hlocal := abs_affine_refinement_left_lt hu0 hhalf hAB hBC
    convert hlocal using 1
    simp [q0, x, u, pow_succ]
    ring_nf
  · have hhalf' : 1 / 2 ≤ u := le_of_lt (lt_of_not_ge hhalf)
    have hlf : dyadicLeft T n.succ q1 ≤ t.1 := by
      exact (midpoint_le_iff T hT n k t).2 hhalf'
    have hrf : t.1 ≤ dyadicRight T n.succ q1 := by
      rw [show dyadicRight T n.succ q1 = dyadicRight T n k by
        simpa [q1] using dyadicRight_succ_odd T n k]
      exact hr
    rw [canonical_apply_eq_normalized T hT ω n k t hl hr,
      canonical_apply_eq_normalized T hT ω n.succ q1 t hlf hrf]
    rw [show dyadicLeft T n.succ q1 = dyadicRight T n.succ q0 by
          simpa [q0, q1] using (dyadicRight_succ_even_eq_left_succ_odd T n k).symm,
      show dyadicRight T n.succ q1 = dyadicRight T n k by
          simpa [q1] using dyadicRight_succ_odd T n k]
    rw [dist_comm, Real.dist_eq]
    have hlocal := abs_affine_refinement_right_lt hhalf' hu1 hAB hBC
    convert hlocal using 1
    simp [q0, q1, x, u, pow_succ]
    ring_nf

/-- The fixed canonical refinement step is charged to the new level's raw bad-edge
event.  The horizon is positive, then the sample and finite level are fixed; this is
a deterministic set inclusion with no probability or limiting assertion. -/
theorem canonicalRawDyadicInterpolant_badStep_subset
    (T : NNReal) (hT : 0 < T) (n : ℕ) :
    {ω | compactDyadicModulus T n.succ <
      dist (canonicalRawDyadicInterpolant T ω n)
        (canonicalRawDyadicInterpolant T ω n.succ)} ⊆
      dyadicBadLevel rawCoordinateProcess T (compactDyadicModulus T) n.succ := by
  intro ω hlarge
  let _ : Nonempty (Set.Icc (0 : NNReal) T) := ⟨⟨0, by simp⟩⟩
  by_contra hgood
  have hsmall : dist (canonicalRawDyadicInterpolant T ω n)
      (canonicalRawDyadicInterpolant T ω n.succ) <
      compactDyadicModulus T n.succ :=
    ContinuousMap.dist_lt_of_nonempty
      (pointwise_dist_lt_of_not_mem_badLevel T hT ω n hgood)
  exact (not_lt_of_ge (le_of_lt hlarge)) hsmall

end BrownianCanonicalDyadicStepClosure
end BlockBand.SourceProcess.WienerRecovery.CEH
