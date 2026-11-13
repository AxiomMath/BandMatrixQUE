module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWickDefs
public import BlockBand.Endpoints.Response.TaggedConvexOrderWickGenAlg

/-!
# The word generator on the tag words `Tr Q^r`

* `wg_polyValue_pairTerm`: for `i < j < r`, `pairTerm(w_r, i, j) ↦ κ T(r - (j-i), j - i)`,
  `T(a, b) = Tr(Q^aP)Tr(Q^bP') + Tr(Q^aP')Tr(Q^bP)`;
* `wg_polyValue_crossTerm`: `crossTerm(w_r, w_s, i, j) ↦ κ [Tr(Q^rPQ^sP') + Tr(Q^rP'Q^sP)]`;
* `wg_polyValue_wordDrift`: `wordDrift(w_r) ↦ Σ_{i<r} Σ_{i<j<r} κ T(r-(j-i), j-i)` (the `g`-term
  has no `P` separator to act on);
* `wg_polyValue_wordCov`: `wordCov(w_r, w_s) ↦ r s κ [Tr(Q^rPQ^sP') + Tr(Q^rP'Q^sP)]`;
* `wg_wordInjection_eq_zero`: the injection vanishes (`nI = 0`).

Also: `wg_mem_vars_wickPoly` (every variable of `Φ_m` is a tag word `w_r`, `r ≥ 1`) and the rank-one
decompositions `P = Σ_α u_α u_α*`, `P' = Σ_β w_β w_β*` (`wg_sum_vecMulVec_col`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

/-!
## Rank-one decompositions of `P` and `P'`
-/

theorem wg_sum_vecMulVec_col {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) :
    ∑ a, vecMulVec (fun i => M i a) (star fun i => M i a) = M * Mᴴ := by
  ext i j
  simp [Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply, conjTranspose_apply]

theorem wg_proj_mul_conjTranspose (W : ℕ) : nearProjection W * (nearProjection W)ᴴ =
    nearProjection W := by
  rw [tcs_nearProjection_hermitian, tcs_nearProjection_idem]

theorem wg_conjProj_eq (b e : ℝ) (W l : ℕ) (ω : GrowthPath W) :
    ((scatteringMatrix b e W l ω)ᴴ * nearProjection W) *
        ((scatteringMatrix b e W l ω)ᴴ * nearProjection W)ᴴ = tcw_conjProj b e W l ω := by
  unfold tcw_conjProj
  rw [conjTranspose_mul, conjTranspose_conjTranspose, tcs_nearProjection_hermitian]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (nearProjection W), tcs_nearProjection_idem]

theorem wg_proj_add_current (b e : ℝ) (W l : ℕ) (ω : GrowthPath W) :
    nearProjection W + pathCurrent b e W l ω = tcw_conjProj b e W l ω := by
  unfold pathCurrent tcw_conjProj
  abel

/-!
## Values of words built from `w_r`
-/

/-- The letter `(Q, I)`. -/
abbrev wg_x0 : TraceLetter 1 0 × Separator := (TraceLetter.tag 0, Separator.id)

theorem wg_tagWord_eq (r : ℕ) : tcx_tagWord r = List.replicate r wg_x0 := rfl

section Path

variable (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W)

/-- The matrix `A_i B_i` of a letter. -/
abbrev wg_lm (x : TraceLetter 1 0 × Separator) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  letterMatrix b e (tcw_tagFamily k) tcw_noInterval W l ω x.1 * separatorMatrix b e W l ω x.2

theorem wg_wordValue_eq (L : TraceWord 1 0) :
    wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω L = ((L.map (wg_lm b e W l k ω)).prod).trace :=
  rfl

theorem wg_prod_replicate (a : ℕ) :
    ((List.replicate a wg_x0).map (wg_lm b e W l k ω)).prod = tco_tagQ b e W l k ω ^ a := by
  rw [List.map_replicate, List.prod_replicate]
  simp only [wg_lm, separatorMatrix, mul_one, tcx_letterMatrix_tag]

theorem wg_setLastSep_replicate (a : ℕ) (s : Separator) :
    setLastSep (List.replicate (a + 1) wg_x0) s = List.replicate a wg_x0 ++ [(TraceLetter.tag 0, s)] := by
  unfold setLastSep
  rw [List.dropLast_replicate, List.getLast?_replicate]
  simp

theorem wg_prod_setLastSep (a : ℕ) (ha : 0 < a) :
    ((setLastSep (List.replicate a wg_x0) .proj).map (wg_lm b e W l k ω)).prod =
      tco_tagQ b e W l k ω ^ a * nearProjection W := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  rw [wg_setLastSep_replicate, List.map_append, List.prod_append, wg_prod_replicate]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, wg_lm,
    separatorMatrix, tcx_letterMatrix_tag]
  rw [pow_succ, Matrix.mul_assoc]

theorem wg_prod_current :
    (([(TraceLetter.current, Separator.id)] : TraceWord 1 0).map (wg_lm b e W l k ω)).prod =
      pathCurrent b e W l ω := by
  simp [wg_lm, letterMatrix, separatorMatrix]

theorem wg_sepAt_replicate (r i : ℕ) : sepAt (List.replicate r wg_x0) i = Separator.id := by
  unfold sepAt
  by_cases h : i < r
  · rw [List.getD_replicate _ h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]

/-!
## `pairTerm`, `crossTerm`, `wordDrift`, `wordCov` on tag words
-/

/-- `T(a, b) = Tr(Q^aP)Tr(Q^bP') + Tr(Q^aP')Tr(Q^bP)`. -/
def wg_T (a c : ℕ) : ℂ :=
  (tco_tagQ b e W l k ω ^ a * nearProjection W).trace *
      (tco_tagQ b e W l k ω ^ c * tcw_conjProj b e W l ω).trace +
    (tco_tagQ b e W l k ω ^ a * tcw_conjProj b e W l ω).trace *
      (tco_tagQ b e W l k ω ^ c * nearProjection W).trace

/-- `C(r, s) = Tr(Q^rPQ^sP') + Tr(Q^rP'Q^sP)`. -/
def wg_Cr (r s : ℕ) : ℂ :=
  (tco_tagQ b e W l k ω ^ r * nearProjection W * tco_tagQ b e W l k ω ^ s *
      tcw_conjProj b e W l ω).trace +
    (tco_tagQ b e W l k ω ^ r * tcw_conjProj b e W l ω * tco_tagQ b e W l k ω ^ s *
      nearProjection W).trace

theorem wg_trace_Q_P_add_J (a : ℕ) :
    (tco_tagQ b e W l k ω ^ a * nearProjection W).trace +
        (tco_tagQ b e W l k ω ^ a * pathCurrent b e W l ω).trace =
      (tco_tagQ b e W l k ω ^ a * tcw_conjProj b e W l ω).trace := by
  rw [← Matrix.trace_add, ← Matrix.mul_add, wg_proj_add_current]

theorem wg_polyValue_pairTerm (D0 : ℝ) (r i j : ℕ) (hij : i < j) (hj : j < r) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω (pairTerm D0 (tcx_tagWord r) i j) =
      ((D0 / 2 : ℝ) : ℂ) * wg_T b e W l k ω (r - (j - i)) (j - i) := by
  unfold pairTerm polyValue
  rw [wg_tagWord_eq, List.rotate_replicate, List.rotate_replicate, List.take_replicate,
    List.take_replicate, List.length_replicate, wg_sepAt_replicate, wg_sepAt_replicate,
    show min (r - (j - i)) r = r - (j - i) by omega, show min (j - i) r = j - i by omega]
  simp only [map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [wg_wordValue_eq, wg_wordValue_eq, wg_wordValue_eq, wg_wordValue_eq,
    wg_prod_setLastSep _ _ _ _ _ _ _ (by omega), wg_prod_setLastSep _ _ _ _ _ _ _ (by omega),
    List.map_append, List.prod_append, List.map_append, List.prod_append, wg_prod_replicate,
    wg_prod_replicate, wg_prod_current, wg_trace_Q_P_add_J, wg_trace_Q_P_add_J]
  unfold wg_T
  ring

theorem wg_polyValue_crossTerm (D0 : ℝ) (r s i j : ℕ) (hr : 0 < r) (hs : 0 < s) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
        (crossTerm D0 (tcx_tagWord r) (tcx_tagWord s) i j) =
      ((D0 / 2 : ℝ) : ℂ) * wg_Cr b e W l k ω r s := by
  unfold crossTerm polyValue
  rw [wg_tagWord_eq, wg_tagWord_eq, List.rotate_replicate, List.rotate_replicate,
    wg_sepAt_replicate, wg_sepAt_replicate]
  simp only [map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]
  simp only [wg_wordValue_eq, List.map_append, List.prod_append,
    wg_prod_setLastSep _ _ _ _ _ _ _ hr, wg_prod_setLastSep _ _ _ _ _ _ _ hs, wg_prod_replicate,
    wg_prod_current]
  unfold wg_Cr
  rw [← wg_proj_add_current]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc]

theorem wg_wordInjection_eq_zero (t : ℝ) (w : TraceWord 1 0) :
    wordInjection b tcw_noInterval t w = 0 := by
  unfold wordInjection
  split
  · next a _ => exact a.elim0
  · rfl

theorem wg_polyValue_wordDrift (D0 : ℝ) (r : ℕ) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω (wordDrift D0 (tcx_tagWord r)) =
      ∑ i ∈ range r, ∑ j ∈ Ioo i r,
        ((D0 / 2 : ℝ) : ℂ) * wg_T b e W l k ω (r - (j - i)) (j - i) := by
  unfold wordDrift
  have hc : (tcx_tagWord r).countP (fun x => decide (x.2 = Separator.proj)) = 0 := by
    rw [wg_tagWord_eq, List.countP_replicate]
    simp
  unfold polyValue
  rw [hc, map_add, map_neg, map_sum, wg_tagWord_eq, List.length_replicate, ← wg_tagWord_eq]
  simp only [Nat.cast_zero, mul_zero, zero_mul, map_zero, neg_zero, zero_add, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_Ioo.1 hj
  exact wg_polyValue_pairTerm b e W l k ω D0 r i j hj'.1 hj'.2

theorem wg_polyValue_wordCov (D0 : ℝ) (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    polyValue b e (tcw_tagFamily k) tcw_noInterval W l ω
        (wordCov D0 (tcx_tagWord r) (tcx_tagWord s)) =
      (r : ℂ) * (s : ℂ) * (((D0 / 2 : ℝ) : ℂ) * wg_Cr b e W l k ω r s) := by
  unfold wordCov
  rw [wg_tagWord_eq, wg_tagWord_eq, List.length_replicate, List.length_replicate,
    ← wg_tagWord_eq, ← wg_tagWord_eq]
  unfold polyValue
  simp only [map_sum]
  have h : ∀ i j, MvPolynomial.eval (wordValue b e (tcw_tagFamily k) tcw_noInterval W l ω)
      (crossTerm D0 (tcx_tagWord r) (tcx_tagWord s) i j) =
        ((D0 / 2 : ℝ) : ℂ) * wg_Cr b e W l k ω r s :=
    fun i j => wg_polyValue_crossTerm b e W l k ω D0 r s i j hr hs
  simp only [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end Path

/-!
## The variables of `Φ_m`
-/

theorem wg_mem_vars_wickPoly (m : ℕ) :
    ∀ w ∈ (tcx_wickPoly m).vars, ∃ r, 0 < r ∧ w = tcx_tagWord r := by
  let S : Set (TracePoly 1 0) := {Φ | ∀ w ∈ Φ.vars, ∃ r, 0 < r ∧ w = tcx_tagWord r}
  have hadd : ∀ Φ Ψ, Φ ∈ S → Ψ ∈ S → Φ + Ψ ∈ S := fun Φ Ψ hΦ hΨ w hw => by
    rcases Finset.mem_union.1 (MvPolynomial.vars_add_subset Φ Ψ hw) with h | h
    · exact hΦ w h
    · exact hΨ w h
  have hmul : ∀ Φ Ψ, Φ ∈ S → Ψ ∈ S → Φ * Ψ ∈ S := fun Φ Ψ hΦ hΨ w hw => by
    rcases Finset.mem_union.1 (MvPolynomial.vars_mul Φ Ψ hw) with h | h
    · exact hΦ w h
    · exact hΨ w h
  have hzero : (0 : TracePoly 1 0) ∈ S := fun w hw => by simp at hw
  have hone : (1 : TracePoly 1 0) ∈ S := fun w hw => by simp at hw
  unfold tcx_wickPoly
  refine Finset.sum_induction _ (· ∈ S) hadd hzero fun π _ => ?_
  refine Multiset.prod_induction (· ∈ S) _ hmul hone fun p hp => ?_
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hp
  intro w hw
  rw [MvPolynomial.vars_X, Finset.mem_singleton] at hw
  exact ⟨r, π.partition.parts_pos hr, hw⟩

end BlockBand.Endpoints
