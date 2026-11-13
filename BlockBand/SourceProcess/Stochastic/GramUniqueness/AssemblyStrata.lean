module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepBounds
public import BlockBand.SourceProcess.Stochastic.SourceSDE.MatrixForms
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram uniqueness: the rank strata of a Gram state

`rankB H = max {k ≤ |c| : e_k(B) > 0}` and `rankC H = max {k ≤ |c| : e_k(M − B) > 0}`
(`Nat.findGreatest`), with `stratumIdx H = (rankB H, rankC H) : Fin (|c|+1) × Fin (|c|+1)`.
* `measurable_stratumIdx`: the index is measurable (each fiber is a finite Boolean combination
  of the open sets `{e_k > 0}`);
* `stratum_facts`: at a feasible state with index `(r, r')`,
  `e_{r+1}(B) = 0`, `e_r(B) > 0`, `e_{r'+1}(M−B) = 0`, `e_{r'}(M−B) > 0`
  (`e_0 = 1`; `e_k = 0` for `k > |c|`; `e_k ≥ 0` at feasible states). No rank theory is used.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.SourceSDE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {c : Type*} [Fintype c] [DecidableEq c]

theorem principalMinorSum_zero (A : Matrix c c ℂ) : principalMinorSum 0 A = 1 := by
  simp [principalMinorSum, Finset.powersetCard_zero]

theorem principalMinorSum_of_lt {k : ℕ} (hk : Fintype.card c < k) (A : Matrix c c ℂ) :
    principalMinorSum k A = 0 := by
  rw [principalMinorSum, Finset.powersetCard_eq_empty.2 (by simpa using hk)]
  simp

open Classical in
/-- Largest `k ≤ |c|` with `e_k(f) > 0`. -/
def rankOf (f : ℕ → ℝ) : ℕ := Nat.findGreatest (fun k => 0 < f k) (Fintype.card c)

/-- The rank index of `B`. -/
def rankB (H : Matrix c c ℂ × Matrix c c ℂ) : ℕ := rankOf (c := c) fun k => principalMinorSum k H.2

/-- The rank index of `M − B`. -/
def rankC (H : Matrix c c ℂ × Matrix c c ℂ) : ℕ :=
  rankOf (c := c) fun k => principalMinorSum k (H.1 - H.2)

/-- The stratum index. -/
def stratumIdx (H : Matrix c c ℂ × Matrix c c ℂ) : Fin (Fintype.card c + 1) × Fin (Fintype.card c + 1) :=
  (⟨rankB H, Nat.lt_succ_of_le (Nat.findGreatest_le _)⟩,
    ⟨rankC H, Nat.lt_succ_of_le (Nat.findGreatest_le _)⟩)

omit [DecidableEq c] in
theorem rankOf_facts {f : ℕ → ℝ} (h0 : f 0 = 1) (hbig : ∀ k, Fintype.card c < k → f k = 0)
    (hnn : ∀ k, 0 ≤ f k) : f (rankOf (c := c) f + 1) = 0 ∧ 0 < f (rankOf (c := c) f) := by
  unfold rankOf
  constructor
  · by_cases hle : Nat.findGreatest (fun k => 0 < f k) (Fintype.card c) + 1 ≤ Fintype.card c
    · have := Nat.findGreatest_is_greatest (P := fun k => 0 < f k) (Nat.lt_succ_self _) hle
      exact le_antisymm (not_lt.1 this) (hnn _)
    · exact hbig _ (not_le.1 hle)
  · by_cases hr : Nat.findGreatest (fun k => 0 < f k) (Fintype.card c) = 0
    · rw [hr, h0]; exact one_pos
    · exact Nat.findGreatest_of_ne_zero (P := fun k => 0 < f k) rfl hr

/-- **Stratum facts** at a feasible state. -/
theorem stratum_facts {D : Matrix c c ℂ} {H : Matrix c c ℂ × Matrix c c ℂ}
    (hH : GramFeasible D H) :
    principalMinorSum (rankB H + 1) H.2 = 0 ∧ 0 < principalMinorSum (rankB H) H.2 ∧
      principalMinorSum (rankC H + 1) (H.1 - H.2) = 0 ∧
        0 < principalMinorSum (rankC H) (H.1 - H.2) := by
  obtain ⟨h1, h2⟩ := rankOf_facts (c := c) (f := fun k => principalMinorSum k H.2)
    (principalMinorSum_zero _) (fun k hk => principalMinorSum_of_lt hk _)
    (fun k => (principalMinorSum_nonneg_of_feasible hH k).1)
  obtain ⟨h3, h4⟩ := rankOf_facts (c := c) (f := fun k => principalMinorSum k (H.1 - H.2))
    (principalMinorSum_zero _) (fun k hk => principalMinorSum_of_lt hk _)
    (fun k => (principalMinorSum_nonneg_of_feasible hH k).2)
  exact ⟨h1, h2, h3, h4⟩

omit [DecidableEq c] in
theorem measurableSet_rankOf_eq {F : (Matrix c c ℂ × Matrix c c ℂ) → ℕ → ℝ}
    (hF : ∀ k, Measurable fun H => F H k) (r : ℕ) :
    MeasurableSet {H | rankOf (c := c) (F H) = r} := by
  have e : {H | rankOf (c := c) (F H) = r} = {H | r ≤ Fintype.card c ∧ (r ≠ 0 → 0 < F H r) ∧
      ∀ n, r < n → n ≤ Fintype.card c → ¬ 0 < F H n} := by
    ext H; simp only [mem_ofPred_eq, rankOf]; convert Nat.findGreatest_eq_iff using 2
  rw [e, measurableSet_setOfPred]
  have hp : ∀ k, Measurable fun H => 0 < F H k := fun k =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const (hF k))
  exact measurable_const.and ((measurable_const.imp (hp r)).and
    (Measurable.forall fun n => measurable_const.imp (measurable_const.imp (hp n).not)))

theorem measurable_stratumIdx :
    Measurable (stratumIdx (c := c)) := by
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  have : BorelSpace (Matrix c c ℂ × Matrix c c ℂ) := Prod.borelSpace
  refine measurable_to_countable' fun x => ?_
  have e : stratumIdx (c := c) ⁻¹' {x} = {H | rankB H = x.1} ∩ {H | rankC H = x.2} := by
    ext H
    simp only [mem_preimage, mem_singleton_iff, stratumIdx, mem_inter_iff, mem_ofPred_eq,
      Prod.ext_iff, Fin.ext_iff]
  rw [e]
  exact (measurableSet_rankOf_eq (fun k => (contDiff_ek_snd k).continuous.measurable) _).inter
    (measurableSet_rankOf_eq (fun k => (contDiff_ek_fst_sub_snd k).continuous.measurable) _)

end BlockBand.SourceProcess.Stochastic.GramUniqueness
