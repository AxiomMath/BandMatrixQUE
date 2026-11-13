module

public import BlockBand.SourceProcess.ComplexUnique.Coeffs

/-!
# The joint clauses as a localized complex martingale problem

`isCLocSol_of_joint` (proved in the sibling module `ClausesMain`): a born Gram solution (`IsBornGramSolution`)
with deterministic Hermitian jumps `J` and a complex source extension
(`IsComplexSourceExtension`) with deterministic jumps `JK` give a
localized complex martingale problem (`IsCLocSol`) for the joint coordinates
`X = jvec (G - J) (𝒦 - J_𝒦)` with jumps `jvec J J_𝒦`, coefficients `jβ`, `jΓ`, `jΓ'` and
localization by the trace stops `gramTraceStop G L`. The sesquilinear Gram clauses come from
the bilinear ones by Hermitian symmetry (`star_bornCompensated`); the Gram–`\bar𝒦` clauses are
conjugates of the `𝒦`–`\bar G` clauses. This file defines the joint coordinates `jX`, `jc` and
proves the auxiliary facts (`jX_add_jc`, `lComp_inl`, `lComp_inr`, `star_bornCompensated`,
`rawHit_le_gramTraceStop`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set ComplexConjugate
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal

variable {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {Ω : Type*} [MeasurableSpace Ω]
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 η : ℝ}
  {D : Matrix (SrcCol K π) (SrcCol K π) ℂ} {J : ℝ≥0 → GramState (SrcCol K π)}
  {JK : ℝ≥0 → Matrix π π ℂ} {G : ℝ≥0 → Ω → GramState (SrcCol K π)}
  {Kc : ℝ≥0 → Ω → Matrix π π ℂ}

/-- The joint continuous part. -/
def jX (G : ℝ≥0 → Ω → GramState (SrcCol K π)) (J : ℝ≥0 → GramState (SrcCol K π))
    (Kc : ℝ≥0 → Ω → Matrix π π ℂ) (JK : ℝ≥0 → Matrix π π ℂ) :
    ℝ≥0 → Ω → JIdx (SrcCol K π) π → ℂ :=
  fun t ω => jvec (G t ω - J t) (Kc t ω - JK t)

/-- The joint jumps. -/
def jc (J : ℝ≥0 → GramState (SrcCol K π)) (JK : ℝ≥0 → Matrix π π ℂ) :
    ℝ≥0 → JIdx (SrcCol K π) π → ℂ :=
  fun t => jvec (J t) (JK t)

omit [Fintype π] [DecidableEq π] [MeasurableSpace Ω] in
theorem jX_add_jc (t : ℝ≥0) (ω : Ω) :
    jX G J Kc JK t ω + jc J JK t = jvec (G t ω) (Kc t ω) := jvec_sub_add _ _ _ _

omit [MeasurableSpace Ω] in
theorem lComp_inl (e : Fin 2 × SrcCol K π × SrcCol K π) :
    lComp (jβ D0 D) (jc J JK) (jX G J Kc JK) (Sum.inl e) =
      bornCompensated D0 D G (fun t _ => J t) e := by
  funext t ω
  unfold lComp bornCompensated
  simp only [jX_add_jc, jβ, Sum.elim_inl, gramOf_jvec]
  rfl

omit [DecidableEq π] [MeasurableSpace Ω] in
theorem lComp_inr (q : π × π) :
    lComp (jβ D0 D) (jc J JK) (jX G J Kc JK) (Sum.inr q) =
      kCompensated Kc (fun t _ => JK t) q.1 q.2 := by
  funext t ω
  simp only [lComp, kCompensated, jβ, Sum.elim_inr, integral_zero, sub_zero, jX, jvec]

omit [Fintype π] [DecidableEq π] in
theorem herm_sub {A B : Matrix (SrcCol K π) (SrcCol K π) ℂ × Matrix (SrcCol K π) (SrcCol K π) ℂ}
    (hA : A.1ᴴ = A.1 ∧ A.2ᴴ = A.2) (hB : B.1ᴴ = B.1 ∧ B.2ᴴ = B.2) :
    (A - B).1ᴴ = (A - B).1 ∧ (A - B).2ᴴ = (A - B).2 := by
  simp only [Prod.fst_sub, Prod.snd_sub, conjTranspose_sub, hA.1, hA.2, hB.1, hB.2, and_self]

omit [MeasurableSpace Ω] in
theorem star_bornCompensated (hD : Dᴴ = D) (hJ : ∀ t, (J t).1ᴴ = (J t).1 ∧ (J t).2ᴴ = (J t).2)
    {ω : Ω} (hf : ∀ s, (G s ω).1ᴴ = (G s ω).1 ∧ (G s ω).2ᴴ = (G s ω).2)
    (e : Fin 2 × SrcCol K π × SrcCol K π) (t : ℝ≥0) :
    star (bornCompensated D0 D G (fun t _ => J t) e t ω) =
      bornCompensated D0 D G (fun t _ => J t) (gramSwap e) t ω := by
  unfold bornCompensated
  rw [star_sub, star_sub, star_gramEntry_of_herm (herm_sub (hf t) (hJ t)).1 (herm_sub (hf t) (hJ t)).2,
    star_gramEntry_of_herm (herm_sub (hf 0) (hJ 0)).1 (herm_sub (hf 0) (hJ 0)).2]
  congr 1
  rw [Complex.star_def, ← integral_conj]
  congr 1
  funext s
  rw [← Complex.star_def, star_gramDriftEntry hD (hf _).1 (hf _).2]

omit [DecidableEq π] [MeasurableSpace Ω] in
/-- The trace stop dominates the hit of `{‖x‖ ≥ k}` by the joint continuous part. -/
theorem rawHit_le_gramTraceStop {CJ : ℝ} (hCJ : ∀ t, ‖jc J JK t‖ ≤ CJ) (k : ℕ) {ω : Ω}
    (hx : Continuous fun t => jX G J Kc JK t ω) :
    rawHit {x : JIdx (SrcCol K π) π → ℂ | (k : ℝ) ≤ ‖x‖} (jX G J Kc JK) ω ≤
      gramTraceStop G (Fintype.card (SrcCol K π) * (k + CJ) + 1) ω := by
  rw [rawHit_eq_hitTime (isClosed_normGe _) hx]
  refine le_iInf₂ fun t ht => iInf₂_le t ?_
  by_contra hk
  simp only [mem_ofPred_eq, not_le] at hk
  have hi : ∀ i, ((G t ω).1 i i).re ≤ k + CJ := fun i => by
    have e : (G t ω).1 i i = (jX G J Kc JK t ω + jc J JK t) (Sum.inl (0, i, i)) := by
      rw [jX_add_jc]; simp [jvec, gramEntry]
    rw [e]
    refine (Complex.re_le_norm _).trans ((norm_le_pi_norm _ _).trans ((norm_add_le _ _).trans
      (add_le_add hk.le (hCJ t))))
  have htr : ((G t ω).1.trace).re ≤ Fintype.card (SrcCol K π) * (k + CJ) := by
    rw [Matrix.trace, Complex.re_sum]
    calc ∑ i, ((G t ω).1 i i).re ≤ ∑ _i : SrcCol K π, ((k : ℝ) + CJ) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith

end BlockBand.SourceProcess.ComplexUnique
