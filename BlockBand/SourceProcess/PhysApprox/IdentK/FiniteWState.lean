module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWTaylor
public import BlockBand.SourceProcess.PhysApprox.B3GenSplit

/-!
# The discrete state along the closed path

* `dYs`, `dKs`, `betaS`: the births-removed increments of step `j → j + 1` and their basic
  increments; **`zeta_succ`**: `zeta (j + 1) = zstep (zeta j) (dYs j) (dKs j)` for `j ≥ n_s`
  (the discrete jump of step `j` is the birth of step `j`);
* `norm_gramEntry_b3JumpAt_le`, `norm_gramEntry_gramJ_le`: both jumps are bounded by
  `CJ = Σ_i |d_* m_i|`;
* **`adm_zeta`**: the discrete states are admissible (`|G_e| ≤ Re Tr M`), constant
  `D = (|SrcCol| + 1) CJ`; `diagReal_dYs` (Hermitian closed Gram states, real births);
* at a step without a birth, the basic increments are the closed increments `b3dX`
  (`betaS_inl`, `betaS_K`, `betaS_Kc`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate

variable {W np K : ℕ}

theorem gramEntry_finset_sum {ι : Type*} (e : GIdx K np) (S : Finset ι) (X : ι → GSt K np) :
    gramEntry e (∑ i ∈ S, X i) = ∑ i ∈ S, gramEntry e (X i) := by
  unfold gramEntry
  split_ifs <;> simp [Prod.fst_sum, Prod.snd_sum, Matrix.sum_apply]

/-- The jump bound `CJ = Σ_i |d_* m_i|`. -/
def cJump (b : ℝ) (m : Fin np → ℝ) : ℝ := ∑ i, |dStar b * m i|

theorem cJump_nonneg (b : ℝ) (m : Fin np → ℝ) : 0 ≤ cJump b m :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem norm_gramEntry_sel_le (b : ℝ) (m : Fin np → ℝ) (p : Fin np → Prop) [DecidablePred p]
    (e : GIdx K np) :
    ‖gramEntry e (∑ i, if p i then
      ((((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
        ((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1) :
          GramState (SrcCol K (Fin np))) else 0)‖ ≤ cJump b m := by
  rw [gramEntry_finset_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  split_ifs with hp
  · unfold gramEntry
    split_ifs <;>
    · simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs
      · simp [Complex.norm_real]
      · simp; positivity
  · simp [gramEntry]; positivity

theorem norm_gramEntry_b3JumpAt_le (b s : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (e : GIdx K np) :
    ‖gramEntry e (b3JumpAt (K := K) b s τ m W n)‖ ≤ cJump b m := by
  rw [Fdd.b3JumpAt_eq_sum]; exact norm_gramEntry_sel_le b m _ e

theorem norm_gramEntry_gramJ_le (b s : ℝ) (τ m : Fin np → ℝ) (t : NNReal) (e : GIdx K np) :
    ‖gramEntry e (gramJ (K := K) b s τ m t)‖ ≤ cJump b m := by
  rw [Ident2.gramJ_eq_sel]; exact norm_gramEntry_sel_le b m _ e

/-!
## Increments
-/

section Path

variable (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)

/-- The births-removed Gram increment of step `j`. -/
def dYs (j : ℕ) (y : ProbedPath W np × ℝ) : GSt K np :=
  b3ClosedGramAt b E s h τ m W (j + 1) Vs y - b3ClosedGramAt b E s h τ m W j Vs y -
    b3BirthAt b τ m W j

/-- The births-removed `𝒦` increment of step `j`. -/
def dKs (j : ℕ) (y : ProbedPath W np × ℝ) : KSt np :=
  b3ClosedKAt b E s h τ m W (j + 1) y - b3ClosedKAt b E s h τ m W j y - b3KBirthAt E τ m W j

/-- The basic increments of step `j`. -/
def betaS (j : ℕ) (y : ProbedPath W np × ℝ) : BI K np → ℂ :=
  bvec (dYs b E s h τ m W Vs j y) (dKs b E s h τ m W j y)

theorem zeta_succ {j : ℕ} (hj : closeLen s W ≤ j) (y : ProbedPath W np × ℝ) :
    zeta b E s h τ m W Vs (j + 1) y =
      zstep (zeta b E s h τ m W Vs j y) (dYs b E s h τ m W Vs j y) (dKs b E s h τ m W j y) := by
  have hJ : b3JumpAt (K := K) b s τ m W (j + 1) = b3JumpAt b s τ m W j + b3BirthAt b τ m W j := by
    unfold b3JumpAt; rw [sum_Ico_succ_top hj]
  have hJK : b3KJumpAt E s τ m W (j + 1) = b3KJumpAt E s τ m W j + b3KBirthAt E τ m W j := by
    unfold b3KJumpAt; rw [sum_Ico_succ_top hj]
  simp only [zeta, zstep, dYs, dKs, hJ, hJK]
  refine Prod.ext (Prod.ext ?_ rfl) (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only; abel
  · simp only; abel
  · funext a; simp only [Matrix.sub_apply, Matrix.add_apply]; ring

/-- **The discrete states are admissible.** -/
theorem adm_zeta (j : ℕ) (y : ProbedPath W np × ℝ) :
    Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m)
      (zeta b E s h τ m W Vs j y) := by
  have hC := cJump_nonneg b m
  have hn : (0 : ℝ) ≤ Fintype.card (SrcCol K (Fin np)) := Nat.cast_nonneg _
  refine ⟨fun e => ?_, fun e => ?_, fun a => rfl⟩
  · simp only [zeta]
    have h1 := norm_gramEntry_b3ClosedGramAt_le b E s h τ m W j Vs y e
    have h2 := norm_gramEntry_b3JumpAt_le (K := K) b s τ m W j e
    have h3 := abs_trRe_le (b3JumpAt (K := K) b s τ m W j)
    have h4 : ∑ k : SrcCol K (Fin np), ‖gramEntry ((0 : Fin 2), k, k)
        (b3JumpAt (K := K) b s τ m W j)‖ ≤ (Fintype.card (SrcCol K (Fin np)) : ℝ) * cJump b m := by
      have := Finset.sum_le_card_nsmul (univ : Finset (SrcCol K (Fin np)))
        (fun k => ‖gramEntry ((0 : Fin 2), k, k) (b3JumpAt (K := K) b s τ m W j)‖) (cJump b m)
        (fun k _ => norm_gramEntry_b3JumpAt_le b s τ m W j _)
      simpa [nsmul_eq_mul] using this
    rw [gramEntry_sub', trRe_sub]
    have h5 : trRe (b3ClosedGramAt b E s h τ m W j Vs y) =
        ((b3ClosedGramAt b E s h τ m W j Vs y).1.trace).re := rfl
    refine (norm_sub_le _ _).trans ?_
    have h6 := le_abs_self (trRe (b3ClosedGramAt b E s h τ m W j Vs y) -
      trRe (b3JumpAt (K := K) b s τ m W j))
    have h7 := le_abs_self (trRe (b3JumpAt (K := K) b s τ m W j))
    linarith
  · simp only [zeta]
    have h1 := norm_gramEntry_b3ClosedGramAt_le b E s h τ m W (closeLen s W) Vs y e
    have h5 : trRe (b3ClosedGramAt b E s h τ m W (closeLen s W) Vs y) =
        ((b3ClosedGramAt b E s h τ m W (closeLen s W) Vs y).1.trace).re := rfl
    have h6 := le_abs_self (trRe (b3ClosedGramAt b E s h τ m W (closeLen s W) Vs y))
    nlinarith

theorem im_birth_diag (j : ℕ) (k : SrcCol K (Fin np)) :
    ((b3BirthAt (K := K) b τ m W j).1 k k).im = 0 := by
  simp only [b3BirthAt, Prod.fst_sum, Matrix.sum_apply, Complex.im_sum]
  refine sum_eq_zero fun i _ => ?_
  split_ifs
  · simp [Matrix.single_apply]; split_ifs <;> simp
  · simp

theorem diagReal_dYs (j : ℕ) (y : ProbedPath W np × ℝ) :
    DiagReal (dYs b E s h τ m W Vs j y) := fun k => by
  simp only [dYs, Prod.fst_sub, Matrix.sub_apply, Complex.sub_im, im_birth_diag, sub_zero]
  have h1 := im_gramEntry_diag_b3 b E s h τ m W (j + 1) Vs y 0 k
  have h2 := im_gramEntry_diag_b3 b E s h τ m W j Vs y 0 k
  simp only [gramEntry, ite_true] at h1 h2
  rw [h1, h2, sub_zero]

theorem birth_eq_zero {j : ℕ} (hj : ¬ IsBirthStep τ W j) :
    b3BirthAt (K := K) b τ m W j = 0 ∧ b3KBirthAt E τ m W j = 0 := by
  unfold IsBirthStep at hj
  push Not at hj
  constructor
  · unfold b3BirthAt; exact sum_eq_zero fun i _ => by simp [hj i]
  · unfold b3KBirthAt; exact sum_eq_zero fun i _ => by simp [hj i]

theorem betaS_inl {j : ℕ} (hj : ¬ IsBirthStep τ W j) (y : ProbedPath W np × ℝ)
    (e : GIdx K np) :
    betaS b E s h τ m W Vs j y (Sum.inl e) = b3dX b E s h τ m W j Vs (Sum.inl e) y := by
  simp [betaS, bvec, dYs, (birth_eq_zero b E τ m W hj).1, b3dX, b3X, cEntry, gramEntry_sub']

theorem betaS_K {j : ℕ} (hj : ¬ IsBirthStep τ W j) (y : ProbedPath W np × ℝ) (a : KIdx np) :
    betaS b E s h τ m W Vs j y (Sum.inr (Sum.inl a)) = b3dX b E s h τ m W j Vs (Sum.inr a) y := by
  simp [betaS, bvec, dKs, (birth_eq_zero (K := K) b E τ m W hj).2, b3dX, b3X, cEntry]

theorem betaS_Kc {j : ℕ} (hj : ¬ IsBirthStep τ W j) (y : ProbedPath W np × ℝ) (a : KIdx np) :
    betaS b E s h τ m W Vs j y (Sum.inr (Sum.inr a)) =
      conj (b3dX b E s h τ m W j Vs (Sum.inr a) y) := by
  simp [betaS, bvec, dKs, (birth_eq_zero (K := K) b E τ m W hj).2, b3dX, b3X, cEntry]

/-- At a birth step, the basic increments are the birth errors of `ComplexClosedSummed`. -/
theorem betaS_inl_birth (j : ℕ) (y : ProbedPath W np × ℝ) (e : GIdx K np) :
    betaS b E s h τ m W Vs j y (Sum.inl e) = b3dX b E s h τ m W j Vs (Sum.inl e) y -
      cEntry (Sum.inl e) (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j) := by
  simp [betaS, bvec, dYs, b3dX, b3X, cEntry, gramEntry_sub']

theorem betaS_K_birth (j : ℕ) (y : ProbedPath W np × ℝ) (a : KIdx np) :
    betaS b E s h τ m W Vs j y (Sum.inr (Sum.inl a)) = b3dX b E s h τ m W j Vs (Sum.inr a) y -
      cEntry (Sum.inr a) (b3BirthAt (K := K) b τ m W j) (b3KBirthAt E τ m W j) := by
  simp [betaS, bvec, dKs, b3dX, b3X, cEntry]

theorem betaS_Kc_birth (j : ℕ) (y : ProbedPath W np × ℝ) (a : KIdx np) :
    betaS b E s h τ m W Vs j y (Sum.inr (Sum.inr a)) = conj (b3dX b E s h τ m W j Vs (Sum.inr a) y -
      cEntry (Sum.inr a) (b3BirthAt (K := K) b τ m W j) (b3KBirthAt E τ m W j)) := by
  simp [betaS, bvec, dKs, b3dX, b3X, cEntry]

/-- Hermitian symmetry of a step without a birth: `conj dG_e = dG_{e*}`. -/
theorem conj_b3dX_inl (j : ℕ) (y : ProbedPath W np × ℝ) (e : GIdx K np) :
    conj (b3dX b E s h τ m W j Vs (Sum.inl e) y) =
      b3dX b E s h τ m W j Vs (Sum.inl (eStar e)) y := by
  simp only [b3dX, b3X, cEntry, map_sub, conj_gramEntry_b3]

end Path

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
