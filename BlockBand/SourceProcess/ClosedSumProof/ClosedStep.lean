module

public import BlockBand.SourceProcess.ClosedSumProof.Events
public import BlockBand.SourceProcess.ClosedSumProof.GramBound
public import BlockBand.SourceProcess.ClosedSumProof.StepCond
public import BlockBand.SourceProcess.ClosedSumProof.ModAbstract

/-!
# The steps of one real coordinate of the closed Gram process

On a window `j₁ ≤ j < j₁ + L` and for a unit phase `u`, the real coordinate
`X_k = Re(u (G_e - J_e)(j₁ + min(k, L)))` (`procX`; `J` = `closedJump`, the model births) has
steps `d_k = 1_{A_j} Re(uΔG_e)` (`dInc`, `A_j = aliveM ∩ noBirth`) up to the birth errors
`β_k` (`betaErr`, the integrand of the third sum of `ClosedSummed`): **`procX_step`**. The
conditional drift and variance of `d_k` are bounded by `W⁻¹C_b(R) + g_k`, `W⁻¹C_c(R) + f_k`
(`dInc_drift`, `dInc_var`, proved in the sibling module `ClosedCond`), `g_k, f_k` the drift and bracket integrands of
`ClosedSummed` (bracket with `(e, swapE e)`), given the fourth moment of the step.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum

variable {W p K M : ℕ}

theorem gramEntry_sub {c : Type*} (e : Fin 2 × c × c) (X Y : GramState c) :
    gramEntry e (X - Y) = gramEntry e X - gramEntry e Y := by
  unfold gramEntry; split_ifs <;> rfl

theorem gramEntry_add {c : Type*} (e : Fin 2 × c × c) (X Y : GramState c) :
    gramEntry e (X + Y) = gramEntry e X + gramEntry e Y := by
  unfold gramEntry; split_ifs <;> rfl

theorem measurable_gramEntry {c : Type*} (e : Fin 2 × c × c) :
    Measurable (gramEntry e : GramState c → ℂ) := by
  unfold gramEntry; split_ifs
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)

theorem closedJump_succ (b s T : ℝ) (q : Fin p → ℝ → ℝ) {j : ℕ} (hj : closeLen s W ≤ j)
    (y : SampledPath W p M × ℝ) :
    closedJump (K := K) b s T q W (j + 1) y = closedJump b s T q W j y + birthAt b s T q j y := by
  unfold closedJump; rw [Finset.sum_Ico_succ_top hj]

theorem birthAt_of_noBirth (b s T : ℝ) (q : Fin p → ℝ → ℝ) {j : ℕ} {y : SampledPath W p M × ℝ}
    (hy : y ∈ noBirth j) : birthAt (K := K) b s T q j y = 0 :=
  Finset.sum_eq_zero fun il _ => ite_eq_right (hy il)

/-- The common level `ρ = |cols|² max(R, 0)` bounding `l1 M, l1 B` before the stop. -/
def rhoR (K p M : ℕ) (R : ℝ) : ℝ := (Fintype.card (SrcCol K (Fin p × Fin M)) : ℝ) ^ 2 * max R 0

/-- The drift constant `C_b(R)`. -/
def driftC (b E : ℝ) (K p M : ℕ) (R : ℝ) : ℝ :=
  |transportD0 b E| * (l1 (srcSignature K (Fin p × Fin M)) * rhoR K p M R) ^ 2 * rhoR K p M R

/-- The bracket constant `C_c(R)`. -/
def covC (b E : ℝ) (K p M : ℕ) (R : ℝ) : ℝ :=
  |transportD0 b E| * rhoR K p M R * (rhoR K p M R +
    rhoR K p M R * l1 (srcSignature K (Fin p × Fin M)) * rhoR K p M R)

theorem rhoR_nonneg (K p M : ℕ) (R : ℝ) : 0 ≤ rhoR K p M R := by unfold rhoR; positivity

theorem driftC_nonneg (b E : ℝ) (K p M : ℕ) (R : ℝ) : 0 ≤ driftC b E K p M R := by
  have := rhoR_nonneg K p M R; have := l1_nonneg (srcSignature K (Fin p × Fin M))
  unfold driftC; positivity

theorem covC_nonneg (b E : ℝ) (K p M : ℕ) (R : ℝ) : 0 ≤ covC b E K p M R := by
  have := rhoR_nonneg K p M R; have := l1_nonneg (srcSignature K (Fin p × Fin M))
  unfold covC; positivity

section Window

variable (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
  (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M))

/-- The closed Gram coordinate `G_e(j)`. -/
def zc (j : ℕ) (y : SampledPath W p M × ℝ) : ℂ := gramEntry e (closedGramAt b E s T h q W j Vs y)

/-- Alive and no birth at step `j` (Borel cap). -/
def am (j : ℕ) : Set (SampledPath W p M × ℝ) := aliveM b E s T h q R W j Vs ∩ noBirth j

/-- Alive and a birth at step `j` (Borel cap). -/
def bm (j : ℕ) : Set (SampledPath W p M × ℝ) := aliveM b E s T h q R W j Vs \ noBirth j

/-- The real coordinate `Re(u (G_e - J_e))` along the window, stopped after `L` steps. -/
def procX (u : ℂ) (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) : ℝ :=
  reMul u (zc b E s T h q W Vs e (j₁ + min k L) y -
    gramEntry e (closedJump b s T q W (j₁ + min k L) y))

/-- The martingale-type step `1_{A_j} Re(uΔG_e)`, `j = j₁ + k`, zero after the window. -/
def dInc (u : ℂ) (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) : ℝ :=
  if k < L then (am b E s T h q R W Vs (j₁ + k)).indicator (fun y => reMul u
    (zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y)) y else 0

/-- The birth error at step `j₁ + k` (third integrand of `ClosedSummed`, Borel cap). -/
def betaErr (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) : ℝ :=
  if k < L then ‖(bm b E s T h q R W Vs (j₁ + k)).indicator (fun y => gramEntry e
    (closedGramAt b E s T h q W (j₁ + k + 1) Vs y - closedGramAt b E s T h q W (j₁ + k) Vs y -
      birthAt b s T q (j₁ + k) y)) y‖ else 0

theorem betaErr_nonneg (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) :
    0 ≤ betaErr b E s T h q R W Vs e j₁ L k y := by
  unfold betaErr; split_ifs <;> simp

/-- **One step of the coordinate**: on the alive event at the window end, `|ΔX_k - d_k| ≤ β_k`. -/
theorem procX_step {j₁ L : ℕ} (hj₁ : closeLen s W ≤ j₁) {u : ℂ} (hu : ‖u‖ = 1)
    {y : SampledPath W p M × ℝ} (hy : y ∈ aliveM b E s T h q R W (j₁ + L) Vs) (k : ℕ) :
    |procX b E s T h q W Vs e u j₁ L (k + 1) y - procX b E s T h q W Vs e u j₁ L k y -
      dInc b E s T h q R W Vs e u j₁ L k y| ≤ betaErr b E s T h q R W Vs e j₁ L k y := by
  by_cases hk : k < L
  · have hm1 : min (k + 1) L = k + 1 := min_eq_left hk
    have hm0 : min k L = k := min_eq_left hk.le
    have hyj : y ∈ aliveM b E s T h q R W (j₁ + k) Vs :=
      ⟨hy.1, fun i hi1 hi2 => hy.2 i hi1 (by omega)⟩
    simp only [procX, dInc, betaErr, ite_eq_left hk, hm1, hm0, ← add_assoc]
    rw [closedJump_succ b s T q (by omega : closeLen s W ≤ j₁ + k), gramEntry_add,
      ← map_sub]
    by_cases hb : y ∈ noBirth (j₁ + k)
    · rw [Set.indicator_of_mem (show y ∈ am b E s T h q R W Vs (j₁ + k) from ⟨hyj, hb⟩),
        birthAt_of_noBirth b s T q hb, show gramEntry e (0 : GramState _) = 0 from by
          unfold gramEntry; split_ifs <;> rfl, ← map_sub]
      have : zc b E s T h q W Vs e (j₁ + k + 1) y - (gramEntry e (closedJump b s T q W (j₁ + k) y) + 0) -
          (zc b E s T h q W Vs e (j₁ + k) y - gramEntry e (closedJump b s T q W (j₁ + k) y)) -
          (zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) = 0 := by ring
      rw [this, map_zero, abs_zero]; exact norm_nonneg _
    · rw [Set.indicator_of_notMem (show y ∉ am b E s T h q R W Vs (j₁ + k) from fun h => hb h.2),
        Set.indicator_of_mem (show y ∈ bm b E s T h q R W Vs (j₁ + k) from ⟨hyj, hb⟩), sub_zero,
        gramEntry_sub, gramEntry_sub]
      refine le_of_eq_of_le ?_ (abs_reMul_le hu _)
      congr 2; simp only [zc]; ring
  · have hm1 : min (k + 1) L = L := min_eq_right (by omega)
    have hm0 : min k L = L := min_eq_right (by omega)
    simp only [procX, dInc, betaErr, ite_eq_right hk, hm1, hm0, sub_self, abs_zero, le_refl]

end Window

end BlockBand.SourceProcess.ClosedSumProof
