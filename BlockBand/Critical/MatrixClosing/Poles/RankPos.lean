module

public import BlockBand.Critical.MatrixClosing.Boundary
public import BlockBand.Critical.MatrixClosing.Poles.Reduction

/-!
# Matrix closing: the rank-zero case and the reduction with hypothesis 1 at positive rank

* `MatrixClosingAt r`: the body of `MatrixClosingStatement` at a fixed frame rank
  (`matrixClosingStatement_iff_forall`; the statement itself is unchanged).
* **`matrixClosingAt_zero`**: at `r = 0` every value lies in the singleton
  `Fin k → Matrix (Fin 0) (Fin 0) ℂ`, so both integrals equal `Φ(0)` (probability measures).
* `matrixClosingAt_of_clauses`: at a fixed rank, from `CollarPolesAt r`, `CollarMeanClause` and
  `CollarBoundaryClause` (the contradiction argument of `matrixClosing_of_clauses` at fixed `r`).
* **`matrixClosing_of_clauses_pos (h1 : ∀ r, 0 < r → CollarPolesAt r) (h2 : CollarMeanClause)
  (hEB : ExactBoundaryMeanContract) : MatrixClosingStatement`** and its Laplace form
  `matrixClosing_of_laplace_pos`.
* `collarMeanClause_rankZero`: `CollarMeanClause` has no content at `r = 0` (no entries), so it
  needs no positivity restriction.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz

/-- `MatrixClosingStatement` at a fixed frame rank `r` (same law, quantifiers and uniformity). -/
def MatrixClosingAt (r : ℕ) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (k : ℕ) (x : Fin k → ℝ)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
    (Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))) (C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ),
    IsCanonicalCauchy r P' Ξ C →
    ∀ Φ : BoundedContinuousFunction (Fin k → Matrix (Fin r) (Fin r) ℂ) ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ (δ : ℝ) (W₀ : ℕ), 0 < δ ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ,
        ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
          matchedDistance b e X ≤ δ →
        ∀ J : Matrix (Fin 2 × Fin W) (Fin r) ℂ, Jᴴ * J = 1 →
          AEMeasurable (shiftedClosing b e x X J) (collarLaw W b) ∧
          |∫ ω, Φ (shiftedClosing b e x X J ω) ∂collarLaw W b -
              ∫ ω, Φ (fun a => C ω (x a)) ∂P'| ≤ ε

theorem matrixClosingStatement_iff_forall : MatrixClosingStatement ↔ ∀ r, MatrixClosingAt r :=
  ⟨fun h r b hb0 hb κ hκ => h b hb0 hb κ hκ r, fun h b hb0 hb κ hκ r => h r b hb0 hb κ hκ⟩

theorem fin_zero_family_eq {k : ℕ} (y z : Fin k → Matrix (Fin 0) (Fin 0) ℂ) : y = z := by
  funext a; ext i; exact Fin.elim0 i

/-- **Matrix closing at frame rank `0`**: all test values live on a singleton. -/
theorem matrixClosingAt_zero : MatrixClosingAt 0 := by
  intro b hb0 hb κ hκ k x Ω' _ P' Ξ C hC Φ ε hε
  have := hC.decorated.prob
  refine ⟨1, 0, one_pos, fun W _ _ e _ X _ _ J _ => ⟨?_, ?_⟩⟩
  · have : shiftedClosing b e x X J = fun _ => (fun _ => 0 : Fin k → Matrix (Fin 0) (Fin 0) ℂ) :=
      funext fun ω => fin_zero_family_eq _ _
    rw [this]; exact aemeasurable_const
  · have h1 : ∀ ω, Φ (shiftedClosing b e x X J ω) = Φ (fun _ => 0) :=
      fun ω => congrArg Φ (fin_zero_family_eq _ _)
    have h2 : ∀ ω, Φ (fun a => C ω (x a)) = Φ (fun _ => 0) :=
      fun ω => congrArg Φ (fin_zero_family_eq _ _)
    simp only [h1, h2, integral_const, probReal_univ, one_smul, sub_self, abs_zero]
    exact hε.le

/-- **Matrix closing at a fixed positive frame rank** from hypotheses 1 (at that rank), 2 and
3: the contradiction argument of `matrixClosing_of_clauses` at fixed `r`. -/
theorem matrixClosingAt_of_clauses {r : ℕ} (h1 : CollarPolesAt r) (h2 : CollarMeanClause)
    (h3 : CollarBoundaryClause) : MatrixClosingAt r := by
  intro b hb0 hb κ hκ k x Ω' _ P' Ξ C hC Φ ε hε
  have := hC.decorated.prob
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ W : ℕ, 0 < W ∧ n ≤ W ∧ ∃ e ∈ bulkInterval κ,
      ∃ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian ∧
        matchedDistance b e X ≤ 1 / ((n : ℝ) + 1) ∧
        ∃ J : Matrix (Fin 2 × Fin W) (Fin r) ℂ, Jᴴ * J = 1 ∧
          (AEMeasurable (shiftedClosing b e x X J) (collarLaw W b) →
            ε < |∫ ω, Φ (shiftedClosing b e x X J ω) ∂collarLaw W b -
              ∫ ω, Φ (fun a => C ω (x a)) ∂P'|) := by
    intro n
    obtain ⟨W, hW, hnW, e, he, X, hX, hd, J, hJ, hbad⟩ :=
      hcon (1 / ((n : ℝ) + 1)) n (by positivity)
    exact ⟨W, hW, hnW, e, he, X, hX, hd, J, hJ, hbad⟩
  choose W hW hnW e he X hX hd J hJ hbad using hseq
  have hdist : Tendsto (fun n => matchedDistance b (e n) (X n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) hd tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_max_of_le_left (norm_nonneg _)
  let S : OldSequence b κ r :=
    { W := W, e := e, X := X, J := J, W_pos := hW,
      tendsto_W := tendsto_atTop_mono hnW tendsto_id, e_mem := he, X_herm := hX,
      tendsto_d := hdist, J_frame := hJ }
  have hH : HerglotzTailHypotheses r (fun N => collarLaw (S.W N) b) S.collarFns P' Ξ :=
    { measurable_eval := fun N i j =>
        measurable_collarFunction_eval b (S.e N) (S.X N) (S.J N) i j
      poles := h1 b hb0 hb κ hκ S Ω' P' Ξ hC.decorated
      mean := h2 b hb0 hb κ hκ r S
      boundary := h3 b hb0 hb κ hκ r S }
  have hT := tendstoInDistribution_shiftedClosing hb hκ S hC hH x
  have hlim := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hT.forall_aemeasurable hT.aemeasurable_limit).1 hT Φ
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  have hb' := hbad N (hT.forall_aemeasurable N)
  have := hN N le_rfl
  rw [Real.dist_eq] at this
  exact absurd hb' (not_lt.2 this.le)

/-- **Matrix closing from hypothesis 1 at positive ranks, hypothesis 2 and hypothesis 3.** -/
theorem matrixClosing_of_clauses_pos' (h1 : ∀ r, 0 < r → CollarPolesAt r) (h2 : CollarMeanClause)
    (h3 : CollarBoundaryClause) : MatrixClosingStatement := by
  refine matrixClosingStatement_iff_forall.2 fun r => ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact matrixClosingAt_zero
  · exact matrixClosingAt_of_clauses (h1 r hr) h2 h3

/-- **`MatrixClosingStatement` from hypothesis 1 at positive ranks, hypothesis 2 and
`ExactBoundaryMeanContract`** (hypothesis 3 is `collarBoundaryClause_of_exactBoundaryMean`).
-/
theorem matrixClosing_of_clauses_pos (h1 : ∀ r, 0 < r → CollarPolesAt r) (h2 : CollarMeanClause)
    (hEB : ExactBoundaryMeanContract) : MatrixClosingStatement :=
  matrixClosing_of_clauses_pos' h1 h2 (Boundary.collarBoundaryClause_of_exactBoundaryMean hEB)

/-- The Laplace form at positive ranks suffices. -/
theorem matrixClosing_of_laplace_pos (h1 : ∀ r, 0 < r → CollarPolesLaplaceAt r)
    (h2 : CollarMeanClause) (hEB : ExactBoundaryMeanContract) : MatrixClosingStatement :=
  matrixClosing_of_clauses_pos (fun r hr => collarPolesAt_of_laplaceAt (h1 r hr)) h2 hEB

/-- `CollarMeanClause` at rank `0` holds trivially (no entries), so it needs no positivity
restriction. -/
theorem collarMeanClause_rankZero {b : ℝ} {κ : ℝ} (S : OldSequence b κ 0) (Y : ℝ)
    (i j : Fin 0) :
    Tendsto (fun N => ∫ ω, CoareaNative.BlockBand.matrixImaginaryPart
        ((S.collarFns N ω).eval ((Y : ℂ) * Complex.I)) i j ∂collarLaw (S.W N) b)
      atTop (𝓝 ((1 : Matrix (Fin 0) (Fin 0) ℂ) i j)) :=
  Fin.elim0 i

end BlockBand.Critical.MatrixClosing.Poles
