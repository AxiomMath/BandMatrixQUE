module

public import BlockBand.Critical.MatrixClosing.Clauses
public import BlockBand.Critical.Herglotz.Main
public import BlockBand.Layers.MatchedScalar

/-!
# Matrix closing: reduction to the three collar clauses

The matrix closing theorem follows from the three hypotheses of the Herglotz tail lemma for the
collar function, by a contradiction argument along a violating old deterministic sequence.

* `boundaryZ_im_pos`, `semicircleDensity_pos`, `poleScale_pos`: positivity facts in the bulk.
* `tendstoInDistribution_shiftedClosing`: along an old sequence, the hypotheses of the Herglotz
  tail lemma for `F_{W_n}` give `(closingMatrix at x_a/(Wρ))_a ⇒ (𝖢_r(x_a))_a`
  (`herglotzTail` and the almost sure identification `ae_collarFunction_eval_eq`).
* `matrixClosing_of_clauses`: `MatrixClosingStatement` from `CollarPolesClause`,
  `CollarMeanClause` and `CollarBoundaryClause`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz

/-!
## Bulk facts
-/

theorem boundaryZ_im_pos {b κ e : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    0 < (boundaryZ b e).im := by
  obtain ⟨h1, h2⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith)
    hκ he
  exact h1.trans_le h2

theorem semicircleDensity_pos {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    0 < Parameters.semicircleDensity e := by
  have h := BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he
  have h4 : 0 < 4 - e ^ 2 := by
    have : e ^ 2 < 4 := by
      have := sq_abs e
      nlinarith [abs_nonneg e]
    linarith
  unfold Parameters.semicircleDensity
  exact div_pos (Real.sqrt_pos.2 h4) (by positivity)

theorem poleScale_pos {κ e : ℝ} {W : ℕ} (hW : 0 < W) (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    0 < poleScale W e :=
  mul_pos (by exact_mod_cast hW) (semicircleDensity_pos hκ he)

/-!
## The reduction
-/

/-- Along an old sequence, the joint middle-shifted closing family converges in law to
`(𝖢_r(x_a))_a`, given the hypotheses of the Herglotz tail lemma for `F_{W_n}`. -/
theorem tendstoInDistribution_shiftedClosing {b : ℝ} (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {r : ℕ} (S : OldSequence b κ r) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    {C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ} (hC : IsCanonicalCauchy r P' Ξ C)
    (hH : HerglotzTailHypotheses r (fun N => collarLaw (S.W N) b) S.collarFns P' Ξ)
    {k : ℕ} (x : Fin k → ℝ) :
    TendstoInDistribution (fun N => shiftedClosing b (S.e N) x (S.X N) (S.J N)) atTop
      (fun ω a => C ω (x a)) (fun N => collarLaw (S.W N) b) P' := by
  have hT := herglotzTail r (fun N => CollarSample (S.W N)) (fun N => collarLaw (S.W N) b)
    S.collarFns Ω' P' Ξ C hC hH k x ∅ isCompact_empty (Set.empty_subset _)
  have hg : Continuous fun p : JointValues r k ∅ => p.1 :=
    continuous_fst (X := Fin k → Matrix (Fin r) (Fin r) ℂ)
      (Y := C((∅ : Set ℂ), Matrix (Fin r) (Fin r) ℂ))
  have h0 := hT.continuous_comp hg
  have hae : ∀ N, (fun ω => (fun p : JointValues r k ∅ => p.1)
      (jointValues (S.collarFns N ω).eval x ∅)) =ᵐ[collarLaw (S.W N) b]
        shiftedClosing b (S.e N) x (S.X N) (S.J N) := by
    intro N
    have hη := boundaryZ_im_pos hb hκ (S.e_mem N)
    have hc := poleScale_pos (S.W_pos N) hκ (S.e_mem N)
    have hall : ∀ᵐ ω ∂collarLaw (S.W N) b, ∀ a : Fin k,
        (S.collarFns N ω).eval (x a) =
          closingMatrix b (S.e N) (microShift (S.W N) (S.e N) (x a)) (S.X N) (S.J N) ω := by
      rw [ae_all_iff]
      intro a
      exact ae_collarFunction_eval_eq hb (S.W_pos N) (S.e N) hη hc (S.X_herm N) (S.J N) (x a)
    filter_upwards [hall] with ω hω
    funext a
    exact hω a
  refine ⟨fun N => ((h0.forall_aemeasurable N).congr (hae N)), h0.aemeasurable_limit, ?_⟩
  have hmap : ∀ N, (collarLaw (S.W N) b).map (shiftedClosing b (S.e N) x (S.X N) (S.J N)) =
      (collarLaw (S.W N) b).map ((fun p : JointValues r k ∅ => p.1) ∘
        fun ω => jointValues (S.collarFns N ω).eval x ∅) :=
    fun N => (Measure.map_congr (hae N)).symm
  have h1 := h0.tendsto
  simp only [← hmap] at h1
  exact h1

/-- **The matrix closing theorem from the three hypotheses of the Herglotz tail lemma for the
collar function.** If the comparison failed uniformly, one would extract an old deterministic
sequence violating it; along that sequence the three clauses give the hypotheses of
`herglotzTail`, so the closing family converges in law (`tendstoInDistribution_shiftedClosing`),
a contradiction. -/
theorem matrixClosing_of_clauses (h1 : CollarPolesClause) (h2 : CollarMeanClause)
    (h3 : CollarBoundaryClause) : MatrixClosingStatement := by
  intro b hb0 hb κ hκ r k x Ω' _ P' Ξ C hC Φ ε hε
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
  have hH := herglotzTailHypotheses_of_clauses h1 h2 h3 hb0 hb hκ S hC.decorated
  have hT := tendstoInDistribution_shiftedClosing hb hκ S hC hH x
  have hlim := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hT.forall_aemeasurable hT.aemeasurable_limit).1 hT Φ
  have hev := (Metric.tendsto_atTop.1 hlim) ε hε
  obtain ⟨N, hN⟩ := hev
  have hb' := hbad N (hT.forall_aemeasurable N)
  have := hN N le_rfl
  rw [Real.dist_eq] at this
  exact absurd hb' (not_lt.2 this.le)

end BlockBand.Critical.MatrixClosing
