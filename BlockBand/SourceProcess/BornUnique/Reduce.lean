module

public import BlockBand.SourceProcess.BornUnique.Data

/-!
# `ModelUnique` from `BornGramLawUnique`

Every finite source model is a born Gram solution with probe births as jumps, and the joint law of
its birth times and initial Gram state is fixed by the parameters. Hence uniqueness of the born
Gram law gives `ModelUnique` (`modelUnique_of_bornGramLawUnique`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

theorem transportD0_pos' {b E : ℝ} (hb : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) :
    0 < transportD0 b E := by
  unfold transportD0
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem isSignature_srcSignature (K : ℕ) (π : Type*) [Fintype π] [DecidableEq π] :
    IsSignature (srcSignature K π) := by
  refine ⟨?_, ?_⟩
  · rw [srcSignature, Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    rcases x with ⟨_, σ⟩ | _
    · by_cases hσ : σ = 0 <;> simp [hσ]
    · simp
  · rw [srcSignature, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    rcases x with ⟨_, σ⟩ | _
    · by_cases hσ : σ = 0 <;> simp [hσ]
    · simp

theorem measurable_sub_const_pi {Ω F : Type*} [MeasurableSpace Ω] {τ : Ω → F → ℝ}
    (hτ : Measurable τ) (s : ℝ) : Measurable fun ω i => τ ω i - s :=
  measurable_pi_iff.2 fun i => (measurable_pi_iff.1 hτ i).sub_const s

/-- The Gram jump of the probe birth `i` with squared norm `v_i` (as in `birthJump`). -/
def probeJump {K : ℕ} {π : Type*} [DecidableEq π] (v : π → ℝ) (i : π) :
    GramState (SrcCol K π) :=
  (((v i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
    ((v i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1)

theorem birthJump_eq_birthSum {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π] (τ v : π → ℝ)
    (t : ℝ) : birthJump (K := K) τ v t = birthSum (probeJump v) τ t :=
  rfl

/-- **`ModelUnique` from `BornGramLawUnique`.** -/
theorem modelUnique_of_bornGramLawUnique (hB : BornGramLawUnique) : ModelUnique := by
  intro b hb0 _ E hE1 hE2 s T _ _ p q _ entrance h K M _ _ Ω m 𝓖 Q tseq τ G hM
    Ω' m' 𝓖' Q' tseq' τ' G' hM' t
  exact hB (SrcCol K (Fin p × Fin M)) (Fin p × Fin M) (transportD0 b E)
    (srcSignature K (Fin p × Fin M)) (transportD0_pos' hb0 hE1 hE2)
    (isSignature_srcSignature K _) (probeJump fun i => dStar b * sourceMass s T (q i.1) / M)
    Ω m 𝓖 Q (fun ω i => τ ω i - s) G hM.prob
    (@measurable_sub_const_pi _ _ (𝓖 0) _ hM.births_measurable s)
    hM.solution Ω' m' 𝓖' Q' (fun ω i => τ' ω i - s) G' hM'.prob
    (@measurable_sub_const_pi _ _ (𝓖' 0) _ hM'.births_measurable s)
    hM'.solution (by rw [model_map_initial hM, model_map_initial hM']) t

end BlockBand.SourceProcess.BornUnique
