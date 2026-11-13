module

public import BlockBand.SourceProcess.ComplexUnique.SegModel
public import BlockBand.SourceProcess.ComplexUnique.SegStratum
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AssemblyStrata
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AssemblyLaw
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorOn

/-!
# The stratum facts of one model under its conditioned law

`seg_cond_facts`: conditioning on the stratum `{stratumIdx G(a) = (r, r')}` (read off the
restarted process at time `0`), the restarted process lives a.s. in `segF D r r' h` at every time
and has exact ranks `(r, r')` before `h` (`stratum_facts` at `a`, then `RankProp` from
`rank_segment`). `toR_tOf_zOf`: a real joint vector is recovered from its time and complex
coordinates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

theorem toR_tOf_zOf {κ : Type*} [Fintype κ] (y : Fin (rDim κ) → ℝ) : toR (tOf y) (zOf y) = y := by
  funext i
  obtain ⟨x, rfl⟩ := (rEquiv κ).surjective i
  rcases x with _ | q
  · simp [toR, tOf]
  · rw [toR_some, y_some y q]

variable {K : ℕ} {π : Type} [Fintype π] [DecidableEq π] {Ω : Type*} [MeasurableSpace Ω]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Matrix (SrcCol K π) (SrcCol K π) ℂ}
  {Y : ℝ≥0 → Ω → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ}
  {G : ℝ≥0 → Ω → GramState (SrcCol K π)} {Kc : ℝ≥0 → Ω → Matrix π π ℂ} {a h : ℝ≥0}

theorem seg_cond_facts (ht : ∀ ω u, tOf (Y u ω) = ((min u h : ℝ≥0) : ℝ))
    (hz : ∀ ω u, u ≤ h → zOf (Y u ω) = jvec (G (a + u) ω) (Kc (a + u) ω))
    (hf : ∀ᵐ ω ∂Q, ∀ u, GramFeasible D (G u ω))
    (hr : ∀ k, ∀ᵐ ω ∂Q, RankProp k (fun u => G (a + u) ω) (Iio h))
    (s : Fin (Fintype.card (SrcCol K π) + 1) × Fin (Fintype.card (SrcCol K π) + 1))
    (hA : MeasurableSet ((fun ω => stratumIdx (gOf (Y 0 ω))) ⁻¹' {s})) :
    (∀ u, ∀ᵐ ω ∂Q[|(fun ω => stratumIdx (gOf (Y 0 ω))) ⁻¹' {s}],
      Y u ω ∈ segF D s.1.val s.2.val h) ∧
    ∀ᵐ ω ∂Q[|(fun ω => stratumIdx (gOf (Y 0 ω))) ⁻¹' {s}], ∀ u < h,
      0 < principalMinorSum s.1.val (gOf (Y u ω)).2 ∧
        0 < principalMinorSum s.2.val ((gOf (Y u ω)).1 - (gOf (Y u ω)).2) := by
  have hg : ∀ ω u, u ≤ h → gOf (Y u ω) = G (a + u) ω := fun ω u hu => by
    simp only [gOf]; rw [hz ω u hu, gramOf_jvec]
  have hon : ∀ᵐ ω ∂Q, ω ∈ (fun ω => stratumIdx (gOf (Y 0 ω))) ⁻¹' {s} →
      principalMinorSum (s.1.val + 1) (G a ω).2 = 0 ∧ 0 < principalMinorSum s.1.val (G a ω).2 ∧
      principalMinorSum (s.2.val + 1) ((G a ω).1 - (G a ω).2) = 0 ∧
      0 < principalMinorSum s.2.val ((G a ω).1 - (G a ω).2) := by
    filter_upwards [hf] with ω hfω hω
    have hs : stratumIdx (G a ω) = s := by
      have := hω; simp only [mem_preimage, mem_singleton_iff] at this
      rwa [hg ω 0 zero_le, add_zero] at this
    have h1 : rankB (G a ω) = s.1.val := by rw [← hs]; rfl
    have h2 : rankC (G a ω) = s.2.val := by rw [← hs]; rfl
    have := stratum_facts (hfω a)
    rw [h1, h2] at this
    exact this
  refine ⟨fun u => ae_cond_of_ae_on hA ?_, ae_cond_of_ae_on hA ?_⟩
  · filter_upwards [hon, hf, hr (s.1.val + 1), hr (s.2.val + 1)] with ω h0 hfω h1 h2 hω
    by_cases hu : h ≤ u
    · left; rw [ht, min_eq_right hu]
    · push Not at hu
      right
      obtain ⟨hzB, -, hzC, -⟩ := h0 hω
      rw [hg ω u hu.le]
      refine ⟨hfω _, h1.1 (by simp only [add_zero]; assumption) u hu, h2.2.2.1 (by simp only [add_zero]; assumption) u hu⟩
  · filter_upwards [hon, hr s.1.val, hr s.2.val] with ω h0 h1 h2 hω u hu
    obtain ⟨-, hpB, -, hpC⟩ := h0 hω
    rw [hg ω u hu.le]
    exact ⟨h1.2.1 (by simp only [add_zero]; assumption) u hu, h2.2.2.2 (by simp only [add_zero]; assumption) u hu⟩

end BlockBand.SourceProcess.ComplexUnique
