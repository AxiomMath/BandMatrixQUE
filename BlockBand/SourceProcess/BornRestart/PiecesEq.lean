module

public import BlockBand.SourceProcess.BornRestart.Pieces

/-!
# The piece stop is the trace stop on every born path

On every path for which `Y - J` is continuous, the stopping time defined piece by piece agrees
with the trace stopping time `gramTraceStop` (`pieceStop_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal

/-- The infimum of a closed condition on a right-continuous function is attained. -/
theorem exists_attained {φ : ℝ≥0 → ℝ} (hφ : ∀ t, ContinuousWithinAt φ (Ici t) t) {K : ℝ}
    (h : (⨅ (t : ℝ≥0) (_ : K ≤ φ t), (t : WithTop ℝ≥0)) ≠ ⊤) :
    ∃ t₀ : ℝ≥0, (⨅ (t : ℝ≥0) (_ : K ≤ φ t), (t : WithTop ℝ≥0)) = t₀ ∧ K ≤ φ t₀ := by
  have hS : ({t | K ≤ φ t} : Set ℝ≥0).Nonempty := by
    by_contra hS
    exact h (iInf₂_eq_top.2 fun t ht => absurd ⟨t, ht⟩ hS)
  have hbdd : BddBelow ({t | K ≤ φ t} : Set ℝ≥0) := OrderBot.bddBelow _
  have hmem : K ≤ φ (sInf {t | K ≤ φ t}) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
      ((hφ _).eventually (eventually_lt_nhds hlt))
    have hle : u ≤ sInf {t | K ≤ φ t} := le_csInf hS fun t ht => by
      by_contra h'
      rw [not_le] at h'
      exact absurd ht (not_le.2 (hsub ⟨csInf_le hbdd ht, h'⟩))
    exact absurd hle (not_le.2 hu)
  exact ⟨_, le_antisymm
    (iInf₂_le (f := fun (t : ℝ≥0) (_ : K ≤ φ t) => (t : WithTop ℝ≥0)) _ hmem)
    (le_iInf₂ fun t ht => WithTop.coe_le_coe.2 (csInf_le hbdd ht)), hmem⟩

variable {c F : Type} [Fintype c] [Fintype F] {Ω : Type*} {j : F → GramState c}
  {Y : ℝ≥0 → Ω → GramState c} {b : Ω → F → ℝ} {ω : Ω}

/-- The trace of a born path is right-continuous. -/
theorem continuousWithinAt_trace (hc : Continuous fun u => Y u ω - birthSum j (b ω) (u : ℝ))
    (t : ℝ≥0) : ContinuousWithinAt (fun u => ((Y u ω).1.trace).re) (Ici t) t := by
  have hJ : ∀ᶠ u : ℝ≥0 in 𝓝[≥] t, birthSum j (b ω) (u : ℝ) = birthSum j (b ω) (t : ℝ) :=
    ((NNReal.continuous_coe.continuousWithinAt (s := Ici t) (x := t)).tendsto_nhdsWithin
      (t := Ici (t : ℝ)) (fun x hx => NNReal.coe_le_coe.2 hx)).eventually
      (birthSum_eventually_eq j (b ω) t)
  have hJc : ContinuousWithinAt (fun u : ℝ≥0 => birthSum j (b ω) (u : ℝ)) (Ici t) t :=
    continuousWithinAt_const.congr_of_eventuallyEq hJ rfl
  have hY : ContinuousWithinAt (fun u => Y u ω) (Ici t) t :=
    (hc.continuousWithinAt.add hJc).congr (fun u _ => (sub_add_cancel _ _).symm)
      (sub_add_cancel _ _).symm
  exact (Complex.continuous_re.comp (continuous_fst.matrix_trace)).continuousAt.comp_continuousWithinAt
    hY

theorem continuous_pieceProc (hc : Continuous fun u => Y u ω - birthSum j (b ω) (u : ℝ))
    (f₀ : Option F) (k : ℕ) : Continuous fun u => pieceProc j Y b f₀ k u ω := by
  unfold pieceProc
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (continuous_pi fun g => ?_))
  · exact Complex.continuous_re.comp ((continuous_fst.comp (hc.add continuous_const)).matrix_trace)
  · exact NNReal.continuous_coe.sub continuous_const
  · split_ifs
    · exact (continuous_const.sub NNReal.continuous_coe).sub continuous_const
    · exact continuous_const

/-- **The piece stop is the trace stop** on every path with continuous `Y - J`. -/
theorem pieceStop_eq (hc : Continuous fun u => Y u ω - birthSum j (b ω) (u : ℝ)) (K : ℝ) :
    pieceStop j Y b K ω = gramTraceStop Y K ω := by
  set B := b ω
  have hcl := isClosed_pieceSet (F := F) K
  refine le_antisymm ?_ (le_iInf fun f₀ => le_iInf fun k => ?_)
  · by_cases htop : gramTraceStop Y K ω = ⊤
    · rw [htop]; exact le_top
    obtain ⟨t₀, ht₀, hK⟩ := exists_attained (continuousWithinAt_trace hc) htop
    obtain ⟨f₀, hs, hno⟩ : ∃ f₀ : Option F, pieceStart B f₀ ≤ t₀ ∧
        ∀ g, B g ≤ pieceStart B f₀ ∨ (t₀ : ℝ) < B g := by
      by_cases hne : (Finset.univ.filter fun f => B f ≤ t₀).Nonempty
      · obtain ⟨f₀, hf₀, hmax⟩ := Finset.exists_max_image _ B hne
        refine ⟨some f₀, max_le (Finset.mem_filter.1 hf₀).2 t₀.coe_nonneg, fun g => ?_⟩
        by_cases hg : B g ≤ t₀
        · exact Or.inl ((hmax g (Finset.mem_filter.2 ⟨Finset.mem_univ g, hg⟩)).trans
            (le_max_left _ _))
        · exact Or.inr (not_le.1 hg)
      · refine ⟨none, t₀.coe_nonneg, fun g => Or.inr (not_le.1 fun hg => hne ⟨g, ?_⟩)⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_univ g, hg⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ g, pieceStart B f₀ < B g → (t₀ : ℝ) + 1 / ((k : ℝ) + 1) ≤ B g := by
      have : ∀ g, ∀ᶠ k : ℕ in atTop,
          pieceStart B f₀ < B g → (t₀ : ℝ) + 1 / ((k : ℝ) + 1) ≤ B g := fun g => by
        by_cases hg : pieceStart B f₀ < B g
        · have ht : (t₀ : ℝ) < B g := (hno g).resolve_left (not_le.2 hg)
          filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
            (eventually_le_nhds (sub_pos.2 ht))] with k hk _
          linarith
        · exact Eventually.of_forall fun _ h => absurd h hg
      exact (eventually_all.2 this).exists
    have hJ := birthSum_eq_of_no_birth j B hs hno
    have hmem : pieceProc j Y b f₀ k t₀ ω ∈ pieceSet K := by
      refine mem_pieceSet.2 ⟨?_, sub_nonneg.2 hs, fun g => ?_⟩
      · show K ≤ ((Y t₀ ω - birthSum j B (t₀ : ℝ) + birthSum j B (pieceStart B f₀)).1.trace).re
        rw [hJ, sub_add_cancel]
        exact hK
      · show 0 ≤ if pieceStart B f₀ < B g then B g - t₀ - 1 / ((k : ℝ) + 1) else 1
        split_ifs with hg
        · linarith [hk g hg]
        · exact zero_le_one
    rw [show gramTraceStop Y K ω = (t₀ : WithTop ℝ≥0) from ht₀]
    refine (iInf₂_le f₀ k).trans ?_
    rw [rawHit_eq_hitTime hcl (continuous_pieceProc hc f₀ k)]
    exact iInf₂_le t₀ hmem
  · rw [rawHit_eq_hitTime hcl (continuous_pieceProc hc f₀ k)]
    refine le_iInf₂ fun t ht => iInf₂_le t ?_
    obtain ⟨h1, h2, h3⟩ := mem_pieceSet.1 ht
    have hno : ∀ g, B g ≤ pieceStart B f₀ ∨ (t : ℝ) < B g := fun g => by
      by_cases hg : pieceStart B f₀ < B g
      · have := h3 g
        simp only [pieceProc, B, hg, ↓reduceIte] at this
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact Or.inr (by linarith)
      · exact Or.inl (not_lt.1 hg)
    have hJ := birthSum_eq_of_no_birth j B (sub_nonneg.1 h2) hno
    simp only [pieceProc] at h1
    rw [hJ, sub_add_cancel] at h1
    exact h1

end BlockBand.SourceProcess.BornRestart
