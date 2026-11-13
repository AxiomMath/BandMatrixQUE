module

public import BlockBand.SourceProcess.BornRestart.PiecesEq
public import BlockBand.SourceProcess.BornRestart.Restart

/-!
# Localizing stopping times for born solutions

* `locStop j G β k`: the raw hitting time (`rawHit`) of `{‖x‖ ≥ k}` by the real coordinates of
  the continuous part `G - J`. It is a stopping time of the raw filtration. Strictly before it
  the continuous part is in the ball of radius `k` (`norm_le_of_lt_locStop`). It lies below
  the trace stop at level `card c (k + jumpBound j) + 1` (`locStop_le_traceStop`) and tends to
  `∞` (`eventually_le_locStop`).
* `isStoppingTime_sub_shift`: if `θ` is a `𝓖`-stopping time, `θ - a` is a stopping time of
  the restarted filtration.
* `norm_le_of_lt_traceStop`: strictly before a trace stop, the continuous part of a feasible
  path is in the ball of radius `K + jumpBound j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal

variable {c F : Type} [Fintype c] [Fintype F] {Ω : Type} {m : MeasurableSpace Ω}

omit [Fintype F] in
theorem stronglyMeasurable_of_measurable_gram {m' : MeasurableSpace Ω} {f : Ω → GramState c}
    (hf : Measurable[m'] f) : StronglyMeasurable[m'] f := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix c c ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → c → ℂ))
  exact hf.stronglyMeasurable

/-- The norm level set. -/
def normSet (k : ℝ) : Set (Fin (gramDim c) → ℝ) := {x | k ≤ ‖x‖}

theorem isClosed_normSet (k : ℝ) : IsClosed (normSet (c := c) k) :=
  isClosed_le continuous_const continuous_norm

/-- **The localizing stopping time** `θ_k`. -/
def locStop (j : F → GramState c) (G : ℝ≥0 → Ω → GramState c) (β : Ω → F → ℝ) (k : ℕ) :
    Ω → WithTop ℝ≥0 :=
  rawHit (normSet (k : ℝ)) fun t ω => toGramReal (G t ω - birthSum j (β ω) (t : ℝ))

variable {j : F → GramState c} {G : ℝ≥0 → Ω → GramState c} {β : Ω → F → ℝ}

theorem isStoppingTime_locStop {𝓖 : Filtration ℝ≥0 m} (hG : ∀ t, StronglyMeasurable[𝓖 t] (G t))
    (hJ : ∀ t : ℝ≥0, StronglyMeasurable[𝓖 0] fun ω => birthSum j (β ω) (t : ℝ)) (k : ℕ) :
    IsStoppingTime 𝓖 (locStop j G β k) :=
  isStoppingTime_rawHit fun t =>
    (continuous_toGramReal.comp_stronglyMeasurable
      ((hG t).sub ((hJ t).mono (𝓖.mono zero_le)))).measurable

variable {ω : Ω}

theorem locStop_eq_hitTime (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ)) (k : ℕ) :
    locStop j G β k ω = hitTime (normSet (k : ℝ))
      (fun t ω => toGramReal (G t ω - birthSum j (β ω) (t : ℝ))) ω :=
  rawHit_eq_hitTime (Y := fun t ω => toGramReal (G t ω - birthSum j (β ω) (t : ℝ)))
    (isClosed_normSet _) (continuous_toGramReal.comp hc)

theorem norm_le_of_lt_locStop (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ))
    {k : ℕ} {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) < locStop j G β k ω) :
    ‖toGramReal (G s ω - birthSum j (β ω) (s : ℝ))‖ ≤ k := by
  rw [locStop_eq_hitTime hc] at hs
  by_contra h
  exact absurd hs (not_lt.2 (iInf₂_le s (show (k : ℝ) ≤ _ from (not_le.1 h).le)))

theorem locStop_le_traceStop (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ))
    (k : ℕ) : locStop j G β k ω ≤
      gramTraceStop G (Fintype.card c * (k + jumpBound j) + 1) ω := by
  rw [locStop_eq_hitTime hc]
  refine le_iInf₂ fun t ht => ?_
  have hk : (k : ℝ) ≤ ‖toGramReal (G t ω - birthSum j (β ω) (t : ℝ))‖ := by
    by_contra h
    have h1 : ‖toGramReal (G t ω)‖ ≤ k + jumpBound j :=
      norm_toGramReal_path_le (g := fun t => G t ω) (b := β ω) (s := t) (not_le.1 h).le
    have h2 := re_trace_le (G t ω) h1
    have h3 : (Fintype.card c : ℝ) * (k + jumpBound j) + 1 ≤ ((G t ω).1.trace).re := ht
    linarith
  exact iInf₂_le (f := fun (s : ℝ≥0)
    (_ : toGramReal (G s ω - birthSum j (β ω) (s : ℝ)) ∈ normSet (c := c) (k : ℝ)) =>
      (s : WithTop ℝ≥0)) t hk

theorem eventually_le_locStop (hc : Continuous fun t => G t ω - birthSum j (β ω) (t : ℝ))
    (T : ℝ≥0) : ∀ᶠ k : ℕ in atTop, (T : WithTop ℝ≥0) ≤ locStop j G β k ω := by
  obtain ⟨R, hR⟩ := exists_path_bound hc T
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop R] with k hk
  rw [locStop_eq_hitTime hc]
  refine le_iInf₂ fun t ht => WithTop.coe_le_coe.2 ?_
  by_contra h
  have := hR t (not_le.1 h).le
  have ht' : (k : ℝ) ≤ ‖toGramReal (G t ω - birthSum j (β ω) (t : ℝ))‖ := ht
  linarith

/-- **`θ - a` is a stopping time of the restarted filtration.** -/
theorem isStoppingTime_sub_shift {𝓖 : Filtration ℝ≥0 m} {a : Ω → ℝ≥0} (ha : Measurable[𝓖 0] a)
    {θ : Ω → WithTop ℝ≥0} (hθ : IsStoppingTime 𝓖 θ) :
    IsStoppingTime (shiftFiltration 𝓖 a ha) fun ω => θ ω - a ω := by
  intro u t
  have e : {ω | θ ω - a ω ≤ u} ∩ {ω | a ω + u < t} =
      {ω | min (θ ω) t ≤ ((a ω + u : ℝ≥0) : WithTop ℝ≥0)} ∩ {ω | a ω + u < t} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, tsub_le_iff_left]
    refine and_congr_left fun hlt => ⟨fun h => (min_le_left _ _).trans (by exact_mod_cast h),
      fun h => ?_⟩
    rcases min_choice (θ ω) t with h' | h'
    · rw [h'] at h; exact_mod_cast h
    · rw [h'] at h
      exact absurd (WithTop.coe_le_coe.1 h) (not_le.2 hlt)
  rw [e]
  have h1 : Measurable[𝓖 t] fun ω => min (θ ω) t :=
    (hθ.min_const t).measurable_of_le fun _ => min_le_right _ _
  exact (measurableSet_le h1 (WithTop.measurable_coe.comp
    ((ha.add_const u).mono (𝓖.mono zero_le) le_rfl))).inter
    (measurableSet_shiftSet 𝓖 a (ha := ha) u t)

/-- Strictly before a trace stop, the continuous part of a feasible path is in a ball. -/
theorem norm_le_of_lt_traceStop {D : Matrix c c ℂ} {Y : ℝ≥0 → Ω → GramState c} {b : F → ℝ}
    {K : ℝ} (hf : ∀ s, GramFeasible D (Y s ω)) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < gramTraceStop Y K ω) :
    ‖toGramReal (Y s ω - birthSum j b (s : ℝ))‖ ≤ K + jumpBound j := by
  have hK : ((Y s ω).1.trace).re < K := by
    by_contra h
    exact absurd hs (not_lt.2 (iInf₂_le (f := fun (t : ℝ≥0) (_ : K ≤ ((Y t ω).1.trace).re) =>
      (t : WithTop ℝ≥0)) s (not_lt.1 h)))
  rw [toGramReal_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_toGramReal_birthSum_le j b _))
  exact ((norm_toGramReal_le_of_feasible (hf s)).trans hK.le)

end BlockBand.SourceProcess.BornRestart
