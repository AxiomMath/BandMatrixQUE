module

public import BlockBand.SourceProcess.ModelExist.TransStop
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepBounds

/-!
# Feasibility and domination for congruent Gram states

* `gramFeasible_congr`: a congruence with `L 𝖣 Lᴴ = 𝖣'` maps `𝖣'`-feasible states to
  `𝖣`-feasible states (realize `H` by `V`, then `congrGram L H` by `VL`);
* `norm_gramEntry_le_of_feasible`: at a feasible state `|G_e| ≤ 2 Re Tr M`;
* `exists_bound_box`: a continuous function of the Gram state is bounded on every entry box;
* `norm_sub_le_stop`, `norm_integral_le_stop`: along a path of feasible states with `G − J`
  continuous and `J` bounded, `G − J` is bounded by `2|K| + C_J` at every time `0 < u ≤ σ_K`,
  and `‖∫_0^u φ(G)‖ ≤ C_φ u`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Filter Topology Set Matrix Finset
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c c' : Type*} [Fintype c] [Fintype c']

theorem gramFeasible_congr {L : Matrix c' c ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
    (hL : L * D * Lᴴ = D') {H : Matrix c' c' ℂ × Matrix c' c' ℂ} (hH : GramFeasible D' H) :
    GramFeasible D (congrGram L H) := by
  obtain ⟨n, P, V, hP1, hP2, hTP, rfl⟩ := hH
  refine ⟨n, P, V * L, hP1, hP2, ?_, ?_⟩
  · have e : gramProjection P (V * L) D = gramProjection P V D' := by
      simp only [gramProjection, conjTranspose_mul, ← hL, Matrix.mul_assoc]
    unfold TwoProjection
    rw [e]
    exact hTP
  · simp only [gramPair, congrGram, sourceGram, nearGram, conjTranspose_mul, Matrix.mul_assoc]

omit [Fintype c'] in
theorem norm_gramEntry_le_of_feasible {D : Matrix c c ℂ} {H : Matrix c c ℂ × Matrix c c ℂ}
    (hH : GramFeasible D H) (e : Fin 2 × c × c) :
    ‖gramEntry e H‖ ≤ 2 * (H.1.trace).re := by
  have h := norm_toGramReal_le_of_feasible hH
  have h0 := (norm_le_pi_norm (toGramReal H) (gramRealEquiv c (e, 0))).trans h
  have h1 := (norm_le_pi_norm (toGramReal H) (gramRealEquiv c (e, 1))).trans h
  simp only [toGramReal, Equiv.symm_apply_apply, reIm, Real.norm_eq_abs] at h0 h1
  simp only [↓reduceIte, one_ne_zero] at h0 h1
  linarith [Complex.norm_le_abs_re_add_abs_im (gramEntry e H)]

omit [Fintype c] [Fintype c'] in
theorem exists_bound_box {f : Matrix c c ℂ × Matrix c c ℂ → ℂ} (hf : Continuous f) (K : ℝ) :
    ∃ C, ∀ H, (∀ e, ‖gramEntry e H‖ ≤ K) → ‖f H‖ ≤ C := by
  set B : Set (Matrix c c ℂ) := Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall 0 K
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 K
  set S : Set (Matrix c c ℂ × Matrix c c ℂ) := {H | ∀ e, ‖gramEntry e H‖ ≤ K}
  have hS : IsClosed S := by
    simp only [S, Set.ofPred_forall]
    exact isClosed_iInter fun e => isClosed_le (continuous_norm.comp (continuous_gramEntry e))
      continuous_const
  have hSB : S ⊆ B ×ˢ B := fun H hH => by
    refine ⟨fun i _ j _ => ?_, fun i _ j _ => ?_⟩
    · simpa [gramEntry] using hH (0, i, j)
    · simpa [gramEntry] using hH (1, i, j)
  obtain ⟨C, hC⟩ := ((hB.prod hB).of_isClosed_subset hS hSB).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, fun H hH => hC H hH⟩

section Path
variable {D : Matrix c c ℂ} {G J : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ} {K : ℝ}

/-- The trace stop of a single path. -/
def pathStop (G : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ) (K : ℝ) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : K ≤ ((G t).1.trace).re), (t : WithTop ℝ≥0)

omit [Fintype c'] in
theorem re_trace_lt_of_lt_pathStop {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) < pathStop G K) :
    ((G s).1.trace).re < K := by
  by_contra h
  have hK : K ≤ ((G s).1.trace).re := le_of_not_gt h
  exact (not_le.2 hs) (iInf₂_le (f := fun (t : ℝ≥0) (_ : K ≤ ((G t).1.trace).re) =>
    (t : WithTop ℝ≥0)) s hK)

omit [Fintype c'] in
theorem norm_entry_lt_stop (hf : ∀ t, GramFeasible D (G t)) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < pathStop G K) (e : Fin 2 × c × c) :
    ‖gramEntry e (G s)‖ ≤ 2 * |K| := by
  have := re_trace_lt_of_lt_pathStop hs
  exact (norm_gramEntry_le_of_feasible (hf s) e).trans (by linarith [le_abs_self K])

omit [Fintype c'] in
theorem norm_sub_le_stop (hf : ∀ t, GramFeasible D (G t))
    (hc : Continuous fun t => G t - J t) {CJ : ℝ} (hJ : ∀ t e, ‖gramEntry e (J t)‖ ≤ CJ)
    {u : ℝ≥0} (hu0 : (0 : WithTop ℝ≥0) < pathStop G K) (hu : (u : WithTop ℝ≥0) ≤ pathStop G K)
    (e : Fin 2 × c × c) : ‖gramEntry e (G u - J u)‖ ≤ 2 * |K| + CJ := by
  have hlt : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < pathStop G K →
      ‖gramEntry e (G s - J s)‖ ≤ 2 * |K| + CJ := fun s hs => by
    have e1 : gramEntry e (G s - J s) = gramEntry e (G s) - gramEntry e (J s) := by
      simp only [gramEntry, Prod.fst_sub, Prod.snd_sub, Matrix.sub_apply]; split_ifs <;> rfl
    rw [e1]
    exact (norm_sub_le _ _).trans (add_le_add (norm_entry_lt_stop hf hs e) (hJ s e))
  rcases eq_or_lt_of_le hu with h | h
  · rcases eq_zero_or_pos u with h0 | h0
    · subst h0; exact hlt 0 hu0
    · have hcont : Continuous fun s => ‖gramEntry e (G s - J s)‖ :=
        continuous_norm.comp ((continuous_gramEntry e).comp hc)
      have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h0⟩
      refine le_of_tendsto ((hcont.tendsto u).mono_left (nhdsWithin_le_nhds (s := Iio u))) ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : s < u)
      exact hlt s (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hs) hu)
  · exact hlt u h

omit [Fintype c'] in
theorem norm_integral_le_stop (hf : ∀ t, GramFeasible D (G t))
    {φ : Matrix c c ℂ × Matrix c c ℂ → ℂ} {C : ℝ}
    (hC : ∀ H, (∀ e, ‖gramEntry e H‖ ≤ 2 * |K|) → ‖φ H‖ ≤ C) {u : ℝ≥0}
    (hu : (u : WithTop ℝ≥0) ≤ pathStop G K) :
    ‖∫ s in Ioc (0 : ℝ) u, φ (G s.toNNReal)‖ ≤ C * u := by
  have h := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) (s := Ioc (0 : ℝ) u)
    (f := fun s => φ (G s.toNNReal)) (C := C) measure_Ioc_lt_top ?_
  · simpa [Real.volume_real_Ioc] using h
  · have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (u : ℝ) := Measure.ae_ne _ _
    filter_upwards [hne] with s hsne hs
    refine hC _ fun e => norm_entry_lt_stop hf ?_ e
    have hsu : s.toNNReal < u := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
      exact lt_of_le_of_ne hs.2 hsne
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hsu) hu

omit [Fintype c'] in
/-- **Domination of a stopped born compensated coordinate along a path.** -/
theorem norm_comp_stopped_le (hf : ∀ t, GramFeasible D (G t))
    (hc : Continuous fun t => G t - J t) {CJ : ℝ} (hJ : ∀ t e, ‖gramEntry e (J t)‖ ≤ CJ)
    {φ : Matrix c c ℂ × Matrix c c ℂ → ℂ} {C : ℝ}
    (hC : ∀ H, (∀ e, ‖gramEntry e H‖ ≤ 2 * |K|) → ‖φ H‖ ≤ C) {s t : ℝ≥0} (hst : s ≤ t)
    (e : Fin 2 × c × c) :
    ‖gramEntry e (G (stopTime (pathStop G K) s) - J (stopTime (pathStop G K) s)) -
        gramEntry e (G 0 - J 0) -
        ∫ r in Ioc (0 : ℝ) (stopTime (pathStop G K) s), φ (G r.toNNReal)‖ ≤
      2 * (2 * |K| + CJ) + |C| * t := by
  have hCJ : 0 ≤ CJ := (norm_nonneg _).trans (hJ 0 e)
  set u := stopTime (pathStop G K) s
  have hu : (u : WithTop ℝ≥0) ≤ pathStop G K := stopTime_le_self' _ s
  have hut : (u : ℝ) ≤ t := NNReal.coe_le_coe.2 ((stopTime_le _ s).trans hst)
  have hRHS : 0 ≤ 2 * (2 * |K| + CJ) + |C| * t := by positivity
  rcases eq_zero_or_pos u with h0 | h0
  · rw [h0]; simp only [sub_self, NNReal.coe_zero, Set.Ioc_self, Measure.restrict_empty,
      integral_zero_measure, norm_zero]; exact hRHS
  · have hσ : (0 : WithTop ℝ≥0) < pathStop G K := lt_of_lt_of_le (WithTop.coe_lt_coe.2 h0) hu
    have h1 := norm_sub_le_stop hf hc hJ hσ hu e
    have h2 := norm_sub_le_stop hf hc hJ hσ (u := 0) (by rw [WithTop.coe_zero]; exact hσ.le) e
    have h3 : ‖∫ r in Ioc (0 : ℝ) u, φ (G r.toNNReal)‖ ≤ |C| * t :=
      (norm_integral_le_stop hf (fun H hH => (hC H hH).trans (le_abs_self C)) hu).trans
        (mul_le_mul_of_nonneg_left hut (abs_nonneg C))
    calc _ ≤ ‖gramEntry e (G u - J u)‖ + ‖gramEntry e (G 0 - J 0)‖ +
          ‖∫ r in Ioc (0 : ℝ) u, φ (G r.toNNReal)‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ _ := by linarith

end Path

end BlockBand.SourceProcess.ModelExist
