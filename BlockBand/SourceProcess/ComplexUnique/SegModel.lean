module

public import BlockBand.SourceProcess.ComplexUnique.ClausesMain
public import BlockBand.SourceProcess.ComplexUnique.ModelJumps
public import BlockBand.SourceProcess.ComplexUnique.RankSeg
public import BlockBand.SourceProcess.BornUnique.Reduce

/-!
# One model on a birth-free segment

`segModel`: for a born Gram solution with a complex source extension and a segment `[a, a + h]`
containing no birth, the restarted real joint process `segY` solves the joint real martingale
problem in `{t < h}` for the shifted filtration, with time coordinate `u ∧ h`, joint coordinates
`jvec (G (a + u)) (𝒦 (a + u))` for `u ≤ h`, and almost surely feasible Gram states.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal

variable {K np : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The restarted real joint process of a model. -/
def segY (E : ℝ) (τ' v m : Fin np → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (a h : ℝ≥0) :
    ℝ≥0 → Ω → Fin (rDim (JIdx (SrcCol K (Fin np)) (Fin np))) → ℝ :=
  rsY (jX G (fun t => birthJump τ' v (t : ℝ)) Kc (fun t => kBirthJump E τ' m (t : ℝ)))
    (jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ))) a h

/-- **One model on a birth-free segment.** -/
theorem segModel {b E : ℝ} (hb : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) {τ' v m : Fin np → ℝ}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hG : IsBornGramSolution Q 𝓖 (transportD0 b E) (srcSignature K (Fin np))
      (fun t _ => birthJump τ' v (t : ℝ)) G)
    (hK : IsComplexSourceExtension Q 𝓖 b E (srcSignature K (Fin np))
      (fun t _ => birthJump τ' v (t : ℝ)) G (fun t _ => kBirthJump E τ' m (t : ℝ)) Kc)
    {a h : ℝ≥0} (hnb : ∀ j, τ' j ≤ a ∨ ((a + h : ℝ≥0) : ℝ) < τ' j) :
    IsMPSolutionOn Q (shiftFil 𝓖 a) (realDrift (jβ (transportD0 b E) (srcSignature K (Fin np))))
        (realCov (jΓ (transportD0 b E) (etaZ b E) (srcSignature K (Fin np)))
          (jΓ' (transportD0 b E) (etaZ b E) (srcSignature K (Fin np))))
        {y | tOf y < h} (segY E τ' v m G Kc a h) ∧
      (∀ ω u, tOf (segY E τ' v m G Kc a h u ω) = ((min u h : ℝ≥0) : ℝ)) ∧
      (∀ ω u, u ≤ h → zOf (segY E τ' v m G Kc a h u ω) = jvec (G (a + u) ω) (Kc (a + u) ω)) ∧
      (∀ᵐ ω ∂Q, ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) ∧
      ∀ k, ∀ᵐ ω ∂Q, RankProp k (fun u => G (a + u) ω) (Iio h) := by
  have hD := isSignature_srcSignature K (Fin np)
  have hD0 := transportD0_pos' hb hE1 hE2
  obtain ⟨CJ, hCJ⟩ := exists_bound_jc (K := K) E τ' v m
  have hseg : ∀ u, a ≤ u → u ≤ a + h →
      jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ)) u =
        jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ)) a :=
    fun u hau hut => jc_seg E τ' v m hnb hau hut
  have hX := isCLocSol_of_joint b E hD.1 (fun t => birthJump_herm τ' v (t : ℝ)) hCJ hG hK
  refine ⟨isMPSolutionOn_rsY hX (continuous_jβ _ _) (continuous_jΓ _ _ _) (continuous_jΓ' _ _ _)
      (measurable_jc E τ' v m) hCJ fun u hau hut => hseg u hau hut.le,
    fun ω u => tOf_rsY _ _ _ _ _ _, fun ω u hu => ?_,
    by filter_upwards [hG.feasible] with ω h using h, fun k => ?_⟩
  · simp only [segY]
    rw [zOf_rsY, min_eq_left hu, ← hseg (a + u) le_self_add (add_le_add le_rfl hu), jX_add_jc]
  · have hG' : IsBornGramSolution Q 𝓖 (transportD0 b E) (srcSignature K (Fin np))
        (fun t _ => birthSum (probeJump (K := K) v) τ' (t : ℝ)) G := hG
    exact rank_segment hD0 hD hG' (fun f => (hnb f).imp id le_of_lt) k

end BlockBand.SourceProcess.ComplexUnique
