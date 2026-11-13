module

public import BlockBand.Palm.RelativeLocalizationHit
public import BlockBand.Palm.MomentFlow.StartShift

/-!
# Relative localization: small gaps along the whole window have vanishing probability

Clause (b1) of `DysonBrownianMotion` gives a simple spectrum only at its times `t > 0`. To include
the base time `a` itself we restart the flow from `a/2` (`BlockBand.Palm.MomentFlow.restartMap`,
its measure-preservation `measurePreserving_restartMap` and `flowMatrix_restartMap`). Proved:

* `flowLam_eq_flowEigenvalue` : `flowLam F u ω = flowEigenvalue F a ω (a + u)` when `ω.1` is
  Hermitian;
* `tendsto_gapEvent` (`a > 0`): `flowLaw N a {∃ u ≤ T, some gap of flowLam(u) ≤ 1/(n+1)} → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal ComplexConjugate

variable {N : ℕ}

theorem flowLam_eq_flowEigenvalue (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) {ω : FlowSample N}
    (hω : ω.1.IsHermitian) (u : ℝ≥0) :
    flowLam F u ω = fun k => flowEigenvalue F a ω (a + u) k := by
  funext k
  have h := flowMatrix_eq F a hω (σ := a + u) (by have := NNReal.coe_nonneg u; linarith)
  rw [show a + (u : ℝ) - a = u by ring, Real.toNNReal_coe] at h
  simp only [flowLam, flowEigenvalue, flowH, h]

theorem hermitianBrownian_isHermitian (B : FlowNoise N) (t : ℝ) :
    (hermitianBrownian B t).IsHermitian := by
  ext a b
  simp only [hermitianBrownian, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
    map_mul, map_add, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
  ring

/-- Gap event on the window `[0,T]` (time of `DysonBrownianMotion`). -/
def gapEvent (F : Matrix (Fin N) (Fin N) ℂ) (T : ℝ≥0) (g : ℝ) : Set (FlowSample N) :=
  {ω | ∃ u : ℝ≥0, u ≤ T ∧ flowLam F u ω ∈ gapSet N g}

/-- Pair gap event. -/
def pairGapEvent (F : Matrix (Fin N) (Fin N) ℂ) (T : ℝ≥0) (i j : Fin N) (g : ℝ) :
    Set (FlowSample N) :=
  {ω | ∃ u : ℝ≥0, u ≤ T ∧ |flowLam F u ω i - flowLam F u ω j| ≤ g}

theorem measurableSet_pairGapEvent {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (T : ℝ≥0) (i j : Fin N) (g : ℝ) : MeasurableSet (pairGapEvent F T i j g) := by
  have hK : IsClosed {lam : Fin N → ℝ | |lam i - lam j| ≤ g} :=
    isClosed_le (((continuous_apply i).sub (continuous_apply j)).abs) continuous_const
  have hst := isStoppingTime_hitTime (flowFiltration N) (fun u ω => flowLam F u ω)
    (fun u => flowLam_adapted F u) (fun ω => flowLam_continuous hF ω) hK T
  have : pairGapEvent F T i j g = {ω | hitTime (fun u ω => flowLam F u ω)
      {lam : Fin N → ℝ | |lam i - lam j| ≤ g} ω ≤ T} := by
    ext ω
    rw [Set.mem_ofPred_eq, hitTime_le_iff (flowLam_continuous hF ω) hK]
    rfl
  rw [this]; exact (flowFiltration N).le T _ hst

theorem gapEvent_subset (F : Matrix (Fin N) (Fin N) ℂ) (T : ℝ≥0) (g : ℝ) :
    gapEvent F T g ⊆ ⋃ p : {p : Fin N × Fin N // p.1 ≠ p.2}, pairGapEvent F T p.1.1 p.1.2 g := by
  rintro ω ⟨u, hu, i, j, hij, hg⟩
  exact Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, u, hu, hg⟩

/-- Collisions on `[0,T]` (including the base time) are null for `a > 0`. -/
theorem collision_null (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) {i j : Fin N} (hij : i ≠ j) :
    flowLaw N a (⋂ n : ℕ, pairGapEvent F T i j (1 / ((n : ℝ) + 1))) = 0 := by
  set C := ⋂ n : ℕ, pairGapEvent F T i j (1 / ((n : ℝ) + 1))
  have hCm : MeasurableSet C := MeasurableSet.iInter fun n => measurableSet_pairGapEvent hF T i j _
  have hmp := BlockBand.Palm.MomentFlow.measurePreserving_restartMap (N := N)
    (a' := a / 2) (a := a) (by linarith) (by linarith)
  rw [← hmp.measure_preimage hCm.nullMeasurableSet]
  refine measure_mono_null (fun ω hω => ?_) ((ae_fst_isHermitian (N := N) (a / 2)).and
    (flow_simpleSpectrum hDBM hF (a / 2)) |> fun h => (ae_iff.mp h))
  simp only [Set.mem_ofPred_eq, not_and_or, not_forall]
  by_contra hcon
  push Not at hcon
  obtain ⟨hH, hsimp⟩ := hcon
  -- the restarted sample is Hermitian
  have hH' : (BlockBand.Palm.MomentFlow.restartMap (N := N) (a / 2) a ω).1.IsHermitian :=
    hH.add (hermitianBrownian_isHermitian _ _)
  -- a collision at some time
  set f : ℝ≥0 → ℝ := fun u => |flowLam F u (BlockBand.Palm.MomentFlow.restartMap (a / 2) a ω) i -
    flowLam F u (BlockBand.Palm.MomentFlow.restartMap (a / 2) a ω) j|
  have hfc : Continuous f := (((continuous_apply i).comp (flowLam_continuous hF _)).sub
    ((continuous_apply j).comp (flowLam_continuous hF _))).abs
  obtain ⟨r, hr, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_isMinOn
    ⟨0, ⟨le_rfl, zero_le (a := T)⟩⟩ hfc.continuousOn
  have hf0 : f r = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨u, hu, hgu⟩ := Set.mem_iInter.mp hω n
    have h1 : f r ≤ f u := hmin ⟨zero_le (a := u), hu⟩
    have h2 : f u ≤ 1 / ((n : ℝ) + 1) := hgu
    linarith
  -- but the spectrum is simple at `a + r > a/2`
  have hσ : a / 2 < a + r := by have := NNReal.coe_nonneg r; linarith
  have hs := hsimp (a + r) hσ
  simp only [f] at hf0
  rw [flowLam_eq_flowEigenvalue F a hH' r] at hf0
  simp only [flowEigenvalue] at hf0
  rw [BlockBand.Palm.MomentFlow.flowMatrix_restartMap F (by linarith : a / 2 ≤ a)
    (by have := NNReal.coe_nonneg r; linarith) ω] at hf0
  have hHerm : (flowMatrix F (a / 2) ω (a + r)).IsHermitian :=
    (hF.add hH).add (hermitianBrownian_isHermitian _ _)
  rw [freshEigenvalue_eq_dyson hHerm, freshEigenvalue_eq_dyson hHerm, abs_eq_zero,
    sub_eq_zero] at hf0
  exact hij (Fin.rev_injective (hs.injective hf0))

/-- **Vanishing small-gap probability on the window `[0,T]`.** -/
theorem tendsto_gapEvent (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => flowLaw N a (gapEvent F T (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hpair : ∀ p : {p : Fin N × Fin N // p.1 ≠ p.2},
      Tendsto (fun n : ℕ => flowLaw N a (pairGapEvent F T p.1.1 p.1.2 (1 / ((n : ℝ) + 1))))
        atTop (𝓝 0) := by
    intro p
    have h := tendsto_measure_iInter_atTop (μ := flowLaw N a)
      (s := fun n : ℕ => pairGapEvent F T p.1.1 p.1.2 (1 / ((n : ℝ) + 1)))
      (fun n => (measurableSet_pairGapEvent hF T _ _ _).nullMeasurableSet)
      (fun m n hmn ω hω => by
        obtain ⟨u, hu, hg⟩ := hω
        exact ⟨u, hu, hg.trans (by gcongr)⟩) ⟨0, measure_ne_top _ _⟩
    rwa [collision_null hDBM hF ha T p.2] at h
  have hsum : Tendsto (fun n : ℕ => ∑ p : {p : Fin N × Fin N // p.1 ≠ p.2},
      flowLaw N a (pairGapEvent F T p.1.1 p.1.2 (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ) fun p _ => hpair p
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    fun n => ?_
  exact (measure_mono (gapEvent_subset F T _)).trans (measure_iUnion_fintype_le _ _)

end BlockBand.Palm.RelativeLocalization
