module

public import BlockBand.Transmission.Dual.MPConverseCalc
public import BlockBand.Transmission.Dual.MPConverseIBP
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse
public import BlockBand.SourceProcess.Stochastic.Representation.Integrator
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.Pathwise

/-!
# Martingale-problem converse: tools

* `testMart`, `IsTestMPSolution`: the `C_c^∞`-test martingale problem in an open set `U`
  (every `φ(Y_t) − φ(Y_0) − ∫_0^t 𝓛φ(Y_s) ds`, `φ` smooth with compact support in `U`, has a
  martingale modification; adapted, a.s. continuous paths).
* Algebra of martingale modifications: `hasMM_sub`, `hasMM_congr`, `hasMM_const_mul` (bounded
  `𝓖_0`-measurable factor), `hasMM_stop` (stopping at the exit from an open set, via the raw
  hitting time `rawHit`, a.s. equal to it on continuous paths).
* Pathwise: `continuous_testMart`, `stopped_testMart_eq` (the stopped test process only sees
  the test on a neighbourhood of `closure W`), and `bracket_alg` (the deterministic identity
  `M_iM_j − ∫a_ij = F_ij − y_i(0)M_j − y_j(0)M_i − G_ij − G_ji`, by the FTC for `A_iA_j`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime
  exists_martingale_stoppedProcess rawHit isStoppingTime_rawHit rawHit_eq_hitTime
  setIntegral_switch measurableSet_toNNReal_le continuous_stopTime stopTime_le
  aesm_stoppedProcess_exit)
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- `φ(Y_t) − φ(Y_0) − ∫_0^t 𝓛φ(Y_s) ds`. -/
def testMart (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (φ : (Fin d → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  φ (Y t ω) - φ (Y 0 ω) - ∫ s in Ioc (0 : ℝ) t, mpGenerator b a φ (Y s.toNNReal ω)

/-- The `C_c^∞`-test martingale problem in the open set `U`. -/
structure IsTestMPSolution (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (U : Set (Fin d → ℝ)) (Y : ℝ≥0 → Ω → Fin d → ℝ) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (Y t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω
  mart : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    HasMartingaleModification Q 𝓖 (testMart b a φ Y)

/-!
## Algebra of martingale modifications
-/

omit [IsProbabilityMeasure Q] in
theorem hasMM_sub {X Z : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (hZ : HasMartingaleModification Q 𝓖 Z) :
    HasMartingaleModification Q 𝓖 (fun t ω => X t ω - Z t ω) := by
  obtain ⟨M, hM, hMX⟩ := hX
  obtain ⟨N, hN, hNZ⟩ := hZ
  exact ⟨M - N, hM.sub hN, fun t => (hMX t).sub (hNZ t)⟩

omit [IsProbabilityMeasure Q] in
theorem hasMM_congr {X Z : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (h : ∀ t, X t =ᵐ[Q] Z t) : HasMartingaleModification Q 𝓖 Z := by
  obtain ⟨M, hM, hMX⟩ := hX
  exact ⟨M, hM, fun t => (hMX t).trans (h t)⟩

omit [IsProbabilityMeasure Q] in
/-- A bounded `𝓖_0`-measurable factor preserves martingale modifications. -/
theorem hasMM_const_mul {X : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓖 0] ξ) {c : ℝ} (hc : ∀ ω, |ξ ω| ≤ c) :
    HasMartingaleModification Q 𝓖 (fun t ω => ξ ω * X t ω) := by
  obtain ⟨M, hM, hMX⟩ := hX
  have hξt : ∀ t, StronglyMeasurable[𝓖 t] ξ := fun t => hξ.mono (𝓖.mono zero_le)
  have hint : ∀ t, Integrable (ξ * M t) Q := fun t =>
    (hM.integrable t).bdd_mul ((hξt t).mono (𝓖.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hc ω)
  refine ⟨fun t => ξ * M t, ⟨fun t => (hξt t).mul (hM.1 t), fun s t hst => ?_⟩, fun t => ?_⟩
  · refine (condExp_mul_of_stronglyMeasurable_left (hξt s) (hint t) (hM.integrable t)).trans ?_
    filter_upwards [hM.2 s t hst] with ω hω
    simp [hω]
  · filter_upwards [hMX t] with ω hω
    simp [hω]

/-- Stopping at the exit time from an open set preserves martingale modifications with a.s.
continuous paths. -/
theorem hasMM_stop {X : ℝ≥0 → Ω → ℝ} (hX : HasMartingaleModification Q 𝓖 X)
    (hXc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω) {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : ∀ t, Measurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {W : Set (Fin d → ℝ)} (hW : IsOpen W) :
    HasMartingaleModification Q 𝓖 (stoppedProcess X (exitTimeFrom W Y)) := by
  obtain ⟨M, hM, hMX⟩ := hX
  have hρ := isStoppingTime_rawHit (F := Wᶜ) hY
  obtain ⟨M', hM', hM'e⟩ := exists_martingale_stoppedProcess hM hMX hXc hρ
  refine ⟨M', hM', fun t => (hM'e t).trans ?_⟩
  filter_upwards [hYc] with ω hω
  simp only [stoppedProcess_eq_stopTime]
  rw [rawHit_eq_hitTime hW.isClosed_compl hω]
  rfl

/-!
## Pathwise facts
-/

omit [MeasurableSpace Ω] in
theorem continuous_setIntegral_path {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hω : Continuous fun t => Y t ω) :
    Continuous fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, g (Y s.toNNReal ω) := by
  have hc : Continuous fun s : ℝ => g (Y s.toNNReal ω) :=
    hg.comp (hω.comp continuous_real_toNNReal)
  have hprim := intervalIntegral.continuous_primitive
    (fun a c => hc.intervalIntegrable (μ := volume) a c) (0 : ℝ)
  have he : (fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, g (Y s.toNNReal ω)) =
      fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, g (Y s.toNNReal ω) := by
    funext t; rw [intervalIntegral.integral_of_le t.coe_nonneg]
  rw [he]; exact hprim.comp NNReal.continuous_coe

omit [MeasurableSpace Ω] in
theorem continuous_testMart {b a} {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : ContinuousOn b U)
    (ha : ContinuousOn a U) {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : tsupport φ ⊆ U) {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hω : Continuous fun t => Y t ω) : Continuous fun t => testMart b a φ Y t ω :=
  ((hφ.continuous.comp hω).sub continuous_const).sub
    (continuous_setIntegral_path (continuous_mpGenerator hU hb ha hφ hφs) hω)

omit [MeasurableSpace Ω] in
/-- The stopped test martingale, when the test agrees with `g` (and its generator with `L`)
on an open `V ⊇ closure W`. -/
theorem stopped_testMart_eq {b a} {W V : Set (Fin d → ℝ)} (hW : IsOpen W)
    (hWV : closure W ⊆ V) {ψ g L : (Fin d → ℝ) → ℝ} (hψg : ∀ y ∈ V, ψ y = g y)
    (hL : ∀ y ∈ V, mpGenerator b a ψ y = L y) {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hω : Continuous fun t => Y t ω) (t : ℝ≥0) :
    stoppedProcess (testMart b a ψ Y) (exitTimeFrom W Y) t ω =
      g (Y (stopTime (exitTimeFrom W Y ω) t) ω) - g (Y 0 ω) -
        ∫ s in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), L (Y s.toNNReal ω) := by
  obtain ⟨hcl, hY0⟩ := Bridges.stopped_path_mem_closure hW hω t
  rw [stoppedProcess_eq_stopTime]
  unfold testMart
  have hint : ∫ s in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), mpGenerator b a ψ
      (Y s.toNNReal ω) = ∫ s in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), L (Y s.toNNReal ω) :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => hL _ (hWV (hcl s hs))
  rw [hint]
  rcases hY0 with h | ⟨h1, h0⟩
  · rw [h]; ring
  · rw [hψg _ (hWV h1), hψg _ (hWV h0)]

open intervalIntegral in
/-- Pathwise bracket identity (FTC for `A_iA_j`). -/
theorem bracket_alg {yi yj bi bj aij Ai Aj Mi Mj : ℝ → ℝ} (hyi : Continuous yi)
    (hyj : Continuous yj) (hbi : Continuous bi) (hbj : Continuous bj) (haij : Continuous aij)
    (hAi : ∀ s, Ai s = ∫ u in (0 : ℝ)..s, bi u) (hAj : ∀ s, Aj s = ∫ u in (0 : ℝ)..s, bj u)
    (hMi : ∀ s, Mi s = yi s - yi 0 - Ai s) (hMj : ∀ s, Mj s = yj s - yj 0 - Aj s) (r : ℝ) :
    Mi r * Mj r - ∫ u in (0 : ℝ)..r, aij u =
      (yi r * yj r - yi 0 * yj 0 - ∫ u in (0 : ℝ)..r, (bi u * yj u + bj u * yi u + aij u)) -
        yi 0 * Mj r - yj 0 * Mi r - (Ai r * Mj r - ∫ u in (0 : ℝ)..r, bi u * Mj u) -
        (Aj r * Mi r - ∫ u in (0 : ℝ)..r, bj u * Mi u) := by
  have cAi : Continuous Ai := by
    rw [show Ai = fun s => ∫ u in (0 : ℝ)..s, bi u from funext hAi]
    exact continuous_primitive (fun a b => hbi.intervalIntegrable a b) 0
  have cAj : Continuous Aj := by
    rw [show Aj = fun s => ∫ u in (0 : ℝ)..s, bj u from funext hAj]
    exact continuous_primitive (fun a b => hbj.intervalIntegrable a b) 0
  have cMi : Continuous Mi := by
    rw [show Mi = fun s => yi s - yi 0 - Ai s from funext hMi]; fun_prop
  have cMj : Continuous Mj := by
    rw [show Mj = fun s => yj s - yj 0 - Aj s from funext hMj]; fun_prop
  have dAi : ∀ s, HasDerivAt Ai (bi s) s := fun s => by
    rw [show Ai = fun s => ∫ u in (0 : ℝ)..s, bi u from funext hAi]
    exact (hbi.integral_hasStrictDerivAt 0 s).hasDerivAt
  have dAj : ∀ s, HasDerivAt Aj (bj s) s := fun s => by
    rw [show Aj = fun s => ∫ u in (0 : ℝ)..s, bj u from funext hAj]
    exact (hbj.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hFTC : ∫ u in (0 : ℝ)..r, (bi u * Aj u + Ai u * bj u) = Ai r * Aj r := by
    rw [integral_eq_sub_of_hasDerivAt (f := fun s => Ai s * Aj s)
      (fun s _ => (dAi s).mul (dAj s))
      (((hbi.mul cAj).add (cAi.mul hbj)).intervalIntegrable 0 r)]
    simp [hAi]
  have ii : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume 0 r :=
    fun f hf => hf.intervalIntegrable 0 r
  have e1 : ∫ u in (0 : ℝ)..r, (bi u * yj u + bj u * yi u + aij u) =
      (∫ u in (0 : ℝ)..r, bi u * Mj u) + (∫ u in (0 : ℝ)..r, bj u * Mi u) +
        (∫ u in (0 : ℝ)..r, (bi u * Aj u + Ai u * bj u)) + yj 0 * Ai r + yi 0 * Aj r +
        ∫ u in (0 : ℝ)..r, aij u := by
    have hpt : ∀ u, bi u * yj u + bj u * yi u + aij u =
        bi u * Mj u + bj u * Mi u + (bi u * Aj u + Ai u * bj u) + yj 0 * bi u +
          yi 0 * bj u + aij u := fun u => by rw [hMi, hMj]; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_add (by apply ii; fun_prop) (ii _ haij),
      intervalIntegral.integral_add (by apply ii; fun_prop) (by apply ii; fun_prop),
      intervalIntegral.integral_add (by apply ii; fun_prop) (by apply ii; fun_prop),
      intervalIntegral.integral_add (by apply ii; fun_prop) (by apply ii; fun_prop),
      intervalIntegral.integral_add (by apply ii; fun_prop) (by apply ii; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hAi, ← hAj]
  rw [e1, hFTC]
  have hyr : yi r = Mi r + Ai r + yi 0 := by rw [hMi]; ring
  have hyr' : yj r = Mj r + Aj r + yj 0 := by rw [hMj]; ring
  rw [hyr, hyr']
  ring

end BlockBand.Transmission.Dual
