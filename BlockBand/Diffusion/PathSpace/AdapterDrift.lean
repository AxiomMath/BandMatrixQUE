module
public import BlockBand.Diffusion.PathSpace.TestMP
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Localize
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Adapter, part 1: stopped test processes and the drift field

Setting: probability space `(Ω, Q)`, **raw** filtration `𝓖` (no completion, no right
continuity), `U` open, `b, a` continuous on `U`, `Z` a solution of the raw test-function
martingale problem `IsTestMPSolution Q 𝓖 b a U Z`.

Which filtration properties are needed: **none.** The only stopping time used is the raw
hitting time `rawHit Wᶜ Z`, which is a `𝓖`-stopping time for every adapted `Z`
(`isStoppingTime_rawHit`, no path regularity, no usual conditions) and equals the exit time
`exitTimeFrom W Z` on every continuous path (`rawHit_compl_eq_exitTimeFrom`); optional stopping
is `exists_martingale_stoppedProcess` (a.s. continuous processes with a martingale
modification, raw filtration). No augmented filtration is needed.

* `testCompensated f g Z t = f(Z_t) - f(Z_0) - ∫_0^t g(Z_u) du`.
* `IsTestMPSolution.exists_martingale_stopped`: for a test `f` and any open `W`, the stopped
  process `testCompensated f (𝓛f) Z` at `exitTimeFrom W Z` has a `𝓖`-martingale modification.
* `stopped_testCompensated_eq`: pathwise localization: if `f = p` near `closure W` and
  `g = q` on `closure W`, the stopped compensated processes agree on continuous paths.
* `IsTestMPSolution.drift`: the `drift` field of `IsMPSolutionOn`.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal

variable {d : ℕ} {Ω : Type*}

/-- The compensated test process `f(Z_t) - f(Z_0) - ∫_0^t g(Z_u) du`. -/
def testCompensated (f g : (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  f (Z t ω) - f (Z 0 ω) - ∫ u in Ioc (0 : ℝ) t, g (Z u.toNNReal ω)

theorem integrableOn_comp_path {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    {Z : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hZ : Continuous fun t => Z t ω) (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ => g (Z s.toNNReal ω)) (Ioc 0 t) :=
  (hg.comp (hZ.comp continuous_real_toNNReal)).integrableOn_Ioc

theorem continuous_testCompensated {f g : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) {Z : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hZ : Continuous fun t => Z t ω) :
    Continuous fun t => testCompensated f g Z t ω :=
  ((hf.comp hZ).sub continuous_const).sub
    (continuous_setIntegral_Ioc (g := fun u => g (Z u ω)) (integrableOn_comp_path hg hZ))

/-- **Pathwise localization.** If `f = p` on `V ⊇ closure W` and `g = q` on `closure W`,
then on every continuous path the processes stopped at the exit from `W` agree. -/
theorem stopped_testCompensated_eq {f p g q : (Fin d → ℝ) → ℝ} {W V : Set (Fin d → ℝ)}
    (hW : IsOpen W) (hWV : closure W ⊆ V) (hfp : ∀ y ∈ V, f y = p y)
    (hgq : ∀ y ∈ closure W, g y = q y) {Z : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hZ : Continuous fun t => Z t ω) (t : ℝ≥0) :
    stoppedProcess (testCompensated f g Z) (exitTimeFrom W Z) t ω =
      stoppedProcess (testCompensated p q Z) (exitTimeFrom W Z) t ω := by
  simp only [stoppedProcess_eq_stopTime, testCompensated]
  obtain ⟨h1, h2⟩ := stopped_path_mem_closure hW hZ t
  have hI : ∫ u in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Z ω) t), g (Z u.toNNReal ω) =
      ∫ u in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Z ω) t), q (Z u.toNNReal ω) :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => hgq _ (h1 s hs)
  rw [hI]
  rcases h2 with h | ⟨ha, hb⟩
  · rw [h]; simp
  · rw [hfp _ (hWV ha), hfp _ (hWV hb)]

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ}

/-- The compensated test process `f(Z_t) - f(Z_0) - ∫_0^t 𝓛f(Z_u) du` is a raw martingale. -/
theorem IsTestMPSolution.martingale_testCompensated (h : IsTestMPSolution Q 𝓖 b a U Z)
    {f : (Fin d → ℝ) → ℝ} (hf : IsMPTest U f) :
    Martingale (testCompensated f (mpGenerator b a f) Z) 𝓖 Q := by
  have hX := h.martingale f hf
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
  have hg0 : StronglyMeasurable[𝓖 ⊥] fun ω => f (Z 0 ω) :=
    (hf.1.continuous.measurable.comp (h.adapted 0)).stronglyMeasurable
  have hgi : Integrable (fun ω => f (Z 0 ω)) Q :=
    Integrable.of_bound (hg0.mono (𝓖.le _)).aestronglyMeasurable C
      (ae_of_all _ fun ω => hC _)
  have := hX.sub (martingale_const_fun 𝓖 Q hg0 hgi)
  convert this using 1
  funext t ω
  simp only [testCompensated, Pi.sub_apply]
  ring

/-- **Optional stopping at an exit time on a raw filtration.** For a test `f` and an open `W`,
the compensated test process stopped at `exitTimeFrom W Z` has a `𝓖`-martingale
modification. -/
theorem IsTestMPSolution.exists_martingale_stopped (h : IsTestMPSolution Q 𝓖 b a U Z)
    (hU : IsOpen U) (hb : ContinuousOn b U) (ha : ContinuousOn a U) {f : (Fin d → ℝ) → ℝ}
    (hf : IsMPTest U f) {W : Set (Fin d → ℝ)} (hW : IsOpen W) :
    ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧ ∀ t,
      N t =ᵐ[Q] stoppedProcess (testCompensated f (mpGenerator b a f) Z) (exitTimeFrom W Z) t := by
  have hX := h.martingale_testCompensated hf
  have hc : ∀ᵐ ω ∂Q, Continuous fun t => testCompensated f (mpGenerator b a f) Z t ω := by
    filter_upwards [h.continuous] with ω hω
    exact continuous_testCompensated hf.1.continuous (continuous_mpGenerator hU hb ha hf) hω
  have hρ : IsStoppingTime 𝓖 (rawHit Wᶜ Z) := isStoppingTime_rawHit h.adapted
  obtain ⟨M, hM, hMX⟩ := exists_martingale_stoppedProcess hX (fun _ => ae_eq_refl _) hc hρ
  refine ⟨M, hM, fun t => (hMX t).trans ?_⟩
  filter_upwards [h.continuous] with ω hω
  simp only [stoppedProcess_eq_stopTime, rawHit_compl_eq_exitTimeFrom hW hω]

/-- On `closure W`, the generator of the localized coordinate `χ y_i` is `b_i`. -/
theorem mpGenerator_bump_coord {χ : (Fin d → ℝ) → ℝ} {V W : Set (Fin d → ℝ)} (hV : IsOpen V)
    (hWV : closure W ⊆ V) (hχ : ∀ y ∈ V, χ y = 1) (i : Fin d) :
    ∀ y ∈ closure W, mpGenerator b a (fun y => χ y * y i) y = b y i := fun y hy => by
  rw [mpGenerator_congr (eventuallyEq_mul_of_eq_one hV hχ (hWV hy)), mpGenerator_coord]

/-- **The drift field of `IsMPSolutionOn`.** -/
theorem IsTestMPSolution.drift (h : IsTestMPSolution Q 𝓖 b a U Z) (hU : IsOpen U)
    (hb : ContinuousOn b U) (ha : ContinuousOn a U) {W : Set (Fin d → ℝ)}
    (hW : IsInteriorDomain W U) (i : Fin d) :
    ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧ ∀ t,
      N t =ᵐ[Q] stoppedProcess (mpCompensated b Z i) (exitTimeFrom W Z) t := by
  obtain ⟨χ, V, hχ, hV, hWV, hχ1⟩ := exists_bump hU hW
  have hf := hχ.mul_left (p := fun y => y i) (contDiff_apply ℝ ℝ i)
  obtain ⟨N, hN, hNe⟩ := h.exists_martingale_stopped hU hb ha hf hW.1
  refine ⟨N, hN, fun t => ?_⟩
  filter_upwards [hNe t, h.continuous] with ω h1 h2
  rw [h1, stopped_testCompensated_eq hW.1 hWV (p := fun y => y i) (q := fun y => b y i)
    (fun y hy => by simp [hχ1 y hy]) (mpGenerator_bump_coord hV hWV hχ1 i) h2]
  rfl

end BlockBand.Diffusion
