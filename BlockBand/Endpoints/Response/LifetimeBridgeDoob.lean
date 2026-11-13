module

public import BlockBand.Endpoints.Response.LifetimeBridgeDoobMeasure
public import BlockBand.Endpoints.Response.LifetimeBridgeSpherePos

/-!
# The lifetime-bridge lemma from the corner heat identity and the Doob killed law

This file proves `LbkHTransformLaw` from the corner heat identity and the Doob killed law alone,
without the Markov input, and deduces the lifetime-bridge lemma.

## Main results

* `LbkDoobParts` (`LbkSplitParts` without `markov`) and `lbkParts_of_doob`.
* `lifetimeBridge_of_doob : (∀ D₀ > 0, LbkDoobParts D₀) → LifetimeBridgeStatement`.
* `lifetimeBridge_of_doob'`, which also supplies `spherePos` by `lbkSphereKernelPos_holds`, so
  that the hypotheses are `LbkBaseExistence`, `LbkBaseTransitionLaw`,
  `LbkCornerHeatIdentity`, `LbkDoobKilledLaw` and `LbkBridgeExistence` (all proved; the
  lemma itself is `lifetimeBridgeStatement_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- **The h-transform law from the corner heat identity and the Doob killed law**: these two
imply `LbkHTransformLaw`; no Markov input.
-/
theorem lbkHTransformLaw_of_doob {D0 : ℝ} (hD0 : 0 < D0) (h1 : LbkCornerHeatIdentity D0)
    (h2 : LbkDoobKilledLaw D0) : LbkHTransformLaw D0 := by
  classical
  intro x y hxy Ω m 𝓖 P N X Y hP k ts hts htp g hg F hF
  obtain ⟨-, hτ⟩ := lbk_extinction_ae_eq hP
  have hk := lbk_kernel_measurable hD0
  have hpos := lbk_extinction_pos_ae_of_dualProcess one_pos hP
  have hGm : Measurable fun q : (Fin k → ℝ × ℝ) × ℝ => F q.1 * g q.2 :=
    (hF.comp measurable_fst).mul (hg.comp measurable_snd)
  -- the integrand is that of the joint law, a.s.
  have hL : ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < dualExtinction N ω
        then g (dualExtinction N ω).toReal * F (fun i => dualPoint X Y (ts i) ω) else 0) ∂P =
      ∫⁻ ω, {ω | ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧
        lbkExtinctionRat N ω < ⊤}.indicator
          (fun ω => F (fun i => dualPoint X Y (ts i) ω) * g (lbkExtinctionRat N ω).toReal) ω ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hτ, hpos] with ω hω hp
    rw [hω] at hp ⊢
    have he := lbk_forall_lt_iff_last hts hp
    by_cases hcS : ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧
        lbkExtinctionRat N ω < ⊤
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hcS.2, he.2 hcS.1⟩), indicator_of_mem (show ω ∈ {ω |
        ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧ lbkExtinctionRat N ω < ⊤}
        from hcS), mul_comm]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hcS ⟨he.1 h.2, h.1⟩), indicator_of_notMem (show ω ∉ {ω |
        ENNReal.ofReal (lbkLastTime ts) < lbkExtinctionRat N ω ∧ lbkExtinctionRat N ω < ⊤}
        from hcS)]
  -- the joint law is the explicit density measure; integrate `F(zs) g(r)`
  rw [hL, ← lbk_jointLaw_lintegral hP ts hGm, lbk_jointLaw_eq_density hD0 h1 h2 hxy hP hts htp,
    lbk_jointDensity_lintegral hD0 x y ts hGm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun zs => ?_
  have hsm : Measurable fun s : ℝ =>
      g (lbkLastTime ts + s) * ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0)) :=
    (hg.comp (measurable_const.add measurable_id)).mul
      (hk.comp (f := fun s : ℝ => (s, lbkLastPoint (x, y) zs, ((0, 0) : ℝ × ℝ)))
        (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have hpt : ∀ s, lbkJointDens D0 x y ts (zs, s) * (F (zs, lbkLastTime ts + s).1 *
      g (zs, lbkLastTime ts + s).2) =
      (ENNReal.ofReal (D0 / 2 * (x + y)) * F zs * lbkFddProd (lbkKernel D0) (x, y) ts zs) *
        (g (lbkLastTime ts + s) *
          ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0))) := by
    intro s
    simp only [lbkJointDens]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul _ hsm]
  ring

/-!
### The parts without the Markov input
-/

/-- The parts of the lifetime-bridge lemma at diffusivity `D₀`: `LbkSplitParts`
without the redundant Markov input `markov`.
-/
structure LbkDoobParts (D0 : ℝ) : Prop where
  spherePos : LbkSphereKernelPos D0
  existence : LbkBaseExistence D0
  transition : LbkBaseTransitionLaw D0
  cornerHeat : LbkCornerHeatIdentity D0
  doob : LbkDoobKilledLaw D0
  bridge : LbkBridgeExistence D0

/-- `LbkSplitParts` forgets to `LbkDoobParts`. -/
theorem lbkDoobParts_of_split {D0 : ℝ} (h : LbkSplitParts D0) : LbkDoobParts D0 :=
  ⟨h.spherePos, h.existence, h.transition, h.cornerHeat, h.doob, h.bridge⟩

/-- `LbkParts` from the parts without the Markov input. -/
theorem lbkParts_of_doob {D0 : ℝ} (hD0 : 0 < D0) (h : LbkDoobParts D0) : LbkParts D0 :=
  ⟨h.spherePos, h.existence, h.transition, lbkHTransformLaw_of_doob hD0 h.cornerHeat h.doob,
    h.bridge⟩

/-- The lifetime-bridge lemma from the parts without the Markov input, as in
`lifetimeBridge_of_split`. -/
theorem lifetimeBridge_of_doob (h : ∀ D0 : ℝ, 0 < D0 → LbkDoobParts D0) :
    LifetimeBridgeStatement :=
  lifetimeBridge_of_parts fun D0 hD0 => lbkParts_of_doob hD0 (h D0 hD0)

/-- The lifetime-bridge lemma from five inputs: `spherePos` is supplied by
`lbkSphereKernelPos_holds`, and the Markov input is not needed. -/
theorem lifetimeBridge_of_doob' (h : ∀ D0 : ℝ, 0 < D0 → LbkBaseExistence D0 ∧
      LbkBaseTransitionLaw D0 ∧ LbkCornerHeatIdentity D0 ∧ LbkDoobKilledLaw D0 ∧
      LbkBridgeExistence D0) :
    LifetimeBridgeStatement :=
  lifetimeBridge_of_doob fun D0 hD0 =>
    ⟨lbkSphereKernelPos_holds D0 hD0, (h D0 hD0).1, (h D0 hD0).2.1, (h D0 hD0).2.2.1,
      (h D0 hD0).2.2.2.1, (h D0 hD0).2.2.2.2⟩

end BlockBand.Endpoints
