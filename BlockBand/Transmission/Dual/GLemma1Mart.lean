module

public import BlockBand.Transmission.Dual.GBase
public import BlockBand.Transmission.Dual.GProdTools
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Main

/-!
# The local Doob identity: the density martingales under the base process

Let `Z` solve the flat base martingale problem `(flatBaseDrift D₀ q, flatDiff D₀ q)` on the flat
chamber, on any filtered probability space (`Ω : Type`), and let `W` be an interior domain of the
flat chamber. By Itô's formula for martingale problems (`martingaleProblemIto_holds`) and the
h-transform identities:
* `hasMM_cauchyH_stop`: `H_q(Z_{t∧τ_W}) − H_q(Z_0)` has a martingale modification
  (`𝓛⁰ H_q = 0`): the density martingale;
* `hasMM_cauchyH_mul_stop`: for `f ∈ C²`,
  `(H_q f)(Z_{t∧τ_W}) − (H_q f)(Z_0) − ∫_0^{t∧τ_W} H_q 𝒟_q f (Z_s) ds` has a martingale
  modification (`𝓛⁰(H_q f) = H_q 𝒟_q f`): the input of Bayes' rule.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ}

theorem continuous_flatBaseDrift (D0 : ℝ) : Continuous (flatBaseDrift D0 q) := by
  refine continuous_pi fun k => Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [flatBaseDrift, Fin.append_left]
    exact continuous_const.mul (continuous_const.add (continuous_const.mul
      ((continuous_apply i).comp (continuous_fst.comp (ofFlat q).continuous))))
  · simp only [flatBaseDrift, Fin.append_right]
    exact continuous_const.mul (continuous_const.sub (continuous_const.mul
      ((continuous_apply j).comp (continuous_snd.comp (ofFlat q).continuous))))

theorem contDiffOn_cauchyH_flat : ContDiffOn ℝ 2 (cauchyH q ∘ ofFlat q) (flatChamber q) :=
  fun w hw => ((contDiffAt_cauchyH_of_mem hw).of_le (by simp)).comp w
    (ofFlat q).contDiff.contDiffAt |>.contDiffWithinAt

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ}
  {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}

/-- Itô's formula for a `C²` function whose generator is `L` on the chamber: the stopped
compensated process has a martingale modification. -/
theorem hasMM_stop_of_generator
    (hZ : IsMPSolutionOn Q 𝓖 (flatBaseDrift D0 q) (flatDiff D0 q) (flatChamber q) Z)
    {φ : (Fin (q + q) → ℝ) → ℝ} (hφ : ContDiffOn ℝ 2 φ (flatChamber q))
    {L : (Fin (q + q) → ℝ) → ℝ}
    (hL : ∀ w ∈ flatChamber q, mpGenerator (flatBaseDrift D0 q) (flatDiff D0 q) φ w = L w)
    {W : Set (Fin (q + q) → ℝ)} (hW : IsInteriorDomain W (flatChamber q)) :
    HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω => φ (Z t ω) - φ (Z 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, L (Z s.toNNReal ω)) (exitTimeFrom W Z)) := by
  obtain ⟨M, hM, hMe⟩ := Semimartingale.martingaleProblemIto_holds (q + q) Ω Q 𝓖
    (flatBaseDrift D0 q) (flatDiff D0 q) (flatChamber q) (isOpen_flatChamber q)
    (continuous_flatBaseDrift D0).continuousOn (contDiff_flatDiff D0).continuous.continuousOn
    Z hZ φ hφ W hW
  refine ⟨M, hM, fun t => (hMe t).trans ?_⟩
  filter_upwards [hZ.continuous] with ω hω
  simp only [stoppedProcess_eq_stopTime]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => hL _ (hW.2.2 ?_)
  exact (Bridges.stopped_path_mem_closure hW.1 hω t).1 s hs

/-- **The density martingale**: `H_q(Z_{t∧τ_W}) − H_q(Z_0)`. -/
theorem hasMM_cauchyH_stop
    (hZ : IsMPSolutionOn Q 𝓖 (flatBaseDrift D0 q) (flatDiff D0 q) (flatChamber q) Z)
    {W : Set (Fin (q + q) → ℝ)} (hW : IsInteriorDomain W (flatChamber q)) :
    HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
      cauchyH q (ofFlat q (Z t ω)) - cauchyH q (ofFlat q (Z 0 ω))) (exitTimeFrom W Z)) := by
  have h := hasMM_stop_of_generator hZ contDiffOn_cauchyH_flat (L := fun _ => 0)
    (fun w hw => mpGenerator_flatBase_cauchyH D0 hw) hW
  simpa using h

/-- **The input of Bayes' rule**: `(H_q f)(Z) − ∫ H_q 𝒟_q f (Z)`, stopped at `τ_W`. -/
theorem hasMM_cauchyH_mul_stop
    (hZ : IsMPSolutionOn Q 𝓖 (flatBaseDrift D0 q) (flatDiff D0 q) (flatChamber q) Z)
    {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f)
    {W : Set (Fin (q + q) → ℝ)} (hW : IsInteriorDomain W (flatChamber q)) :
    HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
      cauchyH q (ofFlat q (Z t ω)) * f (ofFlat q (Z t ω)) -
        cauchyH q (ofFlat q (Z 0 ω)) * f (ofFlat q (Z 0 ω)) -
      ∫ s in Ioc (0 : ℝ) t, cauchyH q (ofFlat q (Z s.toNNReal ω)) *
        dualGenerator D0 f (ofFlat q (Z s.toNNReal ω))) (exitTimeFrom W Z)) := by
  have hφ : ContDiffOn ℝ 2 ((fun z => cauchyH q z * f z) ∘ ofFlat q) (flatChamber q) :=
    fun w hw => (((contDiffAt_cauchyH_of_mem hw).of_le (by simp)).mul hf.contDiffAt).comp w
      (ofFlat q).contDiff.contDiffAt |>.contDiffWithinAt
  exact hasMM_stop_of_generator hZ hφ
    (L := fun w => cauchyH q (ofFlat q w) * dualGenerator D0 f (ofFlat q w))
    (fun w hw => mpGenerator_flatBase_cauchyH_mul D0 hf hw) hW

end BlockBand.Transmission.Dual.G
