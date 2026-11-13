module

public import BlockBand.Transmission.Dual.GLemma1Stop
public import BlockBand.Transmission.Dual.MPConverse
public import BlockBand.Transmission.Dual.MPConverseIBP

/-!
# The local Doob identity: under the tilted measure the stopped path solves the dual problem

For `φ ∈ C_c^∞` with `tsupport φ ⊆ W`, write `Y = Z^τ`, `L = 𝓛φ` (the flat dual generator),
`X_t = φ(Y_t) − φ(z) − ∫_0^t L(Y_s) ds` (`testMart`), and `H = H_q`. Pathwise
(`testMart_mul_densM`): `H(z) X_t M_t = I1_t − φ(z) I2_t − I3_t`, with
* `I1 = (Hφ)(Y) − (Hφ)(z) − ∫_0^{t∧τ} H L (Z)` (`hasMM_cauchyH_mul_stop`, `𝓛⁰(Hf) = H𝒟f`),
* `I2 = H(Y) − H(z)` (`hasMM_cauchyH_stop`),
* `I3 = A_t H(Y_t) − ∫_0^t L(Y_s) H(Y_s) ds`, `A_t = ∫_0^t L(Y)` (`hasMartingaleModification_ibp`).
So `X M` has a `P`-martingale modification (`hasMM_testMart_mul`); by Bayes (`hasMM_tilt`) `X` has
one under `P̃`, and the converse `isMPSolutionOn_of_test` gives **`lemma1_tilt`**: under `P̃`,
`Z^τ` solves the flat dual martingale problem in `W`, for all times.
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

variable {q : ℕ} {D0 : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}
  {z : Fin (q + q) → ℝ} {W : Set (Fin (q + q) → ℝ)}

/-- The flat dual generator. -/
abbrev Lq (D0 : ℝ) (q : ℕ) (φ : (Fin (q + q) → ℝ) → ℝ) : (Fin (q + q) → ℝ) → ℝ :=
  mpGenerator (flatDrift D0 q) (flatDiff D0 q) φ

theorem Lq_eq_zero {φ : (Fin (q + q) → ℝ) → ℝ} {w : Fin (q + q) → ℝ} (hw : w ∉ tsupport φ) :
    Lq D0 q φ w = 0 := by
  rw [Lq, mpGenerator_congr (notMem_tsupport_iff_eventuallyEq.1 hw)]
  simp [mpGenerator]

theorem comp_flatHomeo (φ : (Fin (q + q) → ℝ) → ℝ) : (φ ∘ flatHomeo q) ∘ ofFlat q = φ :=
  funext fun w => congrArg φ ((flatHomeo q).apply_symm_apply w)

/-- **The pathwise identity** `H(z) X_t M_t = I1 − φ(z) I2 − I3`. -/
theorem testMart_mul_densM (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W)
    {φ : (Fin (q + q) → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : tsupport φ ⊆ W) (t : ℝ≥0) (ω : Ω) :
    testMart (flatDrift D0 q) (flatDiff D0 q) φ (stopZ W Z) t ω * densM W Z z t ω =
      (flatH q z)⁻¹ * (stoppedProcess (fun t ω =>
        cauchyH q (ofFlat q (Z t ω)) * (φ ∘ flatHomeo q) (ofFlat q (Z t ω)) -
          cauchyH q (ofFlat q (Z 0 ω)) * (φ ∘ flatHomeo q) (ofFlat q (Z 0 ω)) -
        ∫ s in Ioc (0 : ℝ) t, cauchyH q (ofFlat q (Z s.toNNReal ω)) *
          dualGenerator D0 (φ ∘ flatHomeo q) (ofFlat q (Z s.toNNReal ω))) (exitTimeFrom W Z) t ω -
        φ z * stoppedProcess (fun t ω => cauchyH q (ofFlat q (Z t ω)) -
          cauchyH q (ofFlat q (Z 0 ω))) (exitTimeFrom W Z) t ω -
        ((∫ s in Ioc (0 : ℝ) t, Lq D0 q φ (stopZ W Z s.toNNReal ω)) *
            flatH q (stopZ W Z t ω) -
          ∫ s in Ioc (0 : ℝ) t, Lq D0 q φ (stopZ W Z s.toNNReal ω) *
            flatH q (stopZ W Z s.toNNReal ω))) := by
  have hf : ContDiff ℝ 2 (φ ∘ flatHomeo q) := hφ.comp (contDiff_flatHomeo.of_le (by simp))
  have hgen : ∀ w, dualGenerator D0 (φ ∘ flatHomeo q) (ofFlat q w) = Lq D0 q φ w := fun w => by
    rw [Lq, ← mpGenerator_flat D0 hf w, comp_flatHomeo]
  have hval : ∀ w, (φ ∘ flatHomeo q) (ofFlat q w) = φ w := fun w =>
    congrFun (comp_flatHomeo φ) w
  have hvan : ∀ w ∉ W, flatH q w * Lq D0 q φ w = 0 := fun w hw => by
    rw [Lq_eq_zero (fun h => hw (hφs h)), mul_zero]
  have hI := integral_stopZ hZ hW hvan t ω
  simp only [stoppedProcess_eq_stopTime, hval, hgen, hZ.start]
  simp only [flatH] at hI ⊢
  rw [← hI]
  have e0 : stopZ W Z 0 ω = z := by
    rw [stopZ, stoppedProcess_eq_stopTime, Semimartingale.stopTime_zero, hZ.start]
  have e1 : ∫ s in Ioc (0 : ℝ) t, Lq D0 q φ (stopZ W Z s.toNNReal ω) *
      cauchyH q (ofFlat q (stopZ W Z s.toNNReal ω)) = ∫ s in Ioc (0 : ℝ) t,
      cauchyH q (ofFlat q (stopZ W Z s.toNNReal ω)) * Lq D0 q φ (stopZ W Z s.toNNReal ω) :=
    setIntegral_congr_fun measurableSet_Ioc fun s _ => mul_comm _ _
  rw [e1]
  unfold testMart densM flatH
  rw [e0]
  simp only [stopZ, stoppedProcess_eq_stopTime]
  by_cases hz : cauchyH q (ofFlat q z) = 0
  · simp [hz]
  · field_simp
    ring

theorem exists_bound_closure {F : (Fin (q + q) → ℝ) → ℝ} (hF : Continuous F)
    (hW : IsInteriorDomain W (flatChamber q)) : ∃ B, 0 ≤ B ∧ ∀ w ∈ closure W, |F w| ≤ B := by
  obtain ⟨B, hB⟩ := hW.2.1.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun w hw =>
    (Real.norm_eq_abs _ ▸ hB w hw).trans (le_max_left _ _)⟩

theorem continuous_Lq {φ : (Fin (q + q) → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : tsupport φ ⊆ W) (hW : IsInteriorDomain W (flatChamber q)) : Continuous (Lq D0 q φ) :=
  continuous_mpGenerator (isOpen_flatChamber q) (continuousOn_flatDrift D0)
    (contDiff_flatDiff D0).continuous.continuousOn hφ (hφs.trans (subset_closure.trans hW.2.2))

theorem continuous_flatH_stopZ (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber q)) (hzW : z ∈ W) (ω : Ω) :
    Continuous fun t => flatH q (stopZ W Z t ω) :=
  contDiffOn_cauchyH_flat.continuousOn.comp_continuous (continuous_stopZ hZ ω)
    fun t => hW.2.2 (stopZ_mem_closure hZ hW.1 hzW t ω)

variable [IsProbabilityMeasure P]

/-- **`X M` has a `P`-martingale modification.** -/
theorem hasMM_testMart_mul (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsInteriorDomain W (flatChamber q))
    (hzW : z ∈ W) {φ : (Fin (q + q) → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : tsupport φ ⊆ W) :
    HasMartingaleModification P 𝓖 (fun t ω =>
      testMart (flatDrift D0 q) (flatDiff D0 q) φ (stopZ W Z) t ω * densM W Z z t ω) := by
  have hf : ContDiff ℝ 2 (φ ∘ flatHomeo q) := hφ.comp (contDiff_flatHomeo.of_le (by simp))
  have h1 := hasMM_cauchyH_mul_stop hZ.chamber hf hW
  have h2 := hasMM_cauchyH_stop hZ.chamber hW
  have hLc := continuous_Lq (D0 := D0) hφ hφs hW
  obtain ⟨B, -, hB⟩ := exists_bound_closure hLc hW
  obtain ⟨C, hC⟩ := exists_bound_flatH hW
  have hX' : HasMartingaleModification P 𝓖 (fun t ω => flatH q (stopZ W Z t ω)) := by
    obtain ⟨N, hN, hNe⟩ := h2
    refine ⟨N + fun _ _ => flatH q z, hN.add (martingale_const 𝓖 P _), fun t => ?_⟩
    filter_upwards [hNe t] with ω hω
    simp [hω, stoppedProcess_eq_stopTime, hZ.start, stopZ, flatH]
  have hprog : IsStronglyProgressive 𝓖 (fun t ω => Lq D0 q φ (stopZ W Z t ω)) := fun t =>
    hLc.comp_stronglyMeasurable (isStronglyProgressive_stopZ hZ hW.1 t)
  have h3 := hasMartingaleModification_ibp hX'
    (Eventually.of_forall fun ω => continuous_flatH_stopZ hZ hW hzW ω)
    (fun _ => ⟨C, Eventually.of_forall fun ω t _ => by
      have h := hC _ (stopZ_mem_closure hZ hW.1 hzW t ω)
      rw [abs_of_pos h.1]; exact h.2⟩)
    (β := fun t ω => Lq D0 q φ (stopZ W Z t ω))
    (fun t ω => hB _ (stopZ_mem_closure hZ hW.1 hzW t ω))
    (Eventually.of_forall fun ω =>
      (hLc.comp ((continuous_stopZ hZ ω).comp continuous_real_toNNReal)).measurable)
    (A := fun t ω => ∫ s in Ioc (0 : ℝ) t, Lq D0 q φ (stopZ W Z s.toNNReal ω)) (fun _ _ => rfl)
    (fun t => (SemimartingaleIto.stronglyMeasurable_integral_of_progressive hprog t
      ).aestronglyMeasurable)
  have h2' := hasMM_const_mul h2 (ξ := fun _ => φ z) stronglyMeasurable_const
    (c := |φ z|) fun _ => le_rfl
  have hc := hasMM_const_mul (hasMM_sub (hasMM_sub h1 h2') h3) (ξ := fun _ => (flatH q z)⁻¹)
    stronglyMeasurable_const (c := |(flatH q z)⁻¹|) fun _ => le_rfl
  refine hasMM_congr hc fun t => Eventually.of_forall fun ω => ?_
  exact (testMart_mul_densM hZ hW.1 hφ hφs t ω).symm

/-- **The tilt**: under `P̃ = M_∞ · P`, the stopped base path solves the flat dual
martingale problem in `W` for all times. -/
theorem lemma1_tilt (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsInteriorDomain W (flatChamber q))
    (hzW : z ∈ W) : ∃ (M : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0), IsDensity P 𝓖 M g ∧
      (∀ t, M t =ᵐ[P] densM W Z z t) ∧ IsProbabilityMeasure (tilt P g) ∧
      IsMPSolutionOn (tilt P g) 𝓖 (flatDrift D0 q) (flatDiff D0 q) W (stopZ W Z) := by
  obtain ⟨M, g, hg, hMe, hprob⟩ := exists_tilt hZ hW hzW
  refine ⟨M, g, hg, hMe, hprob, ?_⟩
  refine isMPSolutionOn_of_test hW.1 ((continuousOn_flatDrift D0).mono
    (subset_closure.trans hW.2.2)) (contDiff_flatDiff D0).continuous.continuousOn
    (fun w _ i j => flatDiff_symm D0 w i j) ⟨stronglyMeasurable_stopZ hZ hW.1,
      Eventually.of_forall (continuous_stopZ hZ), fun φ hφ _ hφs => ?_⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  refine hg.hasMM_tilt (fun t => ?_) (hasMM_congr (hasMM_testMart_mul hZ hW hzW hφ2 hφs)
    fun t => by filter_upwards [hMe t] with ω hω; rw [hω])
  obtain ⟨B, -, hB⟩ := exists_bound_closure (continuous_Lq (D0 := D0) hφ2 hφs hW) hW
  obtain ⟨Cφ, -, hCφ⟩ := exists_bound_closure hφ2.continuous hW
  refine ⟨Cφ + Cφ + B * t, Eventually.of_forall fun ω => ?_⟩
  have hi := abs_setIntegral_Ioc_le (f := fun u : ℝ => Lq D0 q φ (stopZ W Z u.toNNReal ω))
    (fun u => hB _ (stopZ_mem_closure hZ hW.1 hzW _ ω)) t
  have ha := hCφ _ (stopZ_mem_closure hZ hW.1 hzW t ω)
  have hb := hCφ _ (stopZ_mem_closure hZ hW.1 hzW 0 ω)
  unfold testMart
  calc _ ≤ |φ (stopZ W Z t ω)| + |φ (stopZ W Z 0 ω)| +
        |∫ u in Ioc (0 : ℝ) t, Lq D0 q φ (stopZ W Z u.toNNReal ω)| :=
          (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ _ := by linarith

end BlockBand.Transmission.Dual.G
