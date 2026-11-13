module

public import BlockBand.Transmission.Dual.GHTilt

/-!
# The local Doob identity for a general h-transform

For an h-transform `IsHTransform D₀ q U h b̃`, a base solution `Z` from `z`, and an interior
domain `W ∋ z` of `U`:
* `lemma1_tiltH`: under `P̃ = M_∞ · P`, `Z^{τ_W}` solves the `(b̃, flatDiff)` problem in `W`;
* `lemma1_lawH`: its law is that of any comparison solution stopped at its exit from `W`
  (uniqueness for stopped martingale problems);
* **`lemma1H`**: `Q₂((Y₂^{τ₂})^{t₀} ∈ B) = E_P[h(Z_{t₀∧τ})/h(z); (Z^τ)^{t₀} ∈ B]`.
Same proofs as for `lemma1`, with `h` for `H_q` and `b̃` for the flat dual drift.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}
  {z : Fin (q + q) → ℝ} {W U : Set (Fin (q + q) → ℝ)} {h : (Fin (q + q) → ℝ) → ℝ}
  {bt : (Fin (q + q) → ℝ) → Fin (q + q) → ℝ}

theorem exists_bound_closureU {F : (Fin (q + q) → ℝ) → ℝ} (hF : Continuous F)
    (hW : IsInteriorDomain W U) : ∃ B, 0 ≤ B ∧ ∀ w ∈ closure W, |F w| ≤ B := by
  obtain ⟨B, hB⟩ := hW.2.1.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun w hw =>
    (Real.norm_eq_abs _ ▸ hB w hw).trans (le_max_left _ _)⟩

theorem IsHTransform.continuous_gen (hh : IsHTransform D0 q U h bt) {φ : (Fin (q + q) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφs : tsupport φ ⊆ U) :
    Continuous (mpGenerator bt (flatDiff D0 q) φ) :=
  continuous_mpGenerator hh.isOpen hh.continuousOn_bt
    (contDiff_flatDiff D0).continuous.continuousOn hφ hφs

/-- **`X M` has a `P`-martingale modification** (general h-transform). -/
theorem hasMM_testMart_mulH (hh : IsHTransform D0 q U h bt) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W U) (hzW : z ∈ W) {φ : (Fin (q + q) → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : tsupport φ ⊆ W) :
    HasMartingaleModification P 𝓖 (fun t ω =>
      testMart bt (flatDiff D0 q) φ (stopZ W Z) t ω * densH h W Z z t ω) := by
  have hφU : tsupport φ ⊆ U := hφs.trans (subset_closure.trans hW.2.2)
  have h1 := hasMM_stop_base hZ hh.isOpen (φ := fun w => h w * φ w)
    (hh.smooth.mul hφ.contDiffOn) (hh.transform φ hφ) hW
  have h2 : HasMartingaleModification P 𝓖 (stoppedProcess (fun t ω => h (Z t ω) - h (Z 0 ω))
      (exitTimeFrom W Z)) := by
    simpa using hasMM_stop_base hZ hh.isOpen hh.smooth hh.harm hW
  have hLc := hh.continuous_gen hφ hφU
  obtain ⟨B, -, hB⟩ := exists_bound_closureU hLc hW
  obtain ⟨C, hC⟩ := exists_bound_h hh hW
  have hX' : HasMartingaleModification P 𝓖 (fun t ω => h (stopZ W Z t ω)) := by
    obtain ⟨N, hN, hNe⟩ := h2
    refine ⟨N + fun _ _ => h z, hN.add (martingale_const 𝓖 P _), fun t => ?_⟩
    filter_upwards [hNe t] with ω hω
    simp [hω, stoppedProcess_eq_stopTime, hZ.start, stopZ]
  have hcont : ∀ ω, Continuous fun t => h (stopZ W Z t ω) := fun ω =>
    hh.smooth.continuousOn.comp_continuous (continuous_stopZ hZ ω)
      fun t => hW.2.2 (stopZ_mem_closure hZ hW.1 hzW t ω)
  have hprog : IsStronglyProgressive 𝓖 (fun t ω => mpGenerator bt (flatDiff D0 q) φ
      (stopZ W Z t ω)) := fun t =>
    hLc.comp_stronglyMeasurable (isStronglyProgressive_stopZ hZ hW.1 t)
  have h3 := hasMartingaleModification_ibp hX' (Eventually.of_forall hcont)
    (fun _ => ⟨C, Eventually.of_forall fun ω t _ => by
      have h' := hC _ (stopZ_mem_closure hZ hW.1 hzW t ω)
      rw [abs_of_pos h'.1]; exact h'.2⟩)
    (β := fun t ω => mpGenerator bt (flatDiff D0 q) φ (stopZ W Z t ω))
    (fun t ω => hB _ (stopZ_mem_closure hZ hW.1 hzW t ω))
    (Eventually.of_forall fun ω =>
      (hLc.comp ((continuous_stopZ hZ ω).comp continuous_real_toNNReal)).measurable)
    (A := fun t ω => ∫ s in Ioc (0 : ℝ) t, mpGenerator bt (flatDiff D0 q) φ
      (stopZ W Z s.toNNReal ω)) (fun _ _ => rfl)
    (fun t => (SemimartingaleIto.stronglyMeasurable_integral_of_progressive hprog t
      ).aestronglyMeasurable)
  have h2' := hasMM_const_mul h2 (ξ := fun _ => φ z) stronglyMeasurable_const
    (c := |φ z|) fun _ => le_rfl
  have hc := hasMM_const_mul (hasMM_sub (hasMM_sub h1 h2') h3) (ξ := fun _ => (h z)⁻¹)
    stronglyMeasurable_const (c := |(h z)⁻¹|) fun _ => le_rfl
  refine hasMM_congr hc fun t => Eventually.of_forall fun ω => ?_
  exact (testMart_mul_densH hZ hW.1 hφs t ω).symm

/-- **The tilt of a general h-transform.** -/
theorem lemma1_tiltH (hh : IsHTransform D0 q U h bt) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W U) (hzW : z ∈ W) : ∃ (M : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0),
      IsDensity P 𝓖 M g ∧ (∀ t, M t =ᵐ[P] densH h W Z z t) ∧ IsProbabilityMeasure (tilt P g) ∧
      IsMPSolutionOn (tilt P g) 𝓖 bt (flatDiff D0 q) W (stopZ W Z) := by
  obtain ⟨M, g, hg, hMe, hprob⟩ := exists_tiltH hh hZ hW hzW
  refine ⟨M, g, hg, hMe, hprob, ?_⟩
  refine isMPSolutionOn_of_test hW.1 (hh.continuousOn_bt.mono (subset_closure.trans hW.2.2))
    (contDiff_flatDiff D0).continuous.continuousOn
    (fun w _ i j => flatDiff_symm D0 w i j) ⟨stronglyMeasurable_stopZ hZ hW.1,
      Eventually.of_forall (continuous_stopZ hZ), fun φ hφ _ hφs => ?_⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  refine hg.hasMM_tilt (fun t => ?_) (hasMM_congr (hasMM_testMart_mulH hh hZ hW hzW hφ2 hφs)
    fun t => by filter_upwards [hMe t] with ω hω; rw [hω])
  obtain ⟨B, -, hB⟩ := exists_bound_closureU
    (hh.continuous_gen hφ2 (hφs.trans (subset_closure.trans hW.2.2))) hW
  obtain ⟨Cφ, -, hCφ⟩ := exists_bound_closureU hφ2.continuous hW
  refine ⟨Cφ + Cφ + B * t, Eventually.of_forall fun ω => ?_⟩
  have hi := abs_setIntegral_Ioc_le (f := fun u : ℝ => mpGenerator bt (flatDiff D0 q) φ
    (stopZ W Z u.toNNReal ω)) (fun u => hB _ (stopZ_mem_closure hZ hW.1 hzW _ ω)) t
  have ha := hCφ _ (stopZ_mem_closure hZ hW.1 hzW t ω)
  have hb := hCφ _ (stopZ_mem_closure hZ hW.1 hzW 0 ω)
  unfold testMart
  calc _ ≤ |φ (stopZ W Z t ω)| + |φ (stopZ W Z 0 ω)| +
        |∫ u in Ioc (0 : ℝ) t, mpGenerator bt (flatDiff D0 q) φ (stopZ W Z u.toNNReal ω)| :=
          (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ _ := by linarith

/-- **The local Doob identity, law form, for a general h-transform.** -/
theorem lemma1_lawH (hD0 : 0 < D0) (hh : IsHTransform D0 q U h bt)
    (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsInteriorDomain W U) (hzW : z ∈ W) {Ω₂ : Type}
    [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}
    (h₂ : IsMPSolutionOn Q₂ 𝓗 bt (flatDiff D0 q) W Y₂) (h₂0 : Q₂.map (Y₂ 0) = Measure.dirac z) :
    ∃ (M : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0), IsDensity P 𝓖 M g ∧
      (∀ t, M t =ᵐ[P] densH h W Z z t) ∧ IsProbabilityMeasure (tilt P g) ∧
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω) =
        (tilt P g).map (fun ω t => stopZ W Z t ω) := by
  obtain ⟨M, g, hg, hMe, hprob, hsol⟩ := lemma1_tiltH hh hZ hW hzW
  refine ⟨M, g, hg, hMe, hprob, ?_⟩
  have h0 : (tilt P g).map (stopZ W Z 0) = Q₂.map (Y₂ 0) := by
    have e : stopZ W Z 0 = fun _ => z := funext fun ω => by
      rw [stopZ, stoppedProcess_eq_stopTime, Semimartingale.stopTime_zero, hZ.start]
    rw [e, h₂0, Measure.map_const, measure_univ, one_smul]
  have hfull := stoppedMartingaleProblemUniquenessPosDef_holds (q + q) bt (flatDiff D0 q) U W
    hh.isOpen hh.lip ((contDiffOn_flatDiff D0).mono hh.sub)
    (fun w hw => flatDiff_posDef hD0 (hh.sub hw)) hW Ω (tilt P g) 𝓖 (stopZ W Z) Ω₂ Q₂ 𝓗 Y₂ hsol
    h₂ h0
  rw [← hfull, stoppedProcess_stopZ hZ hW.1]

/-- **The local Doob identity for a general h-transform.** -/
theorem lemma1H (hD0 : 0 < D0) (hh : IsHTransform D0 q U h bt)
    (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsInteriorDomain W U) (hzW : z ∈ W) {Ω₂ : Type}
    [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}
    (h₂ : IsMPSolutionOn Q₂ 𝓗 bt (flatDiff D0 q) W Y₂) (h₂0 : Q₂.map (Y₂ 0) = Measure.dirac z)
    (t₀ : ℝ≥0) {B : Set (ℝ≥0 → Fin (q + q) → ℝ)} (hB : MeasurableSet B) :
    Q₂.real {ω | (fun t => stoppedProcess Y₂ (exitTimeFrom W Y₂) (min t t₀) ω) ∈ B} =
      ∫ ω in {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B}, densH h W Z z t₀ ω ∂P := by
  obtain ⟨M, g, hg, hMe, hprob, hlaw⟩ := lemma1_lawH hD0 hh hZ hW hzW h₂ h₂0
  have hTB := measurable_truncate (q := q) t₀ hB
  have hY₂m : AEMeasurable (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω) Q₂ :=
    aemeasurable_stopped (fun t => (h₂.adapted t).measurable) h₂.continuous hW.1
  have hZm : Measurable fun ω t => stopZ W Z t ω :=
    Measurable.of_eval fun t => (stronglyMeasurable_stopZ hZ hW.1 t).measurable.mono
      (𝓖.le t) le_rfl
  have hS : MeasurableSet[𝓖 t₀] {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B} :=
    measurable_stopZ_path hZ hW.1 t₀ hB
  have e1 : Q₂ {ω | (fun t => stoppedProcess Y₂ (exitTimeFrom W Y₂) (min t t₀) ω) ∈ B} =
      tilt P g {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B} := by
    have := congrArg (fun μ : Measure (ℝ≥0 → Fin (q + q) → ℝ) =>
      μ ((fun (w : ℝ≥0 → Fin (q + q) → ℝ) t => w (min t t₀)) ⁻¹' B)) hlaw
    rwa [Measure.map_apply_of_aemeasurable hY₂m hTB, Measure.map_apply hZm hTB] at this
  have e2 := hg.setIntegral_tilt_eq (f := fun _ => (1 : ℝ)) stronglyMeasurable_const (C := 1)
    (Eventually.of_forall fun _ => by simp) hS
  rw [setIntegral_const, smul_eq_mul, mul_one] at e2
  rw [measureReal_def, e1, ← measureReal_def, e2]
  refine setIntegral_congr_ae (𝓖.le t₀ _ hS) ?_
  filter_upwards [hMe t₀] with ω hω _
  rw [mul_one, hω]

end BlockBand.Transmission.Dual.G
