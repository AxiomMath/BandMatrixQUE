module

public import BlockBand.SourceProcess.ComplexCoupled.FrameK
public import BlockBand.SourceProcess.CoupledFrames.Holds

/-!
# `CoupledComplexCutoff` holds

`coupledComplexCutoff_holds : CoupledComplexCutoff`, with no hypotheses. Construction: the
coupled-frames construction (`CoupledFrames`) with **deterministic** probe births, run on the
driver space over `S = ℕ → ℝ` with law `ρ`: ambient `Amb K R`, `R = 5K + 2np + 1`; the two
extended solutions `Y₁, Y₂` from `[initialFrame(t, h_i) | 1]` with the same noise; the two-frame
selection at the times `σ_j = τ_j - s > 0` with squared norms `d_* m_j`; born frames
`X_i = bornFrame Y_i`. The `𝒦` part is `frame_complex` for each frame: `ambientKIntegral_holds`
at `Y_i` (same driver space, same noise) and its born increment.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.CoupledFrames
open BlockBand.SourceProcess.ComplexCutoff BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **`CoupledComplexCutoff` holds.** -/
theorem coupledComplexCutoff_holds : CoupledComplexCutoff := by
  intro b E np τ m T hD s hs hsτ ρ hρ hρseq h₁ h₂ K hh₁ hh
  obtain ⟨hb0, hb1, hE1, hE2, -, -, hm, -⟩ := hD
  classical
  set R := 5 * K + 2 * np + 1
  have hR : 5 * K + 2 * np < R := by omega
  let eπ : Fin np ≃ Fin np := Equiv.refl (Fin np)
  let κ := SourceNoise (Amb K R)
  let tq : DriverSample (ℕ → ℝ) κ → ℕ → ℝ := fun x => x.1
  have htq : Measurable[driverAugmented (κ := κ) ρ 0] tq := measurable_fst_driver ρ
  have hseq : ∀ᵐ x ∂driverLaw (κ := κ) ρ, IsTransmissionSequence (tq x) :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [map_fst_driverLaw]; exact hρseq)
  have hlaw : (driverLaw (κ := κ) ρ).map (fun x => seqTraceMeasure (tq x)) =
      ρ.map seqTraceMeasure := by
    rw [show (fun x => seqTraceMeasure (tq x)) =
        seqTraceMeasure ∘ (fun x : DriverSample (ℕ → ℝ) κ => x.1) from rfl,
      ← Measure.map_map measurable_seqTraceMeasure measurable_fst, map_fst_driverLaw]
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hξm := fun h => stronglyMeasurable_extFrame (R := R) htq h
  have hξc : ∀ h, ∀ᵐ x ∂driverLaw (κ := κ) ρ,
      TwoProjection (ambP K R) (extSig K R) (extFrame K R (tq x) h) :=
    fun h => hseq.mono fun x hx => twoProjection_extFrame K R (fun k => hx.2.1 k) h
  obtain ⟨Y₁, hY₁⟩ := (SourceSDE.finiteSourceWellPosed_holds ρ (transportD0 b E) (K + R)
    (ambP K R) (extSig K R) hD0 (isNearProjection_ambP K R) (isSignature_extSig K R) _ (hξm h₁)
    (hξc h₁)).1
  obtain ⟨Y₂, hY₂⟩ := (SourceSDE.finiteSourceWellPosed_holds ρ (transportD0 b E) (K + R)
    (ambP K R) (extSig K R) hD0 (isNearProjection_ambP K R) (isSignature_extSig K R) _ (hξm h₂)
    (hξc h₂)).1
  have hgood : ∀ᵐ x ∂driverLaw (κ := κ) ρ, GoodRank Y₁ Y₂ x := by
    filter_upwards [ae_rank_of_sol hD0 (hξm h₁) (hξc h₁)
        (fun x => principalMinorSum_extFrame_pos K R _ h₁) hY₁,
      ae_rank_of_sol hD0 (hξm h₂) (hξc h₂) (fun x => principalMinorSum_extFrame_pos K R _ h₂) hY₂]
      with x h1 h2 t
    exact ⟨h1 t, h2 t⟩
  set v : Fin np → ℝ := fun j => dStar b * m j
  have hv : ∀ j, 0 ≤ v j := fun j => mul_nonneg (dStar_pos hb1).le (hm j)
  have hσ := measurable_sigD (μ := ρ) (K := K) (R := R) s τ
  have hp₁ := hY₁.1.progressive
  have hp₂ := hY₂.1.progressive
  set w := wv eπ Y₁ Y₂ (sigD s τ) v
  set pv₁ := pv1 eπ Y₁ Y₂ (sigD s τ) v
  set pv₂ := pv2 eπ Y₁ Y₂ (sigD s τ) v
  have hpv₁ := stronglyMeasurable_pv1 eπ v hp₁ hp₂ hσ
  have hpv₂ := stronglyMeasurable_pv2 eπ v hp₁ hp₂ hσ
  have hw := stronglyMeasurable_wv eπ v hp₁ hp₂ hσ
  have hg₁ : ∀ᵐ x ∂driverLaw (κ := κ) ρ, ∀ k,
      Y₁ (bτ eπ (sigD s τ) k x) x *ᵥ ba eπ pv₁ k x = w k x :=
    ae_of_all _ fun x k => wv_eq eπ Y₁ Y₂ (sigD s τ) v k x
  have hg₂ : ∀ᵐ x ∂driverLaw (κ := κ) ρ, ∀ k,
      Y₂ (bτ eπ (sigD s τ) k x) x *ᵥ ba eπ pv₂ k x = w k x :=
    hgood.mono fun x hx k => wv_frame₂ eπ hv hR hx k
  have hw0 : ∀ᵐ x ∂driverLaw (κ := κ) ρ, ∀ k, bτ eπ (sigD s τ) k x = 0 → w k x = 0 :=
    ae_of_all _ fun x k hk => by
      have : τ k - s ≤ 0 := Real.toNNReal_eq_zero.1 hk
      linarith [hsτ k]
  have H₁ : FrameHyp b E s h₁ τ m ρ tq Y₁ pv₁ w :=
    ⟨htq, hseq, hY₁, hpv₁, hw, hg₁, hgood.mono fun x hx => probeSpec₁ eπ hv hR hx⟩
  have H₂ : FrameHyp b E s h₂ τ m ρ tq Y₂ pv₂ w :=
    ⟨htq, hseq, hY₂, hpv₂, hw, hg₂, hgood.mono fun x hx => probeSpec₂ eπ hv hR hx⟩
  obtain ⟨Yb₁, hK₁, hM₁⟩ := frame_complex H₁ hb0 hb1 hE1 hE2 hm hsτ hlaw
  obtain ⟨Yb₂, hK₂, hM₂⟩ := frame_complex H₂ hb0 hb1 hE1 hE2 hm hsτ hlaw
  refine ⟨Amb K R, ℕ → ℝ, inferInstance, inferInstance, inferInstance, ρ, hρ, K + R, ambP K R,
    embK K R, driverAugmented (κ := κ) ρ, tq, np, bτ eπ (sigD s τ), bcol eπ, w, v,
    bFr s τ Y₁ pv₁ w, bFr s τ Y₂ pv₂ w, Yb₁, Yb₂, ?_⟩
  exact
    { nearProj := isNearProjection_ambP K R
      isometry := embK_isometry K R
      frame₁_meas := by
        rw [cutFrame_eq]
        exact (continuous_id.matrix_mul continuous_const).comp_stronglyMeasurable (hξm h₁)
      frame₂_meas := by
        rw [cutFrame_eq]
        exact (continuous_id.matrix_mul continuous_const).comp_stronglyMeasurable (hξm h₂)
      frame₁_two := hseq.mono fun x hx => twoProjection_cutFrame K R _ (fun k => hx.2.1 k) h₁
      frame₂_two := hseq.mono fun x hx => twoProjection_cutFrame K R _ (fun k => hx.2.1 k) h₂
      stopping := fun k => isStoppingTime_of_meas0 (hσ (eπ.symm k)).real_toNNReal
      birth_meas := hw
      col_inj := fun k k' e => eπ.symm.injective (Sum.inr_injective e)
      col_sig := fun k j => srcSignature_col _ j
      col_zero := fun k => ae_of_all _ fun x r => ⟨cutFrame_col _ _ x r _, cutFrame_col _ _ x r _⟩
      birth_near := fun k => hgood.mono fun x hx => ⟨wv_near eπ hv hR hx k, wv_norm eπ hv hR hx k⟩
      birth_total := rfl
      sol₁ := by
        rw [cutFrame_eq]
        exact isBornSDESolution_bornFrame eπ hY₁ hσ hpv₁ hw hg₁ hw0
      sol₂ := by
        rw [cutFrame_eq]
        exact isBornSDESolution_bornFrame eπ hY₂ hσ hpv₂ hw hg₂ hw0
      perp := fun k => hgood.mono fun x hx j hj => coupled_perp eπ hv hR hx k j hj
      kSol₁ := hK₁
      kSol₂ := hK₂
      model₁ := hM₁
      model₂ := hM₂ }

end BlockBand.SourceProcess.ComplexCoupled
