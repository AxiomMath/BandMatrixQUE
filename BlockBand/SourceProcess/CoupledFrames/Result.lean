module

public import BlockBand.SourceProcess.CoupledFrames.Holds

/-!
# Coupled cutoff frames

`coupledCutoffFrames_holds`: the coupled cutoff frames `CoupledCutoffFrames` exist. On one driver
space over `S = (ℕ → ℝ) × (π → ℝ)` (`μ = ρ ⊗ Π birthTimeLaw`), the ambient space
`Amb K R` with `R = 5K + 2|π| + 1`: the two extended solutions `Y_j` of the finite source equation
from `[initialFrame(t, h_j) | 1]` with the same noise; the shared birth vectors of the two-frame
selection (`wv`); the born frames `X_j = bornFrame` (`isBornSDESolution_bornFrame`); their Gram
processes are the finite source models (`frame_model`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal ComplexOrder
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.CutoffLimit

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- **`CoupledCutoffFrames` holds.** -/
theorem coupledCutoffFrames_holds : CoupledCutoffFrames := by
  intro b hb0 hb1 E hE1 hE2 s T _ _ p q hq ρ hρ hρseq h₁ h₂ K M hh₁ hh _
  classical
  set n := Fintype.card (Fin p × Fin M)
  let eπ : (Fin p × Fin M) ≃ Fin n := Fintype.equivFin _
  set R := 5 * K + 2 * n + 1
  have hR : 5 * K + 2 * n < R := by omega
  have : ∀ i : Fin p × Fin M, IsProbabilityMeasure (birthTimeLaw s T (q i.1)) :=
    fun i => isProbabilityMeasure_birthTimeLaw (hq i.1)
  set μ := ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have htseq0 : Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0]
      (fun x : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) (SourceNoise (Amb K R)) => x.1.1) :=
    measurable_fst.comp (measurable_fst_driver μ)
  have hseq := ae_seq (κ := SourceNoise (Amb K R))
    (ν := Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1)) hρseq
  have hξm := fun h => stronglyMeasurable_extFrame (R := R) htseq0 h
  have hξc : ∀ h, ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      TwoProjection (ambP K R) (extSig K R) (extFrame K R x.1.1 h) :=
    fun h => hseq.mono fun x hx => twoProjection_extFrame K R (fun k => hx.2.1 k) h
  obtain ⟨Y₁, hY₁⟩ := (SourceSDE.finiteSourceWellPosed_holds μ (transportD0 b E) (K + R)
    (ambP K R) (extSig K R) hD0 (isNearProjection_ambP K R) (isSignature_extSig K R) _ (hξm h₁)
    (hξc h₁)).1
  obtain ⟨Y₂, hY₂⟩ := (SourceSDE.finiteSourceWellPosed_holds μ (transportD0 b E) (K + R)
    (ambP K R) (extSig K R) hD0 (isNearProjection_ambP K R) (isSignature_extSig K R) _ (hξm h₂)
    (hξc h₂)).1
  have hgood : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, GoodRank Y₁ Y₂ x := by
    filter_upwards [ae_rank_of_sol hD0 (hξm h₁) (hξc h₁)
        (fun x => principalMinorSum_extFrame_pos K R _ h₁) hY₁,
      ae_rank_of_sol hD0 (hξm h₂) (hξc h₂) (fun x => principalMinorSum_extFrame_pos K R _ h₂) hY₂]
      with x h1 h2 t
    exact ⟨h1 t, h2 t⟩
  set v : Fin p × Fin M → ℝ := fun i => dStar b * sourceMass s T (q i.1) / M
  have hv : ∀ i, 0 ≤ v i := fun i => v_nonneg hb1 (hq i.1) M
  have hσ := measurable_σs (κ := SourceNoise (Amb K R)) s μ
  have hp₁ := hY₁.1.progressive
  have hp₂ := hY₂.1.progressive
  set w := wv eπ Y₁ Y₂ (σs s) v
  have h0 := ae_birth_zero (b := b) hq (κ := SourceNoise (Amb K R)) ρ (M := M)
  have hw0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ k,
      bτ eπ (σs s) k x = 0 → w k x = 0 := by
    filter_upwards [hgood, h0] with x hx hz k hk
    have h1 := wv_dot eπ (σ' := σs s) hv hR hx k
    have hv0 : v (eπ.symm k) = 0 := hz (eπ.symm k) hk
    rw [hv0, Complex.ofReal_zero] at h1
    exact dotProduct_star_self_eq_zero.1 h1
  have hpv₁ := stronglyMeasurable_pv1 eπ v hp₁ hp₂ hσ
  have hpv₂ := stronglyMeasurable_pv2 eπ v hp₁ hp₂ hσ
  have hw := stronglyMeasurable_wv eπ v hp₁ hp₂ hσ
  have hg₁ : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ k,
      Y₁ (bτ eπ (σs s) k x) x *ᵥ ba eπ (pv1 eπ Y₁ Y₂ (σs s) v) k x = w k x :=
    ae_of_all _ fun x k => wv_eq eπ Y₁ Y₂ (σs s) v k x
  have hg₂ : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ k,
      Y₂ (bτ eπ (σs s) k x) x *ᵥ ba eπ (pv2 eπ Y₁ Y₂ (σs s) v) k x = w k x :=
    hgood.mono fun x hx k => wv_frame₂ eπ hv hR hx k
  refine ⟨Amb K R, (ℕ → ℝ) × (Fin p × Fin M → ℝ), inferInstance, inferInstance, inferInstance, μ,
    inferInstance, K + R, ambP K R, embK K R, driverAugmented (κ := SourceNoise (Amb K R)) μ,
    fun x => x.1.1, fun x => x.1.2, n, bτ eπ (σs s), bcol eπ, w, fun k => v (eπ.symm k),
    bornFrame eπ Y₁ (σs s) (pv1 eπ Y₁ Y₂ (σs s) v) w,
    bornFrame eπ Y₂ (σs s) (pv2 eπ Y₁ Y₂ (σs s) v) w, ?_⟩
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
      birth_total := Equiv.sum_comp eπ.symm v
      sol₁ := by
        rw [cutFrame_eq]
        exact isBornSDESolution_bornFrame eπ hY₁ hσ hpv₁ hw hg₁ hw0
      sol₂ := by
        rw [cutFrame_eq]
        exact isBornSDESolution_bornFrame eπ hY₂ hσ hpv₂ hw hg₂ hw0
      perp := fun k => hgood.mono fun x hx j hj => coupled_perp eπ hv hR hx k j hj
      model₁ := frame_model eπ hb0 hb1 hE1 hE2 hq hρseq hY₁ hpv₁ hw
        (hgood.mono fun x hx => probeSpec₁ eπ hv hR hx) hg₁
      model₂ := frame_model eπ hb0 hb1 hE1 hE2 hq hρseq hY₂ hpv₂ hw
        (hgood.mono fun x hx => probeSpec₂ eπ hv hR hx) hg₂ }

end BlockBand.SourceProcess.CoupledFrames
