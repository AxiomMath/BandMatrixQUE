module

public import BlockBand.Transmission.PassiveCovariance.LayerIBP

/-!
# Bond IBP on the layer with derivatives only at Hermitian blocks

The diagonal block of a layer sample is almost surely Hermitian, so the bond integration by parts
`stein_layerB` only needs the derivatives at samples with Hermitian block (`stein_layerB_herm`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

theorem measurableSet_isHermitian {n : Type*} [Fintype n] :
    MeasurableSet {A : Matrix n n ℂ | A.IsHermitian} :=
  (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet

theorem ae_isHermitian_gue (n : ℕ) (t : ℝ≥0) : ∀ᵐ A ∂gueMeasure (Fin n) t, A.IsHermitian := by
  rw [BlockBand.Transmission.Bridge.gueMeasure_eq_map, ae_map_iff
    (BlockBand.Transmission.Bridge.measurable_gueRaw n t).aemeasurable measurableSet_isHermitian]
  exact Filter.Eventually.of_forall fun ρ => gueRaw_isHermitian t ρ

theorem ae_isHermitian_pi (n : ℕ) (t : ℝ≥0) :
    ∀ᵐ ω₁ ∂(Measure.pi fun _ : Fin 1 => gueMeasure (Fin n) t), (ω₁ 0).IsHermitian :=
  (measurePreserving_eval (fun _ : Fin 1 => gueMeasure (Fin n) t) 0).quasiMeasurePreserving.ae
    (ae_isHermitian_gue n t)

/-- `stein_layerB` with derivatives required only at samples with Hermitian block. -/
theorem stein_layerB_herm {W : ℕ} (b : ℝ) (Φ Φa Φb : LayerSample W .oneBlockOnePort → ℂ)
    (x y : Fin W) (hm : Measurable Φ)
    (ha : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian → HasDerivAt
      (fun s : ℝ => Φ (ω.1, fun i j => ω.2 i j + (s : ℂ) • Matrix.single x y 1)) (Φa ω) 0)
    (hb : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian → HasDerivAt
      (fun s : ℝ => Φ (ω.1, fun i j => ω.2 i j + ((s : ℂ) * Complex.I) • Matrix.single x y 1))
      (Φb ω) 0)
    (hΦ : MemLp Φ 2 (layerLaw W b .oneBlockOnePort))
    (hΦa : Integrable Φa (layerLaw W b .oneBlockOnePort))
    (hΦb : Integrable Φb (layerLaw W b .oneBlockOnePort)) :
    ∫ ω, ω.2 0 0 x y * Φ ω ∂layerLaw W b .oneBlockOnePort =
      (ginVar W b : ℂ) * ∫ ω, (Φa ω + Complex.I * Φb ω) / 2 ∂layerLaw W b .oneBlockOnePort := by
  set μA := Measure.pi fun _ : Fin 1 => gueMeasure (Fin W) (gueVar W b)
  set μB := Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
    ginibreMeasure (Fin W) (Fin W) (ginVar W b)
  have hL : layerLaw W b .oneBlockOnePort = μA.prod μB := rfl
  rw [hL] at hΦ hΦa hΦb ⊢
  have hent : MemLp (fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 x y) 2 (μA.prod μB) :=
    (((memLp_ginibre_entry (ginVar W b) x y).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 1 => ginibreMeasure (Fin W) (Fin W) (ginVar W b)) 0)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (ginVar W b)) 0)).comp_measurePreserving
      (measurePreserving_snd (μ := μA) (ν := μB))
  have hf : Integrable (fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 x y * Φ ω) (μA.prod μB) :=
    hent.integrable_mul hΦ
  rw [← integral_const_mul]
  refine integral_prod_eq_of_ae_snd _ _ hf (((hΦa.add (hΦb.const_mul _)).div_const _).const_mul _) ?_
  filter_upwards [memLp_two_section_snd hm hΦ, hΦa.prod_right_ae, hΦb.prod_right_ae,
    ae_isHermitian_pi W (gueVar W b)] with ω₁ h0 h1 h2 hH
  rw [integral_pi_fin_one_two, integral_pi_fin_one_two, integral_const_mul]
  have hF := memLp_pi_fin_one_two _ h0
  refine stein_ginibre (ginVar W b) x y (fun B => Φ (ω₁, fun _ _ => B)) (fun B => Φa (ω₁, fun _ _ => B))
    (fun B => Φb (ω₁, fun _ _ => B)) (fun B => ha (ω₁, fun _ _ => B) hH)
    (fun B => hb (ω₁, fun _ _ => B) hH)
    (hF.integrable one_le_two) (integrable_pi_fin_one_two _ h1) (integrable_pi_fin_one_two _ h2)
    ((memLp_ginibre_entry (ginVar W b) x y).integrable_mul hF)

end BlockBand.Transmission.PassiveCovariance
