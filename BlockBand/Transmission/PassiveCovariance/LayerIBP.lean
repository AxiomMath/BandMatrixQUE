module

public import BlockBand.Transmission.PassiveCovariance.GueIBP
public import BlockBand.Transmission.PassiveCovariance.GinibreIBP

/-!
# Gaussian IBP for the fresh one-port layer `layerLaw W b .oneBlockOnePort`

The layer law `layerLaw W b .oneBlockOnePort` is
`(Π_{Fin 1} GUE(c/W)) ⊗ (Π_{Fin 1}Π_{Fin 1} Gin(b/W))`. Fubini
(`integral_prod_eq_of_ae_fst/_snd`), `L²` sections (`memLp_two_section_fst/_snd`) and
`Fin 1`-products (`integral_pi_fin_one`, …, via `measurePreserving_funUnique`) transport
`stein_gue` and `stein_ginibre` to the layer:

* `stein_layerA`: `E[A_xy Φ] = (c/2W) E[Φ_H + iΦ_K]` (`Φ_H`, `Φ_K` the derivatives along
  `E_xy + E_yx`, `i(E_xy - E_yx)` in the block `A`);
* `stein_layerB`: `E[B_xy Φ] = (b/W) E[(Φ_a + iΦ_b)/2]` (derivatives along `E_xy`, `i·E_xy` in
  the bond `B`).

Hypotheses: `Φ` measurable and in `L²`, its derivatives integrable (the coordinate moments are
proved: `memLp_gue_entry`, `memLp_ginibre_entry`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

section Generic
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SFinite ν]

/-- Fubini with the inner integral over the first factor. -/
theorem integral_prod_eq_of_ae_fst (f g : α × β → ℂ) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν))
    (h : ∀ᵐ y ∂ν, ∫ x, f (x, y) ∂μ = ∫ x, g (x, y) ∂μ) :
    ∫ z, f z ∂μ.prod ν = ∫ z, g z ∂μ.prod ν := by
  rw [integral_prod_symm f hf, integral_prod_symm g hg]
  exact integral_congr_ae h

/-- Fubini with the inner integral over the second factor. -/
theorem integral_prod_eq_of_ae_snd (f g : α × β → ℂ) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν))
    (h : ∀ᵐ x ∂μ, ∫ y, f (x, y) ∂ν = ∫ y, g (x, y) ∂ν) :
    ∫ z, f z ∂μ.prod ν = ∫ z, g z ∂μ.prod ν := by
  rw [integral_prod f hf, integral_prod g hg]
  exact integral_congr_ae h

theorem memLp_two_section_fst {f : α × β → ℂ} (hm : Measurable f) (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x => f (x, y)) 2 μ := by
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hf
  filter_upwards [hi.prod_left_ae] with y hy
  exact (memLp_two_iff_integrable_sq_norm (hm.comp measurable_prodMk_right).aestronglyMeasurable).mpr hy

theorem memLp_two_section_snd {f : α × β → ℂ} (hm : Measurable f) (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => f (x, y)) 2 ν := by
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hf
  filter_upwards [hi.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm (hm.comp measurable_prodMk_left).aestronglyMeasurable).mpr hx

end Generic

/-- Integration over `Fin 1 → α` with the product of one copy. -/
theorem integral_pi_fin_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (g : (Fin 1 → α) → ℂ) :
    ∫ ω, g ω ∂Measure.pi (fun _ : Fin 1 => μ) = ∫ a, g (fun _ => a) ∂μ := by
  have h := (measurePreserving_funUnique μ (Fin 1)).symm
  exact (h.integral_comp' g).symm

theorem integrable_pi_fin_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {g : (Fin 1 → α) → ℂ} (hg : Integrable g (Measure.pi (fun _ : Fin 1 => μ))) :
    Integrable (fun a => g (fun _ => a)) μ := by
  have h := (measurePreserving_funUnique μ (Fin 1)).symm
  exact (h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hg

theorem memLp_pi_fin_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {g : (Fin 1 → α) → ℂ} (hg : MemLp g 2 (Measure.pi (fun _ : Fin 1 => μ))) :
    MemLp (fun a => g (fun _ => a)) 2 μ := by
  have h := (measurePreserving_funUnique μ (Fin 1)).symm
  exact hg.comp_measurePreserving h

theorem memLp_coord_gaussian {J : Type*} [Fintype J] (v : J → ℝ≥0) (j : J) :
    MemLp (fun ρ : J → ℝ => ((ρ j : ℝ) : ℂ)) 2 (Measure.pi fun i => gaussianReal 0 (v i)) :=
  ((memLp_id_gaussianReal (μ := 0) (v := v j) 2).comp_measurePreserving
    (measurePreserving_eval _ j)).ofReal

theorem memLp_gue_entry {n : ℕ} (t : ℝ≥0) (a b : Fin n) :
    MemLp (fun A : Matrix (Fin n) (Fin n) ℂ => A a b) 2 (gueMeasure (Fin n) t) := by
  rw [BlockBand.Transmission.Bridge.gueMeasure_eq_map]
  refine (memLp_map_measure_iff (Matrix.measurable_apply.aestronglyMeasurable)
    (BlockBand.Transmission.Bridge.measurable_gueRaw n t).aemeasurable).mpr ?_
  have h := fun j => memLp_coord_gaussian (fun _ : (Fin n × Fin n) × Fin 2 => (1 : ℝ≥0)) j
  have : (fun A : Matrix (Fin n) (Fin n) ℂ => A a b) ∘ BlockBand.Transmission.Bridge.gueRaw t =
      fun ρ => ((Real.sqrt t : ℂ) / 2) * ((ρ ((a, b), 0) : ℂ) + ρ ((b, a), 0)) +
        Complex.I * (((Real.sqrt t : ℂ) / 2) * ((ρ ((a, b), 1) : ℂ) - ρ ((b, a), 1))) := by
    funext ρ; exact gueRaw_apply_ab t ρ a b
  rw [this]
  exact (((h _).add (h _)).const_mul _).add ((((h _).sub (h _)).const_mul _).const_mul _)

/-- The GUE variance `c/W` of the fresh layer. -/
abbrev gueVar (W : ℕ) (b : ℝ) : ℝ≥0 := Real.toNNReal ((1 - 2 * b) / W)

/-- **IBP in the GUE block of the fresh one-port layer.** -/
theorem stein_layerA {W : ℕ} (b : ℝ) (Φ ΦH ΦK : LayerSample W .oneBlockOnePort → ℂ) (x y : Fin W)
    (hm : Measurable Φ)
    (hH : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian → HasDerivAt
      (fun s : ℝ => Φ ((fun i => ω.1 i + (s : ℂ) • hermDir x y), ω.2)) (ΦH ω) 0)
    (hK : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian → HasDerivAt
      (fun s : ℝ => Φ ((fun i => ω.1 i + (s : ℂ) • skewDir x y), ω.2)) (ΦK ω) 0)
    (hΦ : MemLp Φ 2 (layerLaw W b .oneBlockOnePort))
    (hΦH : Integrable ΦH (layerLaw W b .oneBlockOnePort))
    (hΦK : Integrable ΦK (layerLaw W b .oneBlockOnePort)) :
    ∫ ω, ω.1 0 x y * Φ ω ∂layerLaw W b .oneBlockOnePort =
      ((gueVar W b : ℂ) / 2) * ∫ ω, ΦH ω + Complex.I * ΦK ω ∂layerLaw W b .oneBlockOnePort := by
  set μA := Measure.pi fun _ : Fin 1 => gueMeasure (Fin W) (gueVar W b)
  set μB := Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hL : layerLaw W b .oneBlockOnePort = μA.prod μB := rfl
  rw [hL] at hΦ hΦH hΦK ⊢
  have hent : MemLp (fun ω : LayerSample W .oneBlockOnePort => ω.1 0 x y) 2 (μA.prod μB) :=
    ((memLp_gue_entry (gueVar W b) x y).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 1 => gueMeasure (Fin W) (gueVar W b)) 0)).comp_measurePreserving
      (measurePreserving_fst (μ := μA) (ν := μB))
  have hf : Integrable (fun ω : LayerSample W .oneBlockOnePort => ω.1 0 x y * Φ ω) (μA.prod μB) :=
    hent.integrable_mul hΦ
  rw [← integral_const_mul]
  refine integral_prod_eq_of_ae_fst _ _ hf ((hΦH.add (hΦK.const_mul _)).const_mul _) ?_
  filter_upwards [memLp_two_section_fst hm hΦ, hΦH.prod_left_ae, hΦK.prod_left_ae] with ω₂ h0 h1 h2
  rw [integral_pi_fin_one, integral_pi_fin_one]
  rw [integral_const_mul]
  exact stein_gue (gueVar W b) x y (fun A => Φ (fun _ => A, ω₂)) (fun A => ΦH (fun _ => A, ω₂))
    (fun A => ΦK (fun _ => A, ω₂)) (fun A hA => hH (fun _ => A, ω₂) hA) (fun A hA => hK (fun _ => A, ω₂) hA)
    (memLp_pi_fin_one _ h0) (integrable_pi_fin_one _ h1) (integrable_pi_fin_one _ h2)

theorem memLp_ginibre_entry {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ℝ≥0) (a : ι) (c : κ) :
    MemLp (fun B : Matrix ι κ ℂ => B a c) 2 (ginibreMeasure ι κ t) := by
  rw [ginibreMeasure_eq_map]
  refine (memLp_map_measure_iff (Matrix.measurable_apply.aestronglyMeasurable)
    measurable_ginibreCoord.aemeasurable).mpr ?_
  have h := fun j => memLp_coord_gaussian (fun _ : ι × κ × Fin 2 => t / 2) j
  exact (h _).add ((h _).mul_const _)

/-- The Ginibre variance `b/W` of the fresh layer. -/
abbrev ginVar (W : ℕ) (b : ℝ) : ℝ≥0 := Real.toNNReal (b / W)

theorem integral_pi_fin_one_two {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (g : (Fin 1 → Fin 1 → α) → ℂ) :
    ∫ ω, g ω ∂Measure.pi (fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μ) =
      ∫ a, g (fun _ _ => a) ∂μ := by
  rw [integral_pi_fin_one, integral_pi_fin_one]

theorem integrable_pi_fin_one_two {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {g : (Fin 1 → Fin 1 → α) → ℂ}
    (hg : Integrable g (Measure.pi (fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μ))) :
    Integrable (fun a => g (fun _ _ => a)) μ :=
  integrable_pi_fin_one μ (g := fun ω => g fun _ => ω) (integrable_pi_fin_one _ hg)

theorem memLp_pi_fin_one_two {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {g : (Fin 1 → Fin 1 → α) → ℂ}
    (hg : MemLp g 2 (Measure.pi (fun _ : Fin 1 => Measure.pi fun _ : Fin 1 => μ))) :
    MemLp (fun a => g (fun _ _ => a)) 2 μ :=
  memLp_pi_fin_one μ (g := fun ω => g fun _ => ω) (memLp_pi_fin_one _ hg)

/-- **IBP in the Ginibre bond of the fresh one-port layer.** -/
theorem stein_layerB {W : ℕ} (b : ℝ) (Φ Φa Φb : LayerSample W .oneBlockOnePort → ℂ) (x y : Fin W)
    (hm : Measurable Φ)
    (ha : ∀ ω : LayerSample W .oneBlockOnePort, HasDerivAt
      (fun s : ℝ => Φ (ω.1, fun i j => ω.2 i j + (s : ℂ) • Matrix.single x y 1)) (Φa ω) 0)
    (hb : ∀ ω : LayerSample W .oneBlockOnePort, HasDerivAt
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
  filter_upwards [memLp_two_section_snd hm hΦ, hΦa.prod_right_ae, hΦb.prod_right_ae] with ω₁ h0 h1 h2
  rw [integral_pi_fin_one_two, integral_pi_fin_one_two, integral_const_mul]
  have hF := memLp_pi_fin_one_two _ h0
  refine stein_ginibre (ginVar W b) x y (fun B => Φ (ω₁, fun _ _ => B)) (fun B => Φa (ω₁, fun _ _ => B))
    (fun B => Φb (ω₁, fun _ _ => B)) (fun B => ha (ω₁, fun _ _ => B)) (fun B => hb (ω₁, fun _ _ => B))
    (hF.integrable one_le_two) (integrable_pi_fin_one_two _ h1) (integrable_pi_fin_one_two _ h2)
    ((memLp_ginibre_entry (ginVar W b) x y).integrable_mul hF)

end BlockBand.Transmission.PassiveCovariance
