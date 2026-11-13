module
public import BlockBand.SourceProcess.Stochastic.Levy.Brownian
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.MultiBracket
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Product extensions of filtered probability spaces

Setting: two filtered probability spaces `(Ω, 𝓖, Q)` and `(W, 𝓕, ν)` (raw filtrations, any
universes). The product `(Ω × W, 𝓖 ⊗ 𝓕, Q ⊗ ν)` carries the product filtration
`prodFiltration 𝓖 𝓕 t = 𝓖_t ⊗ 𝓕_t` (`comap fst 𝓖_t ⊔ comap snd 𝓕_t`).

* `setIntegral_eq_zero_of_rect`: an integrable `D` with `∫_{A × B} D = 0` on all rectangles
  `A ∈ 𝓖_t`, `B ∈ 𝓕_t` integrates to `0` on every set of `𝓖_t ⊗ 𝓕_t` (π–λ).
* `martingale_of_setIntegral_eq`: martingale criterion by set integrals.
* `martingale_lift_fst`, `martingale_lift_snd`: martingales of either factor are martingales
  of the product filtration; `hasMartingaleModification_lift_fst/snd` (modification form).
* `isFiltrationBrownian_lift_snd`: a `𝓕`-Brownian motion on the second factor is a
  `𝓖 ⊗ 𝓕`-Brownian motion on the product; `indepFun_fst_snd`: the factors are independent.
* `IsL2Integrator.lift_fst`, `IsL2IntegratorVec.lift_fst`: integrator structures lift.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open scoped NNReal ENNReal

universe u v

variable {Ω : Type u} {W : Type v} [mΩ : MeasurableSpace Ω] [mW : MeasurableSpace W]

/-- The product filtration `𝓖_t ⊗ 𝓕_t`. -/
def prodFiltration (𝓖 : Filtration ℝ≥0 mΩ) (𝓕 : Filtration ℝ≥0 mW) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × W)) where
  seq t := MeasurableSpace.comap Prod.fst (𝓖 t) ⊔ MeasurableSpace.comap Prod.snd (𝓕 t)
  mono' _ _ h := sup_le_sup (MeasurableSpace.comap_mono (𝓖.mono h))
    (MeasurableSpace.comap_mono (𝓕.mono h))
  le' t := sup_le ((MeasurableSpace.comap_mono (𝓖.le t)).trans measurable_fst.comap_le)
    ((MeasurableSpace.comap_mono (𝓕.le t)).trans measurable_snd.comap_le)

variable {𝓖 : Filtration ℝ≥0 mΩ} {𝓕 : Filtration ℝ≥0 mW}

theorem measurable_fst_prodFiltration (t : ℝ≥0) :
    Measurable[prodFiltration 𝓖 𝓕 t, 𝓖 t] (Prod.fst : Ω × W → Ω) :=
  measurable_iff_comap_le.2 le_sup_left

theorem measurable_snd_prodFiltration (t : ℝ≥0) :
    Measurable[prodFiltration 𝓖 𝓕 t, 𝓕 t] (Prod.snd : Ω × W → W) :=
  measurable_iff_comap_le.2 le_sup_right

/-- Rectangles `A × B`, `A ∈ 𝓖_t`, `B ∈ 𝓕_t`. -/
def rectSets (𝓖 : Filtration ℝ≥0 mΩ) (𝓕 : Filtration ℝ≥0 mW) (t : ℝ≥0) : Set (Set (Ω × W)) :=
  image2 (· ×ˢ ·) {A | MeasurableSet[𝓖 t] A} {B | MeasurableSet[𝓕 t] B}

theorem prodFiltration_eq_generateFrom (t : ℝ≥0) :
    (prodFiltration 𝓖 𝓕 t : MeasurableSpace (Ω × W)) =
      MeasurableSpace.generateFrom (rectSets 𝓖 𝓕 t) :=
  (@generateFrom_prod Ω W (𝓖 t) (𝓕 t)).symm

theorem isPiSystem_rectSets (t : ℝ≥0) : IsPiSystem (rectSets 𝓖 𝓕 t) :=
  @isPiSystem_prod Ω W (𝓖 t) (𝓕 t)

/-- **π–λ on the product filtration.** -/
theorem setIntegral_eq_zero_of_rect {P : Measure (Ω × W)} {t : ℝ≥0} {D : Ω × W → ℝ}
    (hD : Integrable D P)
    (hrect : ∀ A B, MeasurableSet[𝓖 t] A → MeasurableSet[𝓕 t] B → ∫ x in A ×ˢ B, D x ∂P = 0)
    {S : Set (Ω × W)} (hS : MeasurableSet[prodFiltration 𝓖 𝓕 t] S) : ∫ x in S, D x ∂P = 0 := by
  have hle := (prodFiltration 𝓖 𝓕).le t
  have htot : ∫ x, D x ∂P = 0 := by
    have := hrect univ univ MeasurableSet.univ MeasurableSet.univ
    rwa [univ_prod_univ, setIntegral_univ] at this
  refine @MeasurableSpace.induction_on_inter (Ω × W) (prodFiltration 𝓖 𝓕 t)
    (fun S _ => ∫ x in S, D x ∂P = 0) (rectSets 𝓖 𝓕 t) (prodFiltration_eq_generateFrom t)
    (isPiSystem_rectSets t) (by simp) ?_ ?_ ?_ S hS
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hrect A B hA hB
  · intro T hT h
    rw [setIntegral_compl (hle T hT) hD, htot, h, sub_zero]
  · intro g hdisj hgm hg
    rw [integral_iUnion (fun i => hle _ (hgm i)) hdisj hD.integrableOn]
    exact (tsum_congr hg).trans tsum_zero

/-- **Martingale criterion by set integrals.** -/
theorem martingale_of_setIntegral_eq {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    [IsFiniteMeasure P] {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω')}
    {M : ℝ≥0 → Ω' → ℝ} (hadapt : ∀ t, StronglyMeasurable[𝓗 t] (M t))
    (hint : ∀ t, Integrable (M t) P)
    (h : ∀ s t, s ≤ t → ∀ S, MeasurableSet[𝓗 s] S → ∫ x in S, M t x ∂P = ∫ x in S, M s x ∂P) :
    Martingale M 𝓗 P :=
  ⟨hadapt, fun s t hst => (ae_eq_condExp_of_forall_setIntegral_eq (𝓗.le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun S hS _ => (h s t hst S hS).symm)
    (hadapt s).aestronglyMeasurable).symm⟩

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {ν : Measure W} [IsProbabilityMeasure ν]

/-- **Martingales of the first factor lift.** -/
theorem martingale_lift_fst {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓖 Q) :
    Martingale (fun t (x : Ω × W) => N t x.1) (prodFiltration 𝓖 𝓕) (Q.prod ν) := by
  have hint : ∀ t, Integrable (fun x : Ω × W => N t x.1) (Q.prod ν) := fun t =>
    measurePreserving_fst.integrable_comp_of_integrable (hN.integrable t)
  refine martingale_of_setIntegral_eq (fun t => (hN.1 t).comp_measurable
    (measurable_fst_prodFiltration t)) hint fun s t hst S hS => ?_
  have h0 := setIntegral_eq_zero_of_rect (P := Q.prod ν) (D := fun x => N t x.1 - N s x.1)
    ((hint t).sub (hint s)) (fun A B hA _ => ?_) hS
  · rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at h0
    linarith
  · have e := setIntegral_prod_mul (μ := Q) (ν := ν) (L := ℝ) (fun ω => N t ω - N s ω)
      (fun _ => 1) A B
    simp only [mul_one] at e
    rw [e, integral_sub (hN.integrable t).integrableOn (hN.integrable s).integrableOn,
      hN.setIntegral_eq hst hA, sub_self, zero_mul]

/-- **Martingales of the second factor lift.** -/
theorem martingale_lift_snd {N : ℝ≥0 → W → ℝ} (hN : Martingale N 𝓕 ν) :
    Martingale (fun t (x : Ω × W) => N t x.2) (prodFiltration 𝓖 𝓕) (Q.prod ν) := by
  have hint : ∀ t, Integrable (fun x : Ω × W => N t x.2) (Q.prod ν) := fun t =>
    measurePreserving_snd.integrable_comp_of_integrable (hN.integrable t)
  refine martingale_of_setIntegral_eq (fun t => (hN.1 t).comp_measurable
    (measurable_snd_prodFiltration t)) hint fun s t hst S hS => ?_
  have h0 := setIntegral_eq_zero_of_rect (P := Q.prod ν) (D := fun x => N t x.2 - N s x.2)
    ((hint t).sub (hint s)) (fun A B _ hB => ?_) hS
  · rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at h0
    linarith
  · have e := setIntegral_prod_mul (μ := Q) (ν := ν) (L := ℝ) (fun _ => 1)
      (fun ω => N t ω - N s ω) A B
    simp only [one_mul] at e
    rw [e, integral_sub (hN.integrable t).integrableOn (hN.integrable s).integrableOn,
      hN.setIntegral_eq hst hB, sub_self, mul_zero]

theorem hasMartingaleModification_lift_fst {X : ℝ≥0 → Ω → ℝ}
    (h : HasMartingaleModification Q 𝓖 X) :
    HasMartingaleModification (Q.prod ν) (prodFiltration 𝓖 𝓕) fun t x => X t x.1 := by
  obtain ⟨N, hN, hNX⟩ := h
  exact ⟨_, martingale_lift_fst hN, fun t =>
    measurePreserving_fst.quasiMeasurePreserving.ae_eq_comp (hNX t)⟩

theorem hasMartingaleModification_lift_snd {X : ℝ≥0 → W → ℝ}
    (h : HasMartingaleModification ν 𝓕 X) :
    HasMartingaleModification (Q.prod ν) (prodFiltration 𝓖 𝓕) fun t x => X t x.2 := by
  obtain ⟨N, hN, hNX⟩ := h
  exact ⟨_, martingale_lift_snd hN, fun t =>
    measurePreserving_snd.quasiMeasurePreserving.ae_eq_comp (hNX t)⟩

/-- The two factors are independent under `Q ⊗ ν`. -/
theorem indepFun_fst_snd : IndepFun (Prod.fst : Ω × W → Ω) Prod.snd (Q.prod ν) :=
  indepFun_prod measurable_id measurable_id

/-- **Brownian motions of the second factor lift.** A `𝓕`-Brownian motion `B` on `(W, ν)`
is a `𝓖 ⊗ 𝓕`-Brownian motion on `(Ω × W, Q ⊗ ν)`. -/
theorem isFiltrationBrownian_lift_snd {d : ℕ} {B : ℝ≥0 → W → Fin d → ℝ}
    (hB : IsFiltrationBrownian ν 𝓕 B) :
    IsFiltrationBrownian (Q.prod ν) (prodFiltration 𝓖 𝓕) fun t x => B t x.2 := by
  have hmp := measurePreserving_snd (μ := Q) (ν := ν)
  refine ⟨fun t => (hB.adapted t).comp_measurable (measurable_snd_prodFiltration t),
    hmp.quasiMeasurePreserving.ae hB.continuous, hmp.quasiMeasurePreserving.ae hB.zero,
    fun s t hst => ?_, fun s t hst => (hB.hasLaw s t hst).comp hmp.hasLaw⟩
  have hΔ : Measurable fun w => B t w - B s w :=
    ((hB.adapted t).mono (𝓕.le t)).measurable.sub ((hB.adapted s).mono (𝓕.le s)).measurable
  let m₁ : MeasurableSpace (Ω × W) :=
    MeasurableSpace.comap (fun x : Ω × W => B t x.2 - B s x.2) inferInstance
  refine IndepSets.indep (m1 := m₁) (hΔ.comp measurable_snd).comap_le
    ((prodFiltration 𝓖 𝓕).le s) (@MeasurableSpace.isPiSystem_measurableSet _ m₁)
    (isPiSystem_rectSets s) (@MeasurableSpace.generateFrom_measurableSet _ m₁).symm
    (prodFiltration_eq_generateFrom s) ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨C, hC, rfl⟩ ⟨A, hA, D, hD, rfl⟩
  have hind := (hB.indep s t hst)
  rw [Indep_iff] at hind
  have hpre : (fun x : Ω × W => B t x.2 - B s x.2) ⁻¹' C = univ ×ˢ ((fun w => B t w - B s w) ⁻¹' C) := by
    ext x; simp
  have hAm : MeasurableSet A := 𝓖.le s A hA
  have hDm : MeasurableSet D := 𝓕.le s D hD
  rw [hpre, prod_inter_prod, univ_inter, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, one_mul, hind _ D ⟨C, hC, rfl⟩ hD]
  ring

/-!
### Integrator structures lift
-/

/-- `IsL2Integrator` lifts along the first factor. -/
theorem _root_.BlockBand.SourceProcess.Stochastic.GeneralIntegral.IsL2Integrator.lift_fst {N α : ℝ≥0 → Ω → ℝ} (h : IsL2Integrator Q 𝓖 N α) :
    IsL2Integrator (Q.prod ν) (prodFiltration 𝓖 𝓕) (fun t x => N t x.1)
      (fun t x => α t x.1) := by
  have hmp := measurePreserving_fst (μ := Q) (ν := ν)
  refine ⟨hmp.quasiMeasurePreserving.ae h.continuous, fun t => (h.memLp t).comp_measurePreserving hmp,
    ?_, fun t x => h.alpha_nonneg t x.1, ?_, hmp.quasiMeasurePreserving.ae h.alpha_integrable, ?_⟩
  · obtain ⟨M, hM, hMN⟩ := h.martingale
    exact ⟨_, martingale_lift_fst hM, fun t => hmp.quasiMeasurePreserving.ae_eq_comp (hMN t)⟩
  · exact h.alpha_measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  · obtain ⟨K, hK, hKN⟩ := h.bracket
    exact ⟨_, martingale_lift_fst hK, fun t => hmp.quasiMeasurePreserving.ae_eq_comp (hKN t)⟩

/-- `IsL2IntegratorVec` lifts along the first factor. -/
theorem _root_.BlockBand.SourceProcess.Stochastic.GeneralIntegral.IsL2IntegratorVec.lift_fst {ι : Type*} [Fintype ι] {N : ι → ℝ≥0 → Ω → ℝ}
    {a : ι → ι → ℝ≥0 → Ω → ℝ} (h : IsL2IntegratorVec Q 𝓖 N a) :
    IsL2IntegratorVec (Q.prod ν) (prodFiltration 𝓖 𝓕) (fun i t x => N i t x.1)
      (fun i j t x => a i j t x.1) := by
  have hmp := measurePreserving_fst (μ := Q) (ν := ν)
  refine ⟨fun i => (h.coord i).lift_fst, fun t x v => h.psd t x.1 v, fun i j => ?_,
    fun i j => hmp.quasiMeasurePreserving.ae (h.integrable i j), fun i j => ?_⟩
  · exact (h.measurable i j).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  · obtain ⟨K, hK, hKN⟩ := h.cross i j
    exact ⟨_, martingale_lift_fst hK, fun t => hmp.quasiMeasurePreserving.ae_eq_comp (hKN t)⟩

end BlockBand.SourceProcess.Stochastic.Levy
