module

public import BlockBand.Transmission.DualBoundary.PostLaw

/-!
# Coupled lifted starts on one driver space

For two probability laws `μ₁, μ₂` on `ℝ²` carried by the chamber `𝒞₁`, on the driver
space `LΩ (ℝ² × ℝ²)` with start law `μ₁ ⊗ μ₂`:
* `cStart₁ ω = σ(ω.1.1)`, `cStart₂ ω = σ(ω.1.2)` (`σ = liftSection`, after replacing points
  off `𝒞₁` by the reference point `(1, 1/2)`, a `μ_i`-null change);
* **`isLiftStart_cStart₁/₂`**: admissible starts (augmented-`𝓕₀`-measurable, in `liftM`);
  `liftProj_cStart₁/₂_mem`: their projections are in `𝒞₁` at every `ω`;
* **`map_liftProj_cStart₁/₂`**: the projected start has law `μ_i` (the hypothesis `hlaw` of
  `map_zbar_post_eq_lift`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists BlockBand.Transmission.DualLift
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

/-- The reference interior point `(1, 1/2)`. -/
def refPt : Fin 2 → ℝ := ![1, 1 / 2]

theorem refPt_mem : refPt ∈ flatChamber 1 :=
  DualEntrance.mem_flatChamber_one (by norm_num [refPt]) (by norm_num [refPt])
    (by norm_num [refPt])

open scoped Classical in
/-- Points off the chamber are replaced by `refPt`. -/
def toChamber (z : Fin 2 → ℝ) : Fin 2 → ℝ := if z ∈ flatChamber 1 then z else refPt

theorem toChamber_mem (z : Fin 2 → ℝ) : toChamber z ∈ flatChamber 1 := by
  unfold toChamber; split_ifs with h
  · exact h
  · exact refPt_mem

theorem measurable_toChamber : Measurable toChamber :=
  Measurable.ite (isOpen_flatChamber 1).measurableSet measurable_id measurable_const

/-- The lifted start over a point of `ℝ²`. -/
def secStart (z : Fin 2 → ℝ) : Fin 6 → ℝ := liftSection (toChamber z 0) (toChamber z 1)

theorem measurable_liftSection_pt : Measurable fun z : Fin 2 → ℝ => liftSection (z 0) (z 1) := by
  have h0 : Measurable fun z : Fin 2 → ℝ => z 0 := measurable_pi_apply 0
  have h1 : Measurable fun z : Fin 2 → ℝ => z 1 := measurable_pi_apply 1
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact Real.continuous_sqrt.measurable.comp h0
  · exact measurable_const
  · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp (h1.mul (measurable_const.sub h1)))
  · exact measurable_const
  · exact measurable_const.sub (measurable_const.mul h1)
  · exact measurable_const.div (h0.add h1)

theorem measurable_secStart : Measurable secStart :=
  measurable_liftSection_pt.comp measurable_toChamber

theorem secStart_mem (z : Fin 2 → ℝ) : secStart z ∈ liftM := by
  obtain ⟨h0, h1, h2⟩ := mem_flatChamber_one (toChamber_mem z)
  exact liftSection_mem h0.le h1.le h2.le (by linarith)

theorem liftProj_secStart (z : Fin 2 → ℝ) : liftProj (secStart z) = toChamber z := by
  obtain ⟨h0, -, -⟩ := mem_flatChamber_one (toChamber_mem z)
  rw [secStart, liftProj_liftSection h0.le]
  funext i; fin_cases i <;> rfl

/-- The start space of the coupling. -/
abbrev CS := (Fin 2 → ℝ) × (Fin 2 → ℝ)

/-- First coupled start. -/
def cStart₁ (ω : LΩ CS) : Fin 6 → ℝ := secStart ω.1.1

/-- Second coupled start. -/
def cStart₂ (ω : LΩ CS) : Fin 6 → ℝ := secStart ω.1.2

theorem measurable_fst_L0 (μ : Measure CS) [IsProbabilityMeasure μ] :
    Measurable[L𝓖 μ 0] fun ω : LΩ CS => ω.1 := by
  have hf : Measurable[commonWienerFiltration CS (Fin 5) 0]
      (fun x : LΩ CS => (x.1, commonWienerPast 0 x.2)) := Measurable.of_comap_le le_rfl
  have h : Measurable[commonWienerFiltration CS (Fin 5) 0] fun ω : LΩ CS => ω.1 :=
    Measurable.comp (g := Prod.fst)
      (f := fun x : LΩ CS => (x.1, commonWienerPast 0 x.2)) measurable_fst hf
  exact h.mono (le_augmentedFiltration _ _ 0) le_rfl

theorem isLiftStart_cStart₁ (μ : Measure CS) [IsProbabilityMeasure μ] :
    IsLiftStart μ cStart₁ :=
  ⟨(measurable_secStart.comp (measurable_fst.comp (measurable_fst_L0 μ))).stronglyMeasurable,
    fun _ => secStart_mem _⟩

theorem isLiftStart_cStart₂ (μ : Measure CS) [IsProbabilityMeasure μ] :
    IsLiftStart μ cStart₂ :=
  ⟨(measurable_secStart.comp (measurable_snd.comp (measurable_fst_L0 μ))).stronglyMeasurable,
    fun _ => secStart_mem _⟩

theorem liftProj_cStart₁_mem (ω : LΩ CS) : liftProj (cStart₁ ω) ∈ flatChamber 1 := by
  rw [cStart₁, liftProj_secStart]; exact toChamber_mem _

theorem liftProj_cStart₂_mem (ω : LΩ CS) : liftProj (cStart₂ ω) ∈ flatChamber 1 := by
  rw [cStart₂, liftProj_secStart]; exact toChamber_mem _

theorem map_toChamber {ν : Measure (Fin 2 → ℝ)} (hν : ν (flatChamber 1)ᶜ = 0) :
    ν.map toChamber = ν := by
  have he : toChamber =ᵐ[ν] id := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν] with z hz
    simp only [Set.mem_compl_iff, not_not] at hz
    simp [toChamber, hz]
  rw [Measure.map_congr he, Measure.map_id]

theorem map_fst_LP (μ : Measure CS) [IsProbabilityMeasure μ] :
    (LP μ).map (fun ω : LΩ CS => ω.1) = μ := by
  have h1 : (commonWienerLaw (Fin 5)) univ = 1 := by
    have := measure_univ (μ := LP μ)
    rwa [LP, driverLaw, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul] at this
  change (driverLaw (κ := Fin 5) μ).map Prod.fst = μ
  rw [driverLaw, Measure.map_fst_prod, h1, one_smul]

/-- **The first projected start has law `μ₁`.** -/
theorem map_liftProj_cStart₁ {μ₁ μ₂ : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : μ₁ (flatChamber 1)ᶜ = 0) :
    (LP (μ₁.prod μ₂)).map (fun ω => liftProj (cStart₁ ω)) = μ₁ := by
  have e : (fun ω => liftProj (cStart₁ ω)) =
      (toChamber ∘ Prod.fst) ∘ fun ω : LΩ CS => ω.1 := by
    funext ω; simp [cStart₁, liftProj_secStart]
  rw [e, ← Measure.map_map (measurable_toChamber.comp measurable_fst) measurable_fst,
    map_fst_LP, ← Measure.map_map measurable_toChamber measurable_fst, Measure.map_fst_prod]
  simp [map_toChamber h₁]

/-- **The second projected start has law `μ₂`.** -/
theorem map_liftProj_cStart₂ {μ₁ μ₂ : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₂ : μ₂ (flatChamber 1)ᶜ = 0) :
    (LP (μ₁.prod μ₂)).map (fun ω => liftProj (cStart₂ ω)) = μ₂ := by
  have e : (fun ω => liftProj (cStart₂ ω)) =
      (toChamber ∘ Prod.snd) ∘ fun ω : LΩ CS => ω.1 := by
    funext ω; simp [cStart₂, liftProj_secStart]
  rw [e, ← Measure.map_map (measurable_toChamber.comp measurable_snd) measurable_fst,
    map_fst_LP, ← Measure.map_map measurable_toChamber measurable_snd, Measure.map_snd_prod]
  simp [map_toChamber h₂]

end BlockBand.Transmission.DualBoundary
