module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Model.Construction.PhysicalCanonicalLaw
public import BlockBand.QUE.Invariance.PhysicalRotationGrid
public import BlockBand.QUE.Fourier.PhysicalIntegrability

/-!
# The physical lead-profile theorem: the block-0 Palm law and the uniform rotation

**Main result (exact, with no error term).** For every admissible `p`, every
`FiniteRealization R` (arbitrary measurable ordered eigensystem and profile realization), every
energy `E`, every measurable bounded weight `w` (signed allowed) and every `Φ ∈ C_b(𝒫(𝕋))`:

`E Σ_α w(u_α) Φ(ν_α) = n · E Σ_α p_{α0} w(u_α) · n⁻¹ Σ_{s ∈ ℤ/n} Φ(ℛ_{s/n} ν_α)`

(`physicalOneMark_eq_blockZeroPalm`), measure: the exact physical law `R.model.law`;
`u_α = Nρ(E)(λ_α - E)`, `p_{αk}` the canonical block masses, `ν_α` the canonical profile,
`ℛ_a = massProfileRotation a` (translation by `+a`). The right side is also written as a
function of `(λ_α, (p_{αk})_k)` (`physicalOneMark_eq_blockZeroPalm_massVector`), the form of the
left side of `OneBlockPalmContract.massReal` at block `k = 0`, through the profile of a mass
vector `massVectorProfile` (equal to `ν_α` on the good locus).

**Inputs.** No contract is used, only the model's cyclic invariance
`GaussianRingModel.map_cyclicMatrix` (proved from `IsPhysicalGaussianRingLaw`: the cyclic block
shift preserves the variance profile), the deterministic
covariance of eigenvalues, block masses and profiles under the shift
(`physical_eigenvalue_cyclic`, `physical_blockMass_cyclic`, `physicalOrderedProfile_cyclic`), the
canonical-realization identification `spectral_markedConfig_eq_canonical_ae` and the a.s.
normalization `Σ_k p_{αk} = 1` (`physicalOrderedBlockMass_sum_ae`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.Clocks
open scoped ENNReal BoundedContinuousFunction

section Rotation

variable (p : Parameters)

/-- The uniform rotation average `n⁻¹ Σ_{s ∈ ℤ/n} Φ(ℛ_{s/n} ν)` of a profile functional. -/
def leadProfileRotationAverage (Φ : MassProfile →ᵇ ℝ) (ν : MassProfile) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ s : ZMod p.n, Φ (massProfileRotation (physicalProfileGrid p s) ν)

theorem abs_leadProfileRotationAverage_le (Φ : MassProfile →ᵇ ℝ) (ν : MassProfile) :
    |leadProfileRotationAverage p Φ ν| ≤ ‖Φ‖ := by
  unfold leadProfileRotationAverage
  have hn : (0 : ℝ) < p.n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.n)
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn)]
  calc (p.n : ℝ)⁻¹ * |∑ s : ZMod p.n, Φ (massProfileRotation (physicalProfileGrid p s) ν)|
      ≤ (p.n : ℝ)⁻¹ * ∑ _s : ZMod p.n, ‖Φ‖ := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        rw [← Real.norm_eq_abs]
        exact Φ.norm_coe_le_norm _
    _ = ‖Φ‖ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hn.ne', one_mul]

theorem measurable_massProfile_bcf (Φ : MassProfile →ᵇ ℝ) : Measurable Φ := by
  have := massProfile_opensMeasurableSpace
  exact Φ.continuous.measurable

theorem measurable_leadProfileRotationAverage (Φ : MassProfile →ᵇ ℝ) :
    Measurable (leadProfileRotationAverage p Φ) := by
  unfold leadProfileRotationAverage
  refine measurable_const.mul (Finset.measurable_sum _ fun s _ => ?_)
  have := massProfile_opensMeasurableSpace
  exact (Φ.continuous.comp (continuous_massProfileRotation _)).measurable

/-- Rotating by a grid angle and averaging over the grid is invariant. -/
theorem leadProfileRotationAverage_rotation (Φ : MassProfile →ᵇ ℝ) (ν : MassProfile)
    (t : ZMod p.n) :
    leadProfileRotationAverage p Φ (massProfileRotation (physicalProfileGrid p t) ν) =
      leadProfileRotationAverage p Φ ν := by
  unfold leadProfileRotationAverage
  congr 1
  simp_rw [massProfileRotation_add, ← BlockBand.QUE.Invariance.physicalProfileGrid_add]
  exact Fintype.sum_equiv (Equiv.addRight t) _ _ (fun s => rfl)

end Rotation

section Canonical

variable {p : Parameters}

/-- The physical one-mark statistic in canonical coordinates: for a measurable `w`,
`physicalOneMark R E w Φ = E Σ_α w(u_α) Φ(ν_α)` with the canonical eigenvalues and profiles. -/
theorem physicalOneMark_eq_canonical (R : FiniteRealization p) (E : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w) (Φ : MassProfile →ᵇ ℝ) :
    physicalOneMark R E w Φ =
      ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          Φ (physicalOrderedProfile p H α) ∂(R.model.law : Measure p.SiteMatrix) := by
  unfold physicalOneMark
  apply integral_congr_ae
  filter_upwards [spectral_markedConfig_eq_canonical_ae R.spectral E,
    physicalOrderedMarkedConfig_ae p R.model E] with H h1 h2
  rw [h1, h2]
  have := massProfile_opensMeasurableSpace
  have hm : Measurable (fun x : MarkedSpectralSpace => w x.1 * Φ x.2) :=
    (hw.comp measurable_fst).mul ((measurable_massProfile_bcf Φ).comp measurable_snd)
  rw [integral_finsetSum_measure (fun α _ => ?_)]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_dirac' _ _ hm.stronglyMeasurable]
    rfl
  · exact integrable_dirac enorm_lt_top

theorem measurable_microCoord (E : ℝ) : Measurable (microCoord p E) := by
  unfold microCoord
  exact measurable_const.mul (measurable_id.sub measurable_const)

/-- The cyclic block shift `H ↦ (H_{(x+s),(y+s)})` as a measurable equivalence. -/
def leadProfileCyclicEquiv (s : ZMod p.n) : p.SiteMatrix ≃ᵐ p.SiteMatrix where
  toFun := p.siteReindexMatrix (p.cyclicSiteEquiv s)
  invFun := p.siteReindexMatrix (p.cyclicSiteEquiv s).symm
  left_inv H := by funext x y; simp [Parameters.siteReindexMatrix]
  right_inv H := by funext x y; simp [Parameters.siteReindexMatrix]
  measurable_toFun := p.measurable_siteReindexMatrix _
  measurable_invFun := p.measurable_siteReindexMatrix _

/-- Cyclic invariance of the exact physical law, in integral form (no measurability needed). -/
theorem integral_comp_cyclic (model : p.GaussianRingModel) (s : ZMod p.n)
    (g : p.SiteMatrix → ℝ) :
    (∫ H, g (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) ∂(model.law : Measure p.SiteMatrix)) =
      ∫ H, g H ∂(model.law : Measure p.SiteMatrix) := by
  have h := integral_map_equiv (leadProfileCyclicEquiv (p := p) s) g
    (μ := (model.law : Measure p.SiteMatrix))
  have hmap : Measure.map (leadProfileCyclicEquiv (p := p) s) (model.law : Measure p.SiteMatrix) =
      (model.law : Measure p.SiteMatrix) := model.map_cyclicMatrix s
  rw [hmap] at h
  exact h.symm

/-- Integrability of `p_{αk} · h` for bounded measurable `h`. -/
theorem integrable_blockMass_mul (model : p.GaussianRingModel) (α : Fin p.N) (k : ZMod p.n)
    (h : p.SiteMatrix → ℝ) (hm : Measurable h) (C : ℝ) (hC : ∀ H, |h H| ≤ C) :
    Integrable (fun H => physicalOrderedBlockMass p H α k * h H)
      (model.law : Measure p.SiteMatrix) := by
  refine ((BlockBand.QUE.Fourier.integrable_physicalMass p model α k).mul_const C).mono'
    ((measurable_physicalOrderedBlockMass p α k).mul hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun H => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (physicalOrderedBlockMass_nonneg p H α k)]
  exact mul_le_mul_of_nonneg_left (hC H) (physicalOrderedBlockMass_nonneg p H α k)

/-- **The rotation step of the physical lead-profile theorem.** Exact identity: the physical one-mark
statistic is `n` times the block-0 mass-weighted (Palm) statistic of the
uniformly rotated profile functional.
Measure: the exact physical law;
`w` measurable and
bounded (signed allowed), `Φ ∈ C_b(𝒫(𝕋))`.
Uses only `Σ_k p_{αk} = 1` a.s. and the cyclic
invariance of the physical law.
-/
theorem physicalOneMark_eq_blockZeroPalm (R : FiniteRealization p) (E : ℝ) (w : ℝ → ℝ)
    (hw : Measurable w) (Mw : ℝ) (hMw : ∀ x, |w x| ≤ Mw) (Φ : MassProfile →ᵇ ℝ) :
    physicalOneMark R E w Φ =
      (p.n : ℝ) * ∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
          (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
            leadProfileRotationAverage p Φ (physicalOrderedProfile p H α))
        ∂(R.model.law : Measure p.SiteMatrix) := by
  set μ := (R.model.law : Measure p.SiteMatrix)
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.n
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0)
  -- the per-rank integrand `w(u_α) Φ(ν_α)` and its rotated forms
  let u : Fin p.N → p.SiteMatrix → ℝ := fun α H =>
    w (microCoord p E (physicalOrderedEigenvalue p H α))
  have hu : ∀ α, Measurable (u α) := fun α =>
    hw.comp ((measurable_microCoord E).comp (measurable_physicalOrderedEigenvalue p α))
  have hΦν : ∀ (a : Torus) (α : Fin p.N),
      Measurable (fun H => Φ (massProfileRotation a (physicalOrderedProfile p H α))) := by
    intro a α
    have := massProfile_opensMeasurableSpace
    exact (Φ.continuous.comp (continuous_massProfileRotation a)).measurable.comp
      (measurable_physicalOrderedProfile p α)
  have hbd : ∀ (a : Torus) (α : Fin p.N) H,
      |u α H * Φ (massProfileRotation a (physicalOrderedProfile p H α))| ≤ Mw * ‖Φ‖ := by
    intro a α H
    rw [abs_mul]
    exact mul_le_mul (hMw _) (by rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _)
      (abs_nonneg _) hMw0
  let f : ZMod p.n → p.SiteMatrix → ℝ := fun s H =>
    ∑ α : Fin p.N, physicalOrderedBlockMass p H α s * (u α H * Φ (physicalOrderedProfile p H α))
  let g : ZMod p.n → p.SiteMatrix → ℝ := fun s H =>
    ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
      (u α H * Φ (massProfileRotation (physicalProfileGrid p s) (physicalOrderedProfile p H α)))
  have hint : ∀ (a : Torus) (k : ZMod p.n) (α : Fin p.N), Integrable (fun H =>
      physicalOrderedBlockMass p H α k *
        (u α H * Φ (massProfileRotation a (physicalOrderedProfile p H α)))) μ := fun a k α =>
    integrable_blockMass_mul R.model α k _ ((hu α).mul (hΦν a α)) _ (hbd a α)
  have hf_int : ∀ s, Integrable (f s) μ := by
    intro s
    refine integrable_finsetSum _ fun α _ => ?_
    have := hint 0 s α
    simpa only [massProfileRotation_zero] using this
  have hg_int : ∀ s, Integrable (g s) μ := fun s =>
    integrable_finsetSum _ fun α _ => hint _ 0 α
  -- Step 1: insert `Σ_s p_{αs} = 1`
  have h1 : physicalOneMark R E w Φ = ∫ H, ∑ s : ZMod p.n, f s H ∂μ := by
    rw [physicalOneMark_eq_canonical R E w hw Φ]
    apply integral_congr_ae
    filter_upwards [physicalOrderedBlockMass_sum_ae p R.model] with H hH
    simp only [f]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_mul, hH α, one_mul]
  -- Step 2: each block equals the rotated block-0 statistic
  have h2 : ∀ s, ∫ H, f s H ∂μ = ∫ H, g s H ∂μ := by
    intro s
    rw [← integral_comp_cyclic R.model s (g s)]
    apply integral_congr_ae
    filter_upwards [R.model.isPhysical.1, R.model.ae_charpoly_separable] with H hH hsep
    simp only [f, g, u]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [BlockBand.QUE.Fourier.physical_blockMass_cyclic p H hH hsep α s 0, zero_add,
      BlockBand.QUE.Fourier.physical_eigenvalue_cyclic p H hH α s,
      BlockBand.QUE.Invariance.physicalOrderedProfile_cyclic p H ⟨hH, hsep⟩ α s,
      massProfileRotation_add, add_neg_cancel, massProfileRotation_zero]
  -- Step 3: reassemble
  rw [h1, integral_finsetSum _ fun s _ => hf_int s]
  simp_rw [h2]
  rw [← integral_finsetSum _ fun s _ => hg_int s, ← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun H => ?_
  simp only [g, u, leadProfileRotationAverage]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp

end Canonical

section MassVector

variable (p : Parameters)

/-- The finite measure `Σ_k q_k δ_{k/n}` of a block-mass vector. -/
def massVectorMeasure (q : ZMod p.n → ℝ) : Measure Torus :=
  ∑ k : ZMod p.n, ENNReal.ofReal (q k) • Measure.dirac (physicalProfileGrid p k)

/-- The profile of a block-mass vector:
`Σ_k q_k δ_{k/n}` when it is a probability measure,
`δ_0` otherwise (the convention of the `leadProfile`).
-/
def massVectorProfile (q : ZMod p.n → ℝ) : MassProfile := by
  classical
  exact if h : IsProbabilityMeasure (massVectorMeasure p q) then
      (⟨massVectorMeasure p q, h⟩ : MassProfile)
    else (⟨Measure.dirac 0, inferInstance⟩ : MassProfile)

theorem measurable_massVectorMeasure : Measurable (massVectorMeasure p) := by
  unfold massVectorMeasure
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (ENNReal.measurable_ofReal.comp (measurable_pi_apply k)).smul_measure _

theorem measurable_massVectorProfile : Measurable (massVectorProfile p) := by
  classical
  have hS : MeasurableSet {q : ZMod p.n → ℝ | IsProbabilityMeasure (massVectorMeasure p q)} := by
    have : {q : ZMod p.n → ℝ | IsProbabilityMeasure (massVectorMeasure p q)} =
        (fun q => massVectorMeasure p q Set.univ) ⁻¹' {1} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact isProbabilityMeasure_iff
    rw [this]
    exact (Measure.measurable_coe MeasurableSet.univ).comp (measurable_massVectorMeasure p)
      (measurableSet_singleton 1)
  have hm : Measurable (fun q : ZMod p.n → ℝ =>
      if IsProbabilityMeasure (massVectorMeasure p q) then massVectorMeasure p q
      else Measure.dirac (0 : Torus)) :=
    (measurable_massVectorMeasure p).piecewise hS measurable_const
  have he : (fun q => (massVectorProfile p q : Measure Torus)) =
      (fun q => if IsProbabilityMeasure (massVectorMeasure p q) then massVectorMeasure p q
        else Measure.dirac (0 : Torus)) := by
    funext q
    by_cases h : IsProbabilityMeasure (massVectorMeasure p q) <;> simp [massVectorProfile, h]
  have hc : Measurable (fun q => (massVectorProfile p q : Measure Torus)) := by
    rw [he]; exact hm
  exact hc.subtype_mk

theorem coe_massVectorProfile_of (q : ZMod p.n → ℝ)
    (h : IsProbabilityMeasure (massVectorMeasure p q)) :
    (massVectorProfile p q : Measure Torus) = massVectorMeasure p q := by
  simp [massVectorProfile, h]

/-- On the good locus the canonical profile is the profile of the block-mass vector. -/
theorem physicalOrderedProfile_eq_massVectorProfile (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (α : Fin p.N) :
    physicalOrderedProfile p H α = massVectorProfile p (blockMassVector p H α) := by
  have hpm : massVectorMeasure p (blockMassVector p H α) = physicalOrderedProfileMeasure p H α :=
    rfl
  have hprob : IsProbabilityMeasure (massVectorMeasure p (blockMassVector p H α)) := by
    rw [hpm, isProbabilityMeasure_iff]
    exact physicalOrderedProfileMeasure_univ p H h.1 h.2 α
  apply ProbabilityMeasure.toMeasure_injective
  rw [physicalOrderedProfile_eq p H h.1 h.2 α]
  rw [coe_massVectorProfile_of p _ hprob, hpm]

/-- The rotation step in the form of the left side of `OneBlockPalmContract.massReal` at block `0`:
`E Σ_α w(u_α)Φ(ν_α) = n · E Σ_α p_{α0} f(λ_α, p_α)` with
`f(e, q) = w(Nρ(E)(e - E)) · n⁻¹ Σ_s Φ(ℛ_{s/n} ν(q))`, `ν(q) = massVectorProfile q`. -/
theorem physicalOneMark_eq_blockZeroPalm_massVector (R : FiniteRealization p) (E : ℝ)
    (w : ℝ → ℝ) (hw : Measurable w) (Mw : ℝ) (hMw : ∀ x, |w x| ≤ Mw)
    (Φ : MassProfile →ᵇ ℝ) :
    physicalOneMark R E w Φ =
      (p.n : ℝ) * ∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α 0 *
          (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
            leadProfileRotationAverage p Φ (massVectorProfile p (blockMassVector p H α)))
        ∂(R.model.law : Measure p.SiteMatrix) := by
  rw [physicalOneMark_eq_blockZeroPalm R E w hw Mw hMw Φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [R.model.isPhysical.1, R.model.ae_charpoly_separable] with H hH hsep
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [physicalOrderedProfile_eq_massVectorProfile p H ⟨hH, hsep⟩ α]

end MassVector

end BlockBand.Endpoints.Normalization
