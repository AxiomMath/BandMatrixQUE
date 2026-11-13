module

public import BlockBand.Critical.JointRecovery.FiniteIdentity
public import BlockBand.Critical.JointRecovery.ReadoutTest

/-!
# Joint recovery: the finite-width identities at the level of laws

* `finiteEntireLaw_compl_goodEntire`: the law of `D_W` is carried by `goodEntire`;
* `readoutLaplace_markedLaw_eq`: `readoutLaplace q (R.markedLaw E) f` equals the extracted
  Laplace value `∫ exp(-Σ f(rootDerivativePoint E (n/W) F x)) d(law of D_W)` (bulk `ρ(E) > 0`);
* `finite_two_zeros_spectral`: two distinct real axis zeros of `D_W` in `(x, y)` force
  `ξ.spectral (-(n/W)ρ y, -(n/W)ρ x) ≥ 2` for the physical marked configuration.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set MeasureTheory
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction
open BlockBand.Internal.Contracts.CriticalEntire BlockBand.Model.Construction
open scoped Matrix ENNReal

variable {p : Parameters}

/-- The almost-sure finite-width facts used for the readout identity. -/
structure FiniteFacts (p : Parameters) (E : ℝ) {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (H : p.SiteMatrix) : Prop where
  herm : H.IsHermitian
  base : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0
  inj : Function.Injective (physicalOrderedEigenvalue p H)
  deriv_ne : ∀ α, deriv (axis (finiteEntireDeterminant p E (fullProfile q) H))
    (finiteZero p E H α) ≠ 0
  ratio : ∀ α (a : Fin (k + 1)),
    partialDerivValue a (finiteEntireDeterminant p E (fullProfile q) H)
        (BlockBand.Critical.energySource ((finiteZero p E H α : ℝ) : ℂ)) /
      partialDerivValue 0 (finiteEntireDeterminant p E (fullProfile q) H)
        (BlockBand.Critical.energySource ((finiteZero p E H α : ℝ) : ℂ)) =
      ((∫ r, fullProfile q a r ∂(physicalOrderedProfile p H α : Measure Torus) : ℝ) : ℂ)
  config : (physicalOrderedMarkedConfig p E H).marked.measure =
    ∑ α : Fin p.N, Measure.dirac
      (p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E),
        physicalOrderedProfile p H α)

/-- **The finite-width facts hold almost surely** under the exact physical Gaussian law of any
realization (every admissible `p`, fixed real `E`, any finite family `q`): Hermitian `H`,
`det(H - E) ≠ 0`, simple ordered spectrum, nonzero energy derivative and exact source ratios
at every finite zero, and the Dirac form of the marked configuration. Uses
`physicalOrdered_profile_readback_ae`, `physicalOrderedMarkedConfig_ae`. No limit. -/
theorem ae_finiteFacts (model : p.GaussianRingModel) (E : ℝ) {k : ℕ} (q : Fin k → C(Torus, ℝ)) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), FiniteFacts p E q H := by
  have hq : fullProfile q 0 = ContinuousMap.const Torus (1 : ℝ) := by simp [fullProfile]
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable,
    BlockBand.Critical.physicalOrdered_profile_readback_ae model E (fullProfile q) hq,
    physicalOrderedMarkedConfig_ae p model E] with H hH hsep hread hconf
  obtain ⟨hA, hr⟩ := hread
  have hinjC : Function.Injective (fun i => (hH.eigenvalues i : ℂ)) := by
    rw [hH.charpoly_eq] at hsep
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep
  refine ⟨hH, hA, ?_, ?_, ?_, hconf⟩
  · intro α β hαβ
    rw [physicalOrderedEigenvalue_eq H hH, physicalOrderedEigenvalue_eq H hH] at hαβ
    exact (rankSite p).injective (hinjC (congrArg (fun r : ℝ => (r : ℂ)) hαβ))
  · intro α
    rw [deriv_axis, partialDerivValue_finiteEntireDeterminant E q H hA, finiteZero_cast]
    exact (hr α).1
  · intro α a
    rw [partialDerivValue_finiteEntireDeterminant E q H hA,
      partialDerivValue_finiteEntireDeterminant E q H hA, finiteZero_cast]
    exact (hr α).2 a

/-- Distinct ranks give distinct finite zeros when the ordered spectrum is simple. -/
theorem finiteZero_injective {E : ℝ} {H : p.SiteMatrix}
    (hinj : Function.Injective (physicalOrderedEigenvalue p H)) :
    Function.Injective (finiteZero p E H) := by
  intro α β h
  have hW : (p.W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp p.W_pos)
  apply hinj
  unfold finiteZero at h
  have hW2 : -(p.W : ℝ) ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hW)
  have := mul_left_cancel₀ hW2 h
  linarith

/-- Real axis zeros of `D_W` are exactly the finite zeros. -/
theorem realZero_iff {E : ℝ} {k : ℕ} {q : Fin k → C(Torus, ℝ)} {H : p.SiteMatrix}
    (h : FiniteFacts p E q H) (x : ℝ) :
    axis (finiteEntireDeterminant p E (fullProfile q) H) x = 0 ↔ ∃ α, x = finiteZero p E H α := by
  rw [axis_finiteEntireDeterminant_eq_zero_iff E q H h.herm h.base]
  exact exists_congr fun α => Complex.ofReal_inj

/-- **Goodness of `D_W`** on the finite facts. -/
theorem mem_goodEntire_of_finiteFacts {E : ℝ} {k : ℕ} {q : Fin k → C(Torus, ℝ)}
    {H : p.SiteMatrix} (h : FiniteFacts p E q H) :
    finiteEntireDeterminant p E (fullProfile q) H ∈ goodEntire k := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show finiteEntireDeterminant p E (fullProfile q) H 0 ≠ 0
    rw [coe_finiteEntireDeterminant E q H h.base, BlockBand.Critical.physicalFiniteDeterminant_zero]
    exact one_ne_zero
  · intro w hw
    obtain ⟨α, rfl⟩ := (axis_finiteEntireDeterminant_eq_zero_iff E q H h.herm h.base w).mp hw
    exact Complex.ofReal_im _
  · intro x hx
    obtain ⟨α, rfl⟩ := (realZero_iff h x).mp hx
    exact h.deriv_ne α

/-- The parametrization of the energy zeros by ranks. -/
def zeroOfRank {E : ℝ} {k : ℕ} {q : Fin k → C(Torus, ℝ)} {H : p.SiteMatrix}
    (h : FiniteFacts p E q H) (α : Fin p.N) :
    EnergyZero (finiteEntireDeterminant p E (fullProfile q) H) :=
  ⟨finiteZero p E H α, (realZero_iff h _).mpr ⟨α, rfl⟩⟩

/-- **The readout identity, pointwise.** -/
theorem markedIntegral_readoutTest_eq {E : ℝ} {k : ℕ} {q : Fin k → C(Torus, ℝ)}
    {H : p.SiteMatrix} (h : FiniteFacts p E q H)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) :
    ∫ z, readoutTest q f z ∂(physicalOrderedMarkedConfig p E H).marked.measure =
      extractionSum E ((p.n : ℝ) / p.W) f (finiteEntireDeterminant p E (fullProfile q) H) := by
  have := BlockBand.Model.Construction.markedSpectralSpace_borelSpace
  rw [h.config, integral_finsetSum_measure (f := fun z => readoutTest q f z) (fun α _ =>
    (readoutTest q f).continuous.integrable_of_hasCompactSupport (readoutTest q f).hasCompactSupport)]
  refine (Finset.sum_congr rfl fun α _ =>
    integral_dirac' (fun z => readoutTest q f z) _
      (readoutTest q f).continuous.stronglyMeasurable).trans ?_
  have he : Function.Injective (zeroOfRank h) := fun α β hαβ =>
    finiteZero_injective h.inj (congrArg Subtype.val hαβ)
  unfold extractionSum
  rw [← he.tsum_eq (f := fun y => f (rootDerivativePoint E ((p.n : ℝ) / p.W)
    (finiteEntireDeterminant p E (fullProfile q) H) y)) (by
      intro y _
      obtain ⟨α, hα⟩ := (realZero_iff h y).mp y.2
      exact ⟨α, Subtype.ext hα.symm⟩), tsum_fintype]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [readoutTest_apply]
  congr 1
  unfold rootDerivativePoint profileReadout zeroOfRank
  refine Prod.ext ?_ ?_
  · exact (unfold_finiteZero E H α).symm
  · funext a
    exact (h.ratio α a).symm

/-- The finite law of `D_W` is carried by `goodEntire`. -/
theorem finiteEntireLaw_compl_goodEntire (R : FiniteRealization p) (E : ℝ) {k : ℕ}
    (q : Fin k → C(Torus, ℝ)) :
    (finiteEntireLaw R E (fullProfile q) : Measure (EntireFunction (k + 1))) (goodEntire k)ᶜ = 0 := by
  change ((R.model.law : Measure p.SiteMatrix).map (finiteEntireDeterminant p E (fullProfile q)))
    (goodEntire k)ᶜ = 0
  rw [Measure.map_apply (measurable_finiteEntireDeterminant E _) measurableSet_goodEntire.compl]
  refine measure_mono_null (fun H hH => ?_) (ae_iff.mp (ae_finiteFacts R.model E q))
  exact fun hf => hH (mem_goodEntire_of_finiteFacts hf)

/-- **The readout identity at the level of laws**: `readoutLaplace` of the physical marked law equals the
extracted Laplace value of the finite law of `D_W` at the finite ratio `n/W`. -/
theorem readoutLaplace_markedLaw_eq (R : FiniteRealization p) {E : ℝ}
    (hρ : 0 < Parameters.semicircleDensity E) {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z) :
    readoutLaplace q (R.markedLaw E) f =
      ∫ F, extractionValue E ((p.n : ℝ) / p.W) f F
        ∂(finiteEntireLaw R E (fullProfile q) : Measure (EntireFunction (k + 1))) := by
  have hτ : 0 < (p.n : ℝ) / p.W := div_pos (by have := p.n_ge_four; positivity)
    (by exact_mod_cast p.W_pos)
  have hD := measurable_finiteEntireDeterminant (p := p) E (fullProfile q)
  have hsec : Measurable fun F : EntireFunction (k + 1) =>
      extractionTest E f ((p.n : ℝ) / p.W, F) :=
    (measurable_extractionTest hρ f).comp measurable_prodMk_left
  rw [readoutLaplace_eq_integral q _ f hf, finiteRealization_markedLaw_eq_canonical]
  change ∫ ξ, _ ∂((R.model.law : Measure p.SiteMatrix).map (physicalOrderedMarkedConfig p E)) =
    ∫ F, _ ∂((R.model.law : Measure p.SiteMatrix).map (finiteEntireDeterminant p E (fullProfile q)))
  have hgoodmap : ∀ᵐ F ∂((R.model.law : Measure p.SiteMatrix).map
      (finiteEntireDeterminant p E (fullProfile q))), F ∈ goodEntire k := by
    rw [ae_iff]
    exact finiteEntireLaw_compl_goodEntire R E q
  rw [integral_congr_ae (hgoodmap.mono fun F hF =>
      (extractionTest_of_mem (E := E) (f := f) (p := ((p.n : ℝ) / p.W, F)) ⟨hτ, hF⟩).symm),
    integral_map hD.aemeasurable hsec.aestronglyMeasurable,
    integral_map (measurable_physicalOrderedMarkedConfig p E).aemeasurable
      (markedLaplaceBCF (readoutTest q f) fun _ => hf _).continuous.aestronglyMeasurable]
  refine integral_congr_ae ((ae_finiteFacts R.model E q).mono fun H hH => ?_)
  change Real.exp (-∫ z, readoutTest q f z ∂(physicalOrderedMarkedConfig p E H).marked.measure) =
    extractionTest E f ((p.n : ℝ) / p.W, finiteEntireDeterminant p E (fullProfile q) H)
  rw [extractionTest_of_mem (p := ((p.n : ℝ) / p.W, finiteEntireDeterminant p E (fullProfile q) H))
    ⟨hτ, mem_goodEntire_of_finiteFacts hH⟩]
  simp only [extractionValue]
  rw [markedIntegral_readoutTest_eq hH f]

/-- **Two distinct zeros give two unfolded eigenvalues.** For `x < y`, distinct real zeros of
the axis of `D_W` in `(x, y)` give spectral mass `≥ 2` on `(-(n/W)ρ y, -(n/W)ρ x)`. -/
theorem finite_two_zeros_spectral {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E) {k : ℕ}
    {q : Fin k → C(Torus, ℝ)} {H : p.SiteMatrix} (h : FiniteFacts p E q H) {x y y₁ y₂ : ℝ}
    (hne : y₁ ≠ y₂) (h₁ : y₁ ∈ Ioo x y) (h₂ : y₂ ∈ Ioo x y)
    (hz₁ : axis (finiteEntireDeterminant p E (fullProfile q) H) y₁ = 0)
    (hz₂ : axis (finiteEntireDeterminant p E (fullProfile q) H) y₂ = 0) :
    (1 : ℝ≥0∞) < (physicalOrderedMarkedConfig p E H).spectral.measure
      (Ioo (-(((p.n : ℝ) / p.W) * Parameters.semicircleDensity E) * y)
        (-(((p.n : ℝ) / p.W) * Parameters.semicircleDensity E) * x)) := by
  classical
  have hτ : 0 < (p.n : ℝ) / p.W := div_pos (by have := p.n_ge_four; positivity)
    (by exact_mod_cast p.W_pos)
  set c := ((p.n : ℝ) / p.W) * Parameters.semicircleDensity E with hc
  have hcpos : 0 < c := mul_pos hτ hρ
  obtain ⟨α, rfl⟩ := (realZero_iff h y₁).mp hz₁
  obtain ⟨β, rfl⟩ := (realZero_iff h _).mp hz₂
  have hαβ : α ≠ β := fun h' => hne (by rw [h'])
  set I := Ioo (-c * y) (-c * x) with hI
  have hmem : ∀ γ, finiteZero p E H γ ∈ Ioo x y →
      p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H γ - E) ∈ I := by
    intro γ hγ
    rw [← unfold_finiteZero E H γ, ← hc]
    constructor <;> nlinarith [hγ.1, hγ.2]
  rw [(physicalOrderedMarkedConfig p E H).spectral_eq,
    Measure.map_apply measurable_fst measurableSet_Ioo, h.config]
  rw [Measure.finsetSum_apply]
  have hsub : ({α, β} : Finset (Fin p.N)) ⊆ Finset.univ := Finset.subset_univ _
  calc (1 : ℝ≥0∞) < 2 := by norm_num
    _ = ∑ γ ∈ ({α, β} : Finset (Fin p.N)), (1 : ℝ≥0∞) := by
        rw [Finset.sum_pair hαβ]; norm_num
    _ ≤ ∑ γ ∈ ({α, β} : Finset (Fin p.N)), (Measure.dirac
          (p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H γ - E),
            physicalOrderedProfile p H γ)) (Prod.fst ⁻¹' I) := by
        refine Finset.sum_le_sum fun γ hγ => ?_
        rw [Measure.dirac_apply_of_mem]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
        rcases hγ with rfl | rfl
        · exact hmem _ h₁
        · exact hmem _ h₂
    _ ≤ ∑ γ, (Measure.dirac
          (p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H γ - E),
            physicalOrderedProfile p H γ)) (Prod.fst ⁻¹' I) :=
        Finset.sum_le_sum_of_subset hsub

end BlockBand.Critical.JointRecovery
