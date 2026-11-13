module
public import BlockBand.QUE.Fourier.CyclicTransport
public import BlockBand.QUE.Fourier.PhysicalIntegrability
public import BlockBand.QUE.Haar.PhysicalBridge
/-!
# Finite physical weighted spatial intensity

For the microscopic coordinate `u_α = Nρ(E)(λ_α - E)` and every bounded measurable test `f`,
`E Σ_α f(u_α) p_{α,k} = (1/n) E Σ_α f(u_α)` for every block `k`, by cyclic invariance of the
physical law (`physical_weighted_spatial_identity`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open Matrix MeasureTheory BlockBand.Model.Construction
open scoped BigOperators

/-- The microscopic coordinate `Nρ(E)(λ_α - E)` of the physical model. -/
def canonicalMicroscopic (p : Parameters) (E : ℝ) (α : Fin p.N) (H : p.SiteMatrix) : ℝ :=
  p.N * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E)

theorem measurable_canonicalMicroscopic (p : Parameters) (E : ℝ) (α : Fin p.N) :
    Measurable (canonicalMicroscopic p E α) := by
  unfold canonicalMicroscopic
  exact measurable_const.mul ((measurable_physicalOrderedEigenvalue p α).sub measurable_const)

/-- Cyclic site conjugation preserves each increasing eigenvalue. -/
theorem physical_eigenvalue_cyclic (p : Parameters) (H : p.SiteMatrix) (hH : H.IsHermitian)
    (α : Fin p.N) (s : ZMod p.n) :
    physicalOrderedEigenvalue p (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) α =
      physicalOrderedEigenvalue p H α := by
  let U := sitePermutationUnitary p (p.cyclicSiteEquiv s)
  have h := congrFun (BlockBand.QUE.Haar.orderedEigenvalue_unitaryConjugate U
    (⟨H, hH⟩ : HermitianMatrix p.Site)) (physicalSpectralRank p α)
  rw [← sitePermutation_conjugation]
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ _ (Matrix.isHermitian_mul_mul_conjTranspose _ hH),
    rawIncreasingEigenvalue_eq _ H hH]
  exact h

/-- Every ordered complete eigensystem has, almost surely, the canonical eigenvalues of the same
rank. -/
theorem spectral_eigenvalue_eq_canonical_ae {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α : Fin p.N,
      spectral.eigenvalue H α = physicalOrderedEigenvalue p H α := by
  filter_upwards [model.isPhysical.1, spectral.orthonormal_ae,
    spectral.eigenvector_ae, spectral.ordered_ae] with H hH hv heig hell
  let R (i : Fin (Fintype.card p.Site)) : Fin p.N := Fin.cast (physicalSite_card p) i
  let ell (i : Fin (Fintype.card p.Site)) := spectral.eigenvalue H (R i)
  let v (i : Fin (Fintype.card p.Site)) := spectral.eigenvector H (R i)
  have hv₀ : ∀ i j, (∑ x, starRingEnd ℂ (v i x) * v j x) = if i = j then 1 else 0 := by
    intro i j
    simpa only [v, R, Fin.cast_inj] using hv (R i) (R j)
  have heig₀ : ∀ i, H *ᵥ v i = (ell i : ℂ) • v i := by
    intro i
    exact funext (heig (R i))
  have hell₀ : Monotone ell := by
    intro i j hij
    exact hell (R i) (R j) hij
  have h := BlockBand.QUE.Haar.orderedEigenvalue_eq_of_rank_eigenbasis
    (⟨H, hH⟩ : HermitianMatrix p.Site) ell v hv₀ heig₀ hell₀
  intro α
  have hval := congrFun h (physicalSpectralRank p α)
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ H hH]
  simpa only [orderedEigenvalue, ell, R, physicalSpectralRank, Fin.cast_cast, Fin.cast_eq_self] using hval.symm

/-- Measurable bounded microscopic tests are integrable under the physical law. -/
theorem integrable_canonicalMicroscopic_test (p : Parameters) (model : p.GaussianRingModel)
    (E : ℝ) (α : Fin p.N) (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ)
    (hbound : ∀ u, |f u| ≤ M) :
    Integrable (fun H => f (canonicalMicroscopic p E α H)) (model.law : Measure p.SiteMatrix) := by
  apply (integrable_const M).mono' (hf.comp (measurable_canonicalMicroscopic p E α)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun H => by
    change ‖f (canonicalMicroscopic p E α H)‖ ≤ M
    simpa only [Real.norm_eq_abs] using hbound _)

/-- The microscopic-test and block-mass weights are integrable. -/
theorem integrable_canonicalWeightedMass (p : Parameters) (model : p.GaussianRingModel)
    (E : ℝ) (α : Fin p.N) (k : ZMod p.n) (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    Integrable (fun H => f (canonicalMicroscopic p E α H) * physicalOrderedBlockMass p H α k)
      (model.law : Measure p.SiteMatrix) := by
  have hm := (hf.comp (measurable_canonicalMicroscopic p E α)).mul
    (measurable_physicalOrderedBlockMass p α k)
  apply ((integrable_physicalMass p model α k).const_mul M).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun H => by
    change ‖f (canonicalMicroscopic p E α H) * physicalOrderedBlockMass p H α k‖ ≤
      M * physicalOrderedBlockMass p H α k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (physicalOrderedBlockMass_nonneg p H α k)]
    exact mul_le_mul_of_nonneg_right (hbound _) (physicalOrderedBlockMass_nonneg p H α k))

/-- The rankwise weighted spatial identity for the canonical eigensystem, from cyclic
invariance. -/
theorem canonical_weighted_mass_identity (p : Parameters) (model : p.GaussianRingModel)
    (E : ℝ) (α : Fin p.N) (k : ZMod p.n) (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    (∫ H, f (canonicalMicroscopic p E α H) * physicalOrderedBlockMass p H α k
      ∂(model.law : Measure p.SiteMatrix)) =
      (p.n : ℝ)⁻¹ * (∫ H, f (canonicalMicroscopic p E α H) ∂(model.law : Measure p.SiteMatrix)) := by
  let V (j : ZMod p.n) := ∫ H, f (canonicalMicroscopic p E α H) *
    physicalOrderedBlockMass p H α j ∂(model.law : Measure p.SiteMatrix)
  have hmean (j : ZMod p.n) : V j = V 0 := by
    have hm : Measurable (fun H => f (canonicalMicroscopic p E α H) *
        physicalOrderedBlockMass p H α 0) :=
      (hf.comp (measurable_canonicalMicroscopic p E α)).mul (measurable_physicalOrderedBlockMass p α 0)
    have h := integral_map (p.measurable_siteReindexMatrix (p.cyclicSiteEquiv j)).aemeasurable
      (hm.aestronglyMeasurable : AEStronglyMeasurable _
        (Measure.map (p.siteReindexMatrix (p.cyclicSiteEquiv j)) (model.law : Measure p.SiteMatrix)))
    rw [model.map_cyclicMatrix j] at h
    change V 0 = _ at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [model.isPhysical.1, physical_blockMass_cyclic_ae p model α j] with H hH hmass
    rw [hmass 0, zero_add]
    unfold canonicalMicroscopic
    rw [physical_eigenvalue_cyclic p H hH α j]
  have hsum : (p.n : ℝ) * V 0 =
      ∫ H, f (canonicalMicroscopic p E α H) ∂(model.law : Measure p.SiteMatrix) := by
    calc
      _ = ∑ j : ZMod p.n, V j := by simp_rw [hmean]; simp
      _ = ∫ H, ∑ j : ZMod p.n, f (canonicalMicroscopic p E α H) *
          physicalOrderedBlockMass p H α j ∂(model.law : Measure p.SiteMatrix) :=
        (integral_finsetSum _ (fun j _ => integrable_canonicalWeightedMass p model E α j f hf M hbound)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
        rw [← Finset.mul_sum, hH α, mul_one]
  change V k = _
  rw [hmean k, ← hsum, ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (p.n : ℝ)), one_mul]

/-- Every realization has almost surely the same weighted rank/block observable as the canonical
one (eigenvalue and block mass use the same increasing rank). -/
theorem spectral_weighted_mass_eq_canonical_ae {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ) (α : Fin p.N) (k : ZMod p.n)
    (f : ℝ → ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      f (spectral.unfoldedEigenvalue E H α) * BlockBand.QUE.Haar.physicalBlockMass spectral α H k =
        f (canonicalMicroscopic p E α H) * physicalOrderedBlockMass p H α k := by
  filter_upwards [spectral_eigenvalue_eq_canonical_ae spectral,
    BlockBand.QUE.Haar.spectral_blockMass_eq_canonical_ae spectral] with H heig hmass
  have hb : BlockBand.QUE.Haar.physicalBlockMass spectral α H k =
      physicalOrderedBlockMass p H α k := hmass α k
  rw [hb]
  unfold Parameters.SpectralRealization.unfoldedEigenvalue canonicalMicroscopic
  rw [heig α]

/-- Bounded measurable microscopic tests of every realization are integrable. -/
theorem integrable_spectralMicroscopic_test {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ) (α : Fin p.N)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    Integrable (fun H => f (spectral.unfoldedEigenvalue E H α)) (model.law : Measure p.SiteMatrix) := by
  apply (integrable_canonicalMicroscopic_test p model E α f hf M hbound).congr
  filter_upwards [spectral_eigenvalue_eq_canonical_ae spectral] with H heig
  unfold Parameters.SpectralRealization.unfoldedEigenvalue canonicalMicroscopic
  rw [heig α]

/-- The weighted spectral rank/block observables are integrable under every physical
realization. -/
theorem integrable_spectralWeightedMass {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ) (α : Fin p.N) (k : ZMod p.n)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    Integrable (fun H => f (spectral.unfoldedEigenvalue E H α) *
      BlockBand.QUE.Haar.physicalBlockMass spectral α H k) (model.law : Measure p.SiteMatrix) := by
  apply (integrable_canonicalWeightedMass p model E α k f hf M hbound).congr
  filter_upwards [spectral_weighted_mass_eq_canonical_ae spectral E α k f] with H hH
  exact hH.symm

/-- The rankwise weighted spatial identity for every physical realization: with the microscopic
coordinate `Nρ(E)(λ - E)`, the block factor is `1/n` under the Gaussian law. -/
theorem physical_rank_weighted_mass_identity {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ) (α : Fin p.N) (k : ZMod p.n)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    (∫ H, f (spectral.unfoldedEigenvalue E H α) * BlockBand.QUE.Haar.physicalBlockMass spectral α H k
      ∂(model.law : Measure p.SiteMatrix)) =
      (p.n : ℝ)⁻¹ * (∫ H, f (spectral.unfoldedEigenvalue E H α) ∂(model.law : Measure p.SiteMatrix)) := by
  rw [integral_congr_ae (spectral_weighted_mass_eq_canonical_ae spectral E α k f),
    canonical_weighted_mass_identity p model E α k f hf M hbound]
  congr 1
  apply integral_congr_ae
  filter_upwards [spectral_eigenvalue_eq_canonical_ae spectral] with H heig
  unfold Parameters.SpectralRealization.unfoldedEigenvalue canonicalMicroscopic
  rw [heig α]

/-- Integrability of the rank-summed spatial weights. -/
theorem integrable_spectralWeightedMass_sum {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ) (k : ZMod p.n)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    Integrable (fun H => ∑ α : Fin p.N, f (spectral.unfoldedEigenvalue E H α) *
      BlockBand.QUE.Haar.physicalBlockMass spectral α H k) (model.law : Measure p.SiteMatrix) :=
  integrable_finsetSum _ (fun α _ => integrable_spectralWeightedMass spectral E α k f hf M hbound)

/-- Integrability of the microscopic-test rank sum. -/
theorem integrable_spectralMicroscopic_test_sum {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    Integrable (fun H => ∑ α : Fin p.N, f (spectral.unfoldedEigenvalue E H α))
      (model.law : Measure p.SiteMatrix) :=
  integrable_finsetSum _ (fun α _ => integrable_spectralMicroscopic_test spectral E α f hf M hbound)

/-- The finite weighted spatial identity used for stationarity:
`E Σ_α f(u_α) p_{α,k} = (1/n) E Σ_α f(u_α)`, for every realization, block, real energy and
bounded measurable real test. -/
theorem physical_weighted_spatial_identity {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (E : ℝ) (k : ZMod p.n)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ u, |f u| ≤ M) :
    (∫ H, ∑ α : Fin p.N, f (spectral.unfoldedEigenvalue E H α) *
      BlockBand.QUE.Haar.physicalBlockMass spectral α H k ∂(model.law : Measure p.SiteMatrix)) =
      (p.n : ℝ)⁻¹ *
        (∫ H, ∑ α : Fin p.N, f (spectral.unfoldedEigenvalue E H α) ∂(model.law : Measure p.SiteMatrix)) := by
  rw [integral_finsetSum _ (fun α _ => integrable_spectralWeightedMass spectral E α k f hf M hbound),
    integral_finsetSum _ (fun α _ => integrable_spectralMicroscopic_test spectral E α f hf M hbound)]
  simp_rw [physical_rank_weighted_mass_identity spectral E _ k f hf M hbound]
  exact (Finset.mul_sum _ _ _).symm
end BlockBand.QUE.Fourier
