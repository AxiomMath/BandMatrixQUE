module
public import BlockBand.Counting.SimpleSpectralLimitsPortmanteau
public import BlockBand.Counting.PhysicalSpectralIntensity
public import BlockBand.Counting.PSSSPhysicalConsequences
public import BlockBand.Statements

/-!
# The physical two-point bound for marked laws

For a finite realization of the physical Gaussian ring, the spectral mass of a closed
interval under the marked configuration is almost surely the physical multiplicity count,
and the probability that an open interval of length `b - a` contains two unfolded
eigenvalues is at most `(𝕂 (b - a))²`, by the second factorial moment bound.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open BlockBand.External.PSSS BlockBand.Parameters
open scoped Topology ENNReal NNReal

/-- Closed-interval spectral mass equals the physical multiplicity count almost surely. -/
theorem finiteRealization_spectral_Icc_count_ae {p : Parameters} (R : FiniteRealization p)
    (E a b : ℝ) :
    ∀ᵐ H ∂(R.model.law : Measure p.SiteMatrix),
      (R.spectral.markedConfig E H).spectral.measure (Icc a b) =
        (p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E
          (semicircleDensity E) a b H : ℝ≥0∞) := by
  classical
  filter_upwards [R.model.isPhysical.1,
    BlockBand.QUE.Fourier.spectral_eigenvalue_eq_canonical_ae R.spectral,
    R.spectral.markedConfig_ae E] with H hH heig hconfig
  have hloc (α : Fin p.N) : R.spectral.unfoldedEigenvalue E H α =
      p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) H
        (BlockBand.Model.Construction.physicalSpectralRank p α) := by
    rw [SpectralRealization.unfoldedEigenvalue, heig α]
    unfold BlockBand.Model.Construction.physicalOrderedEigenvalue
    rw [BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ H hH,
      p.physicalUnfoldedEigenvalue_eq ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) H hH]
    simp
  have hc : finiteSpectralCount (fun H α => R.spectral.unfoldedEigenvalue E H α) (Icc a b) H =
      p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E
        (semicircleDensity E) a b H := by
    unfold finiteSpectralCount physicalUnfoldedIntervalCount eigenvalueCount
    simp_rw [hloc]
    let e : Fin p.N ≃ Fin (Fintype.card p.Site) :=
      { toFun := BlockBand.Model.Construction.physicalSpectralRank p
        invFun := Fin.cast (BlockBand.Model.Construction.physicalSite_card p)
        left_inv := by intro i; apply Fin.ext; rfl
        right_inv := by intro i; apply Fin.ext; rfl }
    simpa [Finset.sum_boole, e] using Equiv.sum_comp e
      (fun i => if p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E
        (semicircleDensity E) H i ∈ Icc a b then (1 : ℕ) else 0)
  rw [← hc, (R.spectral.markedConfig E H).spectral_eq,
    Measure.map_apply measurable_fst measurableSet_Icc, hconfig]
  simp [Measure.finsetSum_apply, measurableSet_Icc.preimage measurable_fst,
    Measure.dirac_apply', finiteSpectralCount, Finset.sum_boole,
    SpectralRealization.unfoldedEigenvalue, Set.indicator]

/-- The marked-law two-point event is controlled by the physical second factorial moment. -/
theorem finiteRealization_markedLaw_Ioo_twoPoint_bound {p : Parameters} (R : FiniteRealization p)
    (source : SourceContract.{0}) (E : ℝ) (hrho : 0 < semicircleDensity E)
    (a b : ℝ) (hab : a ≤ b) :
    (R.markedLaw E : Measure MarkedPointMeasure)
      {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo a b)} ≤
      ENNReal.ofReal ((p.physicalUnfoldedConstant source (semicircleDensity E) * (b-a)) ^ 2) := by
  let count := p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E
    (semicircleDensity E) a b
  let f := factorialCount count 2
  have hi : Integrable f (R.model.law : Measure p.SiteMatrix) :=
    R.model.physicalUnfoldedIntervalCount_integrable ⟨0, Matrix.isHermitian_zero⟩
      E (semicircleDensity E) a b 2
  have hn : 0 ≤ᵐ[(R.model.law : Measure p.SiteMatrix)] f :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  have hmark := mul_meas_ge_le_integral_of_nonneg hn hi (1 : ℝ)
  rw [one_mul] at hmark
  have hfac := R.model.physicalUnfoldedIntervalCount_factorialBound source
    ⟨0, Matrix.isHermitian_zero⟩ E (semicircleDensity E) hrho a b hab 2 (by omega)
  have hb : (R.model.law : Measure p.SiteMatrix) {H | (1 : ℝ) ≤ f H} ≤
      ENNReal.ofReal ((p.physicalUnfoldedConstant source (semicircleDensity E) * (b-a)) ^ 2) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (R.model.law : Measure p.SiteMatrix) _)]
    exact ENNReal.ofReal_le_ofReal (hmark.trans hfac)
  change Measure.map (R.spectral.markedConfig E) (R.model.law : Measure p.SiteMatrix) _ ≤ _
  rw [Measure.map_apply (R.spectral.measurable_markedConfig E)
    (isOpen_marked_Ioo_mass_gt a b 1).measurableSet]
  apply le_trans _ hb
  apply measure_mono_ae
  filter_upwards [finiteRealization_spectral_Icc_count_ae R E a b] with H hcount
  intro hcollision
  have hbig : (1 : ℝ≥0∞) < (count H : ℝ≥0∞) := by
    rw [← hcount]
    exact hcollision.trans_le (measure_mono Ioo_subset_Icc_self)
  have hnat : 2 ≤ count H := by exact_mod_cast hbig
  have hreal : (2 : ℝ) ≤ (count H : ℝ) := by exact_mod_cast hnat
  change 1 ≤ factorialCount count 2 H
  rw [factorialCount_eq_prod_sub]
  norm_num [Finset.prod_range_succ]
  nlinarith

end BlockBand.Counting
