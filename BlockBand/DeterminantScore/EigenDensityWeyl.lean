module

public import BlockBand.DeterminantScore.EigenDensity
public import BlockBand.Angular.DetFactorGUE

/-!
# The Weyl/HCIZ eigenvalue density of `K + G_m(t)` from the Weyl integration formula

Used in the proof of the indexed spectral convexity lemma.

* `hermGaussian_eq_withDensity`, `hermGaussianDensity_eq`: `G_m(t)` has the Lebesgue density
  `c_t exp(-Re tr H²/(2t))` in the coordinates `HermCoord m` (`t > 0`).
* `lintegral_orderedEigs_eq`: translation by `K`.
* `freshEigenvalue_conj_diagonal`: the increasing eigenvalues of `U diag(λ) U*` are `λ`.
* `trace_conj_sub_sq_re`: the trace expansion giving the HCIZ phase.
* `weylHCIZDensity_of`: `WeylIntegrationStatement → WeylHCIZDensityStatement`.

`WeylIntegrationStatement` (the classical Weyl integration formula) is a named `Prop`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.EigenDensity

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector Polynomial
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.QUE.Haar
open scoped ENNReal NNReal

variable {m : ℕ}

/-- The Lebesgue density `∏_c φ_{v_c}(x_c)` of `G_m(t)` in the coordinates `HermCoord m`. -/
noncomputable def hermGaussianDensity (m : ℕ) (t : ℝ≥0) (x : HermCoord m → ℝ) : ℝ :=
  ∏ c, ProbabilityTheory.gaussianPDFReal 0 (hermVariance m t c) (x c)

theorem hermVariance_ne_zero {t : ℝ≥0} (ht : 0 < t) (c : HermCoord m) :
    hermVariance m t c ≠ 0 := by
  unfold hermVariance; split_ifs <;> positivity

/-- `G_m(t)` (`t > 0`) has the product Gaussian Lebesgue density on `HermCoord m → ℝ`. -/
theorem hermGaussian_eq_withDensity {t : ℝ≥0} (ht : 0 < t) :
    hermGaussian m t = volume.withDensity fun x => ENNReal.ofReal (hermGaussianDensity m t x) := by
  unfold hermGaussian BlockBand.Internal.Contracts.Inputs.gaussianProduct
  refine Measure.pi_eq fun s hs => ?_
  set f : HermCoord m → ℝ → ℝ := fun c y =>
    (s c).indicator (ProbabilityTheory.gaussianPDFReal 0 (hermVariance m t c)) y with hf
  have hfn : ∀ c y, 0 ≤ f c y := fun c y =>
    Set.indicator_nonneg (fun _ _ => ProbabilityTheory.gaussianPDFReal_nonneg _ _ _) _
  have hfi : ∀ c, Integrable (f c) := fun c =>
    (ProbabilityTheory.integrable_gaussianPDFReal 0 _).indicator (hs c)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have hind : ∀ x, (Set.univ.pi s).indicator
      (fun x => ENNReal.ofReal (hermGaussianDensity m t x)) x =
      ENNReal.ofReal (∏ c, f c (x c)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      simp only [hf]
      rw [Set.indicator_of_mem (hx c (Set.mem_univ c))]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨c, hc⟩ : ∃ c, x c ∉ s c := by
        by_contra h
        push Not at h
        exact hx fun c _ => h c
      rw [Finset.prod_eq_zero (Finset.mem_univ c) (by simp only [hf]; rw [Set.indicator_of_notMem hc]),
        ENNReal.ofReal_zero]
  simp_rw [hind]
  rw [← ofReal_integral_eq_lintegral_ofReal, volume_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun c _ => integral_nonneg (hfn c))]
  · refine Finset.prod_congr rfl fun c _ => ?_
    rw [ProbabilityTheory.gaussianReal_apply _ (hermVariance_ne_zero ht c),
      ofReal_integral_eq_lintegral_ofReal (hfi c)
      (Filter.Eventually.of_forall (hfn c)), ← lintegral_indicator (hs c)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ s c
    · simp [hf, Set.indicator_of_mem hy, ProbabilityTheory.gaussianPDF]
    · simp [hf, Set.indicator_of_notMem hy]
  · rw [volume_pi]; exact Integrable.fintype_prod hfi
  · exact Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun c _ => hfn c (x c)

/-- The normalizing constant `∏_c (2π v_c)^{-1/2}`. -/
noncomputable def hermGaussianConst (m : ℕ) (t : ℝ≥0) : ℝ :=
  ∏ c : HermCoord m, (√(2 * Real.pi * hermVariance m t c))⁻¹

theorem hermGaussianConst_pos {t : ℝ≥0} (ht : 0 < t) : 0 < hermGaussianConst m t := by
  refine Finset.prod_pos fun c _ => inv_pos.2 (Real.sqrt_pos.2 ?_)
  have := hermVariance_ne_zero ht c
  have : (0 : ℝ) < hermVariance m t c := by positivity
  positivity

/-- The density is `c_t exp(-Re tr H(x)²/(2t))` (`Re tr H(x)² = Σ_c w_c x_c²`). -/
theorem hermGaussianDensity_eq {t : ℝ≥0} (ht : 0 < t) (x : HermCoord m → ℝ) :
    hermGaussianDensity m t x = hermGaussianConst m t *
      Real.exp (-(hermOfCoord x * hermOfCoord x).trace.re / (2 * (t : ℝ))) := by
  have htR : (0 : ℝ) < t := ht
  unfold hermGaussianDensity hermGaussianConst
  simp only [ProbabilityTheory.gaussianPDFReal_def, sub_zero]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, BlockBand.Angular.DetFactor.re_trace_hermOfCoord_mul,
    neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold hermVariance BlockBand.Angular.DetFactor.coordWeight
  split_ifs
  · field_simp
  · push_cast
    field_simp

theorem hermOfCoord_sub (x y : HermCoord m → ℝ) :
    hermOfCoord (x - y) = hermOfCoord x - hermOfCoord y := by
  refine eq_sub_of_add_eq ?_
  rw [← hermOfCoord_add, sub_add_cancel]

theorem measurable_freshEigs :
    Measurable fun M : Matrix (Fin m) (Fin m) ℂ =>
      fun k => BlockBand.Internal.Contracts.CoareaPalm.freshEigenvalue M k :=
  Measurable.of_eval fun _ =>
    BlockBand.Model.Construction.measurable_rawIncreasingEigenvalue _

/-- Translation: `E g(λ(K + G)) = ∫ g(λ(H)) c_t e^{-tr(H-K)²/(2t)} dH` (Lebesgue on coordinates). -/
theorem lintegral_orderedEigs_eq {t : ℝ≥0} (ht : 0 < t) {K : Matrix (Fin m) (Fin m) ℂ}
    (hK : K.IsHermitian) {g : (Fin m → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g (BlockBand.DeterminantScore.orderedEigs K x) ∂hermGaussian m t =
      ∫⁻ y, g (fun k => BlockBand.Internal.Contracts.CoareaPalm.freshEigenvalue (hermOfCoord y) k) *
        ENNReal.ofReal (hermGaussianConst m t * Real.exp
          (-((hermOfCoord y - K) * (hermOfCoord y - K)).trace.re / (2 * (t : ℝ)))) := by
  have hρm : Measurable fun x => ENNReal.ofReal (hermGaussianDensity m t x) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact Finset.measurable_prod _ fun c _ =>
      (ProbabilityTheory.measurable_gaussianPDFReal _ _).comp (measurable_pi_apply c)
  have hgm : Measurable fun x => g (BlockBand.DeterminantScore.orderedEigs K x) :=
    hg.comp (BlockBand.DeterminantScore.NegativeSpread.measurable_orderedEigs K)
  rw [hermGaussian_eq_withDensity ht, lintegral_withDensity_eq_lintegral_mul _ hρm hgm]
  set κ := coordOfMatrix K with hκ
  have hHκ : hermOfCoord κ = K := hermOfCoord_coordOfMatrix hK
  rw [← lintegral_sub_right_eq_self _ κ]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm, hermGaussianDensity_eq ht, hermOfCoord_sub, hHκ]
  congr 2
  unfold BlockBand.DeterminantScore.orderedEigs
  rw [hermOfCoord_sub, hHκ, add_sub_cancel]

theorem monotone_freshEigenvalue {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian) :
    Monotone fun k => freshEigenvalue M k := by
  intro i j hij
  simp only [freshEigenvalue, BlockBand.Model.Construction.rawIncreasingEigenvalue, hM, dite_true]
  exact BlockBand.Foundations.Spectral.increasingEigenvalue_monotone hM (by simpa using hij)

theorem multiset_eigenvalues_eq {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian)
    {lam : Fin m → ℝ} (hc : M.charpoly = ∏ i, (X - C ((lam i : ℂ)))) :
    Finset.univ.val.map hM.eigenvalues = Finset.univ.val.map lam := by
  have h1 := hM.charpoly_eq
  rw [hc, Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod] at h1
  have h2 := congrArg Polynomial.roots h1
  have e1 : (Finset.univ.val.map fun i => X - C ((lam i : ℝ) : ℂ)) =
      (Finset.univ.val.map fun i => ((lam i : ℝ) : ℂ)).map (fun z : ℂ => X - C z) := by
    rw [Multiset.map_map]; rfl
  have e2 : (Finset.univ.val.map fun i => X - C ((hM.eigenvalues i : ℝ) : ℂ)) =
      (Finset.univ.val.map fun i => ((hM.eigenvalues i : ℝ) : ℂ)).map (fun z : ℂ => X - C z) := by
    rw [Multiset.map_map]; rfl
  rw [e1, roots_multiset_prod_X_sub_C] at h2
  erw [e2, roots_multiset_prod_X_sub_C] at h2
  have h3 := congrArg (Multiset.map Complex.re) h2
  simp only [Multiset.map_map, Function.comp_def] at h3
  simpa using h3.symm

/-- A Hermitian matrix with characteristic polynomial `∏(X - λ_i)`, `λ` monotone, has increasing
eigenvalues `λ`. -/
theorem freshEigenvalue_eq_of_charpoly {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian)
    {lam : Fin m → ℝ} (hlam : Monotone lam) (hc : M.charpoly = ∏ i, (X - C ((lam i : ℂ)))) :
    (fun k => freshEigenvalue M k) = lam := by
  obtain ⟨e, he⟩ := BlockBand.DeterminantScore.SpectralConvexity.exists_equiv_freshEigenvalue hM
  have hmul : Finset.univ.val.map (fun k => freshEigenvalue M k) = Finset.univ.val.map lam := by
    rw [← multiset_eigenvalues_eq hM hc]
    simp_rw [he]
    rw [show (fun x => hM.eigenvalues (e x)) = hM.eigenvalues ∘ e from rfl,
      ← Multiset.map_map hM.eigenvalues e]
    congr 1
    have := Finset.map_univ_equiv e
    simp
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hmul
  exact List.ofFn_injective (hmul.eq_of_sortedLE (monotone_freshEigenvalue hM).sortedLE_ofFn
    hlam.sortedLE_ofFn)

/-- The increasing eigenvalues of `U diag(λ) U*` are `λ` for monotone `λ`. -/
theorem freshEigenvalue_conj_diagonal (U : Matrix.unitaryGroup (Fin m) ℂ) {lam : Fin m → ℝ}
    (hlam : Monotone lam) :
    (fun k => freshEigenvalue ((U : Matrix (Fin m) (Fin m) ℂ) *
      diagonal (fun i => (lam i : ℂ)) * star (U : Matrix (Fin m) (Fin m) ℂ)) k) = lam := by
  have hD : (diagonal (fun i => (lam i : ℂ))).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  have hM : ((U : Matrix (Fin m) (Fin m) ℂ) * diagonal (fun i => (lam i : ℂ)) *
      star (U : Matrix (Fin m) (Fin m) ℂ)).IsHermitian := by
    rw [Matrix.star_eq_conjTranspose]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hD
  refine freshEigenvalue_eq_of_charpoly hM hlam ?_
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self,
    Matrix.one_mul, Matrix.charpoly_diagonal]

/-- `Re tr(UΛU* - K)² = |λ|² + Re tr K² - 2 Σ_i λ_i Re(U*KU)_{ii}`. -/
theorem trace_conj_sub_sq_re (U : Matrix.unitaryGroup (Fin m) ℂ) (lam : Fin m → ℝ)
    (K : Matrix (Fin m) (Fin m) ℂ) :
    (((U : Matrix (Fin m) (Fin m) ℂ) * diagonal (fun i => (lam i : ℂ)) *
        star (U : Matrix (Fin m) (Fin m) ℂ) - K) *
      ((U : Matrix (Fin m) (Fin m) ℂ) * diagonal (fun i => (lam i : ℂ)) *
        star (U : Matrix (Fin m) (Fin m) ℂ) - K)).trace.re =
      ∑ j, lam j ^ 2 + (K * K).trace.re -
        2 * ∑ i, (((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * K * (U : Matrix (Fin m) (Fin m) ℂ)) i i).re *
          lam i := by
  set V : Matrix (Fin m) (Fin m) ℂ := (U : Matrix (Fin m) (Fin m) ℂ) with hVdef
  set D : Matrix (Fin m) (Fin m) ℂ := diagonal (fun i => (lam i : ℂ))
  have hVV : star V * V = 1 := Matrix.UnitaryGroup.star_mul_self U
  have hAA : (V * D * star V * (V * D * star V)).trace = (D * D).trace := by
    rw [show V * D * star V * (V * D * star V) = V * (D * (star V * V) * D * star V) by
      simp only [Matrix.mul_assoc], hVV, Matrix.mul_one, Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hAK : (V * D * star V * K).trace = (D * (Vᴴ * K * V)).trace := by
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have hKA : (K * (V * D * star V)).trace = (V * D * star V * K).trace := Matrix.trace_mul_comm _ _
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, hAA, hKA, hAK]
  simp only [D, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
    Matrix.diagonal_apply_eq, Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.mul_sum]
  have : ∀ i, lam i * lam i = lam i ^ 2 := fun i => (sq (lam i)).symm
  simp only [this]
  have h2 : ∑ i, lam i * ((Vᴴ * K * V) i i).re = ∑ i, ((Vᴴ * K * V) i i).re * lam i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2, ← Finset.mul_sum]
  ring

theorem integrable_exp_hcizPhase (t : ℝ) (K : Matrix (Fin m) (Fin m) ℂ) (lam : Fin m → ℝ) :
    Integrable (fun U => Real.exp (hcizPhase t K U lam)) (unitaryProbability (A := Fin m)) := by
  have hc : Continuous fun U => Real.exp (hcizPhase t K U lam) :=
    Real.continuous_exp.comp ((continuous_hcizPhase t K).clm_apply continuous_const)
  obtain ⟨C, -, hC⟩ := exists_norm_bound hc
  exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- **Weyl integration formula for Hermitian matrices** (`dH = c_m Δ(λ)² dλ dU` on the Weyl
chamber, eigenvectors Haar). For each `m` there is `C > 0` such that for every measurable
`f ≥ 0` on matrices, `∫ f(H(x)) dx = C ∫_𝒞 Δ(λ)² ∫_{U(m)} f(U diag(λ) U*) dU dλ`, with Lebesgue
measure on the coordinates `HermCoord m` and normalized Haar measure. A classical identity, not
proved here: the Weyl integration formula for general integrands (e.g. Anderson–Guionnet–Zeitouni,
*An Introduction to Random Matrices*, §4.1; their Thm. 2.5.2 is the Gaussian case). -/
def WeylIntegrationStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ f : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞, Measurable f →
    ∫⁻ x, f (hermOfCoord x) = ENNReal.ofReal C *
      ∫⁻ lam in BlockBand.DeterminantScore.SpectralConvexity.weylChamber m,
        ENNReal.ofReal (BlockBand.DeterminantScore.SpectralConvexity.vandermonde lam ^ 2) *
          ∫⁻ U, f ((U : Matrix (Fin m) (Fin m) ℂ) * diagonal (fun i => (lam i : ℂ)) *
            star (U : Matrix (Fin m) (Fin m) ℂ)) ∂(unitaryProbability (A := Fin m))

/-- **`WeylHCIZDensityStatement` from the Weyl integration formula**: Gaussian density,
translation by `K`, `λ(UΛU*) = λ` on the chamber and the trace expansion; the constant is
`c = C c_t e^{-Re tr K²/(2t)}`. -/
theorem weylHCIZDensity_of (hW : WeylIntegrationStatement) : WeylHCIZDensityStatement := by
  intro m t K ht hK
  obtain ⟨C, hC, hrep⟩ := hW m
  have htR : (0 : ℝ) < t := ht
  set cG := hermGaussianConst m t with hcG
  have hcG0 : 0 < cG := hermGaussianConst_pos ht
  refine ⟨C * cG * Real.exp (-(K * K).trace.re / (2 * (t : ℝ))), by positivity, fun g hg => ?_⟩
  rw [lintegral_orderedEigs_eq ht hK hg]
  set F : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞ := fun M =>
    g (fun k => freshEigenvalue M k) * ENNReal.ofReal (cG *
      Real.exp (-((M - K) * (M - K)).trace.re / (2 * (t : ℝ)))) with hF
  have hFm : Measurable F := by
    refine (hg.comp measurable_freshEigs).mul (ENNReal.measurable_ofReal.comp ?_)
    refine Continuous.measurable ?_
    refine continuous_const.mul (Real.continuous_exp.comp ?_)
    refine (Complex.continuous_re.comp ?_).neg.div_const _
    exact ((continuous_id.sub continuous_const).matrix_mul
      (continuous_id.sub continuous_const)).matrix_trace
  refine (hrep F hFm).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun
    BlockBand.DeterminantScore.SpectralConvexity.isOpen_weylChamber.measurableSet
    fun lam hlam => ?_
  have hmono : Monotone lam := (show StrictMono lam from hlam).monotone
  have hinner : ∀ U : Matrix.unitaryGroup (Fin m) ℂ,
      F ((U : Matrix (Fin m) (Fin m) ℂ) * diagonal (fun i => (lam i : ℂ)) *
        star (U : Matrix (Fin m) (Fin m) ℂ)) =
      g lam * ENNReal.ofReal (cG * Real.exp (-(∑ j, lam j ^ 2 + (K * K).trace.re) /
        (2 * (t : ℝ)))) * ENNReal.ofReal (Real.exp (hcizPhase t K U lam)) := by
    intro U
    simp only [hF]
    set r : Fin m → ℝ := fun i =>
      (((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * K * (U : Matrix (Fin m) (Fin m) ℂ)) i i).re with hr
    have hsum : ∑ i, r i / t * lam i = (∑ i, r i * lam i) / t := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hexp : -(∑ j, lam j ^ 2 + (K * K).trace.re - 2 * ∑ i, r i * lam i) / (2 * (t : ℝ)) =
        -(∑ j, lam j ^ 2 + (K * K).trace.re) / (2 * (t : ℝ)) + ∑ i, r i / t * lam i := by
      rw [hsum]
      field_simp
      ring
    rw [freshEigenvalue_conj_diagonal U hmono, trace_conj_sub_sq_re, mul_assoc (g lam),
      ← ENNReal.ofReal_mul (by positivity), mul_assoc cG, ← Real.exp_add, hcizPhase_apply]
    rw [← hexp]
  simp_rw [hinner]
  have hI : ∫⁻ U, ENNReal.ofReal (Real.exp (hcizPhase t K U lam)) ∂(unitaryProbability (A := Fin m))
      = ENNReal.ofReal (hcizIntegral t K lam) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_exp_hcizPhase _ K lam)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm
  have hmeas : Measurable fun U : Matrix.unitaryGroup (Fin m) ℂ =>
      ENNReal.ofReal (Real.exp (hcizPhase t K U lam)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      ((continuous_hcizPhase _ K).clm_apply continuous_const)).measurable
  rw [lintegral_const_mul _ hmeas, hI]
  have hΔ : 0 ≤ BlockBand.DeterminantScore.SpectralConvexity.vandermonde lam ^ 2 := sq_nonneg _
  have hreal : C * cG * Real.exp (-(K * K).trace.re / (2 * (t : ℝ))) *
      BlockBand.DeterminantScore.SpectralConvexity.vandermonde lam ^ 2 *
      Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * hcizIntegral t K lam =
      C * (BlockBand.DeterminantScore.SpectralConvexity.vandermonde lam ^ 2 *
        ((cG * Real.exp (-(∑ j, lam j ^ 2 + (K * K).trace.re) / (2 * (t : ℝ)))) *
          hcizIntegral t K lam)) := by
    rw [show -(∑ j, lam j ^ 2 + (K * K).trace.re) / (2 * (t : ℝ)) =
      -(∑ j, lam j ^ 2) / (2 * (t : ℝ)) + -(K * K).trace.re / (2 * (t : ℝ)) by ring, Real.exp_add]
    ring
  have hh := (hcizIntegral_pos (t : ℝ) K lam).le
  rw [hreal]
  simp (disch := positivity) only [ENNReal.ofReal_mul]
  ring

end BlockBand.DeterminantScore.EigenDensity
