module

public import BlockBand.DeterminantScore.NegativeSpreadSpectral

/-!
# The normalized sector law

For Hermitian `K`, `t > 0` and an attainable sector (`Re Z_ℓ(K) > 0`):
* `sectorLaw m t K ℓ` is a probability measure (`isProbabilityMeasure_sectorLaw`) and
  `∫⁻ g dsectorLaw = (Re Z)⁻¹ ∫⁻ (Re 1{sector}det²) g dG` (`lintegral_sectorLaw`);
* under it `det(K + G) ≠ 0` a.s. (`ae_det_ne_zero_sectorLaw`), and, given the `density` clause of
  `IndexedSpectralConvexityStatement`, the ordered eigenvalues lie in the chamber a.s.
  (`ae_mem_chamber`);
* the determinant square makes `U` integrable: `U = invSqSum(λ)` and `U⁻¹` are integrable
  (`integrable_invSqSum`, `integrable_inv_invSqSum`), by domination of
  `1{sector}det²·U = Tr(adj M)²` and `1{sector}det²·Tr M²` by Gaussian-integrable polynomials
  (`Sector.integrable_cut`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open scoped ENNReal NNReal

variable {m : ℕ} {t : ℝ≥0} {K : Matrix (Fin m) (Fin m) ℂ} {ℓ : ℕ}

/-- The determinant of a Hermitian matrix is real. -/
theorem det_im_eq_zero' {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) : M.det.im = 0 := by
  have h := congrArg Matrix.det hM.eq
  rw [det_conjTranspose] at h
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem sectorDetSq_im (hK : K.IsHermitian) (x : HermCoord m → ℝ) :
    (sectorDetSq K ℓ x).im = 0 := by
  unfold sectorDetSq
  split_ifs
  · have h := det_im_eq_zero' (isHermitian_add_hermOfCoord hK x)
    simp [sq, Complex.mul_im, h]
  · simp

theorem sectorDetSq_re_nonneg (hK : K.IsHermitian) (x : HermCoord m → ℝ) :
    0 ≤ (sectorDetSq K ℓ x).re := by
  unfold sectorDetSq
  split_ifs
  · have h := det_im_eq_zero' (isHermitian_add_hermOfCoord hK x)
    rw [sq, Complex.mul_re, h]
    nlinarith [mul_self_nonneg (K + hermOfCoord x).det.re]
  · simp

theorem integrable_sectorDetSq (hK : K.IsHermitian) :
    Integrable (sectorDetSq K ℓ) (hermGaussian m t) := by
  rw [sectorDetSq_eq_cut, hermGaussian_eq]
  exact integrable_cut hK ℓ _ _

theorem measurable_sectorDetSq (hK : K.IsHermitian) : Measurable (sectorDetSq K ℓ) := by
  rw [sectorDetSq_eq_cut]
  exact measurable_cut hK ℓ _

theorem lintegral_sectorDetSq (hK : K.IsHermitian) :
    ∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re ∂hermGaussian m t =
      ENNReal.ofReal (sectorMass m t K ℓ).re := by
  have hi := integrable_sectorDetSq (t := t) (ℓ := ℓ) hK
  have h1 : (∫ x, sectorDetSq K ℓ x ∂hermGaussian m t).re =
      ∫ x, (sectorDetSq K ℓ x).re ∂hermGaussian m t := (integral_re hi).symm
  rw [sectorMass, h1]
  exact (ofReal_integral_eq_lintegral_ofReal hi.re
    (ae_of_all _ (sectorDetSq_re_nonneg hK))).symm

theorem measurable_sectorDensity (hK : K.IsHermitian) :
    Measurable fun x => ENNReal.ofReal ((sectorDetSq K ℓ x).re / (sectorMass m t K ℓ).re) :=
  ENNReal.measurable_ofReal.comp
    ((Complex.measurable_re.comp (measurable_sectorDetSq hK)).div_const _)

/-- `∫⁻ g dsectorLaw = (Re Z)⁻¹ ∫⁻ (Re 1{sector}det²) g dG`. -/
theorem lintegral_sectorLaw (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re)
    {g : (HermCoord m → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂sectorLaw m t K ℓ = (ENNReal.ofReal (sectorMass m t K ℓ).re)⁻¹ *
      ∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re * g x ∂hermGaussian m t := by
  rw [sectorLaw, lintegral_withDensity_eq_lintegral_mul _ (measurable_sectorDensity hK) hg,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne')]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm (ENNReal.ofReal _), mul_assoc]

theorem isProbabilityMeasure_sectorLaw (hK : K.IsHermitian)
    (hZ : 0 < (sectorMass m t K ℓ).re) : IsProbabilityMeasure (sectorLaw m t K ℓ) := by
  constructor
  rw [← lintegral_one, lintegral_sectorLaw hK hZ measurable_const]
  simp only [mul_one]
  rw [lintegral_sectorDetSq hK]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne' ENNReal.ofReal_ne_top

theorem sectorLaw_absolutelyContinuous : sectorLaw m t K ℓ ≪ hermGaussian m t :=
  withDensity_absolutelyContinuous _ _

theorem ae_det_ne_zero_sectorLaw (ht : 0 < t) :
    ∀ᵐ x ∂sectorLaw m t K ℓ, (K + hermOfCoord x).det ≠ 0 :=
  sectorLaw_absolutelyContinuous.ae_le (ae_det_ne_zero ht K)

theorem measurableSet_chamber : MeasurableSet (chamber m ℓ) := by
  have hset : chamber m ℓ = (⋂ i : Fin m, ⋂ j : Fin m, {lam : Fin m → ℝ | i < j → lam i < lam j}) ∩
      ⋂ k : Fin m, ({lam : Fin m → ℝ | k.val < ℓ → lam k < 0} ∩
        {lam : Fin m → ℝ | ℓ ≤ k.val → 0 < lam k}) := by
    ext lam
    simp only [chamber, StrictMono, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun k => MeasurableSet.inter ?_ ?_)
  · by_cases hij : i < j
    · simpa [hij] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    · simp [hij]
  · by_cases hk : k.val < ℓ
    · simpa [hk] using measurableSet_lt (measurable_pi_apply k) measurable_const
    · simp [hk]
  · by_cases hk : ℓ ≤ k.val
    · simpa [hk] using measurableSet_lt measurable_const (measurable_pi_apply k)
    · simp [hk]

/-- Under the normalized sector law the ordered eigenvalues lie in the chamber a.s. (`density`
clause of `IndexedSpectralConvexityStatement`). -/
theorem ae_mem_chamber (hconv : IndexedSpectralConvexityStatement) (ht : 0 < t)
    (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re) :
    ∀ᵐ x ∂sectorLaw m t K ℓ, orderedEigs K x ∈ chamber m ℓ := by
  obtain ⟨𝒰, -, hdens, -⟩ := hconv.density m t K ℓ ht hK hZ
  set G : (Fin m → ℝ) → ℝ≥0∞ := (chamber m ℓ)ᶜ.indicator 1 with hGdef
  have hGm : Measurable G := measurable_one.indicator measurableSet_chamber.compl
  have hzero : ∫⁻ lam in chamber m ℓ, ENNReal.ofReal (Real.exp (-𝒰 lam)) * G lam = 0 := by
    rw [setLIntegral_congr_fun measurableSet_chamber
      (g := fun _ => (0 : ℝ≥0∞)) (fun lam hlam => by simp [hGdef, hlam])]
    simp
  rw [ae_iff]
  have hpre : {x | ¬ orderedEigs K x ∈ chamber m ℓ} = orderedEigs K ⁻¹' (chamber m ℓ)ᶜ := rfl
  have hind : ∀ x, (orderedEigs K ⁻¹' (chamber m ℓ)ᶜ).indicator 1 x = G (orderedEigs K x) := by
    intro x
    simp only [hGdef]
    rfl
  rw [hpre, ← lintegral_indicator_one
    (measurable_orderedEigs K measurableSet_chamber.compl), lintegral_sectorLaw hK hZ
    ((measurable_one.indicator (measurable_orderedEigs K measurableSet_chamber.compl)))]
  simp_rw [hind]
  rw [hdens G hGm, hzero, mul_zero, mul_zero]

theorem integrable_of_lintegral_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤) : Integrable f μ :=
  ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).2 h⟩

/-- Domination by a Gaussian-integrable cut polynomial gives finite sector-law integral. -/
theorem lintegral_sectorLaw_lt_top (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re)
    (Q : MvPolynomial (HermCoord m) ℂ) {G : (HermCoord m → ℝ) → ℝ} (hG : Measurable G)
    (hle : ∀ x, (sectorDetSq K ℓ x).re * G x ≤ ‖cut K ℓ Q x‖) :
    ∫⁻ x, ENNReal.ofReal (G x) ∂sectorLaw m t K ℓ < ⊤ := by
  rw [lintegral_sectorLaw hK hZ (g := fun x => ENNReal.ofReal (G x))
    (ENNReal.measurable_ofReal.comp hG)]
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hZ)) ?_
  have hint : Integrable (cut K ℓ Q) (hermGaussian m t) := by
    rw [hermGaussian_eq]; exact integrable_cut hK ℓ Q _
  calc ∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re * ENNReal.ofReal (G x) ∂hermGaussian m t
      ≤ ∫⁻ x, ENNReal.ofReal ‖cut K ℓ Q x‖ ∂hermGaussian m t := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (sectorDetSq_re_nonneg hK x)]
        exact ENNReal.ofReal_le_ofReal (hle x)
    _ < ⊤ := hint.norm.lintegral_lt_top

theorem realEval_hermPolyMatrix (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ)
    (a b : Fin m) : realEval (hermPolyMatrix K a b) x = (K + hermOfCoord x) a b := by
  have h := congrArg (fun A => A a b) (mapMatrix_eval_hermPolyMatrix K x)
  simpa [realEval] using h

theorem trace_mul_self_eq_sum {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    (A * A).trace = ∑ a, ∑ b, A a b * A b a := by
  simp [Matrix.trace, Matrix.mul_apply]

/-- `Σ_{a,b} adj_ab adj_ba = Tr (adj M)²`. -/
def adjSqPoly (K : Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (HermCoord m) ℂ :=
  ∑ a, ∑ b, adjPoly K a b * adjPoly K b a

/-- `det² Σ_{a,b} M_ab M_ba = det² Tr M²`. -/
def detSqTraceSqPoly (K : Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (HermCoord m) ℂ :=
  detSqPoly K * ∑ a, ∑ b, hermPolyMatrix K a b * hermPolyMatrix K b a

theorem realEval_adjSqPoly (x : HermCoord m → ℝ) :
    realEval (adjSqPoly K) x =
      ((K + hermOfCoord x).adjugate * (K + hermOfCoord x).adjugate).trace := by
  rw [trace_mul_self_eq_sum]
  simp [adjSqPoly, realEval, map_sum, map_mul, ← realEval_adjPoly]

theorem realEval_detSqTraceSqPoly (x : HermCoord m → ℝ) :
    realEval (detSqTraceSqPoly K) x =
      (K + hermOfCoord x).det ^ 2 * ((K + hermOfCoord x) * (K + hermOfCoord x)).trace := by
  have hsum : ∀ (S : Finset (Fin m)) (f : Fin m → MvPolynomial (HermCoord m) ℂ),
      realEval (∑ a ∈ S, f a) x = ∑ a ∈ S, realEval (f a) x := fun S f => by
    simp [realEval, map_sum]
  rw [trace_mul_self_eq_sum, ← realEval_detSqPoly, detSqTraceSqPoly, realEval_mul, hsum]
  simp_rw [hsum, realEval_mul, realEval_hermPolyMatrix]

theorem det_sq_mul_trace_inv (A : Matrix (Fin m) (Fin m) ℂ) (hdet : A.det ≠ 0) :
    A.det ^ 2 * (A⁻¹ * A⁻¹).trace = (A.adjugate * A.adjugate).trace := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul, ← mul_assoc]
  field_simp

/-- `U = Σλ⁻²` is integrable under the sector law. -/
theorem integrable_invSqSum (hK : K.IsHermitian)
    (hZ : 0 < (sectorMass m t K ℓ).re) :
    Integrable (fun x => invSqSum (orderedEigs K x)) (sectorLaw m t K ℓ) := by
  have hGm : Measurable fun x => invSqSum (orderedEigs K x) :=
    measurable_invSqSum.comp (measurable_orderedEigs K)
  refine integrable_of_lintegral_lt_top hGm (fun x => invSqSum_nonneg _) ?_
  refine lintegral_sectorLaw_lt_top hK hZ (adjSqPoly K) hGm fun x => ?_
  unfold sectorDetSq cut
  split_ifs with hs
  · by_cases hdet : (K + hermOfCoord x).det = 0
    · simp [hdet]
    · rw [invSqSum_orderedEigs hK hdet, realEval_adjSqPoly, ← det_sq_mul_trace_inv _ hdet]
      have him : ((K + hermOfCoord x).det ^ 2).im = 0 := by
        have h := det_im_eq_zero' (isHermitian_add_hermOfCoord hK x)
        simp [sq, Complex.mul_im, h]
      have : ((K + hermOfCoord x).det ^ 2).re * sectorInvSq K x =
          ((K + hermOfCoord x).det ^ 2 *
            ((K + hermOfCoord x)⁻¹ * (K + hermOfCoord x)⁻¹).trace).re := by
        rw [Complex.mul_re, him, zero_mul, sub_zero]; rfl
      rw [this]
      exact Complex.re_le_norm _
  · simp

/-- `U⁻¹ = (Σλ⁻²)⁻¹` is integrable under the sector law (`U⁻¹ ≤ Tr M²`). -/
theorem integrable_inv_invSqSum (hm : 0 < m) (hK : K.IsHermitian)
    (hZ : 0 < (sectorMass m t K ℓ).re) :
    Integrable (fun x => (invSqSum (orderedEigs K x))⁻¹) (sectorLaw m t K ℓ) := by
  have hGm : Measurable fun x => (invSqSum (orderedEigs K x))⁻¹ :=
    (measurable_invSqSum.comp (measurable_orderedEigs K)).inv
  refine integrable_of_lintegral_lt_top hGm (fun x => inv_nonneg.2 (invSqSum_nonneg _)) ?_
  refine lintegral_sectorLaw_lt_top hK hZ (detSqTraceSqPoly K) hGm fun x => ?_
  unfold sectorDetSq cut
  split_ifs with hs
  · by_cases hdet : (K + hermOfCoord x).det = 0
    · simp [hdet]
    · rw [realEval_detSqTraceSqPoly]
      have him : ((K + hermOfCoord x).det ^ 2).im = 0 := by
        have h := det_im_eq_zero' (isHermitian_add_hermOfCoord hK x)
        simp [sq, Complex.mul_im, h]
      have hre : 0 ≤ ((K + hermOfCoord x).det ^ 2).re := by
        have h := det_im_eq_zero' (isHermitian_add_hermOfCoord hK x)
        rw [sq, Complex.mul_re, h]
        nlinarith [mul_self_nonneg (K + hermOfCoord x).det.re]
      calc ((K + hermOfCoord x).det ^ 2).re * (invSqSum (orderedEigs K x))⁻¹
          ≤ ((K + hermOfCoord x).det ^ 2).re *
              ((K + hermOfCoord x) * (K + hermOfCoord x)).trace.re :=
            mul_le_mul_of_nonneg_left (invSqSum_orderedEigs_inv_le hK hdet ⟨0, hm⟩) hre
        _ = ((K + hermOfCoord x).det ^ 2 *
              ((K + hermOfCoord x) * (K + hermOfCoord x)).trace).re := by
            rw [Complex.mul_re, him, zero_mul, sub_zero]
        _ ≤ _ := Complex.re_le_norm _
  · simp

end BlockBand.DeterminantScore.NegativeSpread
