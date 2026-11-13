module

public import BlockBand.Critical.Collar.Density.CondSchurKernels

/-!
# Conditional Schur identity: Cauchy

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

The two limits `ε ↓ 0` and the **Cauchy-height identity** `integral_csTop_stdCauchy`: for
`s ~ Cauchy(0,1)`, `E_s u*[1_{[a₁,a₂]}(csPencil(t + ηs))]₁₁u = ∫_{[a₁,a₂]} y_x* P_η(S(x) + t) y_x dx`
under `CsGeneric` (deterministic `D, B, G`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_eq_im_inv cauchyKernel_nonneg
  continuous_cauchyKernel measurable_cauchyKernel)
open scoped ComplexConjugate ComplexOrder

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {D : Matrix m m ℂ} {B : Matrix m n ℂ} {G : Matrix n n ℂ}

theorem stdCauchy_absolutelyContinuous : stdCauchy ≪ (volume : Measure ℝ) := by
  rw [stdCauchy, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 one_ne_zero]
  exact withDensity_absolutelyContinuous _ _

theorem det_sub_eq_zero_of_eigenvalue {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (r : Fin (Fintype.card ι)) :
    (H - ((increasingEigenvalue hH r : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).det = 0 := by
  refine exists_mulVec_eq_zero_iff.1 ⟨increasingEigenvector hH r, fun h0 => ?_, ?_⟩
  · have h1 := sum_norm_sq_increasingEigenvector hH r
    rw [h0] at h1
    simp at h1
  · rw [sub_mulVec, mulVec_increasingEigenvector, smul_mulVec, one_mulVec, sub_self]

/-- Under genericity, a fixed energy `a` is an eigenvalue of `csPencil(t + ηs)` only for
Lebesgue-null (hence Cauchy-null) `s`. -/
theorem ae_stdCauchy_eigenvalue_ne (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (t : ℝ) {η : ℝ} (hη : 0 < η) (a : ℝ) :
    ∀ᵐ s ∂stdCauchy, ∀ r, increasingEigenvalue
      (csPencil_isHermitian (B := B) hD hG (t + η * s)) r ≠ a := by
  set X₀ : Matrix (m ⊕ n) (m ⊕ n) ℂ := csPencil D B G t - (a : ℂ) • 1
  set Y₀ : Matrix (m ⊕ n) (m ⊕ n) ℂ := (η : ℂ) • csPort
  have hp0 : BlockBand.DeterminantScore.detLinePoly X₀ Y₀ ≠ 0 := by
    intro h
    have hv := BlockBand.DeterminantScore.eval_detLinePoly_complex X₀ Y₀ (-Complex.I)
    rw [h, Polynomial.eval_zero] at hv
    have hu := isUnit_det_csPencil_sub hD hG hgen hη t (z := (a : ℂ)) (by simp)
    have heq : X₀ + (-Complex.I) • Y₀ =
        csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) - (a : ℂ) • 1 := by
      rw [sub_eq_add_neg (t : ℂ), csPencil_add]
      simp only [X₀, Y₀, smul_smul, neg_smul, neg_mul, mul_comm Complex.I (η : ℂ)]
      abel
    rw [heq] at hv
    exact hu.ne_zero hv.symm
  have hsub : {s : ℝ | ¬ ∀ r, increasingEigenvalue
      (csPencil_isHermitian (B := B) hD hG (t + η * s)) r ≠ a} ⊆
      Complex.re '' ((BlockBand.DeterminantScore.detLinePoly X₀ Y₀).roots.toFinset : Set ℂ) := by
    intro s hs
    simp only [Set.mem_ofPred_eq, not_forall, not_not] at hs
    obtain ⟨r, hr⟩ := hs
    refine ⟨(s : ℂ), ?_, by simp⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot,
      BlockBand.DeterminantScore.eval_detLinePoly_complex]
    have h := det_sub_eq_zero_of_eigenvalue (csPencil_isHermitian (B := B) hD hG (t + η * s)) r
    rw [hr, csPencil_real_add] at h
    rw [← h]
    congr 1
    simp only [X₀, Y₀]
    abel
  rw [ae_iff]
  exact stdCauchy_absolutelyContinuous (measure_mono_null hsub
    ((Set.Finite.image _ (Finset.finite_toSet _)).measure_zero _))

/-!
## The two limits `ε ↓ 0`
-/

theorem integral_csF_eq_integral_csK (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ)
    (t : ℝ) {η : ℝ} (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) (a₁ a₂ : ℝ) :
    ∫ x in Set.Icc a₁ a₂, csF D B G u t η ε x =
      ∫ s, (∫ x in Set.Icc a₁ a₂, csK D B G u t η ε s x) ∂stdCauchy := by
  have hc0 := continuous_csK (B := B) hD hG u t η hε
  have hc : Continuous fun p : ℝ × ℝ => csK D B G u t η ε p.2 p.1 := by
    have := hc0.comp continuous_swap
    exact this
  have hint : Integrable (fun p : ℝ × ℝ => csK D B G u t η ε p.2 p.1)
      ((volume.restrict (Set.Icc a₁ a₂)).prod stdCauchy) := by
    refine Integrable.of_bound hc.aestronglyMeasurable ((Real.pi * ε)⁻¹ * ∑ a, ‖u a‖ ^ 2)
      (Eventually.of_forall fun p => ?_)
    obtain ⟨h0, h1⟩ := csK_nonneg_le hD hG u t η hε p.2 p.1
    rw [Real.norm_of_nonneg h0]
    exact h1
  have h := integral_integral_swap (f := fun x s => csK D B G u t η ε s x) hint
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact csF_eq_integral hD hG u t hη hε x

theorem tendsto_integral_setIntegral_csK (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (u : m → ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η) {a₁ a₂ : ℝ}
    (ha : a₁ ≤ a₂) :
    Tendsto (fun ε => ∫ s, (∫ x in Set.Icc a₁ a₂, csK D B G u t η ε s x) ∂stdCauchy) (𝓝[>] 0)
      (𝓝 (∫ s, csTop D B G a₁ a₂ u (t + η * s) ∂stdCauchy)) := by
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ)) (μ := stdCauchy)
    (F := fun ε s => ∫ x in Set.Icc a₁ a₂, csK D B G u t η ε s x)
    (fun _ => ∑ a, ‖u a‖ ^ 2) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_csK hD hG u t η hε).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Icc a₁ a₂))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun s => ?_
    rw [setIntegral_csK_eq hD hG u t η hε s a₁ a₂, ← sum_norm_sq_sumElim (n := n),
      ← sum_eigen_weight (csPencil_isHermitian (B := B) hD hG (t + η * s))]
    have hb := fun r => setIntegral_cauchyKernel_Icc_mem hε ha (increasingEigenvalue
      (csPencil_isHermitian (B := B) hD hG (t + η * s)) r)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun r _ => mul_nonneg (hb r).1 (sq_nonneg _))]
    exact Finset.sum_le_sum fun r _ => mul_le_of_le_one_left (sq_nonneg _) (hb r).2
  · filter_upwards [ae_stdCauchy_eigenvalue_ne hD hG hgen t hη a₁,
      ae_stdCauchy_eigenvalue_ne hD hG hgen t hη a₂] with s hs₁ hs₂
    rw [csTop_eq_sum hD hG]
    have heq : (fun ε => ∫ x in Set.Icc a₁ a₂, csK D B G u t η ε s x) =ᶠ[𝓝[>] 0] fun ε =>
        ∑ r, (∫ x in Set.Icc a₁ a₂, cauchyKernel ε (x - increasingEigenvalue
          (csPencil_isHermitian (B := B) hD hG (t + η * s)) r)) *
        ‖star (increasingEigenvector (csPencil_isHermitian (B := B) hD hG (t + η * s)) r) ⬝ᵥ
          Sum.elim u (0 : n → ℂ)‖ ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact setIntegral_csK_eq hD hG u t η hε s a₁ a₂
    refine Tendsto.congr' heq.symm ?_
    exact tendsto_finsetSum _ fun r _ =>
      (tendsto_setIntegral_cauchyKernel_Icc ha (hs₁ r) (hs₂ r)).mul_const _

theorem continuousOn_csF_resolvent (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (t : ℝ) {η : ℝ} (hη : 0 < η) :
    ContinuousOn (fun p : ℝ × ℝ => (csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) -
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ))⁻¹)
      (Set.univ ×ˢ Set.Ici 0) := by
  refine continuousOn_inv_of_isUnit_det (by fun_prop) fun p hp => ?_
  exact isUnit_det_csPencil_sub hD hG hgen hη t (by simpa using hp.2)

theorem tendsto_setIntegral_csF (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (u : m → ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η) (a₁ a₂ : ℝ) :
    Tendsto (fun ε => ∫ x in Set.Icc a₁ a₂, csF D B G u t η ε x) (𝓝[>] 0)
      (𝓝 (∫ x in Set.Icc a₁ a₂, csF D B G u t η 0 x)) := by
  set ψ := Sum.elim u (0 : n → ℂ)
  set Φ : ℝ × ℝ → ℂ := fun p => star ψ ⬝ᵥ ((csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) -
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ))⁻¹ *ᵥ ψ) with hΦ
  have hΦc : ContinuousOn Φ (Set.univ ×ˢ Set.Ici 0) :=
    (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).comp_continuousOn
      (continuousOn_csF_resolvent hD hG hgen t hη)
  have hK : IsCompact (Set.Icc a₁ a₂ ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hΦc.mono fun p hp =>
    ⟨Set.mem_univ _, hp.2.1⟩)
  have hF : ∀ ε x, csF D B G u t η ε x = Real.pi⁻¹ * (Φ (x, ε)).im := fun ε x => rfl
  refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (μ := volume.restrict (Set.Icc a₁ a₂)) (F := fun ε x => csF D B G u t η ε x)
    (fun _ => Real.pi⁻¹ * C) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hc : Continuous fun x : ℝ => Φ (x, ε) := by
      rw [← continuousOn_univ]
      exact hΦc.comp (Continuous.continuousOn (by fun_prop))
        fun x _ => ⟨Set.mem_univ _, Set.mem_Ici.2 (le_of_lt hε)⟩
    exact (continuous_const.mul (Complex.continuous_im.comp hc)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [hF, norm_mul, Real.norm_of_nonneg (inv_nonneg.2 Real.pi_pos.le)]
    refine mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans
      (hC (x, ε) ⟨hx, hε.1.le, hε.2.le⟩)) (inv_nonneg.2 Real.pi_pos.le)
  · refine Eventually.of_forall fun x => ?_
    simp_rw [hF]
    refine (Complex.continuous_im.continuousAt.tendsto.comp ?_).const_mul _
    have hcw : ContinuousWithinAt (fun ε : ℝ => Φ (x, ε)) (Set.Ici 0) 0 := by
      have h : ContinuousOn (fun ε : ℝ => Φ (x, ε)) (Set.Ici 0) :=
        hΦc.comp (Continuous.continuousOn (by fun_prop)) fun ε hε => ⟨Set.mem_univ _, hε⟩
      exact h.continuousWithinAt (Set.mem_Ici.2 le_rfl)
    exact hcw.tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)

/-!
## Identification of the boundary value and the Cauchy-height identity
-/

theorem csF_zero_eq (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (t : ℝ) {η : ℝ}
    (hη : 0 < η) {x : ℝ} (hDx : IsUnit (D - (x : ℂ) • 1).det) :
    csF D B G u t η 0 x =
      quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x)) (csY D B u x) := by
  have hS := csS_isHermitian (B := B) hD hG x
  have hK : (csS D B G x + (t : ℂ) • (1 : Matrix n n ℂ)).IsHermitian :=
    hS.add (isHermitian_one.smul (Complex.conj_ofReal t))
  have hSu : IsUnit (csS D B G x + ((t : ℂ) - (η : ℂ) * Complex.I) • 1).det := by
    have hsplit : csS D B G x + ((t : ℂ) - (η : ℂ) * Complex.I) • 1 =
        (csS D B G x + (t : ℂ) • (1 : Matrix n n ℂ)) - ((η : ℂ) * Complex.I) • 1 := by
      rw [sub_smul]; abel
    rw [hsplit]
    exact isUnit_det_sub_smul_one' hK (by simp [hη])
  have hDi : ((D - (x : ℂ) • (1 : Matrix m m ℂ))⁻¹).IsHermitian :=
    (hD.sub (isHermitian_one.smul (Complex.conj_ofReal x))).inv
  unfold csF
  have hx : ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (x : ℂ) := by simp
  rw [hx, topForm_eq_schur hD u _ x hDx hSu, Complex.add_im,
    Complex.conj_eq_iff_im.mp (hDi.star_dotProduct_mulVec_comm u u), zero_add,
    im_schurForm_eq_cfc hD hG t hη x]

/-- **The Cauchy-height identity** (deterministic; `CsGeneric`). For `s ~ Cauchy(0,1)`, `η > 0`
and `a₁ ≤ a₂`: `E_s u*[1_{[a₁,a₂]}(csPencil(t + ηs))]₁₁u = ∫_{[a₁,a₂]} y_x* P_η(S(x) + t) y_x dx`. -/
theorem integral_csTop_stdCauchy (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (u : m → ℂ) (t : ℝ) {η : ℝ} (hη : 0 < η) {a₁ a₂ : ℝ}
    (ha : a₁ ≤ a₂) :
    ∫ s, csTop D B G a₁ a₂ u (t + η * s) ∂stdCauchy =
      ∫ x in Set.Icc a₁ a₂, quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x))
        (csY D B u x) := by
  have hL := tendsto_integral_setIntegral_csK hD hG hgen u t hη ha
  have hR := tendsto_setIntegral_csF (B := B) hD hG hgen u t hη a₁ a₂
  have heq : (fun ε => ∫ x in Set.Icc a₁ a₂, csF D B G u t η ε x) =ᶠ[𝓝[>] 0]
      fun ε => ∫ s, (∫ x in Set.Icc a₁ a₂, csK D B G u t η ε s x) ∂stdCauchy := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_csF_eq_integral_csK hD hG u t hη hε a₁ a₂
  rw [tendsto_nhds_unique hL (hR.congr' heq)]
  refine setIntegral_congr_ae measurableSet_Icc ?_
  have hfin := finite_setOf_det_sub_eq_zero D
  have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ {x : ℝ | (D - (x : ℂ) • (1 : Matrix m m ℂ)).det = 0} := by
    rw [ae_iff]; simpa using hfin.measure_zero volume
  filter_upwards [hnull] with x hx _
  have hDx : IsUnit (D - (x : ℂ) • 1).det := isUnit_iff_ne_zero.2 hx
  exact csF_zero_eq hD hG u t hη hDx

end BlockBand.Critical.Collar.Density
