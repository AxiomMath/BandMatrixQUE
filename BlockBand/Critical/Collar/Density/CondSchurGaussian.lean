module

public import BlockBand.Critical.Collar.Density.CondSchurLebesgue

/-!
# Conditional Schur identity: Gaussian

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

**The deterministic Gaussian conditional identity** `lintegral_gaussian_csTop`: for
`θ ~ N(0, σ)`, `E_θ u*[1_{[a₁,a₂]}(csPencil θ)]₁₁u = ∫_{[a₁,a₂]} y_x* φ_σ(-S(x)) y_x dx`
(`CsGeneric`), obtained from the Cauchy-height identity by Gaussian averaging over the location and
dominated convergence in the height.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_eq_im_inv cauchyKernel_nonneg
  continuous_cauchyKernel measurable_cauchyKernel)
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {D : Matrix m m ℂ} {B : Matrix m n ℂ} {G : Matrix n n ℂ}

/-- The Gaussian average of the Cauchy-height right-hand side at energy `x`. -/
def csGx (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (u : m → ℂ) (σ : ℝ≥0)
    (η x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (gaussianPDFReal 0 σ t) *
    ENNReal.ofReal (quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x)) (csY D B u x))

theorem measurable_uncurry_cauchyShift (η : ℝ) :
    Measurable (Function.uncurry fun (t l : ℝ) => cauchyKernel η (l + t)) :=
  (measurable_cauchyKernel η).comp (measurable_snd.add measurable_fst)

theorem measurable_csGx (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (σ : ℝ≥0)
    (η : ℝ) : Measurable (csGx D B G u σ η) := by
  have hQ := measurable_quadForm_cfc_csS (B := B) hD hG u (measurable_uncurry_cauchyShift η)
  have hF : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal 0 σ p.1) *
      ENNReal.ofReal (quadForm (cfc (fun l => cauchyKernel η (l + p.1)) (csS D B G p.2))
        (csY D B u p.2)) :=
    (ENNReal.measurable_ofReal.comp ((measurable_gaussianPDFReal 0 σ).comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp hQ)
  have h2 := hF.lintegral_prod_left' (μ := (volume : Measure ℝ))
  exact h2

theorem cauchyKernel_neg (η y : ℝ) : cauchyKernel η (-y) = cauchyKernel η y := by
  unfold cauchyKernel; ring_nf

theorem csGx_eq_sum (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ) (σ : ℝ≥0) {η : ℝ}
    (hη : 0 < η) (x : ℝ) :
    csGx D B G u σ η x = ∑ r, ENNReal.ofReal (‖star (increasingEigenvector
      (csS_isHermitian (B := B) hD hG x) r) ⬝ᵥ csY D B u x‖ ^ 2) *
        cauchyConv σ η (-increasingEigenvalue (csS_isHermitian (B := B) hD hG x) r) := by
  have hK := csS_isHermitian (B := B) hD hG x
  unfold csGx
  simp_rw [ofReal_quadForm_cfc_eq_sum hK (fun l => cauchyKernel_nonneg hη.le (l + _)),
    Finset.mul_sum]
  rw [lintegral_finsetSum']
  · refine Finset.sum_congr rfl fun r _ => ?_
    simp_rw [mul_left_comm (ENNReal.ofReal (gaussianPDFReal 0 σ _))]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    unfold cauchyConv
    refine lintegral_congr fun t => ?_
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 2
    rw [← cauchyKernel_neg]; ring_nf
  · intro r _
    exact ((ENNReal.measurable_ofReal.comp (measurable_gaussianPDFReal 0 σ)).mul
      (measurable_const.mul (ENNReal.measurable_ofReal.comp ((measurable_cauchyKernel η).comp
        (measurable_const.add measurable_id))))).aemeasurable

/-- Gaussian average of the Cauchy-height identity over the location `t`. -/
theorem lintegral_csTop_cauchyConv (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (u : m → ℂ) (σ : ℝ≥0) {η : ℝ} (hη : 0 < η) {a₁ a₂ : ℝ}
    (ha : a₁ ≤ a₂) :
    ∫⁻ θ, ENNReal.ofReal (csTop D B G a₁ a₂ u θ) * cauchyConv σ η θ =
      ∫⁻ x in Set.Icc a₁ a₂, csGx D B G u σ η x := by
  have hT := ENNReal.measurable_ofReal.comp (measurable_csTop (B := B) hD hG a₁ a₂ u)
  have hP : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal 0 σ p.2) *
      (ENNReal.ofReal (cauchyKernel η (p.1 - p.2)) *
        ENNReal.ofReal (csTop D B G a₁ a₂ u p.1)) :=
    (ENNReal.measurable_ofReal.comp ((measurable_gaussianPDFReal 0 σ).comp measurable_snd)).mul
      ((ENNReal.measurable_ofReal.comp ((measurable_cauchyKernel η).comp
        (measurable_fst.sub measurable_snd))).mul (hT.comp measurable_fst))
  have hQ := measurable_quadForm_cfc_csS (B := B) hD hG u (measurable_uncurry_cauchyShift η)
  have hR : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal 0 σ p.1) *
      ENNReal.ofReal (quadForm (cfc (fun l => cauchyKernel η (l + p.1)) (csS D B G p.2))
        (csY D B u p.2)) :=
    (ENNReal.measurable_ofReal.comp ((measurable_gaussianPDFReal 0 σ).comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp hQ)
  calc ∫⁻ θ, ENNReal.ofReal (csTop D B G a₁ a₂ u θ) * cauchyConv σ η θ
      = ∫⁻ θ, ∫⁻ t, ENNReal.ofReal (gaussianPDFReal 0 σ t) *
          (ENNReal.ofReal (cauchyKernel η (θ - t)) * ENNReal.ofReal (csTop D B G a₁ a₂ u θ)) := by
        refine lintegral_congr fun θ => ?_
        unfold cauchyConv
        rw [mul_comm, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun t => ?_
        rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), mul_assoc]
    _ = ∫⁻ t, ∫⁻ θ, ENNReal.ofReal (gaussianPDFReal 0 σ t) *
          (ENNReal.ofReal (cauchyKernel η (θ - t)) * ENNReal.ofReal (csTop D B G a₁ a₂ u θ)) :=
        lintegral_lintegral_swap hP.aemeasurable
    _ = ∫⁻ t, ENNReal.ofReal (gaussianPDFReal 0 σ t) * ∫⁻ x in Set.Icc a₁ a₂, ENNReal.ofReal
          (quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x)) (csY D B u x)) := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_cauchyKernel_csTop hD hG hgen u t hη ha]
    _ = ∫⁻ t, ∫⁻ x in Set.Icc a₁ a₂, ENNReal.ofReal (gaussianPDFReal 0 σ t) * ENNReal.ofReal
          (quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x)) (csY D B u x)) := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x in Set.Icc a₁ a₂, csGx D B G u σ η x := by
        unfold csGx
        exact lintegral_lintegral_swap hR.aemeasurable

theorem lintegral_cauchyKernel_one_csTop_le (hD : D.IsHermitian) (hG : G.IsHermitian)
    (a₁ a₂ : ℝ) (u : m → ℂ) :
    ∫⁻ θ, ENNReal.ofReal (cauchyKernel 1 (θ - 0)) * ENNReal.ofReal (csTop D B G a₁ a₂ u θ) ≤
      ENNReal.ofReal (∑ a, ‖u a‖ ^ 2) := by
  calc _ ≤ ∫⁻ θ, ENNReal.ofReal (cauchyKernel 1 (0 - θ)) * ENNReal.ofReal (∑ a, ‖u a‖ ^ 2) := by
        refine lintegral_mono fun θ => ?_
        rw [show θ - 0 = -(0 - θ) by ring, cauchyKernel_neg]
        gcongr
        exact (csTop_nonneg_le (B := B) hD hG a₁ a₂ u θ).2
    _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_cauchyKernel_shift one_pos,
          one_mul]

/-- **The Gaussian conditional identity** (deterministic; `CsGeneric`): for `θ ~ N(0, σ)`,
`E_θ u*[1_{[a₁,a₂]}(csPencil θ)]₁₁u = ∫_{[a₁,a₂]} y_x* φ_σ(-S(x)) y_x dx`. -/
theorem lintegral_gaussian_csTop (hD : D.IsHermitian) (hG : G.IsHermitian)
    (hgen : CsGeneric D B) (u : m → ℂ) {σ : ℝ≥0} (hσ : σ ≠ 0) {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) :
    ∫⁻ θ, ENNReal.ofReal (csTop D B G a₁ a₂ u θ) ∂gaussianReal 0 σ =
      ∫⁻ x in Set.Icc a₁ a₂, ENNReal.ofReal (quadForm
        (cfc (fun l => gaussianPDFReal 0 σ (-l)) (csS D B G x)) (csY D B u x)) := by
  obtain ⟨K, hK0, hK⟩ := cauchyConv_le hσ
  set η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hηdef
  have hη : ∀ k, 0 < η k := fun k => by positivity
  have hη1 : ∀ k, η k ≤ 1 := fun k => by
    rw [hηdef]; exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by positivity)
  have hT : Measurable fun θ => ENNReal.ofReal (csTop D B G a₁ a₂ u θ) :=
    ENNReal.measurable_ofReal.comp (measurable_csTop (B := B) hD hG a₁ a₂ u)
  set U : ℝ := ∑ a, ‖u a‖ ^ 2
  -- the left limit
  have hL : Tendsto (fun k => ∫⁻ θ, ENNReal.ofReal (csTop D B G a₁ a₂ u θ) *
      cauchyConv σ (η k) θ) atTop (𝓝 (∫⁻ θ, ENNReal.ofReal (csTop D B G a₁ a₂ u θ) *
        ENNReal.ofReal (gaussianPDFReal 0 σ θ))) := by
    refine tendsto_lintegral_of_dominated_convergence
      (fun θ => ENNReal.ofReal (csTop D B G a₁ a₂ u θ) * ENNReal.ofReal (K * cauchyKernel 1 θ))
      (fun k => hT.mul (measurable_cauchyConv σ (η k)))
      (fun k => Eventually.of_forall fun θ => by
        show _ * _ ≤ _ * _
        gcongr
        exact hK (η k) (hη k) (hη1 k) θ) ?_
      (Eventually.of_forall fun θ => ENNReal.Tendsto.const_mul (tendsto_cauchyConv σ θ)
        (Or.inr ENNReal.ofReal_ne_top))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (b := ENNReal.ofReal K * ENNReal.ofReal U) ?_
    calc _ = ∫⁻ θ, ENNReal.ofReal K * (ENNReal.ofReal (cauchyKernel 1 (θ - 0)) *
          ENNReal.ofReal (csTop D B G a₁ a₂ u θ)) := by
          refine lintegral_congr fun θ => ?_
          rw [sub_zero, ENNReal.ofReal_mul hK0]; ring
      _ ≤ _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact lintegral_cauchyKernel_one_csTop_le hD hG a₁ a₂ u
  -- the right limit
  have hRb : ∀ k x, csGx D B G u σ (η k) x ≤ ENNReal.ofReal K * ENNReal.ofReal (quadForm
      (cfc (fun l => cauchyKernel 1 (l + 0)) (csS D B G x)) (csY D B u x)) := by
    intro k x
    have hKx := csS_isHermitian (B := B) hD hG x
    rw [csGx_eq_sum hD hG u σ (hη k) x, ofReal_quadForm_cfc_eq_sum hKx
      (fun l => cauchyKernel_nonneg zero_le_one (l + 0)), Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [mul_left_comm, ← ENNReal.ofReal_mul hK0]
    gcongr
    refine (hK (η k) (hη k) (hη1 k) _).trans (le_of_eq ?_)
    rw [add_zero, cauchyKernel_neg]
  have hR : Tendsto (fun k => ∫⁻ x in Set.Icc a₁ a₂, csGx D B G u σ (η k) x) atTop
      (𝓝 (∫⁻ x in Set.Icc a₁ a₂, ENNReal.ofReal (quadForm
        (cfc (fun l => gaussianPDFReal 0 σ (-l)) (csS D B G x)) (csY D B u x)))) := by
    refine tendsto_lintegral_of_dominated_convergence
      (fun x => ENNReal.ofReal K * ENNReal.ofReal (quadForm
        (cfc (fun l => cauchyKernel 1 (l + 0)) (csS D B G x)) (csY D B u x)))
      (fun k => measurable_csGx hD hG u σ (η k))
      (fun k => Eventually.of_forall fun x => hRb k x) ?_ (Eventually.of_forall fun x => ?_)
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_cauchyKernel_csTop hD hG hgen u 0 one_pos ha]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (lintegral_cauchyKernel_one_csTop_le hD hG a₁ a₂ u))
    · have hKx := csS_isHermitian (B := B) hD hG x
      simp_rw [csGx_eq_sum hD hG u σ (hη _) x]
      rw [ofReal_quadForm_cfc_eq_sum hKx (fun l => gaussianPDFReal_nonneg 0 σ (-l))]
      exact tendsto_finsetSum _ fun r _ => ENNReal.Tendsto.const_mul (tendsto_cauchyConv σ _)
        (Or.inr ENNReal.ofReal_ne_top)
  have heq : ∀ k, ∫⁻ θ, ENNReal.ofReal (csTop D B G a₁ a₂ u θ) * cauchyConv σ (η k) θ =
      ∫⁻ x in Set.Icc a₁ a₂, csGx D B G u σ (η k) x := fun k =>
    lintegral_csTop_cauchyConv hD hG hgen u σ (hη k) ha
  have hlim := tendsto_nhds_unique hL (hR.congr fun k => (heq k).symm)
  rw [← hlim, gaussianReal_of_var_ne_zero 0 hσ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 σ) hT]
  refine lintegral_congr fun θ => ?_
  simp only [Pi.mul_apply, gaussianPDF]
  rw [mul_comm]

end BlockBand.Critical.Collar.Density
