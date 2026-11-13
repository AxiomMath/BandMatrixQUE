module

public import BlockBand.Critical.WeightedDensity.Density
public import BlockBand.Critical.WeightedDensity.RankOne
public import BlockBand.Critical.WeightedDensity.Poisson
public import BlockBand.Palm.MomentFlow.BridgeLaw

/-!
# The global weighted density bound `(F-e+iη) Σ_F(e) (F-e-iη) ⪯ C_{c,η} √N`

The general part of the global weighted-density lemma.

*Law.* `G ~ GUE_N(c/N)` (`freshGUE`), its split `G = G₁ + G₂` into independent
`GUE_N(c/(2N))` halves (`gueMeasure_conv`), and the scalar split of the weighted density.
*Domain.* every `N ≥ 1`, every Hermitian `F` (no norm bound), every real `e`, every real `η`
(the bound holds for all `η`, not only `η > 0`), every `c > 0`.
*Norms.* Loewner order `A ⪯ B ⇔ (B - A).PosSemidef` (`ComplexOrder`); `‖q‖² = Σ_a |q_a|²`.
*Quantifiers.* `c`, `η` first; then the explicit constant
`C_{c,η} = π⁻¹(4c√(π/c) + 2η²√(π/(2c)))`; then all `N`, `F`, every continuous matrix spectral
density `S` of `F + G` and every `e`.

## Proof, in resolvent form, in three steps

1. (`lintegral_cauchyKernel_weightedForm`) For `ε > 0`, the scalar split, the eigenvector identity
   `u_ℓ*(F - λ_ℓ - iη) q = -u_ℓ*(G + iη) q` (at an eigenvalue, multiplication by `F - λ + iη`
   equals multiplication by `-G + iη`) and the spectral expansion of `R = (F + G - x - iε)⁻¹`
   give `∫ P_ε(x-e) q*(F-e+iη)Σ_F(e)(F-e-iη)q de = π⁻¹ E Im⟨(G+iη)q, R (G+iη)q⟩`.
2. (`lintegral_resolventForm_shiftedVec_le`) Positivity of `Im R` (`Im⟨v,Rv⟩ = ε‖Rv‖²`) bounds
   the form by the vectors `G₁q`, `G₂q`, `iηq`; conditional rank-one spectral averaging over the
   other half (`lintegral_im_resolvent_gue_le`, density of the diagonal entry `≤ (2πτ)^{-1/2}`)
   and `E‖G₁q‖² = (c/2)‖q‖²` (`lintegral_norm_sq_mulVec_gue`) give `≤ C_{c,η}√N ‖q‖²`.
3. (`le_of_forall_lintegral_cauchyKernel_le`) The weighted form is continuous in `e`; letting
   `ε ↓ 0` gives the pointwise bound for the canonical version, hence for every continuous
   version (`eq_sigma_of_isMatrixSpectralDensity`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.WeightedDensity

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.FreshPalm BlockBand.Coarea.GUELaw
  BlockBand.Critical.PointDensity
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

variable {N : ℕ}

/-!
## Loewner-order helpers
-/

theorem quadForm_conjTranspose_mul_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ ℂ) (S : Matrix ι ι ℂ) (q : κ → ℂ) :
    quadForm (Bᴴ * S * B) q = quadForm S (B *ᵥ q) := by
  unfold quadForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

theorem posSemidef_of_quadForm_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (h : ∀ x, 0 ≤ quadForm M x) : M.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => by
    rw [Complex.nonneg_iff]
    exact ⟨h x, (BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian hM x).symm⟩

theorem quadForm_nonneg_of_posSemidef {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ}
    (hM : M.PosSemidef) (x : ι → ℂ) : 0 ≤ quadForm M x :=
  (Complex.nonneg_iff.1 (hM.dotProduct_mulVec_nonneg x)).1

theorem quadForm_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadForm (A - B) x = quadForm A x - quadForm B x := by
  simp [quadForm, sub_mulVec, dotProduct_sub]

theorem quadForm_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadForm (A + B) x = quadForm A x + quadForm B x := by
  simp [quadForm, add_mulVec, dotProduct_add]

theorem quadForm_real_smul {ι : Type*} [Fintype ι] (r : ℝ) (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadForm ((r : ℂ) • A) x = r * quadForm A x := by
  simp [quadForm, smul_mulVec, dotProduct_smul]

theorem quadForm_one {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → ℂ) :
    quadForm (1 : Matrix ι ι ℂ) x = ∑ a, ‖x a‖ ^ 2 := by
  rw [quadForm, one_mulVec, BlockBand.Wegner.re_star_dotProduct_self]

theorem conjTranspose_sub_shift {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (e η : ℝ) :
    (F - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ =
      F - ((e : ℂ) - (η : ℂ) * Complex.I) • 1 := by
  rw [conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one]
  congr 2
  simp [Complex.ext_iff]

theorem quadForm_sigma_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) (y : Fin N → ℂ) :
    0 ≤ quadForm (sigma F c e) y := by
  rw [quadForm, star_dotProduct_sigma_mulVec, Complex.re_sum]
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun ℓ _ => integral_nonneg fun A0 =>
    mul_nonneg (palmWeight_nonneg F c e ℓ A0) (sq_nonneg _)

/-!
## Resolvent forms
-/

/-- `(G + iη) q`. -/
def shiftedVec (G : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (q : Fin N → ℂ) : Fin N → ℂ :=
  G *ᵥ q + ((η : ℂ) * Complex.I) • q

/-- `Im ⟨v, (F + G - z)⁻¹ v⟩`. -/
def resolventForm (F G : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (v : Fin N → ℂ) : ℝ :=
  (star v ⬝ᵥ ((F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ v)).im

theorem measurable_resolventForm (F : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    Measurable fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) => resolventForm F p.1 z p.2 := by
  have hinv : Measurable fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      (F + p.1 - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ :=
    BlockBand.Wegner.measurable_matrix_inv.comp
      ((continuous_const.add continuous_fst).sub continuous_const).measurable
  have hcont : Continuous fun r : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      (star r.2 ⬝ᵥ (r.1 *ᵥ r.2)).im :=
    Complex.continuous_im.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd))
  exact hcont.measurable.comp (hinv.prodMk measurable_snd)

theorem resolventForm_nonneg {F G : Matrix (Fin N) (Fin N) ℂ} (hH : (F + G).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (v : Fin N → ℂ) : 0 ≤ resolventForm F G z v :=
  im_dotProduct_inv_mulVec_nonneg hH hz v

theorem resolventForm_add_le {F G : Matrix (Fin N) (Fin N) ℂ} (hH : (F + G).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (a b : Fin N → ℂ) :
    resolventForm F G z (a + b) ≤ 2 * resolventForm F G z a + 2 * resolventForm F G z b := by
  unfold resolventForm
  rw [im_dotProduct_inv_mulVec hH hz, im_dotProduct_inv_mulVec hH hz,
    im_dotProduct_inv_mulVec hH hz, BlockBand.Wegner.re_star_dotProduct_self,
    BlockBand.Wegner.re_star_dotProduct_self, BlockBand.Wegner.re_star_dotProduct_self,
    mulVec_add]
  set R : Matrix (Fin N) (Fin N) ℂ := (F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
  have h : ∀ i, ‖(R *ᵥ a + R *ᵥ b) i‖ ^ 2 ≤ 2 * ‖(R *ᵥ a) i‖ ^ 2 + 2 * ‖(R *ᵥ b) i‖ ^ 2 := by
    intro i
    rw [Pi.add_apply]
    have h1 := norm_add_le ((R *ᵥ a) i) ((R *ᵥ b) i)
    have h2 := norm_nonneg ((R *ᵥ a) i + (R *ᵥ b) i)
    nlinarith [sq_nonneg (‖(R *ᵥ a) i‖ - ‖(R *ᵥ b) i‖), norm_nonneg ((R *ᵥ a) i),
      norm_nonneg ((R *ᵥ b) i)]
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  nlinarith [hz]

theorem resolventForm_smul (F G : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (η : ℝ) (v : Fin N → ℂ) :
    resolventForm F G z (((η : ℂ) * Complex.I) • v) = η ^ 2 * resolventForm F G z v := by
  unfold resolventForm
  rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc]
  have : star ((η : ℂ) * Complex.I) * ((η : ℂ) * Complex.I) = ((η ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two]
  rw [this, Complex.im_ofReal_mul]

/-!
## Step 1: the Cauchy-smoothed weighted form is a resolvent form
-/

/-- At an eigenvalue, multiplication by `F - λ + iη` is multiplication by `-(G - iη)`:
`(F - λ_ℓ - iη) q` and `(G + iη) q` have opposite overlaps with `u_ℓ`. -/
theorem star_shift_dotProduct_eigenvector {F G : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hG : G.IsHermitian) (hS : SimpleSpectrum (F + G)) (η : ℝ) (q : Fin N → ℂ) (ℓ : Fin N) :
    star ((F - (((freshEigenvalue (F + G) ℓ : ℝ) : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q) ⬝ᵥ
        freshEigenvector (F + G) ℓ =
      -(star (shiftedVec G η q) ⬝ᵥ freshEigenvector (F + G) ℓ) := by
  set u := freshEigenvector (F + G) ℓ
  set lam := freshEigenvalue (F + G) ℓ
  have hu : F *ᵥ u + G *ᵥ u = (lam : ℂ) • u := by
    rw [← add_mulVec]; exact hS.mulVec_freshEigenvector ℓ
  have hrel : star q ⬝ᵥ (F *ᵥ u) + star q ⬝ᵥ (G *ᵥ u) = (lam : ℂ) * (star q ⬝ᵥ u) := by
    rw [← dotProduct_add, hu, dotProduct_smul, smul_eq_mul]
  have e1 : star ((F - ((lam : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q) ⬝ᵥ u =
      star q ⬝ᵥ (F *ᵥ u) - star ((lam : ℂ) + (η : ℂ) * Complex.I) * (star q ⬝ᵥ u) := by
    rw [star_mulVec, ← dotProduct_mulVec, conjTranspose_sub, hF.eq, conjTranspose_smul,
      conjTranspose_one, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
  have e2 : star (shiftedVec G η q) ⬝ᵥ u =
      star q ⬝ᵥ (G *ᵥ u) + star ((η : ℂ) * Complex.I) * (star q ⬝ᵥ u) := by
    rw [shiftedVec, star_add, add_dotProduct, star_mulVec, ← dotProduct_mulVec, hG.eq, star_smul,
      smul_dotProduct, smul_eq_mul]
  rw [e1, e2]
  have hs1 : star ((lam : ℂ) + (η : ℂ) * Complex.I) = (lam : ℂ) - (η : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hs2 : star ((η : ℂ) * Complex.I) = -((η : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  rw [hs1, hs2]
  linear_combination hrel

/-- Deterministic spectral form of the smoothed weighted density, on simple spectrum:
`Σ_ℓ P_ε(x-λ_ℓ) |((F - λ_ℓ - iη)q)* u_ℓ|² = π⁻¹ Im⟨(G+iη)q, (F+G-x-iε)⁻¹ (G+iη)q⟩`. -/
theorem sum_cauchyKernel_eq_resolventForm {F G : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hG : G.IsHermitian) (hS : SimpleSpectrum (F + G)) {ε : ℝ} (hε : 0 < ε) (x η : ℝ)
    (q : Fin N → ℂ) :
    ∑ ℓ : Fin N, cauchyKernel ε (x - freshEigenvalue (F + G) ℓ) *
        ‖star ((F - (((freshEigenvalue (F + G) ℓ : ℝ) : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q) ⬝ᵥ
          freshEigenvector (F + G) ℓ‖ ^ 2 =
      Real.pi⁻¹ * resolventForm F G ⟨x, ε⟩ (shiftedVec G η q) := by
  have hz : (⟨x, ε⟩ : ℂ).im ≠ 0 := hε.ne'
  unfold resolventForm
  rw [hS.inv_eq_sum hz, Matrix.sum_mulVec, dotProduct_sum, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [star_shift_dotProduct_eigenvector hF hG hS η q ℓ, norm_neg, smul_mulVec, dotProduct_smul,
    smul_eq_mul, star_dotProduct_freshProjector_mulVec, Complex.im_mul_ofReal,
    cauchyKernel_eq_im_inv hε]
  ring

/-- `ρ_q(e) = q*(F-e+iη)Σ_F(e)(F-e-iη)q = ((F-e-iη)q)* Σ_F(e) ((F-e-iη)q)`. -/
def weightedForm (F : Matrix (Fin N) (Fin N) ℂ) (c η : ℝ) (q : Fin N → ℂ) (e : ℝ) : ℝ :=
  quadForm (sigma F c e) ((F - ((e : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q)

theorem continuous_shiftVec (F : Matrix (Fin N) (Fin N) ℂ) (η : ℝ) (q : Fin N → ℂ) :
    Continuous fun e : ℝ => (F - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix (Fin N) (Fin N) ℂ))
      *ᵥ q :=
  (continuous_const.sub (((Complex.continuous_ofReal.add continuous_const).smul
    continuous_const))).matrix_mulVec continuous_const

theorem continuous_weightedForm (F : Matrix (Fin N) (Fin N) ℂ) (c η : ℝ) (q : Fin N → ℂ) :
    Continuous (weightedForm F c η q) :=
  Complex.continuous_re.comp ((continuous_star.comp (continuous_shiftVec F η q)).dotProduct
    ((continuous_sigma F c).matrix_mulVec (continuous_shiftVec F η q)))

/-- **Step 1.** For `ε > 0`: `∫ P_ε(x-e) ρ_q(e) de = E_G π⁻¹ Im⟨(G+iη)q, (F+G-x-iε)⁻¹(G+iη)q⟩`. -/
theorem lintegral_cauchyKernel_weightedForm (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) (x η : ℝ) (q : Fin N → ℂ) :
    ∫⁻ e, ENNReal.ofReal (cauchyKernel ε (x - e) * weightedForm F c η q e) =
      ∫⁻ G, ENNReal.ofReal (Real.pi⁻¹ * resolventForm F G ⟨x, ε⟩ (shiftedVec G η q))
        ∂freshGUE N c := by
  set Ψ : ℝ × (Fin N → ℂ) → ℝ≥0∞ := fun p => ENNReal.ofReal (cauchyKernel ε (x - p.1)) *
    ENNReal.ofReal (‖star ((F - ((p.1 : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q) ⬝ᵥ p.2‖ ^ 2)
    with hΨdef
  have hΨ : Measurable Ψ := by
    refine (ENNReal.continuous_ofReal.comp ((continuous_cauchyKernel hε).comp
      (continuous_const.sub continuous_fst))).measurable.mul ?_
    refine (ENNReal.continuous_ofReal.comp (((continuous_star.comp
      ((continuous_shiftVec F η q).comp continuous_fst)).dotProduct continuous_snd).norm.pow 2)).measurable
  have hL : ∀ e, ENNReal.ofReal (cauchyKernel ε (x - e) * weightedForm F c η q e) =
      ∑ ℓ : Fin N, ∫⁻ A0, ENNReal.ofReal (palmWeight F c e ℓ A0) *
        Ψ (e, freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c := by
    intro e
    rw [ENNReal.ofReal_mul (cauchyKernel_nonneg hε.le _), weightedForm, ofReal_quadForm_sigma,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun A0 => ?_
    rw [hΨdef, ENNReal.ofReal_mul (palmWeight_nonneg F c e ℓ A0)]
    ring
  simp_rw [hL]
  rw [lintegral_sigmaKernel_eq hN hF hc hΨ]
  refine lintegral_congr_ae ?_
  have ht : 0 < Real.toNNReal (c / N) := Real.toNNReal_pos.2 (div_pos hc (by exact_mod_cast hN))
  filter_upwards [ae_simpleSpectrum_add_gue hF ht, ae_isHermitian_gueMeasure
    (ι := Fin N) (Real.toNNReal (c / N))] with G hS hG
  rw [← sum_cauchyKernel_eq_resolventForm hF hG hS hε x η q,
    ENNReal.ofReal_sum_of_nonneg fun ℓ _ => mul_nonneg (cauchyKernel_nonneg hε.le _) (sq_nonneg _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [hΨdef, ENNReal.ofReal_mul (cauchyKernel_nonneg hε.le _)]

/-!
## Step 2: the Gaussian bound `C_{c,η} √N`
-/

/-- The explicit constant `C_{c,η} = π⁻¹ (4 c √(π/c) + 2 η² √(π/(2c)))`. -/
def globalConst (c η : ℝ) : ℝ :=
  Real.pi⁻¹ * (4 * c * Real.sqrt (Real.pi / c) + 2 * η ^ 2 * Real.sqrt (Real.pi / (2 * c)))

theorem globalConst_nonneg {c : ℝ} (hc : 0 ≤ c) (η : ℝ) : 0 ≤ globalConst c η := by
  unfold globalConst
  have := Real.pi_pos
  positivity

theorem measurable_resolventForm_comp (F : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) {α : Type*}
    [MeasurableSpace α] {g : α → Matrix (Fin N) (Fin N) ℂ} {v : α → Fin N → ℂ}
    (hg : Measurable g) (hv : Measurable v) :
    Measurable fun a => ENNReal.ofReal (resolventForm F (g a) z (v a)) :=
  ENNReal.measurable_ofReal.comp ((measurable_resolventForm F z).comp (hg.prodMk hv))

theorem measurable_mulVec_const (q : Fin N → ℂ) :
    Measurable fun G : Matrix (Fin N) (Fin N) ℂ => G *ᵥ q :=
  (continuous_id.matrix_mulVec continuous_const).measurable

/-- `E_G Im⟨Gq, (F+G-z)⁻¹ Gq⟩ ≤ 4 √(π/(2τ)) N τ ‖q‖²`, `G ~ GUE(2τ)`, through the split
`G = G₁ + G₂` and conditional rank-one averaging over each half. -/
theorem lintegral_resolventForm_mulVec_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {τ : ℝ≥0} (hτ : 0 < τ) {z : ℂ} (hz : 0 < z.im) (q : Fin N → ℂ) :
    ∫⁻ G, ENNReal.ofReal (resolventForm F G z (G *ᵥ q)) ∂gueMeasure (Fin N) (τ + τ) ≤
      ENNReal.ofReal (4 * (Real.sqrt (Real.pi / (2 * τ)) * (N * τ * ∑ a, ‖q a‖ ^ 2))) := by
  set μ := gueMeasure (Fin N) τ
  set K := Real.sqrt (Real.pi / (2 * τ))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hmadd : Measurable fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      p.1 + p.2 := BlockBand.Coarea.FixedOmega.measurable_matrix_add measurable_fst measurable_snd
  rw [← BlockBand.Palm.MomentFlow.gueMeasure_conv τ τ,
    lintegral_map (f := fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (resolventForm F G z (G *ᵥ q)))
      (measurable_resolventForm_comp F z measurable_id (measurable_mulVec_const q)) hmadd]
  -- pointwise splitting
  have hsplit : ∀ᵐ p ∂μ.prod μ, ENNReal.ofReal (resolventForm F (p.1 + p.2) z ((p.1 + p.2) *ᵥ q)) ≤
      2 * ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.1 *ᵥ q)) +
        2 * ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.2 *ᵥ q)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae
        (ae_isHermitian_gueMeasure (ι := Fin N) τ),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae
        (ae_isHermitian_gueMeasure (ι := Fin N) τ)] with p h1 h2
    have hH : (F + (p.1 + p.2)).IsHermitian := hF.add (h1.add h2)
    rw [add_mulVec]
    calc ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.1 *ᵥ q + p.2 *ᵥ q))
        ≤ ENNReal.ofReal (2 * resolventForm F (p.1 + p.2) z (p.1 *ᵥ q) +
            2 * resolventForm F (p.1 + p.2) z (p.2 *ᵥ q)) :=
          ENNReal.ofReal_le_ofReal (resolventForm_add_le hH hz _ _)
      _ = _ := by
        rw [ENNReal.ofReal_add (by have := resolventForm_nonneg hH hz (p.1 *ᵥ q); positivity)
          (by have := resolventForm_nonneg hH hz (p.2 *ᵥ q); positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hm1 : Measurable fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.1 *ᵥ q)) :=
    measurable_resolventForm_comp F z hmadd ((measurable_mulVec_const q).comp measurable_fst)
  have hm2 : Measurable fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.2 *ᵥ q)) :=
    measurable_resolventForm_comp F z hmadd ((measurable_mulVec_const q).comp measurable_snd)
  -- each half
  have hhalf : ∫⁻ G1, ENNReal.ofReal (K * ∑ a, ‖(G1 *ᵥ q) a‖ ^ 2) ∂μ =
      ENNReal.ofReal (K * (N * τ * ∑ a, ‖q a‖ ^ 2)) := by
    simp_rw [ENNReal.ofReal_mul hK]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_norm_sq_mulVec_gue]
  have hT1 : ∫⁻ p, ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.1 *ᵥ q)) ∂μ.prod μ ≤
      ENNReal.ofReal (K * (N * τ * ∑ a, ‖q a‖ ^ 2)) := by
    rw [lintegral_prod _ hm1.aemeasurable, ← hhalf]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_isHermitian_gueMeasure (ι := Fin N) τ] with G1 hG1
    have h := lintegral_im_resolvent_gue_le (hF.add hG1) hτ hz (G1 *ᵥ q)
    refine le_of_eq_of_le ?_ h
    refine lintegral_congr fun G2 => ?_
    simp only [resolventForm, add_assoc]
  have hT2 : ∫⁻ p, ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.2 *ᵥ q)) ∂μ.prod μ ≤
      ENNReal.ofReal (K * (N * τ * ∑ a, ‖q a‖ ^ 2)) := by
    rw [lintegral_prod_symm _ hm2.aemeasurable, ← hhalf]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_isHermitian_gueMeasure (ι := Fin N) τ] with G2 hG2
    have h := lintegral_im_resolvent_gue_le (hF.add hG2) hτ hz (G2 *ᵥ q)
    refine le_of_eq_of_le ?_ h
    refine lintegral_congr fun G1 => ?_
    simp only [resolventForm]
    rw [add_comm G1 G2, ← add_assoc]
  calc ∫⁻ p, ENNReal.ofReal (resolventForm F (p.1 + p.2) z ((p.1 + p.2) *ᵥ q)) ∂μ.prod μ
      ≤ ∫⁻ p, (2 * ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.1 *ᵥ q)) +
          2 * ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.2 *ᵥ q))) ∂μ.prod μ :=
        lintegral_mono_ae hsplit
    _ = 2 * ∫⁻ p, ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.1 *ᵥ q)) ∂μ.prod μ +
          2 * ∫⁻ p, ENNReal.ofReal (resolventForm F (p.1 + p.2) z (p.2 *ᵥ q)) ∂μ.prod μ := by
        rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul _ hm1,
          lintegral_const_mul _ hm2]
    _ ≤ 2 * ENNReal.ofReal (K * (N * τ * ∑ a, ‖q a‖ ^ 2)) +
          2 * ENNReal.ofReal (K * (N * τ * ∑ a, ‖q a‖ ^ 2)) := by gcongr
    _ = ENNReal.ofReal (4 * (K * (N * τ * ∑ a, ‖q a‖ ^ 2))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
        ring

/-- **Step 2.** `E_G π⁻¹ Im⟨(G+iη)q, (F+G-z)⁻¹(G+iη)q⟩ ≤ C_{c,η} √N ‖q‖²`, `G ~ GUE_N(c/N)`. -/
theorem lintegral_resolventForm_shiftedVec_le (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.im) (η : ℝ) (q : Fin N → ℂ) :
    ∫⁻ G, ENNReal.ofReal (Real.pi⁻¹ * resolventForm F G z (shiftedVec G η q)) ∂freshGUE N c ≤
      ENNReal.ofReal (globalConst c η * Real.sqrt N * ∑ a, ‖q a‖ ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set nq := ∑ a, ‖q a‖ ^ 2
  have hnq : 0 ≤ nq := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set τ : ℝ≥0 := Real.toNNReal (c / (2 * N))
  have hτr : (τ : ℝ) = c / (2 * N) := Real.coe_toNNReal _ (by positivity)
  have hτ : 0 < τ := Real.toNNReal_pos.2 (by positivity)
  have htt : Real.toNNReal (c / N) = τ + τ := by
    rw [← Real.toNNReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have htr : ((Real.toNNReal (c / N) : ℝ≥0) : ℝ) = c / N := Real.coe_toNNReal _ (by positivity)
  have hpi : 0 < Real.pi⁻¹ := inv_pos.2 Real.pi_pos
  set K1 := Real.sqrt (Real.pi / (2 * τ))
  set K2 := Real.sqrt (Real.pi / (2 * ((Real.toNNReal (c / N) : ℝ≥0) : ℝ)))
  -- pointwise
  have hpt : ∀ᵐ G ∂freshGUE N c,
      ENNReal.ofReal (Real.pi⁻¹ * resolventForm F G z (shiftedVec G η q)) ≤
        ENNReal.ofReal (2 * Real.pi⁻¹) * ENNReal.ofReal (resolventForm F G z (G *ᵥ q)) +
          ENNReal.ofReal (2 * Real.pi⁻¹ * η ^ 2) * ENNReal.ofReal (resolventForm F G z q) := by
    filter_upwards [ae_isHermitian_gueMeasure (ι := Fin N) (Real.toNNReal (c / N))] with G hG
    have hH : (F + G).IsHermitian := hF.add hG
    have h1 := resolventForm_add_le hH hz (G *ᵥ q) (((η : ℂ) * Complex.I) • q)
    rw [resolventForm_smul] at h1
    have n1 := resolventForm_nonneg hH hz (G *ᵥ q)
    have n2 := resolventForm_nonneg hH hz q
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold shiftedVec
    nlinarith
  have hmA : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (resolventForm F G z (G *ᵥ q)) :=
    measurable_resolventForm_comp F z measurable_id (measurable_mulVec_const q)
  have hA := lintegral_resolventForm_mulVec_le hF hτ hz q
  rw [← htt] at hA
  have hB := lintegral_im_resolvent_gue_le hF
    (Real.toNNReal_pos.2 (div_pos hc hNr)) hz q
  calc ∫⁻ G, ENNReal.ofReal (Real.pi⁻¹ * resolventForm F G z (shiftedVec G η q)) ∂freshGUE N c
      ≤ ∫⁻ G, (ENNReal.ofReal (2 * Real.pi⁻¹) * ENNReal.ofReal (resolventForm F G z (G *ᵥ q)) +
          ENNReal.ofReal (2 * Real.pi⁻¹ * η ^ 2) * ENNReal.ofReal (resolventForm F G z q))
          ∂freshGUE N c := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * Real.pi⁻¹) *
          ∫⁻ G, ENNReal.ofReal (resolventForm F G z (G *ᵥ q)) ∂freshGUE N c +
        ENNReal.ofReal (2 * Real.pi⁻¹ * η ^ 2) *
          ∫⁻ G, ENNReal.ofReal (resolventForm F G z q) ∂freshGUE N c := by
        rw [lintegral_add_left (hmA.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 * Real.pi⁻¹) * ENNReal.ofReal (4 * (K1 * (N * τ * nq))) +
        ENNReal.ofReal (2 * Real.pi⁻¹ * η ^ 2) * ENNReal.ofReal (K2 * nq) := by
        gcongr
        exact hB
    _ = ENNReal.ofReal (2 * Real.pi⁻¹ * (4 * (K1 * (N * τ * nq))) +
          2 * Real.pi⁻¹ * η ^ 2 * (K2 * nq)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal (globalConst c η * Real.sqrt N * nq) := by
        congr 1
        have h1 : K1 = Real.sqrt (Real.pi / c) * Real.sqrt N := by
          show Real.sqrt (Real.pi / (2 * τ)) = _
          rw [← Real.sqrt_mul (div_nonneg Real.pi_pos.le hc.le)]
          congr 1
          rw [hτr]
          field_simp
        have h2 : K2 = Real.sqrt (Real.pi / (2 * c)) * Real.sqrt N := by
          show Real.sqrt (Real.pi / (2 * ((Real.toNNReal (c / N) : ℝ≥0) : ℝ))) = _
          rw [← Real.sqrt_mul (div_nonneg Real.pi_pos.le (by positivity))]
          congr 1
          rw [htr]
          field_simp
        rw [h1, h2, hτr, globalConst]
        field_simp

/-!
## Step 3: the pointwise bound and the Loewner statement
-/

/-- Pointwise bound for the canonical version, every `e`, every `q`:
`q*(F-e+iη)Σ_F(e)(F-e-iη)q ≤ C_{c,η} √N ‖q‖²`. -/
theorem weightedForm_le (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {c : ℝ} (hc : 0 < c) (η : ℝ) (q : Fin N → ℂ) (x : ℝ) :
    weightedForm F c η q x ≤ globalConst c η * Real.sqrt N * ∑ a, ‖q a‖ ^ 2 := by
  refine le_of_forall_lintegral_cauchyKernel_le (continuous_weightedForm F c η q)
    (by
      have := globalConst_nonneg hc.le η
      have : 0 ≤ ∑ a, ‖q a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity) fun ε hε => ?_
  rw [lintegral_cauchyKernel_weightedForm hN hF hc hε x η q]
  exact lintegral_resolventForm_shiftedVec_le hN hF hc (z := ⟨x, ε⟩) hε η q

/-- Loewner form of a pointwise quadratic-form bound `q*(Bᴴ S B)q ≤ K ‖q‖²`. -/
theorem posSemidef_smul_one_sub_of_le {S : Matrix (Fin N) (Fin N) ℂ} (hS : S.IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℂ) {K : ℝ}
    (h : ∀ q : Fin N → ℂ, quadForm S (B *ᵥ q) ≤ K * ∑ a, ‖q a‖ ^ 2) :
    (((K : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Bᴴ * S * B).PosSemidef := by
  refine posSemidef_of_quadForm_nonneg
    (((isHermitian_one).smul (Complex.conj_ofReal K)).sub (isHermitian_conjTranspose_mul_mul B hS))
    fun q => ?_
  rw [quadForm_sub, quadForm_real_smul, quadForm_one, quadForm_conjTranspose_mul_mul]
  linarith [h q]

/-- **The global weighted density bound, first assertion.** Law `G ~ GUE_N(c/N)`. For fixed
`c > 0` and `η` there is `C = C_{c,η}` (explicitly `globalConst c η`) such that for every `N ≥ 1`
and every Hermitian `F` (no norm bound): the expected matrix spectral density of `F + G` has a
continuous version, and every continuous version `Σ_F` satisfies, for every real `e`,
`(F - e + iη) Σ_F(e) (F - e - iη) ⪯ C √N I`. -/
theorem globalWeightedDensity_general {c : ℝ} (hc : 0 < c) (η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ F : Matrix (Fin N) (Fin N) ℂ, F.IsHermitian →
      (∃ S : ℝ → Matrix (Fin N) (Fin N) ℂ, Continuous S ∧ IsMatrixSpectralDensity N c F S) ∧
      ∀ S : ℝ → Matrix (Fin N) (Fin N) ℂ, Continuous S → IsMatrixSpectralDensity N c F S →
        ∀ e : ℝ, (((C * Real.sqrt N : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
          (F - ((e : ℂ) - (η : ℂ) * Complex.I) • 1) * S e *
            (F - ((e : ℂ) + (η : ℂ) * Complex.I) • 1)).PosSemidef := by
  refine ⟨globalConst c η, globalConst_nonneg hc.le η, fun N hN F hF => ⟨⟨sigma F c,
    continuous_sigma F c, isMatrixSpectralDensity_sigma hN hF hc⟩, fun S hS hSd e => ?_⟩⟩
  rw [eq_sigma_of_isMatrixSpectralDensity hN hF hc hS hSd, ← conjTranspose_sub_shift hF e η]
  exact posSemidef_smul_one_sub_of_le (sigma_isHermitian F c e) _ fun q => by
    have h := weightedForm_le hN hF hc η q e
    rw [weightedForm] at h
    linarith

end BlockBand.Critical.WeightedDensity
