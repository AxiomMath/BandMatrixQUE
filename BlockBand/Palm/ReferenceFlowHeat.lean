module

public import BlockBand.Palm.ReferenceFlowSpec
public import BlockBand.Internal.Contracts.Inputs

/-!
# Gaussian heat identities for the reference flow

Symmetry of second derivatives, the contraction identity for Gaussian pairings, the circular
Gaussian matrix as an image of real coordinates, and the Stein identity for it.

* `D2_symm`: the second derivative of a `C²` function is symmetric.
* `gaussPair`, `gaussPair_of_anticomm` (**contraction identity**): for a symmetric real
  bilinear form `Q`, Hermitian `S, B` and `SB + BS = WWᴴ`, `gaussPair Q B S = ½ gaussPair Q W W`.
  Proof: `gaussPair Q P R = pairForm Q (R Pᴴ)` for a real-linear functional `pairForm Q` on
  matrices with `pairForm Q Mᴴ = pairForm Q M`.
* `integral_fderiv_lmul` (**Stein identity**): for bounded `C²` `f`, any `m`, `S`, `B`,
  `E Df(m + SG)[BG] = ½ Σ_{j,α} E (D²f(m + SG)[B e_{jα}, S e_{jα}] +
  D²f(m + SG)[i B e_{jα}, i S e_{jα}])` under `matCircularLaw N p`, from
  `MultivariateGaussianIBP` with variance `1/2` in each of the `2Np` real coordinates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ComplexConjugate

variable {N p : ℕ}

/-!
## Symmetry of the second derivative
-/

/-- `D²f(y)[u,v] = D²f(y)[v,u]` for `f ∈ C²`. -/
theorem D2_symm {f : RefState N p → ℝ} (hf : ContDiff ℝ 2 f) (y u v : RefState N p) :
    D2 f y u v = D2 f y v u :=
  (hf.contDiffAt.isSymmSndFDerivAt (by simp)) u v

/-!
## The contraction identity
-/

/-- Real pairing of two matrices against a real bilinear form `Q`:
`Σ_{j,α} (Q[P e_{jα}, R e_{jα}] + Q[i P e_{jα}, i R e_{jα}])`. -/
def gaussPair (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) (P R : Matrix (Fin N) (Fin N) ℂ) :
    ℝ :=
  ∑ j : Fin N, ∑ α : Fin p, (Q (lmul P (unitEntry j α)) (lmul R (unitEntry j α)) +
    Q (Complex.I • lmul P (unitEntry j α)) (Complex.I • lmul R (unitEntry j α)))

theorem lmul_unitEntry (P : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) (α : Fin p) :
    lmul P (unitEntry j α : RefState N p) = ∑ i, P i j • (unitEntry i α : RefState N p) := by
  funext k β
  by_cases h : β = α
  · subst h
    simp [lmul, unitEntry, Finset.sum_apply]
  · simp [lmul, unitEntry, Finset.sum_apply, h]

theorem smul_eq_re_im (c : ℂ) (v : RefState N p) :
    c • v = c.re • v + c.im • (Complex.I • v) := by
  funext i α
  apply Complex.ext <;> simp; ring

theorem Q_csum {ι : Type*} [Fintype ι] (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (u : ι → RefState N p) (c d : ι → ℂ) :
    Q (∑ i, c i • u i) (∑ k, d k • u k) = ∑ i, ∑ k,
      ((c i).re * (d k).re * Q (u i) (u k) + (c i).re * (d k).im * Q (u i) (Complex.I • u k) +
        (c i).im * (d k).re * Q (Complex.I • u i) (u k) +
        (c i).im * (d k).im * Q (Complex.I • u i) (Complex.I • u k)) := by
  simp only [map_sum, _root_.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_re_im (c i), smul_eq_re_im (d k)]
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul]
  ring

/-- Symmetric part of the coefficients of `Q` on column `α`. -/
def qA (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) (α : Fin p) (i k : Fin N) : ℝ :=
  Q (unitEntry i α) (unitEntry k α) + Q (Complex.I • unitEntry i α) (Complex.I • unitEntry k α)

/-- Antisymmetric part of the coefficients of `Q` on column `α`. -/
def qB (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) (α : Fin p) (i k : Fin N) : ℝ :=
  Q (unitEntry i α) (Complex.I • unitEntry k α) - Q (Complex.I • unitEntry i α) (unitEntry k α)

/-- The real-linear functional `M ↦ Σ_α Re tr(H_α M)` with `H_α = qA - i qB` Hermitian. -/
def pairForm (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    ℝ :=
  ∑ α : Fin p, ∑ i : Fin N, ∑ k : Fin N, (qA Q α i k * (M k i).re + qB Q α i k * (M k i).im)

theorem pairForm_add (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (M M' : Matrix (Fin N) (Fin N) ℂ) : pairForm Q (M + M') = pairForm Q M + pairForm Q M' := by
  simp only [pairForm, Matrix.add_apply, Complex.add_re, Complex.add_im, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem pairForm_conjTranspose (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (hQ : ∀ u v, Q u v = Q v u) (M : Matrix (Fin N) (Fin N) ℂ) :
    pairForm Q Mᴴ = pairForm Q M := by
  unfold pairForm
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im, qA, qB]
  rw [hQ (unitEntry k α) (unitEntry i α),
    hQ (Complex.I • unitEntry k α) (Complex.I • unitEntry i α),
    hQ (unitEntry k α) (Complex.I • unitEntry i α), hQ (Complex.I • unitEntry k α) (unitEntry i α)]
  ring

theorem gaussPair_eq_pairForm (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (P R : Matrix (Fin N) (Fin N) ℂ) : gaussPair Q P R = pairForm Q (R * Pᴴ) := by
  unfold gaussPair pairForm
  simp only [lmul_unitEntry, Finset.smul_sum, smul_smul, Q_csum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [mul_apply, conjTranspose_apply, Complex.re_sum, Complex.im_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, qA, qB]
  ring

/-- **Contraction identity.** For a symmetric real bilinear form `Q`, Hermitian `S, B` with
`SB + BS = WWᴴ`: `gaussPair Q B S = ½ gaussPair Q W W`. -/
theorem gaussPair_of_anticomm (Q : RefState N p →L[ℝ] RefState N p →L[ℝ] ℝ)
    (hQ : ∀ u v, Q u v = Q v u)
    {S B W : Matrix (Fin N) (Fin N) ℂ} (hS : S.IsHermitian) (hB : B.IsHermitian)
    (h : S * B + B * S = W * Wᴴ) : gaussPair Q B S = (1 / 2 : ℝ) * gaussPair Q W W := by
  rw [gaussPair_eq_pairForm, gaussPair_eq_pairForm, ← h, pairForm_add, hB.eq]
  have h1 : pairForm Q (S * B) = pairForm Q (B * S) := by
    rw [← pairForm_conjTranspose Q hQ (S * B), conjTranspose_mul, hS.eq, hB.eq]
  rw [← h1]
  ring

/-!
## The circular array as an image of real Gaussian coordinates
-/

/-- Real coordinates `((j, α), q)` of the circular array (`q = 0`: real part, `q = 1`:
imaginary part). -/
abbrev CircIdx (N p : ℕ) := (Fin N × Fin p) × Fin 2

/-- The real Gaussian law of the coordinates: i.i.d. `gaussianReal 0 (1/2)`. -/
abbrev circGauss (N p : ℕ) : Measure (CircIdx N p → ℝ) :=
  gaussianProduct (fun _ : CircIdx N p => (1 / 2 : ℝ≥0))

/-- `r ↦ (r_{(jα),0} + i r_{(jα),1})_{jα}`, the real-linear sample map of `matCircularLaw`. -/
def circSample (N p : ℕ) : (CircIdx N p → ℝ) →L[ℝ] RefState N p :=
  LinearMap.toContinuousLinearMap
    { toFun := fun r i α => (r ((i, α), 0) : ℂ) + (r ((i, α), 1) : ℂ) * Complex.I
      map_add' := fun r r' => by
        funext i α
        simp only [Pi.add_apply, Complex.ofReal_add]
        ring
      map_smul' := fun c r => by
        funext i α
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Complex.real_smul]
        ring }

theorem circSample_apply (r : CircIdx N p → ℝ) (i : Fin N) (α : Fin p) :
    circSample N p r i α = (r ((i, α), 0) : ℂ) + (r ((i, α), 1) : ℂ) * Complex.I := rfl

/-- `lmul K` as a real continuous linear map. -/
def lmulL (K : Matrix (Fin N) (Fin N) ℂ) : RefState N p →L[ℝ] RefState N p :=
  LinearMap.toContinuousLinearMap
    { toFun := lmul K
      map_add' := fun z z' => by
        funext i α
        simp only [lmul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        funext i α
        simp only [lmul, Pi.smul_apply, Complex.real_smul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring }

@[simp] theorem lmulL_apply (K : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) :
    lmulL K z = lmul K z := rfl

theorem continuous_lmul (K : Matrix (Fin N) (Fin N) ℂ) :
    Continuous (lmul K : RefState N p → RefState N p) :=
  (lmulL K).continuous

theorem lmul_smul_real (K : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (z : RefState N p) :
    lmul K (c • z) = c • lmul K z :=
  (lmulL K).map_smul c z

theorem lmul_sum {ι : Type*} (s : Finset ι) (K : Matrix (Fin N) (Fin N) ℂ)
    (z : ι → RefState N p) : lmul K (∑ i ∈ s, z i) = ∑ i ∈ s, lmul K (z i) :=
  map_sum (lmulL K) z s

theorem matCircularLaw_eq :
    matCircularLaw N p = (circGauss N p).map (circSample N p) := by
  unfold matCircularLaw circularVectorLaw circGauss gaussianProduct
  rw [Measure.map_map]
  · rfl
  · exact (continuous_pi fun i => continuous_pi fun α => continuous_apply _).measurable
  · exact (continuous_pi fun a => by fun_prop).measurable

instance isProbabilityMeasure_circGauss : IsProbabilityMeasure (circGauss N p) := by
  unfold circGauss gaussianProduct
  infer_instance

instance isProbabilityMeasure_matCircularLaw : IsProbabilityMeasure (matCircularLaw N p) := by
  rw [matCircularLaw_eq]
  exact (Measure.isProbabilityMeasure_map_iff
    (circSample N p).continuous.measurable.aemeasurable).mpr inferInstance

/-- Integrals against `matCircularLaw` as integrals over the real coordinates. -/
theorem integral_matCircularLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : RefState N p → E} (hF : Continuous F) :
    ∫ G, F G ∂matCircularLaw N p = ∫ r, F (circSample N p r) ∂circGauss N p := by
  rw [matCircularLaw_eq,
    integral_map (circSample N p).continuous.aemeasurable hF.aestronglyMeasurable]

theorem integrable_matCircularLaw_iff {E : Type*} [NormedAddCommGroup E]
    {F : RefState N p → E} (hF : Continuous F) :
    Integrable F (matCircularLaw N p) ↔
      Integrable (fun r => F (circSample N p r)) (circGauss N p) := by
  rw [matCircularLaw_eq]
  exact integrable_map_measure hF.aestronglyMeasurable (circSample N p).continuous.aemeasurable

/-- Bounded continuous functions are `matCircularLaw`-integrable. -/
theorem integrable_matCircularLaw_of_bound {F : RefState N p → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ z, |F z| ≤ C) : Integrable F (matCircularLaw N p) :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem circSample_single_re (j : Fin N) (α : Fin p) :
    circSample N p (Pi.single ((j, α), 0) 1) = unitEntry j α := by
  funext i β
  by_cases h : i = j ∧ β = α
  · obtain ⟨rfl, rfl⟩ := h
    simp [circSample_apply, unitEntry]
  · have h1 : ((i, β), (0 : Fin 2)) ≠ ((j, α), 0) := fun he => h (by simp_all [Prod.ext_iff])
    have h2 : ((i, β), (1 : Fin 2)) ≠ ((j, α), 0) := fun he => by simp [Prod.ext_iff] at he
    simp [circSample_apply, unitEntry, h1, h2, h]

theorem circSample_single_im (j : Fin N) (α : Fin p) :
    circSample N p (Pi.single ((j, α), 1) 1) = Complex.I • unitEntry j α := by
  funext i β
  by_cases h : i = j ∧ β = α
  · obtain ⟨rfl, rfl⟩ := h
    simp [circSample_apply, unitEntry]
  · have h1 : ((i, β), (1 : Fin 2)) ≠ ((j, α), 1) := fun he => h (by simp_all [Prod.ext_iff])
    have h2 : ((i, β), (0 : Fin 2)) ≠ ((j, α), 1) := fun he => by simp [Prod.ext_iff] at he
    simp [circSample_apply, unitEntry, h1, h2, h]

theorem circSample_eq_sum (r : CircIdx N p → ℝ) :
    circSample N p r = ∑ k, r k • circSample N p (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single r]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

/-!
## Real Gaussian integration by parts in one coordinate
-/

theorem coordPartial_eq_fderiv_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {φ : (ι → ℝ) → ℝ} (hφ : Differentiable ℝ φ) (j : ι) (x : ι → ℝ) :
    coordPartial φ j x = fderiv ℝ φ x (Pi.single j 1) := by
  unfold coordPartial
  have hu := hasDerivAt_update x j (x j)
  have h := (hφ (Function.update x j (x j))).hasFDerivAt.comp_hasDerivAt (x j) hu
  rw [Function.update_eq_self] at h
  exact h.deriv

/-- A real `C¹` function has its classical partial derivative as weak partial derivative
(`HasWeakCoordPartial`). -/
theorem hasWeakCoordPartial_of_contDiff_real {ι : Type} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (j : ι)
    (hg : ∀ x, fderiv ℝ f x (Pi.single j 1) = g x) : HasWeakCoordPartial j f g := by
  have hgfun : g = fun x => fderiv ℝ f x (Pi.single j 1) := funext fun x => (hg x).symm
  subst hgfun
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (fun x => fderiv ℝ f x (Pi.single j 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨hfc.locallyIntegrable, hdc.locallyIntegrable, ?_⟩
  intro φ hφ hφc
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ1 : Continuous (fun x => fderiv ℝ φ x (Pi.single j 1)) :=
    ((hφ.of_le (by exact_mod_cast le_top)).continuous_fderiv (n := 1) (by simp)).clm_apply
      continuous_const
  simp_rw [coordPartial_eq_fderiv_apply hφd j]
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (𝕜 := ℝ)
    (f := φ) (g := f) (v := Pi.single j 1)
    ((hφ1.smul hfc).integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) _ |>.smul_right))
    ((hφ.continuous.smul hdc).integrable_of_hasCompactSupport hφc.smul_right)
    ((hφ.continuous.smul hfc).integrable_of_hasCompactSupport hφc.smul_right)
    (fun x _ => hφd x) (fun x _ => hf.differentiable (by simp) x)
  rw [h, neg_neg]

/-- Coordinates are `circGauss`-integrable. -/
theorem coord_integrable_circGauss (k : CircIdx N p) :
    Integrable (fun r : CircIdx N p → ℝ => r k) (circGauss N p) := by
  unfold circGauss gaussianProduct
  have hmp := measurePreserving_eval
    (fun _ : CircIdx N p => ProbabilityTheory.gaussianReal 0 (1 / 2 : ℝ≥0)) k
  have hid : Integrable id (ProbabilityTheory.gaussianReal 0 (1 / 2 : ℝ≥0)) :=
    (ProbabilityTheory.memLp_id_gaussianReal 1).integrable le_rfl
  exact (hmp.integrable_comp measurable_id.aestronglyMeasurable).mpr hid

/-!
## Bounds from `IsC2BoundedBy`
-/

theorem norm_fderiv_fderiv_le {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (y : RefState N p) : ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact hf.hessian_bound y

theorem abs_fderiv_apply_le {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (y w : RefState N p) : |fderiv ℝ f y w| ≤ C * ‖w‖ := by
  rw [← Real.norm_eq_abs]
  exact ((fderiv ℝ f y).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (hf.deriv_bound y) (norm_nonneg _))

theorem abs_D2_le {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (y u v : RefState N p) : |D2 f y u v| ≤ C * ‖u‖ * ‖v‖ := by
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (fderiv ℝ f) y).le_opNorm₂ u v).trans ?_
  gcongr
  exact norm_fderiv_fderiv_le hf y

theorem contDiff_fderiv_of_C2 {f : RefState N p → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (fderiv ℝ f) :=
  hf.fderiv_right (by norm_num)

theorem continuous_D2_comp {f : RefState N p → ℝ} (hf : ContDiff ℝ 2 f) (m : RefState N p)
    (S : Matrix (Fin N) (Fin N) ℂ) (u v : RefState N p) :
    Continuous (fun G => D2 f (m + lmul S G) u v) :=
  ((((contDiff_fderiv_of_C2 hf).continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_lmul S))).clm_apply continuous_const).clm_apply
    continuous_const

theorem continuous_fderiv_comp {f : RefState N p → ℝ} (hf : ContDiff ℝ 2 f) (m : RefState N p)
    (S B : Matrix (Fin N) (Fin N) ℂ) :
    Continuous (fun G => fderiv ℝ f (m + lmul S G) (lmul B G)) :=
  ((contDiff_fderiv_of_C2 hf).continuous.comp
    (continuous_const.add (continuous_lmul S))).clm_apply (continuous_lmul B)

/-- The `D²f` integrands are `matCircularLaw`-integrable. -/
theorem integrable_D2_lmul {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (m : RefState N p) (S : Matrix (Fin N) (Fin N) ℂ) (u v : RefState N p) :
    Integrable (fun G => D2 f (m + lmul S G) u v) (matCircularLaw N p) :=
  integrable_matCircularLaw_of_bound (continuous_D2_comp hf.contDiff m S u v)
    (fun _ => abs_D2_le hf _ u v)

/-!
## The Stein identity
-/

/-- The coordinate-`k` integrand `Df(m + S G)[B e_k]`, `e_k = circSample (single k 1)`. -/
def steinFn (f : RefState N p → ℝ) (m : RefState N p) (S B : Matrix (Fin N) (Fin N) ℂ)
    (k : CircIdx N p) (r : CircIdx N p → ℝ) : ℝ :=
  fderiv ℝ f (m + lmul S (circSample N p r)) (lmul B (circSample N p (Pi.single k 1)))

theorem hasFDerivAt_steinFn {f : RefState N p → ℝ} (hf : ContDiff ℝ 2 f) (m : RefState N p)
    (S B : Matrix (Fin N) (Fin N) ℂ) (k : CircIdx N p) (r : CircIdx N p → ℝ) :
    HasFDerivAt (steinFn f m S B k)
      ((ContinuousLinearMap.apply ℝ ℝ (lmul B (circSample N p (Pi.single k 1)))).comp
        ((fderiv ℝ (fderiv ℝ f) (m + lmul S (circSample N p r))).comp
          ((lmulL S).comp (circSample N p)))) r := by
  have hA : HasFDerivAt (fun r => m + lmul S (circSample N p r))
      ((lmulL S).comp (circSample N p)) r :=
    ((lmulL S).comp (circSample N p)).hasFDerivAt.const_add m
  exact (ContinuousLinearMap.apply ℝ ℝ (lmul B (circSample N p (Pi.single k 1)))).hasFDerivAt.comp
    r ((((contDiff_fderiv_of_C2 hf).differentiable (by simp)) _).hasFDerivAt.comp r hA)

theorem contDiff_steinFn {f : RefState N p → ℝ} (hf : ContDiff ℝ 2 f) (m : RefState N p)
    (S B : Matrix (Fin N) (Fin N) ℂ) (k : CircIdx N p) : ContDiff ℝ 1 (steinFn f m S B k) :=
  (ContinuousLinearMap.apply ℝ ℝ (lmul B (circSample N p (Pi.single k 1)))).contDiff.comp
    ((contDiff_fderiv_of_C2 hf).comp
      (contDiff_const.add ((lmulL S).comp (circSample N p)).contDiff))

theorem fderiv_steinFn_single {f : RefState N p → ℝ} (hf : ContDiff ℝ 2 f) (m : RefState N p)
    (S B : Matrix (Fin N) (Fin N) ℂ) (k : CircIdx N p) (r : CircIdx N p → ℝ) :
    fderiv ℝ (steinFn f m S B k) r (Pi.single k 1) =
      D2 f (m + lmul S (circSample N p r)) (lmul S (circSample N p (Pi.single k 1)))
        (lmul B (circSample N p (Pi.single k 1))) := by
  rw [(hasFDerivAt_steinFn hf m S B k r).fderiv]
  rfl

theorem integrable_coord_mul_steinFn {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (m : RefState N p) (S B : Matrix (Fin N) (Fin N) ℂ) (k : CircIdx N p) :
    Integrable (fun r => r k • steinFn f m S B k r) (circGauss N p) := by
  have h := (coord_integrable_circGauss k).bdd_mul (f := steinFn f m S B k)
    (contDiff_steinFn hf.contDiff m S B k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs]; exact abs_fderiv_apply_le hf _ _)
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul, mul_comm]

/-- One-coordinate Stein identity from `MultivariateGaussianIBP` (variance `1/2`). -/
theorem integral_coord_mul_steinFn (hIBP : MultivariateGaussianIBP) {C : ℝ}
    {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) (m : RefState N p)
    (S B : Matrix (Fin N) (Fin N) ℂ) (k : CircIdx N p) :
    ∫ r, r k • steinFn f m S B k r ∂circGauss N p =
      (1 / 2 : ℝ) * ∫ r, D2 f (m + lmul S (circSample N p r))
        (lmul S (circSample N p (Pi.single k 1))) (lmul B (circSample N p (Pi.single k 1)))
        ∂circGauss N p := by
  have hc : Continuous fun r => D2 f (m + lmul S (circSample N p r))
      (lmul S (circSample N p (Pi.single k 1))) (lmul B (circSample N p (Pi.single k 1))) :=
    (continuous_D2_comp hf.contDiff m S _ _).comp (circSample N p).continuous
  have hgi : Integrable (fun r => D2 f (m + lmul S (circSample N p r))
      (lmul S (circSample N p (Pi.single k 1))) (lmul B (circSample N p (Pi.single k 1))))
      (circGauss N p) :=
    Integrable.of_bound hc.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact abs_D2_le hf _ _ _)
  have hφi : Integrable (steinFn f m S B k) (circGauss N p) :=
    Integrable.of_bound (contDiff_steinFn hf.contDiff m S B k).continuous.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]; exact abs_fderiv_apply_le hf _ _)
  have h := hIBP (CircIdx N p) (fun _ => (1 / 2 : ℝ≥0)) ℝ k (steinFn f m S B k) _
    (fun _ _ => by norm_num)
    (hasWeakCoordPartial_of_contDiff_real (contDiff_steinFn hf.contDiff m S B k) k
      (fderiv_steinFn_single hf.contDiff m S B k)) hφi hgi
    (integrable_coord_mul_steinFn hf m S B k)
  rw [h, smul_eq_mul]
  norm_num

theorem fderiv_lmul_circSample_eq_sum {f : RefState N p → ℝ} (m : RefState N p)
    (S B : Matrix (Fin N) (Fin N) ℂ) (r : CircIdx N p → ℝ) :
    fderiv ℝ f (m + lmul S (circSample N p r)) (lmul B (circSample N p r)) =
      ∑ k, r k • steinFn f m S B k r := by
  have h : lmul B (circSample N p r) = ∑ k, r k • lmul B (circSample N p (Pi.single k 1)) := by
    conv_lhs => rw [circSample_eq_sum r]
    rw [lmul_sum]
    exact Finset.sum_congr rfl fun k _ => lmul_smul_real B (r k) _
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

/-- The Stein integrand `Df(m + SG)[BG]` is `matCircularLaw`-integrable. -/
theorem integrable_fderiv_lmul {C : ℝ} {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f)
    (m : RefState N p) (S B : Matrix (Fin N) (Fin N) ℂ) :
    Integrable (fun G => fderiv ℝ f (m + lmul S G) (lmul B G)) (matCircularLaw N p) := by
  rw [integrable_matCircularLaw_iff (continuous_fderiv_comp hf.contDiff m S B)]
  have h := integrable_finsetSum Finset.univ fun k _ => integrable_coord_mul_steinFn hf m S B k
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  exact (fderiv_lmul_circSample_eq_sum m S B r).symm

/-- **Stein identity for the circular array.** For bounded `C²` `f`:
`E Df(m + SG)[BG] = ½ Σ_{j,α} E (D²f(m+SG)[B e_{jα}, S e_{jα}] +
D²f(m+SG)[i B e_{jα}, i S e_{jα}])`, `G ~ matCircularLaw N p`. -/
theorem integral_fderiv_lmul (hIBP : MultivariateGaussianIBP) {C : ℝ} {f : RefState N p → ℝ}
    (hf : IsC2BoundedBy C f) (m : RefState N p) (S B : Matrix (Fin N) (Fin N) ℂ) :
    ∫ G, fderiv ℝ f (m + lmul S G) (lmul B G) ∂matCircularLaw N p =
      (1 / 2 : ℝ) * ∑ j : Fin N, ∑ α : Fin p, ∫ G,
        (D2 f (m + lmul S G) (lmul B (unitEntry j α)) (lmul S (unitEntry j α)) +
         D2 f (m + lmul S G) (Complex.I • lmul B (unitEntry j α))
          (Complex.I • lmul S (unitEntry j α)))
        ∂matCircularLaw N p := by
  have hsymm : ∀ k : CircIdx N p,
      ∫ r, D2 f (m + lmul S (circSample N p r))
        (lmul S (circSample N p (Pi.single k 1))) (lmul B (circSample N p (Pi.single k 1)))
        ∂circGauss N p =
      ∫ G, D2 f (m + lmul S G) (lmul B (circSample N p (Pi.single k 1)))
        (lmul S (circSample N p (Pi.single k 1))) ∂matCircularLaw N p := by
    intro k
    rw [integral_matCircularLaw (continuous_D2_comp hf.contDiff m S _ _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun r => D2_symm hf.contDiff _ _ _)
  have hI : ∀ (j : Fin N) (α : Fin p),
      Complex.I • lmul B (unitEntry j α) = lmul B (Complex.I • (unitEntry j α : RefState N p)) ∧
      Complex.I • lmul S (unitEntry j α) = lmul S (Complex.I • (unitEntry j α : RefState N p)) := by
    intro j α
    constructor <;>
    · funext i β
      simp only [lmul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
  calc ∫ G, fderiv ℝ f (m + lmul S G) (lmul B G) ∂matCircularLaw N p
      = ∫ r, ∑ k, r k • steinFn f m S B k r ∂circGauss N p := by
        rw [integral_matCircularLaw (continuous_fderiv_comp hf.contDiff m S B)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun r =>
          fderiv_lmul_circSample_eq_sum m S B r)
    _ = ∑ k, ∫ r, r k • steinFn f m S B k r ∂circGauss N p :=
        integral_finsetSum _ fun k _ => integrable_coord_mul_steinFn hf m S B k
    _ = ∑ k : CircIdx N p, (1 / 2 : ℝ) * ∫ G, D2 f (m + lmul S G)
          (lmul B (circSample N p (Pi.single k 1))) (lmul S (circSample N p (Pi.single k 1)))
          ∂matCircularLaw N p := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_coord_mul_steinFn hIBP hf m S B k, hsymm k]
    _ = _ := by
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Fin.sum_univ_two, circSample_single_re, circSample_single_im, (hI j α).1, (hI j α).2,
          integral_add (integrable_D2_lmul hf m S _ _) (integrable_D2_lmul hf m S _ _)]
        ring

end BlockBand.Palm.ReferenceFlow
