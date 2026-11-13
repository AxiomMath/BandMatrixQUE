module

public import BlockBand.Critical.RelativeVectors.Hessian
public import BlockBand.Critical.RelativeVectors.HermContract
public import BlockBand.Critical.RelativeVectors.GenDiff

/-!
# Tested backward functions: the diagonal and floor errors

For a bounded `C²` test of a fixed array of central labels, the reference backward function has
the representation `g_s(z) = E_aux f((𝓜_{s,t}z + Ξ_{s,t})_tested)`; with `T_j` the map from the
`j`th input vector to the tested array, `∇_j²g_s = E_aux T_j^*(∇²f)T_j`, and `Σ_j ‖T_j‖²_HS` is at
most the tested dimension since `‖𝓜‖ ≤ 1`.

Setting: tested labels `ι : Fin k → Fin N`, the tested projection `π z = (z_{ι m})_m`
(`testProj`), a `C²` test `φ` of the tested array with `|φ| ≤ K₀`, `‖Dφ‖ ≤ K₁`, `‖D²φ‖ ≤ K₂`, the
array test `f = φ ∘ π`, and its backward function `g(z) = ∫ f(Mz + Ξ) dP` (measurable `M`, `Ξ`,
entries `|M_kj| ≤ 1`, which follows from the contraction field of `IsReferenceFlow`).
`T_i v = π(M e_i v) = (M_{ι m, i} v)_m` (`colMap`), `τ_i = Σ_m |M_{ι m, i}|²`.

* `fderiv_comp_testProj_apply`, `fderiv_fderiv_comp_testProj_apply`: the chain rule for `φ ∘ π`.
* `hq_backward`: `hq (D²g) i v = ∫ hermForm (T_i^* D²φ T_i) v dP` (the label-`i` Hessian of `g`).
* `diagError_backward_le`: if `|Σ_{|i-j| ≥ ℓ} c_ij(|p^*z_j|² - ‖p‖²)| ≤ X_i‖p‖²` for every
  label `i` and `p`, then `|diagError(D²g)| ≤ 2r²K₂ Σ_i X_i ∫ τ_i dP`.
* `sum_tau_le`: `Σ_i τ_i ≤ k` for every row-contraction (`Σ_i |M_{ki}|² ≤ 1`).
* `floorError_backward_le`: `|floorError| ≤ Σ_i |β̂_i - β_i|(½K₁‖z_i‖ ∫√τ_i + ½ r K₂ ∫τ_i)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.CoarseRelative

variable {N r k : ℕ}

/-- Tested projection `π z = (z_{ι m})_m`. -/
def testProj (ι : Fin k → Fin N) : (Fin N → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) :=
  ContinuousLinearMap.pi fun m => ContinuousLinearMap.proj (ι m)

@[simp] theorem testProj_apply (ι : Fin k → Fin N) (z : Fin N → Fin r → ℂ) :
    testProj ι z = fun m => z (ι m) := rfl

theorem norm_testProj_le (ι : Fin k → Fin N) (z : Fin N → Fin r → ℂ) :
    ‖testProj ι z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun m => ?_
  exact norm_le_pi_norm z (ι m)

theorem opNorm_testProj_le (ι : Fin k → Fin N) :
    ‖(testProj ι : (Fin N → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]; exact norm_testProj_le ι z

/-- `T_i v = π(M e_i v) = (M_{ι m, i} v)_m`. -/
theorem testProj_arrayMul_single (ι : Fin k → Fin N) (M : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (v : Fin r → ℂ) :
    testProj ι (arrayMul M (single i v)) = fun m => M (ι m) i • v := by
  funext m q
  simp [arrayMul, single, Pi.single_apply, ite_apply]

/-!
## The chain rule for `φ ∘ π`
-/

section Chain

variable {φ : (Fin k → Fin r → ℂ) → ℝ}

theorem fderiv_comp_testProj (ι : Fin k → Fin N) (hφ : ContDiff ℝ 2 φ) :
    fderiv ℝ (fun z => φ (testProj ι z)) =
      fun x => (fderiv ℝ φ (testProj ι x)).comp
        (testProj ι : (Fin N → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ)) := by
  funext x
  exact ((hφ.differentiable (by norm_num) _).hasFDerivAt.comp x
    (testProj ι : (Fin N → Fin r → ℂ) →L[ℝ] _).hasFDerivAt).fderiv

theorem fderiv_comp_testProj_apply (ι : Fin k → Fin N) (hφ : ContDiff ℝ 2 φ)
    (x u : Fin N → Fin r → ℂ) :
    fderiv ℝ (fun z => φ (testProj ι z)) x u = fderiv ℝ φ (testProj ι x) (testProj ι u) := by
  rw [fderiv_comp_testProj ι hφ]; rfl

theorem fderiv_fderiv_comp_testProj_apply (ι : Fin k → Fin N) (hφ : ContDiff ℝ 2 φ)
    (x u w : Fin N → Fin r → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => φ (testProj ι z))) x u w =
      fderiv ℝ (fderiv ℝ φ) (testProj ι x) (testProj ι u) (testProj ι w) := by
  rw [fderiv_comp_testProj ι hφ]
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set π := (testProj ι : (Fin N → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ))
  have h := (((ContinuousLinearMap.compL ℝ (Fin N → Fin r → ℂ) (Fin k → Fin r → ℂ) ℝ).flip
    π).hasFDerivAt).comp x ((hd (π x)).hasFDerivAt.comp x π.hasFDerivAt)
  rw [show (fun x => (fderiv ℝ φ (π x)).comp π) =
    ((ContinuousLinearMap.compL ℝ (Fin N → Fin r → ℂ) (Fin k → Fin r → ℂ) ℝ).flip π) ∘
      (fderiv ℝ φ ∘ π) from rfl, h.fderiv]
  rfl

theorem norm_fderiv_comp_testProj_le (ι : Fin k → Fin N) (hφ : ContDiff ℝ 2 φ) {K₁ : ℝ}
    (hK : ∀ y, ‖fderiv ℝ φ y‖ ≤ K₁) (x : Fin N → Fin r → ℂ) :
    ‖fderiv ℝ (fun z => φ (testProj ι z)) x‖ ≤ K₁ := by
  rw [fderiv_comp_testProj ι hφ]
  refine ((fderiv ℝ φ (testProj ι x)).opNorm_comp_le _).trans ?_
  have := mul_le_mul (hK (testProj ι x)) (opNorm_testProj_le (r := r) ι)
    (norm_nonneg _) (le_trans (norm_nonneg (fderiv ℝ φ (testProj ι x))) (hK _))
  simpa using this

theorem norm_fderiv_fderiv_comp_testProj_le (ι : Fin k → Fin N) (hφ : ContDiff ℝ 2 φ) {K₂ : ℝ}
    (hK : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ K₂) (hK₂ : 0 ≤ K₂) (x : Fin N → Fin r → ℂ) :
    ‖fderiv ℝ (fderiv ℝ (fun z => φ (testProj ι z))) x‖ ≤ K₂ := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK₂ fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [fderiv_fderiv_comp_testProj_apply ι hφ]
  refine ((fderiv ℝ (fderiv ℝ φ) (testProj ι x) (testProj ι u)).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ φ) (testProj ι x)).le_opNorm _).trans
    (mul_le_mul (hK _) (norm_testProj_le ι u) (norm_nonneg _) hK₂)) (norm_nonneg _)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_testProj_le ι w) (by positivity)

end Chain

/-!
## Label-`i` pullback of a bilinear form
-/

/-- `S_t v = (t_m v)_m`. -/
def colMap (t : Fin k → ℂ) : (Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) :=
  ContinuousLinearMap.pi fun m => t m • ContinuousLinearMap.id ℝ (Fin r → ℂ)

@[simp] theorem colMap_apply (t : Fin k → ℂ) (v : Fin r → ℂ) :
    colMap t v = fun m => t m • v := rfl

/-- `(T^*DT)(v, w) = D(Tv, Tw)`, `T = S_t`. -/
def labelBil (D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ) (t : Fin k → ℂ) :
    (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Fin r → ℂ) (Fin k → Fin r → ℂ) ℝ).flip (colMap t)).comp
    (D.comp (colMap t))

@[simp] theorem labelBil_apply (D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ)
    (t : Fin k → ℂ) (v w : Fin r → ℂ) :
    labelBil D t v w = D (fun m => t m • v) (fun m => t m • w) := rfl

/-- `τ = Σ_m |t_m|²`. -/
def tau (t : Fin k → ℂ) : ℝ := ∑ m, ‖t m‖ ^ 2

theorem tau_nonneg (t : Fin k → ℂ) : 0 ≤ tau t := by unfold tau; positivity

theorem norm_colMap_le (t : Fin k → ℂ) (v : Fin r → ℂ) :
    ‖(fun m => t m • v : Fin k → Fin r → ℂ)‖ ≤ Real.sqrt (tau t) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun m => ?_
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
  refine Real.le_sqrt_of_sq_le ?_
  unfold tau
  exact Finset.single_le_sum (f := fun m => ‖t m‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ m)

theorem abs_labelBil_le {D : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) →L[ℝ] ℝ} {K₂ : ℝ}
    (hD : ‖D‖ ≤ K₂) (t : Fin k → ℂ) (v w : Fin r → ℂ) :
    |labelBil D t v w| ≤ K₂ * tau t * ‖v‖ * ‖w‖ := by
  rw [labelBil_apply, ← Real.norm_eq_abs]
  have hK₂ : 0 ≤ K₂ := (norm_nonneg D).trans hD
  have hs := Real.mul_self_sqrt (tau_nonneg t)
  refine ((D (fun m => t m • v)).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_right ((D.le_opNorm _).trans
    (mul_le_mul hD (norm_colMap_le t v) (norm_nonneg _) hK₂)) (norm_nonneg _)).trans ?_
  calc K₂ * (Real.sqrt (tau t) * ‖v‖) * ‖(fun m => t m • w : Fin k → Fin r → ℂ)‖
      ≤ K₂ * (Real.sqrt (tau t) * ‖v‖) * (Real.sqrt (tau t) * ‖w‖) :=
        mul_le_mul_of_nonneg_left (norm_colMap_le t w) (by positivity)
    _ = K₂ * (Real.sqrt (tau t) * Real.sqrt (tau t)) * ‖v‖ * ‖w‖ := by ring
    _ = K₂ * tau t * ‖v‖ * ‖w‖ := by rw [hs]

/-!
## The backward function of a tested test
-/

/-- `‖Mz‖ ≤ N‖z‖` for entries `|M_kj| ≤ 1`. -/
theorem norm_arrayMul_le {M : Matrix (Fin N) (Fin N) ℂ} (hM : ∀ a b, ‖M a b‖ ≤ 1)
    (z : Fin N → Fin r → ℂ) : ‖arrayMul M z‖ ≤ N * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun q => ?_
  unfold arrayMul
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖M a j * z j q‖ ≤ ∑ _j : Fin N, ‖z‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        calc ‖M a j‖ * ‖z j q‖ ≤ 1 * ‖z j q‖ := mul_le_mul_of_nonneg_right (hM a j) (norm_nonneg _)
          _ = ‖z j q‖ := one_mul _
          _ ≤ ‖z j‖ := norm_le_pi_norm (z j) q
          _ ≤ ‖z‖ := norm_le_pi_norm z j
    _ = N * ‖z‖ := by simp

theorem opNorm_arrayMulCLM_le {M : Matrix (Fin N) (Fin N) ℂ} (hM : ∀ a b, ‖M a b‖ ≤ 1) :
    ‖(arrayMulCLM M : (Fin N → Fin r → ℂ) →L[ℝ] _)‖ ≤ N :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => by
    rw [arrayMulCLM_apply]; exact norm_arrayMul_le hM z

section Backward

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : Ω → Matrix (Fin N) (Fin N) ℂ} {Ξ : Ω → Fin N → Fin r → ℂ}
  {φ : (Fin k → Fin r → ℂ) → ℝ}

/-- Standing hypotheses on a tested test `φ` and the propagator. -/
structure TestedSetting (P : Measure Ω) (M : Ω → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : Ω → Fin N → Fin r → ℂ) (φ : (Fin k → Fin r → ℂ) → ℝ) (K₀ K₁ K₂ : ℝ) : Prop where
  measM : Measurable M
  measXi : Measurable Ξ
  entry : ∀ ω a b, ‖M ω a b‖ ≤ 1
  c2 : ContDiff ℝ 2 φ
  bound0 : ∀ y, |φ y| ≤ K₀
  bound1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ K₁
  bound2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ K₂
  nonneg1 : 0 ≤ K₁
  nonneg2 : 0 ≤ K₂

/-- `D²g(z)(u, w) = ∫ D²φ(π(Mz+Ξ))(π Mu, π Mw) dP` for `g = ∫ φ(π(M · + Ξ)) dP`. -/
theorem hess_tested (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ} (hS : TestedSetting P M Ξ φ K₀ K₁ K₂)
    (z u w : Fin N → Fin r → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z u w =
      ∫ ω, fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))
        (testProj ι (arrayMul (M ω) u)) (testProj ι (arrayMul (M ω) w)) ∂P := by
  have hf : ContDiff ℝ 2 (fun z : Fin N → Fin r → ℂ => φ (testProj ι z)) :=
    hS.c2.comp (testProj ι).contDiff
  have h := fderiv_fderiv_backward_apply (P := P) (f := fun z => φ (testProj ι z)) hS.measM
    hS.measXi hf (B := N) (K₀ := K₀) (K₁ := K₁) (K₂ := K₂)
    (fun ω => opNorm_arrayMulCLM_le (hS.entry ω)) (by positivity) (fun x => hS.bound0 _)
    (norm_fderiv_comp_testProj_le ι hS.c2 hS.bound1) hS.nonneg1
    (norm_fderiv_fderiv_comp_testProj_le ι hS.c2 hS.bound2 hS.nonneg2) hS.nonneg2 z u w
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact fderiv_fderiv_comp_testProj_apply ι hS.c2 _ _ _

/-- Integrability of a Hessian entry. -/
theorem integrable_hess_tested (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (z u w : Fin N → Fin r → ℂ) :
    Integrable (fun ω => fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))
        (testProj ι (arrayMul (M ω) u)) (testProj ι (arrayMul (M ω) w))) P := by
  have hc : Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → Fin r → ℂ) =>
      fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul p.1 z + p.2))
        (testProj ι (arrayMul p.1 u)) (testProj ι (arrayMul p.1 w)) := by
    have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
      (hS.c2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
    have hπ := (testProj ι : (Fin N → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ)).continuous
    refine ((h2.comp (hπ.comp (((continuous_arrayMul_apply z).comp continuous_fst).add
      continuous_snd))).clm_apply (hπ.comp ((continuous_arrayMul_apply u).comp
        continuous_fst))).clm_apply (hπ.comp ((continuous_arrayMul_apply w).comp continuous_fst))
  refine Integrable.of_bound (μ := P) ((hc.measurable.comp
    (hS.measM.prodMk hS.measXi)).aestronglyMeasurable) (K₂ * (N * ‖u‖) * (N * ‖w‖))
    (Filter.Eventually.of_forall fun ω => ?_)
  have hK₂ := hS.nonneg2
  refine ((fderiv ℝ (fderiv ℝ φ) _ _).le_opNorm _).trans ?_
  refine mul_le_mul ?_ ((norm_testProj_le ι _).trans (norm_arrayMul_le (hS.entry ω) w))
    (norm_nonneg _) (by positivity)
  refine ((fderiv ℝ (fderiv ℝ φ) _).le_opNorm _).trans ?_
  exact mul_le_mul (hS.bound2 _) ((norm_testProj_le ι _).trans (norm_arrayMul_le (hS.entry ω) u))
    (norm_nonneg _) hK₂

/-- The label-`i` Hermitian Hessian form of `g`: `hq(D²g) i v = ∫ hermForm(T_i^*D²φT_i) v dP`. -/
theorem hq_backward (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ} (hS : TestedSetting P M Ξ φ K₀ K₁ K₂)
    (z : Fin N → Fin r → ℂ) (i : Fin N) (v : Fin r → ℂ) :
    hq (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z) i v =
      ∫ ω, hermForm (labelBil (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω)))
        (fun m => M ω (ι m) i)) v ∂P := by
  unfold hq hermForm
  rw [hess_tested ι hS, hess_tested ι hS, ← integral_add (integrable_hess_tested ι hS _ _ _)
    (integrable_hess_tested ι hS _ _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [testProj_arrayMul_single, labelBil_apply]

theorem integrable_hermForm_backward (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (z : Fin N → Fin r → ℂ) (i : Fin N) (v : Fin r → ℂ) :
    Integrable (fun ω => hermForm (labelBil (fderiv ℝ (fderiv ℝ φ)
      (testProj ι (arrayMul (M ω) z + Ξ ω))) (fun m => M ω (ι m) i)) v) P := by
  have h := (integrable_hess_tested ι hS z (single i v) (single i v)).add
    (integrable_hess_tested ι hS z (single i (Complex.I • v)) (single i (Complex.I • v)))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [hermForm, testProj_arrayMul_single, labelBil_apply, Pi.add_apply]

theorem integrable_tau (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ} (hS : TestedSetting P M Ξ φ K₀ K₁ K₂)
    (i : Fin N) : Integrable (fun ω => tau (fun m => M ω (ι m) i)) P := by
  have hc : Continuous fun A : Matrix (Fin N) (Fin N) ℂ => tau (fun m => A (ι m) i) := by
    unfold tau
    exact continuous_finsetSum _ fun m _ => (continuous_id.matrix_elem (ι m) i).norm.pow 2
  refine Integrable.of_bound (μ := P) (hc.measurable.comp hS.measM).aestronglyMeasurable k
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tau_nonneg _)]
  unfold tau
  calc ∑ m, ‖M ω (ι m) i‖ ^ 2 ≤ ∑ _m : Fin k, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have := hS.entry ω (ι m) i
        have h0 := norm_nonneg (M ω (ι m) i)
        nlinarith
    _ = k := by simp

/-- **The diagonal error of a tested backward function.** If for every label
`i` the quadratic form of `Δ_i = Σ_{|i-j| ≥ ℓ} c_ij (z_jz_j^* - I_r)` is bounded by `X_i`, then
`|diagError(D²g)(z)| ≤ 2r²K₂ Σ_i X_i ∫ τ_i dP`, `τ_i = Σ_m |M_{ι m, i}|²`. -/
theorem diagError_backward_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (lam : Fin N → ℝ) (ℓ : ℕ) (z : Fin N → Fin r → ℂ)
    (X : Fin N → ℝ)
    (hX : ∀ i (p : Fin r → ℂ), |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤ X i * nsq p) :
    |diagError N r lam ℓ
        (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z) z| ≤
      2 * (r : ℝ) ^ 2 * K₂ * ∑ i, X i * ∫ ω, tau (fun m => M ω (ι m) i) ∂P := by
  set D2 := fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z
  set Bω : Fin N → Ω → (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] ℝ := fun i ω =>
    labelBil (fderiv ℝ (fderiv ℝ φ) (testProj ι (arrayMul (M ω) z + Ξ ω))) (fun m => M ω (ι m) i)
  have hint := integrable_hermForm_backward ι hS z
  -- each label: the inner sum is an integral
  have hi : ∀ i, ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * (hq D2 i (z j) - hqTrace D2 i) =
      ∫ ω, ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j), dysonCoupling N lam i j *
        (hermForm (Bω i ω) (z j) - ∑ q : Fin r, hermForm (Bω i ω) (eR q)) ∂P := by
    intro i
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_sub (hint i (z j)) (integrable_finsetSum _ fun q _ =>
        hint i (eR q)), integral_finsetSum _ fun q _ => hint i (eR q)]
      unfold hqTrace
      rw [hq_backward ι hS z i (z j)]
      congr 2
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hq_backward ι hS z i]
    · intro j _
      exact ((hint i (z j)).sub (integrable_finsetSum _ fun q _ => hint i (eR q))).const_mul _
  have hbound : ∀ i, |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * (hq D2 i (z j) - hqTrace D2 i)| ≤
      8 * (r : ℝ) ^ 2 * K₂ * X i * ∫ ω, tau (fun m => M ω (ι m) i) ∂P := by
    intro i
    rw [hi i, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      ((integrable_tau ι hS i).const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [Real.norm_eq_abs]
    have := herm_contract_le (univ.filter (fun j => ℓ ≤ labelDist i j))
      (fun j => dysonCoupling N lam i j) z (B := Bω i ω) (L := K₂ * tau (fun m => M ω (ι m) i))
      (X := X i) (fun v w => abs_labelBil_le (hS.bound2 _) _ v w)
      (mul_nonneg hS.nonneg2 (tau_nonneg _)) (hX i)
    calc _ ≤ 8 * (r : ℝ) ^ 2 * (K₂ * tau (fun m => M ω (ι m) i)) * X i := this
      _ = 8 * (r : ℝ) ^ 2 * K₂ * X i * tau (fun m => M ω (ι m) i) := by ring
  unfold diagError
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  calc 1 / 4 * |∑ i, ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
        dysonCoupling N lam i j * (hq D2 i (z j) - hqTrace D2 i)|
      ≤ 1 / 4 * ∑ i, 8 * (r : ℝ) ^ 2 * K₂ * X i * ∫ ω, tau (fun m => M ω (ι m) i) ∂P := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hbound i)
    _ = 2 * (r : ℝ) ^ 2 * K₂ * ∑ i, X i * ∫ ω, tau (fun m => M ω (ι m) i) ∂P := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

theorem integrable_sqrt_tau (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (i : Fin N) :
    Integrable (fun ω => Real.sqrt (tau (fun m => M ω (ι m) i))) P := by
  have hc : Continuous fun A : Matrix (Fin N) (Fin N) ℂ => Real.sqrt (tau (fun m => A (ι m) i)) := by
    unfold tau
    exact (continuous_finsetSum _ fun m _ =>
      (continuous_id.matrix_elem (ι m) i).norm.pow 2).sqrt
  refine Integrable.of_bound (μ := P) (hc.measurable.comp hS.measM).aestronglyMeasurable
    (Real.sqrt k) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  unfold tau
  calc ∑ m, ‖M ω (ι m) i‖ ^ 2 ≤ ∑ _m : Fin k, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have := hS.entry ω (ι m) i
        have h0 := norm_nonneg (M ω (ι m) i)
        nlinarith
    _ = k := by simp

/-- `|hqTrace(D²g) i| ≤ 2 r K₂ ∫ τ_i`. -/
theorem abs_hqTrace_backward_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (z : Fin N → Fin r → ℂ) (i : Fin N) :
    |hqTrace (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z)
      i| ≤ 2 * r * K₂ * ∫ ω, tau (fun m => M ω (ι m) i) ∂P := by
  unfold hqTrace
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q : Fin r, |hq (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι
        (arrayMul (M ω) z + Ξ ω)) ∂P)) z) i (Pi.single q 1)|
      ≤ ∑ _q : Fin r, 2 * K₂ * ∫ ω, tau (fun m => M ω (ι m) i) ∂P := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [hq_backward ι hS z i, ← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans ?_
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((integrable_tau ι hS i).const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
        simp only
        rw [Real.norm_eq_abs]
        unfold hermForm
        have h1 := abs_labelBil_le (hS.bound2 (testProj ι (arrayMul (M ω) z + Ξ ω)))
          (fun m => M ω (ι m) i) (eR q) (eR q)
        have h2 := abs_labelBil_le (hS.bound2 (testProj ι (arrayMul (M ω) z + Ξ ω)))
          (fun m => M ω (ι m) i) (Complex.I • eR q) (Complex.I • eR q)
        have hn : ‖(Complex.I • eR q : Fin r → ℂ)‖ = 1 := by
          rw [norm_smul, Complex.norm_I, one_mul, norm_eR]
        rw [norm_eR] at h1
        rw [hn] at h2
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ K₂ * tau (fun m => M ω (ι m) i) * 1 * 1 + K₂ * tau (fun m => M ω (ι m) i) * 1 * 1 :=
            add_le_add h1 h2
          _ = 2 * K₂ * tau (fun m => M ω (ι m) i) := by ring
    _ = 2 * r * K₂ * ∫ ω, tau (fun m => M ω (ι m) i) ∂P := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `|Dg(z)(e_i v)| ≤ K₁‖v‖ ∫ √τ_i`. -/
theorem abs_fderiv_backward_single_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (z : Fin N → Fin r → ℂ) (i : Fin N) (v : Fin r → ℂ) :
    |fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P) z (single i v)| ≤
      K₁ * ‖v‖ * ∫ ω, Real.sqrt (tau (fun m => M ω (ι m) i)) ∂P := by
  have hf : ContDiff ℝ 2 (fun z : Fin N → Fin r → ℂ => φ (testProj ι z)) :=
    hS.c2.comp (testProj ι).contDiff
  rw [fderiv_backward_apply (P := P) (f := fun z => φ (testProj ι z)) hS.measM hS.measXi hf
    (B := N) (K₀ := K₀) (K₁ := K₁) (fun ω => opNorm_arrayMulCLM_le (hS.entry ω))
    (fun x => hS.bound0 _) (norm_fderiv_comp_testProj_le ι hS.c2 hS.bound1) hS.nonneg1 z
    (single i v), ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    ((integrable_sqrt_tau ι hS i).const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [fderiv_comp_testProj_apply ι hS.c2, testProj_arrayMul_single]
  refine ((fderiv ℝ φ _).le_opNorm _).trans ?_
  calc ‖fderiv ℝ φ _‖ * ‖(fun m => M ω (ι m) i • v : Fin k → Fin r → ℂ)‖
      ≤ K₁ * (Real.sqrt (tau (fun m => M ω (ι m) i)) * ‖v‖) :=
        mul_le_mul (hS.bound1 _) (norm_colMap_le _ v) (norm_nonneg _) hS.nonneg1
    _ = K₁ * ‖v‖ * Real.sqrt (tau (fun m => M ω (ι m) i)) := by ring

/-- **The Ornstein–Uhlenbeck floor error of a tested backward function**:
`|floorError| ≤ Σ_i |β̂_i - β_i| (½K₁‖z_i‖ ∫√τ_i + ½ r K₂ ∫τ_i)`. -/
theorem floorError_backward_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂) (bh b : Fin N → ℝ) (z : Fin N → Fin r → ℂ) :
    |floorError bh b
        (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P) z)
        (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)) z) z| ≤
      ∑ i, |bh i - b i| * (1 / 2 * K₁ * ‖z i‖ * ∫ ω, Real.sqrt (tau (fun m => M ω (ι m) i)) ∂P +
        1 / 2 * r * K₂ * ∫ ω, tau (fun m => M ω (ι m) i) ∂P) := by
  unfold floorError
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 := abs_fderiv_backward_single_le ι hS z i (z i)
  have h2 := abs_hqTrace_backward_le ι hS z i
  calc _ ≤ |1 / 2 * fderiv ℝ (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P) z
        (single i (z i))| + |1 / 4 * hqTrace (fderiv ℝ (fderiv ℝ (fun z => ∫ ω, φ (testProj ι
          (arrayMul (M ω) z + Ξ ω)) ∂P)) z) i| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        nlinarith

end Backward

/-- `Σ_i τ_i ≤ k` when every row of `M` has Euclidean norm `≤ 1` (the sum of the squared
Hilbert–Schmidt norms of the `T_i` is at most the tested dimension). -/
theorem sum_tau_le (ι : Fin k → Fin N) {M : Matrix (Fin N) (Fin N) ℂ}
    (hrow : ∀ a, ∑ b, ‖M a b‖ ^ 2 ≤ 1) : ∑ i, tau (fun m => M (ι m) i) ≤ k := by
  unfold tau
  rw [Finset.sum_comm]
  calc ∑ m, ∑ i, ‖M (ι m) i‖ ^ 2 ≤ ∑ _m : Fin k, (1 : ℝ) := Finset.sum_le_sum fun m _ => hrow _
    _ = k := by simp

/-- A row of an `l²` contraction has Euclidean norm `≤ 1`. -/
theorem row_sq_le_of_contraction {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : ∀ v : Fin N → ℂ, l2Norm (M *ᵥ v) ≤ l2Norm v) (a : Fin N) :
    ∑ b, ‖M a b‖ ^ 2 ≤ 1 := by
  set v : Fin N → ℂ := fun b => starRingEnd ℂ (M a b) with hv
  set S := ∑ b, ‖M a b‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hva : (M *ᵥ v) a = (S : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, hv, hS, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.mul_conj']
  have hlv : l2Norm v = Real.sqrt S := by
    unfold l2Norm; congr 1; refine Finset.sum_congr rfl fun b _ => ?_; simp [hv]
  have hge : S ≤ l2Norm (M *ᵥ v) := by
    unfold l2Norm
    refine Real.le_sqrt_of_sq_le ?_
    calc S ^ 2 = ‖(M *ᵥ v) a‖ ^ 2 := by rw [hva, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ b, ‖(M *ᵥ v) b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖(M *ᵥ v) b‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ a)
  have h := hge.trans ((hM v).trans (le_of_eq hlv))
  by_contra hc
  push Not at hc
  have hsq : Real.sqrt S < S := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  linarith

/-- Entries of a row-contraction are bounded by `1`. -/
theorem entry_le_of_row {M : Matrix (Fin N) (Fin N) ℂ} (hrow : ∀ a, ∑ b, ‖M a b‖ ^ 2 ≤ 1)
    (a b : Fin N) : ‖M a b‖ ≤ 1 := by
  have h := (Finset.single_le_sum (f := fun b => ‖M a b‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ b)).trans (hrow a)
  have h0 := norm_nonneg (M a b)
  nlinarith

end BlockBand.Critical.RelativeVectors
