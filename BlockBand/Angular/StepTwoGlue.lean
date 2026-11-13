module

public import BlockBand.Angular.FirstMoment
public import BlockBand.Angular.DetFactor

/-!
# The angular first moment on the good domain with the concrete density

* `norm_physicalCoareaF_le` — **the deterministic norm bound on the good domain**: for Hermitian `H_R` with `dist(E, Spec H_R) ≥ W^{-M₀}` (every eigenvalue
  `λ_k` of `H_R` has `|λ_k - E| ≥ W^{-M₀}`) and `‖V‖ ≤ n_V`, `‖C‖ ≤ n_C`, `n_V + n_C ≤ W`
  (operator norms for the Euclidean `l2Norm`), `‖F(E)‖ ≤ W + W^{M₀+2}` for
  `F(E) = V - Cᴴ(H_R - E)⁻¹C = physicalCoareaF`. Any `W > 0`, `M₀ ∈ ℝ`.
  Also `det(H_R - E) ≠ 0` (`det_sub_ne_zero_of_dist`).
* `normBound_pairToFin_of_goodDomain` — the `NormBound (pairToFin F(E)) (M₀+3)` hypothesis of
  `center_angular_first_moment`, from the good-domain conditions (`M₀ ≥ 0`; `W ≥ 1` holds for
  every `Parameters`).
* `stepOneDensity` — the concrete angular density `Zf = c_{2W,t}(n/2) 𝔷_E`
  (`𝔷_E = pairAngularDensity`), and `ae_stepOneDensity` — it satisfies the `ν_{2W}`-a.e.
  hypothesis on `Zf` of `pair_angular_first_moment` / `center_angular_first_moment`
  (via `detFactor_eq_ofReal` and `ae_projectiveHaar_unit`).
* `center_angular_first_moment_goodDomain` — `center_angular_first_moment` with this concrete
  `Zf` and `A = M₀ + 3`, with the norm clause replaced by the good-domain conditions (and the
  nonpole clause `det(H_R - E) ≠ 0` derived from them); no abstract `Zf` or `NormBound`
  hypothesis remains.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.StepTwoGlue

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.QUE.Fourier BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Stein BlockBand.Angular.ConeDivergence
open BlockBand.Angular.FiberAngular BlockBand.Angular.Stein.AngularData
open BlockBand.Angular.PairCoareaBridge BlockBand.Model
open BlockBand.Angular.FirstMoment BlockBand.Angular.DetFactor
open scoped ENNReal NNReal ComplexConjugate

/-!
## Euclidean operator norms
-/

section OpNorm

open scoped Matrix.Norms.L2Operator

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem l2Norm_eq_euclidean (x : n → ℂ) :
    l2Norm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem l2Norm_mulVec_le_opNorm (A : Matrix m n ℂ) (x : n → ℂ) :
    l2Norm (A *ᵥ x) ≤ ‖A‖ * l2Norm x := by
  rw [l2Norm_eq_euclidean, l2Norm_eq_euclidean]
  exact A.l2_opNorm_mulVec (WithLp.toLp 2 x)

theorem opNorm_le_of_l2 {A : Matrix m n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, l2Norm (A *ᵥ x) ≤ c * l2Norm x) : ‖A‖ ≤ c := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have hx := h (WithLp.ofLp x)
  rw [l2Norm_eq_euclidean, l2Norm_eq_euclidean] at hx
  exact hx

theorem opNorm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
  opNorm_le_of_l2 zero_le_one fun x => by rw [one_mulVec, one_mul]

theorem opNorm_unitary_le {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  have h1 : Uᴴ * U = 1 := hU.1
  have h2 := l2_opNorm_conjTranspose_mul_self U
  rw [h1] at h2
  nlinarith [opNorm_one_le (n := n), norm_nonneg U]

/-- The explicit resolvent of a Hermitian matrix off its spectrum:
`(H - E)⁻¹ = U diag((λ_k - E)⁻¹) Uᴴ`, `U` the eigenvector unitary; right inverse form. -/
theorem sub_mul_resolventDiag {H : Matrix n n ℂ} (hH : H.IsHermitian) {E : ℝ}
    (hE : ∀ k, hH.eigenvalues k ≠ E) :
    (H - (E : ℂ) • 1) * ((hH.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun k => (((hH.eigenvalues k : ℂ) - E))⁻¹) *
      star (hH.eigenvectorUnitary : Matrix n n ℂ)) = 1 := by
  set U : Matrix n n ℂ := ↑hH.eigenvectorUnitary
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hUU' : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hspec : H = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hsub : H - (E : ℂ) • 1 = U * diagonal (fun k => (hH.eigenvalues k : ℂ) - E) * star U := by
    have h1 : (E : ℂ) • (1 : Matrix n n ℂ) = U * diagonal (fun _ => (E : ℂ)) * star U := by
      rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU]
    conv_lhs => rw [hspec, h1]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    rfl
  have hd : diagonal (fun k => (hH.eigenvalues k : ℂ) - E) *
      diagonal (fun k => (((hH.eigenvalues k : ℂ) - E))⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    have : (hH.eigenvalues k : ℂ) - E ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hE k
    exact mul_inv_cancel₀ this
  rw [hsub]
  calc U * diagonal (fun k => (hH.eigenvalues k : ℂ) - E) * star U *
        (U * diagonal (fun k => (((hH.eigenvalues k : ℂ) - E))⁻¹) * star U)
      = U * (diagonal (fun k => (hH.eigenvalues k : ℂ) - E) * (star U * U) *
          diagonal (fun k => (((hH.eigenvalues k : ℂ) - E))⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hUU', Matrix.mul_one, hd, Matrix.mul_one, hUU]

/-- `dist(E, Spec H) ≥ δ > 0` gives `det(H - E) ≠ 0`. -/
theorem det_sub_ne_zero_of_dist {H : Matrix n n ℂ} (hH : H.IsHermitian) {E δ : ℝ}
    (hδ : 0 < δ) (hdist : ∀ k, δ ≤ |hH.eigenvalues k - E|) : (H - (E : ℂ) • 1).det ≠ 0 := by
  have hE : ∀ k, hH.eigenvalues k ≠ E := fun k h => by
    have := hdist k; rw [h, sub_self, abs_zero] at this; linarith
  exact Matrix.det_ne_zero_of_right_inverse (sub_mul_resolventDiag hH hE)

/-- `dist(E, Spec H) ≥ δ > 0` gives `‖(H - E)⁻¹‖ ≤ δ⁻¹`. -/
theorem opNorm_resolvent_le {H : Matrix n n ℂ} (hH : H.IsHermitian) {E δ : ℝ} (hδ : 0 < δ)
    (hdist : ∀ k, δ ≤ |hH.eigenvalues k - E|) :
    ‖physicalCoareaResolvent H E‖ ≤ δ⁻¹ := by
  have hE : ∀ k, hH.eigenvalues k ≠ E := fun k h => by
    have := hdist k; rw [h, sub_self, abs_zero] at this; linarith
  unfold physicalCoareaResolvent
  rw [Matrix.inv_eq_right_inv (sub_mul_resolventDiag hH hE)]
  set U : Matrix n n ℂ := ↑hH.eigenvectorUnitary
  have hU : ‖U‖ ≤ 1 := opNorm_unitary_le hH.eigenvectorUnitary.2
  have hUs : ‖star U‖ ≤ 1 := by
    rw [star_eq_conjTranspose, l2_opNorm_conjTranspose]; exact hU
  have hD : ‖diagonal (fun k => (((hH.eigenvalues k : ℂ) - E))⁻¹)‖ ≤ δ⁻¹ := by
    rw [l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hδ.le)).2 fun k => ?_
    rw [norm_inv, show (hH.eigenvalues k : ℂ) - E = ((hH.eigenvalues k - E : ℝ) : ℂ) by
      push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    exact inv_anti₀ hδ (hdist k)
  calc ‖U * diagonal (fun k => (((hH.eigenvalues k : ℂ) - E))⁻¹) * star U‖
      ≤ ‖U‖ * ‖diagonal (fun k => (((hH.eigenvalues k : ℂ) - E))⁻¹)‖ * ‖star U‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ 1 * δ⁻¹ * 1 := by
        gcongr
    _ = δ⁻¹ := by ring

/-- **The deterministic norm bound on the good domain**. For Hermitian
`H_R` with `dist(E, Spec H_R) ≥ W^{-M₀}` (each eigenvalue `λ_k` of `H_R` has
`|λ_k - E| ≥ W^{-M₀}`), `‖V‖ ≤ n_V`, `‖C‖ ≤ n_C` and `n_V + n_C ≤ W` (Euclidean operator
norms, stated as `l2Norm` bounds), the Schur complement `F(E) = V - Cᴴ(H_R - E)⁻¹C` satisfies
`‖F(E)x‖ ≤ (W + W^{M₀+2})‖x‖`. Any `W > 0` and `M₀ ∈ ℝ`; any finite index types. -/
theorem norm_physicalCoareaF_le {H_R : Matrix m m ℂ} (hH : H_R.IsHermitian) (C : Matrix m n ℂ)
    (V : Matrix n n ℂ) (E : ℝ) {W M₀ nV nC : ℝ} (hW : 0 < W)
    (hdist : ∀ k, W ^ (-M₀) ≤ |hH.eigenvalues k - E|)
    (hnV : 0 ≤ nV) (hnC : 0 ≤ nC) (hsum : nV + nC ≤ W)
    (hV : ∀ x, l2Norm (V *ᵥ x) ≤ nV * l2Norm x) (hC : ∀ x, l2Norm (C *ᵥ x) ≤ nC * l2Norm x)
    (x : n → ℂ) :
    l2Norm (physicalCoareaF H_R C V E *ᵥ x) ≤ (W + W ^ (M₀ + 2)) * l2Norm x := by
  refine (l2Norm_mulVec_le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have hδ : 0 < W ^ (-M₀) := Real.rpow_pos_of_pos hW _
  have hR := opNorm_resolvent_le hH hδ hdist
  rw [Real.rpow_neg hW.le, inv_inv] at hR
  have hVn : ‖V‖ ≤ nV := opNorm_le_of_l2 hnV hV
  have hCn : ‖C‖ ≤ nC := opNorm_le_of_l2 hnC hC
  have hCh : ‖Cᴴ‖ ≤ nC := by rw [l2_opNorm_conjTranspose]; exact hCn
  have hpow : W ^ (M₀ + 2) = W ^ M₀ * (W * W) := by
    rw [Real.rpow_add hW, Real.rpow_two, sq]
  have hRn : 0 ≤ ‖physicalCoareaResolvent H_R E‖ := norm_nonneg _
  have hprod : ‖Cᴴ * physicalCoareaResolvent H_R E * C‖ ≤ nC * W ^ M₀ * nC :=
    calc ‖Cᴴ * physicalCoareaResolvent H_R E * C‖
        ≤ ‖Cᴴ‖ * ‖physicalCoareaResolvent H_R E‖ * ‖C‖ :=
          (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ ≤ nC * W ^ M₀ * nC := by gcongr
  have hWM : 0 ≤ W ^ M₀ := Real.rpow_nonneg hW.le _
  have hnC2 : nC * nC ≤ W * W := mul_le_mul (by linarith) (by linarith) hnC hW.le
  calc ‖physicalCoareaF H_R C V E‖ ≤ ‖V‖ + ‖Cᴴ * physicalCoareaResolvent H_R E * C‖ :=
        norm_sub_le _ _
    _ ≤ nV + nC * W ^ M₀ * nC := add_le_add hVn hprod
    _ ≤ W + W ^ (M₀ + 2) := by
        rw [hpow]
        nlinarith [mul_le_mul_of_nonneg_left hnC2 hWM]

end OpNorm

/-!
## The polynomial deformation domain on the pair
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- **The norm clause of `FreshClass` on the good domain**: for Hermitian
`H_R`, `dist(E, Spec H_R) ≥ W^{-M₀}`, `‖V‖ ≤ n_V`, `‖C‖ ≤ n_C`, `n_V + n_C ≤ W` and
`M₀ ≥ 0`, `NormBound (pairToFin F(E)) (M₀ + 3)`, i.e. `‖F(E)‖ ≤ (2W)^{M₀+3}`. -/
theorem normBound_pairToFin_of_goodDomain (ω : SplitState p i) (hH : ω.1.IsHermitian)
    (E : ℝ) {M₀ nV nC : ℝ} (hM₀ : 0 ≤ M₀)
    (hdist : ∀ k, (p.W : ℝ) ^ (-M₀) ≤ |hH.eigenvalues k - E|)
    (hnV : 0 ≤ nV) (hnC : 0 ≤ nC) (hsum : nV + nC ≤ p.W)
    (hV : ∀ x, l2Norm (ω.2.2 *ᵥ x) ≤ nV * l2Norm x)
    (hC : ∀ x, l2Norm (ω.2.1 *ᵥ x) ≤ nC * l2Norm x) :
    NormBound (pairToFin (physicalCoareaF ω.1 ω.2.1 ω.2.2 E)) (M₀ + 3) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact normBound_pairToFin p i hM₀
    (norm_physicalCoareaF_le hH ω.2.1 ω.2.2 E hW hdist hnV hnC hsum hV hC)

/-- **The concrete angular density** `Zf(v) = c_{2W,t}(n/2) 𝔷_E(v)`, `t = s/(2W)`
(`𝔷_E = pairAngularDensity`, the coarea determinant factor of `detFactor_eq_ofReal`). -/
def stepOneDensity (α : Fin p.N) (s : ℝ) (ω : SplitState p i) (E : ℝ)
    (v : PairSite p i → ℂ) : ℝ :=
  coareaConstant (2 * p.W) (pairTime p s) * ((p.n : ℝ) / 2) * pairAngularDensity p i α s ω E v

variable {p i}

theorem measurable_stepOneDensity (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) :
    Measurable (stepOneDensity p i α s ω E) :=
  measurable_const.mul (measurable_pairAngularDensity α s hR hV E)

theorem stepOneDensity_nonneg (α : Fin p.N) (s : ℝ) {ω : SplitState p i}
    (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) (v : PairSite p i → ℂ) :
    0 ≤ stepOneDensity p i α s ω E v :=
  mul_nonneg (mul_nonneg (coareaConstant_nonneg _ _) (by positivity))
    (pairAngularDensity_nonneg α s hR hV E v)

/-- **The concrete density satisfies the a.e. hypothesis on `Zf`** of
`pair_angular_first_moment` / `center_angular_first_moment` (the angular
measure, with its coarea constant, is exactly the eigenpair density): for every measurable
pair frame `U` and Hermitian `H_R`, `V`,
`ofReal(Zf v) = ofReal(c_{2W,t}(n/2)) · detFactor(v)` for `ν_{2W}`-a.e. `v`. -/
theorem ae_stepOneDensity (α : Fin p.N) (s : ℝ)
    {U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ} (hU : IsPairFrame p i U)
    {ω : SplitState p i} (hR : ω.1.IsHermitian) (hV : ω.2.2.IsHermitian) (E : ℝ) :
    ∀ᵐ v ∂projectiveHaar (PairSite p i), ENNReal.ofReal (stepOneDensity p i α s ω E v) =
      ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p s) * ((p.n : ℝ) / 2)) *
        detFactor p i α s U ω E v := by
  filter_upwards [ae_projectiveHaar_unit (ι := PairSite p i)] with v hv
  have hv1 : l2Norm v = 1 := by
    show Real.sqrt (normSqSum v) = 1
    rw [hv, Real.sqrt_one]
  rw [detFactor_eq_ofReal p i α s hU hR hV E hv1, stepOneDensity,
    ENNReal.ofReal_mul (mul_nonneg (coareaConstant_nonneg _ _) (by positivity))]

end Pair

/-!
## The first moment on the good regular center domain, with the concrete density
-/

/-- **Step 2 of the physical angular estimate on the good regular center domain**, with the
concrete Step 1 density and the good-domain conditions. With `CenterDomainContract.regular`,
`FreshPalmContract` and `FreshEigenpairDensityContract`: for `b, ϑ` and `M₀ ≥ 0` fixed, there
are `y₀ > 0`, `C_ζ`, `C₀ ≥ 1` and, for every `K > 0`, `C_K ≥ 0`, such that for every `ϑ`-bulk
rank `α`, pair `i`, Hermitian residual `H^{(e)}` and energy `E` in the regular center domain
with `dist(E, Spec H^{(e)}_R) ≥ W^{-M₀}` and `‖V‖ ≤ n_V`, `‖C‖ ≤ n_C`, `n_V + n_C ≤ W`
(`V`, `C` the pair and coupling blocks of `H^{(e)}`), the angular data
`D = (K_e(E), s, ζ_e)` exists and, for every measurable pair frame `U` and every `w`, the
Step 1 angular measure `e^{expo} Zf ν_{2W}`, `Zf = stepOneDensity = c_{2W,t}(n/2) 𝔷_E`, obeys
`∫ e^{expo}Zf|w*v|² dν ≤ C₀(∫ e^{expo}Zf dν + (n/2) C_K N^{-K})/N · Re(w*Γw)`, `N = 2W`.
This is `center_angular_first_moment` at `A = M₀ + 3`; the nonpole clause
`det(H^{(e)}_R - E) ≠ 0` follows from the distance condition. -/
theorem center_angular_first_moment_goodDomain (hP : FreshPalmContract)
    (hD : FreshEigenpairDensityContract) (cst : CenterDomainConstants)
    (hcd : CenterDomainContract cst) {b ϑ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hϑ0 : 0 < ϑ)
    (hϑ1 : ϑ < 1 / 2) {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∃ y₀ Cζ : ℝ, 0 < y₀ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ K : ℝ, 0 < K → ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ (p : Parameters), p.b = b → ∀ (α : Fin p.N), IsBulkRank p ϑ α →
      ∀ (i : ZMod p.n) (Hres : p.SiteMatrix) (hH : Hres.IsHermitian) (E : ℝ),
        InCenterDomain p i cst α Hres E →
        (∀ k, (p.W : ℝ) ^ (-M₀) ≤ |(exteriorBlock_isHermitian p i hH).eigenvalues k - E|) →
      ∀ nV nC : ℝ, 0 ≤ nV → 0 ≤ nC → nV + nC ≤ p.W →
        (∀ x, l2Norm (pairBlock p i Hres *ᵥ x) ≤ nV * l2Norm x) →
        (∀ x, l2Norm (couplingBlock p i Hres *ᵥ x) ≤ nC * l2Norm x) →
      ∃ D : AngularData (PairSite p i), D.K = edgeSchur p i Hres E ∧ D.s = splitS p ∧
        D.ζ = dysonRoot p i (cst.ρ₀ p.b (rankMargin p α)) Hres E ∧ y₀ ≤ D.ζ.im ∧
        ‖D.ζ‖ ≤ Cζ ∧
        ∀ U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ, IsPairFrame p i U →
        ∀ w : PairSite p i → ℂ,
          ∫ v, Real.exp (D.expo v) * stepOneDensity p i α (splitS p) (splitOf p i Hres) E v *
              ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar (PairSite p i) ≤
            C₀ * ((∫ v, Real.exp (D.expo v) *
                  stepOneDensity p i α (splitS p) (splitOf p i Hres) E v
                ∂projectiveHaar (PairSite p i)) +
                (p.n : ℝ) / 2 * CK * (Fintype.card (PairSite p i) : ℝ) ^ (-K)) /
              Fintype.card (PairSite p i) * (star w ⬝ᵥ (D.Γ *ᵥ w)).re := by
  obtain ⟨y₀, Cζ, hy₀, C₀, hC₀, hK⟩ :=
    center_angular_first_moment hP hD cst hcd hb0 hb1 hϑ0 hϑ1 (M₀ + 3)
  refine ⟨y₀, Cζ, hy₀, C₀, hC₀, fun K hK' => ?_⟩
  obtain ⟨CK, hCK, h⟩ := hK K hK'
  refine ⟨CK, hCK, ?_⟩
  intro p hpb α hα i Hres hH E hdom hdist nV nC hnV hnC hsum hVn hCn
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hdet : (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0 :=
    det_sub_ne_zero_of_dist (exteriorBlock_isHermitian p i hH) (Real.rpow_pos_of_pos hW _) hdist
  have hnorm : NormBound (pairToFin (edgeSchur p i Hres E + (E : ℂ) • 1)) (M₀ + 3) := by
    rw [edgeSchur, sub_add_cancel]
    exact normBound_pairToFin_of_goodDomain p i (splitOf p i Hres)
      (exteriorBlock_isHermitian p i hH) E hM₀ hdist hnV hnC hsum hVn hCn
  obtain ⟨D, hDK, hDs, hDζ, hy, hζC, hFM⟩ := h p hpb α hα i Hres hH E hdet hdom hnorm
  refine ⟨D, hDK, hDs, hDζ, hy, hζC, fun U hU w => ?_⟩
  have hR : (splitOf p i Hres).1.IsHermitian := exteriorBlock_isHermitian p i hH
  have hV : (splitOf p i Hres).2.2.IsHermitian := pairBlock_isHermitian p i hH
  exact hFM U hU _ (measurable_stepOneDensity α _ hR hV E) (stepOneDensity_nonneg α _ hR hV E)
    (ae_stepOneDensity α _ hU hR hV E) w

end BlockBand.Angular.StepTwoGlue
