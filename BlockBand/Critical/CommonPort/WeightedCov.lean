module

public import BlockBand.Critical.CommonPort.FluctBounds
public import BlockBand.Layers.TraceCovariance
public import BlockBand.Layers.MeanEquations

/-!
# Common-port mean: the weighted trace–matrix covariance

Law: `layerLaw W b .common` (fresh `A_a ~ GUE_W(c/W)`, bonds `Gin(b/W)`), realized as the image
of `gaussianProduct (tflVar W b .common)` under `tflEmbed`; every deterministic Hermitian `X`.
Norms: `ℓ²` operator norm; matrix expectations entrywise (`matrixExpect`, `meqCov`).

* `padTop`, `padTop_mul_eq`, `norm_padTop_mul_le`, `toBlocks11_mul_padTop_conj`: the padded
  weight `K̂`, `‖K̂𝒢‖ ≤ ‖K · topRows 𝒢‖`, `(N K̂ᴴ)₁₁ = N₁₁ Kᴴ`.
* `wcov_abstract`: OU covariance at a fixed regularization for `C¹` bounded `f, U` whose
  derivatives have the kernel form `W⁻¹ Tr(Σ aⱼ Λ cⱼ)`, `Σ a'ₖ Λ c'ₖ` with continuous bounded
  majorants `‖aⱼ‖‖cⱼ‖ ≤ Φ_f`, `‖a'ₖ‖‖c'ₖ‖ ≤ Φ_U`:
  `‖Cov(f, U)‖ ≤ (10 ℓ_f ℓ_U / W²)(E Φ_f² + E Φ_U²)`.
* `wcov_U_hasFDerivAt`, `wcov_reg`: the weighted word `U_κ = w_U(G_κ)(K̂G_κ)ᴴ` has derivative
  `Σₘ aₘ Λ (cₘ(K̂G_κ)ᴴ) - (w_U Gᴴ_κ) Λ (K̂G_κ)ᴴ`; with `f_κ = W⁻¹ Tr w_f(G_κ)`:
  `‖Cov(f_κ, U_κ)‖ ≤ (10 ℓ_f (ℓ_U+1)/W²)(E‖G_κ‖^{2ℓ_f+2} + E[‖G_κ‖^{2ℓ_U+2}‖K̂G_κ‖²])`
  (deterministic letters of norm `≤ 1`).
* `wcov_core`: `κ → 0` (dominated convergence) with the a.e. bounds `‖G_κ‖ ≤ 2Ψ`,
  `‖K̂G_κ‖ ≤ c₁(1+η₀⁻¹)Ψ⁴` (`reg_bounds`) and `E Ψ¹² ≤ M`.
* `cpPsi_twelve_le`: `E Ψ¹² ≤ M` from `GaussianAbsorptionContract` and the GUE/bond moments.
* **`weightedCov_holds`**: for `ℓ_f ≤ 2`, `ℓ_U ≤ 1`, letters of norm `≤ 1`:
  `‖Cov(W⁻¹ Tr w_f(𝒢), w_U(𝒢)(K̂𝒢)ᴴ)‖ ≤ C W⁻²`, uniformly in `W ≥ W₀`, Hermitian `X` and
  `e ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical BlockBand.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. The padded weight `K̂ = [[K, 0], [0, 0]]`
-/

section Pad

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The padded weight `K̂ = [[K, 0], [0, 0]]`. -/
def padTop (K : Matrix n n ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks K 0 0 0

/-- Deterministic: `K̂ G = Jᴴ (K · topRows G)`, `J = selectMatrix Sum.inl` (any `K`, `G`). -/
theorem padTop_mul_eq (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    padTop K * G = (selectMatrix (Sum.inl : n → n ⊕ m))ᴴ * (K * topRows G) := by
  ext p q
  rcases p with p | p
  · have hR : ((selectMatrix (Sum.inl : n → n ⊕ m))ᴴ * (K * topRows G)) (Sum.inl p) q =
        (K * topRows G) p q := by
      rw [Matrix.mul_apply, Finset.sum_eq_single p]
      · simp [conjTranspose_apply, selectMatrix]
      · intro c _ hc; simp [conjTranspose_apply, selectMatrix, Ne.symm hc]
      · simp
    rw [hR]
    simp [padTop, Matrix.mul_apply, Fintype.sum_sum_type, topRows]
  · simp [padTop, Matrix.mul_apply, Fintype.sum_sum_type, selectMatrix]

/-- `‖K̂ G‖ ≤ ‖K · topRows G‖`. -/
theorem norm_padTop_mul_le (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    ‖padTop K * G‖ ≤ ‖K * topRows G‖ := by
  rw [padTop_mul_eq]
  have h1 := norm_le_one_of_mul_conjTranspose _
    (selectMatrix_mul_conjTranspose (Sum.inl_injective : Function.Injective (Sum.inl : n → n ⊕ m)))
  refine (l2_opNorm_mul _ _).trans ?_
  rw [l2_opNorm_conjTranspose]
  calc ‖selectMatrix (Sum.inl : n → n ⊕ m)‖ * ‖K * topRows G‖ ≤ 1 * ‖K * topRows G‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

omit [DecidableEq n] [DecidableEq m] in
/-- `(N K̂ᴴ)₁₁ = N₁₁ Kᴴ`. -/
theorem toBlocks11_mul_padTop_conj (N : Matrix (n ⊕ m) (n ⊕ m) ℂ) (K : Matrix n n ℂ) :
    (N * (padTop (m := m) K)ᴴ).toBlocks₁₁ = N.toBlocks₁₁ * Kᴴ := by
  ext p q
  simp [padTop, toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_conjTranspose]

end Pad

/-!
## 2. The OU covariance with kernel majorants, at a fixed regularization
-/

section Abstract

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- **OU covariance bound with kernel majorants** (the scheme of
`tcv_cov_reg`). Real Gaussian coordinates `μ = gaussianProduct (tflVar W b σ)`; `W ≥ 1`,
`0 < b < 1/2`. For `C¹` bounded `f : ℝ^ι → ℂ`, `U : ℝ^ι → Mat` with bounded derivatives, such
that at every `x` the derivatives have the kernel form
`df(x)v = W⁻¹ Tr(Σⱼ aⱼ (Λv) cⱼ)`, `dU(x)v = Σₖ a'ₖ (Λv) c'ₖ` (`Λ = tflLin`) with
`‖aⱼ‖‖cⱼ‖ ≤ Φ_f(x)`, `‖a'ₖ‖‖c'ₖ‖ ≤ Φ_U(x)` for continuous nonnegative bounded `Φ_f, Φ_U`:
`‖E[f U] - E f E U‖ ≤ (10 ℓ_f ℓ_U / W²)(E Φ_f² + E Φ_U²)` (operator norm). -/
theorem wcov_abstract (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) {ℓf ℓU : ℕ}
    {f : (TflCoord W σ → ℝ) → ℂ}
    {U : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hfd : ContDiff ℝ 1 f) (hUd : ContDiff ℝ 1 U) {Cf Cf' CU CU' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf')
    (hUC : ∀ x, ‖U x‖ ≤ CU) (hU'C : ∀ x, ‖fderiv ℝ U x‖ ≤ CU')
    {Φf ΦU : (TflCoord W σ → ℝ) → ℝ} (hΦfc : Continuous Φf) (hΦUc : Continuous ΦU)
    (hΦf0 : ∀ x, 0 ≤ Φf x) (hΦU0 : ∀ x, 0 ≤ ΦU x) {Bf BU : ℝ} (hΦfB : ∀ x, Φf x ≤ Bf)
    (hΦUB : ∀ x, ΦU x ≤ BU)
    (hf' : ∀ x, ∃ a c : Fin ℓf → Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      (∀ v, fderiv ℝ f x v = (W : ℂ)⁻¹ * (∑ j, a j * tflLin W b σ v * c j).trace) ∧
        ∀ j, ‖a j‖ * ‖c j‖ ≤ Φf x)
    (hU' : ∀ x, ∃ a c : Fin ℓU → Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      (∀ v, fderiv ℝ U x v = ∑ k, a k * tflLin W b σ v * c k) ∧
        ∀ k, ‖a k‖ * ‖c k‖ ≤ ΦU x) :
    ‖(∫ x, f x • U x ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, f x ∂gaussianProduct (tflVar W b σ)) • (∫ x, U x ∂gaussianProduct (tflVar W b σ))‖ ≤
      10 * ℓf * ℓU / (W : ℝ) ^ 2 *
        ((∫ x, Φf x ^ 2 ∂gaussianProduct (tflVar W b σ)) +
          ∫ x, ΦU x ^ 2 ∂gaussianProduct (tflVar W b σ)) := by
  set v := tflVar W b σ with hv
  set μ := gaussianProduct v with hμ
  set c₀ : ℝ := 10 * ℓf * ℓU / (W : ℝ) ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hker : ∀ x y : TflCoord W σ → ℝ,
      ‖∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f x (Pi.single i 1)) • fderiv ℝ U y (Pi.single i 1)‖ ≤
        c₀ * (Φf x ^ 2 + ΦU y ^ 2) := by
    intro x y
    obtain ⟨a, c, hfv, hac⟩ := hf' x
    obtain ⟨a', c', hUv, hac'⟩ := hU' y
    simp_rw [hfv, hUv]
    rw [tcv_kernel_eq]
    refine (tcv_kernel_le σ hW hb0 hb1 a c a' c' (hΦf0 x) hac hac').trans ?_
    have hxy : Φf x * ΦU y ≤ Φf x ^ 2 + ΦU y ^ 2 := by
      nlinarith [hΦf0 x, hΦU0 y, sq_nonneg (Φf x - ΦU y)]
    calc 10 * ℓf * ℓU * Φf x * ΦU y / (W : ℝ) ^ 2 = c₀ * (Φf x * ΦU y) := by
          rw [hc₀]; ring
      _ ≤ c₀ * (Φf x ^ 2 + ΦU y ^ 2) := mul_le_mul_of_nonneg_left hxy hc₀0
  set If : ℝ := ∫ x, Φf x ^ 2 ∂μ with hIf
  set IU : ℝ := ∫ x, ΦU x ^ 2 ∂μ with hIU
  have hpf : Continuous (fun x => Φf x ^ 2) := hΦfc.pow 2
  have hpU : Continuous (fun x => ΦU x ^ 2) := hΦUc.pow 2
  have hkt : ∀ t : ℝ, 0 < t →
      ‖∫ p, ∑ i, (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ U (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂μ.prod μ‖ ≤ c₀ * (If + IU) := by
    intro t ht
    set y : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) → (TflCoord W σ → ℝ) :=
      fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2 with hy
    have hyc : Continuous y := by fun_prop
    have hA : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => Φf p.1 ^ 2)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpf.comp continuous_fst) (C := Bf ^ 2) fun p => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (hΦf0 _) (hΦfB _) 2
    have hB : Integrable (fun p : (TflCoord W σ → ℝ) × (TflCoord W σ → ℝ) => ΦU (y p) ^ 2)
        (μ.prod μ) :=
      ou_integrable_bdd v (hpU.comp hyc) (C := BU ^ 2) fun p => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (hΦU0 _) (hΦUB _) 2
    have hbd := norm_integral_le_of_norm_le ((hA.add hB).const_mul c₀)
      (Eventually.of_forall fun p => hker p.1 (y p))
    refine hbd.trans (le_of_eq ?_)
    rw [integral_const_mul]
    simp only [Pi.add_apply]
    rw [integral_add hA hB, integral_fun_fst (fun x => Φf x ^ 2),
      probReal_univ, one_smul, tcv_integral_interp v hpU ht.le]
  rw [ou_covariance_matrix v hfd hfC hf'C hUd hUC hU'C]
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) * (c₀ * (If + IU))) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  refine (norm_integral_le_of_norm_le hexp ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hkt t ht) (Real.exp_pos _).le
  · rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

end Abstract

/-!
## 3. Weighted words at a fixed regularization
-/

section FixedKappa

variable {W : ℕ} {b : ℝ} {σ : LayerShape} {E : ℝ} {z : ℂ}
  {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}

/-- **Derivative of a weighted word** `U(y) = w(G_κ(y)) (K̂ G_κ(y))ᴴ` (letters of norm `≤ 1`,
any deterministic weight `K̂`): `dU(v) = Σₖ aₖ (Λv) cₖ` with `ℓ + 1` terms and
`‖aₖ‖ ‖cₖ‖ ≤ ‖G_κ‖^{ℓ+1} ‖K̂ G_κ‖`. -/
theorem wcov_U_hasFDerivAt (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (x : TflCoord W σ → ℝ) {ℓ : ℕ}
    (ε : Fin ℓ → Bool) (D : Fin (ℓ + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hD : ∀ j, ‖D j‖ ≤ 1) :
    ∃ T : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      HasFDerivAt (fun y => wordEval ε D (tcvG W b σ E z X κ y) *
        (Kh * tcvG W b σ E z X κ y)ᴴ) T x ∧
      ∃ a c : Fin (ℓ + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
        (∀ v, T v = ∑ k, a k * tcvLam W b σ v * c k) ∧
        ∀ k, ‖a k‖ * ‖c k‖ ≤
          ‖tcvG W b σ E z X κ x‖ ^ (ℓ + 1) * ‖Kh * tcvG W b σ E z X κ x‖ := by
  set G := tcvG W b σ E z X κ with hGdef
  have hΛh : ∀ v', (tcvLam W b σ v')ᴴ = tcvLam W b σ v' := tcv_lin_herm W b σ
  have hderG := tcv_G_hasFDerivAt W b σ E z hX hz hκ
  obtain ⟨TV, hTV, a, c, hTVv, hac⟩ := tcv_word_hasFDerivAt hΛh hderG zero_le_one x ε D hD
  obtain ⟨TG, hTG, hTGv⟩ := hderG x
  have hH : HasFDerivAt (fun y => (Kh * G y)ᴴ) (tcvConjCLM.comp (Kh • TG)) x :=
    (tcvConjCLM (n := LayerSite W σ)).hasFDerivAt.comp x (hTG.const_mul Kh)
  have h2 := hTV.mul' hH
  set V := wordEval ε D (G x) with hV
  set H := Kh * G x with hHdef
  have hVn : ‖V‖ ≤ ‖G x‖ ^ ℓ := by
    have := tcv_norm_wordEval_le zero_le_one ε D (G x) hD
    simpa using this
  refine ⟨_, h2, Fin.cons (-(V * (G x)ᴴ)) a, Fin.cons Hᴴ (fun m => c m * Hᴴ), fun v => ?_,
    fun k => ?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, _root_.add_apply,
      _root_.smul_apply, ContinuousLinearMap.comp_apply, tcvConjCLM_apply, hTGv,
      hTVv]
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, smul_eq_mul]
    have e1 : (Kh * -(G x * tcvLam W b σ v * G x))ᴴ =
        -((G x)ᴴ * tcvLam W b σ v * Hᴴ) := by
      rw [hHdef, conjTranspose_mul, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul,
        conjTranspose_mul, hΛh]
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [e1, Finset.sum_mul]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · have hG0 := norm_nonneg (G x)
    have hH0 := norm_nonneg H
    refine Fin.cases ?_ (fun m => ?_) k
    · simp only [Fin.cons_zero, norm_neg, l2_opNorm_conjTranspose]
      calc ‖V * (G x)ᴴ‖ * ‖H‖ ≤ (‖V‖ * ‖G x‖) * ‖H‖ := by
            gcongr
            exact (l2_opNorm_mul _ _).trans (le_of_eq (by rw [l2_opNorm_conjTranspose]))
        _ ≤ (‖G x‖ ^ ℓ * ‖G x‖) * ‖H‖ := by gcongr
        _ = ‖G x‖ ^ (ℓ + 1) * ‖H‖ := by ring
    · simp only [Fin.cons_succ]
      have h := hac m
      rw [one_pow, one_mul] at h
      calc ‖a m‖ * ‖c m * Hᴴ‖ ≤ ‖a m‖ * (‖c m‖ * ‖H‖) := by
            gcongr
            exact (l2_opNorm_mul _ _).trans (le_of_eq (by rw [l2_opNorm_conjTranspose]))
        _ = (‖a m‖ * ‖c m‖) * ‖H‖ := by ring
        _ ≤ ‖G x‖ ^ (ℓ + 1) * ‖H‖ := by gcongr

/-- **Weighted covariance at a fixed regularization** (real coordinates,
`μ = gaussianProduct (tflVar W b σ)`). `W ≥ 1`, `0 < b < 1/2`, Hermitian `X`, `Im z ≥ 0`,
`κ > 0`, any deterministic weight `K̂`, words with letters of norm `≤ 1`. With
`f_κ = W⁻¹ Tr w_f(G_κ)` and `U_κ = w_U(G_κ) (K̂ G_κ)ᴴ`:
`‖E[f_κ U_κ] - E f_κ E U_κ‖ ≤ (10 ℓ_f (ℓ_U + 1) / W²)
  (E ‖G_κ‖^{2(ℓ_f+1)} + E[(‖G_κ‖^{ℓ_U+1} ‖K̂ G_κ‖)²])`. -/
theorem wcov_reg (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) (Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    {ℓf ℓU : ℕ}
    (εf : Fin ℓf → Bool) (Df : Fin (ℓf + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (εU : Fin ℓU → Bool) (DU : Fin (ℓU + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hDf : ∀ j, ‖Df j‖ ≤ 1) (hDU : ∀ j, ‖DU j‖ ≤ 1) :
    ‖(∫ x, tcvTr W σ (wordEval εf Df (tcvG W b σ E z X κ x)) •
          (wordEval εU DU (tcvG W b σ E z X κ x) * (Kh * tcvG W b σ E z X κ x)ᴴ)
          ∂gaussianProduct (tflVar W b σ)) -
        (∫ x, tcvTr W σ (wordEval εf Df (tcvG W b σ E z X κ x)) ∂gaussianProduct (tflVar W b σ)) •
          (∫ x, wordEval εU DU (tcvG W b σ E z X κ x) * (Kh * tcvG W b σ E z X κ x)ᴴ
            ∂gaussianProduct (tflVar W b σ))‖ ≤
      10 * ℓf * (ℓU + 1 : ℕ) / (W : ℝ) ^ 2 *
        ((∫ x, (‖tcvG W b σ E z X κ x‖ ^ (ℓf + 1)) ^ 2 ∂gaussianProduct (tflVar W b σ)) +
          ∫ x, (‖tcvG W b σ E z X κ x‖ ^ (ℓU + 1) * ‖Kh * tcvG W b σ E z X κ x‖) ^ 2
            ∂gaussianProduct (tflVar W b σ)) := by
  set G := tcvG W b σ E z X κ with hGdef
  set Λ := tcvLam W b σ with hΛdef
  have hGc : ContDiff ℝ 1 G := tcv_G_contDiff W b σ E z hX hz hκ
  have hGcont : Continuous G := hGc.continuous
  have hGle : ∀ x, ‖G x‖ ≤ κ⁻¹ := tcv_G_le W b σ E z hX hz hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hderG := tcv_G_hasFDerivAt W b σ E z hX hz hκ
  have hΛh : ∀ v', (Λ v')ᴴ = Λ v' := tcv_lin_herm W b σ
  have hpowle : ∀ (m : ℕ) x, ‖G x‖ ^ m ≤ κ⁻¹ ^ m := fun m x =>
    pow_le_pow_left₀ (norm_nonneg _) (hGle x) m
  have hHle : ∀ x, ‖Kh * G x‖ ≤ ‖Kh‖ * κ⁻¹ := fun x =>
    (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left (hGle x) (norm_nonneg _))
  set f : (TflCoord W σ → ℝ) → ℂ := fun x => tcvTr W σ (wordEval εf Df (G x)) with hfdef
  set U : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => wordEval εU DU (G x) * (Kh * G x)ᴴ with hUdef
  have hfd : ContDiff ℝ 1 f := (tcvTr W σ).contDiff.comp (tcv_contDiff_word hGc εf Df)
  have hUd : ContDiff ℝ 1 U :=
    (tcv_contDiff_word hGc εU DU).mul
      ((tcvConjCLM (n := LayerSite W σ)).contDiff.comp (contDiff_const.mul hGc))
  have hwle : ∀ {ℓ : ℕ} (ε : Fin ℓ → Bool) (D : Fin (ℓ + 1) → Matrix (LayerSite W σ)
      (LayerSite W σ) ℂ), (∀ j, ‖D j‖ ≤ 1) → ∀ x, ‖wordEval ε D (G x)‖ ≤ κ⁻¹ ^ ℓ := by
    intro ℓ ε D hD x
    have := tcv_norm_wordEval_le zero_le_one ε D (G x) hD
    rw [one_pow, one_mul] at this
    exact this.trans (hpowle ℓ x)
  have hfC : ∀ x, ‖f x‖ ≤ 4 * κ⁻¹ ^ ℓf := fun x =>
    (tcv_tr_le σ hW _).trans (by gcongr; exact hwle εf Df hDf x)
  have hUC : ∀ x, ‖U x‖ ≤ κ⁻¹ ^ ℓU * (‖Kh‖ * κ⁻¹) := fun x => by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    exact mul_le_mul (hwle εU DU hDU x) (hHle x) (norm_nonneg _) (by positivity)
  have hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ ‖tcvTr W σ‖ * (ℓf * (1 ^ (ℓf + 1) * κ⁻¹ ^ (ℓf + 1)) * ‖Λ‖) :=
    fun x => by
    obtain ⟨T, hT, a, c, hTv, hac⟩ := tcv_word_hasFDerivAt hΛh hderG zero_le_one x εf Df hDf
    have hfx : HasFDerivAt f ((tcvTr W σ).comp T) x := (tcvTr W σ).hasFDerivAt.comp x hT
    rw [hfx.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    gcongr
    exact tcv_clm_norm_le hTv (by positivity) fun m =>
      (hac m).trans (by gcongr; exact hGle x)
  have hU'C : ∀ x, ‖fderiv ℝ U x‖ ≤
      (ℓU + 1 : ℕ) * (κ⁻¹ ^ (ℓU + 1) * (‖Kh‖ * κ⁻¹)) * ‖Λ‖ := fun x => by
    obtain ⟨T, hT, a, c, hTv, hac⟩ := wcov_U_hasFDerivAt hX hz hκ Kh x εU DU hDU
    rw [hT.fderiv]
    exact tcv_clm_norm_le hTv (by positivity) fun m =>
      (hac m).trans (mul_le_mul (hpowle _ x) (hHle x) (norm_nonneg _) (by positivity))
  have hΦfc : Continuous (fun x => ‖G x‖ ^ (ℓf + 1)) := (continuous_norm.comp hGcont).pow _
  have hΦUc : Continuous (fun x => ‖G x‖ ^ (ℓU + 1) * ‖Kh * G x‖) :=
    ((continuous_norm.comp hGcont).pow _).mul
      (continuous_norm.comp (continuous_const.mul hGcont))
  refine wcov_abstract hW hb0 hb1 hfd hUd hfC hf'C hUC hU'C hΦfc hΦUc
    (fun x => by positivity) (fun x => by positivity) (fun x => hpowle _ x)
    (fun x => mul_le_mul (hpowle _ x) (hHle x) (norm_nonneg _) (by positivity))
    (fun x => ?_) (fun x => ?_)
  · obtain ⟨T, hT, a, c, hTv, hac⟩ := tcv_word_hasFDerivAt hΛh hderG zero_le_one x εf Df hDf
    have hfx : HasFDerivAt f ((tcvTr W σ).comp T) x := (tcvTr W σ).hasFDerivAt.comp x hT
    refine ⟨a, c, fun v => ?_, fun j => ?_⟩
    · rw [hfx.fderiv, ContinuousLinearMap.comp_apply, hTv, tcvTr_apply]
      rfl
    · have := hac j
      rwa [one_pow, one_mul] at this
  · obtain ⟨T, hT, a, c, hTv, hac⟩ := wcov_U_hasFDerivAt hX hz hκ Kh x εU DU hDU
    exact ⟨a, c, fun v => by rw [hT.fderiv, hTv]; rfl, hac⟩

end FixedKappa

/-!
## 4. The limit `κ → 0` for the common-port weight `K̂ = [[z_b - X, 0], [0, 0]]`
-/

section Limit

variable {W : ℕ} {b : ℝ}

/-- The constant `c₁ (1 + η₀⁻¹)`, `c₁ = 1 + 2(7 + η₀⁻¹)`, of `reg_bounds`. -/
def wcovKh (η₀ : ℝ) : ℝ := (1 + 2 * (7 + η₀⁻¹)) * (1 + η₀⁻¹)

/-- `wcovKh η₀ ≥ 0` for `η₀ > 0` (real constant). -/
theorem wcovKh_nonneg {η₀ : ℝ} (hη : 0 < η₀) : 0 ≤ wcovKh η₀ := by
  unfold wcovKh; positivity

/-- **Weighted covariance in the real coordinates** (`κ → 0` by dominated convergence).
`μ = gaussianProduct (tflVar W b .common)`; `W ≥ 1`, `0 < b < 1/2`, Hermitian `X`, `|e| ≤ 2`,
`0 < η₀ ≤ Im z₀`; words with `ℓ_f ≤ 2`, `ℓ_U ≤ 1` resolvent letters and deterministic letters of
norm `≤ 1`; hypotheses: a.s. invertibility and `E Ψ¹² ≤ M` (`Ψ = cpPsi`). With
`𝒢 = commonPortResolvent`, `K̂ = padTop (z_b - X)`, `f = W⁻¹ Tr w_f(𝒢)`, `U = w_U(𝒢)(K̂𝒢)ᴴ`:
`f, U, fU` are integrable and
`‖E[fU] - E f E U‖ ≤ 40 · 4096 (1 + c_K²) M / W²`, `c_K = wcovKh η₀`. -/
theorem wcov_core (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {e : ℝ} (he : |e| ≤ 2)
    {η₀ : ℝ} (hη : 0 < η₀) (hzim : η₀ ≤ (commonZ b e).im) {ℓf ℓU : ℕ} (hℓf : ℓf ≤ 2)
    (hℓU : ℓU ≤ 1) (εf : Fin ℓf → Bool)
    (Df : Fin (ℓf + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
    (εU : Fin ℓU → Bool)
    (DU : Fin (ℓU + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
    (hDf : ∀ j, ‖Df j‖ ≤ 1) (hDU : ∀ j, ‖DU j‖ ≤ 1)
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b .common),
      IsUnit (layerMatrix .common e (commonZ b e) X (tflEmbed W b .common x)).det)
    {M : ℝ} (hΨi : Integrable (fun x => cpPsi b e X (tflEmbed W b .common x) ^ 12)
      (gaussianProduct (tflVar W b .common)))
    (hΨM : ∫ x, cpPsi b e X (tflEmbed W b .common x) ^ 12
      ∂gaussianProduct (tflVar W b .common) ≤ M) :
    Integrable (fun x => tcvTr W .common
        (wordEval εf Df (commonPortResolvent b e X (tflEmbed W b .common x))))
        (gaussianProduct (tflVar W b .common)) ∧
      Integrable (fun x => wordEval εU DU (commonPortResolvent b e X (tflEmbed W b .common x)) *
        (padTop (matchedLeadK b e X) * commonPortResolvent b e X (tflEmbed W b .common x))ᴴ)
        (gaussianProduct (tflVar W b .common)) ∧
      Integrable (fun x => tcvTr W .common
          (wordEval εf Df (commonPortResolvent b e X (tflEmbed W b .common x))) •
        (wordEval εU DU (commonPortResolvent b e X (tflEmbed W b .common x)) *
          (padTop (matchedLeadK b e X) * commonPortResolvent b e X (tflEmbed W b .common x))ᴴ))
        (gaussianProduct (tflVar W b .common)) ∧
      ‖(∫ x, tcvTr W .common
            (wordEval εf Df (commonPortResolvent b e X (tflEmbed W b .common x))) •
          (wordEval εU DU (commonPortResolvent b e X (tflEmbed W b .common x)) *
            (padTop (matchedLeadK b e X) * commonPortResolvent b e X (tflEmbed W b .common x))ᴴ)
            ∂gaussianProduct (tflVar W b .common)) -
        (∫ x, tcvTr W .common
            (wordEval εf Df (commonPortResolvent b e X (tflEmbed W b .common x)))
            ∂gaussianProduct (tflVar W b .common)) •
          (∫ x, wordEval εU DU (commonPortResolvent b e X (tflEmbed W b .common x)) *
            (padTop (matchedLeadK b e X) * commonPortResolvent b e X (tflEmbed W b .common x))ᴴ
            ∂gaussianProduct (tflVar W b .common))‖ ≤
        40 * 4096 * (1 + wcovKh η₀ ^ 2) * M / (W : ℝ) ^ 2 := by
  set μ := gaussianProduct (tflVar W b .common) with hμ
  set Kh : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    padTop (matchedLeadK b e X) with hKh
  set Gr : (TflCoord W .common → ℝ) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    fun x => commonPortResolvent b e X (tflEmbed W b .common x) with hGrdef
  set Ff : Matrix (LayerSite W .common) (LayerSite W .common) ℂ → ℂ :=
    fun N => tcvTr W .common (wordEval εf Df N) with hFf
  set FU : Matrix (LayerSite W .common) (LayerSite W .common) ℂ →
      Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    fun N => wordEval εU DU N * (Kh * N)ᴴ with hFU
  have hFfc : Continuous Ff := (tcvTr W .common).continuous.comp (tcv_continuous_wordEval εf Df)
  have hFUc : Continuous FU :=
    (tcv_continuous_wordEval εU DU).mul (continuous_const.mul continuous_id).matrix_conjTranspose
  have hGr : Measurable Gr :=
    (measurable_layerResolvent .common e (commonZ b e) X).comp (tfl_measurable_embed W b .common)
  have hz0 : 0 ≤ (commonZ b e).im := hη.le.trans hzim
  set cK := wcovKh η₀ with hcK
  have hcK0 : 0 ≤ cK := wcovKh_nonneg hη
  set t : (TflCoord W .common → ℝ) → ℝ :=
    fun x => 2 * cpPsi b e X (tflEmbed W b .common x) with ht
  have ht1 : ∀ x, 1 ≤ t x := fun x => by
    have := one_le_cpPsi b e X (tflEmbed W b .common x); simp only [ht]; linarith
  have ht0 : ∀ x, 0 ≤ t x := fun x => zero_le_one.trans (ht1 x)
  have hpw : ∀ x {k : ℕ}, k ≤ 12 → t x ^ k ≤ t x ^ 12 := fun x k hk =>
    pow_le_pow_right₀ (ht1 x) hk
  have hT12 : Integrable (fun x => t x ^ 12) μ := by
    have : (fun x => t x ^ 12) = fun x => 4096 * cpPsi b e X (tflEmbed W b .common x) ^ 12 := by
      funext x; simp only [ht]; ring
    rw [this]; exact hΨi.const_mul _
  have hT12M : ∫ x, t x ^ 12 ∂μ ≤ 4096 * M := by
    have : (fun x => t x ^ 12) = fun x => 4096 * cpPsi b e X (tflEmbed W b .common x) ^ 12 := by
      funext x; simp only [ht]; ring
    rw [this, integral_const_mul]; linarith
  -- pointwise bounds through `(‖N‖ ≤ t, ‖K̂N‖ ≤ c_K t⁴)`
  have hbnds : ∀ x (N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ), ‖N‖ ≤ t x →
      ‖Kh * N‖ ≤ cK * t x ^ 4 →
      ‖Ff N‖ ≤ 4 * t x ^ 12 ∧ ‖FU N‖ ≤ cK * t x ^ 12 ∧ ‖Ff N • FU N‖ ≤ 4 * cK * t x ^ 12 := by
    intro x N hN hKN
    have hN0 := norm_nonneg N
    have hwf : ‖wordEval εf Df N‖ ≤ t x ^ ℓf := by
      have := tcv_norm_wordEval_le zero_le_one εf Df N hDf
      rw [one_pow, one_mul] at this
      exact this.trans (pow_le_pow_left₀ hN0 hN _)
    have hwU : ‖wordEval εU DU N‖ ≤ t x ^ ℓU := by
      have := tcv_norm_wordEval_le zero_le_one εU DU N hDU
      rw [one_pow, one_mul] at this
      exact this.trans (pow_le_pow_left₀ hN0 hN _)
    have h1 : ‖Ff N‖ ≤ 4 * t x ^ ℓf := (tcv_tr_le .common hW _).trans (by gcongr)
    have h2 : ‖FU N‖ ≤ cK * t x ^ (ℓU + 4) := by
      refine (l2_opNorm_mul _ _).trans ?_
      rw [l2_opNorm_conjTranspose]
      calc ‖wordEval εU DU N‖ * ‖Kh * N‖ ≤ t x ^ ℓU * (cK * t x ^ 4) :=
            mul_le_mul hwU hKN (norm_nonneg _) (by have := ht0 x; positivity)
        _ = cK * t x ^ (ℓU + 4) := by ring
    have hx0 := ht0 x
    refine ⟨h1.trans (mul_le_mul_of_nonneg_left (hpw x (by omega : ℓf ≤ 12)) (by norm_num)),
      h2.trans (mul_le_mul_of_nonneg_left (hpw x (by omega : ℓU + 4 ≤ 12)) hcK0), ?_⟩
    rw [norm_smul]
    calc ‖Ff N‖ * ‖FU N‖ ≤ (4 * t x ^ ℓf) * (cK * t x ^ (ℓU + 4)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 4 * cK * t x ^ (ℓf + (ℓU + 4)) := by ring
      _ ≤ 4 * cK * t x ^ 12 :=
          mul_le_mul_of_nonneg_left (hpw x (by omega : ℓf + (ℓU + 4) ≤ 12)) (by positivity)
  -- the regularized family `κ_m = 1/(m+1)` and its a.e. bounds
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκ1 : ∀ m, κm m ≤ 1 := fun m => by
    rw [hκm, div_le_one (by positivity)]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (TflCoord W .common → ℝ) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    fun m => tcvG W b .common e (commonZ b e) X (κm m) with hGm
  have hGmc : ∀ m, Continuous (Gm m) := fun m =>
    (tcv_G_contDiff W b .common e (commonZ b e) hX hz0 (hκpos m)).continuous
  have hreg : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ≤ t x ∧ ‖Kh * Gm m x‖ ≤ cK * t x ^ 4 := by
    intro m
    filter_upwards [hinv] with x hx
    have hGeq : Gm m x = regResolvent e (commonZ b e) X (κm m) (tflEmbed W b .common x) := by
      simp only [hGm]; rw [tcvG, tflPsi_inv_eq]; rfl
    obtain ⟨h1, -, h3⟩ := reg_bounds hb0.le (by linarith) he hX hη hzim (hκpos m) (hκ1 m)
      (tflEmbed W b .common x) (tflEmbed_blockDiag_isHermitian W b .common x) hx
    rw [hGeq]
    have hP1 := one_le_cpPsi b e X (tflEmbed W b .common x)
    refine ⟨h1, (norm_padTop_mul_le _ _).trans (h3.trans ?_)⟩
    simp only [hcK, wcovKh, ht]
    have hc0 : 0 ≤ (1 + 2 * (7 + η₀⁻¹)) * (1 + η₀⁻¹) := by positivity
    have hP4 : cpPsi b e X (tflEmbed W b .common x) ^ 4 ≤
        (2 * cpPsi b e X (tflEmbed W b .common x)) ^ 4 := by
      gcongr; linarith
    exact mul_le_mul_of_nonneg_left hP4 hc0
  have hGmlim : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (Gr x)) := by
    filter_upwards [hinv] with x hx
    exact tcv_G_tendsto .common e (commonZ b e) hx hκlim
  have hregall : ∀ᵐ x ∂μ, ∀ m, ‖Gm m x‖ ≤ t x ∧ ‖Kh * Gm m x‖ ≤ cK * t x ^ 4 :=
    ae_all_iff.mpr hreg
  have hlimN : ∀ᵐ x ∂μ, ‖Gr x‖ ≤ t x ∧ ‖Kh * Gr x‖ ≤ cK * t x ^ 4 := by
    filter_upwards [hregall, hGmlim] with x hx hl
    exact ⟨le_of_tendsto' hl.norm fun m => (hx m).1,
      le_of_tendsto' (((continuous_const.mul continuous_id).tendsto _).comp hl).norm
        fun m => (hx m).2⟩
  -- integrability of the limits
  have hfm : AEStronglyMeasurable (fun x => Ff (Gr x)) μ :=
    (hFfc.measurable.comp hGr).aestronglyMeasurable
  have hUm : AEStronglyMeasurable (fun x => FU (Gr x)) μ :=
    (hFUc.measurable.comp hGr).aestronglyMeasurable
  have hfi : Integrable (fun x => Ff (Gr x)) μ :=
    (hT12.const_mul 4).mono' hfm (hlimN.mono fun x hx => (hbnds x _ hx.1 hx.2).1)
  have hUi : Integrable (fun x => FU (Gr x)) μ :=
    (hT12.const_mul cK).mono' hUm (hlimN.mono fun x hx => (hbnds x _ hx.1 hx.2).2.1)
  have hfUi : Integrable (fun x => Ff (Gr x) • FU (Gr x)) μ :=
    (hT12.const_mul (4 * cK)).mono' (hfm.smul hUm)
      (hlimN.mono fun x hx => (hbnds x _ hx.1 hx.2).2.2)
  refine ⟨hfi, hUi, hfUi, ?_⟩
  -- dominated convergence for the three means
  have hlimFU : Tendsto (fun m => ∫ x, Ff (Gm m x) • FU (Gm m x) ∂μ) atTop
      (𝓝 (∫ x, Ff (Gr x) • FU (Gr x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 4 * cK * t x ^ 12)
      (fun m => ((hFfc.comp (hGmc m)).smul (hFUc.comp (hGmc m))).aestronglyMeasurable)
      (hT12.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hreg m] with x hx
      exact (hbnds x _ hx.1 hx.2).2.2
    · filter_upwards [hGmlim] with x hx
      exact ((hFfc.tendsto _).comp hx).smul ((hFUc.tendsto _).comp hx)
  have hlimF : Tendsto (fun m => ∫ x, Ff (Gm m x) ∂μ) atTop (𝓝 (∫ x, Ff (Gr x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 4 * t x ^ 12)
      (fun m => (hFfc.comp (hGmc m)).aestronglyMeasurable)
      (hT12.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hreg m] with x hx
      exact (hbnds x _ hx.1 hx.2).1
    · filter_upwards [hGmlim] with x hx
      exact (hFfc.tendsto _).comp hx
  have hlimU : Tendsto (fun m => ∫ x, FU (Gm m x) ∂μ) atTop (𝓝 (∫ x, FU (Gr x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => cK * t x ^ 12)
      (fun m => (hFUc.comp (hGmc m)).aestronglyMeasurable)
      (hT12.const_mul _) (fun m => ?_) ?_
    · filter_upwards [hreg m] with x hx
      exact (hbnds x _ hx.1 hx.2).2.1
    · filter_upwards [hGmlim] with x hx
      exact (hFUc.tendsto _).comp hx
  have hlim := (hlimFU.sub (hlimF.smul hlimU)).norm
  refine le_of_tendsto' hlim fun m => ?_
  -- the bound for each `κ_m`
  refine (wcov_reg hW hb0 hb1 hX hz0 (hκpos m) Kh εf Df εU DU hDf hDU).trans ?_
  have hA : ∫ x, (‖Gm m x‖ ^ (ℓf + 1)) ^ 2 ∂μ ≤ 4096 * M := by
    refine le_trans (integral_mono_ae ?_ hT12 ?_) hT12M
    · refine hT12.mono' ((((hGmc m).norm.pow _).pow 2).aestronglyMeasurable) ?_
      filter_upwards [hreg m] with x hx
      rw [Real.norm_of_nonneg (by positivity), ← pow_mul]
      exact (pow_le_pow_left₀ (norm_nonneg _) hx.1 _).trans
        (hpw x (by omega : (ℓf + 1) * 2 ≤ 12))
    · filter_upwards [hreg m] with x hx
      rw [← pow_mul]
      exact (pow_le_pow_left₀ (norm_nonneg _) hx.1 _).trans
        (hpw x (by omega : (ℓf + 1) * 2 ≤ 12))
  have hBpt : ∀ x, ‖Gm m x‖ ≤ t x → ‖Kh * Gm m x‖ ≤ cK * t x ^ 4 →
      (‖Gm m x‖ ^ (ℓU + 1) * ‖Kh * Gm m x‖) ^ 2 ≤ cK ^ 2 * t x ^ 12 := by
    intro x h1 h2
    have hx0 := ht0 x
    calc (‖Gm m x‖ ^ (ℓU + 1) * ‖Kh * Gm m x‖) ^ 2
        ≤ (t x ^ (ℓU + 1) * (cK * t x ^ 4)) ^ 2 := by
          gcongr
      _ = cK ^ 2 * t x ^ (2 * ℓU + 10) := by ring
      _ ≤ cK ^ 2 * t x ^ 12 :=
          mul_le_mul_of_nonneg_left (hpw x (by omega : 2 * ℓU + 10 ≤ 12)) (by positivity)
  have hB : ∫ x, (‖Gm m x‖ ^ (ℓU + 1) * ‖Kh * Gm m x‖) ^ 2 ∂μ ≤ cK ^ 2 * (4096 * M) := by
    refine le_trans (integral_mono_ae ?_ (hT12.const_mul (cK ^ 2)) ?_) ?_
    · refine (hT12.const_mul (cK ^ 2)).mono'
        (((((hGmc m).norm.pow _).mul
          (continuous_norm.comp (continuous_const.mul (hGmc m)))).pow 2).aestronglyMeasurable) ?_
      filter_upwards [hreg m] with x hx
      rw [Real.norm_of_nonneg (by positivity)]
      exact hBpt x hx.1 hx.2
    · filter_upwards [hreg m] with x hx
      exact hBpt x hx.1 hx.2
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hT12M (by positivity)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hℓf' : (ℓf : ℝ) ≤ 2 := by exact_mod_cast hℓf
  have hℓU' : ((ℓU + 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : ℓU + 1 ≤ 2)
  have hA0 : 0 ≤ ∫ x, (‖Gm m x‖ ^ (ℓf + 1)) ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have hB0 : 0 ≤ ∫ x, (‖Gm m x‖ ^ (ℓU + 1) * ‖Kh * Gm m x‖) ^ 2 ∂μ :=
    integral_nonneg fun x => by positivity
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun x => by
    have := one_le_cpPsi b e X (tflEmbed W b .common x); positivity) hΨM
  have hc : 10 * (ℓf : ℝ) * ((ℓU + 1 : ℕ) : ℝ) ≤ 40 := by
    have := Nat.cast_nonneg (α := ℝ) ℓf
    nlinarith
  calc 10 * (ℓf : ℝ) * ((ℓU + 1 : ℕ) : ℝ) / (W : ℝ) ^ 2 *
        ((∫ x, (‖Gm m x‖ ^ (ℓf + 1)) ^ 2 ∂μ) +
          ∫ x, (‖Gm m x‖ ^ (ℓU + 1) * ‖Kh * Gm m x‖) ^ 2 ∂μ)
      ≤ 40 / (W : ℝ) ^ 2 * (4096 * M + cK ^ 2 * (4096 * M)) := by
        gcongr
    _ = 40 * 4096 * (1 + cK ^ 2) * M / (W : ℝ) ^ 2 := by ring

end Limit

/-!
## 5. Moments of `Ψ` and the weighted covariance on `layerLaw`
-/

section Contract

/-- **Twelfth moment of `Ψ = cpPsi`** (law `layerLaw W b .common`): from
`GaussianAbsorptionContract` (at `η₀`, `|z| ≤ 3`), `gueBlock_eLpNorm_le` and `bond_eLpNorm_le`
at exponent `48`: there are `M, W₀` with `E Ψ¹² ≤ M` for `W ≥ W₀`, every Hermitian `X` and every
`e` with `η₀ ≤ Im z₀`, `|z₀| ≤ 3`. -/
theorem cpPsi_twelve_le (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ : ℝ, 0 < η₀ →
      ∃ (M : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
        ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        ∀ e : ℝ, η₀ ≤ (commonZ b e).im → ‖commonZ b e‖ ≤ 3 →
          Integrable (fun ω => cpPsi b e X ω ^ 12) (layerLaw W b .common) ∧
            ∫ ω, cpPsi b e X ω ^ 12 ∂layerLaw W b .common ≤ M := by
  intro b hb0 hb1 η₀ hη
  obtain ⟨ε₁, CG, hε₁, hCG, hGA'⟩ := hGA b hb0 hb1 η₀ 3 hη
  obtain ⟨CA, hCA, hA⟩ := gueBlock_eLpNorm_le
  set CB := bondMomentConst b with hCB
  have hCB0 : 0 < CB := bondMomentConst_pos b
  set Mψ : ℝ := CA * CA * (CB * (1 + CG)) with hMψ
  have hMψ0 : 0 ≤ Mψ := by positivity
  refine ⟨Mψ ^ 12, ⌈(48 : ℝ) + 1 + 48 / ε₁⌉₊, fun W hW hW₀ X hX e hzim hznorm => ?_⟩
  have hWr : (48 : ℝ) + 1 + 48 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hW₀)
  have hpe : 0 ≤ 48 / ε₁ := by positivity
  have hq48 : (48 : ℝ) ≤ ε₁ * W := by
    have : 48 / ε₁ ≤ W := by linarith
    rw [div_le_iff₀ hε₁] at this; linarith
  have hq48W : (48 : ℝ) ≤ (W : ℝ) - 1 := by linarith
  have := bond_isProbabilityMeasure_layerLaw W b .common
  obtain ⟨-, hmom⟩ := hGA' W hW .common X hX e (commonZ b e) hzim hznorm
  have h48 : (4 : ℝ) * 12 = 48 := by norm_num
  have hAl : ∀ a : Fin 2, eLpNorm (fun ω : LayerSample W .common => 1 + ‖ω.1 a‖)
      (ENNReal.ofReal (4 * 12)) (layerLaw W b .common) ≤ ENNReal.ofReal CA := fun a => by
    rw [h48]; exact hA W b hb0.le hb1.le .common a 48 (by norm_num) hq48W
  have hBl : eLpNorm (fun ω : LayerSample W .common => 1 + ‖bondMatrix .common ω.2‖)
      (ENNReal.ofReal (4 * 12)) (layerLaw W b .common) ≤ ENNReal.ofReal CB := by
    rw [h48]; exact bond_eLpNorm_le .common hb0 (by norm_num) (by linarith)
  have hGl : eLpNorm (fun ω : LayerSample W .common => 1 + ‖commonPortResolvent b e X ω‖)
      (ENNReal.ofReal (4 * 12)) (layerLaw W b .common) ≤ ENNReal.ofReal (1 + CG) := by
    rw [h48]
    exact eLpNorm_one_add_le (by norm_num) hCG.le (hmom 48 (by norm_num) hq48)
  have hΨ := eLpNorm_cpPsi_le (X := X) (e := e) (by norm_num : (0 : ℝ) < 12) hAl hBl hGl
  have hΨeq : ENNReal.ofReal CA * ENNReal.ofReal CA * (ENNReal.ofReal CB * ENNReal.ofReal (1 + CG))
      = ENNReal.ofReal Mψ := by
    rw [hMψ, ← ENNReal.ofReal_mul hCA.le, ← ENNReal.ofReal_mul hCB0.le,
      ← ENNReal.ofReal_mul (by positivity)]
  rw [hΨeq] at hΨ
  have hnn : ∀ ω, 0 ≤ cpPsi b e X ω := fun ω => zero_le_one.trans (one_le_cpPsi b e X ω)
  have hΨ' : eLpNorm (fun ω => ‖cpPsi b e X ω‖) (ENNReal.ofReal ((12 : ℕ) : ℝ))
      (layerLaw W b .common) ≤ ENNReal.ofReal Mψ := by
    rw [eLpNorm_norm, Nat.cast_ofNat]
    · exact hΨ
    · exact (measurable_cpPsi b e X).aestronglyMeasurable
  obtain ⟨hi, hle⟩ := tcv_moment (by norm_num : 1 ≤ 12) hMψ0 hΨ'
  have hfun : (fun ω => ‖cpPsi b e X ω‖ ^ 12) = fun ω => cpPsi b e X ω ^ 12 := by
    funext ω; rw [Real.norm_of_nonneg (hnn ω)]
  rw [hfun] at hi hle
  exact ⟨hi, hle⟩

/-- **The weighted trace–matrix covariance** (by the argument of the trace–matrix covariance bound). Law `layerLaw W b .common`
(conditional on the deformation: every deterministic Hermitian `X`); `0 < b < 1/2`, `κ > 0`
first, then `C, W₀`; uniformly in `W ≥ W₀`, Hermitian `X`, `e ∈ bulkInterval κ` and the words
(`ℓ_f ≤ 2`, `ℓ_U ≤ 1` resolvent letters, deterministic letters of norm `≤ 1`). With
`𝒢 = commonPortResolvent b e X`, `K̂ = padTop (z_b I - X)` (`‖K̂‖` unbounded in `X`),
`f = W⁻¹ Tr w_f(𝒢)`, `U = w_U(𝒢) (K̂𝒢)ᴴ`: `f`, `U`, `fU` are integrable and
`‖E(fU) - (Ef)(EU)‖ ≤ C W⁻²` (operator norm, entrywise `matrixExpect`).
Hypothesis: `GaussianAbsorptionContract`; other inputs `gueBlock_eLpNorm_le`,
`bond_eLpNorm_le`, `reg_bounds`, `ou_covariance_matrix`, `tcv_kernel_le` (with `tcv_kernel_eq`). -/
theorem weightedCov_holds (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
        ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        ∀ e ∈ bulkInterval κ, ∀ (ℓf ℓU : ℕ), ℓf ≤ 2 → ℓU ≤ 1 →
        ∀ (εf : Fin ℓf → Bool)
          (Df : Fin (ℓf + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
          (εU : Fin ℓU → Bool)
          (DU : Fin (ℓU + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ),
          (∀ j, ‖Df j‖ ≤ 1) → (∀ j, ‖DU j‖ ≤ 1) →
          Integrable (fun ω => (W : ℂ)⁻¹ * (wordEval εf Df (commonPortResolvent b e X ω)).trace)
              (layerLaw W b .common) ∧
            Integrable (fun ω => wordEval εU DU (commonPortResolvent b e X ω) *
              (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ)
              (layerLaw W b .common) ∧
            Integrable (fun ω =>
              ((W : ℂ)⁻¹ * (wordEval εf Df (commonPortResolvent b e X ω)).trace) •
                (wordEval εU DU (commonPortResolvent b e X ω) *
                  (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ))
              (layerLaw W b .common) ∧
            ‖meqCov (layerLaw W b .common)
                (fun ω => (W : ℂ)⁻¹ * (wordEval εf Df (commonPortResolvent b e X ω)).trace)
                (fun ω => wordEval εU DU (commonPortResolvent b e X ω) *
                  (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ)‖ ≤
              C / (W : ℝ) ^ 2 := by
  intro b hb0 hb1 κ hκ
  by_cases hκ2 : 2 < κ
  · refine ⟨0, 0, fun W _ _ X _ e he => ?_⟩
    exact absurd (le_trans he.1 he.2) (by linarith)
  push Not at hκ2
  set η₀ : ℝ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη0 : 0 < η₀ := by
    have hs := Real.sqrt_pos.mpr (BlockBand.Layers.four_sub_sq_pos hκ (by linarith))
    have : 0 < 1 - 2 * b := by linarith
    positivity
  obtain ⟨M, WΨ, hΨ⟩ := cpPsi_twelve_le hGA b hb0 hb1 η₀ hη0
  obtain ⟨ε₁, CG, hε₁, hCG, hGA'⟩ := hGA b hb0 hb1 η₀ 3 hη0
  refine ⟨40 * 4096 * (1 + wcovKh η₀ ^ 2) * M, WΨ, ?_⟩
  intro W hW hW₀ X hX e he ℓf ℓU hℓf hℓU εf Df εU DU hDf hDU
  have heabs : |e| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ he).le
  have hzim : η₀ ≤ (commonZ b e).im := commonZ_im_ge_of_mem_bulkInterval hb1.le hκ he
  have hznorm : ‖commonZ b e‖ ≤ 3 := norm_commonZ_le hb0.le (by linarith) heabs
  obtain ⟨hinv, -⟩ := hGA' W hW .common X hX e (commonZ b e) hzim hznorm
  obtain ⟨hΨi, hΨM⟩ := hΨ W hW hW₀ X hX e hzim hznorm
  set μc := gaussianProduct (tflVar W b .common) with hμc
  set Φ := tflEmbed W b .common with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b .common
  have hlaw : layerLaw W b .common = μc.map Φ := tfl_layerLaw_eq_map W b .common
  have hinvc : ∀ᵐ x ∂μc, IsUnit (layerMatrix .common e (commonZ b e) X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hΨm : Measurable (fun ω => cpPsi b e X ω ^ 12) := (measurable_cpPsi b e X).pow_const 12
  have hΨic : Integrable (fun x => cpPsi b e X (Φ x) ^ 12) μc := by
    rw [hlaw] at hΨi
    exact (integrable_map_measure hΨm.aestronglyMeasurable hΦ.aemeasurable).mp hΨi
  have hΨMc : ∫ x, cpPsi b e X (Φ x) ^ 12 ∂μc ≤ M := by
    rw [hlaw, integral_map hΦ.aemeasurable hΨm.aestronglyMeasurable] at hΨM
    exact hΨM
  obtain ⟨hFi, hUi, hFUi, hbd⟩ := wcov_core hW hb0 hb1 hX heabs hη0 hzim hℓf hℓU εf Df εU DU
    hDf hDU hinvc hΨic hΨMc
  -- measurability on the layer
  have hGm : Measurable (fun ω => commonPortResolvent b e X ω) :=
    measurable_layerResolvent .common e (commonZ b e) X
  have hFc : Continuous (fun N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
      tcvTr W .common (wordEval εf Df N)) :=
    (tcvTr W .common).continuous.comp (tcv_continuous_wordEval εf Df)
  have hUc : Continuous (fun N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
      wordEval εU DU N * (padTop (matchedLeadK b e X) * N)ᴴ) :=
    (tcv_continuous_wordEval εU DU).mul (continuous_const.mul continuous_id).matrix_conjTranspose
  have hfm : Measurable (fun ω => tcvTr W .common
      (wordEval εf Df (commonPortResolvent b e X ω))) := hFc.measurable.comp hGm
  have hUm : Measurable (fun ω => wordEval εU DU (commonPortResolvent b e X ω) *
      (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ) := hUc.measurable.comp hGm
  have hfUm : Measurable (fun ω => tcvTr W .common
      (wordEval εf Df (commonPortResolvent b e X ω)) •
        (wordEval εU DU (commonPortResolvent b e X ω) *
          (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ)) := hfm.smul hUm
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Integrable (fun ω => tcvTr W .common
      (wordEval εf Df (commonPortResolvent b e X ω))) (layerLaw W b .common)
    rw [hlaw, integrable_map_measure hfm.aestronglyMeasurable hΦ.aemeasurable]
    exact hFi
  · rw [hlaw, integrable_map_measure hUm.aestronglyMeasurable hΦ.aemeasurable]
    exact hUi
  · change Integrable (fun ω => tcvTr W .common
      (wordEval εf Df (commonPortResolvent b e X ω)) •
        (wordEval εU DU (commonPortResolvent b e X ω) *
          (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ)) (layerLaw W b .common)
    rw [hlaw, integrable_map_measure hfUm.aestronglyMeasurable hΦ.aemeasurable]
    exact hFUi
  · change ‖matrixExpect (layerLaw W b .common) (fun ω => tcvTr W .common
        (wordEval εf Df (commonPortResolvent b e X ω)) •
          (wordEval εU DU (commonPortResolvent b e X ω) *
            (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ)) -
      (∫ ω, tcvTr W .common (wordEval εf Df (commonPortResolvent b e X ω))
        ∂layerLaw W b .common) •
        matrixExpect (layerLaw W b .common) (fun ω => wordEval εU DU (commonPortResolvent b e X ω) *
          (padTop (matchedLeadK b e X) * commonPortResolvent b e X ω)ᴴ)‖ ≤ _
    rw [tcv_matrixExpect_eq hfUm hFUi, tcv_matrixExpect_eq hUm hUi, hlaw,
      integral_map hΦ.aemeasurable hfm.aestronglyMeasurable]
    exact hbd.trans (le_of_eq (by ring))

end Contract

end BlockBand.Critical.CommonPort
