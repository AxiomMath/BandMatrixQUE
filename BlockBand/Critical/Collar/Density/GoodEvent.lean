module

public import BlockBand.Critical.Collar.Density.Conditional
public import BlockBand.Palm.CoarseRelativeDyson

/-!
# The regular event of the conditional collar

On the regular event, the conditional Schur complement `F` of the collar lies in the fresh class.
Deterministic; no measure. Every `W ≥ 1`, Hermitian `A_j`, `X`, real `e` with `|e| < 2`.

* `freshRegular_of_chi`: a small certificate defect `χ` implies `FreshRegular` with uniform
  constants.
* `norm_certificateChi_collarFW`: `‖χ_F(0, ā)‖ = |W⁻¹ Tr 𝒢_port - a|` for the conditional `F`
  (`μ = ā`, `(F - cā)⁻¹ = H*`).
* `l2Norm_collarF_mulVec_le`: if `‖D⁻¹v‖ ≤ t⁻¹‖v‖` and `Σ|B_xy|² ≤ β` then
  `‖F v‖ ≤ (|e| + β/t)‖v‖`; `normBound_collarFW` turns this into `NormBound` when
  `|e| + β/t ≤ W^A`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical BlockBand.Palm
open scoped ComplexOrder ComplexConjugate

variable {W : ℕ}

/-!
## The regularity certificate in terms of `FreshRegular`
-/

/-- **The regularity certificate implies fresh regularity**: from
`Palm.certificate_full_uniform` (at `E = 0`), a certificate defect `‖χ_F(0, μ)‖ ≤ ε` with
`V ≤ Im μ`, `‖μ‖ ≤ 1` gives `FreshRegular F c 0 r s₀ v₀`, with constants uniform in `N` and `F`. -/
theorem freshRegular_of_chi {c V : ℝ} (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) :
    ∃ ε r s₀ v₀ : ℝ, 0 < ε ∧ FreshConstants c r s₀ v₀ ∧
      ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ μ : ℂ,
        V ≤ μ.im → ‖μ‖ ≤ 1 → ‖certificateChi F c 0 μ‖ ≤ ε → FreshRegular F c 0 r s₀ v₀ := by
  obtain ⟨ε, r, s₀, v₀, C, hε, hr, hs₀, hs₀c, hv₀, -, h⟩ := certificate_full_uniform hc hc1 hV
  refine ⟨ε, r, s₀, v₀, hε, ⟨hc, hc1, hr, hs₀, hs₀c, hv₀⟩, fun N hN F hF μ hVμ hμ hχ => ?_⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨hreg, -⟩ := h (Fin N) F hF 0 μ hVμ hμ hχ
  intro s hs x hx η hη
  have hs0 : 0 < s := by linarith [hs.1]
  have hz : (⟨x, η⟩ : ℂ) = (x : ℂ) + Complex.I * η := by
    apply Complex.ext <;> simp
  obtain ⟨-, h1, h2⟩ := hreg s hs.1 hs.2 x hx η hη.1 hη.2
  rw [hz, BlockBand.Palm.CoarseRelative.freshDyson_eq_certificate hF hN hs0 (by simpa using hη.1)]
  exact ⟨h1, h2⟩

/-!
## The certificate defect of the conditional `F`
-/

theorem trace_submatrix_portEquiv (M : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) :
    (M.submatrix (portEquiv W).symm (portEquiv W).symm).trace = M.trace := by
  unfold Matrix.trace
  exact Equiv.sum_comp (portEquiv W).symm (fun x => M x x)

/-- **`χ` of the conditional `F`**: `‖χ_F(0, ā)‖ = |W⁻¹ Tr 𝒢_port - a|`, for Hermitian `A_j, X`,
invertible `D` and `|e| < 2`; `c = 1 - 2b`. -/
theorem norm_certificateChi_collarFW {b e : ℝ} (he : |e| < 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian) (hb : b < 1 / 2)
    (hD : IsUnit (collarTopBlock e X ω).det) :
    ‖certificateChi (collarFW e X ω) (1 - 2 * b) 0 (star (matchedA e))‖ =
      ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖ := by
  have hw_eq := collarShiftW_eq (b := b) he.le
  have hwim : (collarShiftW b e).im < 0 := by
    rw [hw_eq]
    have := BlockBand.Layers.matchedA_im_neg he
    have hc : 0 < 1 - 2 * b := by linarith
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hc this
  have hS := isUnit_det_collarF_sub (b := b) hX hA hwim
  have hF := collarFW_isHermitian e hX hA
  have hstar : ((0 : ℝ) : ℂ) + ((1 - 2 * b : ℝ) : ℂ) * star (matchedA e) = star (collarShiftW b e) := by
    rw [hw_eq, star_mul', Complex.star_def, Complex.conj_ofReal]; simp
  have hinv : (collarFW e X ω - star (collarShiftW b e) • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ =
      ((collarFW e X ω - collarShiftW b e • 1)⁻¹)ᴴ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_sub, hF.eq, conjTranspose_smul,
      conjTranspose_one]
  have htr : certificateMatrixTrace (collarFW e X ω)
      (((0 : ℝ) : ℂ) + ((1 - 2 * b : ℝ) : ℂ) * star (matchedA e)) =
        star ((W : ℂ)⁻¹ * (commonPortH b e X ω).trace) := by
    rw [hstar, certificateMatrixTrace, certificateMatrixResolvent, hinv, trace_conjTranspose,
      collarFW_sub_eq, inv_submatrix_equiv, trace_submatrix_portEquiv,
      ← commonPortH_eq b e X ω hD hS, Fintype.card_fin, star_mul', div_eq_mul_inv, mul_comm]
    simp
  rw [certificateChi, htr, portBlockTrace_commonPortResolvent, ← star_sub, norm_star]

/-!
## The polynomial norm of `F`
-/

theorem sum_norm_sq_mulVec_le_frobenius {m n : Type} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (v : n → ℂ) :
    ∑ a, ‖(M *ᵥ v) a‖ ^ 2 ≤ (∑ a, ∑ b, ‖M a b‖ ^ 2) * ∑ b, ‖v b‖ ^ 2 := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 : ‖(M *ᵥ v) a‖ ≤ ∑ b, ‖M a b‖ * ‖v b‖ := by
    unfold mulVec dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h3 : (∑ b, ‖M a b‖ * ‖v b‖) ^ 2 ≤ (∑ b, ‖M a b‖ ^ 2) * ∑ b, ‖v b‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h0 : 0 ≤ ‖(M *ᵥ v) a‖ := norm_nonneg _
  calc ‖(M *ᵥ v) a‖ ^ 2 ≤ (∑ b, ‖M a b‖ * ‖v b‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h3

theorem frobenius_conjTranspose {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    ∑ a, ∑ b, ‖Mᴴ a b‖ ^ 2 = ∑ a, ∑ b, ‖M a b‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp [conjTranspose_apply]

/-- **Polynomial norm of `F`.** If `‖D⁻¹v‖² ≤ t⁻²‖v‖²` for all `v` and `Σ|B_xy|² ≤ β`, then
`‖F v‖ ≤ (|e| + β/t) ‖v‖` (`l2Norm`). -/
theorem l2Norm_collarF_mulVec_le {e : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {ω : LayerSample W .common} {t β : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hDinv : ∀ v, ∑ a, ‖((collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤ (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2)
    (hB : ∑ a, ∑ b, ‖bondMatrix .common ω.2 a b‖ ^ 2 ≤ β) (v : Fin 1 × Fin W → ℂ) :
    l2Norm (collarF e X ω *ᵥ v) ≤ (|e| + β / t) * l2Norm v := by
  set Bm := bondMatrix .common ω.2
  have hBv : ∀ u, ∑ a, ‖(Bm *ᵥ u) a‖ ^ 2 ≤ β * ∑ a, ‖u a‖ ^ 2 := fun u =>
    (sum_norm_sq_mulVec_le_frobenius Bm u).trans (mul_le_mul_of_nonneg_right hB
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hBHv : ∀ u, ∑ a, ‖(Bmᴴ *ᵥ u) a‖ ^ 2 ≤ β * ∑ a, ‖u a‖ ^ 2 := fun u =>
    (sum_norm_sq_mulVec_le_frobenius Bmᴴ u).trans (by
      rw [frobenius_conjTranspose]
      exact mul_le_mul_of_nonneg_right hB (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hsplit : collarF e X ω *ᵥ v =
      -((e : ℂ) • v) - Bmᴴ *ᵥ ((collarTopBlock e X ω)⁻¹ *ᵥ (Bm *ᵥ v)) := by
    rw [collarF, sub_mulVec, neg_mulVec, smul_mulVec, one_mulVec, ← mulVec_mulVec,
      ← mulVec_mulVec]
  have hl2 : ∀ u : Fin 1 × Fin W → ℂ, l2Norm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ _)‖ := by
    intro u
    rw [l2Norm, EuclideanSpace.norm_eq]
  -- norms through `l2Norm` and its square
  have hsq : ∀ (u : Fin 1 × Fin W → ℂ) (K : ℝ), 0 ≤ K →
      ∑ a, ‖u a‖ ^ 2 ≤ K ^ 2 * ∑ a, ‖v a‖ ^ 2 → l2Norm u ≤ K * l2Norm v := by
    intro u K hK h
    unfold l2Norm
    rw [← Real.sqrt_sq hK, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt h
  have hnv : l2Norm (-((e : ℂ) • v)) = |e| * l2Norm v := by
    unfold l2Norm
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, norm_neg, norm_mul, mul_pow,
      ← Finset.mul_sum, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  have hsecond : l2Norm (Bmᴴ *ᵥ ((collarTopBlock e X ω)⁻¹ *ᵥ (Bm *ᵥ v))) ≤ β / t * l2Norm v := by
    refine hsq _ _ (div_nonneg hβ ht.le) ?_
    have h1 := hBHv ((collarTopBlock e X ω)⁻¹ *ᵥ (Bm *ᵥ v))
    have h2 := hDinv (Bm *ᵥ v)
    have h3 := hBv v
    have hv0 : 0 ≤ ∑ a, ‖v a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc _ ≤ β * ((t ^ 2)⁻¹ * (β * ∑ a, ‖v a‖ ^ 2)) := by
          refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans ?_) hβ)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (β / t) ^ 2 * ∑ a, ‖v a‖ ^ 2 := by field_simp
  have htri : l2Norm (-((e : ℂ) • v) - Bmᴴ *ᵥ ((collarTopBlock e X ω)⁻¹ *ᵥ (Bm *ᵥ v))) ≤
      l2Norm (-((e : ℂ) • v)) +
        l2Norm (Bmᴴ *ᵥ ((collarTopBlock e X ω)⁻¹ *ᵥ (Bm *ᵥ v))) := by
    rw [hl2, hl2, hl2, WithLp.toLp_sub]
    exact norm_sub_le _ _
  rw [hsplit]
  calc _ ≤ _ := htri
    _ ≤ |e| * l2Norm v + β / t * l2Norm v := by rw [hnv]; linarith
    _ = (|e| + β / t) * l2Norm v := by ring

theorem l2Norm_submatrix_portEquiv (u : Fin 1 × Fin W → ℂ) :
    l2Norm (u ∘ (portEquiv W).symm) = l2Norm u := by
  unfold l2Norm
  congr 1
  exact Equiv.sum_comp (portEquiv W).symm (fun x => ‖u x‖ ^ 2)

/-- **`NormBound` of the conditional `F`** (`‖F‖ ≤ W^A`), from the same two cutoffs and
`|e| + β/t ≤ W^A`. -/
theorem normBound_collarFW {e : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {ω : LayerSample W .common} {t β A : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hDinv : ∀ v, ∑ a, ‖((collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤ (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2)
    (hB : ∑ a, ∑ b, ‖bondMatrix .common ω.2 a b‖ ^ 2 ≤ β)
    (hA : |e| + β / t ≤ (W : ℝ) ^ A) :
    NormBound (collarFW e X ω) A := by
  intro x
  have h := l2Norm_collarF_mulVec_le ht hβ hDinv hB (x ∘ portEquiv W)
  have hx : (x ∘ portEquiv W) ∘ (portEquiv W).symm = x := by
    funext i; simp
  have hFx : collarFW e X ω *ᵥ x = (collarF e X ω *ᵥ (x ∘ portEquiv W)) ∘ (portEquiv W).symm := by
    funext i
    simp only [collarFW, mulVec, dotProduct, submatrix_apply, Function.comp_apply]
    rw [← Equiv.sum_comp (portEquiv W).symm
      (fun x1 => collarF e X ω ((portEquiv W).symm i) x1 * x ((portEquiv W) x1))]
    simp
  rw [hFx, l2Norm_submatrix_portEquiv]
  have hxl : l2Norm (x ∘ portEquiv W) = l2Norm x := by
    rw [← l2Norm_submatrix_portEquiv (x ∘ portEquiv W), hx]
  rw [hxl] at h
  exact h.trans (mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _))

end BlockBand.Critical.Collar.Density
