module

public import BlockBand.Critical.MatrixClosing.Poles.GoodEventAlgebra

/-!
# The good event of the conditional collar: the pointwise good event

Deterministic; no measure.

* `certificate_regular_uniform`: `Palm.certificate_full_uniform`
  (the regularity certificate, `E = 0`) as one statement: constants `ε_t, r₀, s₀, v₀, C`
  from `c ∈ (0,1)` and `V > 0` such that `‖χ_F(0, μ)‖ ≤ ε_t`, `Im μ ≥ V`, `|μ| ≤ 1` imply
  `FreshRegular F c 0 r₀ s₀ v₀` and `|m_{F,c}(0) - μ| ≤ C‖χ_F(0, μ)‖`.
* `collarFresh_of_event`: on the regular event (`A` Hermitian, `D` invertible,
  `‖D⁻¹‖ ≤ W³`, `Σ|B_xy|² ≤ W³`, `|W⁻¹Tr 𝒢_port - a| ≤ ε_t`, `W ≥ 2`), the conditional `F` is
  in `FreshClass F 7 c 0 r₀ s₀ v₀` and `|m_{F,c}(0) - ā| ≤ C|W⁻¹Tr 𝒢_port - a|`.
* **`collarGood_of_bounds`**: the density-scale and frame-covariance conditions pointwise: from
  the fresh class,
  `|m_{F,c}(0) - ā| ≤ k ≤ πε`, `‖L‖² ≤ R`, `λ(2k/v₀ + (k/v₀)²)R ≤ ε/3`,
  `λ|u_i^*(LL^* - M)u_j| ≤ ε/3` and `λ‖M - γI‖ ≤ ε/3`, the sample is in `CollarGood ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.RelativeVectors
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {W r : ℕ}

/-- **The regularity certificate at `E = 0`**, stated with `FreshConstants` and `FreshRegular`
(from `Palm.certificate_full_uniform` and `Collar.Density.freshRegular_of_chi`): there are
`εt, r₀, s₀, v₀, C` such that for every Hermitian `F` and `μ` with `V ≤ Im μ`, `‖μ‖ ≤ 1` and
`‖certificateChi F c 0 μ‖ ≤ εt`, `F` is regular and `‖freshDyson F c 0 - μ‖ ≤ C ‖certificateChi F c 0 μ‖`.
-/
theorem certificate_regular_uniform {c V : ℝ} (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) :
    ∃ εt r₀ s₀ v₀ C : ℝ, 0 < εt ∧ FreshConstants c r₀ s₀ v₀ ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ μ : ℂ,
        V ≤ μ.im → ‖μ‖ ≤ 1 → ‖BlockBand.Palm.certificateChi F c 0 μ‖ ≤ εt →
          FreshRegular F c 0 r₀ s₀ v₀ ∧
            ‖freshDyson F c ((0 : ℝ) : ℂ) - μ‖ ≤ C * ‖BlockBand.Palm.certificateChi F c 0 μ‖ := by
  obtain ⟨ε₁, r₀, s₀, v₀, hε₁, hK, hreg⟩ := Collar.Density.freshRegular_of_chi hc hc1 hV
  obtain ⟨ε₂, r₂, s₂, v₂, C, hε₂, -, -, -, -, hC, hcert⟩ :=
    BlockBand.Palm.certificate_full_uniform.{0} hc hc1 hV
  refine ⟨min ε₁ ε₂, r₀, s₀, v₀, C, lt_min hε₁ hε₂, hK, hC, fun N hN F hF μ hVμ hμ hχ => ?_⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨hreg N hN F hF μ hVμ hμ (hχ.trans (min_le_left _ _)), ?_⟩
  obtain ⟨-, hm, -⟩ := hcert (Fin N) F hF 0 μ hVμ hμ (hχ.trans (min_le_right _ _))
  rw [BlockBand.Palm.CoarseRelative.freshDyson_eq_certificate hF hN hc (by simp)]
  exact hm

/-- **The regular event puts `F` in the fresh class.** -/
theorem collarFresh_of_event {b e c V εt r₀ s₀ v₀ C : ℝ} (hcdef : c = 1 - 2 * b)
    (hb : b < 1 / 2) (he : |e| < 2) (hW2 : (2 : ℝ) ≤ W)
    (H : ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ μ : ℂ,
        V ≤ μ.im → ‖μ‖ ≤ 1 → ‖BlockBand.Palm.certificateChi F c 0 μ‖ ≤ εt →
          FreshRegular F c 0 r₀ s₀ v₀ ∧
            ‖freshDyson F c ((0 : ℝ) : ℂ) - μ‖ ≤ C * ‖BlockBand.Palm.certificateChi F c 0 μ‖)
    (hVμ : V ≤ (star (matchedA e)).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {ω₁ : LayerSample W .common} (hA : ∀ k, (ω₁.1 k).IsHermitian)
    (hD : IsUnit (Collar.Density.collarTopBlock e X ω₁).det)
    (hDinv : ∀ v, ∑ a, ‖((Collar.Density.collarTopBlock e X ω₁)⁻¹ *ᵥ v) a‖ ^ 2 ≤
      ((((W : ℝ) ^ 3)⁻¹) ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2)
    (hB : ∑ x, ∑ y, ‖bondMatrix .common ω₁.2 x y‖ ^ 2 ≤ (W : ℝ) ^ 3)
    (hχ : ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω₁) 0 - matchedA e‖ ≤ εt) :
    FreshClass (collarF e X ω₁) 7 c 0 r₀ s₀ v₀ ∧
      ‖freshDyson (collarF e X ω₁) c ((0 : ℝ) : ℂ) - star (matchedA e)‖ ≤
        C * ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω₁) 0 - matchedA e‖ := by
  subst hcdef
  have hW : 0 < W := by
    have : (0 : ℝ) < W := by linarith
    exact_mod_cast this
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  rw [collarF_eq_collarFW]
  have hF := Collar.Density.collarFW_isHermitian e hX hA
  have ht : (0 : ℝ) < ((W : ℝ) ^ 3)⁻¹ := by positivity
  have hβ : (0 : ℝ) < (W : ℝ) ^ 3 := by positivity
  have hA7 : |e| + (W : ℝ) ^ 3 / ((W : ℝ) ^ 3)⁻¹ ≤ (W : ℝ) ^ (7 : ℝ) := by
    have h7 : (W : ℝ) ^ (7 : ℝ) = (W : ℝ) ^ (7 : ℕ) := by norm_cast
    have hβt : (W : ℝ) ^ 3 / ((W : ℝ) ^ 3)⁻¹ = (W : ℝ) ^ 6 := by field_simp
    rw [h7, hβt]
    have h6 : (2 : ℝ) ^ 6 ≤ (W : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hW2 6
    have : (W : ℝ) ^ 7 = W * W ^ 6 := by ring
    nlinarith [abs_nonneg e]
  have hnb := Collar.Density.normBound_collarFW ht hβ.le hDinv hB hA7
  have hχeq := Collar.Density.norm_certificateChi_collarFW he hX hA hb hD
  have hμn : ‖star (matchedA e)‖ ≤ 1 := by
    rw [norm_star, BlockBand.Layers.norm_matchedA he.le]
  obtain ⟨hFR, hm⟩ := H W hW _ hF (star (matchedA e)) hVμ hμn (by rw [hχeq]; exact hχ)
  rw [hχeq] at hm
  exact ⟨⟨hF, hnb, hFR⟩, hm⟩

/-- **The good event, pointwise**: the density-scale and frame-covariance conditions. -/
theorem collarGood_of_bounds {b e : ℝ} (hb : b < 1 / 2) (he : |e| < 2) (hW : 0 < W)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {J : Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hJ : Jᴴ * J = 1) {ω₁ : LayerSample W .common}
    (hA : ∀ k, (ω₁.1 k).IsHermitian) (hD : IsUnit (Collar.Density.collarTopBlock e X ω₁).det)
    {A r₀ s₀ v₀ ε k R : ℝ} (hFC : FreshClass (collarF e X ω₁) A (1 - 2 * b) 0 r₀ s₀ v₀)
    (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hv₀ : 0 < v₀)
    (hk : ‖freshDyson (collarF e X ω₁) (1 - 2 * b) ((0 : ℝ) : ℂ) - star (matchedA e)‖ ≤ k)
    (hkε : k ≤ Real.pi * ε) (hL : ‖commonPortL b e X ω₁‖ ^ 2 ≤ R)
    (hcov : collarLambda W b e * ((2 * (k / v₀) + (k / v₀) ^ 2) * R) ≤ ε / 3)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hf : ∀ i j : Fin r, collarLambda W b e *
      ‖star (fun x => J x i) ⬝ᵥ ((commonPortLL b e X ω₁ - M) *ᵥ fun x => J x j)‖ ≤ ε / 3)
    (hM : collarLambda W b e * ‖M - ((commonPortGamma b : ℝ) : ℂ) •
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ ε / 3) :
    CollarGood b e X J A r₀ s₀ v₀ ε ω₁ := by
  have hc : 0 < 1 - 2 * b := by linarith
  have h0 : (⟨0, 0⟩ : ℂ) = ((0 : ℝ) : ℂ) := by apply Complex.ext <;> simp
  have hreg := (hFC.2.2 (1 - 2 * b) ⟨by linarith, le_rfl⟩ 0 (by simp; exact hr₀.le) 0
    ⟨le_rfl, zero_le_one⟩)
  rw [h0] at hreg
  have hpi := Real.pi_pos
  refine ⟨hFC, fun i j => ?_, ?_⟩
  · have hlam := collarLambda_mul_gamma hW hb he
    have h := collarCov_entry_le hb he hX hJ hA hD hv₀ hreg.1 hk M (commonPortGamma b) hlam i j
    refine h.trans ?_
    have hk0 : 0 ≤ k := (norm_nonneg _).trans hk
    have hl0 := collarLambda_nonneg W (e := e) hb
    have hT : (2 * (k / v₀) + (k / v₀) ^ 2) * ‖commonPortL b e X ω₁‖ ^ 2 ≤
        (2 * (k / v₀) + (k / v₀) ^ 2) * R :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have := mul_le_mul_of_nonneg_left hT hl0
    have := hf i j
    nlinarith
  · unfold unfoldingDensity
    rw [semicircleDensity_eq_im, ← sub_div, abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    have h1 : |(star (matchedA e)).im - (freshDyson (collarF e X ω₁) (1 - 2 * b)
        ((0 : ℝ) : ℂ)).im| ≤ k := by
      rw [abs_sub_comm, ← Complex.sub_im]
      exact (Complex.abs_im_le_norm _).trans hk
    linarith

end BlockBand.Critical.MatrixClosing.Poles
