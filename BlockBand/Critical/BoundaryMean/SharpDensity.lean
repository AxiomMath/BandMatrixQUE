module

public import BlockBand.Critical.Collar.Density.TwoSidedDensity
public import BlockBand.Critical.BoundaryMean.CauchyWindow
public import BlockBand.Critical.BoundaryMean.Statement

/-!
# `HermitianCollarMeanStatement`: the sharp collar density in two-sided resolvent form

The sharp collar density estimate of the exact boundary-mean theorem, at `s = 0` and uniformly
in the energy, converted to two-sided resolvent form through a window and a Cauchy tail; proved
from the listed inputs.

*Law.* `collarLaw W b`, `0 < b < 1/2`; deterministic Hermitian `X` (no norm bound);
`e ∈ bulkInterval κ`, every `κ > 0`.

* `measurable_im_collarRowForm`, `hermitianCollarForm_eq`:
  `h_ν(X, q) = π ∫ P_ν(-x) ρ_q(x) dx` with `ρ_q(x) = q*(K_X - x)Ψ_X(x)(K_X - x)*q`
  (`Density.lintegral_cauchyKernel_collarWeightedForm` at `z = z_b`; `Im⟨y,(ℋ-iν)⁻¹y⟩ ≥ 0` a.s.).
* `window_arith_hermitian`, `final_arith_hermitian`: scalar bookkeeping.
* **`hermitianCollarMean_holds`**: `HermitianCollarMeanStatement`, from `FreshPalmContract`,
  `PointDensityContract`, `CommonPortMeanContract`, `TraceMatrixContract`, `PSSS.SourceContract`.
  Constants: `κ₁ = min(κ,1)`, `κ_P = κ₁/2`; `(d_P, C_P, ε_P, W_P)` from
  `Density.collarDensity_two_sided` at `κ_P`; then `ε = ε_P`, `C = πC_P`, `d₂ = d_P/2`, `W₀ = W_P`.
  For `δ > 0`: window `σ = min(s₀, δ/(2π(C₂+1)))`, `ν₀ = δ/(2(1+σ⁻²)(C_row+1))`,
  `C_row = 2·25 + 2(1-2b) + b`; `ν₀` depends on `(b, κ, δ)` only (uniform in `W`, `e`, `X`, `q`).
  Window `|x| ≤ σ`: `Ψ^{(e)}_X(x) = Ψ^{(e+x)}_X(0)` (`collarDensity_energy_shift`, both diagonal
  blocks shifted), weight `z_b(e) - x` at energy `e + x` (`‖· - z_b(e+x)‖ ≤ (L_z+1)|x|`),
  `d_{e+x}(X) ≤ d_e(X) + L_d|x|`, `|η(e+x) - η(e)| ≤ L_z|x|`. Tail: `P_ν ≤ ν(1+σ⁻²)P₁` and the
  `W`-uniform fresh-row mass `∫P₁ρ_q ≤ π⁻¹C_row‖q‖²` (`lintegral_collarRowForm_I_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Density
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem measurable_im_collarRowForm (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (s w : ℂ) (q : Fin 2 × Fin W → ℂ) :
    Measurable fun ω : CollarSample W => (star (collarRowVec w q ω) ⬝ᵥ
      ((collarMatrix e X ω - s • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
        collarRowVec w q ω)).im := by
  have hM : Measurable fun ω : CollarSample W =>
      (collarMatrix e X ω - s • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ :=
    (BlockBand.Wegner.measurable_matrix_inv (n := LayerSite W .common)).comp
      (measurable_matrix_of_entries fun i j => ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp (measurable_collarMatrix e X))).sub measurable_const)
  have hcont : Continuous fun p : Matrix (LayerSite W .common) (LayerSite W .common) ℂ ×
      (LayerSite W .common → ℂ) => (star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).im :=
    Complex.continuous_im.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd))
  exact hcont.measurable.comp (hM.prodMk (measurable_collarRowVec w q))

/-- `h_ν(X, q) = π ∫ P_ν(-x) ρ_q(x) dx` (`Density.lintegral_cauchyKernel_collarWeightedForm`,
`z = z_b`), as a real number. -/
theorem hermitianCollarForm_eq (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {ν : ℝ} (hν : 0 < ν)
    (q : Fin 2 × Fin W → ℂ) :
    hermitianCollarForm W b e ν X q = Real.pi * (∫⁻ x, ENNReal.ofReal (cauchyKernel ν (0 - x) *
      collarWeightedForm W b e X (boundaryZ b e) q x)).toReal := by
  rw [lintegral_cauchyKernel_collarWeightedForm hW hb e hX (boundaryZ b e) q hν]
  have hw : Collar.Kernel.rowCoeff b e 0 = star (boundaryZ b e) + (e : ℂ) := by
    rw [Collar.Kernel.rowCoeff, star_add, Complex.star_def, Complex.conj_ofReal, add_zero]
  have hs : ((ν : ℂ) * Complex.I) = (⟨0, ν⟩ : ℂ) := by apply Complex.ext <;> simp
  set w := star (boundaryZ b e) + (e : ℂ)
  set g : CollarSample W → ℝ := fun ω => (star (collarRowVec w q ω) ⬝ᵥ
      ((collarMatrix e X ω - (⟨0, ν⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
        (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec w q ω)).im with hg
  have hform : hermitianCollarForm W b e ν X q = ∫ ω, g ω ∂collarLaw W b := by
    rw [hermitianCollarForm, hw, hs]
  have hg0 : 0 ≤ᵐ[collarLaw W b] g := by
    filter_upwards [ae_collarMatrix_isHermitian (W := W) b e hX] with ω hω
    exact im_dotProduct_inv_mulVec_nonneg' hω.1 (by simpa using hν) _
  rw [hform, integral_eq_lintegral_of_nonneg_ae hg0
    (measurable_im_collarRowForm e X _ w q).aestronglyMeasurable]
  have hpi := Real.pi_pos
  have h1 : ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * g ω) ∂collarLaw W b =
      ENNReal.ofReal Real.pi⁻¹ * ∫⁻ ω, ENNReal.ofReal (g ω) ∂collarLaw W b := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hpi.le)]
  simp only [hg] at h1 ⊢
  rw [h1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hpi.le), ← mul_assoc,
    mul_inv_cancel₀ hpi.ne', one_mul]

/-- The arithmetic of the energy window. -/
theorem window_arith_hermitian {ρx ηx ηe nq d dx εP δx x σ CP Ld Lz : ℝ}
    (hP : |ρx - ηx / Real.pi * nq| ≤ CP * (dx + εP + δx) * nq) (hdx : dx ≤ d + Ld * |x|)
    (hδx : δx ≤ (Lz + 1) * |x|) (hηη : |ηx - ηe| ≤ Lz * |x|) (hnq : 0 ≤ nq) (hCP : 0 ≤ CP)
    (hx : |x| ≤ σ) (hLd : 0 ≤ Ld) (hLz : 0 ≤ Lz) :
    |ρx - ηe / Real.pi * nq| ≤ (CP * (d + εP) + (CP * (Ld + Lz + 1) + Lz / Real.pi) * σ) * nq := by
  have hpi := Real.pi_pos
  have hx0 := abs_nonneg x
  have h1 : CP * (dx + εP + δx) * nq ≤ CP * (d + εP + (Ld + Lz + 1) * |x|) * nq := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCP) hnq
    nlinarith
  have h2 : |ηx / Real.pi * nq - ηe / Real.pi * nq| ≤ Lz * |x| / Real.pi * nq := by
    rw [← sub_mul, ← sub_div, abs_mul, abs_div, abs_of_pos hpi, abs_of_nonneg hnq]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hηη hpi.le) hnq
  have h3 : |ρx - ηe / Real.pi * nq| ≤ CP * (d + εP + (Ld + Lz + 1) * |x|) * nq +
      Lz * |x| / Real.pi * nq := by
    calc |ρx - ηe / Real.pi * nq| = |(ρx - ηx / Real.pi * nq) +
          (ηx / Real.pi * nq - ηe / Real.pi * nq)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hP.trans h1) h2)
  have h4 : CP * (d + εP + (Ld + Lz + 1) * |x|) * nq + Lz * |x| / Real.pi * nq ≤
      (CP * (d + εP) + (CP * (Ld + Lz + 1) + Lz / Real.pi) * σ) * nq := by
    have e : CP * (d + εP + (Ld + Lz + 1) * |x|) * nq + Lz * |x| / Real.pi * nq =
        (CP * (d + εP) + (CP * (Ld + Lz + 1) + Lz / Real.pi) * |x|) * nq := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hnq
    have h5 : 0 ≤ CP * (Ld + Lz + 1) + Lz / Real.pi := by positivity
    linarith [mul_le_mul_of_nonneg_left hx h5]
  exact h3.trans h4

/-- The final arithmetic: from the two-sided bounds on `t = ∫P_νρ`. -/
theorem final_arith_hermitian {t c Aw T₁ ν k η nq δ CP d εP C₂ σ Crow : ℝ} (hnq : 0 ≤ nq)
    (hc : c = η / Real.pi * nq) (hη1 : η ≤ 1)
    (hAw : Aw = (CP * (d + εP) + C₂ * σ) * nq) (hT₁ : T₁ = Real.pi⁻¹ * (Crow * nq))
    (hlo : c - Aw - ν * k * c ≤ t) (hhi : t ≤ c + Aw + ν * k * T₁) (hν : 0 ≤ ν) (hk : 0 ≤ k)
    (hCrow : 0 ≤ Crow) (hσ : Real.pi * C₂ * σ ≤ δ / 2) (hνk : ν * k * (Crow + 1) ≤ δ / 2) :
    |Real.pi * t - η * nq| ≤ (Real.pi * CP * (d + εP) + δ) * nq := by
  have hpi := Real.pi_pos
  have e1 : Real.pi * c = η * nq := by rw [hc]; field_simp
  have e2 : Real.pi * Aw = Real.pi * CP * (d + εP) * nq + Real.pi * C₂ * σ * nq := by
    rw [hAw]; ring
  have e3 : Real.pi * (ν * k * T₁) = ν * k * Crow * nq := by rw [hT₁]; field_simp
  have e4 : Real.pi * (ν * k * c) = ν * k * η * nq := by rw [hc]; field_simp
  have h1 : Real.pi * C₂ * σ * nq ≤ δ / 2 * nq := mul_le_mul_of_nonneg_right hσ hnq
  have h2 : ν * k * Crow * nq ≤ δ / 2 * nq := by
    refine mul_le_mul_of_nonneg_right (le_trans ?_ hνk) hnq
    have : 0 ≤ ν * k := mul_nonneg hν hk
    nlinarith
  have h3 : ν * k * η * nq ≤ δ / 2 * nq := by
    refine mul_le_mul_of_nonneg_right (le_trans ?_ hνk) hnq
    have : 0 ≤ ν * k := mul_nonneg hν hk
    nlinarith
  have hlo' := mul_le_mul_of_nonneg_left hlo hpi.le
  have hhi' := mul_le_mul_of_nonneg_left hhi hpi.le
  rw [mul_sub, mul_sub, e1, e2, e4] at hlo'
  rw [mul_add, mul_add, e1, e2, e3] at hhi'
  rw [abs_le]
  constructor
  · have : (Real.pi * CP * (d + εP) + δ) * nq =
        Real.pi * CP * (d + εP) * nq + δ / 2 * nq + δ / 2 * nq := by ring
    linarith
  · have : (Real.pi * CP * (d + εP) + δ) * nq =
        Real.pi * CP * (d + εP) * nq + δ / 2 * nq + δ / 2 * nq := by ring
    linarith

set_option maxHeartbeats 1000000 in

/-- **`HermitianCollarMeanStatement`** (the sharp collar density, two-sided
resolvent form), from the inputs `FreshPalmContract`, `PointDensityContract`,
`CommonPortMeanContract`, `TraceMatrixContract` and the native `PSSS.SourceContract`. -/
theorem hermitianCollarMean_holds (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) : HermitianCollarMeanStatement := by
  intro b hb0 hb κ hκ
  set κ₁ : ℝ := min κ 1 with hκ₁def
  have hκ₁ : 0 < κ₁ := lt_min hκ one_pos
  set κP : ℝ := κ₁ / 2 with hκPdef
  have hκP : 0 < κP := by positivity
  have hκP1 : κP ≤ 1 := by
    have := min_le_right κ 1; rw [hκPdef]; linarith
  obtain ⟨dP, CP, εP, WP, hdP, hCP, hεP, hεP0, hPd⟩ :=
    collarDensity_two_sided hP hPD hCM hTM source hb0 hb hκP hκP1
  have hm4 : 0 < 4 - (2 - κP) ^ 2 := BlockBand.Layers.four_sub_sq_pos hκP (by linarith)
  have hsq : 0 < Real.sqrt (4 - (2 - κP) ^ 2) := Real.sqrt_pos.2 hm4
  set La : ℝ := 1 / 2 + 1 / Real.sqrt (4 - (2 - κP) ^ 2)
  have hLa : 0 < La := by positivity
  set Lz : ℝ := 1 + (1 - b) * La
  have hLz : 0 < Lz := by have : 0 < 1 - b := by linarith
                          positivity
  set η : ℝ := (1 - b) * Real.sqrt (4 - (2 - κP) ^ 2) / 2
  have hη : 0 < η := by have : 0 < 1 - b := by linarith
                        positivity
  set Ld : ℝ := Lz / η ^ 2 + La
  have hLd : 0 < Ld := by positivity
  set s₀ : ℝ := min (κ₁ / 2) (min (1 / (Lz + 1)) (dP / (2 * Ld)))
  have hs₀ : 0 < s₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hpi := Real.pi_pos
  set C₂ : ℝ := CP * (Ld + Lz + 1) + Lz / Real.pi
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨εP, Real.pi * CP, dP / 2, WP, hεP, by positivity, ?_⟩
  intro W hW hW₀ e he δ hδ
  set σ : ℝ := min s₀ (δ / (2 * Real.pi * (C₂ + 1))) with hσdef
  have hσ : 0 < σ := lt_min hs₀ (by positivity)
  set Crow : ℝ := 2 * 25 + 2 * (1 - 2 * b) + b
  have hCrow : 0 ≤ Crow := by have : 0 ≤ 1 - 2 * b := by linarith
                              positivity
  set k : ℝ := 1 + σ⁻¹ ^ 2
  have hk : 0 < k := by positivity
  refine ⟨δ / (2 * k * (Crow + 1)), by positivity, ?_⟩
  rintro ν ⟨hν, hνlt⟩ X hX hd q
  set z := boundaryZ b e with hz
  set d := matchedDistance b e X with hddef
  have hd0 : 0 ≤ d := le_max_of_le_left (norm_nonneg _)
  set nq := ∑ x, ‖q x‖ ^ 2 with hnqdef
  have hnq : 0 ≤ nq := by positivity
  set ρ := collarWeightedForm W b e X z q with hρ
  set c : ℝ := z.im / Real.pi * nq with hc
  set Aw : ℝ := (CP * (d + εP W) + C₂ * σ) * nq with hAw
  have hεPW := hεP0 W
  have hAw0 : 0 ≤ Aw := by positivity
  have he₁ : e ∈ bulkInterval κ₁ := bulkInterval_mono (min_le_left _ _) he
  have heP : e ∈ bulkInterval κP := bulkInterval_mono (by rw [hκPdef]; linarith) he₁
  have hηE : ∀ E ∈ bulkInterval κP, η ≤ (boundaryZ b E).im := fun E hE =>
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (by linarith) hκP hE).2
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκP heP).le
  have hηe0 : 0 ≤ z.im := hη.le.trans (hηE e heP)
  have hηe1 : z.im ≤ 1 := boundaryZ_im_le_one' hb0.le (by linarith) he2
  -- the window
  have hwin : ∀ x, |x| ≤ σ → |ρ x - c| ≤ Aw := by
    intro x hx
    have hxs : |x| ≤ s₀ := hx.trans (min_le_left _ _)
    have hmem : e + x ∈ bulkInterval κP := bulkInterval_add_mem he₁ (hxs.trans (min_le_left _ _))
    have hzx : ‖z - boundaryZ b (e + x)‖ ≤ Lz * |x| := by
      have := norm_boundaryZ_sub_le (b := b) (by linarith) hκP heP hmem
      rwa [show e - (e + x) = -x by ring, abs_neg] at this
    have hdx : matchedDistance b (e + x) X ≤ d + Ld * |x| := by
      have h1 := matchedDistance_le_energy (b := b) hW hX (hη.trans_le (hηE e heP))
        (hη.trans_le (hηE _ hmem))
      have h2 : ‖matchedA (e + x) - matchedA e‖ ≤ La * |x| := by
        have := norm_matchedA_sub_le hκP hmem heP
        rwa [show e + x - e = x by ring] at this
      have h3 : ((boundaryZ b (e + x)).im * (boundaryZ b e).im)⁻¹ ≤ (η ^ 2)⁻¹ := by
        rw [sq]
        exact inv_anti₀ (by positivity) (mul_le_mul (hηE _ hmem) (hηE e heP) hη.le
          (hη.le.trans (hηE _ hmem)))
      have h5 : ‖boundaryZ b e - boundaryZ b (e + x)‖ *
          ((boundaryZ b (e + x)).im * (boundaryZ b e).im)⁻¹ ≤ Lz * |x| * (η ^ 2)⁻¹ :=
        mul_le_mul hzx h3 (inv_nonneg.2 (mul_pos (hη.trans_le (hηE _ hmem))
          (hη.trans_le (hηE e heP))).le) (mul_nonneg hLz.le (abs_nonneg _))
      have h6 : Lz * |x| * (η ^ 2)⁻¹ + La * |x| = Ld * |x| := by
        simp only [Ld]; field_simp
      linarith only [h1, h2, h5, h6]
    have hdxP : matchedDistance b (e + x) X ≤ dP := by
      have h1 : |x| ≤ dP / (2 * Ld) := hxs.trans ((min_le_right _ _).trans (min_le_right _ _))
      have h2 : Ld * |x| ≤ dP / 2 := by
        rw [le_div_iff₀ (by positivity)] at h1; linarith only [h1]
      linarith only [hdx, h2, hd]
    have hw : ‖(z - (x : ℂ)) - boundaryZ b (e + x)‖ ≤ (Lz + 1) * |x| := by
      have e1 : (z - (x : ℂ)) - boundaryZ b (e + x) = (z - boundaryZ b (e + x)) - (x : ℂ) := by
        ring
      rw [e1]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith only [hzx]
    have hw1 : (Lz + 1) * |x| ≤ 1 := by
      have h1 : |x| ≤ 1 / (Lz + 1) := hxs.trans ((min_le_right _ _).trans (min_le_left _ _))
      calc (Lz + 1) * |x| ≤ (Lz + 1) * (1 / (Lz + 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = 1 := by field_simp
    have hform : ρ x = quadForm (collarDensity W b (e + x) X 0)
        (((z - (x : ℂ)) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)ᴴ *ᵥ q) := by
      have hK : z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X - (x : ℂ) • 1 =
          (z - (x : ℂ)) • 1 - X := by rw [sub_smul]; abel
      rw [hρ, collarWeightedForm, collarWeightVec, collarDensity_energy_shift hW b e hX x, hK]
      rfl
    have hPx := hPd W hW hW₀ (e + x) hmem X hX hdxP (z - x) (hw.trans hw1) q
    have hηη : |(boundaryZ b (e + x)).im - z.im| ≤ Lz * |x| := by
      have := Complex.abs_im_le_norm (z - boundaryZ b (e + x))
      rw [Complex.sub_im, abs_sub_comm] at this
      exact this.trans hzx
    rw [hform]
    have := window_arith_hermitian hPx hdx hw hηη hnq hCP hx hLd.le hLz.le
    simpa only [hc, hAw] using this
  -- the Cauchy tail
  have hT : ∫⁻ x, ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) ≤
      ENNReal.ofReal (Real.pi⁻¹ * (Crow * nq)) := by
    rw [hρ, lintegral_cauchyKernel_collarWeightedForm hW hb e hX z q one_pos]
    refine (lintegral_collarRowForm_I_le hW hb0 hb e hX (star z + e) q).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hw5 : ‖star z + (e : ℂ)‖ ≤ 5 := by
      have hz3 := BlockBand.Layers.norm_boundaryZ_le hb0.le (by linarith) he2
      calc ‖star z + (e : ℂ)‖ ≤ ‖star z‖ + ‖(e : ℂ)‖ := norm_add_le _ _
        _ ≤ 3 + 2 := by
            rw [norm_star, Complex.norm_real, Real.norm_eq_abs]
            exact add_le_add hz3 he2
        _ = 5 := by norm_num
    have hw25 : ‖star z + (e : ℂ)‖ ^ 2 ≤ 25 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hw5 2
      norm_num at this
      exact this
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hnq) (by positivity)
    simp only [Crow]
    linarith only [hw25]
  obtain ⟨hlo, hhi⟩ := lintegral_cauchyKernel_two_sided
    (collarWeightedForm_nonneg hW b e hX z q) (by positivity : 0 ≤ c) hAw0
    (by positivity : 0 ≤ Real.pi⁻¹ * (Crow * nq)) hσ hν hwin hT
  set L := ∫⁻ x, ENNReal.ofReal (cauchyKernel ν (0 - x) * ρ x) with hL
  have hLfin : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hup : L.toReal ≤ c + Aw + ν * k * (Real.pi⁻¹ * (Crow * nq)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hhi
  have hdown : c - Aw - ν * k * c ≤ L.toReal := by
    rcases le_or_gt (c - Aw - ν * k * c) 0 with h | h
    · exact h.trans ENNReal.toReal_nonneg
    · exact (ENNReal.ofReal_le_iff_le_toReal hLfin).1 hlo
  have hEq := hermitianCollarForm_eq hW hb e hX hν q
  rw [hEq]
  have hσδ : Real.pi * C₂ * σ ≤ δ / 2 := by
    have h1 : σ ≤ δ / (2 * Real.pi * (C₂ + 1)) := min_le_right _ _
    have h2 : Real.pi * C₂ * σ ≤ Real.pi * (C₂ + 1) * σ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hpi.le) hσ.le
    have h3 : Real.pi * (C₂ + 1) * σ ≤ Real.pi * (C₂ + 1) * (δ / (2 * Real.pi * (C₂ + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : Real.pi * (C₂ + 1) * (δ / (2 * Real.pi * (C₂ + 1))) = δ / 2 := by
      field_simp
    linarith only [h2, h3, h4]
  have hνk : ν * k * (Crow + 1) ≤ δ / 2 := by
    have h1 : ν * k * (Crow + 1) ≤ δ / (2 * k * (Crow + 1)) * k * (Crow + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hνlt.le hk.le) (by positivity)
    have h2 : δ / (2 * k * (Crow + 1)) * k * (Crow + 1) = δ / 2 := by field_simp
    linarith only [h1, h2]
  have key := final_arith_hermitian (t := L.toReal) hnq hc hηe1 hAw rfl hdown hup hν.le hk.le
    hCrow hσδ hνk
  calc _ ≤ (Real.pi * CP * (d + εP W) + δ) * nq := key
    _ = _ := by ring

end BlockBand.Critical.BoundaryMean
