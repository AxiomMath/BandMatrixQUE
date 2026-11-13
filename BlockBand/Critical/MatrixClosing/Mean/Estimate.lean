module

public import BlockBand.Critical.MatrixClosing.Mean.Form
public import BlockBand.Critical.MatrixClosing.Mean.Window
public import BlockBand.Critical.MatrixClosing.Mean.Tail
public import BlockBand.Critical.MatrixClosing.Mean.Limit
public import BlockBand.Critical.MatrixClosing.Reduction

/-!
# Matrix closing, mean clause: the quantitative collar mean

*Law.* `collarLaw W b`, `0 < b < 1/2`; deterministic Hermitian `X` with `d(X) ≤ d₁` (no norm
bound), orthonormal frame `J` (`Jᴴ J = 1`), `e ∈ bulkInterval κ`, any `κ > 0`.

**`collarMean_estimate`**: `ω ↦ Re v*Im F_W(iY)v` is integrable and, for every `σ ∈ (0, s₀]`,
`|E Re v*Im F_W(iY)v - ‖v‖²| ≤ (π/η)‖v‖²(C(d(X) + ε_W) + Bσ + ν(1+σ⁻²)C₂)`, `ν = Y/(Wρ(e))`.
Proof: `ofReal_re_quad_imPart` and `lintegral_spectralSum_eq` give
`E = (π/η)∫P_ν ρ`, `ρ = meanDensity`; the window `meanDensity_two_sided` (bulk
`min κ 1`), the tail `lintegral_spectralSum_one_le` and
`lintegral_cauchyKernel_two_sided_enn` bound `∫P_νρ`; `(π/η)(η/π)‖v‖² = ‖v‖²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Critical.Herglotz
open CoareaNative.BlockBand (matrixImaginaryPart)
open scoped ENNReal NNReal ComplexOrder

variable {W : ℕ}

theorem sum_norm_sq_frame_mulVec {r : ℕ} {J : Matrix (Fin 2 × Fin W) (Fin r) ℂ}
    (hJ : Jᴴ * J = 1) (v : Fin r → ℂ) : ∑ a, ‖(J *ᵥ v) a‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [← BlockBand.Wegner.re_star_dotProduct_self, ← BlockBand.Wegner.re_star_dotProduct_self,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hJ, one_mulVec]

theorem toReal_mem_of_two_sided {I : ℝ≥0∞} {lo hi : ℝ} (hlo : ENNReal.ofReal lo ≤ I)
    (hhi : I ≤ ENNReal.ofReal hi) (hhi0 : 0 ≤ hi) : lo ≤ I.toReal ∧ I.toReal ≤ hi := by
  have hfin : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  refine ⟨?_, ENNReal.toReal_le_of_le_ofReal hhi0 hhi⟩
  rcases le_or_gt lo 0 with h | h
  · exact h.trans ENNReal.toReal_nonneg
  · exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hlo

/-- **The quantitative collar mean** (hypothesis 2, before the limit). For `0 < b < 1/2`,
`κ > 0` there are `d₁ > 0`, `C, B, C₂ ≥ 0`, `s₀ > 0`, `ε_W → 0`, `W₀` such that for `W ≥ W₀`,
`e ∈ bulkInterval κ`, Hermitian `X` with `d(X) ≤ d₁`, every orthonormal frame `J`, every `v` and
`Y > 0`: `ω ↦ Re v*Im F_W(iY)v` is integrable under `collarLaw W b` and for `0 < σ ≤ s₀`
`|E Re v*Im F_W(iY)v - ‖v‖²| ≤ (π/η)‖v‖²(C(d(X) + ε_W) + Bσ + ν(1+σ⁻²)C₂)`, `ν = Y/(Wρ(e))`. -/
theorem collarMean_estimate (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : BlockBand.Internal.Contracts.Layers.TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ (d₁ C B s₀ C₂ : ℝ) (ε : ℕ → ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ 0 ≤ B ∧ 0 < s₀ ∧ 0 ≤ C₂ ∧
      Tendsto ε atTop (𝓝 0) ∧ (∀ W, 0 ≤ ε W) ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ e ∈ bulkInterval κ, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        matchedDistance b e X ≤ d₁ → ∀ (r : ℕ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ),
        Jᴴ * J = 1 → ∀ (v : Fin r → ℂ) (Y : ℝ), 0 < Y →
          Integrable (fun ω => (star v ⬝ᵥ (matrixImaginaryPart ((collarFunction b e X J ω).eval
            ((Y : ℂ) * Complex.I)) *ᵥ v)).re) (collarLaw W b) ∧
          ∀ σ : ℝ, 0 < σ → σ ≤ s₀ →
            |∫ ω, (star v ⬝ᵥ (matrixImaginaryPart ((collarFunction b e X J ω).eval
                ((Y : ℂ) * Complex.I)) *ᵥ v)).re ∂collarLaw W b - ∑ i, ‖v i‖ ^ 2| ≤
              Real.pi / (boundaryZ b e).im * (∑ i, ‖v i‖ ^ 2) *
                (C * (matchedDistance b e X + ε W) + B * σ +
                  Y / poleScale W e * (1 + σ⁻¹ ^ 2) * C₂) := by
  set κ₁ : ℝ := min κ 1
  have hκ₁ : 0 < κ₁ := lt_min hκ one_pos
  obtain ⟨d₁, C, B, s₀, ε, W₀, hd₁, hC, hB, hs₀, hε, hε0, hwin⟩ :=
    meanDensity_two_sided hP hPD hCM hTM source hb0 hb hκ₁ (min_le_right _ _)
  obtain ⟨C₁, W₁, hC₁, htail⟩ := lintegral_spectralSum_one_le hCM hb0 hb hκ
  have hpi := Real.pi_pos
  refine ⟨d₁, C, B, s₀, Real.pi⁻¹ + C₁, ε, max W₀ W₁, hd₁, hC, hB, hs₀, by positivity, hε, hε0,
    ?_⟩
  intro W hW hW₀ e he X hX hd r J hJ v Y hY
  have he₁ : e ∈ bulkInterval κ₁ := Collar.Density.bulkInterval_mono (min_le_left _ _) he
  have hη := boundaryZ_im_pos hb hκ he
  have hp := poleScale_pos hW hκ he
  set η := (boundaryZ b e).im
  set ν := Y / poleScale W e with hνdef
  have hν : 0 < ν := div_pos hY hp
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hη1 : η ≤ 1 := Collar.Density.boundaryZ_im_le_one' hb0.le (by linarith) he2
  set q := J *ᵥ v
  set nq := ∑ i, ‖v i‖ ^ 2 with hnqdef
  have hnq : 0 ≤ nq := by positivity
  have hq : ∑ a, ‖q a‖ ^ 2 = nq := sum_norm_sq_frame_mulVec hJ v
  set u := (matchedLeadK b e X)ᴴ *ᵥ q
  set g : CollarSample W → ℝ := fun ω => (star v ⬝ᵥ (matrixImaginaryPart
    ((collarFunction b e X J ω).eval ((Y : ℂ) * Complex.I)) *ᵥ v)).re with hgdef
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => re_quad_imPart_nonneg hη hp hY X J ω v
  have hgm : Measurable g := by
    have h : g = fun ω => Real.pi / η * (spectralSum (cauchyKernel ν) e X u ω).toReal := by
      funext ω; exact re_quad_imPart_eq_toReal hη hp hY X J ω v
    rw [h]
    exact measurable_const.mul
      (measurable_spectralSum (measurable_cauchyKernel ν) e X u).ennreal_toReal
  -- the extended-real identity
  set I := ∫⁻ s, ENNReal.ofReal (cauchyKernel ν s) * meanDensity W b e X u s with hIdef
  have hL : ∫⁻ ω, ENNReal.ofReal (g ω) ∂collarLaw W b = ENNReal.ofReal (Real.pi / η) * I := by
    have h1 : ∀ ω, ENNReal.ofReal (g ω) = ENNReal.ofReal (Real.pi / η) *
        spectralSum (cauchyKernel ν) e X u ω := fun ω => ofReal_re_quad_imPart hη hp hY X J ω v
    simp_rw [h1]
    rw [lintegral_const_mul _ (measurable_spectralSum (measurable_cauchyKernel ν) e X u),
      lintegral_spectralSum_eq hW hb e hX u (measurable_cauchyKernel ν)
        (cauchyKernel_nonneg hν.le)]
  -- the tail
  have hT : ∫⁻ s, ENNReal.ofReal (cauchyKernel 1 s) * meanDensity W b e X u s ≤
      ENNReal.ofReal (C₁ * nq) := by
    rw [← lintegral_spectralSum_eq hW hb e hX u (measurable_cauchyKernel 1)
      (cauchyKernel_nonneg zero_le_one), ← hq]
    exact htail W hW (le_of_max_le_right hW₀) e he X hX q
  -- the window, for every `σ ≤ s₀`
  set c : ℝ := η / Real.pi * nq with hc
  have hc0 : 0 ≤ c := by positivity
  have hbounds : ∀ σ : ℝ, 0 < σ → σ ≤ s₀ →
      ENNReal.ofReal (c - (C * (matchedDistance b e X + ε W) + B * σ) * nq -
          ν * (1 + σ⁻¹ ^ 2) * c) ≤ I ∧
        I ≤ ENNReal.ofReal (c + (C * (matchedDistance b e X + ε W) + B * σ) * nq +
          ν * (1 + σ⁻¹ ^ 2) * (C₁ * nq)) := by
    intro σ hσ hσs
    have hA0 : 0 ≤ (C * (matchedDistance b e X + ε W) + B * σ) * nq := by
      have : 0 ≤ matchedDistance b e X := le_max_of_le_left (norm_nonneg _); have := hε0 W; positivity
    refine lintegral_cauchyKernel_two_sided_enn hc0 hA0 hσ hν (by positivity) (fun s hs => ?_) hT
    obtain ⟨h1, h2⟩ := hwin W hW (le_of_max_le_left hW₀) e he₁ X hX hd q s (hs.trans hσs)
    rw [hq] at h1 h2
    have hBs : B * |s| * nq ≤ B * σ * nq :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hB) hnq
    constructor
    · refine (ENNReal.ofReal_le_ofReal ?_).trans h1
      simp only [c]; nlinarith
    · refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [c]; nlinarith
  -- integrability and the integral
  have hfin : ∫⁻ ω, ENNReal.ofReal (g ω) ∂collarLaw W b ≠ ⊤ := by
    rw [hL]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbounds s₀ hs₀ le_rfl).2)
  have hint : Integrable g (collarLaw W b) :=
    ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall hg0)).2 (lt_top_iff_ne_top.2 hfin)⟩
  refine ⟨hint, fun σ hσ hσs => ?_⟩
  have hEq : ∫ ω, g ω ∂collarLaw W b = Real.pi / η * I.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable,
      hL, ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_pos hpi hη).le]
  obtain ⟨hlo, hhi⟩ := hbounds σ hσ hσs
  have hA0 : 0 ≤ (C * (matchedDistance b e X + ε W) + B * σ) * nq := by
    have : 0 ≤ matchedDistance b e X := le_max_of_le_left (norm_nonneg _); have := hε0 W; positivity
  have hk0 : 0 ≤ ν * (1 + σ⁻¹ ^ 2) := by positivity
  obtain ⟨hlo', hhi'⟩ := toReal_mem_of_two_sided hlo hhi (by positivity)
  change |∫ ω, g ω ∂collarLaw W b - nq| ≤ _
  rw [hEq]
  have hpc : Real.pi / η * c = nq := by simp only [c]; field_simp
  have hcle : c ≤ Real.pi⁻¹ * nq := by
    simp only [c]
    rw [div_eq_mul_inv, mul_comm η]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (inv_nonneg.2 hpi.le) hη1) hnq
  have hpe : 0 ≤ Real.pi / η := (div_pos hpi hη).le
  set A := (C * (matchedDistance b e X + ε W) + B * σ) * nq
  set k := ν * (1 + σ⁻¹ ^ 2)
  have hkc : k * c ≤ k * ((Real.pi⁻¹ + C₁) * nq) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hk0
  have hkT : k * (C₁ * nq) ≤ k * ((Real.pi⁻¹ + C₁) * nq) :=
    mul_le_mul_of_nonneg_left (by nlinarith [inv_nonneg.2 hpi.le]) hk0
  have hfinal : Real.pi / η * (A + k * ((Real.pi⁻¹ + C₁) * nq)) =
      Real.pi / η * nq * (C * (matchedDistance b e X + ε W) + B * σ +
        k * (Real.pi⁻¹ + C₁)) := by
    simp only [A, k]; ring
  rw [← hfinal, abs_le]
  have e2 : Real.pi / η * (A + k * ((Real.pi⁻¹ + C₁) * nq)) =
      Real.pi / η * A + Real.pi / η * (k * ((Real.pi⁻¹ + C₁) * nq)) := by ring
  rw [e2]
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hlo' hpe
    have e1 : Real.pi / η * (c - A - k * c) = nq - Real.pi / η * A - Real.pi / η * (k * c) := by
      rw [← hpc]; ring
    have h2 := mul_le_mul_of_nonneg_left hkc hpe
    rw [e1] at h1
    linarith only [h1, h2]
  · have h1 := mul_le_mul_of_nonneg_left hhi' hpe
    have e1 : Real.pi / η * (c + A + k * (C₁ * nq)) =
        nq + Real.pi / η * A + Real.pi / η * (k * (C₁ * nq)) := by
      rw [← hpc]; ring
    have h2 := mul_le_mul_of_nonneg_left hkT hpe
    rw [e1] at h1
    linarith only [h1, h2]

end BlockBand.Critical.MatrixClosing.Mean
