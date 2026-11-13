module

public import BlockBand.Critical.MatrixClosing.Mean.Spectral
public import BlockBand.Critical.Collar.Density.TwoSidedDensity
public import BlockBand.Critical.MatrixClosing.MiddleShift.Params

/-!
# Matrix closing, mean clause: the shifted weighted density (two-sided)

*Law.* `layerLaw W b .common`, `0 < b < 1/2`; deterministic Hermitian `X` (no norm bound);
`e ∈ bulkInterval κ`, `0 < κ ≤ 1`.

* `meanDensity_eq_cond`: `meanDensity(s)` is the conditional density at `(e + s, X - s)`.
* **`meanDensity_two_sided`**: for `|s| ≤ s₀`, `d(X) ≤ d₁`, every `q`,
  `E_{A,B} q*KTΣ_F(s)T*K*q = (η/π)‖q‖² ± (C(d(X) + ε_W) + B|s|)‖q‖²`, `K = z_b - X`.
  Proof: `Collar.Density.lintegral_condCollarDensity_two_sided` at `(e + s, X - s)` (bulk `κ/2`),
  the weight change `z_b(e) - s ↦ z_b(e + s)` (`weight_change`, `weight_change_two_sided`),
  `d_{e+s}(X - s) ≤ d_e(X) + L|s|` (`matchedDistance_shift_le`) and `density_budget`.

Hypotheses: `FreshPalmContract`, `PointDensityContract`, `CommonPortMeanContract`,
`TraceMatrixContract`, `PSSS.SourceContract` (those of `lintegral_condCollarDensity_two_sided`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open scoped ENNReal NNReal ComplexOrder

variable {W : ℕ}

/-- The integrand of `meanDensity` at `s` is the conditional density `condCollarDensity` at
`(e + s, X - s)`. -/
theorem meanDensity_eq_cond (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e s : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (u : Fin 2 × Fin W → ℂ) :
    meanDensity W b e X u s = ∫⁻ ω, ENNReal.ofReal (quadForm
      (Collar.Density.condCollarDensity b (e + s) (X - (s : ℂ) • 1) ω) u)
        ∂layerLaw W b .common := by
  unfold meanDensity
  refine lintegral_congr_ae ((BlockBand.Layers.lct_ae_blocks_isHermitian W b .common).mono
    fun ω hA => ?_)
  dsimp only
  rw [condCollarDensity_middle hW hb e s hX hA]
  have h := quadForm_conjTranspose_mul_mul (Collar.Density.collarTW e X ω)ᴴ
    (sigma (Collar.Density.collarFW e X ω) (1 - 2 * b) s) u
  rw [conjTranspose_conjTranspose] at h
  rw [h]

/-- **The shifted weighted density, two-sided, for the middle-shifted density.** For
`0 < κ ≤ 1` there are `d₁ > 0`, `C, B ≥ 0`, `s₀ > 0`, `ε_W → 0` and `W₀` such that for `W ≥ W₀`,
`e ∈ bulkInterval κ`, Hermitian `X` with `d(X) ≤ d₁`, every `q` and `|s| ≤ s₀`,
`E_{A,B} q*KTΣ_F(s)T*K*q = (η/π)‖q‖² ± (C(d(X) + ε_W) + B|s|)‖q‖²` (`K = z_b - X`). -/
theorem meanDensity_two_sided (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : BlockBand.Internal.Contracts.Layers.TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ (d₁ C B s₀ : ℝ) (ε : ℕ → ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ 0 ≤ B ∧ 0 < s₀ ∧
      Tendsto ε atTop (𝓝 0) ∧ (∀ W, 0 ≤ ε W) ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ e ∈ bulkInterval κ, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        matchedDistance b e X ≤ d₁ → ∀ q : Fin 2 × Fin W → ℂ, ∀ s : ℝ, |s| ≤ s₀ →
          ENNReal.ofReal ((boundaryZ b e).im / Real.pi * ∑ a, ‖q a‖ ^ 2 -
              (C * (matchedDistance b e X + ε W) + B * |s|) * ∑ a, ‖q a‖ ^ 2) ≤
            meanDensity W b e X ((matchedLeadK b e X)ᴴ *ᵥ q) s ∧
          meanDensity W b e X ((matchedLeadK b e X)ᴴ *ᵥ q) s ≤
            ENNReal.ofReal ((boundaryZ b e).im / Real.pi * ∑ a, ‖q a‖ ^ 2 +
              (C * (matchedDistance b e X + ε W) + B * |s|) * ∑ a, ‖q a‖ ^ 2) := by
  set κ' : ℝ := κ / 2 with hκ'def
  have hκ' : 0 < κ' := by positivity
  have hκ'2 : κ' < 2 := by rw [hκ'def]; linarith
  obtain ⟨dS, CS, εS, WS, hdS, hCS, hεS, hεS0, hS⟩ :=
    Collar.Density.lintegral_condCollarDensity_two_sided hP hPD hCM hTM source hb0 hb hκ' hκ'2
  have hm4 : 0 < 4 - (2 - κ') ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ' (by linarith)
  have hsq : 0 < Real.sqrt (4 - (2 - κ') ^ 2) := Real.sqrt_pos.2 hm4
  set La : ℝ := 1 / 2 + 1 / Real.sqrt (4 - (2 - κ') ^ 2)
  have hLa : 0 < La := by positivity
  set Lz : ℝ := 1 + (1 - b) * La
  have hLz : 0 < Lz := by have : 0 < 1 - b := by linarith
                          positivity
  set η : ℝ := (1 - b) * Real.sqrt (4 - (2 - κ') ^ 2) / 2
  have hη : 0 < η := by have : 0 < 1 - b := by linarith
                        positivity
  set Ld : ℝ := (Lz + 1) / η ^ 2 + La
  have hLd : 0 < Ld := by positivity
  set h₀ : ℝ := min (κ / 2) (min (1 / (Lz + 1)) (dS / (2 * Ld)))
  have hh₀ : 0 < h₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set Mp : ℝ := 2 * (1 + 4 / η ^ 2)
  have hMp : 0 ≤ Mp := by positivity
  set Cη : ℝ := 4 / η + 4 / η ^ 2
  have hCη : 0 ≤ Cη := by positivity
  have hpi := Real.pi_pos
  set B₀ : ℝ := CS * Mp * Ld + Lz * Mp / Real.pi + Cη * Lz / Real.pi
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨dS / 2, CS * Mp, Cη / Real.pi + B₀, h₀, εS, WS, by positivity, by positivity,
    by positivity, hh₀, hεS, hεS0, ?_⟩
  intro W hW hW₀ e he X hX hd q s hs
  set d := matchedDistance b e X with hddef
  have hd0 : 0 ≤ d := le_max_of_le_left (norm_nonneg _)
  set nq := ∑ a, ‖q a‖ ^ 2 with hnqdef
  have hnq : 0 ≤ nq := by positivity
  set X' := X - (s : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) with hX'def
  have hX' : X'.IsHermitian := hX.sub (isHermitian_one.smul (Complex.conj_ofReal s))
  set z : ℂ := boundaryZ b e - (s : ℂ) with hzdef
  set u := (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X')ᴴ *ᵥ q with hu
  have hueq : (matchedLeadK b e X)ᴴ *ᵥ q = u := by
    rw [hu, matchedLeadK, hX'def, hzdef, sub_smul]
    congr 2
    abel
  rw [hueq, meanDensity_eq_cond hW hb e s hX u, ← hX'def]
  have he' : e ∈ bulkInterval κ' := Collar.Density.bulkInterval_mono (by rw [hκ'def]; linarith) he
  have hmem : e + s ∈ bulkInterval κ' :=
    Collar.Density.bulkInterval_add_mem he (hs.trans (min_le_left _ _))
  have hηE : ∀ E ∈ bulkInterval κ', η ≤ (boundaryZ b E).im := fun E hE =>
    (BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (by linarith) hκ' hE).2
  have hzy : ‖boundaryZ b e - boundaryZ b (e + s)‖ ≤ Lz * |s| := by
    have := Collar.Density.norm_boundaryZ_sub_le (b := b) (by linarith) hκ' he' hmem
    rwa [show e - (e + s) = -s by ring, abs_neg] at this
  have hη' := hηE _ hmem
  have hη'0 : 0 < (boundaryZ b (e + s)).im := hη.trans_le hη'
  have hηe0' : 0 < (boundaryZ b e).im := hη.trans_le (hηE e he')
  -- the old-response distance at `(e + s, X - s)`
  have hdy : matchedDistance b (e + s) X' ≤ d + Ld * |s| := by
    have hY : (-imPart X).PosSemidef := by
      rw [show imPart X = 0 by rw [imPart, hX.eq, sub_self, smul_zero], neg_zero]
      exact PosSemidef.zero
    have h1 := matchedDistance_shift_le hW hηe0' hη'0 hY
    have h2 : ‖matchedA (e + s) - matchedA e‖ ≤ La * |s| := by
      have := Collar.Density.norm_matchedA_sub_le hκ' hmem he'
      rwa [show e + s - e = s by ring] at this
    have hΔ : ‖shiftDefect b e s‖ ≤ (Lz + 1) * |s| := by
      have e1 : shiftDefect b e s = (boundaryZ b (e + s) - boundaryZ b e) + (s : ℂ) := by
        rw [shiftDefect]; ring
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs]
      linarith only [hzy]
    have h3 : ((boundaryZ b (e + s)).im * (boundaryZ b e).im)⁻¹ ≤ (η ^ 2)⁻¹ := by
      rw [sq]
      exact inv_anti₀ (by positivity) (mul_le_mul hη' (hηE e he') hη.le hη'0.le)
    have h5 : ‖shiftDefect b e s‖ * ((boundaryZ b (e + s)).im * (boundaryZ b e).im)⁻¹ ≤
        (Lz + 1) * |s| * (η ^ 2)⁻¹ :=
      mul_le_mul hΔ h3 (inv_nonneg.2 (mul_pos hη'0 hηe0').le) (by positivity)
    have h6 : (Lz + 1) * |s| * (η ^ 2)⁻¹ + La * |s| = Ld * |s| := by
      simp only [Ld]; field_simp
    linarith only [h1, h2, h5, h6]
  have hdyS : matchedDistance b (e + s) X' ≤ dS := by
    have h1 : |s| ≤ dS / (2 * Ld) := hs.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : Ld * |s| ≤ dS / 2 := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith only [h1]
    linarith only [hdy, h2, hd]
  have hLzy : (Lz + 1) * |s| ≤ 1 := by
    have h1 : |s| ≤ 1 / (Lz + 1) := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc (Lz + 1) * |s| ≤ (Lz + 1) * (1 / (Lz + 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 1 := by field_simp
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hηe0 : 0 ≤ (boundaryZ b e).im := hηe0'.le
  have hηe1 : (boundaryZ b e).im ≤ 1 := Collar.Density.boundaryZ_im_le_one' hb0.le (by linarith) he2
  -- the weight change `z = z_b(e) + s ↦ z' = z_b(e + s)` at the old response `X - s`
  obtain ⟨hp1, hp2⟩ := Collar.Density.weight_change hX' (z := z) hη'0 q
  have hp3 := Collar.Density.weight_change_two_sided hX' (z := z) hη'0 q
  set K' := matchedLeadK b (e + s) X'
  set p := K'ᴴ⁻¹ *ᵥ u with hpdef
  have heq : ∀ ω, quadForm (Collar.Density.condCollarDensity b (e + s) X' ω) u =
      quadForm (K' * Collar.Density.condCollarDensity b (e + s) X' ω * K'ᴴ) p := by
    intro ω
    have := quadForm_conjTranspose_mul_mul K'ᴴ (Collar.Density.condCollarDensity b (e + s) X' ω) p
    rw [conjTranspose_conjTranspose] at this
    rw [this]
    congr 1
    exact hp1.symm
  simp_rw [heq]
  obtain ⟨hlo, hhi⟩ := hS W hW hW₀ (e + s) hmem X' hX' hdyS p
  set δ := ‖z - boundaryZ b (e + s)‖ with hδ
  have hzs : ‖z - boundaryZ b e‖ = |s| := by
    rw [hzdef, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hδle : δ ≤ |s| + Lz * |s| := by
    have := norm_sub_le_norm_sub_add_norm_sub z (boundaryZ b e) (boundaryZ b (e + s))
    linarith [hzy, hzs]
  have hδ2 : δ ≤ 2 := by linarith [hLzy]
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hinv : ((boundaryZ b (e + s)).im ^ 2)⁻¹ ≤ (η ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hη.le hη' 2)
  have hnp : ∑ a, ‖p a‖ ^ 2 ≤ Mp * nq := by
    refine hp2.trans (mul_le_mul_of_nonneg_right ?_ hnq)
    have hδsq : δ ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ hδ0 hδ2 2
      norm_num at this
      exact this
    have h4 : δ ^ 2 * ((boundaryZ b (e + s)).im ^ 2)⁻¹ ≤ 4 * (η ^ 2)⁻¹ :=
      mul_le_mul hδsq hinv (by positivity) (by norm_num)
    have hMpe : Mp = 2 * (1 + 4 * (η ^ 2)⁻¹) := by simp only [Mp, div_eq_mul_inv]
    rw [hMpe]
    linarith only [h4]
  have ht : δ / (boundaryZ b (e + s)).im ≤ δ / η :=
    div_le_div_of_nonneg_left hδ0 hη hη'
  have hnpq : |∑ a, ‖p a‖ ^ 2 - nq| ≤ Cη / 2 * (|s| + Lz * |s|) * nq := by
    refine hp3.trans (mul_le_mul_of_nonneg_right ?_ hnq)
    have ht0 : 0 ≤ δ / (boundaryZ b (e + s)).im := by positivity
    have htη : δ / η ≤ 2 / η := div_le_div_of_nonneg_right hδ2 hη.le
    have h1 : 2 * (δ / (boundaryZ b (e + s)).im) + (δ / (boundaryZ b (e + s)).im) ^ 2 ≤
        (2 + 2 / η) * (δ / η) := by
      have := mul_le_mul ht (ht.trans htη) ht0 (by positivity)
      linarith only [this, ht, sq (δ / (boundaryZ b (e + s)).im)]
    have h2 : (2 + 2 / η) * (δ / η) = Cη / 2 * δ := by
      simp only [Cη]; field_simp; ring
    have h3 : Cη / 2 * δ ≤ Cη / 2 * (|s| + Lz * |s|) :=
      mul_le_mul_of_nonneg_left hδle (by positivity)
    linarith only [h1, h2, h3]
  have hηη : |(boundaryZ b (e + s)).im - (boundaryZ b e).im| ≤ Lz * |s| := by
    have := Complex.abs_im_le_norm (boundaryZ b e - boundaryZ b (e + s))
    rw [Complex.sub_im, abs_sub_comm] at this
    exact this.trans hzy
  obtain ⟨hb1, hb2⟩ := Collar.Density.density_budget hnq (by positivity) hnp hnpq hηη hηe0 hηe1
    hdy hd0 hLd.le (hεS0 W) hCS (abs_nonneg s) hCη hLz.le (abs_nonneg s)
  constructor
  · refine (ENNReal.ofReal_le_ofReal ?_).trans hlo
    have : (CS * Mp * (d + εS W) + (Cη / Real.pi + B₀) * |s|) * nq =
        (CS * Mp * (d + εS W) + Cη / Real.pi * |s| + B₀ * |s|) * nq := by ring
    linarith
  · refine hhi.trans (ENNReal.ofReal_le_ofReal ?_)
    have : (CS * Mp * (d + εS W) + (Cη / Real.pi + B₀) * |s|) * nq =
        (CS * Mp * (d + εS W) + Cη / Real.pi * |s| + B₀ * |s|) * nq := by ring
    linarith

end BlockBand.Critical.MatrixClosing.Mean
