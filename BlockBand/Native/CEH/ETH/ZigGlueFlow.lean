module

public import BlockBand.Native.CEH.ETH.ZigGlueAlg
public import BlockBand.Native.CEH.ETH.FlowItoZ
public import BlockBand.Native.CEH.ETH.FlowTube

/-!
# CEH ETH: flow glue (tube, sign of `Z`, min form, endpoint bridge)

Setting: `F` a matrix, `G : ℝ≥0 → Ω → Matrix` with `F + G σ ω` Hermitian where needed (for a
Hermitian Brownian motion `G` and Hermitian `F` this holds for every `σ, ω`), the flow resolvent
`R_σ(z, m) = flowResolvent F G z m s σ ω = (F + G_σ - (z + (s - σ) m))⁻¹`,
`Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩ = Re (fz_chain R₁ R₂ A)`.

* **The tube at both points and for the adjoints.** `zgl_TubeGood N ζ F G z m s σ ω` is the
  good event of `flowTube_holds_flowResolvent`: `|⟨R_σ⟩ - m| ≤ N^ζ/(N η_σ)`, `|⟨R_σ⟩ - m| ≤ c/2`,
  `|Im⟨R_σ⟩| ≤ 3c/2` with `c = |Im m|`, `η_σ = zigHeight |Im z| c s σ`.
  `zgl_tubeGood_conj`: it transfers to `(z̄, m̄)` (deterministic, by `fz_flowResolvent_conj`).
  `zgl_flowTube_two`: for all `ε, ζ, D > 0` there is `N₀` with: for `N ≥ N₀`, every Hermitian
  Brownian space, `s > 0`, `F`, and MDE solutions `M₁, M₂` at nonreal `z₁, z₂` with
  `N^ε ≤ N |Im zᵢ| ρᵢ`, the event "for some `σ ≤ s` one of the four tubes
  `(z₁, m₁), (z₂, m₂), (z̄₁, m̄₁), (z̄₂, m̄₂)` fails" has `Q`-measure `≤ N^{-D}` (union bound
  of two applications of `flowTube_holds_flowResolvent` at `D + 1`, `N ≥ 2`).
* **The sign of `Z`.** For `Im zᵢ > 0`, `Im mᵢ ≥ 0`, `σ ≤ s`:
  `fz_chain R₁ R₂ A` is real, `Z ≥ 0` and `|fz_chain| = Z` (`zgl_imChain_flow_nonneg`);
  `zgl_fz_chain_conj_left/right/both`: `fz_chain` changes sign under one conjugation
  (`Z(z₁, z̄₂) = Z(z̄₁, z₂) = -Z(z₁, z₂)`, `Z(z̄₁, z̄₂) = Z(z₁, z₂)`), so
  `|fz_chain|` is the same in all four constellations (`zgl_norm_fz_chain_conj_*`).
* **The min form of the trivial bound.** `zgl_norm_imaginaryPart_mul_le_swap`:
  `|⟨Im R₁ Im R₂⟩| ≤ |⟨Im R₂⟩|/η₁`; `zgl_norm_imaginaryPart_mul_le_min`: `≤ min(|⟨Im R₁⟩|/η₂,
  |⟨Im R₂⟩|/η₁)` (resolvents of a Hermitian `H`, `ηᵢ = |Im wᵢ|`); and along the flow, on the
  tube, `zgl_norm_imaginaryPart_mul_flow_le`:
  `|⟨Im R₁ Im R₂⟩| ≤ (3/2) min(c₁/η_{2,σ}, c₂/η_{1,σ})`, `cᵢ = |Im mᵢ|`.
* **The endpoint.** At `σ = s` the flow resolvent is the CEH resolvent of `F + G_s`, so
  `cehPositiveChain (F + G_s) z₁ z₂ A = fz_chain R₁ R₂ A` (`zgl_cehPositiveChain_eq`) and its
  modulus is `Z` for `Im zᵢ > 0` (`zgl_norm_cehPositiveChain_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.Inputs
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig
open BlockBand.External.CEH (normalizedTrace SourceHermitian sourceDensity)
open scoped NNReal ENNReal ComplexConjugate

variable {N : ℕ}

/-!
## Heights along the flow
-/

/-- The flow resolvent is `Phase1.resolvent` at the characteristic. -/
theorem zgl_flowResolvent_eq_resolvent {Ω : Type*} (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s σ : ℝ≥0) (ω : Ω) :
    flowResolvent F G z m s σ ω = Phase1.resolvent (F + G σ ω) (flowSpectral z m s σ) := rfl

/-- `|Im z_σ| = zigHeight |Im z| |Im m| s σ` for `Im z · Im m ≥ 0`, `σ ≤ s`. -/
theorem zgl_abs_im_flowSpectral {z m : ℂ} (hm : 0 ≤ z.im * m.im) {s σ : ℝ} (hσ : σ ≤ s) :
    |(flowSpectral z m s σ).im| = zigHeight |z.im| |m.im| s σ := by
  rw [flowSpectral_im, zigHeight]
  set a := z.im
  set b := m.im
  have hc : 0 ≤ s - σ := by linarith
  have hab : |a| * |b| = a * b := by rw [← abs_mul, abs_of_nonneg hm]
  rw [← sq_eq_sq₀ (abs_nonneg _) (by positivity), sq_abs]
  linear_combination (-1 : ℝ) * sq_abs a + (-2 * (s - σ)) * hab + (-(s - σ) ^ 2) * sq_abs b

/-- `0 < Im z_σ` for `Im z > 0`, `Im m ≥ 0`, `σ ≤ s`. -/
theorem zgl_im_flowSpectral_pos {z m : ℂ} (hz : 0 < z.im) (hm : 0 ≤ m.im) {s σ : ℝ}
    (hσ : σ ≤ s) : 0 < (flowSpectral z m s σ).im := by
  rw [flowSpectral_im]
  have : 0 ≤ (s - σ) * m.im := mul_nonneg (by linarith) hm
  linarith

/-!
## The tube at both points and for the adjoints
-/

section Tube

variable {Ω : Type*}

/-- The good event of `flowTube_holds_flowResolvent` at `(z, m)` and time `σ`. -/
def zgl_TubeGood (N : ℕ) (ζ : ℝ) (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s σ : ℝ≥0) (ω : Ω) : Prop :=
  ‖normalizedTrace (flowResolvent F G z m s σ ω) - m‖ ≤
      (N : ℝ) ^ ζ / (N * zigHeight |z.im| |m.im| s σ) ∧
    ‖normalizedTrace (flowResolvent F G z m s σ ω) - m‖ ≤ |m.im| / 2 ∧
    |(normalizedTrace (flowResolvent F G z m s σ ω)).im| ≤ 3 / 2 * |m.im|

/-- **Adjoints**: the tube at `(z, m)` gives the tube at `(z̄, m̄)` (same thresholds). -/
theorem zgl_tubeGood_conj {ζ : ℝ} {F : Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {z m : ℂ} {s σ : ℝ≥0} {ω : Ω}
    (hH : (F + G σ ω).IsHermitian) (h : zgl_TubeGood N ζ F G z m s σ ω) :
    zgl_TubeGood N ζ F G (conj z) (conj m) s σ ω := by
  have e : normalizedTrace (flowResolvent F G (conj z) (conj m) s σ ω) =
      conj (normalizedTrace (flowResolvent F G z m s σ ω)) := by
    rw [fz_flowResolvent_conj z m s σ ω hH, Phase1.normalizedTrace_conjTranspose]
  have en : ‖normalizedTrace (flowResolvent F G (conj z) (conj m) s σ ω) - conj m‖ =
      ‖normalizedTrace (flowResolvent F G z m s σ ω) - m‖ := by
    rw [e, ← map_sub, Complex.norm_conj]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [en, Complex.conj_im, Complex.conj_im, abs_neg, abs_neg]; exact h1
  · rw [en, Complex.conj_im, abs_neg]; exact h2
  · rw [e, Complex.conj_im, Complex.conj_im, abs_neg, abs_neg]; exact h3

/-- `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`. -/
theorem zgl_two_mul_rpow_neg_succ_le {D : ℝ} (hN : (2 : ℝ) ≤ N) :
    2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have e : (N : ℝ) ^ (-D) = (N : ℝ) ^ (-(D + 1)) * N := by
    rw [← Real.rpow_add_one hN0.ne']
    ring_nf
  rw [e, mul_comm 2]
  exact mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hN0.le _)

end Tube

/-- **The two-point tube with adjoints.** For all `ε, ζ, D > 0` there is `N₀` such that for
`N ≥ N₀`, every Hermitian Brownian motion `G` on any `(Ω, Q, 𝓖)` (`Ω : Type`), `s > 0`,
Hermitian `F`, MDE solutions `Mᵢ` at nonreal `zᵢ` with `N^ε ≤ N |Im zᵢ| ρᵢ`
(`mᵢ = ⟨Mᵢ⟩`, `ρᵢ = sourceDensity Mᵢ`): the event that for some `σ ≤ s` one of the four tubes
`(z₁, m₁)`, `(z₂, m₂)`, `(z̄₁, m̄₁)`, `(z̄₂, m̄₂)` fails has `Q`-measure `≤ N^{-D}`. -/
theorem zgl_flowTube_two : ∀ ε ζ D : ℝ, 0 < ε → 0 < ζ → 0 < D → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
      (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ), IsHermitianBrownian Q 𝓖 N G →
    ∀ (s : ℝ≥0), 0 < (s : ℝ) → ∀ (F : SourceHermitian N) (z₁ z₂ : ℂ)
      (M₁ M₂ : Matrix (Fin N) (Fin N) ℂ),
      IsManuscriptMDE (s : ℝ) F z₁ M₁ → z₁.im ≠ 0 → (N : ℝ) ^ ε ≤ N * |z₁.im| * sourceDensity M₁ →
      IsManuscriptMDE (s : ℝ) F z₂ M₂ → z₂.im ≠ 0 → (N : ℝ) ^ ε ≤ N * |z₂.im| * sourceDensity M₂ →
    Q {ω | ∃ σ : ℝ≥0, σ ≤ s ∧
        ¬ (zgl_TubeGood N ζ F.1 G z₁ (normalizedTrace M₁) s σ ω ∧
          zgl_TubeGood N ζ F.1 G z₂ (normalizedTrace M₂) s σ ω ∧
          zgl_TubeGood N ζ F.1 G (conj z₁) (conj (normalizedTrace M₁)) s σ ω ∧
          zgl_TubeGood N ζ F.1 G (conj z₂) (conj (normalizedTrace M₂)) s σ ω)} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro ε ζ D hε hζ hD
  obtain ⟨N₀, hN₀⟩ := flowTube_holds_flowResolvent ε ζ (D + 1) hε hζ (by linarith)
  refine ⟨max N₀ 2, ?_⟩
  intro N hN Ω _ Q _ 𝓖 G hG s hs F z₁ z₂ M₁ M₂ h₁ hz₁ hd₁ h₂ hz₂ hd₂
  have hN₀' : N ≥ N₀ := le_of_max_le_left hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have b₁ := hN₀ N hN₀' Q 𝓖 G hG s hs F z₁ M₁ h₁ hz₁ hd₁
  have b₂ := hN₀ N hN₀' Q 𝓖 G hG s hs F z₂ M₂ h₂ hz₂ hd₂
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans ((add_le_add b₁ b₂).trans ?_))
  · intro ω hω
    obtain ⟨σ, hσ, hbad⟩ := hω
    have hH : (F.1 + G σ ω).IsHermitian := F.2.add (hG.hermitian σ ω)
    by_cases g₁ : zgl_TubeGood N ζ F.1 G z₁ (normalizedTrace M₁) s σ ω
    · by_cases g₂ : zgl_TubeGood N ζ F.1 G z₂ (normalizedTrace M₂) s σ ω
      · exact absurd ⟨g₁, g₂, zgl_tubeGood_conj hH g₁, zgl_tubeGood_conj hH g₂⟩ hbad
      · exact Or.inr ⟨σ, hσ, g₂⟩
    · exact Or.inl ⟨σ, hσ, g₁⟩
  · have hpos : 0 ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (by positivity) _
    rw [← ENNReal.ofReal_add hpos hpos]
    exact ENNReal.ofReal_le_ofReal (by linarith [zgl_two_mul_rpow_neg_succ_le (D := D) hN2])

/-!
## The sign of `Z` and the four constellations
-/

section Sign

variable {Ω : Type*} {F : Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
  {s σ : ℝ≥0} {ω : Ω}

/-- **Sign of `Z`**: for `Im zᵢ > 0`, `Im mᵢ ≥ 0`, `σ ≤ s` and Hermitian `F + G_σ`, the chain
`fz_chain R₁ R₂ A = ⟨Im R₁ A Im R₂ Aᴴ⟩` is real, `Z = Re ≥ 0` and `|fz_chain| = Z`. -/
theorem zgl_imChain_flow_nonneg (hH : (F + G σ ω).IsHermitian) {z₁ m₁ z₂ m₂ : ℂ}
    (hz₁ : 0 < z₁.im) (hm₁ : 0 ≤ m₁.im) (hz₂ : 0 < z₂.im) (hm₂ : 0 ≤ m₂.im) (hσ : σ ≤ s)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ (fz_chain (flowResolvent F G z₁ m₁ s σ ω) (flowResolvent F G z₂ m₂ s σ ω) A).re ∧
      fz_chain (flowResolvent F G z₁ m₁ s σ ω) (flowResolvent F G z₂ m₂ s σ ω) A =
        ((fz_chain (flowResolvent F G z₁ m₁ s σ ω) (flowResolvent F G z₂ m₂ s σ ω) A).re :
          ℂ) ∧
      ‖fz_chain (flowResolvent F G z₁ m₁ s σ ω) (flowResolvent F G z₂ m₂ s σ ω) A‖ =
        (fz_chain (flowResolvent F G z₁ m₁ s σ ω) (flowResolvent F G z₂ m₂ s σ ω) A).re := by
  have hσ' : (σ : ℝ) ≤ s := NNReal.coe_le_coe.2 hσ
  have hw₁ := zgl_im_flowSpectral_pos hz₁ hm₁ hσ'
  have hw₂ := zgl_im_flowSpectral_pos hz₂ hm₂ hσ'
  exact ⟨bw_re_normalizedTrace_imChain_nonneg hH hw₁ hw₂ A,
    bw_normalizedTrace_imChain_eq_re hH hw₁.ne' hw₂.ne' A,
    bw_norm_normalizedTrace_imChain_eq_re hH hw₁ hw₂ A⟩

/-- The MDE sign condition: `Im z > 0` gives `Im ⟨M⟩ ≥ 0`. -/
theorem zgl_im_normalizedTrace_nonneg_of_mde {s' : ℝ} {F' : SourceHermitian N} {z : ℂ}
    {M : Matrix (Fin N) (Fin N) ℂ} (h : IsManuscriptMDE s' F' z M) (hz : 0 < z.im) :
    0 ≤ (normalizedTrace M).im :=
  (mul_nonneg_iff_of_pos_left hz).1 (Phase1.mde_im_mul_im_nonneg h)

/-- `Z(z₁, z̄₂) = -Z(z₁, z₂)` (any `R₁`). -/
theorem zgl_fz_chain_conj_right (hH : (F + G σ ω).IsHermitian) (R₁ : Matrix (Fin N) (Fin N) ℂ)
    (z m : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    fz_chain R₁ (flowResolvent F G (conj z) (conj m) s σ ω) A =
      -fz_chain R₁ (flowResolvent F G z m s σ ω) A := by
  rw [fz_flowResolvent_conj z m s σ ω hH]
  change normalizedTrace (bwImChain A _ _) = -normalizedTrace (bwImChain A _ _)
  rw [bf_bwImChain_conjTranspose_right, bf_normalizedTrace_neg]

/-- `Z(z̄₁, z₂) = -Z(z₁, z₂)` (any `R₂`). -/
theorem zgl_fz_chain_conj_left (hH : (F + G σ ω).IsHermitian) (R₂ : Matrix (Fin N) (Fin N) ℂ)
    (z m : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    fz_chain (flowResolvent F G (conj z) (conj m) s σ ω) R₂ A =
      -fz_chain (flowResolvent F G z m s σ ω) R₂ A := by
  rw [fz_flowResolvent_conj z m s σ ω hH]
  change normalizedTrace (bwImChain A _ _) = -normalizedTrace (bwImChain A _ _)
  rw [bf_bwImChain_conjTranspose_left, bf_normalizedTrace_neg]

/-- `Z(z̄₁, z̄₂) = Z(z₁, z₂)`. -/
theorem zgl_fz_chain_conj_both (hH : (F + G σ ω).IsHermitian) (z₁ m₁ z₂ m₂ : ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    fz_chain (flowResolvent F G (conj z₁) (conj m₁) s σ ω)
        (flowResolvent F G (conj z₂) (conj m₂) s σ ω) A =
      fz_chain (flowResolvent F G z₁ m₁ s σ ω) (flowResolvent F G z₂ m₂ s σ ω) A := by
  rw [zgl_fz_chain_conj_left hH, zgl_fz_chain_conj_right hH, neg_neg]

/-- `|Z|` is the same in the constellation `(z₁, z̄₂)`. -/
theorem zgl_norm_fz_chain_conj_right (hH : (F + G σ ω).IsHermitian)
    (R₁ : Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖fz_chain R₁ (flowResolvent F G (conj z) (conj m) s σ ω) A‖ =
      ‖fz_chain R₁ (flowResolvent F G z m s σ ω) A‖ := by
  rw [zgl_fz_chain_conj_right hH, norm_neg]

/-- `|Z|` is the same in the constellation `(z̄₁, z₂)`. -/
theorem zgl_norm_fz_chain_conj_left (hH : (F + G σ ω).IsHermitian)
    (R₂ : Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖fz_chain (flowResolvent F G (conj z) (conj m) s σ ω) R₂ A‖ =
      ‖fz_chain (flowResolvent F G z m s σ ω) R₂ A‖ := by
  rw [zgl_fz_chain_conj_left hH, norm_neg]

end Sign

/-!
## The min form of the `Y` trivial bound
-/

section MinForm

variable {H : Matrix (Fin N) (Fin N) ℂ} {w₁ w₂ : ℂ}

/-- `‖⟨Im R⟩‖ = |Im⟨R⟩|`. -/
theorem zgl_norm_normalizedTrace_imaginaryPart (R : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (External.CEH.imaginaryPart R)‖ = |(normalizedTrace R).im| := by
  rw [Phase1.normalizedTrace_imaginaryPart, Complex.norm_real, Real.norm_eq_abs]

/-- **Swapped orientation**: `|⟨Im R₁ Im R₂⟩| ≤ |⟨Im R₂⟩| / η₁`. -/
theorem zgl_norm_imaginaryPart_mul_le_swap (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) :
    ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) *
        External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ ≤
      ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ / |w₁.im| := by
  rw [Phase1.normalizedTrace_mul_comm]
  exact bf_norm_normalizedTrace_imaginaryPart_mul_le hH hw₂ hw₁

/-- **Min form**: `|⟨Im R₁ Im R₂⟩| ≤ min(|⟨Im R₁⟩|/η₂, |⟨Im R₂⟩|/η₁)`. -/
theorem zgl_norm_imaginaryPart_mul_le_min (hH : H.IsHermitian) (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) :
    ‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) *
        External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ ≤
      min (‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁))‖ / |w₂.im|)
        (‖normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂))‖ / |w₁.im|) :=
  le_min (bf_norm_normalizedTrace_imaginaryPart_mul_le hH hw₁ hw₂)
    (zgl_norm_imaginaryPart_mul_le_swap hH hw₁ hw₂)

end MinForm

/-- **Min form along the flow, on the tube**: for Hermitian `F + G_σ`, nonreal `zᵢ` with
`Im zᵢ Im mᵢ ≥ 0`, `σ ≤ s` and `|Im⟨R_{i,σ}⟩| ≤ (3/2) cᵢ` (`cᵢ = |Im mᵢ|`, the tube):
`|⟨Im R_{1,σ} Im R_{2,σ}⟩| ≤ (3/2) min(c₁/η_{2,σ}, c₂/η_{1,σ})`,
`η_{i,σ} = zigHeight |Im zᵢ| cᵢ s σ`. -/
theorem zgl_norm_imaginaryPart_mul_flow_le {Ω : Type*} {F : Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {s σ : ℝ≥0} {ω : Ω}
    (hH : (F + G σ ω).IsHermitian) {z₁ m₁ z₂ m₂ : ℂ} (hz₁ : z₁.im ≠ 0)
    (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im) (hσ : σ ≤ s)
    (ht₁ : |(normalizedTrace (flowResolvent F G z₁ m₁ s σ ω)).im| ≤ 3 / 2 * |m₁.im|)
    (ht₂ : |(normalizedTrace (flowResolvent F G z₂ m₂ s σ ω)).im| ≤ 3 / 2 * |m₂.im|) :
    ‖normalizedTrace (External.CEH.imaginaryPart (flowResolvent F G z₁ m₁ s σ ω) *
        External.CEH.imaginaryPart (flowResolvent F G z₂ m₂ s σ ω))‖ ≤
      3 / 2 * min (|m₁.im| / zigHeight |z₂.im| |m₂.im| s σ)
        (|m₂.im| / zigHeight |z₁.im| |m₁.im| s σ) := by
  have hσ' : (σ : ℝ) ≤ s := NNReal.coe_le_coe.2 hσ
  have hw₁ : (flowSpectral z₁ m₁ s σ).im ≠ 0 := flowSpectral_im_ne_zero hz₁ hm₁ hσ'
  have hw₂ : (flowSpectral z₂ m₂ s σ).im ≠ 0 := flowSpectral_im_ne_zero hz₂ hm₂ hσ'
  have h := zgl_norm_imaginaryPart_mul_le_min hH hw₁ hw₂
  rw [← zgl_flowResolvent_eq_resolvent, ← zgl_flowResolvent_eq_resolvent,
    zgl_norm_normalizedTrace_imaginaryPart, zgl_norm_normalizedTrace_imaginaryPart,
    zgl_abs_im_flowSpectral hm₁ hσ', zgl_abs_im_flowSpectral hm₂ hσ'] at h
  have he₁ : 0 < zigHeight |z₁.im| |m₁.im| s σ :=
    zigHeight_pos (abs_pos.2 hz₁) (abs_nonneg _) hσ'
  have he₂ : 0 < zigHeight |z₂.im| |m₂.im| s σ :=
    zigHeight_pos (abs_pos.2 hz₂) (abs_nonneg _) hσ'
  refine h.trans ?_
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  refine min_le_min ?_ ?_
  · rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right ht₁ he₂.le
  · rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right ht₂ he₁.le

/-!
## The endpoint bridge to `cehPositiveChain`
-/

section Endpoint

open CEHNative.BlockBand CEHNative.BlockBand.External.CEH

variable {Ω : Type*}

/-- At `σ = s` the flow resolvent is the CEH resolvent of `F + G_s` at `z`. -/
theorem zgl_flowResolvent_self (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (σ : ℝ≥0) (ω : Ω) :
    flowResolvent F G z m σ σ ω = cehHermitianResolvent (F + G σ ω) z := by
  simp [flowResolvent, flowSpectral, cehHermitianResolvent]

/-- The same at the window time `σ = Real.toNNReal s`. -/
theorem zgl_flowResolvent_toNNReal (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s : ℝ) (ω : Ω) :
    flowResolvent F G z m (Real.toNNReal s) (Real.toNNReal s) ω =
      cehHermitianResolvent (F + G (Real.toNNReal s) ω) z :=
  zgl_flowResolvent_self F G z m _ ω

/-- **G8**: the `matrixImaginaryPart` is `External.CEH.imaginaryPart`. -/
theorem zgl_matrixImaginaryPart_eq (X : Matrix (Fin N) (Fin N) ℂ) :
    matrixImaginaryPart X = External.CEH.imaginaryPart X := by
  rw [matrixImaginaryPart, External.CEH.imaginaryPart]
  congr 1
  rw [mul_inv, Complex.inv_I]
  ring

/-- `cehPositiveChain (F + G_σ) z₁ z₂ A = fz_chain R_{1,σ} R_{2,σ} A` at `σ = s`
(any `m₁, m₂`). -/
theorem zgl_cehPositiveChain_eq (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (σ : ℝ≥0) (ω : Ω)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    cehPositiveChain (F + G σ ω) z₁ z₂ A =
      fz_chain (flowResolvent F G z₁ m₁ σ σ ω) (flowResolvent F G z₂ m₂ σ σ ω) A := by
  rw [cehPositiveChain, fz_chain, zgl_flowResolvent_self, zgl_flowResolvent_self,
    zgl_matrixImaginaryPart_eq, zgl_matrixImaginaryPart_eq]
  rfl

/-- For Hermitian `F + G_σ` and nonreal `zᵢ`,
`‖cehPositiveChain (F + G_σ) z₁ z₂ A‖ = |Z_σ|` at `σ = s`, `Z = Re fz_chain`. -/
theorem zgl_norm_cehPositiveChain_eq_abs {F : Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {σ : ℝ≥0} {ω : Ω}
    (hH : (F + G σ ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (m₁ m₂ : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖cehPositiveChain (F + G σ ω) z₁ z₂ A‖ =
      |(fz_chain (flowResolvent F G z₁ m₁ σ σ ω) (flowResolvent F G z₂ m₂ σ σ ω) A).re| := by
  rw [zgl_cehPositiveChain_eq F G z₁ m₁ z₂ m₂ σ ω A]
  have hw₁ : (flowSpectral z₁ m₁ σ σ).im ≠ 0 := by simpa [flowSpectral] using hz₁
  have hw₂ : (flowSpectral z₂ m₂ σ σ).im ≠ 0 := by simpa [flowSpectral] using hz₂
  change ‖normalizedTrace (bwImChain A (Phase1.resolvent (F + G σ ω) (flowSpectral z₁ m₁ σ σ))
    (Phase1.resolvent (F + G σ ω) (flowSpectral z₂ m₂ σ σ)))‖ = |(normalizedTrace (bwImChain A
    (Phase1.resolvent (F + G σ ω) (flowSpectral z₁ m₁ σ σ))
    (Phase1.resolvent (F + G σ ω) (flowSpectral z₂ m₂ σ σ)))).re|
  rw [bw_normalizedTrace_imChain_eq_re hH hw₁ hw₂ A, Complex.norm_real, Complex.ofReal_re,
    Real.norm_eq_abs]

/-- For Hermitian `F + G_σ` and `Im zᵢ > 0`,
`‖cehPositiveChain (F + G_σ) z₁ z₂ A‖ = Z_σ` at `σ = s`. -/
theorem zgl_norm_cehPositiveChain_eq {F : Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {σ : ℝ≥0} {ω : Ω}
    (hH : (F + G σ ω).IsHermitian) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (m₁ m₂ : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖cehPositiveChain (F + G σ ω) z₁ z₂ A‖ =
      (fz_chain (flowResolvent F G z₁ m₁ σ σ ω) (flowResolvent F G z₂ m₂ σ σ ω) A).re := by
  rw [zgl_cehPositiveChain_eq F G z₁ m₁ z₂ m₂ σ ω A]
  have hw₁ : 0 < (flowSpectral z₁ m₁ σ σ).im := by simpa [flowSpectral] using hz₁
  have hw₂ : 0 < (flowSpectral z₂ m₂ σ σ).im := by simpa [flowSpectral] using hz₂
  exact bw_norm_normalizedTrace_imChain_eq_re hH hw₁ hw₂ A

end Endpoint

end BlockBand.Native.CEH.ETH
