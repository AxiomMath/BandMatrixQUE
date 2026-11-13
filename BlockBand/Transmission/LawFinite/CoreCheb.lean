module

public import BlockBand.Transmission.LawFinite.PathStep

/-!
# The finite-core steps `r → r+1`, `r ≥ 1`, by Chebyshev

One fresh layer keeps `q` from dropping by a constant factor, except with probability `O(1/W)`.
Hypothesis `PassiveBoundsStatement`, used through `massMeanRefined_bulk` and `ml_fresh_bulk`.

* `cheb_core`: on `δ₀(Z) ≤ d`, `q(Z) > 0`: `P(q(Z₊) < (c₁/4)q(Z)) ≤ 16C₂²/(c₁²W)`, from
  `μ = Eq₊ ≥ c₁q/2` (`drift_mean_lower`) and `‖q₊ - μ‖₂ ≤ C₂q/√W`;
* **`cheb_absorbed`**: the same with a fresh absorption `0 ≤ ε ≤ Kε/W²` (absorption moved into
  the input: `jetDistance0_absorb_le`, `passiveMass_le_absorb`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- Chebyshev arithmetic: `(c₁q/4)⁻²(C₂q/√W)² = 16C₂²/(c₁²W)`. -/
theorem cheb_arith {c₁ C₂ q W : ℝ} (hc₁ : 0 < c₁) (hq : 0 < q) (hW : 0 < W) :
    (c₁ * q / 4)⁻¹ ^ (2 : ℝ) * (C₂ / Real.sqrt W * q) ^ (2 : ℝ) = 16 * C₂ ^ 2 / (c₁ ^ 2 * W) := by
  rw [Real.rpow_two, Real.rpow_two, mul_pow, div_pow, Real.sq_sqrt hW.le]
  field_simp
  ring

/-- **Chebyshev step at an unabsorbed passive input** (Chebyshev in place of
the reciprocal): `b, κ` first; then `d, c > 0`, `C ≥ 0`, `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`
and every passive `Z` with `δ₀(Z) ≤ d` and `q(Z) > 0`: `P(q(Z₊) < c·q(Z)) ≤ C/W`.
From the two-sided refined mean (`μ ≥ c₁q/2`) and `ml_fresh_bulk` at `n = 2`. -/
theorem cheb_core (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ d c C : ℝ, 0 < d ∧ 0 < c ∧ 0 ≤ C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ Z : Matrix (Fin W) (Fin W) ℂ, (passiveY Z).PosSemidef →
        jetDistance0 b E Z ≤ d → 0 < passiveMass b E Z →
          freshLaw W b {ω | passiveMass b E (freshSchur E Z ω) < c * passiveMass b E Z} ≤
            ENNReal.ofReal (C / W) := by
  obtain ⟨Cr, Wr, hCr, hMR⟩ := massMeanRefined_bulk hA hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂, hF2⟩ := ml_fresh_bulk hA hb0 hb hκ 2 (by norm_num)
  have hηL : 0 < etaLow b κ := etaLow_pos (by linarith) hκ
  set Li := (etaLow b κ)⁻¹
  set c₁ := (1 + Li ^ 2 / (4 * b))⁻¹
  have hc₁ : 0 < c₁ := by positivity
  set Kr := Cr * (4 * Li + 6)
  have hKr : 0 ≤ Kr := by positivity
  set d := min (c₁ / (4 * (Kr + 1))) 1
  have hd : 0 < d := lt_min (by positivity) one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hKd : Kr * (2 * d) ≤ c₁ / 2 := by
    have hd4 : d ≤ c₁ / (4 * (Kr + 1)) := min_le_left _ _
    have : Kr * (2 * d) ≤ Kr * (2 * (c₁ / (4 * (Kr + 1)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hKr
    refine this.trans ?_
    rw [show Kr * (2 * (c₁ / (4 * (Kr + 1)))) = c₁ / 2 * (Kr / (Kr + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  refine ⟨d, c₁ / 4, 16 * C₂ ^ 2 / c₁ ^ 2, hd, by positivity, by positivity,
    max (max Wr W₂) ⌈d⁻¹⌉₊, fun W hW E hE Z hZ hδ hq => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWr, hW₂⟩, hWd⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hdinv : 1 ≤ d⁻¹ := (one_le_inv₀ hd).mpr hd1
  have hW1r : (1 : ℝ) ≤ W := hdinv.trans ((Nat.le_ceil _).trans (by exact_mod_cast hWd))
  have hW1 : 1 ≤ W := by exact_mod_cast hW1r
  have hWpos : (0 : ℝ) < W := by linarith
  have hWinv : (W : ℝ)⁻¹ ≤ d := by
    rw [inv_le_comm₀ hWpos hd]; exact (Nat.le_ceil _).trans (by exact_mod_cast hWd)
  have hWsq : (W : ℝ)⁻¹ ^ 2 ≤ d := Generator.rf_Wsq hW1r hWinv
  have he2 : jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2 ≤ 2 * d := by linarith
  have hKe : Kr * (jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2) ≤ c₁ / 2 :=
    (mul_le_mul_of_nonneg_left he2 hKr).trans hKd
  obtain ⟨hmean2, hfl2⟩ := hF2 W hW₂ E hE Z hZ
  have hMRb := hMR W hWr E hE Z hZ
  rw [← hmean2] at hMRb
  have hErr := refinedErr_le_bulk hb0 hb h1 h2 hZ hLi hW1 (by linarith)
  have hm' : |(∫ ω, qc b E (freshSchur E Z ω) ∂freshLaw W b) - passiveMass b E Z /
      (1 + alphaCoef b E * passiveMass b E Z / W)| ≤
      Kr * (jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2) * passiveMass b E Z := by
    refine hMRb.trans ?_
    calc Cr * refinedErr b E Z ≤ Cr * ((4 * Li + 6) * (jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2) *
          passiveMass b E Z) := mul_le_mul_of_nonneg_left hErr hCr
      _ = _ := by ring
  obtain ⟨hα0, hα, hqW⟩ := drift_bulk_aux hb0 hb h1 h2 hLi Z
  obtain ⟨hmlo, -⟩ := drift_mean_lower hq hWpos hb0 hα0 hα hqW hm' hKe
  -- Chebyshev
  set m := ∫ ω, qc b E (freshSchur E Z ω) ∂freshLaw W b
  set g : LayerSample W .oneBlockOnePort → ℝ := fun ω => ‖qc b E (freshSchur E Z ω) - m‖
  have hg2 : eLpNorm g (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (C₂ / Real.sqrt W * passiveMass b E Z) := by
    have h2 : ((2 : ℕ) : ℝ≥0∞) = 2 := by norm_num
    rw [h2] at hfl2
    have hm : AEStronglyMeasurable (fun ω => qc b E (freshSchur E Z ω) - m) (freshLaw W b) :=
      ((measurable_qc_fresh b E Z).sub measurable_const).aestronglyMeasurable
    rw [ENNReal.ofReal_ofNat, show g = fun ω => ‖qc b E (freshSchur E Z ω) - m‖ from rfl,
      eLpNorm_norm _ hm]
    exact hfl2
  have hsub : {ω | passiveMass b E (freshSchur E Z ω) < c₁ / 4 * passiveMass b E Z} ≤ᵐ[freshLaw W b]
      {ω | c₁ * passiveMass b E Z / 4 < g ω} := by
    filter_upwards [ae_layer_herm (W := W) b] with ω hA' hlt
    have hqc := qc_eq (b := b) (E := E) (PathScalar.passiveY_freshSchur E hZ ω hA')
    change passiveMass b E (freshSchur E Z ω) < c₁ / 4 * passiveMass b E Z at hlt
    change c₁ * passiveMass b E Z / 4 < ‖qc b E (freshSchur E Z ω) - m‖
    rw [hqc, Real.norm_eq_abs]
    refine lt_of_lt_of_le ?_ (neg_le_abs _)
    linarith
  refine (measure_mono_ae hsub).trans ?_
  refine (markov_ofReal (freshLaw W b) (fun ω => norm_nonneg _) two_pos (by positivity)
    (by have : 0 ≤ C₂ := by linarith
        positivity) hg2).trans (le_of_eq ?_)
  rw [cheb_arith hc₁ hq hWpos]
  congr 1; field_simp

/-- **Chebyshev step with a fresh absorption** `0 ≤ ε ≤ Kε/W²`: `b, κ, Kε` first; then
`d, c > 0`, `C ≥ 0`, `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`, every passive `X` with
`δ₀(X) ≤ d`, `q(X) > 0`: `P(q(freshSchur E (X - iε)) < c·q(X)) ≤ C/W`. The absorption is moved
into the input: `δ₀(X - iε) ≤ δ₀(X) + ε/η²`, `q(X) ≤ (1 + ε/η)²q(X - iε)`. -/
theorem cheb_absorbed (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) {Kε : ℝ} (hKε : 0 ≤ Kε) :
    ∃ d c C : ℝ, 0 < d ∧ 0 < c ∧ 0 ≤ C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        jetDistance0 b E X ≤ d → 0 < passiveMass b E X → ∀ ε : ℝ, 0 ≤ ε →
          ε ≤ Kε / (W : ℝ) ^ 2 →
          freshLaw W b {ω | passiveMass b E (freshSchur E (absorbedInput X ε) ω) <
            c * passiveMass b E X} ≤ ENNReal.ofReal (C / W) := by
  obtain ⟨d₀, c₀, C₀, hd₀, hc₀, hC₀, W₀, hst⟩ := cheb_core hA hb0 hb hκ
  have hηL : 0 < etaLow b κ := etaLow_pos (by linarith) hκ
  set Li := (etaLow b κ)⁻¹
  have hLi0 : 0 < Li := inv_pos.mpr hηL
  refine ⟨d₀ / 2, c₀ / 4, C₀, by positivity, by positivity, hC₀,
    max W₀ (⌈2 * Kε * Li ^ 2 / d₀ + Kε * Li⌉₊ + 1), fun W hW E hE X hY hδ hq ε hε hεK => ?_⟩
  have hW0 : W₀ ≤ W := le_of_max_le_left hW
  have hW1 : ⌈2 * Kε * Li ^ 2 / d₀ + Kε * Li⌉₊ + 1 ≤ W := le_of_max_le_right hW
  have hWr : 2 * Kε * Li ^ 2 / d₀ + Kε * Li + 1 ≤ (W : ℝ) := by
    have := Nat.le_ceil (2 * Kε * Li ^ 2 / d₀ + Kε * Li)
    have h' : ((⌈2 * Kε * Li ^ 2 / d₀ + Kε * Li⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW1
    push_cast at h'; linarith
  have hWpos : (1 : ℝ) ≤ W := by
    have : 0 ≤ 2 * Kε * Li ^ 2 / d₀ + Kε * Li := by positivity
    linarith
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hεW : ε ≤ Kε / W := by
    refine hεK.trans (div_le_div_of_nonneg_left hKε (by positivity) ?_)
    nlinarith
  have hεη : ε / etaZ b E ≤ Kε * Li / W := by
    rw [div_eq_mul_inv]
    calc ε * (etaZ b E)⁻¹ ≤ Kε / W * Li := mul_le_mul hεW hLi (by positivity) (by positivity)
      _ = _ := by ring
  have hεη2 : ε / etaZ b E ^ 2 ≤ Kε * Li ^ 2 / W := by
    rw [div_eq_mul_inv, ← inv_pow]
    calc ε * (etaZ b E)⁻¹ ^ 2 ≤ Kε / W * Li ^ 2 :=
          mul_le_mul hεW (pow_le_pow_left₀ (by positivity) hLi 2) (by positivity) (by positivity)
      _ = _ := by ring
  have hWp : (0 : ℝ) < W := by linarith
  have hb1 : Kε * Li / W ≤ 1 := by
    rw [div_le_one hWp]; have : 0 ≤ 2 * Kε * Li ^ 2 / d₀ := by positivity
    linarith
  have hb2 : Kε * Li ^ 2 / W ≤ d₀ / 2 := by
    rw [div_le_iff₀ hWp]
    have h0 : 0 ≤ Kε * Li := by positivity
    have h3 : 2 * Kε * Li ^ 2 / d₀ ≤ W := by linarith
    rw [div_le_iff₀ hd₀] at h3; nlinarith
  set Z := absorbedInput X ε
  have hZ : (passiveY Z).PosSemidef := passiveY_absorbedInput hY hε
  have hδZ : jetDistance0 b E Z ≤ d₀ := by
    have := jetDistance0_absorb_le hb0 hb h1 h2 hY hε
    exact this.trans (by linarith)
  have hqZ := passiveMass_le_absorb hb0 hb h1 h2 hY hε
  have hfac : (1 + ε / etaZ b E) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ ε / etaZ b E := by positivity
    nlinarith
  have hqZ' : passiveMass b E X / 4 ≤ passiveMass b E Z := by
    have hq0 : 0 ≤ passiveMass b E Z := passiveMass_nonneg b E hZ
    nlinarith
  have hqZpos : 0 < passiveMass b E Z := by linarith
  refine (measure_mono fun ω hω => ?_).trans (hst W hW0 E hE Z hZ hδZ hqZpos)
  change passiveMass b E (freshSchur E Z ω) < c₀ / 4 * passiveMass b E X at hω
  change passiveMass b E (freshSchur E Z ω) < c₀ * passiveMass b E Z
  nlinarith

end BlockBand.Transmission.LawFinite
