module

public import BlockBand.Native.CEH.ETH.DeterministicSpectral
public import BlockBand.Native.CEH.ETH.DeterministicN2

/-!
# CEH ETH: CEH Lemma 5.6 bounds 1–4 in hybrid form (diagonal model)

**Hybrid form**: target data `Dᵢ = diag (f - ζᵢ)⁻¹` (`Θᵢ = Im ζᵢ > 0`), a
target-regular `A` (`⟨D₁AD₂ᴴ⟩ = 0`), and a variance `σ ∈ [0, s]` entering only through the
hybrid approximation `twoResApprox σ` (denominators `1 - σ⟨·⟩`). The MDE enters only through
the Ward condition `s aᵢ < 1`, `aᵢ = ⟨DᵢDᵢᴴ⟩` (true for MDE solutions at variance `s`,
`mul_wardMass_mde_lt_one`). Notation: `tᵢ = Im⟨Dᵢ⟩`, `P = Re⟨Im D₁ A Im D₂ Aᴴ⟩`,
`c = ⟨D₁D₂⟩` (the `(+,+)` stable trace).

Bounds, for every `σ ∈ [0, s]` (constants uniform in `σ`):
* `(+,+)`: `|⟨M^A_σ(z₁⁺,z₂⁺)⟩| ≤ 4 √P √(t₂/Θ₁) / |1 - sc|`;
* `(-,-)`: `|⟨M^A_σ(z₁⁻,z₂⁻)⟩| ≤ 4 √P √(t₁/Θ₂) / |1 - sc|`;
* `(+,-)`: `⟨M^A_σ(z₁⁺,z₂⁻)⟩ = 0`;
* `(-,+)`: `|⟨M^A_σ(z₁⁻,z₂⁺)⟩| ≤ 4 √P √(a₁/(Θ₁Θ₂)) |ζ₁ - ζ̄₂| / |1 - sc|`;
* `M̂` (CEH (5.24)): `|⟨M̂_σ⟩| ≤ ¼` (sum of the three).
On the regular-window regime these give `|⟨M^A_σ⟩|, |⟨M̂_σ⟩| ≤ C(s, K, κ) √P`
(`lemma56_window_bound`), and `√P ≤ π √(ρ₁ρ₂) s₂(σ)` (`sqrt_chain_le`), so CEH (5.23) bounds
1–4 hold in the hybrid form with a constant depending only on `(s, K, κ)`; since CEH's
right-hand sides carry the extra factors `√(ρⱼ/ηᵢ,σ) ≥ √(κ/(π(ηᵢ + sK)))`, these are at least
as strong as CEH's whenever the heights are bounded (e.g. `ηᵢ ≤ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open scoped ComplexConjugate

variable {N : ℕ}

/-- Generic: `s a(X₁) < 1`, `s a(X₂) < 1`, `s ≥ 0` give `s |⟨X₁X₂⟩| < 1`. -/
theorem mul_norm_NTrace_lt_one_of_wardMass {s : ℝ} (hs : 0 ≤ s)
    (X₁ X₂ : Matrix (Fin N) (Fin N) ℂ) (h₁ : s * wardMass X₁ < 1) (h₂ : s * wardMass X₂ < 1) :
    s * ‖NTrace (X₁ * X₂)‖ < 1 := by
  have hcs := norm_NTrace_mul_le_wardMass X₁ X₂
  have n₁ := wardMass_nonneg X₁
  have n₂ := wardMass_nonneg X₂
  have e₁ := Real.sq_sqrt n₁
  have e₂ := Real.sq_sqrt n₂
  have hprod : s * (Real.sqrt (wardMass X₁) * Real.sqrt (wardMass X₂)) < 1 := by
    have hsq : (s * (Real.sqrt (wardMass X₁) * Real.sqrt (wardMass X₂))) ^ 2 < 1 := by
      rw [mul_pow, mul_pow, e₁, e₂]
      have p₁ : 0 ≤ s * wardMass X₁ := mul_nonneg hs n₁
      have p₂ : 0 ≤ s * wardMass X₂ := mul_nonneg hs n₂
      nlinarith
    have hnn : 0 ≤ s * (Real.sqrt (wardMass X₁) * Real.sqrt (wardMass X₂)) := by positivity
    nlinarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcs hs) hprod

/-- Abbreviation for the diagonal resolvent `diag (f - ζ)⁻¹`. -/
abbrev dg (f : Fin N → ℝ) (ζ : ℂ) : Matrix (Fin N) (Fin N) ℂ := diagonal (resEntry f ζ)

/-- `|1 - sc| ≤ 2 |1 - σc|`, `1 - σc ≠ 0` and `|1 - sc| > 0` for `c = ⟨X₁X₂⟩`, when
`s a(Xᵢ) < 1` and `0 ≤ σ ≤ s`. -/
theorem hybrid_den_facts {s σ : ℝ} (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    (X₁ X₂ : Matrix (Fin N) (Fin N) ℂ) (h₁ : s * wardMass X₁ < 1) (h₂ : s * wardMass X₂ < 1) :
    ‖1 - (s : ℂ) * NTrace (X₁ * X₂)‖ ≤ 2 * ‖hybridDen σ X₁ X₂‖ ∧ hybridDen σ X₁ X₂ ≠ 0 ∧
      0 < ‖1 - (s : ℂ) * NTrace (X₁ * X₂)‖ := by
  have hs : 0 ≤ s := hσ0.trans hσs
  have hlt := mul_norm_NTrace_lt_one_of_wardMass hs X₁ X₂ h₁ h₂
  refine ⟨norm_one_sub_le_two_mul _ hσ0 hσs hlt.le, ?_, norm_one_sub_pos _ hs hlt⟩
  exact norm_pos_iff.1 (norm_one_sub_pos _ hσ0
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hσs (norm_nonneg _)) hlt))

theorem NTrace_mm_pair (X₁ X₂ : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (X₁ᴴ * X₂ᴴ) = star (NTrace (X₁ * X₂)) := by
  rw [← conjTranspose_mul]
  simp only [NTrace, Conventions.normalizedTrace, Matrix.trace_conjTranspose, star_mul',
    star_inv₀, star_natCast]
  rw [Matrix.trace_mul_comm X₂ X₁]

/-- A ratio bound: `‖x‖ ≤ X`, `‖den‖ ≥ ‖D‖/2 > 0` give `‖x / den‖ ≤ 2X / ‖D‖`. -/
theorem norm_div_le_of_half {x den : ℂ} {X D : ℝ} (hx : ‖x‖ ≤ X) (hD : 0 < D)
    (hden : D ≤ 2 * ‖den‖) : ‖x / den‖ ≤ 2 * X / D := by
  have hpos : 0 < ‖den‖ := by linarith
  rw [norm_div, div_le_div_iff₀ hpos hD]
  have := norm_nonneg x
  have hX : 0 ≤ X := this.trans hx
  nlinarith

section Hybrid

variable (f : Fin N → ℝ) {ζ₁ ζ₂ : ℂ} (A : Matrix (Fin N) (Fin N) ℂ) {s σ : ℝ}

/-- **Hybrid `(+,+)` bound**: `|⟨M^A_σ(z₁⁺,z₂⁺)⟩| ≤ 4 √P √(t₂/Θ₁) / |1 - s⟨D₁D₂⟩|`. -/
theorem norm_twoResApprox_pp_le (hΘ₁ : 0 < ζ₁.im) (hΘ₂ : 0 < ζ₂.im)
    (hreg : NTrace (dg f ζ₁ * A * (dg f ζ₂)ᴴ) = 0) (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    (ha₁ : s * wardMass (dg f ζ₁) < 1) (ha₂ : s * wardMass (dg f ζ₂) < 1) :
    ‖NTrace (twoResApprox σ (dg f ζ₁) A (dg f ζ₂))‖ ≤
      2 * (2 * Real.sqrt (chainP f ζ₁ ζ₂ A) * Real.sqrt ((NTrace (dg f ζ₂)).im / ζ₁.im)) /
          ‖1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂)‖ := by
  obtain ⟨hd2, hne, h0⟩ := hybrid_den_facts hσ0 hσs (dg f ζ₁) (dg f ζ₂) ha₁ ha₂
  rw [NTrace_twoResApprox σ _ _ _ hne]
  exact norm_div_le_of_half (norm_NTrace_pp_le f hΘ₁ hΘ₂ A hreg) h0 hd2

/-- **Hybrid `(-,-)` bound**: `|⟨M^A_σ(z₁⁻,z₂⁻)⟩| ≤ 4 √P √(t₁/Θ₂) / |1 - s⟨D₁D₂⟩|`. -/
theorem norm_twoResApprox_mm_le (hΘ₁ : 0 < ζ₁.im) (hΘ₂ : 0 < ζ₂.im)
    (hreg : NTrace (dg f ζ₁ * A * (dg f ζ₂)ᴴ) = 0) (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    (ha₁ : s * wardMass (dg f ζ₁) < 1) (ha₂ : s * wardMass (dg f ζ₂) < 1) :
    ‖NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂)ᴴ)‖ ≤
      2 * (2 * Real.sqrt (chainP f ζ₁ ζ₂ A) * Real.sqrt ((NTrace (dg f ζ₁)).im / ζ₂.im)) /
          ‖1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂)‖ := by
  obtain ⟨hd2, hne, h0⟩ := hybrid_den_facts hσ0 hσs (dg f ζ₁)ᴴ (dg f ζ₂)ᴴ
    (by rwa [wardMass_conjTranspose]) (by rwa [wardMass_conjTranspose])
  rw [NTrace_twoResApprox σ _ _ _ hne]
  have hconj : ‖1 - (s : ℂ) * NTrace ((dg f ζ₁)ᴴ * (dg f ζ₂)ᴴ)‖ =
      ‖1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂)‖ := by
    rw [NTrace_mm_pair, ← norm_star (1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂))]
    simp [star_sub, star_mul', Complex.conj_ofReal]
  rw [hconj] at hd2 h0
  exact norm_div_le_of_half (norm_NTrace_mm_le f hΘ₁ hΘ₂ A hreg) h0 hd2

/-- **Hybrid `(+,-)` identity**: `⟨M^A_σ(z₁⁺,z₂⁻)⟩ = 0` for a regular `A` (every `σ`). -/
theorem NTrace_twoResApprox_pm_eq_zero (hreg : NTrace (dg f ζ₁ * A * (dg f ζ₂)ᴴ) = 0) :
    NTrace (twoResApprox σ (dg f ζ₁) A (dg f ζ₂)ᴴ) = 0 := by
  have h := NTrace_twoResApprox_mul σ (dg f ζ₁) A (dg f ζ₂)ᴴ 1
  simp only [Matrix.mul_one] at h
  rw [h, hreg]
  simp

end Hybrid

/-!
## The `(-,+)` constellation
-/

theorem sub_ne_zero_of_im_ne (f : Fin N → ℝ) {ζ : ℂ} (hζ : ζ.im ≠ 0) (k : Fin N) :
    (f k : ℂ) - ζ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hζ (by linarith)

/-- Averaged resolvent identity: `(ζ - ζ') ⟨D_ζ D_ζ'⟩ = ⟨D_ζ⟩ - ⟨D_ζ'⟩`. -/
theorem pair_identity (f : Fin N → ℝ) {ζ ζ' : ℂ} (hζ : ζ.im ≠ 0) (hζ' : ζ'.im ≠ 0) :
    (ζ - ζ') * NTrace (dg f ζ * dg f ζ') = NTrace (dg f ζ) - NTrace (dg f ζ') := by
  rw [diagonal_mul_diagonal, NTrace_diagonal', NTrace_diagonal', NTrace_diagonal', ← mul_sub,
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resEntry_sub f k (sub_ne_zero_of_im_ne f hζ k) (sub_ne_zero_of_im_ne f hζ' k)]
  ring

/-- The characteristic form of the hybrid denominator:
`(ζ - ζ')(1 - σ⟨D_ζD_ζ'⟩) = (ζ - σ⟨D_ζ⟩) - (ζ' - σ⟨D_ζ'⟩)`. -/
theorem mul_hybridDen_eq (f : Fin N → ℝ) {ζ ζ' : ℂ} (hζ : ζ.im ≠ 0) (hζ' : ζ'.im ≠ 0)
    (σ : ℝ) :
    (ζ - ζ') * hybridDen σ (dg f ζ) (dg f ζ') =
      (ζ - (σ : ℂ) * NTrace (dg f ζ)) - (ζ' - (σ : ℂ) * NTrace (dg f ζ')) := by
  have h := pair_identity f hζ hζ'
  rw [hybridDen]
  linear_combination (-(σ : ℂ)) * h

theorem dg_conjTranspose (f : Fin N → ℝ) (ζ : ℂ) : (dg f ζ)ᴴ = dg f (conj ζ) := by
  rw [dg, diagonal_conjTranspose]
  congr 1
  funext k
  exact star_resEntry f ζ k

theorem NTrace_dg_conj (f : Fin N → ℝ) (ζ : ℂ) :
    NTrace (dg f (conj ζ)) = conj (NTrace (dg f ζ)) := by
  rw [← dg_conjTranspose]
  simp only [NTrace, Conventions.normalizedTrace, Matrix.trace_conjTranspose, map_mul, map_inv₀,
    map_natCast]
  rfl

theorem norm_sub_le_norm_conj_sub {u v : ℂ} (hu : 0 ≤ u.im) (hv : 0 ≤ v.im) :
    ‖u - v‖ ≤ ‖conj u - v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith [mul_nonneg hu hv]

/-- `Im (ζ - σ⟨D_ζ⟩) = Θ (1 - σ a) > 0` when `σ a < 1`. -/
theorem im_char_pos (f : Fin N → ℝ) {ζ : ℂ} (hΘ : 0 < ζ.im) {σ : ℝ}
    (ha : σ * wardMass (dg f ζ) < 1) : 0 < (ζ - (σ : ℂ) * NTrace (dg f ζ)).im := by
  have hW := im_mul_wardMass_resEntry f ζ
  rw [Complex.sub_im, Complex.im_ofReal_mul, ← hW]
  have : ζ.im - σ * (ζ.im * wardMass (dg f ζ)) = ζ.im * (1 - σ * wardMass (dg f ζ)) := by ring
  rw [this]
  exact mul_pos hΘ (by linarith)

section MixedPlus

variable (f : Fin N → ℝ) {ζ₁ ζ₂ : ℂ} (A : Matrix (Fin N) (Fin N) ℂ) {s σ : ℝ}

/-- **Hybrid `(-,+)` bound**: `|⟨M^A_σ(z₁⁻,z₂⁺)⟩| ≤ 4 √P √(a₁/(Θ₁Θ₂)) |ζ₁ - ζ̄₂| / |1 - s⟨D₁D₂⟩|`.
The near-critical denominator `1 - σ⟨D₁ᴴD₂⟩` is compensated by the numerator, which is
`O(|ζ₁ - ζ₂|)` by regularity. -/
theorem norm_twoResApprox_mp_le (hΘ₁ : 0 < ζ₁.im) (hΘ₂ : 0 < ζ₂.im)
    (hreg : NTrace (dg f ζ₁ * A * (dg f ζ₂)ᴴ) = 0) (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    (ha₁ : s * wardMass (dg f ζ₁) < 1) (ha₂ : s * wardMass (dg f ζ₂) < 1) :
    ‖NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂))‖ ≤
      2 * (2 * Real.sqrt (chainP f ζ₁ ζ₂ A) *
        Real.sqrt (wardMass (dg f ζ₁) / (ζ₁.im * ζ₂.im))) * ‖ζ₁ - conj ζ₂‖ /
          ‖1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂)‖ := by
  set X := 2 * Real.sqrt (chainP f ζ₁ ζ₂ A) *
    Real.sqrt (wardMass (dg f ζ₁) / (ζ₁.im * ζ₂.im)) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hnum := norm_NTrace_mp_le f hΘ₁ hΘ₂ A hreg
  rw [show 2 * ‖ζ₁ - ζ₂‖ * Real.sqrt (chainP f ζ₁ ζ₂ A) *
      Real.sqrt (wardMass (dg f ζ₁) / (ζ₁.im * ζ₂.im)) = ‖ζ₁ - ζ₂‖ * X by rw [hXdef]; ring]
    at hnum
  obtain ⟨hd2, hne, h0⟩ := hybrid_den_facts hσ0 hσs (dg f ζ₁) (dg f ζ₂) ha₁ ha₂
  have hσ₁ : σ * wardMass (dg f ζ₁) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hσs (wardMass_nonneg _)) ha₁
  have hσ₂ : σ * wardMass (dg f ζ₂) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hσs (wardMass_nonneg _)) ha₂
  set w₁ := ζ₁ - (σ : ℂ) * NTrace (dg f ζ₁) with hw₁
  set w₂ := ζ₂ - (σ : ℂ) * NTrace (dg f ζ₂) with hw₂
  have hw₁p : 0 < w₁.im := im_char_pos f hΘ₁ hσ₁
  have hw₂p : 0 < w₂.im := im_char_pos f hΘ₂ hσ₂
  -- `(ζ₁ - ζ₂)(1 - σc) = w₁ - w₂`
  have hpp := mul_hybridDen_eq f hΘ₁.ne' hΘ₂.ne' σ
  -- `(ζ̄₁ - ζ₂)(1 - σc') = w̄₁ - w₂`
  have hcne : (conj ζ₁).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 hΘ₁.ne'
  have hmp := mul_hybridDen_eq f hcne hΘ₂.ne' σ
  rw [NTrace_dg_conj] at hmp
  have hcw : conj ζ₁ - (σ : ℂ) * conj (NTrace (dg f ζ₁)) = conj w₁ := by
    rw [hw₁, map_sub, map_mul, Complex.conj_ofReal]
  rw [hcw] at hmp
  have hzne : conj ζ₁ - ζ₂ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hwne : conj w₁ - w₂ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hden' : hybridDen σ (dg f (conj ζ₁)) (dg f ζ₂) ≠ 0 := by
    intro h; rw [h, mul_zero] at hmp; exact hwne hmp.symm
  have hnum' : ‖NTrace (dg f (conj ζ₁) * A * dg f ζ₂)‖ ≤ ‖ζ₁ - ζ₂‖ * X := by
    rw [← dg_conjTranspose]; exact hnum
  rw [dg_conjTranspose, NTrace_twoResApprox σ _ _ _ hden', norm_div]
  have hdpos : 0 < ‖hybridDen σ (dg f (conj ζ₁)) (dg f ζ₂)‖ := norm_pos_iff.2 hden'
  have hnorm_mp : ‖hybridDen σ (dg f (conj ζ₁)) (dg f ζ₂)‖ * ‖conj ζ₁ - ζ₂‖ =
      ‖conj w₁ - w₂‖ := by
    rw [← norm_mul, mul_comm, hmp]
  have hnorm_pp : ‖ζ₁ - ζ₂‖ * ‖hybridDen σ (dg f ζ₁) (dg f ζ₂)‖ = ‖w₁ - w₂‖ := by
    rw [← norm_mul, hpp]
  have hcmp : ‖w₁ - w₂‖ ≤ ‖conj w₁ - w₂‖ := norm_sub_le_norm_conj_sub hw₁p.le hw₂p.le
  have hzz : ‖ζ₁ - conj ζ₂‖ = ‖conj ζ₁ - ζ₂‖ := by
    rw [← norm_star (ζ₁ - conj ζ₂)]
    simp [star_sub]
  rw [hzz, div_le_div_iff₀ hdpos h0]
  -- ‖num‖ ‖1-sc‖ ≤ 2 X ‖w̄₁ - w₂‖ ‖ζ̄₁-ζ₂‖ / ‖ζ̄₁ - ζ₂‖ ... cross-multiplied
  have hz0 : 0 < ‖conj ζ₁ - ζ₂‖ := norm_pos_iff.2 hzne
  have key : ‖NTrace (dg f (conj ζ₁) * A * dg f ζ₂)‖ *
      ‖1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂)‖ ≤ 2 * X * ‖conj w₁ - w₂‖ := by
    calc ‖NTrace (dg f (conj ζ₁) * A * dg f ζ₂)‖ * ‖1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂)‖
        ≤ (‖ζ₁ - ζ₂‖ * X) * (2 * ‖hybridDen σ (dg f ζ₁) (dg f ζ₂)‖) :=
          mul_le_mul hnum' hd2 (norm_nonneg _) (by positivity)
      _ = 2 * X * (‖ζ₁ - ζ₂‖ * ‖hybridDen σ (dg f ζ₁) (dg f ζ₂)‖) := by ring
      _ ≤ 2 * X * ‖conj w₁ - w₂‖ := by rw [hnorm_pp]; gcongr
  rw [← hnorm_mp] at key
  calc _ ≤ _ := key
    _ = _ := by ring

end MixedPlus

/-!
## The fourfold approximation `M̂` (CEH (5.24))
-/

/-- The hybrid fourfold approximation `M̂_σ = -¼(M^A_{++} + M^A_{--} - M^A_{+-} - M^A_{-+})`
(CEH (5.24), variance `σ`); at `σ = s` it is the `positiveDeterministicApprox (√s)`.
-/
def hatApprox (σ : ℝ) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (-(1 / 4 : ℂ)) • (twoResApprox σ M₁ A M₂ + twoResApprox σ M₁ᴴ A M₂ᴴ -
    twoResApprox σ M₁ A M₂ᴴ - twoResApprox σ M₁ᴴ A M₂)

theorem hatApprox_target {s : ℝ} (hs : 0 ≤ s) (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    hatApprox s M₁ A M₂ = positiveDeterministicApprox (Real.sqrt s : ℂ) M₁ A M₂ := by
  simp only [hatApprox, positiveDeterministicApprox, deterministicConstellation, chooseAdjoint,
    twoResApprox_eq_twoResolventApprox_sqrt hs]

/-- Monotone replacement in a bound `2(2√P√u)/D`. -/
theorem bound_mono {P u U D D₀ : ℝ} (hu : u ≤ U) (hD₀ : 0 < D₀) (hD : D₀ ≤ D) :
    2 * (2 * Real.sqrt P * Real.sqrt u) / D ≤ 4 * Real.sqrt P * Real.sqrt U / D₀ := by
  have h1 : Real.sqrt u ≤ Real.sqrt U := Real.sqrt_le_sqrt hu
  have hP := Real.sqrt_nonneg P
  have hu0 := Real.sqrt_nonneg u
  calc 2 * (2 * Real.sqrt P * Real.sqrt u) / D ≤ 2 * (2 * Real.sqrt P * Real.sqrt u) / D₀ :=
        div_le_div_of_nonneg_left (by positivity) hD₀ hD
    _ ≤ 4 * Real.sqrt P * Real.sqrt U / D₀ := by
        rw [div_le_div_iff_of_pos_right hD₀]; nlinarith

section Window

variable (f : Fin N → ℝ) {ζ₁ ζ₂ : ℂ} (A : Matrix (Fin N) (Fin N) ℂ) {s σ K κ B : ℝ}

/-- The uniform window constant `C(s, K, κ, B) = (2√(K/(sκ)) + 2B√(K/(sκ)³)) / (sκ²)`. -/
def lemma56Const (s K κ B : ℝ) : ℝ :=
  (2 * Real.sqrt (K / (s * κ)) + 2 * B * Real.sqrt (K / (s * κ) ^ 3)) / (s * κ ^ 2)

/-- **CEH Lemma 5.6 bounds 1–4, hybrid form, regular-window regime** (diagonal model).
Hypotheses: `N > 0`, `s > 0`, `0 ≤ σ ≤ s`, `Θᵢ > 0`, `s aᵢ < 1` (MDE), `A` regular,
window bounds `κ ≤ tᵢ ≤ K` (`κ > 0`) and `|ζ₁ - ζ̄₂| ≤ B` (under `θ = 1`, `B = 4sK` when
`|mᵢ| ≤ K`). Conclusion: in all four constellations and for `M̂_σ`, the trace is
`≤ C √P` with `C = lemma56Const s K κ B`, uniformly in `σ ∈ [0, s]`. -/
theorem lemma56_window_bound (hN : 0 < N) (hs : 0 < s) (hκ : 0 < κ)
    (hΘ₁ : 0 < ζ₁.im) (hΘ₂ : 0 < ζ₂.im)
    (hreg : NTrace (dg f ζ₁ * A * (dg f ζ₂)ᴴ) = 0) (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    (ha₁ : s * wardMass (dg f ζ₁) < 1) (ha₂ : s * wardMass (dg f ζ₂) < 1)
    (hκ₁ : κ ≤ (NTrace (dg f ζ₁)).im) (hκ₂ : κ ≤ (NTrace (dg f ζ₂)).im)
    (hK₁ : (NTrace (dg f ζ₁)).im ≤ K) (hK₂ : (NTrace (dg f ζ₂)).im ≤ K)
    (hB : ‖ζ₁ - conj ζ₂‖ ≤ B) :
    ‖NTrace (twoResApprox σ (dg f ζ₁) A (dg f ζ₂))‖ ≤
        lemma56Const s K κ B * Real.sqrt (chainP f ζ₁ ζ₂ A) ∧
      ‖NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂)ᴴ)‖ ≤
        lemma56Const s K κ B * Real.sqrt (chainP f ζ₁ ζ₂ A) ∧
      NTrace (twoResApprox σ (dg f ζ₁) A (dg f ζ₂)ᴴ) = 0 ∧
      ‖NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂))‖ ≤
        lemma56Const s K κ B * Real.sqrt (chainP f ζ₁ ζ₂ A) ∧
      ‖NTrace (hatApprox σ (dg f ζ₁) A (dg f ζ₂))‖ ≤
        lemma56Const s K κ B * Real.sqrt (chainP f ζ₁ ζ₂ A) := by
  set t₁ := (NTrace (dg f ζ₁)).im
  set t₂ := (NTrace (dg f ζ₂)).im
  set P := chainP f ζ₁ ζ₂ A
  have hK : 0 ≤ K := (hκ.le.trans hκ₁).trans hK₁
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hW₁ := im_mul_wardMass_resEntry f ζ₁
  have hW₂ := im_mul_wardMass_resEntry f ζ₂
  -- `Θᵢ ≥ s tᵢ ≥ s κ`
  have hΘt₁ : s * t₁ ≤ ζ₁.im := by
    have : s * t₁ = ζ₁.im * (s * wardMass (dg f ζ₁)) := by
      rw [show t₁ = ζ₁.im * wardMass (dg f ζ₁) from hW₁.symm]; ring
    rw [this]; nlinarith
  have hΘt₂ : s * t₂ ≤ ζ₂.im := by
    have : s * t₂ = ζ₂.im * (s * wardMass (dg f ζ₂)) := by
      rw [show t₂ = ζ₂.im * wardMass (dg f ζ₂) from hW₂.symm]; ring
    rw [this]; nlinarith
  have hsκ : 0 < s * κ := mul_pos hs hκ
  have hΘκ₁ : s * κ ≤ ζ₁.im := le_trans (mul_le_mul_of_nonneg_left hκ₁ hs.le) hΘt₁
  have hΘκ₂ : s * κ ≤ ζ₂.im := le_trans (mul_le_mul_of_nonneg_left hκ₂ hs.le) hΘt₂
  -- the stable denominator
  have hden : 2 * s * κ ^ 2 ≤ ‖1 - (s : ℂ) * NTrace (dg f ζ₁ * dg f ζ₂)‖ := by
    have h := half_mul_sq_le_norm_one_sub hN hs.le (dg f ζ₁) (dg f ζ₂) ha₁.le ha₂.le
    have : 2 * κ ≤ t₁ + t₂ := by linarith
    have h4 : (2 * κ) ^ 2 ≤ (t₁ + t₂) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
    have : 2 * s * κ ^ 2 ≤ s * (t₁ + t₂) ^ 2 / 2 := by nlinarith
    exact this.trans h
  have hD₀ : 0 < 2 * s * κ ^ 2 := by positivity
  -- the three scalar ratios
  have hu₁ : t₂ / ζ₁.im ≤ K / (s * κ) := by
    rw [div_le_div_iff₀ (by linarith) hsκ]; nlinarith
  have hu₂ : t₁ / ζ₂.im ≤ K / (s * κ) := by
    rw [div_le_div_iff₀ (by linarith) hsκ]; nlinarith
  have hu₃ : wardMass (dg f ζ₁) / (ζ₁.im * ζ₂.im) ≤ K / (s * κ) ^ 3 := by
    have ha : wardMass (dg f ζ₁) = t₁ / ζ₁.im := by
      rw [eq_div_iff hΘ₁.ne', mul_comm]; exact hW₁
    rw [ha, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (s * κ) ^ 3 ≤ ζ₁.im * (ζ₁.im * ζ₂.im) := by
      have := mul_le_mul hΘκ₁ (mul_le_mul hΘκ₁ hΘκ₂ hsκ.le hΘ₁.le) (by positivity) hΘ₁.le
      nlinarith
    have ht₁0 : 0 ≤ t₁ := hκ.le.trans hκ₁
    nlinarith [mul_le_mul_of_nonneg_right hK₁ (pow_pos hsκ 3).le,
      mul_le_mul_of_nonneg_left h3 hK]
  have hp := Real.sqrt_nonneg P
  have hsk2 : 0 < s * κ ^ 2 := by positivity
  have hC1 : 4 * Real.sqrt P * Real.sqrt (K / (s * κ)) / (2 * s * κ ^ 2) ≤
      lemma56Const s K κ B * Real.sqrt P := by
    have e : 4 * Real.sqrt P * Real.sqrt (K / (s * κ)) / (2 * s * κ ^ 2) =
        (2 * Real.sqrt (K / (s * κ)) / (s * κ ^ 2)) * Real.sqrt P := by
      field_simp; ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hp
    rw [lemma56Const]
    apply div_le_div_of_nonneg_right _ hsk2.le
    have : 0 ≤ 2 * B * Real.sqrt (K / (s * κ) ^ 3) := by positivity
    linarith
  have hC3 : 4 * Real.sqrt P * Real.sqrt (K / (s * κ) ^ 3) / (2 * s * κ ^ 2) * B ≤
      lemma56Const s K κ B * Real.sqrt P := by
    have e : 4 * Real.sqrt P * Real.sqrt (K / (s * κ) ^ 3) / (2 * s * κ ^ 2) * B =
        (2 * B * Real.sqrt (K / (s * κ) ^ 3) / (s * κ ^ 2)) * Real.sqrt P := by
      field_simp; ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hp
    rw [lemma56Const]
    apply div_le_div_of_nonneg_right _ hsk2.le
    have : 0 ≤ 2 * Real.sqrt (K / (s * κ)) := by positivity
    linarith
  have hpp : ‖NTrace (twoResApprox σ (dg f ζ₁) A (dg f ζ₂))‖ ≤
      lemma56Const s K κ B * Real.sqrt P :=
    ((norm_twoResApprox_pp_le f A hΘ₁ hΘ₂ hreg hσ0 hσs ha₁ ha₂).trans
      (bound_mono hu₁ hD₀ hden)).trans hC1
  have hmm : ‖NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂)ᴴ)‖ ≤
      lemma56Const s K κ B * Real.sqrt P :=
    ((norm_twoResApprox_mm_le f A hΘ₁ hΘ₂ hreg hσ0 hσs ha₁ ha₂).trans
      (bound_mono hu₂ hD₀ hden)).trans hC1
  have hpm := NTrace_twoResApprox_pm_eq_zero (σ := σ) f A hreg
  have hmp : ‖NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂))‖ ≤
      lemma56Const s K κ B * Real.sqrt P := by
    refine (norm_twoResApprox_mp_le f A hΘ₁ hΘ₂ hreg hσ0 hσs ha₁ ha₂).trans ?_
    rw [mul_div_right_comm]
    refine le_trans ?_ hC3
    exact mul_le_mul (bound_mono hu₃ hD₀ hden) hB (norm_nonneg _) (by positivity)
  refine ⟨hpp, hmm, hpm, hmp, ?_⟩
  have hC0 : 0 ≤ lemma56Const s K κ B * Real.sqrt P :=
    (norm_nonneg _).trans hpp
  rw [hatApprox, NTrace_smul, NTrace_sub, NTrace_sub, NTrace_add, hpm, sub_zero, norm_mul]
  have h4 : ‖(-(1 / 4 : ℂ))‖ = 1 / 4 := by rw [norm_neg, norm_div]; norm_num
  rw [h4]
  have := norm_sub_le (NTrace (twoResApprox σ (dg f ζ₁) A (dg f ζ₂)) +
    NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂)ᴴ))
    (NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂)))
  have := norm_add_le (NTrace (twoResApprox σ (dg f ζ₁) A (dg f ζ₂)))
    (NTrace (twoResApprox σ (dg f ζ₁)ᴴ A (dg f ζ₂)ᴴ))
  linarith

end Window

/-!
## `√P` and the control `s₂(σ)`
-/

theorem NTrace_matrixImaginaryPart_eq (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (matrixImaginaryPart X) = (((NTrace X).im : ℝ) : ℂ) := by
  have hre := re_NTrace_matrixImaginaryPart X
  have him : (NTrace (matrixImaginaryPart X)).im = 0 := by
    simp only [NTrace, Conventions.normalizedTrace, matrixImaginaryPart, Matrix.trace_smul,
      Matrix.trace_sub, Matrix.trace_conjTranspose, smul_eq_mul]
    have hN : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hN]
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

/-- `P = t₁ t₂ ⟨Γ₁AΓ₂Aᴴ⟩` (real part), for `tᵢ = Im⟨Mᵢ⟩ ≠ 0`. -/
theorem chain_eq_mul_sTwoBase (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) (h₁ : (NTrace M₁).im ≠ 0)
    (h₂ : (NTrace M₂).im ≠ 0) :
    (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re =
      (NTrace M₁).im * (NTrace M₂).im * sTwoBase M₁ M₂ A := by
  rw [sTwoBase, gammaMatrix, gammaMatrix, NTrace_matrixImaginaryPart_eq,
    NTrace_matrixImaginaryPart_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, NTrace_smul]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  field_simp

/-- **`√P ≤ π √(ρ₁ρ₂) s₂(σ)`** for every `σ ≥ 0`, `ρᵢ = cehDensityOf Mᵢ`, `Im⟨Mᵢ⟩ > 0`. -/
theorem sqrt_chain_le (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ) (h₁ : 0 < (NTrace M₁).im)
    (h₂ : 0 < (NTrace M₂).im) {σ : ℝ} (hσ : 0 ≤ σ) :
    Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re ≤
      Real.pi * Real.sqrt (cehDensityOf M₁ * cehDensityOf M₂) * sTwoAt σ M₁ M₂ A := by
  rw [chain_eq_mul_sTwoBase M₁ M₂ A h₁.ne' h₂.ne', cehDensityOf_eq, cehDensityOf_eq]
  have hπ := Real.pi_pos
  have hb := sTwoBase_le_sTwoAt_sq hσ M₁ M₂ A
  have hs0 : 0 ≤ sTwoAt σ M₁ M₂ A := Real.sqrt_nonneg _
  have e1 : Real.pi * Real.sqrt ((NTrace M₁).im / Real.pi * ((NTrace M₂).im / Real.pi)) =
      Real.sqrt ((NTrace M₁).im * (NTrace M₂).im) := by
    rw [show (NTrace M₁).im / Real.pi * ((NTrace M₂).im / Real.pi) =
        (NTrace M₁).im * (NTrace M₂).im / Real.pi ^ 2 by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hπ.le]
    field_simp
  calc Real.sqrt ((NTrace M₁).im * (NTrace M₂).im * sTwoBase M₁ M₂ A)
      ≤ Real.sqrt ((NTrace M₁).im * (NTrace M₂).im * sTwoAt σ M₁ M₂ A ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = Real.sqrt ((NTrace M₁).im * (NTrace M₂).im) * sTwoAt σ M₁ M₂ A := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs0]
    _ = _ := by rw [e1]

end BlockBand.Native.CEH.ETH
