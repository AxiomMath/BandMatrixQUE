module

public import Mathlib

/-!
# Common-port mean: stability of the common-port ladder

Deterministic; no measure. Domain: `0 ≤ b < 1/2`, `c = 1 - 2b`, complex coefficients
`𝖠_ab` with absolute row sums `≤ ρ`, complex `ω` (the factor `u_p conj ḡ_p ≈ |a|² = 1`) and
residuals `r_a, r_p`, under the contraction condition `q = ρ(c + 2b²|ω|) < 1`. Norm: the
complex modulus, `∞`-norm over the two blocks.

* `ladder_rowSum_identity`: `d(c + 2b²) = 1 - bc/(1-b)`, `d = (1-b)⁻¹`; `ladder_rowSum_lt_one`.
* `ladder_stability`: every solution of the perturbed ladder satisfies
  `|t_a - 1/c| ≤ Err/(1-q)` with
  `Err = ρ b(|ω-1|/c + |r_p|) + γ max_a|s_a - d| + max_a|r_a|`, `s_a = Σ_b 𝖠_ab`, `γ = (1-b)/c`,
  and `|t_p - 1/c| ≤ 2b|ω| Err/(1-q) + |ω-1|/c + |r_p|`.
* `ladder_source_le`: `|c t_a + b t_p - γ| ≤ c|t_a - 1/c| + b|t_p - 1/c|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

/-- **Row sum of the feedback matrix** of the common-port ladder. Deterministic, no measure; real identity for every `b < 1`:
`d(c + 2b²) = 1 - bc/(1-b)`, `d = (1-b)⁻¹`, `c = 1 - 2b`. -/
theorem ladder_rowSum_identity {b : ℝ} (hb : b < 1) :
    (1 - b)⁻¹ * ((1 - 2 * b) + 2 * b ^ 2) = 1 - b * (1 - 2 * b) / (1 - b) := by
  have h : (1 - b) ≠ 0 := by linarith
  field_simp
  ring

/-- **The feedback row sum is a strict contraction.** Deterministic, no measure; for `0 < b < 1/2`
(strict `0 < b`): `d(c + 2b²) < 1`, `d = (1-b)⁻¹`, `c = 1 - 2b`. -/
theorem ladder_rowSum_lt_one {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    (1 - b)⁻¹ * ((1 - 2 * b) + 2 * b ^ 2) < 1 := by
  rw [ladder_rowSum_identity (by linarith)]
  have : 0 < b * (1 - 2 * b) / (1 - b) := by
    apply div_pos (mul_pos hb0 (by linarith)) (by linarith)
  linarith

/-- **Stability of the perturbed common-port ladder** (deterministic stability core only).
Deterministic, no measure. Hypotheses: `0 ≤ b < 1/2`, `c = 1 - 2b`; complex coefficients `A_aj`
(`a, j ∈ Fin 2`) with absolute row sums `Σ_j |A_aj| ≤ ρ`; complex `ω`, residuals `r_a, r_p`; the
contraction condition `q = ρ(c + 2b²|ω|) < 1`. Norm: complex modulus, `∞`-norm over the two blocks.
Conclusion, for every solution `t, t_p` of `t_a = Σ_j A_aj(c t_j + b t_p) + r_a`,
`t_p = ω(1 + b(t₀ + t₁)) + r_p` (an a-priori bound; existence is not asserted):
`|t_a - 1/c| ≤ Err/(1-q)` and `|t_p - 1/c| ≤ 2b|ω| Err/(1-q) + |ω-1|/c + |r_p|`, where
`Err = ρb(|ω-1|/c + |r_p|) + γ max_a|Σ_j A_aj - d| + max_a|r_a|`, `γ = (1-b)/c`, `d = (1-b)⁻¹`.
The link between the row-sum defect `Σ_j A_aj - d` and `δ = matchedDistance` is not part of
this lemma. -/
theorem ladder_stability {A : Fin 2 → Fin 2 → ℂ} {t r : Fin 2 → ℂ} {tp rp ω : ℂ} {b ρ : ℝ}
    (hb0 : 0 ≤ b) (hb : b < 1 / 2) (hρ : ∀ a, ∑ j, ‖A a j‖ ≤ ρ)
    (hq : ρ * ((1 - 2 * b) + 2 * b ^ 2 * ‖ω‖) < 1)
    (ht : ∀ a, t a = ∑ j, A a j * (((1 - 2 * b : ℝ) : ℂ) * t j + (b : ℂ) * tp) + r a)
    (htp : tp = ω * (1 + (b : ℂ) * (t 0 + t 1)) + rp) :
    let c : ℝ := 1 - 2 * b
    let q : ℝ := ρ * (c + 2 * b ^ 2 * ‖ω‖)
    let Err : ℝ := ρ * b * (‖ω - 1‖ / c + ‖rp‖) +
      (1 - b) / c * (max ‖∑ j, A 0 j - ((1 - b : ℝ) : ℂ)⁻¹‖ ‖∑ j, A 1 j - ((1 - b : ℝ) : ℂ)⁻¹‖) +
      max ‖r 0‖ ‖r 1‖
    (∀ a, ‖t a - ((c : ℝ) : ℂ)⁻¹‖ ≤ Err / (1 - q)) ∧
      ‖tp - ((c : ℝ) : ℂ)⁻¹‖ ≤ 2 * b * ‖ω‖ * (Err / (1 - q)) + ‖ω - 1‖ / c + ‖rp‖ := by
  intro c q Err
  have hc : 0 < c := by simp only [c]; linarith
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hb1 : (1 - b : ℝ) ≠ 0 := by linarith
  set τ : ℂ := ((c : ℝ) : ℂ)⁻¹ with hτ
  have hτn : ‖τ‖ = 1 / c := by
    rw [hτ, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le, one_div]
  set e : Fin 2 → ℂ := fun a => t a - τ with he
  set ep : ℂ := tp - τ with hep
  -- `1 + 2bτ = τ`
  have hτ1 : 1 + (b : ℂ) * (τ + τ) = τ := by
    rw [hτ]; field_simp; simp only [c]; push_cast; ring
  -- `(cτ + bτ) d = τ`, i.e. `γ d = τ`
  have hγ : (((1 - 2 * b : ℝ) : ℂ) * τ + (b : ℂ) * τ) = ((1 - b : ℝ) : ℂ) * τ := by
    push_cast; ring
  have hep_eq : ep = ω * (b : ℂ) * (e 0 + e 1) + (ω - 1) * τ + rp := by
    simp only [hep, he]
    rw [htp]
    linear_combination ω * hτ1
  set E : ℝ := max ‖e 0‖ ‖e 1‖ with hE
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (le_max_left _ _)
  have heE : ∀ a, ‖e a‖ ≤ E := by
    intro a; fin_cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hepn : ‖ep‖ ≤ 2 * b * ‖ω‖ * E + ‖ω - 1‖ / c + ‖rp‖ := by
    rw [hep_eq]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      le_rfl)
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
      have : ‖e 0 + e 1‖ ≤ 2 * E := (norm_add_le _ _).trans (by linarith [heE 0, heE 1])
      calc ‖ω‖ * b * ‖e 0 + e 1‖ ≤ ‖ω‖ * b * (2 * E) := by gcongr
        _ = 2 * b * ‖ω‖ * E := by ring
    · rw [norm_mul, hτn]; exact le_of_eq (by ring)
  -- the error equation for the top traces
  have hea : ∀ a, e a = ∑ j, A a j * (((1 - 2 * b : ℝ) : ℂ) * e j + (b : ℂ) * ep) +
      ((1 - b : ℝ) : ℂ) * τ * (∑ j, A a j - ((1 - b : ℝ) : ℂ)⁻¹) + r a := by
    intro a
    have h1 : ∀ j, A a j * (((1 - 2 * b : ℝ) : ℂ) * t j + (b : ℂ) * tp) =
        A a j * (((1 - 2 * b : ℝ) : ℂ) * e j + (b : ℂ) * ep) +
          A a j * (((1 - b : ℝ) : ℂ) * τ) := by
      intro j; simp only [he, hep]; rw [← hγ]; ring
    have hd : ((1 - b : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb1)
    show t a - τ = _
    rw [ht a, Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib, ← Finset.sum_mul]
    linear_combination τ * hd
  set Sd : ℝ := max ‖∑ j, A 0 j - ((1 - b : ℝ) : ℂ)⁻¹‖ ‖∑ j, A 1 j - ((1 - b : ℝ) : ℂ)⁻¹‖
  set Rm : ℝ := max ‖r 0‖ ‖r 1‖
  have hSd : ∀ a, ‖∑ j, A a j - ((1 - b : ℝ) : ℂ)⁻¹‖ ≤ Sd := by
    intro a; fin_cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hRm : ∀ a, ‖r a‖ ≤ Rm := by
    intro a; fin_cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hγn : ‖((1 - b : ℝ) : ℂ) * τ‖ = (1 - b) / c := by
    rw [norm_mul, hτn, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; ring
  have hbound : ∀ a, ‖e a‖ ≤ q * E + Err := by
    intro a
    rw [hea a]
    have hinner : ∀ j, ‖((1 - 2 * b : ℝ) : ℂ) * e j + (b : ℂ) * ep‖ ≤
        c * E + b * (2 * b * ‖ω‖ * E + ‖ω - 1‖ / c + ‖rp‖) := by
      intro j
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
        exact mul_le_mul_of_nonneg_left (heE j) hc.le
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
        exact mul_le_mul_of_nonneg_left hepn hb0
    have hsum : ‖∑ j, A a j * (((1 - 2 * b : ℝ) : ℂ) * e j + (b : ℂ) * ep)‖ ≤
        ρ * (c * E + b * (2 * b * ‖ω‖ * E + ‖ω - 1‖ / c + ‖rp‖)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j, ‖A a j * (((1 - 2 * b : ℝ) : ℂ) * e j + (b : ℂ) * ep)‖
          ≤ ∑ j, ‖A a j‖ * (c * E + b * (2 * b * ‖ω‖ * E + ‖ω - 1‖ / c + ‖rp‖)) :=
            Finset.sum_le_sum fun j _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hinner j) (norm_nonneg _)
        _ = (∑ j, ‖A a j‖) * (c * E + b * (2 * b * ‖ω‖ * E + ‖ω - 1‖ / c + ‖rp‖)) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ ρ * (c * E + b * (2 * b * ‖ω‖ * E + ‖ω - 1‖ / c + ‖rp‖)) :=
            mul_le_mul_of_nonneg_right (hρ a) (by positivity)
    have hmid : ‖((1 - b : ℝ) : ℂ) * τ * (∑ j, A a j - ((1 - b : ℝ) : ℂ)⁻¹)‖ ≤
        (1 - b) / c * Sd := by
      rw [norm_mul, hγn]
      exact mul_le_mul_of_nonneg_left (hSd a) (by
        have : 0 ≤ 1 - b := by linarith
        positivity)
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add hsum hmid)) (hRm a)) |>.trans (le_of_eq ?_)
    simp only [q, Err]
    ring
  have hEb : E ≤ q * E + Err := max_le (hbound 0) (hbound 1)
  have hq1 : 0 < 1 - q := by simp only [q]; linarith
  have hEfin : E ≤ Err / (1 - q) := by
    rw [le_div_iff₀ hq1]; linarith
  refine ⟨fun a => (heE a).trans hEfin, ?_⟩
  refine hepn.trans ?_
  have : 0 ≤ 2 * b * ‖ω‖ := by positivity
  gcongr

/-- **Top source coefficient** (`ct_i + bv_s = (1-b)/c + O(δ)` in Lipschitz form). Deterministic, no measure; for
`0 ≤ b < 1/2`, `c = 1 - 2b`, `γ = (1-b)/c` and all complex `t_a, t_p`:
`|c t_a + b t_p - γ| ≤ c|t_a - 1/c| + b|t_p - 1/c|` (complex modulus). -/
theorem ladder_source_le {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (ta tp : ℂ) :
    ‖((1 - 2 * b : ℝ) : ℂ) * ta + (b : ℂ) * tp - (((1 - b) / (1 - 2 * b) : ℝ) : ℂ)‖ ≤
      (1 - 2 * b) * ‖ta - (((1 - 2 * b : ℝ)) : ℂ)⁻¹‖ +
        b * ‖tp - (((1 - 2 * b : ℝ)) : ℂ)⁻¹‖ := by
  have hc : (1 - 2 * b : ℝ) ≠ 0 := by linarith
  have hc' : ((1 - 2 * b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hid : ((1 - 2 * b : ℝ) : ℂ) * ta + (b : ℂ) * tp - (((1 - b) / (1 - 2 * b) : ℝ) : ℂ) =
      ((1 - 2 * b : ℝ) : ℂ) * (ta - ((1 - 2 * b : ℝ) : ℂ)⁻¹) +
        (b : ℂ) * (tp - ((1 - 2 * b : ℝ) : ℂ)⁻¹) := by
    push_cast
    field_simp
    ring
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]

end BlockBand.Critical.CommonPort
