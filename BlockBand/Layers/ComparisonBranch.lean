module

public import BlockBand.Layers.ComparisonStability

/-!
# Branch identification from verifiable hypotheses

From the proof of the layer-contraction lemma:

> The port `w` is bounded below as above. On `d(X) ≤ d_*` the top `v_i` is also bounded below:
> the inverse identity comparing `M` with `R` gives a fixed lower bound on each normalized squared
> block column of `M` from that of `R`, which equals `-Im(W⁻¹ Tr R_ii)/η`. All these quantities are
> bounded above.

`BlockBand.Layers.cmp_sep_branch` / `cmp_com_branch` (module `ComparisonStability`) assume a lower
bound `-Im m̄_i ≥ y₀` on the approximate top means. This module derives that lower bound
deterministically from hypotheses that can be checked directly on the layer means:

* the means solve the equations up to residuals `‖r‖, ‖r'‖ ≤ η` (the trace–matrix lemma);
* `-Im m̄_i ≥ 0` (for the layer means this is the sign of `-Im 𝒢_pp ≥ 0`, from
  `𝒢 - 𝒢* = -2i Im z 𝒢 P_ports 𝒢*`);
* `|m̄_i| ≤ K` (from the absorber bound on `‖𝒢‖`).

The port lower bound comes from the residual port equation alone: `-Im (z - b m̄)⁻¹ =
|(z - b m̄)⁻¹|² Im(z - b m̄) ≥ Im z / (3 + K)²`. The top lower bound uses the row comparison
`R = M̄ (1 - D R)` (`cmp_row_compare`): `Σ_q |R_pq|² ≤ 2 (1 + Δ²/ζ_R²) Σ_q |M̄_pq|²`, the row-mass
identities for `M̄` and `R`, and `-Im tr_i R ≥ -Im a - d(X) ≥ α₀/2` on `d(X) ≤ α₀/2`.

## Main results

* `cmp_top_lower`: the abstract top lower bound.
* `cmp_sep_lower`, `cmp_com_lower`: the lower bounds for both port cases.
* `cmp_comparison_branch`: the deterministic comparison statement of
  `cmp_comparison_deterministic` with the branch clause under the hypotheses above.

All statements are deterministic and uniform in `W` and the Hermitian two-port `X`; constants
depend only on `b, κ, K`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Layers

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Row comparison.** `M̄ = (H - diag σ̄)⁻¹` with `Im σ̄ < 0`, `R = (H - diag σ⁰)⁻¹` with
`-Im σ⁰ ≥ y > 0`, `|σ̄_k - σ⁰_k| ≤ Δ`: `Σ_q |R_pq|² ≤ 2 (1 + Δ²/y²) Σ_q |M̄_pq|²`
(from `R = M̄ - M̄ diag(σ̄ - σ⁰) R` and the row bound `y² |v R|² ≤ |v|²`). -/
theorem cmp_row_compare (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ σ₀ : n → ℂ) {y Δ : ℝ}
    (hy : 0 < y) (hσ' : ∀ p, (σ p).im < 0) (hσ₀ : ∀ p, y ≤ -(σ₀ p).im)
    (hΔ : ∀ k, ‖σ k - σ₀ k‖ ≤ Δ) (p : n) :
    ∑ q, ‖(H - diagonal σ₀)⁻¹ p q‖ ^ 2 ≤
      2 * (1 + Δ ^ 2 / y ^ 2) * ∑ q, ‖(H - diagonal σ)⁻¹ p q‖ ^ 2 := by
  have hσ₀' : ∀ p, (σ₀ p).im < 0 := fun p => by linarith [hσ₀ p]
  set M := (H - diagonal σ)⁻¹ with hM
  set R := (H - diagonal σ₀)⁻¹ with hR
  set w : n → ℂ := fun k => M p k * (σ - σ₀) k with hw
  have hrow : ∀ q, R p q = M p q - (w ᵥ* R) q := fun q => by
    have h := congrFun (congrFun (cmp_inv_sub_inv H hH σ σ₀ hσ' hσ₀') p) q
    rw [Matrix.sub_apply, cmp_mul_diag_mul_apply] at h
    rw [← hM, ← hR] at h
    have : (w ᵥ* R) q = ∑ k, M p k * (σ - σ₀) k * R k q := rfl
    rw [this, ← h]; ring
  have h1 := cmp_vecMul_le H hH σ₀ hy hσ₀ w
  rw [← hR] at h1
  have h2 : cmpSq w ≤ Δ ^ 2 * ∑ k, ‖M p k‖ ^ 2 := by
    rw [cmpSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hw]
    simp only [norm_mul, mul_pow, Pi.sub_apply]
    have := pow_le_pow_left₀ (norm_nonneg _) (hΔ k) 2
    have := mul_le_mul_of_nonneg_left this (sq_nonneg ‖M p k‖)
    linarith
  have h3 : cmpSq (w ᵥ* R) ≤ Δ ^ 2 / y ^ 2 * ∑ k, ‖M p k‖ ^ 2 := by
    have hy2 : 0 < y ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hy2]
    linarith
  have h4 : ∀ q, ‖R p q‖ ^ 2 ≤ 2 * ‖M p q‖ ^ 2 + 2 * ‖(w ᵥ* R) q‖ ^ 2 := fun q => by
    rw [hrow q]
    have := norm_sub_le (M p q) ((w ᵥ* R) q)
    have h0 := norm_nonneg (M p q - (w ᵥ* R) q)
    nlinarith [sq_nonneg (‖M p q‖ - ‖(w ᵥ* R) q‖)]
  calc ∑ q, ‖R p q‖ ^ 2 ≤ ∑ q, (2 * ‖M p q‖ ^ 2 + 2 * ‖(w ᵥ* R) q‖ ^ 2) :=
        Finset.sum_le_sum fun q _ => h4 q
    _ = 2 * ∑ q, ‖M p q‖ ^ 2 + 2 * cmpSq (w ᵥ* R) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
    _ ≤ 2 * ∑ q, ‖M p q‖ ^ 2 + 2 * (Δ ^ 2 / y ^ 2 * ∑ k, ‖M p k‖ ^ 2) := by linarith
    _ = 2 * (1 + Δ ^ 2 / y ^ 2) * ∑ q, ‖M p q‖ ^ 2 := by ring

end General

section Block

variable {W : ℕ}

/-- Total row block mass: `Σ_j A_ij = W⁻¹ Σ_x Σ_q |M_(i,x) q|²`. -/
theorem cmp_sum_rowMass (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    ∑ j, cmpRowMass M i j = (W : ℝ)⁻¹ * ∑ x : Fin W, ∑ q, ‖M (i, x) q‖ ^ 2 := by
  simp only [cmpRowMass, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]

/-- **Top lower bound**. `H` Hermitian; `M̄ = (H - diag σ̄)⁻¹` with
`-Im σ̄_j ≥ y₃ > 0`; `R = (H - s₀)⁻¹` for a constant shift with `0 < ζ_lo ≤ -Im s₀ ≤ 1`,
`-Im tr_i R ≥ v_R`; `|σ̄_j - s₀| ≤ Δ`. Then
`-Im tr_i M̄ ≥ y₃ v_R / (2 (1 + Δ²/ζ_lo²))`. -/
theorem cmp_top_lower (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    (σ : Fin 2 → ℂ) (s₀ : ℂ) {y₃ ζlo Δ vR : ℝ} (hy₃ : 0 < y₃) (hζlo : 0 < ζlo)
    (hs₀lo : ζlo ≤ -s₀.im) (hs₀hi : -s₀.im ≤ 1) (hσ : ∀ j, y₃ ≤ -(σ j).im)
    (hΔ : ∀ j, ‖σ j - s₀‖ ≤ Δ) (i : Fin 2)
    (hvR : vR ≤ -(blockTrace (cmpInv H (fun _ => s₀)) i).im) :
    y₃ * vR / (2 * (1 + Δ ^ 2 / ζlo ^ 2)) ≤ -(blockTrace (cmpInv H σ) i).im := by
  have hζR0 : 0 < -s₀.im := lt_of_lt_of_le hζlo hs₀lo
  have hσ₀y : ∀ p : Fin 2 × Fin W, ζlo ≤ -(cmpExt (fun _ => s₀) p).im := fun _ => hs₀lo
  have hσim : ∀ j, (σ j).im < 0 := fun j => by linarith [hσ j]
  have hs₀im : ∀ j : Fin 2, ((fun _ => s₀) j).im < 0 := fun _ => by simp only; linarith
  -- row mass of `R`
  have hRmass : ∑ j, cmpRowMass (cmpInv H (fun _ => s₀)) i j * (-s₀.im) =
      -(blockTrace (cmpInv H (fun _ => s₀)) i).im :=
    cmp_rowMass_im H hH (fun _ => s₀) hs₀im i
  rw [← Finset.sum_mul] at hRmass
  -- row mass of `M̄`
  have hMmass := cmp_rowMass_im H hH σ hσim i
  have hMlow : y₃ * ∑ j, cmpRowMass (cmpInv H σ) i j ≤ -(blockTrace (cmpInv H σ) i).im := by
    rw [← hMmass, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have := mul_le_mul_of_nonneg_left (hσ j) (cmpRowMass_nonneg (cmpInv H σ) i j)
      linarith
  -- comparison of the two row masses
  have hK0 : 0 < 2 * (1 + Δ ^ 2 / ζlo ^ 2) := by positivity
  have hcmp : ∑ j, cmpRowMass (cmpInv H (fun _ => s₀)) i j ≤
      2 * (1 + Δ ^ 2 / ζlo ^ 2) * ∑ j, cmpRowMass (cmpInv H σ) i j := by
    rw [cmp_sum_rowMass, cmp_sum_rowMass]
    calc (W : ℝ)⁻¹ * ∑ x : Fin W, ∑ q, ‖cmpInv H (fun _ => s₀) (i, x) q‖ ^ 2
        ≤ (W : ℝ)⁻¹ * ∑ x : Fin W, 2 * (1 + Δ ^ 2 / ζlo ^ 2) *
            ∑ q, ‖cmpInv H σ (i, x) q‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
          exact cmp_row_compare H hH (cmpExt σ) (cmpExt (fun _ => s₀)) hζlo
            (fun p => hσim p.1) hσ₀y (fun k => hΔ k.1) (i, x)
      _ = 2 * (1 + Δ ^ 2 / ζlo ^ 2) * ((W : ℝ)⁻¹ * ∑ x : Fin W,
            ∑ q, ‖cmpInv H σ (i, x) q‖ ^ 2) := by
          rw [← Finset.mul_sum]; ring
  -- assemble
  have hA0 : 0 ≤ ∑ j, cmpRowMass (cmpInv H σ) i j :=
    Finset.sum_nonneg fun j _ => cmpRowMass_nonneg _ _ _
  have hRA : vR ≤ ∑ j, cmpRowMass (cmpInv H (fun _ => s₀)) i j := by
    have hR0 : 0 ≤ ∑ j, cmpRowMass (cmpInv H (fun _ => s₀)) i j :=
      Finset.sum_nonneg fun j _ => cmpRowMass_nonneg _ _ _
    have := mul_le_mul_of_nonneg_left hs₀hi hR0
    linarith
  have h1 : vR ≤ 2 * (1 + Δ ^ 2 / ζlo ^ 2) * ∑ j, cmpRowMass (cmpInv H σ) i j := hRA.trans hcmp
  have h2 : vR / (2 * (1 + Δ ^ 2 / ζlo ^ 2)) ≤ ∑ j, cmpRowMass (cmpInv H σ) i j := by
    rw [div_le_iff₀ hK0]; linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hy₃.le
  rw [mul_div_assoc]
  linarith

/-- Port lower bound from the residual port equation: for `Im(z - b w) ≥ ζ₀ > 0` and
`|z - b w| ≤ 3 + K`, `-Im (z - b w)⁻¹ ≥ ζ₀ / (3 + K)²` and `|(z - b w)⁻¹| ≤ ζ₀⁻¹`. -/
theorem cmp_port_lower {q : ℂ} {ζ₀ K : ℝ} (hζ₀ : 0 < ζ₀) (hq : ζ₀ ≤ q.im) (hK : 0 ≤ K)
    (hqK : ‖q‖ ≤ 3 + K) : ζ₀ / (3 + K) ^ 2 ≤ -(q⁻¹).im ∧ ‖q⁻¹‖ ≤ ζ₀⁻¹ := by
  obtain ⟨h1, h2⟩ := cmp_inv_bounds hζ₀ hq hqK
  refine ⟨?_, h1⟩
  rw [cmp_neg_im_inv]
  have h3 : ((3 + K)⁻¹) ^ 2 ≤ ‖q⁻¹‖ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have h4 := mul_le_mul h3 hq hζ₀.le (sq_nonneg _)
  rw [inv_pow] at h4
  rw [div_eq_inv_mul]
  linarith

/-- **Lower bounds for approximate separate-port means**.
Hypotheses checkable on the layer means: residual equations with `‖r‖, ‖r'‖ ≤ η`,
`-Im m̄_i ≥ 0`, `|m̄_i| ≤ K`; `Im z ≥ ζ₀`, `|z| ≤ 3`; a constant reference shift `s₀` with
`ζ_lo ≤ -Im s₀ ≤ 1`, `|s₀| ≤ 1` and `-Im tr_i (H - s₀)⁻¹ ≥ v_R`. For `η ≤ min(1, w₁/2)`,
`w₁ = ζ₀/(3+K)²`: `-Im ū_i ≥ w₁ - η` and
`-Im m̄_i ≥ (b w₁/2) v_R / (2 (1 + Δ²/ζ_lo²)) - η`, `Δ = K + ζ₀⁻¹ + 2`. -/
theorem cmp_sep_lower {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hH : H.IsHermitian) {b ζ₀ K η ζlo vR : ℝ} {z s₀ : ℂ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3) (hK : 0 ≤ K)
    (hηw : η ≤ ζ₀ / (3 + K) ^ 2 / 2) (hη1 : η ≤ 1)
    (hζlo : 0 < ζlo) (hs₀lo : ζlo ≤ -s₀.im) (hs₀hi : -s₀.im ≤ 1) (hs₀n : ‖s₀‖ ≤ 1)
    (hvR : ∀ i, vR ≤ -(blockTrace (cmpInv H (fun _ => s₀)) i).im)
    (mb ub r r' : Fin 2 → ℂ)
    (happ : ∀ i, mb i = blockTrace (cmpInv H (cmpSepShift b mb ub)) i + r i ∧
      ub i = (z - (b : ℂ) * mb i)⁻¹ + r' i)
    (hr : ‖r‖ ≤ η) (hr' : ‖r'‖ ≤ η) (hpos : ∀ i, 0 ≤ -(mb i).im) (hKm : ∀ i, ‖mb i‖ ≤ K)
    (i : Fin 2) :
    b * (ζ₀ / (3 + K) ^ 2 / 2) * vR / (2 * (1 + (K + ζ₀⁻¹ + 2) ^ 2 / ζlo ^ 2)) - η ≤
        -(mb i).im ∧ ζ₀ / (3 + K) ^ 2 - η ≤ -(ub i).im := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hq : ∀ j, ζ₀ ≤ (z - (b : ℂ) * mb j).im ∧ ‖z - (b : ℂ) * mb j‖ ≤ 3 + K := fun j => by
    constructor
    · have : (z - (b : ℂ) * mb j).im = z.im + b * (-(mb j).im) := by
        simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
      rw [this]; have := mul_nonneg hb0.le (hpos j); linarith
    · have h1 := norm_sub_le z ((b : ℂ) * mb j)
      rw [cmp_norm_real_mul hb0.le] at h1
      have := mul_le_mul (show b ≤ 1 by linarith) (hKm j) (norm_nonneg _) zero_le_one
      linarith
  have hport := fun j => cmp_port_lower hζ₀ (hq j).1 hK (hq j).2
  have hrj : ∀ j, ‖r' j‖ ≤ η := fun j => (norm_le_pi_norm r' j).trans hr'
  have hw : ∀ j, ζ₀ / (3 + K) ^ 2 - η ≤ -(ub j).im := fun j => by
    rw [(happ j).2, Complex.add_im]
    have := (le_abs_self (r' j).im).trans ((Complex.abs_im_le_norm _).trans (hrj j))
    linarith [(hport j).1]
  set w₁ := ζ₀ / (3 + K) ^ 2 with hw₁
  have hw₁0 : 0 < w₁ := by positivity
  have hy₃ : ∀ j, b * (w₁ / 2) ≤ -(cmpSepShift b mb ub j).im := fun j => by
    simp only [cmpSepShift]
    rw [cmp_im_comb]
    have h1 := mul_nonneg hc0 (hpos j)
    have h2 := mul_le_mul_of_nonneg_left (show w₁ / 2 ≤ -(ub j).im by linarith [hw j]) hb0.le
    linarith
  have hΔ : ∀ j, ‖cmpSepShift b mb ub j - s₀‖ ≤ K + ζ₀⁻¹ + 2 := fun j => by
    simp only [cmpSepShift]
    have h1 := norm_sub_le (((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub j) s₀
    have h2 := norm_add_le (((1 - 2 * b : ℝ) : ℂ) * mb j) ((b : ℂ) * ub j)
    rw [cmp_norm_real_mul hc0, cmp_norm_real_mul hb0.le] at h2
    have h3 := mul_le_mul (show 1 - 2 * b ≤ 1 by linarith) (hKm j) (norm_nonneg _) zero_le_one
    have hub : ‖ub j‖ ≤ ζ₀⁻¹ + 1 := by
      rw [(happ j).2]
      have := norm_add_le ((z - (b : ℂ) * mb j)⁻¹) (r' j)
      linarith [(hport j).2, hrj j]
    have h4 := mul_le_mul (show b ≤ 1 by linarith) hub (norm_nonneg _) zero_le_one
    linarith
  have htop := cmp_top_lower H hH (cmpSepShift b mb ub) s₀ (by positivity) hζlo hs₀lo hs₀hi
    hy₃ hΔ i (hvR i)
  refine ⟨?_, hw i⟩
  have e : blockTrace (cmpInv H (cmpSepShift b mb ub)) i = mb i - r i := by
    rw [(happ i).1]; ring
  rw [e, Complex.sub_im] at htop
  have := (le_abs_self (r i).im).trans ((Complex.abs_im_le_norm _).trans
    ((norm_le_pi_norm r i).trans hr))
  have e2 : b * (w₁ / 2) * vR / (2 * (1 + (K + ζ₀⁻¹ + 2) ^ 2 / ζlo ^ 2)) =
      b * (ζ₀ / (3 + K) ^ 2 / 2) * vR / (2 * (1 + (K + ζ₀⁻¹ + 2) ^ 2 / ζlo ^ 2)) := by rw [hw₁]
  linarith

/-- **Lower bounds for approximate common-port means.** Same hypotheses as `cmp_sep_lower`
with the common-port equations: `-Im ū₀ ≥ w₁ - η` and the same top lower bound. -/
theorem cmp_com_lower {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hH : H.IsHermitian) {b ζ₀ K η ζlo vR : ℝ} {z s₀ : ℂ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3) (hK : 0 ≤ K)
    (hηw : η ≤ ζ₀ / (3 + K) ^ 2 / 2) (hη1 : η ≤ 1)
    (hζlo : 0 < ζlo) (hs₀lo : ζlo ≤ -s₀.im) (hs₀hi : -s₀.im ≤ 1) (hs₀n : ‖s₀‖ ≤ 1)
    (hvR : ∀ i, vR ≤ -(blockTrace (cmpInv H (fun _ => s₀)) i).im)
    (mb r : Fin 2 → ℂ) (ub r' : ℂ)
    (happ : (∀ i, mb i = blockTrace (cmpInv H (cmpComShift b mb ub)) i + r i) ∧
      ub = (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ + r')
    (hr : ‖r‖ ≤ η) (hr' : ‖r'‖ ≤ η) (hpos : ∀ i, 0 ≤ -(mb i).im) (hKm : ∀ i, ‖mb i‖ ≤ K)
    (i : Fin 2) :
    b * (ζ₀ / (3 + K) ^ 2 / 2) * vR / (2 * (1 + (K + ζ₀⁻¹ + 2) ^ 2 / ζlo ^ 2)) - η ≤
        -(mb i).im ∧ ζ₀ / (3 + K) ^ 2 - η ≤ -ub.im := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hq : ζ₀ ≤ (z - (b : ℂ) * (mb 0 + mb 1)).im ∧ ‖z - (b : ℂ) * (mb 0 + mb 1)‖ ≤ 3 + K := by
    constructor
    · have : (z - (b : ℂ) * (mb 0 + mb 1)).im = z.im + b * ((-(mb 0).im) + (-(mb 1).im)) := by
        simp only [Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      rw [this]; have := mul_nonneg hb0.le (add_nonneg (hpos 0) (hpos 1)); linarith
    · have h1 := norm_sub_le z ((b : ℂ) * (mb 0 + mb 1))
      rw [cmp_norm_real_mul hb0.le] at h1
      have h2 := (norm_add_le (mb 0) (mb 1)).trans (add_le_add (hKm 0) (hKm 1))
      have := mul_le_mul (show b ≤ 1 / 2 by linarith) h2 (norm_nonneg _) (by norm_num)
      linarith
  have hport := cmp_port_lower hζ₀ hq.1 hK hq.2
  have hw : ζ₀ / (3 + K) ^ 2 - η ≤ -ub.im := by
    rw [happ.2, Complex.add_im]
    have := (le_abs_self r'.im).trans ((Complex.abs_im_le_norm _).trans hr')
    linarith [hport.1]
  set w₁ := ζ₀ / (3 + K) ^ 2 with hw₁
  have hw₁0 : 0 < w₁ := by positivity
  have hy₃ : ∀ j, b * (w₁ / 2) ≤ -(cmpComShift b mb ub j).im := fun j => by
    simp only [cmpComShift]
    rw [cmp_im_comb]
    have h1 := mul_nonneg hc0 (hpos j)
    have h2 := mul_le_mul_of_nonneg_left (show w₁ / 2 ≤ -ub.im by linarith [hw]) hb0.le
    linarith
  have hub : ‖ub‖ ≤ ζ₀⁻¹ + 1 := by
    rw [happ.2]
    have := norm_add_le ((z - (b : ℂ) * (mb 0 + mb 1))⁻¹) r'
    linarith [hport.2]
  have hΔ : ∀ j, ‖cmpComShift b mb ub j - s₀‖ ≤ K + ζ₀⁻¹ + 2 := fun j => by
    simp only [cmpComShift]
    have h1 := norm_sub_le (((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub) s₀
    have h2 := norm_add_le (((1 - 2 * b : ℝ) : ℂ) * mb j) ((b : ℂ) * ub)
    rw [cmp_norm_real_mul hc0, cmp_norm_real_mul hb0.le] at h2
    have h3 := mul_le_mul (show 1 - 2 * b ≤ 1 by linarith) (hKm j) (norm_nonneg _) zero_le_one
    have h4 := mul_le_mul (show b ≤ 1 by linarith) hub (norm_nonneg _) zero_le_one
    linarith
  have htop := cmp_top_lower H hH (cmpComShift b mb ub) s₀ (by positivity) hζlo hs₀lo hs₀hi
    hy₃ hΔ i (hvR i)
  refine ⟨?_, hw⟩
  have e : blockTrace (cmpInv H (cmpComShift b mb ub)) i = mb i - r i := by
    rw [happ.1 i]; ring
  rw [e, Complex.sub_im] at htop
  have := (le_abs_self (r i).im).trans ((Complex.abs_im_le_norm _).trans
    ((norm_le_pi_norm r i).trans hr))
  have e2 : b * (w₁ / 2) * vR / (2 * (1 + (K + ζ₀⁻¹ + 2) ^ 2 / ζlo ^ 2)) =
      b * (ζ₀ / (3 + K) ^ 2 / 2) * vR / (2 * (1 + (K + ζ₀⁻¹ + 2) ^ 2 / ζlo ^ 2)) := by rw [hw₁]
  linarith

end Block

/-!
## The comparison statement with verifiable branch hypotheses
-/

/-- The uniform top lower bound used by `cmp_comparison_branch`. -/
def cmpTopLow (b K α₀ : ℝ) : ℝ :=
  b * ((1 - 2 * b) * α₀ / (3 + K) ^ 2 / 2) * (α₀ / 2) /
    (2 * (1 + (K + ((1 - 2 * b) * α₀)⁻¹ + 2) ^ 2 / ((1 - b) * α₀) ^ 2))

/-- **Deterministic comparison with verifiable branch hypotheses**.
`b ∈ (0, 1/2)`, `κ > 0`, `K ≥ 0` first; then `d_* > 0`, `C`, `η₀ > 0`, `C''`; uniformly in
`W ≥ 1`, Hermitian two-port `X`, `E ∈ bulkInterval κ` with `d(X) ≤ d_*`: the comparison
solutions of `cmp_comparison_deterministic` exist (both port cases, negative imaginary parts,
within `C d(X)` of `a`), and every approximate solution `(m̄, ū)` (resp. `(m̄, ū₀)`) with residuals
`‖r‖, ‖r'‖ ≤ η ≤ η₀`, `-Im m̄_i ≥ 0` and `|m̄_i| ≤ K` is within `C'' η` of it. These are the
hypotheses the layer means satisfy with `η = O(W⁻²)` (the trace–matrix lemma), `-Im 𝒢 ≥ 0`,
and the absorber bound (the Gaussian absorption lemma). -/
theorem cmp_comparison_branch : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∀ K : ℝ, 0 ≤ K →
    ∃ dstar C η₀ C'' : ℝ, 0 < dstar ∧ 0 < η₀ ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
        (∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
          (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
          (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ∀ (η : ℝ) (mb ub r r' : Fin 2 → ℂ), 0 ≤ η → η ≤ η₀ → ‖r‖ ≤ η → ‖r'‖ ≤ η →
            (∀ i, 0 ≤ -(mb i).im) → (∀ i, ‖mb i‖ ≤ K) →
            (∀ i, mb i = blockTrace (twoPortTop b E X mb ub)⁻¹ i + r i ∧
              ub i = (boundaryZ b E - (b : ℂ) * mb i)⁻¹ + r' i) →
            ∀ i, ‖mb i - m i‖ + ‖ub i - u i‖ ≤ C'' * η) ∧
        (∃ (m : Fin 2 → ℂ) (u₀ : ℂ), IsCommonPortSolution b E X m u₀ ∧
          (∀ i, (m i).im < 0) ∧ u₀.im < 0 ∧
          (∀ i, ‖m i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ‖u₀ - matchedA E‖ ≤ C * matchedDistance b E X ∧
          ∀ (η : ℝ) (mb r : Fin 2 → ℂ) (ub r' : ℂ), 0 ≤ η → η ≤ η₀ → ‖r‖ ≤ η → ‖r'‖ ≤ η →
            (∀ i, 0 ≤ -(mb i).im) → (∀ i, ‖mb i‖ ≤ K) →
            ((∀ i, mb i = blockTrace (commonPortTop b E X mb ub)⁻¹ i + r i) ∧
              ub = (commonZ b E - (b : ℂ) * (mb 0 + mb 1))⁻¹ + r') →
            (∀ i, ‖mb i - m i‖ ≤ C'' * η) ∧ ‖ub - u₀‖ ≤ C'' * η) := by
  intro b hb0 hb1 κ hκ K hK
  obtain ⟨α₀, hα₀, hα₀1, hbulk⟩ := cmp_bulk_setup hκ
  have hc : 0 < 1 - 2 * b := by linarith
  have h1b : 0 < 1 - b := by linarith
  have hζ₀0 : 0 < (1 - 2 * b) * α₀ := mul_pos hc hα₀
  have hζlo0 : 0 < (1 - b) * α₀ := mul_pos h1b hα₀
  have hyl : 0 < cmpTopLow b K α₀ := by unfold cmpTopLow; positivity
  obtain ⟨d₁, C, η₁, C'', hd₁, hη₁, hdet⟩ :=
    cmp_comparison_deterministic b hb0 hb1 κ hκ (cmpTopLow b K α₀ / 2) (by linarith)
  have hw0 : 0 < (1 - 2 * b) * α₀ / (3 + K) ^ 2 / 2 := by positivity
  refine ⟨min d₁ (α₀ / 2), C, min (min η₁ ((1 - 2 * b) * α₀ / (3 + K) ^ 2 / 2))
    (min 1 (cmpTopLow b K α₀ / 2)), C'', lt_min hd₁ (by linarith),
    lt_min (lt_min hη₁ hw0) (lt_min one_pos (by linarith)), ?_⟩
  intro W hW X hX E hE hd
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hdd : matchedDistance b E X ≤ d₁ := hd.trans (min_le_left _ _)
  have hdα : matchedDistance b E X ≤ α₀ / 2 := hd.trans (min_le_right _ _)
  obtain ⟨hsep, hcom⟩ := hdet W hW X hX E hE hdd
  have hH := cmpTopH_isHermitian E hX
  have hEabs' := hEabs.le
  -- the reference shift `s₀ = (1 - b) a`
  have hs₀im : -((1 - (b : ℂ)) * matchedA E).im = (1 - b) * (-(matchedA E).im) := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im]
    ring
  have haim1 : -(matchedA E).im ≤ 1 :=
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans ha1.le)
  have hs₀lo : (1 - b) * α₀ ≤ -((1 - (b : ℂ)) * matchedA E).im := by
    rw [hs₀im]; exact mul_le_mul_of_nonneg_left (by linarith) h1b.le
  have hs₀hi : -((1 - (b : ℂ)) * matchedA E).im ≤ 1 := by
    rw [hs₀im]
    have := mul_le_mul (show 1 - b ≤ 1 by linarith) haim1 (by linarith) zero_le_one
    linarith
  have hs₀n : ‖(1 - (b : ℂ)) * matchedA E‖ ≤ 1 := by
    rw [norm_mul, ha1, mul_one, show (1 - (b : ℂ)) = ((1 - b : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg h1b.le]
    linarith
  have hvR : ∀ i, α₀ / 2 ≤ -(blockTrace (cmpInv (cmpTopH E X)
      (fun _ => (1 - (b : ℂ)) * matchedA E)) i).im := fun i => by
    have h := cmp_le_matchedDistance b E X i
    rw [cmp_resolvent_eq hEabs' X] at h
    have := Complex.im_le_norm (blockTrace (cmpInv (cmpTopH E X)
      (fun _ => (1 - (b : ℂ)) * matchedA E)) i - matchedA E)
    rw [Complex.sub_im] at this
    linarith
  have hzs : (1 - 2 * b) * α₀ ≤ (boundaryZ b E).im := by
    rw [boundaryZ_im hEabs']
    have := mul_le_mul_of_nonneg_left haim h1b.le
    nlinarith
  have hzc : (1 - 2 * b) * α₀ ≤ (commonZ b E).im := by
    rw [commonZ_im hEabs']
    have := mul_le_mul_of_nonneg_left haim hc.le
    nlinarith
  have hzs3 := norm_boundaryZ_le hb0.le (by linarith) hEabs'
  have hzc3 := norm_commonZ_le hb0.le (by linarith) hEabs'
  have hηprops : ∀ η, η ≤ min (min η₁ ((1 - 2 * b) * α₀ / (3 + K) ^ 2 / 2))
      (min 1 (cmpTopLow b K α₀ / 2)) →
      η ≤ η₁ ∧ η ≤ (1 - 2 * b) * α₀ / (3 + K) ^ 2 / 2 ∧ η ≤ 1 ∧ η ≤ cmpTopLow b K α₀ / 2 :=
    fun η h => ⟨h.trans ((min_le_left _ _).trans (min_le_left _ _)),
      h.trans ((min_le_left _ _).trans (min_le_right _ _)),
      h.trans ((min_le_right _ _).trans (min_le_left _ _)),
      h.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  constructor
  · obtain ⟨m, u, hsol, him, hclose, hbr⟩ := hsep
    refine ⟨m, u, hsol, him, hclose, ?_⟩
    intro η mb ub r r' hη0 hη hr hr' hpos hKm happ i
    obtain ⟨hηa, hηb, hηc, hηd⟩ := hηprops η hη
    have hlow := fun j => (cmp_sep_lower (cmpTopH E X) hH hb0 hb1 hζ₀0 hzs hzs3 hK hηb hηc
      hζlo0 hs₀lo hs₀hi hs₀n hvR mb ub r r' happ hr hr' hpos hKm j).1
    refine hbr η mb ub r r' hη0 hηa hr hr' (fun j => ?_) happ i
    have := hlow j
    unfold cmpTopLow at hηd ⊢
    linarith
  · obtain ⟨m, u₀, hsol, him, hu₀im, hclose, hcloseu, hbr⟩ := hcom
    refine ⟨m, u₀, hsol, him, hu₀im, hclose, hcloseu, ?_⟩
    intro η mb r ub r' hη0 hη hr hr' hpos hKm happ
    obtain ⟨hηa, hηb, hηc, hηd⟩ := hηprops η hη
    have hlow := fun j => (cmp_com_lower (cmpTopH E X) hH hb0 hb1 hζ₀0 hzc hzc3 hK hηb hηc
      hζlo0 hs₀lo hs₀hi hs₀n hvR mb r ub r' happ hr hr' hpos hKm j).1
    refine hbr η mb r ub r' hη0 hηa hr hr' (fun j => ?_) happ
    have := hlow j
    unfold cmpTopLow at hηd ⊢
    linarith

end BlockBand.Layers
