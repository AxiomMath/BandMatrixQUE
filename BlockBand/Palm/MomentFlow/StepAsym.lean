module

public import BlockBand.Palm.MomentFlow.StepScale

/-!
# Exponent bookkeeping for the induction step

* `Nτ/ℓ ≤ 2N^{-1/150}`, `ℓ/w ≤ N^{-1/600}` (Main), `w/N = N^{-1/600}` (window energy `δ`),
  `N^ε/√(Nη) ≤ N^{-1/4}`, `N^ε/(Nη) ≤ N^{-1/2}` (averaged law), `2^Lη ≤ N^{-1/1000}`,
  `τ = N^{-1/100}` (slow error of the removal average), shell factor
  `16βη(L+1) + 2/2^L ≤ C N^{-1/1000}` (`β = 4rNV_c/(K_w w)`), long kernel `G η N/ℓ ≤ C N^{-1/1000}`,
  damping `G exp(-(rv₀/η) 2^{-(r+1)} τ) = G exp(-rv₀2^{-(r+1)}N^ε) ≤ C N^{-1/1000}`;
* **`step_asym`**: an explicit `Cfin` and `Kco` and, eventually in `N`, the conjunction used by
  `cmWin_step` (admissibility of the scales and the final bound
  `Main + G e^{…} + maxPathErr/(rv₀/η) ≤ Cfin N^{-min(κ', 1/1000)}`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Filter Topology

/-- `maxPathErr / (rv/η) = X / v`. -/
theorem maxPathErr_div (N r : ℕ) (hr : 1 ≤ r) {η β G Vb E₂ E₃ E₄ eR Main v : ℝ} (L : ℕ)
    (hη : 0 < η) (hv : 0 < v) :
    maxPathErr N r η β G Vb E₂ E₃ E₄ eR Main L / ((r : ℝ) * v / η) =
      (r3Const N r η β Vb E₂ E₄ eR Main L + Vb * E₄ + G * E₂ + r * ((N : ℝ) * η)⁻¹ +
        ((r : ℝ) + 1) * G * E₃) / v := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  unfold maxPathErr
  field_simp

/-- Algebraic collection of the error of `maxPath`. -/
theorem collect_bound {r : ℕ} {t Vb eR E₂ rK E₄ S Main GE₂ GE₃ k₁ k₂ k₃ k₄ k₅ k₆ k₇ k₈ : ℝ}
    (ht1 : t ≤ 1) (hVb : 0 ≤ Vb) (heR0 : 0 ≤ eR) (hE₂0 : 0 ≤ E₂) (hrK0 : 0 ≤ rK)
    (hE₄0 : 0 ≤ E₄) (hS0 : 0 ≤ S) (hM0 : 0 ≤ Main)
    (h₁ : eR ≤ k₁ * t) (h₂ : E₂ ≤ k₂ * t) (h₃ : rK ≤ k₃ * t) (h₄ : S ≤ k₄ * t)
    (h₅ : Main ≤ k₅ * t) (h₆ : E₄ ≤ k₆ * t) (h₇ : GE₂ ≤ k₇ * t) (h₈ : GE₃ ≤ k₈ * t)
    (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂) (hk₃ : 0 ≤ k₃) (hk₆ : 0 ≤ k₆) :
    eR + (E₂ + rK) + S * ((Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + rK)) + (Vb + E₂ + rK) * Main +
        Vb * E₄ + GE₂ + rK + ((r : ℝ) + 1) * GE₃ ≤
      (k₁ + k₂ + k₃ + k₄ * ((Vb + 1) * (1 + k₆) + k₁ + (Vb + k₂ + k₃)) + (Vb + k₂ + k₃) * k₅ +
        Vb * k₆ + k₇ + k₃ + ((r : ℝ) + 1) * k₈) * t := by
  have b₁ : eR ≤ k₁ := h₁.trans (by nlinarith)
  have b₂ : E₂ ≤ k₂ := h₂.trans (by nlinarith)
  have b₃ : rK ≤ k₃ := h₃.trans (by nlinarith)
  have b₆ : E₄ ≤ k₆ := h₆.trans (by nlinarith)
  have hY : (Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + rK) ≤
      (Vb + 1) * (1 + k₆) + k₁ + (Vb + k₂ + k₃) := by nlinarith
  have hY0 : 0 ≤ (Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + rK) := by positivity
  have e1 : S * ((Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + rK)) ≤
      k₄ * t * ((Vb + 1) * (1 + k₆) + k₁ + (Vb + k₂ + k₃)) :=
    mul_le_mul h₄ hY hY0 (hS0.trans h₄)
  have e2 : (Vb + E₂ + rK) * Main ≤ (Vb + k₂ + k₃) * (k₅ * t) :=
    mul_le_mul (by linarith) h₅ hM0 (by linarith)
  have e3 : Vb * E₄ ≤ Vb * (k₆ * t) := mul_le_mul_of_nonneg_left h₆ hVb
  have e4 : ((r : ℝ) + 1) * GE₃ ≤ ((r : ℝ) + 1) * (k₈ * t) :=
    mul_le_mul_of_nonneg_left h₈ (by positivity)
  nlinarith

/-!
## Pointwise exponent bounds (`N ≥ 1`, `0 < ε ≤ 10^{-5}`)
-/

section Pointwise

variable {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000)
include hN hε hε5

theorem asym_E2 (CA : ℝ) (hCA : 0 ≤ CA) :
    CA * (N : ℝ) ^ ε / ((N : ℝ) * cmEta N ε) ≤ CA * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [N_mul_cmEta hN, mul_div_assoc, ← Real.rpow_sub hNp]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_exp hN (by linarith)) hCA

theorem asym_rK (r : ℕ) :
    (r : ℝ) * ((N : ℝ) * cmEta N ε)⁻¹ ≤ r * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [N_mul_cmEta hN, ← Real.rpow_neg hNp.le]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_exp hN (by linarith)) (by positivity)

theorem asym_sqrt (CR : ℝ) (hCR : 0 ≤ CR) :
    CR * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * cmEta N ε) ≤ CR * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [N_mul_cmEta hN, Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le, mul_div_assoc,
    ← Real.rpow_sub hNp]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_exp hN (by linarith)) hCR

theorem asym_two_pow_eta :
    (2 : ℝ) ^ stL N * cmEta N ε ≤ (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := two_pow_stL_le hN
  have h2 : 0 < cmEta N ε := cmEta_pos hN ε
  calc (2 : ℝ) ^ stL N * cmEta N ε ≤ (N : ℝ) ^ (1 / 1000 : ℝ) * cmEta N ε :=
        mul_le_mul_of_nonneg_right h1 h2.le
    _ = (N : ℝ) ^ ((1 / 1000 : ℝ) + -(ε + 1 / 100)) := by
        rw [cmEta_eq hN, ← Real.rpow_add hNp]
    _ ≤ _ := rpow_le_rpow_exp hN (by linarith)

omit hε hε5 in
theorem asym_tau : cmTau N ≤ (N : ℝ) ^ (-(1 / 1000 : ℝ)) :=
  rpow_le_rpow_exp hN (by norm_num)

omit hε hε5 in
theorem asym_wN (K : ℝ) (hK : 0 ≤ K) : K * (cmW N / N) ≤ K * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  rw [cmW_div (by omega)]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_exp hN (by norm_num)) hK

theorem asym_inv_eta : (cmEta N ε)⁻¹ ≤ N := by
  rw [cmEta_inv hN]
  calc (N : ℝ) ^ (ε + 1 / 100) ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_exp hN (by linarith)
    _ = N := Real.rpow_one _

theorem asym_eta_le_one : cmEta N ε ≤ 1 := by
  rw [cmEta_eq hN]; exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN)
    (by linarith)

theorem asym_eta_ge : (N : ℝ) ^ (-(1 - 4 * ε)) ≤ cmEta N ε := by
  rw [cmEta_eq hN]; exact rpow_le_rpow_exp hN (by linarith)

omit hε hε5 in
theorem asym_pow_eps {C : ℝ} (hC : |C| * ε ≤ 1 / 100000) :
    (N : ℝ) ^ (|C| * ε) ≤ (N : ℝ) ^ (1 / 100000 : ℝ) := rpow_le_rpow_exp hN hC

omit hε hε5 in
theorem asym_ell_w : (cmEll N : ℝ) / cmW N ≤ (N : ℝ) ^ (-(1 / 600 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  calc (cmEll N : ℝ) / cmW N ≤ (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / cmW N :=
        div_le_div_of_nonneg_right cmEll_le (cmW_pos hN).le
    _ = (N : ℝ) ^ (-(1 / 600 : ℝ)) := by
        unfold cmW; rw [← Real.rpow_sub hNp]; norm_num

omit hε hε5 in
theorem asym_Ntau_ell :
    (N : ℝ) * cmTau N / cmEll N ≤ 2 * (N : ℝ) ^ (-(1 / 150 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := cmEll_ge hN
  have hx : 0 < (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) := Real.rpow_pos_of_pos hNp _
  have hNt : (N : ℝ) * cmTau N = (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
    unfold cmTau
    rw [show (N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) =
      (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) by rw [Real.rpow_one],
      ← Real.rpow_add hNp]; norm_num
  calc (N : ℝ) * cmTau N / cmEll N ≤ (N : ℝ) * cmTau N /
        ((N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2) :=
        div_le_div_of_nonneg_left (by rw [hNt]; positivity) (by positivity) hl
    _ = 2 * ((N : ℝ) ^ (1 - (1 / 100 : ℝ)) / (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)) := by
        rw [hNt]; field_simp
    _ = 2 * (N : ℝ) ^ (-(1 / 150 : ℝ)) := by rw [← Real.rpow_sub hNp]; norm_num

omit hε hε5 in
theorem asym_E3 (CL : ℝ) (hCL : 0 ≤ CL) :
    cmEta N ε * (CL * N / cmEll N) ≤ 2 * CL * (N : ℝ) ^ (-(ε + 1 / 150)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := cmEll_ge hN
  have hx : 0 < (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) := Real.rpow_pos_of_pos hNp _
  have hη := cmEta_pos hN ε
  have h1 : CL * N / cmEll N ≤ CL * N / ((N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hl
  have h2 : CL * N / ((N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2) =
      2 * CL * (N : ℝ) ^ ((1 / 100 : ℝ) / 3) := by
    calc CL * N / ((N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2) =
        2 * CL * ((N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)) := by
          rw [Real.rpow_one]; field_simp
      _ = _ := by rw [← Real.rpow_sub hNp]; norm_num
  calc cmEta N ε * (CL * N / cmEll N) ≤ cmEta N ε * (2 * CL * (N : ℝ) ^ ((1 / 100 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) hη.le
    _ = 2 * CL * ((N : ℝ) ^ (-(ε + 1 / 100)) * (N : ℝ) ^ ((1 / 100 : ℝ) / 3)) := by
        rw [cmEta_eq hN]; ring
    _ = 2 * CL * (N : ℝ) ^ (-(ε + 1 / 150)) := by
        rw [← Real.rpow_add hNp]; congr 2; ring

end Pointwise

/-!
## The step quantities
-/

/-- Rough bound `G = |C₂| N^{|C₁|ε} + 1` of the flattened datum. -/
def stG (C₁ C₂ ε : ℝ) (N : ℕ) : ℝ := |C₂| * (N : ℝ) ^ (|C₁| * ε) + 1

/-- `Main = |C₂⁴| N^{|C₁⁴|ε} ℓ/w + |C₂³| N^{|C₁³|ε} Nτ/ℓ` (flattening commutator and long jumps). -/
def stMain (C₁₃ C₂₃ C₁₄ C₂₄ ε : ℝ) (N : ℕ) : ℝ :=
  |C₂₄| * (N : ℝ) ^ (|C₁₄| * ε) * ((cmEll N : ℝ) / cmW N) +
    |C₂₃| * (N : ℝ) ^ (|C₁₃| * ε) * ((N : ℝ) * cmTau N / cmEll N)

/-- Relative error of the removal average at all heights `η ≤ h ≤ 2^Lη` and times `u ≥ c₀ - τ`. -/
def stEA (CR slow v₀ Kδ ε : ℝ) (N : ℕ) : ℝ :=
  CR * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * cmEta N ε) +
    v₀⁻¹ * slow * (Kδ * (cmW N / N) + 2 ^ stL N * cmEta N ε + cmTau N)

/-- Averaged-law error at heights `≥ η`. -/
def stE2 (CA ε : ℝ) (N : ℕ) : ℝ := CA * (N : ℝ) ^ ε / ((N : ℝ) * cmEta N ε)

/-- Long kernel bound `η · C N/ℓ`. -/
def stE3 (CL ε : ℝ) (N : ℕ) : ℝ := cmEta N ε * (CL * N / cmEll N)

/-- `CM(r-1)` constant error. -/
def stE4 (C' κ' : ℝ) (N : ℕ) : ℝ := |C'| * (N : ℝ) ^ (-κ')

/-- Upper bound `K_B N^p` for `max(1, N‖q‖²)`. -/
def stB1 (KB p : ℝ) (N : ℕ) : ℝ := KB * (N : ℝ) ^ p

/-- Additive error of the removal average with `D_R ≥ (r+1)(p+1) + 1`. -/
def stEB (r : ℕ) (KB p v₀ ε : ℝ) (N : ℕ) : ℝ :=
  stB1 KB p N ^ r * (stB1 KB p N / cmEta N ε + v₀⁻¹) *
    (N : ℝ) ^ (-(((r : ℝ) + 1) * (p + 1) + 1))

/-- Ramp Lipschitz constant `β = 4rNV_c/(K_w w)`. -/
def stBeta (r : ℕ) (Vc Kw : ℝ) (N : ℕ) : ℝ := 4 * r * N * Vc / (Kw * cmW N)

section Terms

variable {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000)
include hN hε hε5

theorem asym_G {C₁ C₂ : ℝ} (h1 : |C₁| * ε ≤ 1 / 100000) :
    stG C₁ C₂ ε N ≤ (|C₂| + 1) * (N : ℝ) ^ (1 / 100000 : ℝ) := by
  unfold stG
  have h := asym_pow_eps hN h1
  have h0 : 1 ≤ (N : ℝ) ^ (1 / 100000 : ℝ) := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  nlinarith [abs_nonneg C₂]

theorem asym_G_le_N {C₁ C₂ : ℝ} (h1 : |C₁| * ε ≤ 1 / 100000) :
    stG C₁ C₂ ε N ≤ (|C₂| + 1) * N := by
  refine (asym_G hN hε hε5 h1).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  calc (N : ℝ) ^ (1 / 100000 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_exp hN (by norm_num)
    _ = N := Real.rpow_one _

theorem asym_EA {CR slow v₀ Kδ : ℝ} (hCR : 0 ≤ CR) (hs : 0 ≤ slow) (hv : 0 < v₀) (hK : 0 ≤ Kδ) :
    stEA CR slow v₀ Kδ ε N ≤ (CR + v₀⁻¹ * slow * (Kδ + 2)) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  unfold stEA
  have h1 := asym_sqrt hN hε hε5 CR hCR
  have h2 : (N : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    rpow_le_rpow_exp hN (by norm_num)
  have h3 := asym_wN hN Kδ hK
  have h4 := asym_two_pow_eta hN hε hε5
  have h5 := asym_tau (N := N) hN
  have hvs : 0 ≤ v₀⁻¹ * slow := by positivity
  have h6 : v₀⁻¹ * slow * (Kδ * (cmW N / N) + 2 ^ stL N * cmEta N ε + cmTau N) ≤
      v₀⁻¹ * slow * ((Kδ + 2) * (N : ℝ) ^ (-(1 / 1000 : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) hvs
  nlinarith

theorem asym_EB {r : ℕ} {KB p v₀ : ℝ} (hKB : 1 ≤ KB) (hp : 0 ≤ p) (hv : 0 < v₀) :
    stEB r KB p v₀ ε N ≤ KB ^ r * (KB + v₀⁻¹) * (N : ℝ) ^ (-(1 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold stEB stB1
  have hη := cmEta_pos hN ε
  have hηi := asym_inv_eta hN hε hε5
  have hNp1 : (N : ℝ) ^ p * N = (N : ℝ) ^ (p + 1) := by
    rw [Real.rpow_add hNp, Real.rpow_one]
  have h1 : KB * (N : ℝ) ^ p / cmEta N ε + v₀⁻¹ ≤ (KB + v₀⁻¹) * (N : ℝ) ^ (p + 1) := by
    have a1 : KB * (N : ℝ) ^ p / cmEta N ε ≤ KB * (N : ℝ) ^ (p + 1) := by
      rw [div_eq_mul_inv, ← hNp1]
      have : 0 ≤ KB * (N : ℝ) ^ p := by positivity
      nlinarith
    have a2 : v₀⁻¹ ≤ v₀⁻¹ * (N : ℝ) ^ (p + 1) :=
      le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hN1 (by linarith))
    nlinarith
  have h2 : (KB * (N : ℝ) ^ p) ^ r ≤ KB ^ r * (N : ℝ) ^ ((p + 1) * r) := by
    rw [mul_pow, Real.rpow_mul_natCast hNp.le]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (rpow_le_rpow_exp hN (by linarith)) r) (by positivity)
  have h3 : (KB * (N : ℝ) ^ p) ^ r * (KB * (N : ℝ) ^ p / cmEta N ε + v₀⁻¹) ≤
      KB ^ r * (KB + v₀⁻¹) * (N : ℝ) ^ ((p + 1) * r + (p + 1)) := by
    rw [Real.rpow_add hNp]
    calc (KB * (N : ℝ) ^ p) ^ r * (KB * (N : ℝ) ^ p / cmEta N ε + v₀⁻¹)
        ≤ (KB ^ r * (N : ℝ) ^ ((p + 1) * r)) * ((KB + v₀⁻¹) * (N : ℝ) ^ (p + 1)) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = _ := by ring
  calc (KB * (N : ℝ) ^ p) ^ r * (KB * (N : ℝ) ^ p / cmEta N ε + v₀⁻¹) *
        (N : ℝ) ^ (-(((r : ℝ) + 1) * (p + 1) + 1))
      ≤ KB ^ r * (KB + v₀⁻¹) * (N : ℝ) ^ ((p + 1) * r + (p + 1)) *
        (N : ℝ) ^ (-(((r : ℝ) + 1) * (p + 1) + 1)) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = KB ^ r * (KB + v₀⁻¹) * ((N : ℝ) ^ ((p + 1) * r + (p + 1)) *
        (N : ℝ) ^ (-(((r : ℝ) + 1) * (p + 1) + 1))) := by ring
    _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring

theorem asym_shell {r : ℕ} {Vc Kw : ℝ} (hVc : 0 ≤ Vc) (hKw : 0 < Kw) :
    shellFac (stBeta r Vc Kw N) (cmEta N ε) (stL N) ≤
      (64 * r * Vc / Kw + 4) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hη := cmEta_pos hN ε
  have hw := cmW_pos hN
  unfold shellFac stBeta
  have h2L := two_pow_stL_le hN
  have h2L' := le_two_pow_stL hN
  have hL1 := stL_succ_le N
  have hx : 0 < (N : ℝ) ^ (1 / 1000 : ℝ) := Real.rpow_pos_of_pos hNp _
  -- first part
  have hβ : 4 * r * N * Vc / (Kw * cmW N) = 4 * r * Vc / Kw * (N : ℝ) ^ (1 / 600 : ℝ) := by
    rw [← N_div_cmW hN]; field_simp
  have e1 : 16 * (4 * r * N * Vc / (Kw * cmW N)) * cmEta N ε * ((stL N : ℝ) + 1) ≤
      64 * r * Vc / Kw * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [hβ]
    have hc : 0 ≤ 4 * r * Vc / Kw := by positivity
    have a1 : (N : ℝ) ^ (1 / 600 : ℝ) * cmEta N ε * ((stL N : ℝ) + 1) ≤
        (N : ℝ) ^ (1 / 600 : ℝ) * cmEta N ε * (N : ℝ) ^ (1 / 1000 : ℝ) :=
      mul_le_mul_of_nonneg_left (hL1.trans h2L) (by positivity)
    have a2 : (N : ℝ) ^ (1 / 600 : ℝ) * cmEta N ε * (N : ℝ) ^ (1 / 1000 : ℝ) ≤
        (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
      rw [cmEta_eq hN, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
      exact rpow_le_rpow_exp hN (by linarith)
    calc 16 * (4 * r * Vc / Kw * (N : ℝ) ^ (1 / 600 : ℝ)) * cmEta N ε * ((stL N : ℝ) + 1)
        = 16 * (4 * r * Vc / Kw) * ((N : ℝ) ^ (1 / 600 : ℝ) * cmEta N ε * ((stL N : ℝ) + 1)) := by
          ring
      _ ≤ 16 * (4 * r * Vc / Kw) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) :=
          mul_le_mul_of_nonneg_left (a1.trans a2) (by positivity)
      _ = _ := by ring
  have e2 : 2 * cmEta N ε / (2 ^ stL N * cmEta N ε) ≤ 4 * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    have h2p : (0 : ℝ) < 2 ^ stL N := by positivity
    rw [show 2 * cmEta N ε / (2 ^ stL N * cmEta N ε) = 2 / 2 ^ stL N by field_simp]
    calc (2 : ℝ) / 2 ^ stL N = 4 / (2 * 2 ^ stL N) := by field_simp; norm_num
      _ ≤ 4 / (N : ℝ) ^ (1 / 1000 : ℝ) := div_le_div_of_nonneg_left (by norm_num) hx h2L'
      _ = 4 * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by rw [Real.rpow_neg hNp.le, div_eq_mul_inv]
  nlinarith

omit hε hε5 in
theorem asym_Main {C₁₃ C₂₃ C₁₄ C₂₄ : ℝ} (h13 : |C₁₃| * ε ≤ 1 / 100000)
    (h14 : |C₁₄| * ε ≤ 1 / 100000) :
    stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N ≤ (|C₂₄| + 2 * |C₂₃|) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold stMain
  have a1 := asym_pow_eps hN h14
  have a2 := asym_pow_eps hN h13
  have b1 := asym_ell_w (N := N) hN
  have b2 := asym_Ntau_ell (N := N) hN
  have c1 : (N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(1 / 600 : ℝ)) ≤
      (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hNp]; exact rpow_le_rpow_exp hN (by norm_num)
  have c2 : (N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(1 / 150 : ℝ)) ≤
      (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hNp]; exact rpow_le_rpow_exp hN (by norm_num)
  have d1 : (N : ℝ) ^ (|C₁₄| * ε) * ((cmEll N : ℝ) / cmW N) ≤ (N : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    (mul_le_mul a1 b1 (by have := cmW_pos hN; positivity) (by positivity)).trans c1
  have d2 : (N : ℝ) ^ (|C₁₃| * ε) * ((N : ℝ) * cmTau N / cmEll N) ≤
      2 * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    have := mul_le_mul a2 b2 (by have := cmEll_pos hN; unfold cmTau; positivity) (by positivity)
    nlinarith
  have := mul_le_mul_of_nonneg_left d1 (abs_nonneg C₂₄)
  have := mul_le_mul_of_nonneg_left d2 (abs_nonneg C₂₃)
  nlinarith

theorem asym_GE2 {C₁ C₂ CA : ℝ} (h1 : |C₁| * ε ≤ 1 / 100000) (hCA : 0 ≤ CA) :
    stG C₁ C₂ ε N * stE2 CA ε N ≤ (|C₂| + 1) * CA * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have a := asym_G (C₂ := C₂) hN hε hε5 h1
  have b := asym_E2 hN hε hε5 CA hCA
  have hE : 0 ≤ stE2 CA ε N := by
    unfold stE2; have := cmEta_pos hN ε; positivity
  have c : (N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hNp]; exact rpow_le_rpow_exp hN (by norm_num)
  calc stG C₁ C₂ ε N * stE2 CA ε N ≤ ((|C₂| + 1) * (N : ℝ) ^ (1 / 100000 : ℝ)) *
        (CA * (N : ℝ) ^ (-(1 / 2 : ℝ))) := mul_le_mul a b hE (by positivity)
    _ = (|C₂| + 1) * CA * ((N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left c (by positivity)

theorem asym_GE3 {C₁ C₂ CL : ℝ} (h1 : |C₁| * ε ≤ 1 / 100000) (hCL : 0 ≤ CL) :
    stG C₁ C₂ ε N * stE3 CL ε N ≤ 2 * CL * (|C₂| + 1) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have a := asym_G (C₂ := C₂) hN hε hε5 h1
  have b := asym_E3 (ε := ε) hN CL hCL
  have hE : 0 ≤ stE3 CL ε N := by
    unfold stE3; have := cmEta_pos hN ε; have := cmEll_pos hN; positivity
  have c : (N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(ε + 1 / 150)) ≤
      (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hNp]; exact rpow_le_rpow_exp hN (by linarith)
  calc stG C₁ C₂ ε N * stE3 CL ε N ≤ ((|C₂| + 1) * (N : ℝ) ^ (1 / 100000 : ℝ)) *
        (2 * CL * (N : ℝ) ^ (-(ε + 1 / 150))) := mul_le_mul a b hE (by positivity)
    _ = 2 * CL * (|C₂| + 1) * ((N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(ε + 1 / 150))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left c (by positivity)

theorem asym_Gexp {C₁ C₂ : ℝ} (h1 : |C₁| * ε ≤ 1 / 100000) {X : ℝ}
    (hX : X ≤ (N : ℝ) ^ (-(1 : ℝ))) (hX0 : 0 ≤ X) :
    stG C₁ C₂ ε N * X ≤ (|C₂| + 1) * (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have a := asym_G (C₂ := C₂) hN hε hε5 h1
  have c : (N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(1 : ℝ)) ≤
      (N : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hNp]; exact rpow_le_rpow_exp hN (by norm_num)
  calc stG C₁ C₂ ε N * X ≤ ((|C₂| + 1) * (N : ℝ) ^ (1 / 100000 : ℝ)) * (N : ℝ) ^ (-(1 : ℝ)) :=
        mul_le_mul a hX hX0 (by positivity)
    _ = (|C₂| + 1) * ((N : ℝ) ^ (1 / 100000 : ℝ) * (N : ℝ) ^ (-(1 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left c (by positivity)

end Terms

theorem poly_le_pow {N : ℕ} (hN : 1 ≤ N) (r : ℕ) {Kco C : ℝ} (hK : 0 ≤ Kco)
    (hbig : (1 + Kco) * (5 + |C|) + 7 ≤ N) :
    (1 + Kco * N) * (1 + (N : ℝ) ^ (r + 1) * (3 + (|C| + 1) * N)) + 7 ≤ (N : ℝ) ^ (r + 4) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set n : ℝ := (N : ℝ) with hn'
  have p1 : (1 : ℝ) ≤ n ^ (r + 1) := one_le_pow₀ hn
  have e2 : n ^ (r + 2) = n ^ (r + 1) * n := pow_succ _ _
  have e3 : n ^ (r + 3) = n ^ (r + 2) * n := pow_succ _ _
  have e4 : n ^ (r + 4) = n ^ (r + 3) * n := pow_succ _ _
  have p2 : n ^ (r + 1) ≤ n ^ (r + 2) := by rw [e2]; nlinarith
  have p3 : n ^ (r + 2) ≤ n ^ (r + 3) := by rw [e3]; nlinarith
  have a1 : 1 + Kco * n ≤ (1 + Kco) * n := by nlinarith
  have a2 : 1 + n ^ (r + 1) * (3 + (|C| + 1) * n) ≤ (5 + |C|) * n ^ (r + 2) := by
    have := abs_nonneg C
    nlinarith
  have a3 : (1 + Kco * n) * (1 + n ^ (r + 1) * (3 + (|C| + 1) * n)) ≤
      (1 + Kco) * (5 + |C|) * n ^ (r + 3) := by
    have h0 : 0 ≤ 1 + n ^ (r + 1) * (3 + (|C| + 1) * n) := by positivity
    calc (1 + Kco * n) * (1 + n ^ (r + 1) * (3 + (|C| + 1) * n))
        ≤ ((1 + Kco) * n) * ((5 + |C|) * n ^ (r + 2)) := mul_le_mul a1 a2 h0 (by positivity)
      _ = (1 + Kco) * (5 + |C|) * n ^ (r + 3) := by rw [e3]; ring
  have p4 : 7 ≤ 7 * n ^ (r + 3) := by nlinarith
  rw [e4]
  nlinarith

/-- `k₁` of the collected error. -/
def stK1 (r : ℕ) (v₀ slow Kδ CR C' KB : ℝ) : ℝ :=
  (CR + v₀⁻¹ * slow * (Kδ + 2)) * (1 + |C'|) + KB ^ r * (KB + v₀⁻¹)

/-- The collected constant `K_x`. -/
def stKx (r : ℕ) (v₀ slow Kw Kδ C₂₃ C₂₄ CR CA CL C' KB : ℝ) : ℝ :=
  stK1 r v₀ slow Kδ CR C' KB + CA + r +
    (64 * r * (v₀⁻¹ + 1) / Kw + 4) * ((max v₀ v₀⁻¹ + 1) * (1 + |C'|) +
      stK1 r v₀ slow Kδ CR C' KB + (max v₀ v₀⁻¹ + CA + r)) +
    (max v₀ v₀⁻¹ + CA + r) * (|C₂₄| + 2 * |C₂₃|) + max v₀ v₀⁻¹ * |C'| + (|C₂₄| + 1) * CA + r +
    ((r : ℝ) + 1) * (2 * CL * (|C₂₄| + 1))

/-- The final constant of the step. -/
def stCfin (r : ℕ) (v₀ slow Kw Kδ C₂₃ C₂₄ CR CA CL C' KB : ℝ) : ℝ :=
  (|C₂₄| + 2 * |C₂₃|) + (|C₂₄| + 1) + stKx r v₀ slow Kw Kδ C₂₃ C₂₄ CR CA CL C' KB / v₀

/-- The coefficient bound constant. -/
def stKco (r : ℕ) (v₀ : ℝ) : ℝ := r * (1 + max v₀ v₀⁻¹ + v₀) * (2 * max v₀ v₀⁻¹ + 5)

theorem stK1_nonneg {r : ℕ} {v₀ slow Kδ CR C' KB : ℝ} (hv₀ : 0 < v₀) (hs : 0 ≤ slow)
    (hKδ : 0 ≤ Kδ) (hCR : 0 ≤ CR) (hKB : 1 ≤ KB) : 0 ≤ stK1 r v₀ slow Kδ CR C' KB := by
  unfold stK1; have : (0 : ℝ) ≤ KB := by linarith
  positivity

theorem stKco_nonneg (r : ℕ) {v₀ : ℝ} (hv₀ : 0 < v₀) : 0 ≤ stKco r v₀ := by
  unfold stKco; have : 0 ≤ max v₀ v₀⁻¹ := le_max_of_le_left hv₀.le
  positivity

/-- The final bound at one `N` (`maxPath` constant part). -/
theorem step_main_bound {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r)
    {v₀ slow Kw Kδ C₁₃ C₂₃ C₁₄ C₂₄ CR CA CL κ' C' KB p ε : ℝ}
    (hv₀ : 0 < v₀) (hslow : 0 ≤ slow) (hKw : 0 < Kw) (hKδ : 0 ≤ Kδ) (hCR : 0 ≤ CR)
    (hCA : 0 ≤ CA) (hCL : 0 ≤ CL) (hκ' : 0 < κ') (hKB : 1 ≤ KB) (hp : 0 ≤ p) (hε : 0 < ε)
    (hε5 : ε ≤ 1 / 100000) (h13 : |C₁₃| * ε ≤ 1 / 100000) (h14 : |C₁₄| * ε ≤ 1 / 100000)
    (e8 : Real.exp (-((r * v₀ * (1 / 2 : ℝ) ^ (r + 1)) * (N : ℝ) ^ ε)) ≤ (N : ℝ) ^ (-(1 : ℝ))) :
    stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N + stG C₁₄ C₂₄ ε N *
          Real.exp (-((r : ℝ) * v₀ / cmEta N ε) * ((1 / 2 : ℝ) ^ (r + 1) * cmTau N)) +
        maxPathErr N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) (stG C₁₄ C₂₄ ε N) (max v₀ v₀⁻¹)
          (stE2 CA ε N) (stE3 CL ε N) (stE4 C' κ' N)
          (stEA CR slow v₀ Kδ ε N * (1 + stE4 C' κ' N) + stEB r KB p v₀ ε N)
          (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N) (stL N) / ((r : ℝ) * v₀ / cmEta N ε) ≤
        stCfin r v₀ slow Kw Kδ C₂₃ C₂₄ CR CA CL C' KB * (N : ℝ) ^ (-(min κ' (1 / 1000))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hη := cmEta_pos hN ε
  have hVb0 : 0 ≤ max v₀ v₀⁻¹ := le_max_of_le_left hv₀.le
  have hVc0 : 0 < v₀⁻¹ + 1 := by positivity
  have hKA : 0 ≤ CR + v₀⁻¹ * slow * (Kδ + 2) := by positivity
  have hKEB : 0 ≤ KB ^ r * (KB + v₀⁻¹) := by
    have : (0 : ℝ) ≤ KB := by linarith
    positivity
  have ht1 : (N : ℝ) ^ (-(min κ' (1 / 1000))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN)
      (by simp only [Left.neg_nonpos_iff, le_min_iff]; constructor <;> linarith)
  have hq : (N : ℝ) ^ (-(1 / 1000 : ℝ)) ≤ (N : ℝ) ^ (-(min κ' (1 / 1000))) :=
    rpow_le_rpow_exp hN (by simp only [neg_le_neg_iff]; exact min_le_right _ _)
  have hq' : (N : ℝ) ^ (-κ') ≤ (N : ℝ) ^ (-(min κ' (1 / 1000))) :=
    rpow_le_rpow_exp hN (by simp only [neg_le_neg_iff]; exact min_le_left _ _)
  have hq2 : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    rpow_le_rpow_exp hN (by norm_num)
  have hq1 : (N : ℝ) ^ (-(1 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 1000 : ℝ)) :=
    rpow_le_rpow_exp hN (by norm_num)
  have bEA := asym_EA hN hε hε5 hCR hslow hv₀ hKδ (CR := CR) (slow := slow) (v₀ := v₀) (Kδ := Kδ)
  have hE40 : 0 ≤ stE4 C' κ' N := by unfold stE4; positivity
  have hE4 : stE4 C' κ' N ≤ |C'| * (N : ℝ) ^ (-(min κ' (1 / 1000))) :=
    mul_le_mul_of_nonneg_left hq' (abs_nonneg _)
  have hE4' : stE4 C' κ' N ≤ |C'| := hE4.trans (by nlinarith [abs_nonneg C'])
  have hEB := asym_EB (r := r) hN hε hε5 hKB hp hv₀ (p := p)
  have hEB0 : 0 ≤ stEB r KB p v₀ ε N := by
    unfold stEB stB1; have : (0 : ℝ) ≤ KB := by linarith
    positivity
  have hEA0 : 0 ≤ stEA CR slow v₀ Kδ ε N := by
    unfold stEA; have := cmW_pos hN; unfold cmTau; positivity
  have h₁ : stEA CR slow v₀ Kδ ε N * (1 + stE4 C' κ' N) + stEB r KB p v₀ ε N ≤
      stK1 r v₀ slow Kδ CR C' KB * (N : ℝ) ^ (-(min κ' (1 / 1000))) := by
    have a : stEA CR slow v₀ Kδ ε N * (1 + stE4 C' κ' N) ≤
        (CR + v₀⁻¹ * slow * (Kδ + 2)) * (N : ℝ) ^ (-(min κ' (1 / 1000))) * (1 + |C'|) :=
      mul_le_mul (bEA.trans (mul_le_mul_of_nonneg_left hq hKA)) (by linarith) (by positivity)
        (by positivity)
    have b : stEB r KB p v₀ ε N ≤ KB ^ r * (KB + v₀⁻¹) * (N : ℝ) ^ (-(min κ' (1 / 1000))) :=
      hEB.trans (mul_le_mul_of_nonneg_left (hq1.trans hq) hKEB)
    unfold stK1
    linarith
  have hE2 : stE2 CA ε N ≤ CA * (N : ℝ) ^ (-(min κ' (1 / 1000))) :=
    (asym_E2 hN hε hε5 CA hCA).trans (mul_le_mul_of_nonneg_left (hq2.trans hq) hCA)
  have hE20 : 0 ≤ stE2 CA ε N := by unfold stE2; positivity
  have hrK : (r : ℝ) * ((N : ℝ) * cmEta N ε)⁻¹ ≤ r * (N : ℝ) ^ (-(min κ' (1 / 1000))) :=
    (asym_rK hN hε hε5 r).trans (mul_le_mul_of_nonneg_left (hq2.trans hq) hr0.le)
  have hrK0 : 0 ≤ (r : ℝ) * ((N : ℝ) * cmEta N ε)⁻¹ := by positivity
  have hS := asym_shell (r := r) hN hε hε5 hVc0.le hKw
  have hS0 : 0 ≤ shellFac (stBeta r (v₀⁻¹ + 1) Kw N) (cmEta N ε) (stL N) := by
    unfold shellFac stBeta; have := cmW_pos hN; positivity
  have hM := asym_Main hN (C₂₃ := C₂₃) (C₂₄ := C₂₄) h13 h14
  have hM0 : 0 ≤ stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N := by
    unfold stMain; have := cmW_pos hN; have := cmEll_pos hN; unfold cmTau; positivity
  have hGE2 := asym_GE2 (C₂ := C₂₄) hN hε hε5 h14 hCA
  have hGE3 := asym_GE3 (C₂ := C₂₄) hN hε hε5 h14 hCL
  have hX := collect_bound (r := r) ht1 hVb0 (by positivity) hE20 hrK0 hE40 hS0 hM0 h₁ hE2 hrK
    (hS.trans (mul_le_mul_of_nonneg_left hq (by positivity)))
    (hM.trans (mul_le_mul_of_nonneg_left hq (by positivity))) hE4
    (hGE2.trans (mul_le_mul_of_nonneg_left hq (by positivity)))
    (hGE3.trans (mul_le_mul_of_nonneg_left hq (by positivity)))
    (stK1_nonneg hv₀ hslow hKδ hCR hKB) hCA hr0.le (abs_nonneg _)
  have hdiv := maxPathErr_div N r hr (stL N) hη hv₀ (β := stBeta r (v₀⁻¹ + 1) Kw N)
    (G := stG C₁₄ C₂₄ ε N) (Vb := max v₀ v₀⁻¹) (E₂ := stE2 CA ε N) (E₃ := stE3 CL ε N)
    (E₄ := stE4 C' κ' N)
    (eR := stEA CR slow v₀ Kδ ε N * (1 + stE4 C' κ' N) + stEB r KB p v₀ ε N)
    (Main := stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N)
  have hexp : Real.exp (-((r : ℝ) * v₀ / cmEta N ε) * ((1 / 2 : ℝ) ^ (r + 1) * cmTau N)) ≤
      (N : ℝ) ^ (-(1 : ℝ)) := by
    have e : -((r : ℝ) * v₀ / cmEta N ε) * ((1 / 2 : ℝ) ^ (r + 1) * cmTau N) =
        -((r * v₀ * (1 / 2 : ℝ) ^ (r + 1)) * (N : ℝ) ^ ε) := by
      rw [← cmTau_div_cmEta hN ε]; field_simp
    rw [e]; exact e8
  have hGexp := asym_Gexp (C₂ := C₂₄) hN hε hε5 h14 hexp (Real.exp_pos _).le
  rw [hdiv]
  have hX' : r3Const N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) (max v₀ v₀⁻¹) (stE2 CA ε N)
        (stE4 C' κ' N) (stEA CR slow v₀ Kδ ε N * (1 + stE4 C' κ' N) + stEB r KB p v₀ ε N)
        (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N) (stL N) + max v₀ v₀⁻¹ * stE4 C' κ' N +
        stG C₁₄ C₂₄ ε N * stE2 CA ε N + r * ((N : ℝ) * cmEta N ε)⁻¹ +
        ((r : ℝ) + 1) * stG C₁₄ C₂₄ ε N * stE3 CL ε N ≤
      stKx r v₀ slow Kw Kδ C₂₃ C₂₄ CR CA CL C' KB * (N : ℝ) ^ (-(min κ' (1 / 1000))) := by
    unfold r3Const stKx; rw [mul_assoc ((r : ℝ) + 1)]; exact hX
  have hXv := div_le_div_of_nonneg_right (c := v₀) hX' hv₀.le
  have hM' := hM.trans (mul_le_mul_of_nonneg_left hq (by positivity))
  have hG' := hGexp.trans (mul_le_mul_of_nonneg_left hq (by positivity))
  refine (add_le_add (add_le_add hM' hG') hXv).trans (le_of_eq ?_)
  unfold stCfin stKx
  field_simp

/-- The `maxPath` coefficient at one `N`. -/
theorem step_coef_bound {N r : ℕ} (hN : 1 ≤ N) {v₀ Kw CA ε : ℝ} (hv₀ : 0 < v₀) (hKw : 0 < Kw)
    (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000)
    (hS : shellFac (stBeta r (v₀⁻¹ + 1) Kw N) (cmEta N ε) (stL N) ≤ 1)
    (hE2 : stE2 CA ε N ≤ 1) (hrK : (r : ℝ) * ((N : ℝ) * cmEta N ε)⁻¹ ≤ 1) :
    maxPathCoef N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) v₀ (max v₀ v₀⁻¹) (stE2 CA ε N)
      (stL N) ≤ stKco r v₀ * N := by
  have hη := cmEta_pos hN ε
  have hVb0 : 0 ≤ max v₀ v₀⁻¹ := le_max_of_le_left hv₀.le
  have hS0 : 0 ≤ shellFac (stBeta r (v₀⁻¹ + 1) Kw N) (cmEta N ε) (stL N) := by
    unfold shellFac stBeta; have := cmW_pos hN; positivity
  have hE20 : 0 ≤ stE2 CA ε N ∨ True := Or.inr trivial
  clear hE20
  unfold maxPathCoef r3Coef
  have hc1 : 1 + shellFac (stBeta r (v₀⁻¹ + 1) Kw N) (cmEta N ε) (stL N) * (max v₀ v₀⁻¹ + 2) +
      (max v₀ v₀⁻¹ + stE2 CA ε N + r * ((N : ℝ) * cmEta N ε)⁻¹) ≤ 2 * max v₀ v₀⁻¹ + 5 := by
    have d := mul_le_mul_of_nonneg_right hS (by linarith : (0 : ℝ) ≤ max v₀ v₀⁻¹ + 2)
    linarith
  have hf : (r : ℝ) * (1 + max v₀ v₀⁻¹) / cmEta N ε + (r : ℝ) * v₀ / cmEta N ε ≤
      r * (1 + max v₀ v₀⁻¹ + v₀) * N := by
    have := asym_inv_eta hN hε hε5
    have e : (r : ℝ) * (1 + max v₀ v₀⁻¹) / cmEta N ε + (r : ℝ) * v₀ / cmEta N ε =
        r * (1 + max v₀ v₀⁻¹ + v₀) * (cmEta N ε)⁻¹ := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left this (by positivity)
  by_cases hc0 : 0 ≤ 1 + shellFac (stBeta r (v₀⁻¹ + 1) Kw N) (cmEta N ε) (stL N) *
      (max v₀ v₀⁻¹ + 2) + (max v₀ v₀⁻¹ + stE2 CA ε N + r * ((N : ℝ) * cmEta N ε)⁻¹)
  · calc ((r : ℝ) * (1 + max v₀ v₀⁻¹) / cmEta N ε + (r : ℝ) * v₀ / cmEta N ε) *
          (1 + shellFac (stBeta r (v₀⁻¹ + 1) Kw N) (cmEta N ε) (stL N) * (max v₀ v₀⁻¹ + 2) +
            (max v₀ v₀⁻¹ + stE2 CA ε N + r * ((N : ℝ) * cmEta N ε)⁻¹))
        ≤ (r * (1 + max v₀ v₀⁻¹ + v₀) * N) * (2 * max v₀ v₀⁻¹ + 5) :=
          mul_le_mul hf hc1 hc0 (by positivity)
      _ = stKco r v₀ * N := by unfold stKco; ring
  · have h0 : 0 ≤ (r : ℝ) * (1 + max v₀ v₀⁻¹) / cmEta N ε + (r : ℝ) * v₀ / cmEta N ε := by
      positivity
    have : ((r : ℝ) * (1 + max v₀ v₀⁻¹) / cmEta N ε + (r : ℝ) * v₀ / cmEta N ε) *
        (1 + shellFac (stBeta r (v₀⁻¹ + 1) Kw N) (cmEta N ε) (stL N) * (max v₀ v₀⁻¹ + 2) +
          (max v₀ v₀⁻¹ + stE2 CA ε N + r * ((N : ℝ) * cmEta N ε)⁻¹)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h0 (le_of_lt (not_le.1 hc0))
    have : 0 ≤ stKco r v₀ * N := mul_nonneg (stKco_nonneg r hv₀) (by positivity)
    linarith

/-- **Exponent bookkeeping of the step**, eventually in `N`. -/
theorem step_asym {r : ℕ} (hr : 1 ≤ r)
    {v₀ slow r₀ s₀ c₀ Kw Kδ C₁₃ C₂₃ C₁₄ C₂₄ CR CA CL κ' C' KB p ε : ℝ}
    (hv₀ : 0 < v₀) (hslow : 0 ≤ slow) (hr₀ : 0 < r₀) (hs₀ : 0 < s₀) (hc₀ : 0 < c₀) (hKw : 0 < Kw)
    (hKδ : 0 ≤ Kδ) (hCR : 0 ≤ CR) (hCA : 0 ≤ CA) (hCL : 0 ≤ CL) (hκ' : 0 < κ') (hKB : 1 ≤ KB)
    (hp : 0 ≤ p) (hε : 0 < ε) (hε5 : ε ≤ 1 / 100000) (h13 : |C₁₃| * ε ≤ 1 / 100000)
    (h14 : |C₁₄| * ε ≤ 1 / 100000) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧ cmTau N < c₀ ∧ cmTau N ≤ s₀ ∧ Kδ * (cmW N / N) ≤ r₀ / 2 ∧
      stEA CR slow v₀ Kδ ε N ≤ 1 ∧ stE2 CA ε N ≤ 1 ∧ 1 ≤ stBeta r (v₀⁻¹ + 1) Kw N ∧
      stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N + stG C₁₄ C₂₄ ε N *
          Real.exp (-((r : ℝ) * v₀ / cmEta N ε) * ((1 / 2 : ℝ) ^ (r + 1) * cmTau N)) +
        maxPathErr N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) (stG C₁₄ C₂₄ ε N) (max v₀ v₀⁻¹)
          (stE2 CA ε N) (stE3 CL ε N) (stE4 C' κ' N)
          (stEA CR slow v₀ Kδ ε N * (1 + stE4 C' κ' N) + stEB r KB p v₀ ε N)
          (stMain C₁₃ C₂₃ C₁₄ C₂₄ ε N) (stL N) / ((r : ℝ) * v₀ / cmEta N ε) ≤
        stCfin r v₀ slow Kw Kδ C₂₃ C₂₄ CR CA CL C' KB * (N : ℝ) ^ (-(min κ' (1 / 1000))) ∧
      maxPathCoef N r (cmEta N ε) (stBeta r (v₀⁻¹ + 1) Kw N) v₀ (max v₀ v₀⁻¹) (stE2 CA ε N)
          (stL N) ≤ stKco r v₀ * N ∧
      (1 + stKco r v₀ * N) * (1 + (N : ℝ) ^ (r + 1) * (3 + (|C₂₄| + 1) * N)) + 7 ≤
        (N : ℝ) ^ (r + 4) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hVc0 : 0 < v₀⁻¹ + 1 := by positivity
  have hc' : 0 < r * v₀ * (1 / 2 : ℝ) ^ (r + 1) := by positivity
  have ev1 := eventually_ge_atTop 1
  have ev2 := ev_mul_rpow_neg_le 1 (p := 1 / 100) (c := c₀ / 2) (by norm_num) (by linarith)
  have ev3 := ev_mul_rpow_neg_le 1 (p := 1 / 100) (c := s₀) (by norm_num) hs₀
  have ev4 := ev_mul_rpow_neg_le Kδ (p := 1 / 600) (c := r₀ / 2) (by norm_num) (by linarith)
  have ev5 := ev_mul_rpow_neg_le (CR + v₀⁻¹ * slow * (Kδ + 2)) (p := 1 / 1000) (c := 1)
    (by norm_num) one_pos
  have ev6 := ev_mul_rpow_neg_le CA (p := 1 / 2) (c := 1) (by norm_num) one_pos
  have ev7 := ev_le_rpow (Kw / (4 * r * (v₀⁻¹ + 1))) (p := 1 / 600) (by norm_num)
  have ev8 := eventually_exp_le_rpow hc' hε 1
  have ev9 := ev_mul_rpow_neg_le (64 * r * (v₀⁻¹ + 1) / Kw + 4) (p := 1 / 1000) (c := 1)
    (by norm_num) one_pos
  have ev10 := ev_mul_rpow_neg_le (r : ℝ) (p := 1 / 2) (c := 1) (by norm_num) one_pos
  have ev11 : ∀ᶠ N : ℕ in atTop, (1 + stKco r v₀) * (5 + |C₂₄|) + 7 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [ev1, ev2, ev3, ev4, ev5, ev6, ev7, ev8, ev9, ev10, ev11] with N hN e2 e3 e4 e5
    e6 e7 e8 e9 e10 e11
  have hτ : cmTau N = 1 * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by rw [one_mul]; rfl
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hτ]; linarith
  · rw [hτ]; exact e3
  · rw [cmW_div (by omega)]; exact e4
  · exact (asym_EA hN hε hε5 hCR hslow hv₀ hKδ).trans e5
  · exact (asym_E2 hN hε hε5 CA hCA).trans e6
  · unfold stBeta
    rw [le_div_iff₀ (mul_pos hKw (cmW_pos hN))]
    have h1 := N_div_cmW hN
    have hw := cmW_pos hN
    have : Kw / (4 * r * (v₀⁻¹ + 1)) * cmW N ≤ (N : ℝ) := by
      rw [← h1] at e7
      rw [le_div_iff₀ hw] at e7; exact e7
    calc 1 * (Kw * cmW N) = (Kw / (4 * r * (v₀⁻¹ + 1)) * cmW N) * (4 * r * (v₀⁻¹ + 1)) := by
          field_simp
      _ ≤ (N : ℝ) * (4 * r * (v₀⁻¹ + 1)) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = 4 * r * N * (v₀⁻¹ + 1) := by ring
  · exact step_main_bound hN hr hv₀ hslow hKw hKδ hCR hCA hCL hκ' hKB hp hε hε5 h13 h14 e8
  · exact step_coef_bound hN hv₀ hKw hε hε5 ((asym_shell hN hε hε5 hVc0.le hKw).trans e9)
      ((asym_E2 hN hε hε5 CA hCA).trans e6) ((asym_rK hN hε hε5 r).trans e10)
  · exact poly_le_pow hN r (stKco_nonneg r hv₀) e11

end BlockBand.Palm.MomentFlow
