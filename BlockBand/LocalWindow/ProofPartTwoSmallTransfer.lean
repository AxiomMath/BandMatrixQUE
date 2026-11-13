module

public import BlockBand.LocalWindow.ProofPartTwoSmallPoint

/-!
# The error budget at one eigenvector, small `ρ`

The overlap error of part (ii) at one eigenvector of the Schur matrix in the small-`ρ` branch is
`O(W^{-1/2+ε})`.

## Main results

* **`smallRho_point_le`**: `smallRho_window_transfer` with the count `N_c = ⌊C_c d^β⌋`
  (`d = 2W`), an operator error `r ≤ 2W^{-2}` and an observable error `‖J - J_g‖ ≤ √(2W) K r`
  (class (b), `opNorm_spectralTest_sub_le`; `K = 0` for class (a)); if `β + ε_w ≤ ε` and
  `β + ε_w ≤ 1/2` the overlap error is at most `(2C_c + 4L + 144 + 8K) W^{-1/2+ε}`,
  `L = 2 resLip(s, v₀)/v₀`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

theorem resLip_nonneg (s v₀ : ℝ) (hs : 0 ≤ s) : 0 ≤ resLip s v₀ := by
  unfold resLip
  have := rootLip_nonneg s v₀
  have : 0 ≤ 1 + s * rootLip s v₀ := by nlinarith
  positivity

/-- **The error budget at one eigenvector**. Hypotheses of
`smallRho_window_transfer` with the count event of `gue_windowCount_le` (`≤ C_c d^β`,
`d = 2W`), an operator error `0 ≤ r ≤ 2W^{-2}` and `‖J - J_g‖ ≤ √(2W) K r` (`K ≥ 0`); with
`0 < β`, `0 < ε_w`, `β + ε_w ≤ ε`, `β + ε_w ≤ 1/2`, `C_c ≥ 0`:
`|Re(u*Ju) - windowCenter J K s λ| ≤ (2C_c + 4L + 144 + 8K) W^{-1/2+ε}`,
`L = 2 resLip(s, v₀)/v₀`. -/
theorem smallRho_point_le {K Kg G J Jg : PairMatrix p i} (hK : K.IsHermitian)
    (hKg : Kg.IsHermitian) (hG : G.IsHermitian) (sel : CEH.EigenpairSelection (2 * p.W))
    {s μ β εw ε r₀ v₀ Cc Kq r : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀)
    (hRg : PairRootRectangle Kg s μ r₀ v₀) (hRK : PairRootRectangle K s μ r₀ v₀)
    (hhr : ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) ≤ r₀) (hJgn : ‖Jg‖ ≤ 1)
    (hgood : PairWindowGood Kg hKg sel s μ β εw Jg G)
    (hcount : ∃ hG' : G.IsHermitian,
      ((Finset.univ.filter fun k => pairEigval sel (Kg + G) (hKg.add hG') k ∈
        Icc (μ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (μ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card :
          ℝ) ≤ Cc * ((2 * p.W : ℕ) : ℝ) ^ β)
    {u : PairSite p i → ℂ} (hu : l2Norm u = 1) {lam : ℝ} (hAu : (K + G) *ᵥ u = (lam : ℂ) • u)
    (hlam : |lam - μ| ≤ ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2) (hr : 0 ≤ r)
    (hKr : ‖K - Kg‖ ≤ r) (hrW : r ≤ 2 * (p.W : ℝ) ^ (-2 : ℝ))
    (hJ : ‖J - Jg‖ ≤ Real.sqrt (2 * (p.W : ℝ)) * Kq * r) (hKq : 0 ≤ Kq) (hβ : 0 < β)
    (hεw : 0 < εw) (hβε : β + εw ≤ ε) (hβh : β + εw ≤ 1 / 2) (hCc : 0 ≤ Cc) :
    |(star u ⬝ᵥ (J *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i J K s lam| ≤
      (2 * Cc + 4 * (2 * resLip s v₀ / v₀) + 144 + 8 * Kq) * (p.W : ℝ) ^ (-(1 / 2 : ℝ) + ε) := by
  obtain ⟨hG', hc⟩ := hcount
  have hcount' : (Finset.univ.filter fun k => pairEigval sel (Kg + G) (hKg.add hG) k ∈
      Icc (μ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (μ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card ≤
        ⌊Cc * ((2 * p.W : ℕ) : ℝ) ^ β⌋₊ := Nat.le_floor hc
  have hNcle : ((⌊Cc * ((2 * p.W : ℕ) : ℝ) ^ β⌋₊ : ℕ) : ℝ) ≤ Cc * ((2 * p.W : ℕ) : ℝ) ^ β :=
    Nat.floor_le (by positivity)
  have ht := smallRho_window_transfer hK hKg hG sel hs hv₀ hRg hRK hhr hJgn hgood hcount' hu hAu
    hlam hr hKr (J := J)
  have hdW : ((2 * p.W : ℕ) : ℝ) = 2 * (p.W : ℝ) := by push_cast; ring
  have hW1 : (1 : ℝ) ≤ (p.W : ℝ) := by exact_mod_cast p.W_pos
  generalize ⌊Cc * ((2 * p.W : ℕ) : ℝ) ^ β⌋₊ = Nc at ht hNcle
  generalize ((2 * p.W : ℕ) : ℝ) = d at ht hNcle hdW
  generalize (p.W : ℝ) = W at ht hrW hJ hdW hW1 ⊢
  have hL0 : 0 ≤ 2 * resLip s v₀ / v₀ := by have := resLip_nonneg s v₀ hs.le; positivity
  generalize 2 * resLip s v₀ / v₀ = L at ht hL0 ⊢
  have hW0 : (0 : ℝ) < W := by linarith
  have hd1 : W ≤ d := by rw [hdW]; linarith
  have hd0 : 0 < d := by linarith
  set w := W ^ (-(1 / 2 : ℝ) + ε) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hW0.le _
  -- the elementary powers
  have hWm2 : W ^ (-2 : ℝ) ≤ w := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hWm1 : W ^ (-1 : ℝ) ≤ w := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hW21 : W ^ (-2 : ℝ) * W = W ^ (-1 : ℝ) := by
    rw [show W ^ (-2 : ℝ) * W = W ^ (-2 : ℝ) * W ^ (1 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hW0]; norm_num
  have hWm2' : W ^ (-2 : ℝ) ≤ W ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
  have hWm2_0 : 0 ≤ W ^ (-2 : ℝ) := Real.rpow_nonneg hW0.le _
  -- (1) the count term
  have t1 : (Nc : ℝ) * (2 * (d ^ εw * d ^ (-(1 : ℝ) / 2))) ≤ 2 * Cc * w := by
    have e1 : d ^ β * (d ^ εw * d ^ (-(1 : ℝ) / 2)) = d ^ (β + εw - 1 / 2) := by
      rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]; ring_nf
    have e2 : d ^ (β + εw - 1 / 2) ≤ W ^ (β + εw - 1 / 2) :=
      Real.rpow_le_rpow_of_nonpos hW0 hd1 (by linarith)
    have e3 : W ^ (β + εw - 1 / 2) ≤ w := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have hp : 0 ≤ d ^ εw * d ^ (-(1 : ℝ) / 2) := by positivity
    calc (Nc : ℝ) * (2 * (d ^ εw * d ^ (-(1 : ℝ) / 2)))
        ≤ Cc * d ^ β * (2 * (d ^ εw * d ^ (-(1 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_right hNcle (by positivity)
      _ = 2 * Cc * (d ^ β * (d ^ εw * d ^ (-(1 : ℝ) / 2))) := by ring
      _ ≤ 2 * Cc * w := by rw [e1]; exact mul_le_mul_of_nonneg_left (e2.trans e3) (by positivity)
  -- (2) the centre variation across the window
  have t2 : L * (3 / 2 * d ^ (-1 + β)) ≤ 2 * L * w := by
    have e1 : d ^ (-1 + β) ≤ W ^ (-1 + β) := Real.rpow_le_rpow_of_nonpos hW0 hd1 (by linarith)
    have e2 : W ^ (-1 + β) ≤ w := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have : 3 / 2 * d ^ (-1 + β) ≤ 2 * w := by
      have := Real.rpow_nonneg hd0.le (-1 + β); linarith [e1.trans e2]
    calc L * (3 / 2 * d ^ (-1 + β)) ≤ L * (2 * w) := mul_le_mul_of_nonneg_left this hL0
      _ = 2 * L * w := by ring
  -- (3) the outside-window component `τ = r/(h/2) ≤ 8 W^{-1}`
  set τ := r / (d ^ (-1 + β) / 2) with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hτle : τ ≤ 8 * W ^ (-1 : ℝ) := by
    have hh : d ^ (-1 + β) = (d ^ (1 - β))⁻¹ := by
      rw [← Real.rpow_neg hd0.le]; ring_nf
    have e1 : τ = 2 * r * d ^ (1 - β) := by
      rw [hτ, hh]; field_simp
    have e2 : d ^ (1 - β) ≤ d := by
      calc d ^ (1 - β) ≤ d ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = d := Real.rpow_one d
    rw [e1]
    calc 2 * r * d ^ (1 - β) ≤ 2 * (2 * W ^ (-2 : ℝ)) * d :=
          mul_le_mul (by linarith) e2 (by positivity) (by positivity)
      _ = 8 * (W ^ (-2 : ℝ) * W) := by rw [hdW]; ring
      _ = 8 * W ^ (-1 : ℝ) := by rw [hW21]
  have hWm1_1 : W ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
  have hWm1_0 : 0 ≤ W ^ (-1 : ℝ) := Real.rpow_nonneg hW0.le _
  have t3 : 2 * τ ≤ 16 * w := by linarith
  have t4 : 2 * τ ^ 2 ≤ 128 * w := by
    have : τ ^ 2 ≤ 64 * W ^ (-1 : ℝ) := by
      have h1 : τ ^ 2 ≤ (8 * W ^ (-1 : ℝ)) ^ 2 := pow_le_pow_left₀ hτ0 hτle 2
      have h2 : W ^ (-1 : ℝ) * W ^ (-1 : ℝ) ≤ W ^ (-1 : ℝ) :=
        mul_le_of_le_one_left hWm1_0 hWm1_1
      have h3 : (8 * W ^ (-1 : ℝ)) ^ 2 = 64 * (W ^ (-1 : ℝ) * W ^ (-1 : ℝ)) := by ring
      linarith
    linarith
  -- (4) the centre move by the operator error
  have t5 : L * r ≤ 2 * L * w := by
    have : r ≤ 2 * w := by linarith
    calc L * r ≤ L * (2 * w) := mul_le_mul_of_nonneg_left this hL0
      _ = 2 * L * w := by ring
  -- (5) the observable move
  have t6 : 2 * ‖J - Jg‖ ≤ 8 * Kq * w := by
    have hs2 : Real.sqrt (2 * W) ≤ 2 * W := by
      have h1 : 2 * W ≤ (2 * W) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
      exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by linarith))
    have e1 : Real.sqrt (2 * W) * r ≤ 4 * W ^ (-1 : ℝ) := by
      calc Real.sqrt (2 * W) * r ≤ 2 * W * (2 * W ^ (-2 : ℝ)) :=
            mul_le_mul hs2 hrW hr (by positivity)
        _ = 4 * (W ^ (-2 : ℝ) * W) := by ring
        _ = 4 * W ^ (-1 : ℝ) := by rw [hW21]
    have e2 : Real.sqrt (2 * W) * Kq * r ≤ 4 * Kq * w := by
      have h1 := mul_le_mul_of_nonneg_left e1 hKq
      have h2 : Kq * (4 * W ^ (-1 : ℝ)) ≤ Kq * (4 * w) :=
        mul_le_mul_of_nonneg_left (by linarith) hKq
      calc Real.sqrt (2 * W) * Kq * r = Kq * (Real.sqrt (2 * W) * r) := by ring
        _ ≤ Kq * (4 * w) := h1.trans h2
        _ = 4 * Kq * w := by ring
    linarith
  refine ht.trans (le_trans (b := 8 * Kq * w + (2 * Cc * w + 2 * L * w + 16 * w + 128 * w) +
    2 * L * w) ?_ (le_of_eq (by ring)))
  linarith only [t1, t2, t3, t4, t5, t6]

end BlockBand.LocalWindow.ProofPartTwo
