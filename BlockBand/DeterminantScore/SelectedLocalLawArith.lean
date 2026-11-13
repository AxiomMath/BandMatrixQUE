module

public import BlockBand.DeterminantScore.SelectedLocalLawPoint

/-!
# The selected-energy local law: the deterministic conclusion and the scale arithmetic

* **`selected_point`**: at a selected energy `E` with grid neighbour `e`, from the grid local law
  (`‖Tr (K̂_e + G - iη)⁻¹ - d ā(e)‖ ≤ d^δ/η + dρ`), the transfer `trace_transfer`, the Lipschitz
  bound of `ā` and the regularity package at `K₀(E)` (`pairDyson_near`, `‖χ(K₀(E))‖ ≤ certErr(E)`):
  `‖Tr R_η - d m_E(iη)‖ ≤ 2/η + 2W (c²/ε₀² + 1)h/η² + d^δ/η + 2dL(η + χ₀) + d L_a h`.
* `scale_le`: with `η = W^{-3/5}`, `u = W^ε/η`: `1/η, W·W⁻²/η², Wη, W·W^{-1/2}, W·W⁻² ≤ u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedLocalLaw

open Matrix BlockBand.Palm
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.DeterminantScore.SelectedResolvent
open scoped ComplexConjugate

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

section Point

variable {p : Parameters} {i : ZMod p.n}

/-- **The deterministic conclusion at one selected energy**. Let
`H_R, V, G` be Hermitian, `‖C‖, ‖C*‖ ≤ c`, `ε₀ > 0`, `s = splitS p = c₀`, `PairRegularBody c₀
(√κ/2) ε₁ δ_P L`, `0 < η ≤ δ_P`, `χ₀ ≤ ε₁`; `E, e ∈ bulkInterval κ` with `|E - e| ≤ h`, `E` a
nonpole energy with at most one eigenvalue of `H_R` within `ε₀`, `certErr(E) ≤ χ₀`, and the grid
local law `‖Tr (K̂_e + G - iη)⁻¹ - d ā(e)‖ ≤ d^δ/η + d L(η + χ₀)` (`d = 2W`). Then
`‖Tr (A(E) - iη)⁻¹ - d m_E(iη)‖ ≤ 2/η + 2W (c²/ε₀² + 1)h/η² + d^δ/η + 2dL(η + χ₀) + d L_a h`,
`L_a = 1/2 + 2/√κ`. -/
theorem selected_point (x : SplitState p i × PairMatrix p i) (hH : x.1.1.IsHermitian)
    (hV : x.1.2.2.IsHermitian) (hG : x.2.IsHermitian) {ε₀ c κ h η χ₀ δ ε₁ δP L c₀ : ℝ}
    (hε₀ : 0 < ε₀) (hc : 0 ≤ c) (hκ : 0 < κ)
    (hC : ∀ v, ‖T x.1.2.1 v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖T x.1.2.1ᴴ w‖ ≤ c * ‖w‖)
    (hsp : splitS p = c₀) (hreg : PairRegularBody c₀ (Real.sqrt κ / 2) ε₁ δP L) (hL : 0 ≤ L)
    (hη : 0 < η) (hηδ : η ≤ δP) (hχ₁ : χ₀ ≤ ε₁) {E e : ℝ} (hE : E ∈ bulkInterval κ)
    (he : e ∈ bulkInterval κ) (hEe : |E - e| ≤ h)
    (hdet : (x.1.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0)
    (hnear : (nearSet ε₀ hH E).card ≤ 1) (hcert : certErr p i x.1 E ≤ χ₀)
    (hbad : ‖((hatK ε₀ x.1 e + x.2 - (((0 : ℝ) : ℂ) + Complex.I * η) •
          (1 : PairMatrix p i))⁻¹).trace - ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)‖ ≤
        ((2 * p.W : ℕ) : ℝ) ^ δ / η + ((2 * p.W : ℕ) : ℝ) * (L * (η + χ₀))) :
    ‖((schurA p i x.1 x.2 E - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i))⁻¹).trace -
        ((2 * p.W : ℝ) : ℂ) *
          pairDyson p i (schurK0 p i x.1 E) (splitS p) ((η : ℂ) * Complex.I)‖ ≤
      2 / η + 2 * p.W * ((c ^ 2 / ε₀ ^ 2 + 1) * h) / η ^ 2 + ((2 * p.W : ℕ) : ℝ) ^ δ / η +
        2 * ((2 * p.W : ℕ) : ℝ) * (L * (η + χ₀)) +
        ((2 * p.W : ℕ) : ℝ) * ((1 / 2 + 2 / Real.sqrt κ) * h) := by
  set dR : ℝ := ((2 * p.W : ℕ) : ℝ) with hdR
  have hd0 : 0 ≤ dR := Nat.cast_nonneg _
  have hW0 : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hdC : ((2 * p.W : ℝ) : ℂ) = ((2 * p.W : ℕ) : ℂ) := by push_cast; ring
  have hzeq : ((η : ℂ) * Complex.I) = ((0 : ℝ) : ℂ) + Complex.I * η := by push_cast; ring
  -- the transfer from the grid energy
  have h1 := trace_transfer x.1 x.2 hH hV hG hε₀ hc hC hC' (e := e) hdet hnear hη
  have hr : 2 * p.W * ((c ^ 2 / ε₀ ^ 2 + 1) * |E - e|) / η ^ 2 ≤
      2 * p.W * ((c ^ 2 / ε₀ ^ 2 + 1) * h) / η ^ 2 := by gcongr
  -- the reference energies
  have hμ : ‖conj (matchedA e) - conj (matchedA E)‖ ≤ (1 / 2 + 2 / Real.sqrt κ) * h := by
    rw [← map_sub, Complex.norm_conj]
    refine (norm_matchedA_sub_le hκ he hE).trans ?_
    rw [abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hEe (by positivity)
  -- the regularity package at `K₀(E)`
  have hK := WeightedTrace.schurK0_isHermitian hH hV E
  obtain ⟨hVμ, hμ1⟩ := conj_matchedA_bounds hκ hE
  have hchi : ‖certificateChi (schurK0 p i x.1 E) c₀ 0 (conj (matchedA E))‖ ≤ χ₀ := by
    rw [← hsp]; exact (norm_chi_le_certErr x.1 hH hV E).trans hcert
  have hδ0 : 0 ≤ δP := hη.le.trans hηδ
  have hzim : 0 ≤ ((η : ℂ) * Complex.I).im := by simp [hη.le]
  have hznorm : ‖(η : ℂ) * Complex.I‖ = η := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  obtain ⟨-, -, hnearE⟩ := pairDyson_near hreg hL hδ0 hK hVμ hμ1 hchi hχ₁ hzim
    (by rw [hznorm]; exact hηδ)
  rw [hznorm] at hnearE
  rw [hsp, hdC]
  set m := pairDyson p i (schurK0 p i x.1 E) c₀ ((η : ℂ) * Complex.I)
  set z : ℂ := ((0 : ℝ) : ℂ) + Complex.I * η with hz
  rw [hzeq]
  set R := ((schurA p i x.1 x.2 E - z • (1 : PairMatrix p i))⁻¹).trace
  set Rh := ((hatK ε₀ x.1 e + x.2 - z • (1 : PairMatrix p i))⁻¹).trace
  have heq : R - ((2 * p.W : ℕ) : ℂ) * m = (R - Rh) + (Rh - ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)) +
      ((2 * p.W : ℕ) : ℂ) * (conj (matchedA e) - conj (matchedA E)) +
      ((2 * p.W : ℕ) : ℂ) * (conj (matchedA E) - m) := by ring
  rw [heq]
  have n3 : ‖((2 * p.W : ℕ) : ℂ) * (conj (matchedA e) - conj (matchedA E))‖ ≤
      dR * ((1 / 2 + 2 / Real.sqrt κ) * h) := by
    rw [norm_mul, Complex.norm_natCast]; exact mul_le_mul_of_nonneg_left hμ hd0
  have n4 : ‖((2 * p.W : ℕ) : ℂ) * (conj (matchedA E) - m)‖ ≤ dR * (L * (η + χ₀)) := by
    rw [norm_mul, Complex.norm_natCast, norm_sub_rev]; exact mul_le_mul_of_nonneg_left hnearE hd0
  have t1 := norm_add_le ((R - Rh) + (Rh - ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)) +
      ((2 * p.W : ℕ) : ℂ) * (conj (matchedA e) - conj (matchedA E)))
    (((2 * p.W : ℕ) : ℂ) * (conj (matchedA E) - m))
  have t2 := norm_add_le ((R - Rh) + (Rh - ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)))
      (((2 * p.W : ℕ) : ℂ) * (conj (matchedA e) - conj (matchedA E)))
  have t3 := norm_add_le (R - Rh) (Rh - ((2 * p.W : ℕ) : ℂ) * conj (matchedA e))
  linarith

end Point

section Scale

/-- **Scale facts at `η = W^{-3/5}`**: with `u = W^ε/η` (`W ≥ 1`, `ε > 0`), each of `1/η`,
`W·W⁻²/η²`, `Wη`, `W·W^{-1/2}`, `W·W⁻²` is at most `u`. -/
theorem scale_le {W ε : ℝ} (hW : 1 ≤ W) (hε : 0 < ε) :
    1 / W ^ (-(3 / 5 : ℝ)) ≤ W ^ ε / W ^ (-(3 / 5 : ℝ)) ∧
      W * W ^ (-2 : ℝ) / (W ^ (-(3 / 5 : ℝ))) ^ 2 ≤ W ^ ε / W ^ (-(3 / 5 : ℝ)) ∧
      W * W ^ (-(3 / 5 : ℝ)) ≤ W ^ ε / W ^ (-(3 / 5 : ℝ)) ∧
      W * W ^ (-(1 / 2 : ℝ)) ≤ W ^ ε / W ^ (-(3 / 5 : ℝ)) ∧
      W * W ^ (-2 : ℝ) ≤ W ^ ε / W ^ (-(3 / 5 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hu : W ^ ε / W ^ (-(3 / 5 : ℝ)) = W ^ (ε + 3 / 5) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hW0.le, neg_neg, ← Real.rpow_add hW0]
  have hmul : ∀ a : ℝ, W * W ^ a = W ^ (1 + a) := fun a => by
    rw [Real.rpow_add hW0, Real.rpow_one]
  have hsq : (W ^ (-(3 / 5 : ℝ))) ^ 2 = W ^ (-(6 / 5 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hle : ∀ a : ℝ, a ≤ 3 / 5 → W ^ a ≤ W ^ (ε + 3 / 5) := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  rw [hu]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [one_div, ← Real.rpow_neg hW0.le, neg_neg]; exact hle _ le_rfl
  · rw [hsq, div_eq_mul_inv, ← Real.rpow_neg hW0.le, neg_neg, hmul, ← Real.rpow_add hW0]
    exact hle _ (by norm_num)
  · rw [hmul]; exact hle _ (by norm_num)
  · rw [hmul]; exact hle _ (by norm_num)
  · rw [hmul]; exact hle _ (by norm_num)

end Scale

end BlockBand.DeterminantScore.SelectedLocalLaw
