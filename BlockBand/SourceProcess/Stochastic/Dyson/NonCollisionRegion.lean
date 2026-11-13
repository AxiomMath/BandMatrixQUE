module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionLyap
public import BlockBand.SourceProcess.Stochastic.Dyson.B2Stops

/-!
# McKean's argument: bounds on the Lyapunov function and the stopped region

Deterministic bounds, for spectra with all gaps `≥ δ` and spread `≤ R`:
`abs_lyap_le`, `lyap_le`, `lyap_le_of_close` (one gap `≤ ε` forces `lyap ≤ 2N² log R + log ε`),
`lyapDrift_le`. Pathwise: `ncRho G F s n m = min (gapStop n) (normStop m)` is a stopping time
of `u ↦ 𝓖_{s+u}` (`isStoppingTime_ncRho`), and up to it (`region_le_ncRho`) the spectrum of
`F + G_{s+v}` has gaps `≥ 1/n` and spread `≤ 2(k + N m)` provided the initial spectrum
has gaps `> 1/k ≥ 1/n` and eigenvalues in `[-k, k]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory Filter Topology Finset
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-!
### Deterministic bounds
-/

theorem log_le_log_of_abs_le {x R : ℝ} (hR : 1 ≤ R) (h : |x| ≤ R) :
    Real.log x ≤ Real.log R := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.log_nonneg hR]
  · rw [← Real.log_abs x]; exact Real.log_le_log (abs_pos.mpr hx) h

theorem log_le_log_of_le_abs {x δ : ℝ} (hδ : 0 < δ) (h : δ ≤ |x|) :
    Real.log δ ≤ Real.log x := by
  rw [← Real.log_abs x]; exact Real.log_le_log hδ h

theorem sum_pairs_le {f : Fin N → Fin N → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i, ∀ j ∈ univ.erase i, f i j ≤ c) :
    ∑ i, ∑ j ∈ univ.erase i, f i j ≤ (N : ℝ) ^ 2 * c := by
  calc ∑ i, ∑ j ∈ univ.erase i, f i j ≤ ∑ _i : Fin N, ∑ _j : Fin N, c :=
        sum_le_sum fun i _ => (sum_le_sum fun j hj => hf i j hj).trans
          (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => hc)
    _ = (N : ℝ) ^ 2 * c := by simp [sum_const, card_univ]; ring

theorem abs_sum_pairs_le {f : Fin N → Fin N → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i, ∀ j ∈ univ.erase i, |f i j| ≤ c) :
    |∑ i, ∑ j ∈ univ.erase i, f i j| ≤ (N : ℝ) ^ 2 * c :=
  ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)).trans
    (sum_pairs_le hc hf)

variable {y : Fin (N * N) → ℝ} {δ R : ℝ}

theorem abs_lyap_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hgap : ∀ i j, i ≠ j → δ ≤ |lam N i y - lam N j y|)
    (hspr : ∀ i j, |lam N i y - lam N j y| ≤ R) :
    |lyap N y| ≤ (N : ℝ) ^ 2 * (Real.log R - Real.log δ) := by
  have hlR := Real.log_nonneg hR
  have hlδ := Real.log_nonpos hδ.le hδ1
  refine abs_sum_pairs_le (by linarith) fun i j hj => abs_le.mpr ⟨?_, ?_⟩
  · have := log_le_log_of_le_abs hδ (hgap i j (Ne.symm (ne_of_mem_erase hj))); linarith
  · have := log_le_log_of_abs_le hR (hspr i j); linarith

theorem lyap_le (hR : 1 ≤ R) (hspr : ∀ i j, |lam N i y - lam N j y| ≤ R) :
    lyap N y ≤ (N : ℝ) ^ 2 * Real.log R :=
  sum_pairs_le (Real.log_nonneg hR) fun i j _ => log_le_log_of_abs_le hR (hspr i j)

theorem row_log_le (hR : 1 ≤ R) (hspr : ∀ i j, |lam N i y - lam N j y| ≤ R) (i : Fin N)
    (s : Finset (Fin N)) :
    ∑ j ∈ s, Real.log (lam N i y - lam N j y) ≤ (N : ℝ) * Real.log R :=
  calc _ ≤ ∑ _j : Fin N, Real.log R :=
        (sum_le_sum fun j _ => log_le_log_of_abs_le hR (hspr i j)).trans
          (sum_le_sum_of_subset_of_nonneg (subset_univ s) fun _ _ _ => Real.log_nonneg hR)
    _ = _ := by simp

/-- One small gap forces the Lyapunov function down. -/
theorem lyap_le_of_close (hR : 1 ≤ R) (hspr : ∀ i j, |lam N i y - lam N j y| ≤ R)
    {i₀ j₀ : Fin N} (hij : i₀ ≠ j₀) {ε : ℝ} (hpos : 0 < |lam N i₀ y - lam N j₀ y|)
    (hle : |lam N i₀ y - lam N j₀ y| ≤ ε) :
    lyap N y ≤ 2 * (N : ℝ) ^ 2 * Real.log R + Real.log ε := by
  have hlR := Real.log_nonneg hR
  have hj₀ : j₀ ∈ univ.erase i₀ := mem_erase.mpr ⟨Ne.symm hij, mem_univ _⟩
  unfold lyap
  rw [← add_sum_erase _ _ (mem_univ i₀), ← add_sum_erase _ _ hj₀]
  have h1 : Real.log (lam N i₀ y - lam N j₀ y) ≤ Real.log ε := by
    rw [← Real.log_abs (lam N i₀ y - lam N j₀ y)]; exact Real.log_le_log hpos hle
  have h2 := row_log_le hR hspr i₀ ((univ.erase i₀).erase j₀)
  have h3 : ∑ i ∈ univ.erase i₀, ∑ j ∈ univ.erase i, Real.log (lam N i y - lam N j y) ≤
      (N : ℝ) ^ 2 * Real.log R :=
    calc _ ≤ ∑ _i ∈ univ.erase i₀, (N : ℝ) * Real.log R :=
          sum_le_sum fun i _ => row_log_le hR hspr i _
      _ ≤ ∑ _i : Fin N, (N : ℝ) * Real.log R :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp; ring
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · nlinarith [(show (1 : ℝ) ≤ N by exact_mod_cast h)]
  nlinarith [mul_le_mul_of_nonneg_right hNN hlR]

theorem lyapDrift_le (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |lam N i y - lam N j y|) :
    lyapDrift N y ≤ (N : ℝ) ^ 2 * (δ⁻¹) ^ 2 := by
  have hS : ∑ i, ∑ j ∈ univ.erase i, ((lam N i y - lam N j y)⁻¹) ^ 2 ≤ (N : ℝ) ^ 2 * (δ⁻¹) ^ 2 :=
    sum_pairs_le (sq_nonneg _) fun i j hj => by
      rw [← sq_abs, abs_inv]
      exact pow_le_pow_left₀ (by positivity)
        (inv_anti₀ hδ (hgap i j (Ne.symm (ne_of_mem_erase hj)))) 2
  have hS0 : 0 ≤ ∑ i, ∑ j ∈ univ.erase i, ((lam N i y - lam N j y)⁻¹) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hN1 : 1 / (N : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact (div_le_one (by exact_mod_cast h)).mpr (by exact_mod_cast h)
  unfold lyapDrift
  nlinarith

end BlockBand.SourceProcess.Stochastic.Dyson
