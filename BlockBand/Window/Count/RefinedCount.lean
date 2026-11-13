module

public import BlockBand.Window.Count.RefinedCountSplit
public import BlockBand.Window.Count.RefinedCountTools
public import BlockBand.Window.Count.SpectralSmoothing

/-!
# The refined count: auxiliary bounds

Elementary bounds (`|Im a²| ≤ 1`, `N_-(M) ≤ dim`, `1 ≤ a_{n,W}`, `W^{1/3} ≤ a_{n,W}/log 2`) for the
count clause of the refined count, `‖N_H(e) - N F_sc(e)‖_q ≤ C_q a_{n,W}`, proved in
`refinedCount_count_of`.

Proof outline (with the mean taken from the rank-location theorem): delete block `0`;
a.s. `N_H = Ξ + Z + M(Σ) + κ₀` with `Ξ = ringCompensatedPhase`, `Z = N_-(A₀-e-Σ) - E_A N_-`,
`M(Σ) = E_A N_-(A₀-e-Σ) - Θ_{z₀}(Σ) - κ₀`, `κ₀ = cW Im a²/(2π)`. Then
* `‖Ξ - EΞ‖_q ≤ C√n` (`RingCompensatedPhaseContract.fluctuation`);
* `‖Z‖_q ≤ C W^{1/3}` (`SharperFreshCountStatement`, conditionally on `Σ`, then Fubini);
* `|M(Σ)| ≤ C(W d² + W^{2/5} log 2W)` on `d ≤ d_*` (`FreshCountContract.mean`) and
  `|M| ≤ 3W ≤ 3W d²/d_*²` off it, with `‖d‖_{2q} ≤ C√(2q)/W`
  (`MatchedTracesContract.commonPort`, for `W ≥ 2q/ε₀`);
* `|E N_H - N F_sc| ≤ C(n/W + W^{2/5} log 2W)` (`RankLocationContract.count_mean`);
* for `W < 2q/ε₀`, `‖N_H - NF_sc‖_q ≤ C√W` (`RankLocationContract.count_moment`).
The structural input is `RingFreshBlockSplitAE` (Schur inertia, transport to `Fin W`,
fresh-block independence), proved as `ringFreshBlockSplitAE`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal NNReal

theorem norm_matchedA_sq_im_le {E : ℝ} (hE : |E| ≤ 2) : |(matchedA E ^ 2).im| ≤ 1 := by
  have hs : Real.sqrt (4 - E ^ 2) * Real.sqrt (4 - E ^ 2) = 4 - E ^ 2 := by
    rw [Real.mul_self_sqrt]; nlinarith [abs_le.mp hE]
  have h1 : ‖matchedA E‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [matchedA, Complex.normSq_apply]; nlinarith [hs]
  calc |(matchedA E ^ 2).im| ≤ ‖matchedA E ^ 2‖ := Complex.abs_im_le_norm _
    _ = 1 := by rw [norm_pow, h1]

theorem negativeCount_le_card {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    (negativeCount M : ℝ) ≤ Fintype.card ι := by
  rw [negativeCount_cast]
  have := abs_spectralSum_le (g := negInd) (B := 1)
    (fun x => by unfold negInd; split_ifs <;> simp) M
  simpa using (le_abs_self _).trans this

theorem measurable_negativeCount_real {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun M : Matrix ι ι ℂ => (negativeCount M : ℝ)) := by
  simp_rw [negativeCount_cast]; exact measurable_spectralSum measurable_negInd

theorem one_le_countScale (p : BlockBand.Parameters) : 1 ≤ countScale p.n p.W := by
  unfold countScale
  have hn : (4 : ℝ) ≤ p.n := by exact_mod_cast p.n_ge_four
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have h1 : 1 ≤ Real.sqrt p.n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 : 0 ≤ (p.n : ℝ) / p.W := by positivity
  have h3 : 0 ≤ (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  linarith

theorem rpow_third_le_countScale (p : BlockBand.Parameters) :
    (p.W : ℝ) ^ (1 / 3 : ℝ) ≤ countScale p.n p.W / Real.log 2 := by
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have h1 : (p.W : ℝ) ^ (1 / 3 : ℝ) ≤ (p.W : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
  have h2 : Real.log 2 ≤ Real.log (2 * p.W) := Real.log_le_log (by norm_num) (by linarith)
  have h3 : (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) ≤ countScale p.n p.W := by
    unfold countScale
    have : 0 ≤ Real.sqrt p.n + (p.n : ℝ) / p.W := by positivity
    linarith
  calc (p.W : ℝ) ^ (1 / 3 : ℝ) * Real.log 2 ≤ (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * p.W) :=
        mul_le_mul h1 h2 hl2.le (by positivity)
    _ ≤ _ := h3

end BlockBand.Window.Count
