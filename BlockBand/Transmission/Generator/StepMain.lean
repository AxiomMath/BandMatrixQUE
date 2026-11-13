module

public import BlockBand.Transmission.Generator.StepQuad

/-!
# Zeroth-order, main and `f`-terms of the `k ≥ 2` one-step drift (deterministic)

* `step_zeroth`: `|Re Tr S̄^k - c^kP_k - kc^{k-1}(Re Tr(G_kŪ) - cP_k)| ≤ k6^{2k}‖Ū - c‖²P₁`
  (`S̄ = sand T Ū`, `G_k = gPow T k`);
* `step_main_term`: `Re Σ c^j w_{im} a(2 - t_i - t_m) = c^j(A_k + (Dk/2)P₁P_k)/W` at
  `a = D/(2W)` (`pd_drift`);
* `step_fterm`: `|Σ w_{im}(σf'_{ii}f'_{mm} + σ'conj…)| ≤ (‖σ‖+‖σ'‖)(j+1)²τ²`,
  `τ = |Tr(Tf)| + √P₁·hs(T,f)` (`wsum_quad`, `norm_sum_pow_fd_le`);
* `step_scalar`: `|c^kP_k + c^j(A_k + (Dk/2)P₁P_k)/W - P_k - A_k/W| ≤ k²y²|P_k| + jy|A_k|/W`
  for `c = (1+y)⁻¹`, `y = DP₁/(2W)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}

theorem sand_smul_one (hT : T.PosSemidef) (c : ℝ) :
    sand hT ((c : ℂ) • 1) = diagonal (fun i => ((c * ts_lam hT i : ℝ) : ℂ)) := by
  rw [sand_smul, sand_one]
  ext i m
  by_cases h : i = m
  · subst h; simp
  · simp [diagonal_apply_ne _ h]

theorem ts_ent_sub_smul_one (hT : T.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) (c : ℂ)
    (i : Fin W) : ts_ent hT (Z - c • 1) i i = ts_ent hT Z i i - c := by
  rw [sub_eq_add_neg, ← neg_smul, ts_ent_add, ts_ent_smul, ts_ent_one]; ring

/-- **Zeroth order.** -/
theorem step_zeroth (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (Ub : Matrix (Fin W) (Fin W) ℂ) (hSb : ‖sand hT Ub‖ ≤ 1) (j : ℕ) :
    |((sand hT Ub) ^ (j + 2)).trace.re - c ^ (j + 2) * ∑ i, ts_lam hT i ^ (j + 2) -
        ((j + 2 : ℕ) : ℝ) * c ^ (j + 1) * ((gPow hT (j + 2) * Ub).trace.re -
          c * ∑ i, ts_lam hT i ^ (j + 2))| ≤
      ((j + 1 + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (j + 1 + 1)) * (‖Ub - (c : ℂ) • 1‖ ^ 2 * T.trace.re) := by
  set D' := diagonal (fun i => ((c * ts_lam hT i : ℝ) : ℂ))
  set Δ := sand hT (Ub - (c : ℂ) • 1)
  have hA : sand hT Ub = D' + Δ := by simp only [Δ, sand_sub, sand_smul_one, D']; abel
  have hD'1 : ‖D'‖ ≤ 1 := norm_diagonal_le (c := (1 : ℝ)) _ zero_le_one fun i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hc0 (ts_lam_nonneg hT i))]
    nlinarith [ts_lam_nonneg hT i, ht1 i]
  have hΔ : ‖Δ‖ ≤ 2 := by
    have : Δ = sand hT Ub - D' := by rw [hA]; abel
    rw [this]; exact (norm_sub_le _ _).trans (by linarith)
  have h := pe_first (hD'1.trans (by norm_num)) hΔ (by norm_num : (1 : ℝ) ≤ 2) (j + 1)
  have hP : (D' ^ (j + 1 + 1)).trace = (((c ^ (j + 2) * ∑ i, ts_lam hT i ^ (j + 2)) : ℝ) : ℂ) := by
    rw [trace_diag_pow]; push_cast; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hL : (D' ^ (j + 1) * Δ).trace = (((c ^ (j + 1) * ((gPow hT (j + 2) * Ub).trace.re -
      c * ∑ i, ts_lam hT i ^ (j + 2))) : ℝ) : ℂ) + (c ^ (j + 1) : ℂ) *
      (((gPow hT (j + 2) * Ub).trace.im : ℝ) * Complex.I) := by
    have e1 : (D' ^ (j + 1) * Δ).trace = ∑ i, (((c * ts_lam hT i) ^ (j + 1) : ℝ) : ℂ) *
        (ts_lam hT i : ℂ) * (ts_ent hT Ub i i - c) := by
      rw [diagonal_pow, trace_diag_mul_sand]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ts_ent_sub_smul_one]
      simp
    have e2 : (gPow hT (j + 2) * Ub).trace = ((gPow hT (j + 2) * Ub).trace.re : ℂ) +
        ((gPow hT (j + 2) * Ub).trace.im : ℝ) * Complex.I := (Complex.re_add_im _).symm
    rw [trace_gPow_mul] at e2
    rw [e1]
    have e3 : ∑ i, (((c * ts_lam hT i) ^ (j + 1) : ℝ) : ℂ) * (ts_lam hT i : ℂ) *
        (ts_ent hT Ub i i - c) = (c ^ (j + 1) : ℂ) * (∑ i, ((ts_lam hT i ^ (j + 2) : ℝ) : ℂ) *
          ts_ent hT Ub i i) - (c ^ (j + 2) : ℂ) * ∑ i, ((ts_lam hT i ^ (j + 2) : ℝ) : ℂ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [e3, e2, trace_gPow_mul]
    push_cast; ring
  rw [hA] at hSb ⊢
  have hre : ((D' + Δ) ^ (j + 2)).trace.re - c ^ (j + 2) * ∑ i, ts_lam hT i ^ (j + 2) -
      ((j + 2 : ℕ) : ℝ) * c ^ (j + 1) * ((gPow hT (j + 2) * Ub).trace.re -
        c * ∑ i, ts_lam hT i ^ (j + 2)) =
      (((D' + Δ) ^ (j + 1 + 1)).trace - (D' ^ (j + 1 + 1)).trace -
        ((j + 1 + 1 : ℕ) : ℂ) * (D' ^ (j + 1) * Δ).trace).re := by
    rw [hP, hL]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im]
    push_cast
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
  exact mul_le_mul_of_nonneg_left (frobSq_sand_le hT ht1 _) (by positivity)

/-- **Main term and `f`-terms split.** -/
theorem step_main_term (hT : T.PosSemidef) (D c : ℝ) (σ σ' : ℂ) (f : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) :
    (∑ i, ∑ m, ((c ^ j : ℝ) : ℂ) * (((ts_lam hT i * ts_lam hT m *
          wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) *
          ((((D / (2 * W)) : ℝ) : ℂ) * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) +
            σ * (ts_ent hT f i i * ts_ent hT f m m) +
            σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))))).re =
      c ^ j * (transmissionDrift D (j + 2) (powSums (ts_lam hT)) + D * ((j + 2 : ℕ) : ℝ) / 2 *
        powSums (ts_lam hT) 1 * powSums (ts_lam hT) (j + 2)) / W +
      (((c ^ j : ℝ) : ℂ) * ∑ i, ∑ m, ((ts_lam hT i * ts_lam hT m *
          wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) *
          (σ * (ts_ent hT f i i * ts_ent hT f m m) +
            σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m)))).re := by
  set t := ts_lam hT
  have hd := pd_drift D t j
  have e : ∑ i, ∑ m, ((c ^ j : ℝ) : ℂ) * (((t i * t m * wsum j (t i) (t m) : ℝ) : ℂ) *
        ((((D / (2 * W)) : ℝ) : ℂ) * ((2 - t i - t m : ℝ) : ℂ) +
          σ * (ts_ent hT f i i * ts_ent hT f m m) +
          σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m)))) =
      (((c ^ j * (D / (2 * W)) * ∑ i, ∑ m, t i * t m * (2 - t i - t m) * wsum j (t i) (t m)) :
        ℝ) : ℂ) + ((c ^ j : ℝ) : ℂ) * ∑ i, ∑ m, ((t i * t m * wsum j (t i) (t m) : ℝ) : ℂ) *
          (σ * (ts_ent hT f i i * ts_ent hT f m m) +
            σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))) := by
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e, Complex.add_re, Complex.ofReal_re]
  congr 1
  have : D / 2 * ∑ i, ∑ m, t i * t m * (2 - t i - t m) * wsum j (t i) (t m) =
      transmissionDrift D (j + 2) (powSums t) + D * ((j + 2 : ℕ) : ℝ) / 2 * powSums t 1 *
        powSums t (j + 2) := by linarith
  rw [← this]
  field_simp

/-- **`f`-terms.** -/
theorem step_fterm (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) (σ σ' : ℂ)
    (f : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    ‖∑ i, ∑ m, ((ts_lam hT i * ts_lam hT m * wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) *
        (σ * (ts_ent hT f i i * ts_ent hT f m m) +
          σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m)))‖ ≤
      (‖σ‖ + ‖σ'‖) * ((j + 1 : ℕ) : ℝ) ^ 2 *
        (‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f) ^ 2 := by
  set t := ts_lam hT
  set τ := ‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f
  have hτ0 : 0 ≤ τ := add_nonneg (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  set Z := ∑ i, ∑ m, ((t i * t m * wsum j (t i) (t m) : ℝ) : ℂ) *
    (ts_ent hT f i i * ts_ent hT f m m)
  have hZ : ‖Z‖ ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * τ ^ 2 := by
    simp only [Z]
    rw [wsum_quad]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ p ∈ antidiagonal j, ‖((p.1 + 1 : ℕ) : ℂ) * ((∑ i, ((t i ^ (p.1 + 1) : ℝ) : ℂ) *
        ts_ent hT f i i) * (∑ m, ((t m ^ (p.2 + 1) : ℝ) : ℂ) * ts_ent hT f m m))‖ ≤
        ((j + 1 : ℕ) : ℝ) * τ ^ 2 := by
      intro p hp
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have a1 := norm_sum_pow_fd_le hT ht1 f (n := p.1 + 1) (by omega)
      have a2 := norm_sum_pow_fd_le hT ht1 f (n := p.2 + 1) (by omega)
      have a3 : ((p.1 + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
      calc ((p.1 + 1 : ℕ) : ℝ) * (‖∑ i, ((t i ^ (p.1 + 1) : ℝ) : ℂ) * ts_ent hT f i i‖ *
            ‖∑ m, ((t m ^ (p.2 + 1) : ℝ) : ℂ) * ts_ent hT f m m‖) ≤
            ((j + 1 : ℕ) : ℝ) * (τ * τ) :=
            mul_le_mul a3 (mul_le_mul a1 a2 (norm_nonneg _) hτ0) (by positivity) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    push_cast; ring
  have hconj : ∑ i, ∑ m, ((t i * t m * wsum j (t i) (t m) : ℝ) : ℂ) *
      (conj (ts_ent hT f i i) * conj (ts_ent hT f m m)) = conj Z := by
    simp only [Z, map_sum, map_mul, Complex.conj_ofReal]
  have e : ∑ i, ∑ m, ((t i * t m * wsum j (t i) (t m) : ℝ) : ℂ) *
      (σ * (ts_ent hT f i i * ts_ent hT f m m) +
        σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))) = σ * Z + σ' * conj Z := by
    rw [← hconj]
    simp only [Z, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have := mul_le_mul_of_nonneg_left hZ (norm_nonneg σ)
  have := mul_le_mul_of_nonneg_left hZ (norm_nonneg σ')
  nlinarith

/-- **Scalar combination.** -/
theorem step_scalar {D W' Pk P1 A y : ℝ} (hW : 0 < W') (hy : y = D * P1 / (2 * W')) (hy0 : 0 ≤ y)
    (j : ℕ) :
    |(1 + y)⁻¹ ^ (j + 2) * Pk + (1 + y)⁻¹ ^ j * (A + D * ((j + 2 : ℕ) : ℝ) / 2 * P1 * Pk) / W' -
        Pk - A / W'| ≤ ((j + 2 : ℕ) : ℝ) ^ 2 * y ^ 2 * |Pk| + j * y * |A| / W' := by
  obtain ⟨h1, h2⟩ := ck_expand hy0 j
  have e : (1 + y)⁻¹ ^ (j + 2) * Pk + (1 + y)⁻¹ ^ j * (A + D * ((j + 2 : ℕ) : ℝ) / 2 * P1 * Pk) /
      W' - Pk - A / W' = ((1 + y)⁻¹ ^ (j + 2) - 1 + ((j + 2 : ℕ) : ℝ) * y * (1 + y)⁻¹ ^ j) * Pk +
      ((1 + y)⁻¹ ^ j - 1) * A / W' := by
    rw [hy]; field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  · rw [abs_div, abs_mul, abs_of_pos hW]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) hW.le

end BlockBand.Transmission.Generator
