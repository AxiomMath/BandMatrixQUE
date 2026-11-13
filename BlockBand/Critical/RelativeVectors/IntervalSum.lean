module

public import BlockBand.Critical.RelativeVectors.IntervalKernel

/-!
# The abstract interval comparison

Deterministic and abstract (finite sums of reals; no matrix or law). Points `λ_i`, weights
`μ_i ≥ 0`, a scale `n`, a continuous Lipschitz weight `φ` on `[x, y]`. With
`I_w(e) = Σ_i μ_i pk h (λ_i - e)` (`= Im w^*G(e+ih)w` for `μ_i = |w^*u_i|²`) and
`I_t(e) = Σ_i pk h (λ_i - e)` (`= Im Tr G(e+ih)`), `S = {i : λ_i ∈ [x, y]}`:

`interval_sum_compare`: if `|n I_w(e) - φ(e) I_t(e)| ≤ ε₁` on `[x, y]` (the local law at
height `h`, isotropic against scalar, with the smooth covariance `φ`), then
`|n Σ_S μ_i - Σ_S φ(λ_i)| ≤ C(n S_μ + B_φ S_1 + L(y-x)B_W) + (y-x)ε₁/π`, `C = 2R² + 4`, where
`S_μ`, `S_1` are the dyadic endpoint sums (`dyW`) of the two measures at `x` and `y`, `B_φ`, `L`
bound `φ` and its Lipschitz constant, and `B_W` bounds `Σ_S dyW(λ_i - e)` on `[x, y]`.

Proof: integrate over the bottom side `[x, y]` at height `h` (`integral_pk`); the kernel error
against the indicator is `indicator_sub_kap_le` (endpoint strips); `φ` is transferred from the
spectral integral to the eigenvalue sum by `abs_mul_pk_le` (its Lipschitz variation under the
kernel). This replaces an integration by parts against the counting function: the isotropic and
the scalar local laws enter only through `ε₁`, at energies, so no rank/energy matching of
endpoints is needed (the endpoints may themselves be eigenvalues).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Real Set

variable {ι : Type*} [Fintype ι]

theorem intervalIntegrable_pk {h : ℝ} (hh : 0 < h) (lam x y : ℝ) :
    IntervalIntegrable (fun e => pk h (lam - e)) MeasureTheory.volume x y :=
  ((continuous_pk hh).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _

theorem continuous_dyW {h : ℝ} (hh : 0 < h) (K : ℕ) : Continuous (dyW h K) := by
  unfold dyW
  refine continuous_const.mul ((continuous_finsetSum _ fun k _ => ?_).add (continuous_pk one_pos))
  exact continuous_pk (by positivity)

/-- One eigenvalue: the weight `φ` under the kernel against `1_S φ(λ)`. -/
theorem single_weight_le {h R : ℝ} (hh : 0 < h) (hR : 1 ≤ R) {K : ℕ}
    (hK : 1 < 2 ^ (K + 1) * h) {x y : ℝ} (hxy : x ≤ y) (hyx : y - x ≤ R) {φ : ℝ → ℝ}
    (hφc : ContinuousOn φ (Icc x y)) {Bφ L : ℝ} (hL0 : 0 ≤ L) (hφb : ∀ e ∈ Icc x y, |φ e| ≤ Bφ)
    (hφL : ∀ e ∈ Icc x y, ∀ e' ∈ Icc x y, |φ e - φ e'| ≤ L * |e - e'|) (lam : ℝ) :
    |(∫ e in x..y, φ e * pk h (lam - e)) / π - (if lam ∈ Icc x y then φ lam else 0)| ≤
      Bφ * ((2 * R ^ 2 + 4) * (dyW h K (lam - x) + dyW h K (lam - y))) +
        (if lam ∈ Icc x y then L * (2 * R ^ 2 + 4) * (∫ e in x..y, dyW h K (lam - e)) / π
          else 0) := by
  have hC0 : 0 ≤ 2 * R ^ 2 + 4 := by positivity
  have hB0 : 0 ≤ Bφ := (abs_nonneg _).trans (hφb x ⟨le_rfl, hxy⟩)
  have hker := indicator_sub_kap_le hh hR hK hxy hyx lam
  have hpkc : ContinuousOn (fun e => pk h (lam - e)) (Icc x y) :=
    ((continuous_pk hh).comp (continuous_const.sub continuous_id)).continuousOn
  have huIcc : uIcc x y = Icc x y := uIcc_of_le hxy
  have hint : IntervalIntegrable (fun e => φ e * pk h (lam - e)) MeasureTheory.volume x y := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hφc.mul hpkc
  have hk := kap_eq_integral hh x y lam
  by_cases hin : lam ∈ Icc x y
  · simp only [hin, ↓reduceIte] at hker ⊢
    -- (1/π)∫ φ pk - φ(λ) = (1/π)∫ (φ - φ(λ)) pk + φ(λ)(kap - 1)
    have hsplit : (∫ e in x..y, φ e * pk h (lam - e)) / π - φ lam =
        (∫ e in x..y, (φ e - φ lam) * pk h (lam - e)) / π + φ lam * (kap h x y lam - 1) := by
      have : ∫ e in x..y, (φ e - φ lam) * pk h (lam - e) =
          (∫ e in x..y, φ e * pk h (lam - e)) - φ lam * ∫ e in x..y, pk h (lam - e) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hint
          ((intervalIntegrable_pk hh lam x y).const_mul _)]
        congr 1; ext e; ring
      rw [this, hk]
      field_simp
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have h2 : |φ lam * (kap h x y lam - 1)| ≤
        Bφ * ((2 * R ^ 2 + 4) * (dyW h K (lam - x) + dyW h K (lam - y))) := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul (hφb lam hin) hker (abs_nonneg _) hB0
    have h1 : |(∫ e in x..y, (φ e - φ lam) * pk h (lam - e)) / π| ≤
        L * (2 * R ^ 2 + 4) * (∫ e in x..y, dyW h K (lam - e)) / π := by
      rw [abs_div, abs_of_pos pi_pos, div_le_div_iff_of_pos_right pi_pos]
      refine (intervalIntegral.abs_integral_le_integral_abs hxy).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hxy
      · apply ContinuousOn.intervalIntegrable
        rw [huIcc]
        exact ((hφc.sub continuousOn_const).mul hpkc).abs
      · exact ((continuous_dyW hh K).comp (continuous_const.sub continuous_id)).intervalIntegrable
          _ _ |>.const_mul _
      · intro e he
        rw [abs_mul, abs_of_nonneg (pk_nonneg hh.le _)]
        have hd : |lam - e| ≤ R := by
          rw [abs_le]; constructor <;> linarith [he.1, he.2, hin.1, hin.2]
        have h3 := abs_mul_pk_le hh hR hK hd
        have h4 := hφL e he lam hin
        rw [abs_sub_comm e lam] at h4
        calc |φ e - φ lam| * pk h (lam - e) ≤ L * |lam - e| * pk h (lam - e) :=
              mul_le_mul_of_nonneg_right h4 (pk_nonneg hh.le _)
          _ = L * (|lam - e| * pk h (lam - e)) := by ring
          _ ≤ L * ((2 * R ^ 2 + 4) * dyW h K (lam - e)) := mul_le_mul_of_nonneg_left h3 hL0
          _ = L * (2 * R ^ 2 + 4) * dyW h K (lam - e) := by ring
    linarith
  · simp only [hin, ↓reduceIte, sub_zero, add_zero] at hker ⊢
    rw [zero_sub, abs_neg, abs_of_nonneg (kap_nonneg hh hxy lam)] at hker
    have hb : |(∫ e in x..y, φ e * pk h (lam - e)) / π| ≤ Bφ * kap h x y lam := by
      rw [abs_div, abs_of_pos pi_pos, hk, mul_div_assoc', div_le_div_iff_of_pos_right pi_pos]
      refine (intervalIntegral.abs_integral_le_integral_abs hxy).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hxy
      · apply ContinuousOn.intervalIntegrable
        rw [huIcc]; exact (hφc.mul hpkc).abs
      · exact (intervalIntegrable_pk hh lam x y).const_mul _
      · intro e he
        rw [abs_mul, abs_of_nonneg (pk_nonneg hh.le _)]
        exact mul_le_mul_of_nonneg_right (hφb e he) (pk_nonneg hh.le _)
    exact hb.trans (mul_le_mul_of_nonneg_left hker hB0)

/-- **The abstract interval comparison.** See the module docstring. -/
theorem interval_sum_compare {h R : ℝ} (hh : 0 < h) (hR : 1 ≤ R) {K : ℕ}
    (hK : 1 < 2 ^ (K + 1) * h) {x y : ℝ} (hxy : x ≤ y) (hyx : y - x ≤ R)
    (lam μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) {n : ℝ} (hn : 0 ≤ n) {φ : ℝ → ℝ}
    (hφc : ContinuousOn φ (Icc x y)) {Bφ L ε₁ BW : ℝ} (hL0 : 0 ≤ L) (hφb : ∀ e ∈ Icc x y, |φ e| ≤ Bφ)
    (hφL : ∀ e ∈ Icc x y, ∀ e' ∈ Icc x y, |φ e - φ e'| ≤ L * |e - e'|)
    (h1 : ∀ e ∈ Icc x y, |n * (∑ i, μ i * pk h (lam i - e)) - φ e * ∑ i, pk h (lam i - e)| ≤ ε₁)
    (h3 : ∀ e ∈ Icc x y,
      ∑ i ∈ Finset.univ.filter (fun i => lam i ∈ Icc x y), dyW h K (lam i - e) ≤ BW) :
    |n * (∑ i ∈ Finset.univ.filter (fun i => lam i ∈ Icc x y), μ i) -
        ∑ i ∈ Finset.univ.filter (fun i => lam i ∈ Icc x y), φ (lam i)| ≤
      (2 * R ^ 2 + 4) * (n * ∑ i, μ i * (dyW h K (lam i - x) + dyW h K (lam i - y)) +
        Bφ * ∑ i, (dyW h K (lam i - x) + dyW h K (lam i - y)) + L * (y - x) * BW / π) +
      (y - x) * ε₁ / π := by
  classical
  set C := 2 * R ^ 2 + 4 with hCdef
  have hC0 : 0 ≤ C := by positivity
  set S := Finset.univ.filter (fun i => lam i ∈ Icc x y) with hS
  have huIcc : uIcc x y = Icc x y := uIcc_of_le hxy
  have hpkc : ∀ i, ContinuousOn (fun e => pk h (lam i - e)) (Icc x y) := fun i =>
    ((continuous_pk hh).comp (continuous_const.sub continuous_id)).continuousOn
  have hint : ∀ i, IntervalIntegrable (fun e => φ e * pk h (lam i - e)) MeasureTheory.volume x y :=
    fun i => by apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hφc.mul (hpkc i)
  -- indicator sums
  have hSμ : ∑ i ∈ S, μ i = ∑ i, (if lam i ∈ Icc x y then 1 else 0) * μ i := by
    rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun i _ => ?_; split_ifs <;> simp
  have hSφ : ∑ i ∈ S, φ (lam i) = ∑ i, (if lam i ∈ Icc x y then φ (lam i) else 0) := by
    rw [Finset.sum_filter]
  -- the spectral integrals
  have hIw : (∫ e in x..y, n * ∑ i, μ i * pk h (lam i - e)) / π =
      n * ∑ i, μ i * kap h x y (lam i) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun i _ => (intervalIntegrable_pk hh (lam i) x y).const_mul (μ i))]
    simp only [intervalIntegral.integral_const_mul, kap_eq_integral hh]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hIt : (∫ e in x..y, φ e * ∑ i, pk h (lam i - e)) / π =
      ∑ i, (∫ e in x..y, φ e * pk h (lam i - e)) / π := by
    simp only [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum (fun i _ => hint i), Finset.sum_div]
  have hIwI : IntervalIntegrable (fun e => n * ∑ i, μ i * pk h (lam i - e)) MeasureTheory.volume
      x y := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul
      ((continuous_pk hh).comp (continuous_const.sub continuous_id)))
  have hItI : IntervalIntegrable (fun e => φ e * ∑ i, pk h (lam i - e)) MeasureTheory.volume
      x y := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hφc.mul (continuousOn_finsetSum _ fun i _ => hpkc i)
  -- decomposition
  set T1 := n * ∑ i, ((if lam i ∈ Icc x y then 1 else 0) - kap h x y (lam i)) * μ i
  set T2 := (∫ e in x..y, (n * ∑ i, μ i * pk h (lam i - e) - φ e * ∑ i, pk h (lam i - e))) / π
  set T3 := ∑ i, ((∫ e in x..y, φ e * pk h (lam i - e)) / π -
      (if lam i ∈ Icc x y then φ (lam i) else 0))
  have hdec : n * (∑ i ∈ S, μ i) - ∑ i ∈ S, φ (lam i) = T1 + T2 + T3 := by
    have e2 : T2 = n * ∑ i, μ i * kap h x y (lam i) -
        ∑ i, (∫ e in x..y, φ e * pk h (lam i - e)) / π := by
      simp only [T2]
      rw [intervalIntegral.integral_sub hIwI hItI, sub_div, hIw, hIt]
    have eT1 : T1 = n * ∑ i, (if lam i ∈ Icc x y then 1 else 0) * μ i -
        n * ∑ i, μ i * kap h x y (lam i) := by
      simp only [T1, sub_mul, Finset.sum_sub_distrib, mul_sub]
      congr 2
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have eT3 : T3 = ∑ i, (∫ e in x..y, φ e * pk h (lam i - e)) / π -
        ∑ i, (if lam i ∈ Icc x y then φ (lam i) else 0) := Finset.sum_sub_distrib _ _
    rw [eT1, e2, eT3, hSμ, hSφ]
    ring
  rw [hdec]
  -- bounds
  have hT1 : |T1| ≤ C * (n * ∑ i, μ i * (dyW h K (lam i - x) + dyW h K (lam i - y))) := by
    simp only [T1]
    rw [abs_mul, abs_of_nonneg hn]
    have : |∑ i, ((if lam i ∈ Icc x y then 1 else 0) - kap h x y (lam i)) * μ i| ≤
        C * ∑ i, μ i * (dyW h K (lam i - x) + dyW h K (lam i - y)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (hμ i)]
      have := indicator_sub_kap_le hh hR hK hxy hyx (lam i)
      nlinarith [hμ i]
    nlinarith
  have hT2 : |T2| ≤ (y - x) * ε₁ / π := by
    simp only [T2]
    rw [abs_div, abs_of_pos pi_pos, div_le_div_iff_of_pos_right pi_pos]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y)
      (f := fun e => n * ∑ i, μ i * pk h (lam i - e) - φ e * ∑ i, pk h (lam i - e)) (C := ε₁)
      (fun e he => by
        rw [Real.norm_eq_abs]
        exact h1 e (by rw [uIoc_of_le hxy] at he; exact ⟨he.1.le, he.2⟩))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hxy)] at this
    linarith
  have hT3 : |T3| ≤ C * (Bφ * ∑ i, (dyW h K (lam i - x) + dyW h K (lam i - y))) +
      C * (L * (y - x) * BW / π) := by
    simp only [T3]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ =>
      single_weight_le hh hR hK hxy hyx hφc hL0 hφb hφL (lam i)).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add (le_of_eq ?_) ?_
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    · rw [← Finset.sum_filter]
      · have e : ∑ i ∈ S, L * C * (∫ e in x..y, dyW h K (lam i - e)) / π =
            L * C * (∫ e in x..y, ∑ i ∈ S, dyW h K (lam i - e)) / π := by
          rw [intervalIntegral.integral_finsetSum (f := fun i e => dyW h K (lam i - e)) fun i _ =>
            ((continuous_dyW hh K).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _,
            Finset.mul_sum, Finset.sum_div]
        rw [e, show C * (L * (y - x) * BW / π) = L * C * ((y - x) * BW) / π by ring]
        rw [div_le_div_iff_of_pos_right pi_pos]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL0 hC0)
        have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
          (f := fun e => ∑ i ∈ S, dyW h K (lam i - e)) (g := fun _ => BW) hxy
          ((continuous_finsetSum _ fun i _ =>
            (continuous_dyW hh K).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _)
          intervalIntegrable_const (fun e he => h3 e he)
        rw [intervalIntegral.integral_const, smul_eq_mul] at this
        linarith
  have hsum := add_le_add (add_le_add hT1 hT2) hT3
  calc |T1 + T2 + T3| ≤ |T1| + |T2| + |T3| := (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

end BlockBand.Critical.RelativeVectors
