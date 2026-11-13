module

public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreBackward
public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreInitial
public import BlockBand.Endpoints.Response.TaggedConvexOrder

/-!
# The fixed-energy core of the tagged convex order theorem

## Main results

* `tcc_comparisonAlong`: along one tagged sequence, the prelimit convex comparison
  `TcoConvexComparisonAlong` (the content of `TcoTagComparisonCore`) from three inputs along the
  sequence: the summed one-step inequality `TcoOneStepAlong` (the one-step expansion, the
  remainder bound and the drift bound), the moments `TccMomentsAlong` and the initial value
  `TccBirthAlong`. The proof is the backward comparison: with
  `u_l = tcc_backward D₀ ((n-l)/W) φ`, `E φ(Z_n) - E Ψ_{u_{k+1}}(Q_{k+1})` telescopes into the
  one-step terms of `TcoOneStepAlong` applied to the convex family `u_{l+1}`, plus the
  time-discretization error `Σ_l Σ_m φ_m e^{λ_m t_{l+1}}(1 + λ_m/W - e^{λ_m/W}) E Z_l^m = O(1/W)`;
  and `E Ψ_{u_{k+1}}(Q_{k+1}) → u(τ - s, d) = E φ(d e^{√D₀B_{τ-s} - D₀(τ-s)/2})` by the initial
  value. The energy is not used: the energy-uniform core needs only energy-uniform versions of the
  three inputs.
* `taggedConvexOrder_fixed_of_oneStep`: the fixed-energy statement
  `TaggedConvexOrderFixedStatement` (`taggedConvexOrder_fixed` composed with the above).

Besides the contracts, the hypothesis is `TcoOneStepCoreFixed`, a finite-`W` one-step statement strictly
weaker than `TcoTagComparisonCoreFixed`; see the docstring of `TcoOneStepAlong`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- `∫ψ dμ = Σ_{m ≤ M} ψ_m ∫x^m dμ` for `deg ψ ≤ M`. -/
theorem tcc_integral_poly_eq_sum {μ : Measure ℝ} {M : ℕ}
    (hi : ∀ m ∈ range (M + 1), Integrable (fun x : ℝ => x ^ m) μ) {ψ : ℝ[X]}
    (hψ : ψ.natDegree ≤ M) :
    ∫ x, ψ.eval x ∂μ = ∑ m ∈ range (M + 1), ψ.coeff m * ∫ x, x ^ m ∂μ := by
  simp_rw [tcc_eval_eq_sum hψ]
  rw [integral_finsetSum _ fun m hm => (hi m hm).const_mul _]
  exact sum_congr rfl fun m _ => integral_const_mul _ _

/-- `|E x^m| ≤ 1 + C` from `E x^{2m} ≤ C`. -/
theorem tcc_abs_moment_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (m : ℕ) {C : ℝ}
    (hC : ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ ≤ ENNReal.ofReal C) :
    |∫ x, x ^ m ∂μ| ≤ 1 + max C 0 := by
  obtain ⟨i2, -⟩ := tco_integrable_of_lintegral_pow m hC
  have h0 : ∀ x : ℝ, 0 ≤ x ^ (2 * m) := fun x => by rw [pow_mul]; positivity
  have hle : ∫ x, x ^ (2 * m) ∂μ ≤ max C 0 :=
    tcc_integral_le_of_lintegral h0 (by fun_prop) (le_max_right _ _)
      (hC.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hpt : ∀ x : ℝ, |x ^ m| ≤ 1 + x ^ (2 * m) := by
    intro x
    rw [abs_pow]
    rcases le_or_gt |x| 1 with h | h
    · have : |x| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg x) h
      linarith [h0 x]
    · have : |x| ^ m ≤ |x| ^ (2 * m) := pow_le_pow_right₀ h.le (by omega)
      rw [(even_two_mul m).pow_abs] at this
      linarith
  calc |∫ x, x ^ m ∂μ| ≤ ∫ x, |x ^ m| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (1 + x ^ (2 * m)) ∂μ :=
        integral_mono (tco_integrable_of_lintegral_pow m hC).2.abs
          ((integrable_const _).add i2) hpt
    _ = 1 + ∫ x, x ^ (2 * m) ∂μ := by
        rw [integral_add (integrable_const _) i2, integral_const]; simp [measureReal_def]
    _ ≤ 1 + max C 0 := by linarith

theorem tcc_sum_Ico_telescope (V : ℕ → ℝ) {k n : ℕ} (h : k ≤ n) :
    ∑ l ∈ Ico k n, (V (l + 1) - V l) = V n - V k := by
  rw [sum_Ico_eq_sum_range]
  have := sum_range_sub (fun i => V (k + i)) (n - k)
  rw [show k + (n - k) = n by omega, add_zero] at this
  rw [← this]
  exact sum_congr rfl fun i _ => by rw [add_assoc]

/-- The telescoping identity of the backward comparison, in coefficients: `t_l = (n-l)/w`,
`V_l = Σ_m a_m e^{λ_m t_l} M_{l,m}`. -/
theorem tcc_telescope_identity (a lam : ℕ → ℝ) (N n k : ℕ) {w : ℝ} (hw : w ≠ 0)
    (mom : ℕ → ℕ → ℝ) (hk : k + 1 ≤ n) :
    (∑ m ∈ range (N + 1), a m * Real.exp (lam m * (((n - n : ℕ) : ℝ) / w)) * mom n m) -
      ∑ m ∈ range (N + 1), a m * Real.exp (lam m * (((n - (k + 1) : ℕ) : ℝ) / w)) *
        mom (k + 1) m =
    ∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (N + 1), a m *
        Real.exp (lam m * (((n - (l + 1) : ℕ) : ℝ) / w)) *
        (mom (l + 1) m - mom l m - w⁻¹ * (lam m * mom l m)) +
      ∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (N + 1), a m *
        Real.exp (lam m * (((n - (l + 1) : ℕ) : ℝ) / w)) *
        (1 + lam m / w - Real.exp (lam m / w)) * mom l m := by
  set V : ℕ → ℝ := fun l => ∑ m ∈ range (N + 1),
    a m * Real.exp (lam m * (((n - l : ℕ) : ℝ) / w)) * mom l m
  change V n - V (k + 1) = _
  rw [← tcc_sum_Ico_telescope V hk, ← sum_add_distrib]
  refine sum_congr rfl fun l hl => ?_
  have hln : l < n := (mem_Ico.1 hl).2
  simp only [V]
  rw [← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  have ht : (((n - l : ℕ) : ℝ) / w) = (((n - (l + 1) : ℕ) : ℝ) / w) + 1 / w := by
    rw [show n - l = (n - (l + 1)) + 1 by omega]; push_cast; ring
  rw [ht, mul_add, Real.exp_add]
  field_simp
  ring

/-- The prelimit convex comparison along one tagged sequence, from the summed one-step
inequality, the moments and the initial value along the sequence. -/
theorem tcc_comparisonAlong {b : ℝ} {s τ E : ℝ} (σ : TcoTagSequence s τ E)
    (hD0 : 0 ≤ transportD0 b E) (hOne : TcoOneStepAlong b σ) (hM : TccMomentsAlong b σ)
    (hB : TccBirthAlong b σ) : TcoConvexComparisonAlong b σ := by
  intro φ hφ δ hδ
  set D0 := transportD0 b E
  set N := φ.natDegree
  set T' := τ + 1
  set a : ℕ → ℝ := fun i => φ.coeff i
  set lam : ℕ → ℝ := tcc_lam D0
  have hlam : ∀ m, 0 ≤ lam m := tcc_lam_nonneg hD0
  have hsτ := tco_tagSequence_s_le σ
  choose Cf hCf using hM
  set Mb : ℕ → ℝ := fun m => 1 + max (Cf m) 0
  have hMb : ∀ m, 0 ≤ Mb m := fun m => by have := le_max_right (Cf m) 0; simp only [Mb]; linarith
  set Acoef : ℝ := ∑ i ∈ range (N + 1), |a i| * Real.exp (lam i * T')
  set K2 : ℝ := ∑ m ∈ range (N + 1), |a m| * Real.exp (lam m * T') * (lam m ^ 2 / 2) * Mb m
  have hK2 : 0 ≤ K2 := sum_nonneg fun m _ => by have := hMb m; positivity
  -- the time to the end at the birth length
  set tt : ℕ → ℕ → ℝ := fun j l => (((σ.n j - l : ℕ) : ℝ) / σ.W j)
  set mom : ℕ → ℕ → ℕ → ℝ := fun j l m =>
    ∫ x, x ^ m ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j)
  have hW0 : ∀ j, (0 : ℝ) < σ.W j := fun j => by exact_mod_cast σ.W_pos j
  have hinvW : Tendsto (fun j => ((σ.W j : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp σ.width_tendsto)
  have htt : Tendsto (fun j => tt j (σ.k j + 1)) atTop (𝓝 (τ - s)) := by
    have e : ∀ j, tt j (σ.k j + 1) =
        (σ.n j : ℝ) / σ.W j - (σ.k j : ℝ) / σ.W j - ((σ.W j : ℝ))⁻¹ := by
      intro j
      simp only [tt]
      rw [Nat.cast_sub (σ.tag_lt j)]
      push_cast
      ring
    simp_rw [e]
    simpa using (σ.ratio_tendsto.sub σ.tag_tendsto).sub hinvW
  -- the initial value
  set G : ℝ := tco_gbmExpect D0 (dStar b) (τ - s) φ
  have hG : G = ∑ m ∈ range (N + 1),
      a m * Real.exp (lam m * (τ - s)) * dStar b ^ m := by
    simp only [G]
    rw [tcc_gbmExpect_eq_eval_backward D0 _ _ hD0 (by linarith),
      tcc_eval_eq_sum (tcc_backward_natDegree_le D0 (τ - s) φ)]
    exact sum_congr rfl fun m _ => by rw [tcc_backward_coeff]
  have hVk : Tendsto (fun j => ∑ m ∈ range (N + 1),
      a m * Real.exp (lam m * tt j (σ.k j + 1)) * mom j (σ.k j + 1) m) atTop (𝓝 G) := by
    rw [hG]
    refine tendsto_finsetSum _ fun m _ => ?_
    exact (tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul htt))).mul (hB m)
  -- eventual conditions
  have hmomE : ∀ᶠ j in atTop, ∀ m ∈ range (N + 1), ∀ l, σ.k j < l → l ≤ σ.n j →
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
        ENNReal.ofReal (Cf m) :=
    (eventually_all_finset _).2 fun m _ => hCf m
  have hK2E : ∀ᶠ j in atTop, T' * K2 * ((σ.W j : ℝ))⁻¹ < δ / 3 := by
    have h := (tendsto_const_nhds (x := T' * K2)).mul hinvW
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  filter_upwards [tcc_eventually_len σ 0, hmomE, hK2E, hOne N Acoef (δ / 3) (by positivity),
    hVk.eventually (gt_mem_nhds (show G < G + δ / 3 by linarith))] with
    j hlen hmj hK2j hOnej hVkj
  obtain ⟨-, hn⟩ := hlen
  set W := σ.W j
  set n := σ.n j
  set k := σ.k j
  set e := σ.energy j
  have hWj := hW0 j
  have hkn : k + 1 ≤ n := σ.tag_lt j
  have hnT : (n : ℝ) / W ≤ T' := by rw [div_le_iff₀ hWj]; exact hn
  have httT : ∀ l, tt j l ≤ T' := by
    intro l
    refine le_trans ?_ hnT
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le n l) hWj.le
  have htt0 : ∀ l, 0 ≤ tt j l := fun l => by positivity
  -- integrability and moment bounds on the lengths `k < l ≤ n`
  have hint : ∀ l, k < l → l ≤ n → ∀ m ∈ range (N + 1),
      Integrable (fun x : ℝ => x ^ m) (tcc_law b e W l k) := by
    intro l h1 h2 m hm
    have := tcc_law_prob b e W l k
    exact (tco_integrable_of_lintegral_pow m (hmj m hm l h1 h2)).2
  have hmb : ∀ l, k < l → l ≤ n → ∀ m ∈ range (N + 1), |mom j l m| ≤ Mb m := by
    intro l h1 h2 m hm
    have := tcc_law_prob b e W l k
    exact tcc_abs_moment_le m (hmj m hm l h1 h2)
  -- the convex family `ψ_l = u_{l+1}`
  set ψ : ℕ → ℝ[X] := fun l => tcc_backward D0 (tt j (l + 1)) φ
  have hψdeg : ∀ l, (ψ l).natDegree ≤ N := fun l => tcc_backward_natDegree_le _ _ _
  have hψcoef : ∀ l i, |(ψ l).coeff i| ≤ Acoef := by
    intro l i
    simp only [ψ]
    rw [tcc_backward_coeff]
    by_cases hi : i ∈ range (N + 1)
    · refine le_trans ?_ (single_le_sum (f := fun i => |a i| * Real.exp (lam i * T'))
        (fun i _ => by positivity) hi)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      gcongr
      · exact hlam i
      · exact httT _
    · have : φ.natDegree < i := by simp at hi; omega
      rw [coeff_eq_zero_of_natDegree_lt this, zero_mul, abs_zero]
      exact sum_nonneg fun i _ => by positivity
  have hOne' := hOnej ψ (fun l => tcc_backward_convex D0 _ hD0 (htt0 _) hφ) hψdeg hψcoef
  -- expansion of the one-step terms
  have hA : ∑ l ∈ Ico (k + 1) n,
      (tcc_psi b e W (l + 1) k (ψ l) - tcc_psi b e W l k (ψ l) -
        (W : ℝ)⁻¹ * tcc_psi b e W l k (tcc_gen D0 (ψ l))) =
      ∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (N + 1), a m * Real.exp (lam m * tt j (l + 1)) *
        (mom j (l + 1) m - mom j l m - (W : ℝ)⁻¹ * (lam m * mom j l m)) := by
    refine sum_congr rfl fun l hl => ?_
    obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
    rw [tcc_psi_eq, tcc_psi_eq, tcc_psi_eq,
      tcc_integral_poly_eq_sum (hint (l + 1) (by omega) (by omega)) (hψdeg l),
      tcc_integral_poly_eq_sum (hint l (by omega) (by omega)) (hψdeg l),
      tcc_integral_poly_eq_sum (hint l (by omega) (by omega))
        ((tcc_gen_natDegree_le D0 _).trans (hψdeg l)), mul_sum, ← sum_sub_distrib,
      ← sum_sub_distrib]
    refine sum_congr rfl fun m _ => ?_
    simp only [ψ, tcc_gen_coeff, tcc_backward_coeff, mom, a, lam]
    ring
  -- the discretization error
  have hBl : ∀ l ∈ Ico (k + 1) n, |∑ m ∈ range (N + 1), a m * Real.exp (lam m * tt j (l + 1)) *
      (1 + lam m / W - Real.exp (lam m / W)) * mom j l m| ≤ K2 * ((W : ℝ)⁻¹) ^ 2 := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
    rw [show K2 * ((W : ℝ)⁻¹) ^ 2 = ∑ m ∈ range (N + 1),
      |a m| * Real.exp (lam m * T') * (lam m ^ 2 / 2) * Mb m * ((W : ℝ)⁻¹) ^ 2 by
      rw [sum_mul]]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
    set x := lam m / W
    have hx : 0 ≤ x := div_nonneg (hlam m) hWj.le
    obtain ⟨r0, r1⟩ := tco_exp_remainder hx 2
    simp only [sum_range_succ, sum_range_zero, pow_zero, Nat.factorial, pow_one] at r0 r1
    norm_num at r0 r1
    have hexp : Real.exp (lam m * tt j (l + 1)) * Real.exp x ≤ Real.exp (lam m * T') := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : tt j (l + 1) + (W : ℝ)⁻¹ = tt j l := by
        simp only [tt]
        rw [show n - l = (n - (l + 1)) + 1 by omega]; push_cast; ring
      calc lam m * tt j (l + 1) + x = lam m * (tt j (l + 1) + (W : ℝ)⁻¹) := by
            simp only [x]; ring
        _ ≤ lam m * T' := by rw [this]; exact mul_le_mul_of_nonneg_left (httT l) (hlam m)
    have hmm := hmb l (by omega) (by omega) m hm
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp x - (1 + x))]
    calc |a m| * Real.exp (lam m * tt j (l + 1)) * (Real.exp x - (1 + x)) * |mom j l m|
        ≤ |a m| * Real.exp (lam m * tt j (l + 1)) * (x ^ 2 * Real.exp x / 2) * Mb m := by
          gcongr
          linarith
      _ = |a m| * (Real.exp (lam m * tt j (l + 1)) * Real.exp x) * (x ^ 2 / 2) * Mb m := by
          ring
      _ ≤ |a m| * Real.exp (lam m * T') * (x ^ 2 / 2) * Mb m := by
          gcongr
      _ = |a m| * Real.exp (lam m * T') * (lam m ^ 2 / 2) * Mb m * ((W : ℝ)⁻¹) ^ 2 := by
          simp only [x]; ring
  have hBsum : |∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (N + 1), a m *
      Real.exp (lam m * tt j (l + 1)) * (1 + lam m / W - Real.exp (lam m / W)) * mom j l m| ≤
      δ / 3 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum hBl).trans ?_
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcard : ((n - (k + 1) : ℕ) : ℝ) ≤ T' * W := by
      refine le_trans (by exact_mod_cast Nat.sub_le n (k + 1)) hn
    calc ((n - (k + 1) : ℕ) : ℝ) * (K2 * ((W : ℝ)⁻¹) ^ 2)
        ≤ T' * W * (K2 * ((W : ℝ)⁻¹) ^ 2) := by gcongr
      _ = T' * K2 * (W : ℝ)⁻¹ := by field_simp
      _ ≤ δ / 3 := hK2j.le
  -- assemble
  have hid := tcc_telescope_identity a lam N n k hWj.ne' (mom j) hkn
  have hVn : (∑ m ∈ range (N + 1), a m * Real.exp (lam m * (((n - n : ℕ) : ℝ) / W)) *
      mom j n m) = tcc_psi b e W n k φ := by
    rw [tcc_psi_eq, tcc_integral_poly_eq_sum (hint n (by omega) le_rfl) le_rfl]
    refine sum_congr rfl fun m _ => ?_
    simp [a, mom, e, W, n, k]
  change tcc_psi b e W n k φ ≤ G + δ
  rw [← hVn]
  have hOne'' : ∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (N + 1), a m *
      Real.exp (lam m * tt j (l + 1)) *
      (mom j (l + 1) m - mom j l m - (W : ℝ)⁻¹ * (lam m * mom j l m)) ≤ δ / 3 := by
    rw [← hA]; exact hOne'
  have hVkj' : ∑ m ∈ range (N + 1), a m * Real.exp (lam m * (((n - (k + 1) : ℕ) : ℝ) / W)) *
      mom j (k + 1) m < G + δ / 3 := hVkj
  have := (abs_le.1 hBsum).2
  linarith

/-- **`TcoTagComparisonCoreFixed`** from `FullSourceMomentsContract` (`tag`, the moments),
`TagBirthValueContract` (`trace`, `square`, the initial value) and `TcoOneStepCoreFixed` (the
one-step expansion, the remainder bound and the drift bound), via `tcc_comparisonAlong`.
-/
theorem tcoTagComparisonCoreFixed_holds (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) (hOne : TcoOneStepCoreFixed) :
    TcoTagComparisonCoreFixed := by
  intro b hb hb' E hE1 hE2 s τ hs σ hσ
  exact tcc_comparisonAlong σ (tco_transportD0_nonneg hb hE1 hE2)
    (hOne b hb hb' E hE1 hE2 s τ hs σ hσ) (tcc_momentsAlong_fixed hMom hb hb' hE1 hE2 σ hσ)
    (tcc_birthAlong_fixed hMom hBirth hb hb' hE1 hE2 hs σ hσ)

/-- **The tagged convex order theorem at the fixed energy `E`**
(`TaggedConvexOrderFixedStatement`), from `FullSourceMomentsEnergyUniformContract` (as in
`taggedConvexOrder_fixed`), `FullSourceMomentsContract`, `TagBirthValueContract` and
`TcoOneStepCoreFixed`.
-/
theorem taggedConvexOrder_fixed_of_oneStep (hMomU : FullSourceMomentsEnergyUniformContract)
    (hMom : FullSourceMomentsContract) (hBirth : TagBirthValueContract)
    (hOne : TcoOneStepCoreFixed) : TaggedConvexOrderFixedStatement :=
  taggedConvexOrder_fixed hMomU (tcoTagComparisonCoreFixed_holds hMom hBirth hOne)

end BlockBand.Endpoints
