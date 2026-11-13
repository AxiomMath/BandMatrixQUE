module

public import BlockBand.Endpoints.Response.TaggedConvexOrderStepDefs
public import BlockBand.Endpoints.Response.TaggedConvexOrderCore

/-!
# The tagged convex comparison from the bounded-variation one-step input

## Main results

* `tcs_backward_family_bv`: the coefficients of the backward family `l ↦ u(t_l, ·)`
  (`tcc_backward`, `t_l` antitone) have total variation `≤ |φ_i| e^{λ_i T}` (they are monotone).
* `tcs_comparisonAlongBV`: the analogue of `tcc_comparisonAlong` with the weaker
  `TcoOneStepAlongBV`. Since `tcc_comparisonAlong` takes `TcoOneStepAlong`, which the
  bounded-variation reading does not imply, it cannot be applied directly; the proof is the same
  (backward comparison, discretisation error, initial value), reusing `tcc_backward*`,
  `tcc_telescope_identity`, `tcc_integral_poly_eq_sum`, `tcc_abs_moment_le`, with the one extra
  check `hψbv` that the family `u_{l+1}` satisfies the bounded-variation hypothesis.
* `taggedConvexOrder_fixed_of_oneStepBV`: the fixed-energy statement.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- Total variation of a nonnegative antitone sequence on `[a, n)` is at most its value at `a`. -/
theorem tcs_sum_abs_sub_antitone (g : ℕ → ℝ) (hg : Antitone g) (hg0 : ∀ l, 0 ≤ g l) (a n : ℕ) :
    ∑ l ∈ Ico a n, |g (l + 1) - g l| ≤ g a := by
  rcases le_or_gt a n with h | h
  · have e : ∀ l ∈ Ico a n, |g (l + 1) - g l| = -(g (l + 1) - g l) := fun l _ =>
      abs_of_nonpos (sub_nonpos.2 (hg (Nat.le_succ l)))
    rw [sum_congr rfl e, sum_neg_distrib, tcc_sum_Ico_telescope g h]
    linarith [hg0 n]
  · rw [Ico_eq_empty_of_le h.le, sum_empty]
    exact hg0 a

/-- The backward family has coefficients of bounded variation: for `D₀ ≥ 0` and times `t_l`
antitone in `l` and `≤ T`, `Σ_{a≤l<n} |coeff_i u(t_{l+1}) - coeff_i u(t_l)| ≤ |φ_i| e^{λ_i T}`,
since `coeff_i u(t_l) = φ_i e^{λ_i t_l}` is monotone in `l`. -/
theorem tcs_backward_family_bv (D0 : ℝ) (hD0 : 0 ≤ D0) (φ : ℝ[X]) (t : ℕ → ℝ) (ht : Antitone t)
    (T : ℝ) (htT : ∀ l, t l ≤ T) (a n i : ℕ) :
    ∑ l ∈ Ico a n, |(tcc_backward D0 (t (l + 1)) φ).coeff i - (tcc_backward D0 (t l) φ).coeff i| ≤
      |φ.coeff i| * Real.exp (tcc_lam D0 i * T) := by
  set g : ℕ → ℝ := fun l => |φ.coeff i| * Real.exp (tcc_lam D0 i * t l)
  have hg : Antitone g := fun l l' hll' => by
    simp only [g]
    gcongr
    · exact tcc_lam_nonneg hD0 i
    · exact ht hll'
  have e : ∀ l ∈ Ico a n,
      |(tcc_backward D0 (t (l + 1)) φ).coeff i - (tcc_backward D0 (t l) φ).coeff i| =
        |g (l + 1) - g l| := fun l _ => by
    simp only [g, tcc_backward_coeff]
    rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_abs]
  rw [sum_congr rfl e]
  refine (tcs_sum_abs_sub_antitone g hg (fun l => by positivity) a n).trans ?_
  simp only [g]
  gcongr
  · exact tcc_lam_nonneg hD0 i
  · exact htT a

/-- The prelimit convex comparison along one tagged sequence from the bounded-variation one-step
input: `tcc_comparisonAlong` with `TcoOneStepAlongBV` in place of `TcoOneStepAlong`; the backward
family `u_{l+1}` is checked to have coefficients of total variation `≤ Σ_i|φ_i|e^{λ_iT'}`
(`tcs_backward_family_bv`). -/
theorem tcs_comparisonAlongBV {b : ℝ} {s τ E : ℝ} (σ : TcoTagSequence s τ E)
    (hD0 : 0 ≤ transportD0 b E) (hOne : TcoOneStepAlongBV b σ) (hM : TccMomentsAlong b σ)
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
  -- the backward family has coefficients of bounded variation
  have htt_anti : Antitone fun l => tt j (l + 1) := by
    intro l l' hll'
    simp only [tt]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast (show n - (l' + 1) ≤ n - (l + 1) by omega)) hWj.le
  have hψbv : ∀ i, ∑ l ∈ Ico (k + 1) n, |(ψ (l + 1)).coeff i - (ψ l).coeff i| ≤ Acoef := by
    intro i
    refine (tcs_backward_family_bv D0 hD0 φ _ htt_anti T' (fun l => httT _) (k + 1) n i).trans ?_
    by_cases hi : i ∈ range (N + 1)
    · exact single_le_sum (f := fun i => |a i| * Real.exp (lam i * T'))
        (fun i _ => by positivity) hi
    · have : φ.natDegree < i := by simp at hi; omega
      rw [coeff_eq_zero_of_natDegree_lt this, abs_zero, zero_mul]
      exact sum_nonneg fun i _ => by positivity
  have hOne' := hOnej ψ (fun l => tcc_backward_convex D0 _ hD0 (htt0 _) hφ) hψdeg hψcoef hψbv
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

/-- **`TcoTagComparisonCoreFixed` from the bounded-variation one-step input**: from
`FullSourceMomentsContract` (`tag`), `TagBirthValueContract` (`trace`, `square`) and
`TcoOneStepCoreFixedBV` (weaker than `TcoOneStepCoreFixed`).
-/
theorem tcoTagComparisonCoreFixed_of_BV (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) (hOneBV : TcoOneStepCoreFixedBV) :
    TcoTagComparisonCoreFixed := by
  intro b hb hb' E hE1 hE2 s τ hs σ hσ
  exact tcs_comparisonAlongBV σ (tco_transportD0_nonneg hb hE1 hE2)
    (hOneBV b hb hb' E hE1 hE2 s τ hs σ hσ) (tcc_momentsAlong_fixed hMom hb hb' hE1 hE2 σ hσ)
    (tcc_birthAlong_fixed hMom hBirth hb hb' hE1 hE2 hs σ hσ)

/-- **The tagged convex order theorem at the fixed energy `E`** from
`FullSourceMomentsEnergyUniformContract`, `FullSourceMomentsContract`, `TagBirthValueContract` and
`TcoOneStepCoreFixedBV`.
-/
theorem taggedConvexOrder_fixed_of_oneStepBV (hMomU : FullSourceMomentsEnergyUniformContract)
    (hMom : FullSourceMomentsContract) (hBirth : TagBirthValueContract)
    (hOneBV : TcoOneStepCoreFixedBV) : TaggedConvexOrderFixedStatement :=
  taggedConvexOrder_fixed hMomU (tcoTagComparisonCoreFixed_of_BV hMom hBirth hOneBV)

end BlockBand.Endpoints
