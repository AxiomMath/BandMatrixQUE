module

public import BlockBand.Endpoints.Response.TaggedConvexOrderStepComparison

/-!
# Abel summation: the bounded-variation one-step input from fixed monomial tests

## Main results

* `tcs_abel_identity`, `tcs_abel_bound`: summation by parts
  `Σ_{a≤l<n} c_l r_l = c_n R_n - Σ_{a≤l<n} (c_{l+1} - c_l) R_{l+1}`, `R_l = Σ_{a≤i<l} r_i`, hence
  `|Σ c_l r_l| ≤ (|c_n| + TV(c)) sup_{a≤l'≤n} |R_{l'}|`.
* `tcoOneStepCoreFixedBV_of_split`, `tcoTagComparisonCoreFixed_of_split`: the fixed-energy forms.

The hypothesis is `TcsOneStepSplitAlong` (see its docstring): the one-step error of the monomial
`X^m` splits as `ε_l(m) = d_l(m) + r_l(m)`, where the drift deficit `d_l` is linear in the test and
nonpositive on convex tests at every step `l`, and the partial sums `Σ_{k+1≤l<l'} r_l(m)` of the
remainder of each fixed monomial are uniformly small. In the intended application,
`d_l(m) = (D₀/2W) m(m-1) E E_h[X^{m-2}((v*Pv)(v*P'v) - X²)]` (nonpositive on convex tests by
`0 ≤ (v*Pv)(v*P'v) ≤ X²`), and `r_l(m)` is the remainder of the one-step tagged convex generator
expansion, with `Σ_l E|r_l| = o(1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal

/-- Summation by parts on `[a, n)`: `Σ c_l r_l = c_n R_n - Σ (c_{l+1} - c_l) R_{l+1}` with
`R_l = Σ_{a≤i<l} r_i`. -/
theorem tcs_abel_identity (c r : ℕ → ℝ) {a n : ℕ} (h : a ≤ n) :
    ∑ l ∈ Ico a n, c l * r l =
      c n * ∑ i ∈ Ico a n, r i -
        ∑ l ∈ Ico a n, (c (l + 1) - c l) * ∑ i ∈ Ico a (l + 1), r i := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn (fun l => c l * r l), ih,
      sum_Ico_succ_top hn (fun l => (c (l + 1) - c l) * ∑ i ∈ Ico a (l + 1), r i),
      sum_Ico_succ_top hn r]
    ring

/-- Abel bound: `|Σ_{a≤l<n} c_l r_l| ≤ A S + B S` for `|c_n| ≤ A`, total variation
`Σ_{a≤l<n} |c_{l+1} - c_l| ≤ B` and partial sums `|Σ_{a≤i<l'} r_i| ≤ S` for `a ≤ l' ≤ n`. -/
theorem tcs_abel_bound (c r : ℕ → ℝ) {a n : ℕ} (h : a ≤ n) {A B S : ℝ} (hc : |c n| ≤ A)
    (hbv : ∑ l ∈ Ico a n, |c (l + 1) - c l| ≤ B)
    (hS : ∀ l', a ≤ l' → l' ≤ n → |∑ i ∈ Ico a l', r i| ≤ S) :
    |∑ l ∈ Ico a n, c l * r l| ≤ A * S + B * S := by
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS a le_rfl h)
  rw [tcs_abel_identity c r h]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul hc (hS n h le_rfl) (abs_nonneg _) ((abs_nonneg _).trans hc)
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l ∈ Ico a n, |(c (l + 1) - c l) * ∑ i ∈ Ico a (l + 1), r i|
        ≤ ∑ l ∈ Ico a n, |c (l + 1) - c l| * S := by
          refine sum_le_sum fun l hl => ?_
          obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hS (l + 1) (by omega) (by omega)) (abs_nonneg _)
      _ = (∑ l ∈ Ico a n, |c (l + 1) - c l|) * S := by rw [sum_mul]
      _ ≤ B * S := mul_le_mul_of_nonneg_right hbv hS0

/-- The one-step error of the monomial `X^m` at path length `l` (birth index `k`, energy `e`,
width `W`): `ε_l(m) = E Z_{l+1}^m - E Z_l^m - W⁻¹λ_m E Z_l^m`, `λ_m = (D₀/2)m(m-1)`, i.e. the
summand of `TcoOneStepAlong` at the test `ψ_l = X^m`. -/
def tcs_monoErr (b e D0 : ℝ) (W l k m : ℕ) : ℝ :=
  ∫ x, x ^ m ∂tcc_law b e W (l + 1) k - ∫ x, x ^ m ∂tcc_law b e W l k -
    (W : ℝ)⁻¹ * (tcc_lam D0 m * ∫ x, x ^ m ∂tcc_law b e W l k)

/-- The split one-step error for fixed monomials along one tagged sequence.

For every degree `M` and `δ > 0`, eventually in `j` there are numbers `d_l(m)` (the drift
deficit) such that
* (sign) at every step `k+1 ≤ l < n` and for every polynomial `ψ` convex on `[0,∞)` with
  `deg ψ ≤ M`: `Σ_{m≤M} ψ_m d_l(m) ≤ 0`;
* (remainder) for every `m ≤ M` and every `k+1 ≤ l' ≤ n`:
  `|Σ_{k+1≤l<l'} (ε_l(m) - d_l(m))| ≤ δ`, with `ε_l(m) = tcs_monoErr` at `D₀ = D₀(E)`.

Intended content: `d_l(m) = (D₀/2W) m(m-1) E E_h[X^{m-2}((v*Pv)(v*P'v) - X²)]`, `v = Q_l^{1/2}h`,
`X = ‖v‖²`, so that `Σ_m ψ_m d_l(m) = (D₀/2W) E E_h[ψ''(X)((v*Pv)(v*P'v) - X²)] ≤ 0` for convex
`ψ` (`ψ'' ≥ 0` on `[0,∞)`, `P, P'` projections), and `ε_l(m) - d_l(m) = r_l(X^m)` is the
remainder of the one-step tagged convex generator expansion, with
`Σ_l E|r_l| ≤ C(W^{-1/2} + W⁻¹)`, so every partial sum is `o(1)`. -/
def TcsOneStepSplitAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ (M : ℕ) (δ : ℝ), 0 < δ → ∀ᶠ j in atTop, ∃ dfc : ℕ → ℕ → ℝ,
    (∀ l ∈ Ico (σ.k j + 1) (σ.n j), ∀ ψ : ℝ[X], ConvexOn ℝ (Set.Ici 0) (fun x => ψ.eval x) →
      ψ.natDegree ≤ M → ∑ m ∈ range (M + 1), ψ.coeff m * dfc l m ≤ 0) ∧
    ∀ m ≤ M, ∀ l', σ.k j + 1 ≤ l' → l' ≤ σ.n j →
      |∑ l ∈ Ico (σ.k j + 1) l',
        (tcs_monoErr b (σ.energy j) (transportD0 b E) (σ.W j) l (σ.k j) m - dfc l m)| ≤ δ

/-- `TcsOneStepSplitAlong` along every tagged sequence at the constant energy `E`. -/
def TcsOneStepSplitCoreFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, (∀ j, σ.energy j = E) → TcsOneStepSplitAlong b σ

/-- `TcoOneStepAlongBV` from the moments and the split monomial input (linearity in the test,
Abel summation of the remainder against the bounded-variation coefficients, the sign clause at
every step). -/
theorem tcs_oneStepAlongBV_of_split {b : ℝ} {s τ E : ℝ} {σ : TcoTagSequence s τ E}
    (hM : TccMomentsAlong b σ) (hS : TcsOneStepSplitAlong b σ) : TcoOneStepAlongBV b σ := by
  intro M A δ hδ
  set A' := |A|
  have hA' : 0 ≤ A' := abs_nonneg A
  set δ' := δ / (2 * (A' + 1) * ((M : ℝ) + 1))
  have hδ' : 0 < δ' := by positivity
  choose Cf hCf using hM
  have hmomE : ∀ᶠ j in atTop, ∀ m ∈ range (M + 1), ∀ l, σ.k j < l → l ≤ σ.n j →
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
        ENNReal.ofReal (Cf m) :=
    (eventually_all_finset _).2 fun m _ => hCf m
  filter_upwards [hmomE, hS M δ' hδ'] with j hmj hSj
  obtain ⟨dfc, hsign, hrem⟩ := hSj
  intro ψ hconv hdeg hcoef hbv
  set W := σ.W j
  set n := σ.n j
  set k := σ.k j
  set e := σ.energy j
  set D0 := transportD0 b E
  have hkn : k + 1 ≤ n := σ.tag_lt j
  have hint : ∀ l, k < l → l ≤ n → ∀ m ∈ range (M + 1),
      Integrable (fun x : ℝ => x ^ m) (tcc_law b e W l k) := by
    intro l h1 h2 m hm
    have := tcc_law_prob b e W l k
    exact (tco_integrable_of_lintegral_pow m (hmj m hm l h1 h2)).2
  set err : ℕ → ℕ → ℝ := fun l m => tcs_monoErr b e D0 W l k m
  have hexp : ∀ l ∈ Ico (k + 1) n,
      tcc_psi b e W (l + 1) k (ψ l) - tcc_psi b e W l k (ψ l) -
        (W : ℝ)⁻¹ * tcc_psi b e W l k (tcc_gen D0 (ψ l)) =
      ∑ m ∈ range (M + 1), (ψ l).coeff m * err l m := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
    rw [tcc_psi_eq, tcc_psi_eq, tcc_psi_eq,
      tcc_integral_poly_eq_sum (hint (l + 1) (by omega) (by omega)) (hdeg l),
      tcc_integral_poly_eq_sum (hint l (by omega) (by omega)) (hdeg l),
      tcc_integral_poly_eq_sum (hint l (by omega) (by omega))
        ((tcc_gen_natDegree_le D0 _).trans (hdeg l)), mul_sum, ← sum_sub_distrib,
      ← sum_sub_distrib]
    refine sum_congr rfl fun m _ => ?_
    simp only [err, tcs_monoErr, tcc_gen_coeff]
    ring
  rw [sum_congr rfl hexp]
  have hsplit : ∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (M + 1), (ψ l).coeff m * err l m =
      ∑ m ∈ range (M + 1), ∑ l ∈ Ico (k + 1) n, (ψ l).coeff m * (err l m - dfc l m) +
        ∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (M + 1), (ψ l).coeff m * dfc l m := by
    rw [sum_comm (s := range (M + 1)), ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [hsplit]
  have hneg : ∑ l ∈ Ico (k + 1) n, ∑ m ∈ range (M + 1), (ψ l).coeff m * dfc l m ≤ 0 :=
    sum_nonpos fun l hl => hsign l hl (ψ l) (hconv l) (hdeg l)
  have hm : ∀ m ∈ range (M + 1),
      |∑ l ∈ Ico (k + 1) n, (ψ l).coeff m * (err l m - dfc l m)| ≤ A' * δ' + A' * δ' := by
    intro m hm
    have hmM : m ≤ M := by simp at hm; omega
    exact tcs_abel_bound (fun l => (ψ l).coeff m) (fun l => err l m - dfc l m) hkn
      ((hcoef n m).trans (le_abs_self A)) ((hbv m).trans (le_abs_self A))
      (fun l' h1 h2 => hrem m hmM l' h1 h2)
  have hpos : ∑ m ∈ range (M + 1), ∑ l ∈ Ico (k + 1) n, (ψ l).coeff m * (err l m - dfc l m) ≤
      δ := by
    calc _ ≤ ∑ m ∈ range (M + 1), |∑ l ∈ Ico (k + 1) n, (ψ l).coeff m * (err l m - dfc l m)| :=
          sum_le_sum fun m _ => le_abs_self _
      _ ≤ ∑ m ∈ range (M + 1), (A' * δ' + A' * δ') := sum_le_sum hm
      _ = A' * δ / (A' + 1) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          simp only [δ']
          push_cast
          field_simp
          ring
      _ ≤ δ := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  linarith

/-- `TcoOneStepCoreFixedBV` from the `FullSourceMomentsContract` and the isolated
`TcsOneStepSplitCoreFixed`.
-/
theorem tcoOneStepCoreFixedBV_of_split (hMom : FullSourceMomentsContract)
    (hSplit : TcsOneStepSplitCoreFixed) : TcoOneStepCoreFixedBV :=
  fun b hb hb' E hE1 hE2 s τ hs σ hσ =>
    tcs_oneStepAlongBV_of_split (tcc_momentsAlong_fixed hMom hb hb' hE1 hE2 σ hσ)
      (hSplit b hb hb' E hE1 hE2 s τ hs σ hσ)

/-- `TcoTagComparisonCoreFixed` from the `FullSourceMomentsContract`,
`TagBirthValueContract` and the isolated `TcsOneStepSplitCoreFixed`.
-/
theorem tcoTagComparisonCoreFixed_of_split (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) (hSplit : TcsOneStepSplitCoreFixed) :
    TcoTagComparisonCoreFixed :=
  tcoTagComparisonCoreFixed_of_BV hMom hBirth (tcoOneStepCoreFixedBV_of_split hMom hSplit)

end BlockBand.Endpoints
