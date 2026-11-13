module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Scheme.Moments2
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Taylor scheme with integral bounds: pathwise error majorant)

On `IGood` (fixed `s ≤ t`, grid `n`), with the Taylor constants of `taylorRem_uniform`
(`C_T`, and `δ` for a given `ε > 0`) and any `c > 0`, the error
`E_n = (X_t - X_s) - T¹_n - ½ T²_n` satisfies
`|E_n| ≤ |Riemann_n - ∫𝓛φ| + (M₂ d + 2) ε S_n + (C_T/δ)(S_n²/(2c) + 2c m_n²) + κ W_n`,
with `S_n = Σ_k Σ_i (ΔN^i_k)²`, `m_n = max_k ‖ΔZ_k‖`, `W_n = Σ_k (ΔG_k)²` (`sqG`, the squared
control increments) and `κ = errConst' d M₂ R C_T δ ε`. Compared with the pointwise-bounded
scheme, the deterministic term `Δ · errConst` is replaced by the random `κ W_n`.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {C : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0} {ω : Ω}

/-- The constant multiplying `W_n` in the error majorant. -/
def errConst' (d : ℕ) (M₂ R C_T δ ε : ℝ) : ℝ :=
  (1 / 2) * M₂ * d ^ 2 * (1 / (2 * ε) + 1) + ε * (2 * d) + C_T / δ * (2 * R) * (2 * d)

/-- **Pathwise error majorant.** -/
theorem err_le' (hω : IGood K Z β α N B C s t ω) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) {R : ℝ} (hR : ∀ z ∈ K, ‖z‖ ≤ R) {M₂ : ℝ}
    (hM₂0 : 0 ≤ M₂) (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂)
    {C_T δ ε c : ℝ} (hCT : 0 ≤ C_T) (hδ : 0 < δ) (hε : 0 < ε) (hc : 0 < c)
    (hT1 : ∀ y ∈ K, ∀ z ∈ K, |taylorRem φ y z| ≤ C_T * ‖z - y‖ ^ 2)
    (hT2 : ∀ y ∈ K, ∀ z ∈ K, ‖z - y‖ ≤ δ → |taylorRem φ y z| ≤ ε * ‖z - y‖ ^ 2) (n : ℕ) :
    |schemeProc φ Z β α t ω - schemeProc φ Z β α s ω - transform1 φ Z N s t n ω -
        (1 / 2) * transform2 φ Z α N s t n ω| ≤
      |riemannSum φ Z β α s t n ω - ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| +
      (M₂ * d + 2) * ε * sqSum N s t n ω +
      C_T / δ * (sqSum N s t n ω ^ 2 / (2 * c) + 2 * c * meshMax Z s t n ω ^ 2) +
      sqG β α s t n ω * errConst' d M₂ R C_T δ ε := by
  have hdec := schemeProc_sub_eq' hω hU hKU hφ hst n
  set S := sqSum N s t n ω
  set m := meshMax Z s t n ω
  set W := sqG β α s t n ω
  have hW0 : 0 ≤ W := sqG_nonneg n
  have hγ0 : ∀ k, 0 ≤ incG β α s t n k ω := fun k => hω.incG_nonneg hst n k
  -- cross terms
  have hcr : |crossSum φ Z β N s t n ω| ≤
      M₂ * (2 * d * ε * S + d ^ 2 * (1 / (2 * ε) + 1) * W) := by
    unfold crossSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range (n + 1), |∑ i, ∑ j, dφ2 φ Z s t n i j k ω *
          (incN N s t n i k ω * incI β s t n j k ω + incI β s t n i k ω * incN N s t n j k ω +
            incI β s t n i k ω * incI β s t n j k ω)|
        ≤ ∑ k ∈ Finset.range (n + 1), M₂ * (2 * d * ε * ∑ i, incN N s t n i k ω ^ 2 +
            d ^ 2 * incG β α s t n k ω ^ 2 * (1 / (2 * ε) + 1)) :=
          Finset.sum_le_sum fun k _ => abs_cross_le _ hM₂0
            (fun i j => (abs_bilin_ev_le _ i j).trans (hM₂ _ (hω.1.1 _))) _ _ (hγ0 k)
            (fun i => hω.abs_incI_le' hst n i k) hε
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [sqSum, S, W, sqG, Finset.mul_sum]
          congr 1; congr 1
          refine Finset.sum_congr rfl fun k _ => by ring
  -- remainder terms
  have hm : ∀ k ∈ Finset.range (n + 1),
      ‖Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω‖ ≤ m := fun k hk =>
    Finset.le_sup' (fun k => ‖Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω‖) hk
  have hm2R : m ≤ 2 * R := by
    refine Finset.sup'_le _ _ fun k _ => (norm_sub_le _ _).trans ?_
    linarith [hR _ (hω.1.1 (grid s t n (k + 1))), hR _ (hω.1.1 (grid s t n k))]
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0 (by simp))
  have hsqZ : ∀ k, ‖Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω‖ ^ 2 ≤
      2 * ∑ i, incN N s t n i k ω ^ 2 + 2 * d * incG β α s t n k ω ^ 2 := by
    intro k
    refine (norm_sq_le_sum_sq _).trans ?_
    rw [incZ_eq hω.1 n k]
    simp only [Pi.add_apply]
    calc ∑ i, (incN N s t n i k ω + incI β s t n i k ω) ^ 2
        ≤ ∑ i, (2 * incN N s t n i k ω ^ 2 + 2 * incG β α s t n k ω ^ 2) :=
          Finset.sum_le_sum fun i _ => by
            have h1 := hω.abs_incI_le' hst n i k
            have h2 : incI β s t n i k ω ^ 2 ≤ incG β α s t n k ω ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
            nlinarith [sq_nonneg (incN N s t n i k ω - incI β s t n i k ω)]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
  have hrem : |remSum φ Z s t n ω| ≤ (ε + C_T / δ * m) * (2 * S + 2 * d * W) := by
    unfold remSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hq : 0 ≤ ε + C_T / δ * m := by positivity
    calc ∑ k ∈ Finset.range (n + 1),
          |taylorRem φ (Z (grid s t n k) ω) (Z (grid s t n (k + 1)) ω)|
        ≤ ∑ k ∈ Finset.range (n + 1), (ε + C_T / δ * m) *
            (2 * ∑ i, incN N s t n i k ω ^ 2 + 2 * d * incG β α s t n k ω ^ 2) :=
          Finset.sum_le_sum fun k hk => (abs_taylorRem_le_mix hCT hδ hε.le hT1 hT2 (hω.1.1 _)
            (hω.1.1 _) (hm k hk)).trans (mul_le_mul_of_nonneg_left (hsqZ k) hq)
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          rfl
  -- assemble
  have hE : schemeProc φ Z β α t ω - schemeProc φ Z β α s ω - transform1 φ Z N s t n ω -
      (1 / 2) * transform2 φ Z α N s t n ω =
      (riemannSum φ Z β α s t n ω - ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) +
      (1 / 2) * crossSum φ Z β N s t n ω + remSum φ Z s t n ω := by
    rw [hdec]; ring
  rw [hE]
  have hmS := mul_le_amgm hc m S
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCTd : 0 ≤ C_T / δ := div_nonneg hCT hδ.le
  have h3 := abs_add_le ((riemannSum φ Z β α s t n ω -
      ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) + (1 / 2) * crossSum φ Z β N s t n ω)
    (remSum φ Z s t n ω)
  have h4 := abs_add_le (riemannSum φ Z β α s t n ω -
      ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) ((1 / 2) * crossSum φ Z β N s t n ω)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h4
  have hrem' : |remSum φ Z s t n ω| ≤ 2 * ε * S +
      C_T / δ * (S ^ 2 / (2 * c) + 2 * c * m ^ 2) +
      W * (ε * (2 * d) + C_T / δ * (2 * R) * (2 * d)) := by
    refine hrem.trans ?_
    have hc0 : 0 ≤ 2 * d * W := by positivity
    have hmc : m * (2 * d * W) ≤ 2 * R * (2 * d * W) := mul_le_mul_of_nonneg_right hm2R hc0
    have : C_T / δ * (m * S) ≤ C_T / δ * (c * m ^ 2 + S ^ 2 / (4 * c)) :=
      mul_le_mul_of_nonneg_left hmS hCTd
    have : C_T / δ * (m * (2 * d * W)) ≤ C_T / δ * (2 * R * (2 * d * W)) :=
      mul_le_mul_of_nonneg_left hmc hCTd
    have e2 : S ^ 2 / (2 * c) = 2 * (S ^ 2 / (4 * c)) := by field_simp; ring
    rw [e2]
    nlinarith
  have hcr' : (1 / 2) * |crossSum φ Z β N s t n ω| ≤ M₂ * d * ε * S +
      W * ((1 / 2) * M₂ * d ^ 2 * (1 / (2 * ε) + 1)) := by
    nlinarith
  unfold errConst'
  nlinarith

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
