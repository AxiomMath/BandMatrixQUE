module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Moments
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: pathwise error majorant

On `GoodPt` (fixed `s ≤ t`, grid `n`, mesh `Δ`), with the Taylor constants of
`taylorRem_uniform` (`C_T`, and `δ` for a given `ε > 0`) and any `c > 0`, the error
`E_n = (X_t - X_s) - T¹_n - ½ T²_n = (Riemann_n - ∫𝓛φ) + ½ Cross_n + Rem_n` satisfies
`|E_n| ≤ |Riemann_n - ∫𝓛φ| + (M₂ d + 2) ε S_n + (C_T/δ) (S_n²/(2c) + 2c m_n²) + κ Δ`,
where `S_n = Σ_k Σ_i (ΔN^i_k)²`, `m_n = max_k ‖ΔZ_k‖` and `κ` is an explicit constant.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ}

/-- `γ |x| ≤ ε x² + γ²/(4ε)`. -/
theorem mul_abs_le_amgm {γ ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    γ * |x| ≤ ε * x ^ 2 + γ ^ 2 / (4 * ε) := by
  rw [← sq_abs x, ← sub_nonneg]
  have key : ε * |x| ^ 2 + γ ^ 2 / (4 * ε) - γ * |x| = (2 * ε * |x| - γ) ^ 2 / (4 * ε) := by
    field_simp; ring
  rw [key]; positivity

/-- `m S ≤ c m² + S²/(4c)`. -/
theorem mul_le_amgm {c : ℝ} (hc : 0 < c) (m S : ℝ) : m * S ≤ c * m ^ 2 + S ^ 2 / (4 * c) := by
  rw [← sub_nonneg]
  have key : c * m ^ 2 + S ^ 2 / (4 * c) - m * S = (2 * c * m - S) ^ 2 / (4 * c) := by
    field_simp; ring
  rw [key]; positivity

/-- Deterministic bound for the cross terms of one cell. -/
theorem abs_cross_le (D2 : Fin d → Fin d → ℝ) {M₂ : ℝ} (hM : 0 ≤ M₂)
    (hD : ∀ i j, |D2 i j| ≤ M₂) (a c : Fin d → ℝ) {γ : ℝ} (hγ : 0 ≤ γ) (hc : ∀ i, |c i| ≤ γ)
    {ε : ℝ} (hε : 0 < ε) :
    |∑ i, ∑ j, D2 i j * (a i * c j + c i * a j + c i * c j)| ≤
      M₂ * (2 * d * ε * ∑ i, a i ^ 2 + d ^ 2 * γ ^ 2 * (1 / (2 * ε) + 1)) := by
  have step : ∀ i j, |D2 i j * (a i * c j + c i * a j + c i * c j)| ≤
      M₂ * (γ * |a i| + γ * |a j| + γ ^ 2) := by
    intro i j
    rw [abs_mul]
    refine mul_le_mul (hD i j) ?_ (abs_nonneg _) hM
    have h1 : |a i * c j| ≤ γ * |a i| := by
      rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hc j) (abs_nonneg _)
    have h2 : |c i * a j| ≤ γ * |a j| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)
    have h3 : |c i * c j| ≤ γ ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul (hc i) (hc j) (abs_nonneg _) hγ
    calc |a i * c j + c i * a j + c i * c j| ≤ |a i * c j + c i * a j| + |c i * c j| :=
          abs_add_le _ _
      _ ≤ |a i * c j| + |c i * a j| + |c i * c j| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  have hsum : ∑ i, |a i| * γ ≤ ε * ∑ i, a i ^ 2 + d * (γ ^ 2 / (4 * ε)) := by
    rw [Finset.mul_sum]
    calc ∑ i, |a i| * γ ≤ ∑ i, (ε * a i ^ 2 + γ ^ 2 / (4 * ε)) :=
          Finset.sum_le_sum fun i _ => by rw [mul_comm]; exact mul_abs_le_amgm hε (a i)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hs : (∑ x, γ * |a x|) = γ * ∑ x, |a x| := (Finset.mul_sum _ _ _).symm
  calc |∑ i, ∑ j, D2 i j * (a i * c j + c i * a j + c i * c j)|
      ≤ ∑ i, ∑ j, M₂ * (γ * |a i| + γ * |a j| + γ ^ 2) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => step i j))
    _ = M₂ * (2 * d * (∑ i, |a i| * γ) + d ^ 2 * γ ^ 2) := by
        have e1 : ∀ i, ∑ j, M₂ * (γ * |a i| + γ * |a j| + γ ^ 2) =
            M₂ * (d * (γ * |a i|) + γ * ∑ j, |a j| + d * γ ^ 2) := by
          intro i
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs]
          ring
        rw [Finset.sum_congr rfl fun i _ => e1 i, ← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        have e : (d : ℝ) ^ 2 * γ ^ 2 * (1 / (2 * ε) + 1) =
            2 * d * (d * (γ ^ 2 / (4 * ε))) + d ^ 2 * γ ^ 2 := by
          field_simp; ring
        rw [e]
        nlinarith [hsum]

/-- Taylor remainder bound combining the global and the local estimate. -/
theorem abs_taylorRem_le_mix {φ : (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)} {C_T δ ε : ℝ}
    (hCT : 0 ≤ C_T) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hT1 : ∀ y ∈ K, ∀ z ∈ K, |taylorRem φ y z| ≤ C_T * ‖z - y‖ ^ 2)
    (hT2 : ∀ y ∈ K, ∀ z ∈ K, ‖z - y‖ ≤ δ → |taylorRem φ y z| ≤ ε * ‖z - y‖ ^ 2)
    {y z : Fin d → ℝ} (hy : y ∈ K) (hz : z ∈ K) {m : ℝ} (hm : ‖z - y‖ ≤ m) :
    |taylorRem φ y z| ≤ (ε + C_T / δ * m) * ‖z - y‖ ^ 2 := by
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
  have hq : 0 ≤ C_T / δ * m := by positivity
  by_cases h : ‖z - y‖ ≤ δ
  · refine (hT2 y hy z hz h).trans ?_
    nlinarith [sq_nonneg ‖z - y‖]
  · push Not at h
    refine (hT1 y hy z hz).trans ?_
    have h1 : C_T ≤ C_T / δ * m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left (h.le.trans hm) hCT
    nlinarith [sq_nonneg ‖z - y‖]

/-- Largest increment norm of `Z` over the cells of the grid. -/
def meshMax (Z : ℝ≥0 → Ω → Fin d → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩
    fun k => ‖Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω‖

/-- The constant multiplying the mesh in the error majorant. -/
def errConst (d : ℕ) (M₂ Cβ R C_T δ ε : ℝ) (s t : ℝ≥0) : ℝ :=
  (1 / 2) * M₂ * d ^ 2 * Cβ ^ 2 * (t - s : ℝ) * (1 / (2 * ε) + 1) +
    ε * (2 * d * Cβ ^ 2 * (t - s : ℝ)) + C_T / δ * (2 * R) * (2 * d * Cβ ^ 2 * (t - s : ℝ))

variable {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {Cβ Cα : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0} {ω : Ω}

/-- **Pathwise error majorant.** -/
theorem err_le (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    (hα : ∀ t ω i j, |α t ω i j| ≤ Cα) (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U)
    (hst : s ≤ t) {R : ℝ} (hR : ∀ z ∈ K, ‖z‖ ≤ R) {M₂ : ℝ} (hM₂0 : 0 ≤ M₂)
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) (hCβ : 0 ≤ Cβ)
    {C_T δ ε c : ℝ} (hCT : 0 ≤ C_T) (hδ : 0 < δ) (hε : 0 < ε) (hc : 0 < c)
    (hT1 : ∀ y ∈ K, ∀ z ∈ K, |taylorRem φ y z| ≤ C_T * ‖z - y‖ ^ 2)
    (hT2 : ∀ y ∈ K, ∀ z ∈ K, ‖z - y‖ ≤ δ → |taylorRem φ y z| ≤ ε * ‖z - y‖ ^ 2) (n : ℕ) :
    |schemeProc φ Z β α t ω - schemeProc φ Z β α s ω - transform1 φ Z N s t n ω -
        (1 / 2) * transform2 φ Z α N s t n ω| ≤
      |riemannSum φ Z β α s t n ω - ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| +
      (M₂ * d + 2) * ε * sqSum N s t n ω +
      C_T / δ * (sqSum N s t n ω ^ 2 / (2 * c) + 2 * c * meshMax Z s t n ω ^ 2) +
      ((t - s : ℝ) / (n + 1)) * errConst d M₂ Cβ R C_T δ ε s t := by
  set Δ : ℝ := (t - s : ℝ) / (n + 1) with hΔ
  set γ : ℝ := Cβ * Δ with hγ
  have hts : (0 : ℝ) ≤ t - s := by
    have : (s : ℝ) ≤ t := by exact_mod_cast hst
    linarith
  have hΔ0 : 0 ≤ Δ := div_nonneg hts (by positivity)
  have hγ0 : 0 ≤ γ := mul_nonneg hCβ hΔ0
  have hnΔ : ((n : ℝ) + 1) * Δ = t - s := by rw [hΔ]; field_simp
  have hdec := schemeProc_sub_eq hω hβ hα hU hKU hφ hst n
  set S := sqSum N s t n ω
  set m := meshMax Z s t n ω
  -- cross terms
  have hcr : |crossSum φ Z β N s t n ω| ≤
      M₂ * (2 * d * ε * S + (n + 1) * (d ^ 2 * γ ^ 2 * (1 / (2 * ε) + 1))) := by
    unfold crossSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range (n + 1), |∑ i, ∑ j, dφ2 φ Z s t n i j k ω *
          (incN N s t n i k ω * incI β s t n j k ω + incI β s t n i k ω * incN N s t n j k ω +
            incI β s t n i k ω * incI β s t n j k ω)|
        ≤ ∑ k ∈ Finset.range (n + 1), M₂ * (2 * d * ε * ∑ i, incN N s t n i k ω ^ 2 +
            d ^ 2 * γ ^ 2 * (1 / (2 * ε) + 1)) :=
          Finset.sum_le_sum fun k _ => abs_cross_le _ hM₂0
            (fun i j => (abs_bilin_ev_le _ i j).trans (hM₂ _ (hω.1 _))) _ _ hγ0
            (fun i => abs_incI_le hω hβ hst n i k) hε
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [sqSum, S]
  -- remainder terms
  have hm : ∀ k ∈ Finset.range (n + 1),
      ‖Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω‖ ≤ m := fun k hk =>
    Finset.le_sup' (fun k => ‖Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω‖) hk
  have hm2R : m ≤ 2 * R := by
    refine Finset.sup'_le _ _ fun k _ => (norm_sub_le _ _).trans ?_
    linarith [hR _ (hω.1 (grid s t n (k + 1))), hR _ (hω.1 (grid s t n k))]
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0 (by simp))
  have hsqZ : ∀ k, ‖Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω‖ ^ 2 ≤
      2 * ∑ i, incN N s t n i k ω ^ 2 + 2 * d * γ ^ 2 := by
    intro k
    refine (norm_sq_le_sum_sq _).trans ?_
    rw [incZ_eq hω n k]
    simp only [Pi.add_apply]
    calc ∑ i, (incN N s t n i k ω + incI β s t n i k ω) ^ 2
        ≤ ∑ i, (2 * incN N s t n i k ω ^ 2 + 2 * γ ^ 2) := Finset.sum_le_sum fun i _ => by
          have h1 := abs_incI_le hω hβ hst n i k
          have h2 : incI β s t n i k ω ^ 2 ≤ γ ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          nlinarith [sq_nonneg (incN N s t n i k ω - incI β s t n i k ω)]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
  have hrem : |remSum φ Z s t n ω| ≤ (ε + C_T / δ * m) * (2 * S + (n + 1) * (2 * d * γ ^ 2)) := by
    unfold remSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hq : 0 ≤ ε + C_T / δ * m := by positivity
    calc ∑ k ∈ Finset.range (n + 1),
          |taylorRem φ (Z (grid s t n k) ω) (Z (grid s t n (k + 1)) ω)|
        ≤ ∑ k ∈ Finset.range (n + 1), (ε + C_T / δ * m) *
            (2 * ∑ i, incN N s t n i k ω ^ 2 + 2 * d * γ ^ 2) :=
          Finset.sum_le_sum fun k hk => (abs_taylorRem_le_mix hCT hδ hε.le hT1 hT2 (hω.1 _)
            (hω.1 _) (hm k hk)).trans (mul_le_mul_of_nonneg_left (hsqZ k) hq)
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [sqSum, S]
  -- assemble
  have hE : schemeProc φ Z β α t ω - schemeProc φ Z β α s ω - transform1 φ Z N s t n ω -
      (1 / 2) * transform2 φ Z α N s t n ω =
      (riemannSum φ Z β α s t n ω - ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) +
      (1 / 2) * crossSum φ Z β N s t n ω + remSum φ Z s t n ω := by
    rw [hdec]; ring
  rw [hE]
  have hγ2 : ((n : ℝ) + 1) * γ ^ 2 = Cβ ^ 2 * Δ * (t - s) := by
    rw [hγ, ← hnΔ]; ring
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
      Δ * (ε * (2 * d * Cβ ^ 2 * (t - s : ℝ)) + C_T / δ * (2 * R) * (2 * d * Cβ ^ 2 * (t - s))) := by
    refine hrem.trans ?_
    have e : (n + 1 : ℝ) * (2 * d * γ ^ 2) = Δ * (2 * d * Cβ ^ 2 * (t - s)) := by
      rw [show (n + 1 : ℝ) * (2 * d * γ ^ 2) = 2 * d * ((n + 1) * γ ^ 2) by ring, hγ2]; ring
    rw [e]
    have hc0 : 0 ≤ Δ * (2 * d * Cβ ^ 2 * (t - s : ℝ)) := by positivity
    have hmc : m * (Δ * (2 * d * Cβ ^ 2 * (t - s : ℝ))) ≤
        2 * R * (Δ * (2 * d * Cβ ^ 2 * (t - s : ℝ))) := mul_le_mul_of_nonneg_right hm2R hc0
    have : C_T / δ * (m * S) ≤ C_T / δ * (c * m ^ 2 + S ^ 2 / (4 * c)) :=
      mul_le_mul_of_nonneg_left hmS hCTd
    have : C_T / δ * (m * (Δ * (2 * d * Cβ ^ 2 * (t - s : ℝ)))) ≤
        C_T / δ * (2 * R * (Δ * (2 * d * Cβ ^ 2 * (t - s : ℝ)))) :=
      mul_le_mul_of_nonneg_left hmc hCTd
    have e2 : S ^ 2 / (2 * c) = 2 * (S ^ 2 / (4 * c)) := by field_simp; ring
    rw [e2]
    linarith
  have hcr' : (1 / 2) * |crossSum φ Z β N s t n ω| ≤ M₂ * d * ε * S +
      Δ * ((1 / 2) * M₂ * d ^ 2 * Cβ ^ 2 * (t - s : ℝ) * (1 / (2 * ε) + 1)) := by
    have e : (n + 1 : ℝ) * (d ^ 2 * γ ^ 2 * (1 / (2 * ε) + 1)) =
        d ^ 2 * ((n + 1) * γ ^ 2) * (1 / (2 * ε) + 1) := by ring
    rw [e, hγ2] at hcr
    linarith
  unfold errConst
  linarith

end BlockBand.SourceProcess.Stochastic.Semimartingale
