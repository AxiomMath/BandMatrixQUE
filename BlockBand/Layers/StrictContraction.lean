module

public import BlockBand.Layers.MatchedScalar
public import BlockBand.Layers.ResolventRowSum

/-!
# The strict contraction of the linearized separate-port equations

The strict contraction bound (from the proof of the layer-contraction lemma), stated as
`StrictContractionContract`.

The linearized separate-port equations are `v = δ + (c + b²a²) Q v`, `w = b a² v`, with
`Q_ij = W⁻¹ Tr R_ij R_ji`, `R = (z_∂ - X)⁻¹`. From `|c + b²a²| ≤ r_κ < (1-b)²` on
`bulkInterval κ` (`MatchedScalar`) and `max_i Σ_j |Q_ij| ≤ (1-b)⁻¹ + C d(X)` (`ResolventRowSum`),
every solution has `max_i |w_i| ≤ q max_i |δ_i|` with an explicit `q < 1` on `d(X) ≤ d_*`.
Deterministic; uniform in `W` and the Hermitian two-port `X`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open BlockBand.Internal.Contracts.Layers

/-- Max-norm contraction for a two-component linear system: if `|v_i| ≤ Δ + β ρ_i max_j |v_j|`
with `β ρ_i ≤ t`, then `(1 - t) max_j |v_j| ≤ Δ`. -/
theorem max_le_of_linear_bound (v δ : Fin 2 → ℂ) (β t : ℝ) (ρ : Fin 2 → ℝ)
    (hβρ : ∀ i, β * ρ i ≤ t)
    (hv : ∀ i, ‖v i‖ ≤ ‖δ i‖ + β * ρ i * max ‖v 0‖ ‖v 1‖) :
    (1 - t) * max ‖v 0‖ ‖v 1‖ ≤ max ‖δ 0‖ ‖δ 1‖ := by
  set M := max ‖v 0‖ ‖v 1‖ with hM
  set Δ := max ‖δ 0‖ ‖δ 1‖ with hΔ
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (le_max_left _ _)
  have hi : ∀ i, ‖v i‖ ≤ Δ + t * M := by
    intro i
    have hδ : ‖δ i‖ ≤ Δ := by
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    have : β * ρ i * M ≤ t * M := mul_le_mul_of_nonneg_right (hβρ i) hM0
    linarith [hv i]
  have hMle : M ≤ Δ + t * M := max_le (hi 0) (hi 1)
  linarith

/-- **The strict contraction bound, linearized clause** (`StrictContractionContract.linearized`).
On `d(X) ≤ d_*` every solution of `v = δ + (c + b²a²) Q v` has `|b a² v_i| ≤ q max_j |δ_j|`,
with `q = b / (1 - t')`, `t' = (r_κ/(1-b) + 1 - b)/2 < 1 - b`, `r_κ = √((1-b)⁴ - 2cb²κ)`. -/
theorem strictContraction_linearized : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar q : ℝ, 0 < dstar ∧ q < 1 ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
      ∀ δ v : Fin 2 → ℂ,
        (∀ i, v i = δ i + (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2) *
          ∑ j, blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j * v j) →
        ∀ i, ‖(b : ℂ) * matchedA E ^ 2 * v i‖ ≤ q * max ‖δ 0‖ ‖δ 1‖ := by
  intro b hb0 hb1 κ hκ
  obtain ⟨C, hC⟩ := strictContraction_rowSum b hb0 hb1 κ hκ
  set C' := max C 0 with hC'
  set r := Real.sqrt ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrlt : r < (1 - b) ^ 2 := contractionRadius_lt hb0 hb1 hκ
  have h1b : 0 < 1 - b := by linarith
  set t := r / (1 - b) with ht
  have ht0 : 0 ≤ t := div_nonneg hr0 h1b.le
  have htlt : t < 1 - b := by
    rw [ht, div_lt_iff₀ h1b]; nlinarith
  set t' := (t + (1 - b)) / 2 with ht'
  have ht'lt : t' < 1 - b := by rw [ht']; linarith
  have ht'ge : t ≤ t' := by rw [ht']; linarith
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set dstar := ((1 - b) - t) / (2 * (r * C' + 1)) with hdstar
  have hden : 0 < 2 * (r * C' + 1) := by positivity
  have hdstar0 : 0 < dstar := div_pos (by linarith) hden
  have hgap : r * C' * dstar ≤ t' - t := by
    have h : r * C' * dstar = (r * C') / (r * C' + 1) * (((1 - b) - t) / 2) := by
      rw [hdstar]; field_simp
    have hfrac : (r * C') / (r * C' + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hpos : 0 ≤ ((1 - b) - t) / 2 := by linarith
    rw [h, ht']
    nlinarith
  refine ⟨dstar, b / (1 - t'), hdstar0, ?_, ?_⟩
  · rw [div_lt_one (by linarith)]; linarith
  intro W hW X hX E hE hd δ v hv i
  have hEabs : |E| ≤ 2 := by
    have := abs_le_of_mem_bulkInterval hE; linarith
  have hβ : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ≤ r :=
    norm_contraction_le_of_mem_bulkInterval hb1.le hκ.le hE
  set β := ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ with hβdef
  have hβ0 : 0 ≤ β := norm_nonneg _
  set ρ : Fin 2 → ℝ := fun i => ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖
    with hρ
  have hρ0 : ∀ i, 0 ≤ ρ i := fun i => Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hdist0 : 0 ≤ matchedDistance b E X := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρle : ∀ i, ρ i ≤ (1 - b)⁻¹ + C' * dstar := by
    intro i
    have h := hC W hW X hX E hE i
    have : C * matchedDistance b E X ≤ C' * dstar :=
      calc C * matchedDistance b E X ≤ C' * matchedDistance b E X :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hdist0
        _ ≤ C' * dstar := mul_le_mul_of_nonneg_left hd hC'0
    simp only [hρ]; linarith
  have hβρ : ∀ i, β * ρ i ≤ t' := by
    intro i
    calc β * ρ i ≤ r * ((1 - b)⁻¹ + C' * dstar) :=
          mul_le_mul hβ (hρle i) (hρ0 i) hr0
      _ = t + r * C' * dstar := by rw [ht]; field_simp
      _ ≤ t' := by linarith
  have hvb : ∀ i, ‖v i‖ ≤ ‖δ i‖ + β * ρ i * max ‖v 0‖ ‖v 1‖ := by
    intro i
    have hsum : ‖∑ j, blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j * v j‖ ≤
        ρ i * max ‖v 0‖ ‖v 1‖ := by
      calc ‖∑ j, blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j * v j‖
          ≤ ∑ j, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j * v j‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ * max ‖v 0‖ ‖v 1‖ := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          fin_cases j
          · exact le_max_left _ _
          · exact le_max_right _ _
        _ = ρ i * max ‖v 0‖ ‖v 1‖ := by rw [hρ, Finset.sum_mul]
    calc ‖v i‖ = ‖δ i + (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2) *
          ∑ j, blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j * v j‖ := by rw [← hv i]
      _ ≤ ‖δ i‖ + β * ‖∑ j, blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j * v j‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖δ i‖ + β * (ρ i * max ‖v 0‖ ‖v 1‖) := by gcongr
      _ = ‖δ i‖ + β * ρ i * max ‖v 0‖ ‖v 1‖ := by ring
  have ht'1 : t' < 1 := by linarith
  have hmax := max_le_of_linear_bound v δ β t' ρ hβρ hvb
  have h1t : 0 < 1 - t' := by linarith
  have hvi : ‖v i‖ ≤ max ‖v 0‖ ‖v 1‖ := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hMbound : max ‖v 0‖ ‖v 1‖ ≤ max ‖δ 0‖ ‖δ 1‖ / (1 - t') := by
    rw [le_div_iff₀ h1t]; linarith
  have hnorm : ‖(b : ℂ) * matchedA E ^ 2 * v i‖ = b * ‖v i‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_matchedA hEabs, one_pow, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hb0.le]
  rw [hnorm]
  calc b * ‖v i‖ ≤ b * (max ‖δ 0‖ ‖δ 1‖ / (1 - t')) :=
        mul_le_mul_of_nonneg_left (hvi.trans hMbound) hb0.le
    _ = b / (1 - t') * max ‖δ 0‖ ‖δ 1‖ := by ring

/-- **The strict contraction bound, margin clause** (`StrictContractionContract.margin`).
`b, κ` first, then `d_* > 0` and `t = (r_κ/(1-b) + 1 - b)/2 < 1 - b`,
`r_κ = √((1-b)⁴ - 2cb²κ)`; for every `W ≥ 1`, Hermitian two-port `X` with `d(X) ≤ d_*` and
`E ∈ bulkInterval κ`: `|c + b²a²| Σ_j |Q_ij| ≤ t` for each `i`. Deterministic. -/
theorem strictContraction_margin : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar t : ℝ, 0 < dstar ∧ t < 1 - b ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar → ∀ i : Fin 2,
        ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
          ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤ t := by
  intro b hb0 hb1 κ hκ
  obtain ⟨C, hC⟩ := strictContraction_rowSum b hb0 hb1 κ hκ
  set C' := max C 0 with hC'
  set r := Real.sqrt ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrlt : r < (1 - b) ^ 2 := contractionRadius_lt hb0 hb1 hκ
  have h1b : 0 < 1 - b := by linarith
  set t := r / (1 - b) with ht
  have htlt : t < 1 - b := by
    rw [ht, div_lt_iff₀ h1b]; nlinarith
  set t' := (t + (1 - b)) / 2 with ht'
  have ht'lt : t' < 1 - b := by rw [ht']; linarith
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set dstar := ((1 - b) - t) / (2 * (r * C' + 1)) with hdstar
  have hden : 0 < 2 * (r * C' + 1) := by positivity
  have hdstar0 : 0 < dstar := div_pos (by linarith) hden
  have hgap : r * C' * dstar ≤ t' - t := by
    have h : r * C' * dstar = (r * C') / (r * C' + 1) * (((1 - b) - t) / 2) := by
      rw [hdstar]; field_simp
    have hfrac : (r * C') / (r * C' + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hpos : 0 ≤ ((1 - b) - t) / 2 := by linarith
    rw [h, ht']
    nlinarith
  refine ⟨dstar, t', hdstar0, ht'lt, ?_⟩
  intro W hW X hX E hE hd i
  have hβ : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ≤ r :=
    norm_contraction_le_of_mem_bulkInterval hb1.le hκ.le hE
  have hρ0 : 0 ≤ ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hdist0 : 0 ≤ matchedDistance b E X := le_trans (norm_nonneg _) (le_max_left _ _)
  have hρle : ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤
      (1 - b)⁻¹ + C' * dstar := by
    have h := hC W hW X hX E hE i
    have : C * matchedDistance b E X ≤ C' * dstar :=
      calc C * matchedDistance b E X ≤ C' * matchedDistance b E X :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hdist0
        _ ≤ C' * dstar := mul_le_mul_of_nonneg_left hd hC'0
    linarith
  calc ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
        ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖
      ≤ r * ((1 - b)⁻¹ + C' * dstar) := mul_le_mul hβ hρle hρ0 hr0
    _ = t + r * C' * dstar := by rw [ht]; field_simp
    _ ≤ t' := by linarith

/-- **`StrictContractionContract`** (the strict contraction bound): all
four clauses (`scalar`, `rowSum`, `linearized`, `margin`). Deterministic; constants depend
only on `b` and the bulk margin `κ`. -/
theorem strictContraction_holds : StrictContractionContract :=
  ⟨strictContraction_scalar, strictContraction_rowSum, strictContraction_linearized,
    strictContraction_margin⟩

end BlockBand.Layers
