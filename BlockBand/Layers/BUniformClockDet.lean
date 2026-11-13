module

public import BlockBand.Layers.ComparisonBranch

/-!
# `b`-uniform deterministic comparison, separate ports

The strict contraction bound and the deterministic part of the layer-contraction lemma for
separate ports, with every constant replaced by an explicit bound uniform for `b ∈ [β, 1/2 - β]`
(using `b ≥ β`, `1 - 2b ≥ 2β`, `1 - b ≥ 1/2`). This is the deterministic ingredient of the
`b`-uniform clock-mean identity.

No measure is involved. Domain: `β ∈ (0,1/4)`, `κ > 0`, then the constants, then uniformly in
`b ∈ [β, 1/2 - β]`, `W ≥ 1`, Hermitian two-port `X`, `E ∈ bulkInterval κ` with
`d(X) = matchedDistance b E X ≤ d_*`. Norms: complex modulus, sup norm on `Fin 2 → ℂ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Layers

/-!
## 1. Row sum and margin, uniform in `b`
-/

/-- Row sum with the explicit constant `2/α₀` (adapted from `strictContraction_rowSum`): if `Im a ≤ -α₀`, then
`Σ_j |Q_ij| ≤ (1-b)⁻¹ + (2/α₀) d(X)` for `0 < b ≤ 1/2`. -/
theorem bu_rowSum {α₀ b E : ℝ} (hα₀ : 0 < α₀) (hb1 : b ≤ 1 / 2) (hE : |E| < 2)
    (haim : (matchedA E).im ≤ -α₀) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : X.IsHermitian) (i : Fin 2) :
    ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤
      (1 - b)⁻¹ + 2 / α₀ * matchedDistance b E X := by
  have hE4 : E ^ 2 ≤ 4 := by
    have h := abs_lt.mp hE
    nlinarith
  have hs : α₀ ≤ Real.sqrt (4 - E ^ 2) / 2 := by
    have := rowSum_im_matchedA E; linarith
  have h1b : 0 < 1 - b := by linarith
  have hs0 : 0 < Real.sqrt (4 - E ^ 2) := by linarith
  have hz : 0 < (boundaryZ b E).im := by rw [rowSum_im_boundaryZ hE4]; positivity
  refine (sum_norm_blockPairTrace_le_center X hX _ hz (matchedA E) i).trans ?_
  rw [rowSum_im_boundaryZ hE4, rowSum_im_matchedA]
  have hfirst : -(-Real.sqrt (4 - E ^ 2) / 2) / ((1 - b) * (Real.sqrt (4 - E ^ 2) / 2)) =
      (1 - b)⁻¹ := by
    field_simp
  rw [hfirst]
  gcongr
  have hd : ‖blockTrace ((boundaryZ b E • 1 - X)⁻¹) i - matchedA E‖ ≤ matchedDistance b E X := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hden : α₀ / 2 ≤ (1 - b) * (Real.sqrt (4 - E ^ 2) / 2) := by nlinarith
  calc ‖blockTrace ((boundaryZ b E • 1 - X)⁻¹) i - matchedA E‖ /
        ((1 - b) * (Real.sqrt (4 - E ^ 2) / 2))
      ≤ matchedDistance b E X / (α₀ / 2) :=
        div_le_div₀ ((norm_nonneg _).trans hd) hd (by positivity) hden
    _ = 2 / α₀ * matchedDistance b E X := by field_simp

/-- `|c + b²a²| ≤ (1-b)² - 2 min(β³κ, 1/4)` on `bulkInterval κ`, for `b ∈ [β, 1/2 - β]`
(from `norm_sq_contraction_le_of_mem_bulkInterval`). -/
theorem bu_contraction_le {β κ b E : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) (hE : E ∈ bulkInterval κ) :
    ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ≤
      (1 - b) ^ 2 - 2 * min (β ^ 3 * κ) (1 / 4) := by
  obtain ⟨hb0, hb1⟩ := hb
  have hsq := norm_sq_contraction_le_of_mem_bulkInterval (b := b) (by linarith) hκ.le hE
  set x := ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ with hx
  set g := min (β ^ 3 * κ) (1 / 4) with hg
  have hx0 : 0 ≤ x := norm_nonneg _
  have hgle : g ≤ β ^ 3 * κ := min_le_left _ _
  have hbb : β ^ 2 ≤ b ^ 2 := by nlinarith
  have h12 : 2 * β ≤ 1 - 2 * b := by linarith
  have hδ : 4 * g ≤ 2 * (1 - 2 * b) * b ^ 2 * κ := by
    have h1 : β ^ 3 * κ * 4 ≤ 2 * (1 - 2 * b) * b ^ 2 * κ := by
      have h2 : 2 * β * β ^ 2 ≤ (1 - 2 * b) * b ^ 2 :=
        mul_le_mul h12 hbb (by positivity) (by linarith)
      nlinarith
    linarith
  set A := (1 - b) ^ 2 with hA
  have hA1 : A ≤ 1 := by rw [hA]; nlinarith
  have hA0 : 0 ≤ A := sq_nonneg _
  have hxx : x ^ 2 ≤ A ^ 2 - 4 * g := by rw [hA]; nlinarith
  have hg0 : 0 ≤ g := le_min (by positivity) (by norm_num)
  have hxA : x ≤ A := by nlinarith
  -- `(A - x)(A + x) ≥ 4g` and `A + x ≤ 2`
  nlinarith

/-- **Uniform margin** (adapted from `strictContraction_margin`):
`β ∈ (0,1/4)`, `κ > 0` first; then `d_m > 0` and `g = min(β³κ, 1/4) > 0`; uniformly in
`b ∈ [β, 1/2 - β]`, `W`, Hermitian `X`, `E ∈ bulkInterval κ` with `d(X) ≤ d_m`:
`|c + b²a²| Σ_j |Q_ij| ≤ 1 - b - g`. -/
theorem bu_margin {β κ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) :
    ∃ dm g : ℝ, 0 < dm ∧ 0 < g ∧ g ≤ 1 / 4 ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dm → ∀ i : Fin 2,
        ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
          ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ ≤ 1 - b - g := by
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  set g := min (β ^ 3 * κ) (1 / 4) with hg
  have hg0 : 0 < g := lt_min (by positivity) (by norm_num)
  refine ⟨g * α₀ / 2, g, by positivity, hg0, min_le_right _ _, ?_⟩
  intro b hb W _ X hX E hE hd i
  obtain ⟨hEabs, -, haim⟩ := hbulk E hE
  have hb0 := hb.1
  have hb1 := hb.2
  have hrow := bu_rowSum hα₀ (b := b) (by linarith) hEabs haim X hX i
  have hx := bu_contraction_le hβ0 hκ hb hE
  set x := ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ with hxdef
  set S := ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) i j‖ with hS
  have hx0 : 0 ≤ x := norm_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have h1b : 0 < 1 - b := by linarith
  have hdg : 2 / α₀ * matchedDistance b E X ≤ g := by
    calc 2 / α₀ * matchedDistance b E X ≤ 2 / α₀ * (g * α₀ / 2) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = g := by field_simp
  have hx1 : x ≤ 1 := by nlinarith
  have hfrac : x * (1 - b)⁻¹ ≤ (1 - b) - 2 * g := by
    rw [← div_eq_mul_inv, div_le_iff₀ h1b]
    nlinarith
  calc x * S ≤ x * ((1 - b)⁻¹ + 2 / α₀ * matchedDistance b E X) :=
        mul_le_mul_of_nonneg_left hrow hx0
    _ = x * (1 - b)⁻¹ + x * (2 / α₀ * matchedDistance b E X) := by ring
    _ ≤ ((1 - b) - 2 * g) + 1 * g :=
        add_le_add hfrac (mul_le_mul hx1 hdg (by positivity) zero_le_one)
    _ ≤ 1 - b - g := by linarith

/-!
## 2. Existence of the comparison solution, uniform in `b`
-/

/-- **Separate-port comparison solution, uniform in `b`** (existence/sign/closeness part of
`cmp_twoPort_stable`, with the proof adapted): `β ∈ (0,1/4)`,
`κ > 0` first; then `d_* > 0`, `C ≥ 0`; uniformly in `b ∈ [β, 1/2-β]`, `W`, Hermitian `X`,
`E ∈ bulkInterval κ` with `d(X) ≤ d_*`: a solution `(m, u)` of `IsTwoPortSolution` with
`Im m_i, Im u_i < 0` and `|m_i - a| + |u_i - a| ≤ C d(X)`. Constants: `y₁ = α₀/4`,
`ρ = min(y₁, 1/4, g/(4K₁), g/4)`, `d_* = min(d_m, βρ/2)`, `C = 2/β`. -/
theorem bu_twoPort_exists {β κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1 / 4) (hκ : 0 < κ) :
    ∃ dstar C : ℝ, 0 < dstar ∧ 0 ≤ C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
      ∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
        (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
        (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ C * matchedDistance b E X) := by
  obtain ⟨α₀, hα₀, hα₀1, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨dm, g, hdm, hg0, hg4, hmargin⟩ := bu_margin hβ0 hκ
  obtain ⟨y₁, hy₁⟩ : ∃ x : ℝ, x = α₀ / 4 := ⟨_, rfl⟩
  have hy₁0 : 0 < y₁ := by rw [hy₁]; positivity
  have hy₁α : y₁ < α₀ := by rw [hy₁]; linarith
  obtain ⟨K₁, hK₁⟩ : ∃ x : ℝ, x = 2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3 := ⟨_, rfl⟩
  have hyi0 : 0 < y₁⁻¹ := inv_pos.mpr hy₁0
  have hK₁0 : 0 < K₁ := by
    have := pow_pos hyi0 2; have := pow_pos hyi0 3; rw [hK₁]; linarith
  obtain ⟨ρ, hρ⟩ : ∃ x : ℝ, x = min (min y₁ (1 / 4)) (min (g / (4 * K₁)) (g / 4)) :=
    ⟨_, rfl⟩
  have hρ0 : 0 < ρ := hρ ▸ lt_min (lt_min hy₁0 (by norm_num))
    (lt_min (div_pos hg0 (by linarith)) (by linarith))
  have hρy : ρ ≤ y₁ := hρ ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / 4 := hρ ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hρK' : ρ ≤ g / (4 * K₁) := hρ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hρK : ρ * K₁ ≤ g / 4 := by
    calc ρ * K₁ ≤ g / (4 * K₁) * K₁ := mul_le_mul_of_nonneg_right hρK' hK₁0.le
      _ = g / 4 := by field_simp
  refine ⟨min dm (β * ρ / 2), 2 / β, lt_min hdm (by positivity), by positivity, ?_⟩
  intro b hb W hW X hX E hE hd
  obtain ⟨hb0', hb1'⟩ := hb
  have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb0'
  have hb1 : b < 1 / 2 := by linarith
  obtain ⟨t', ht'⟩ : ∃ x : ℝ, x = 1 - b - g := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ x : ℝ, x = 1 - b - g / 2 := ⟨_, rfl⟩
  have h1t : 1 - t₁ = b + g / 2 := by rw [ht₁]; ring
  have h1t0 : 0 < 1 - t₁ := by rw [h1t]; linarith
  have h1tβ : β ≤ 1 - t₁ := by rw [h1t]; linarith
  have ht₁0 : 0 ≤ t₁ := by rw [ht₁]; linarith
  have ht₁1 : t₁ < 1 := by linarith
  have hcoef : t' + ρ * (2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3) ≤ t₁ := by
    rw [← hK₁, ht₁, ht']; linarith
  have hbρ : b * ρ ≤ 1 / 2 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hβ1' : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ≤ 1 := by
    have h := bu_contraction_le hβ0 hκ ⟨hb0', hb1'⟩ hE
    have hg' : 0 ≤ min (β ^ 3 * κ) (1 / 4) := le_min (by positivity) (by norm_num)
    nlinarith
  have hzq : ∀ w : ℂ, boundaryZ b E - (b : ℂ) * w = (matchedA E)⁻¹ - (b : ℂ) * (w - matchedA E) :=
    fun w => by unfold boundaryZ; ring
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hdρ : matchedDistance b E X ≤ (1 - t₁) * ρ / 2 := by
    have h1 : matchedDistance b E X ≤ β * ρ / 2 := hd.trans (min_le_right _ _)
    have h2 : β * ρ ≤ (1 - t₁) * ρ := mul_le_mul_of_nonneg_right h1tβ hρ0.le
    linarith
  have hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * matchedA E).im := by
    have : ((1 - (b : ℂ)) * matchedA E).im = (1 - b) * (matchedA E).im := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im]
      ring
    rw [this, hy₁]
    have := mul_le_mul_of_nonneg_left haim (show (0 : ℝ) ≤ 1 - b by linarith)
    nlinarith
  have hH : (cmpTopH E X).IsHermitian := cmpTopH_isHermitian E hX
  have hR := cmp_resolvent_eq (b := b) hEabs.le X
  have hmarg : ∀ i, ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
      ∑ j, ‖cmpPair (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E))
        (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E)) i j‖ ≤ t' := fun i => by
    have := hmargin b ⟨hb0', hb1'⟩ W hW X hX E hE (hd.trans (min_le_left _ _)) i
    rw [hR] at this
    simp only [← cmpPair_self] at this
    rw [ht']
    linarith
  have hRd : ∀ i, ‖blockTrace (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E)) i -
      matchedA E‖ ≤ matchedDistance b E X := fun i => by
    rw [← hR]; exact cmp_le_matchedDistance b E X i
  obtain ⟨ms, hfix, hDle⟩ := cmp_sep_exists (cmpTopH E X) hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁0 hzq
    hσ₀im rfl hβ1' hmarg hcoef ht₁0 ht₁1 hd0 (by nlinarith) hRd
  have hmsa : ∀ j, ‖ms j - matchedA E‖ ≤ matchedDistance b E X / (1 - t₁) := fun j =>
    (norm_le_pi_norm (ms - fun _ => matchedA E) j).trans hDle
  have hdt : matchedDistance b E X / (1 - t₁) ≤ ρ / 2 := by
    rw [div_le_iff₀ h1t0]; linarith
  have hms : ∀ j, ‖ms j - matchedA E‖ ≤ ρ := fun j => by linarith [hmsa j]
  have hport := fun w (hw : ‖w - matchedA E‖ ≤ ρ) => cmp_sep_port ha1 hb0.le hbρ (hzq w) hw
  have husa : ∀ j, ‖(boundaryZ b E - (b : ℂ) * ms j)⁻¹ - matchedA E‖ ≤
      2 * b * ‖ms j - matchedA E‖ :=
    fun j => (hport _ (hms j)).2.2.2.2
  refine ⟨ms, fun j => (boundaryZ b E - (b : ℂ) * ms j)⁻¹, fun i => ⟨?_, rfl⟩,
    fun i => ⟨?_, ?_⟩, fun i => ?_⟩
  · rw [cmp_twoPortTop_inv]; exact (hfix i).symm
  · have := Complex.im_le_norm (ms i - matchedA E)
    rw [Complex.sub_im] at this
    linarith [hms i]
  · have := Complex.im_le_norm ((boundaryZ b E - (b : ℂ) * ms i)⁻¹ - matchedA E)
    rw [Complex.sub_im] at this
    have h1 := husa i
    have h2 := mul_le_mul (show 2 * b ≤ 1 by linarith) (hms i) (norm_nonneg _) zero_le_one
    linarith
  · have h1 := husa i
    have h2 := hmsa i
    have h3 : (1 + 2 * b) * ‖ms i - matchedA E‖ ≤
        (1 + 2 * b) * (matchedDistance b E X / (1 - t₁)) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : (1 + 2 * b) * (matchedDistance b E X / (1 - t₁)) ≤
        2 / β * matchedDistance b E X := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hi : (1 - t₁)⁻¹ ≤ β⁻¹ := inv_anti₀ hβ0 h1tβ
      have h5 : (1 + 2 * b) * (matchedDistance b E X * (1 - t₁)⁻¹) ≤
          2 * (matchedDistance b E X * β⁻¹) := by
        apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hi hd0) (by positivity)
          (by norm_num)
      linarith
    calc ‖ms i - matchedA E‖ + ‖(boundaryZ b E - (b : ℂ) * ms i)⁻¹ - matchedA E‖
        ≤ (1 + 2 * b) * ‖ms i - matchedA E‖ := by linarith
      _ ≤ 2 / β * matchedDistance b E X := h3.trans h4

/-!
## 3. Uniform branch constants
-/

/-- Uniform lower bound for `cmpEps b ζ₀ y₀` on `b ∈ [β, 1/2 - β]`. -/
def buEpsL (β ζ₀ y₀ : ℝ) : ℝ :=
  β * ζ₀ / (4 + 2 / (2 * β * y₀)) ^ 2 / (2 / (2 * β * y₀) + 1 / ζ₀ + 2)

/-- Uniform lower bound for `cmpEta b ζ₀ y₀` on `b ∈ [β, 1/2 - β]`. -/
def buEtaL (β ζ₀ y₀ : ℝ) : ℝ :=
  min (min 1 (2 * β * y₀)) (min (y₀ / 2)
    (buEpsL β ζ₀ y₀ / (2 * (1 / y₀ + 1 / (2 * β * y₀)))))

/-- Uniform upper bound for `cmpBranchC b ζ₀ y₀` on `b ∈ [β, 1/2 - β]`. -/
def buBranchCU (β ζ₀ y₀ : ℝ) : ℝ :=
  (1 + ζ₀⁻¹ ^ 2) * (2 / (2 * β * y₀)) * (2 / buEpsL β ζ₀ y₀) *
    (1 / (2 * β * y₀) + 2 / y₀) + 1

theorem buEpsL_pos {β ζ₀ y₀ : ℝ} (hβ : 0 < β) (hζ₀ : 0 < ζ₀) (hy₀ : 0 < y₀) :
    0 < buEpsL β ζ₀ y₀ := by
  unfold buEpsL; positivity

theorem buEtaL_pos {β ζ₀ y₀ : ℝ} (hβ : 0 < β) (hζ₀ : 0 < ζ₀) (hy₀ : 0 < y₀) :
    0 < buEtaL β ζ₀ y₀ := by
  have := buEpsL_pos hβ hζ₀ hy₀
  unfold buEtaL
  exact lt_min (lt_min one_pos (by positivity)) (lt_min (by linarith) (by positivity))

theorem bu_epsL_le {β ζ₀ y₀ b : ℝ} (hβ : 0 < β) (hζ₀ : 0 < ζ₀) (hy₀ : 0 < y₀)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) : buEpsL β ζ₀ y₀ ≤ cmpEps b ζ₀ y₀ := by
  obtain ⟨hb0, hb1⟩ := hb
  have h1 : 2 * β * y₀ ≤ (1 - 2 * b) * y₀ := mul_le_mul_of_nonneg_right (by linarith) hy₀.le
  have h2 : 2 / ((1 - 2 * b) * y₀) ≤ 2 / (2 * β * y₀) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
  have hp : 0 < (1 - 2 * b) * y₀ := lt_of_lt_of_le (by positivity) h1
  have hbpos : 0 < b := by linarith
  unfold buEpsL cmpEps
  gcongr

theorem bu_etaL_le {β ζ₀ y₀ b : ℝ} (hβ : 0 < β) (hζ₀ : 0 < ζ₀) (hy₀ : 0 < y₀)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) : buEtaL β ζ₀ y₀ ≤ cmpEta b ζ₀ y₀ := by
  have he := bu_epsL_le hβ hζ₀ hy₀ hb
  have hepos := buEpsL_pos hβ hζ₀ hy₀
  obtain ⟨hb0, hb1⟩ := hb
  have h1 : 2 * β * y₀ ≤ (1 - 2 * b) * y₀ := mul_le_mul_of_nonneg_right (by linarith) hy₀.le
  have hp : 0 < (1 - 2 * b) * y₀ := lt_of_lt_of_le (by positivity) h1
  have h3 : b / ((1 - 2 * b) * y₀) ≤ 1 / (2 * β * y₀) :=
    div_le_div₀ (by norm_num) (by linarith) (by positivity) h1
  have hcpos : 0 < cmpEps b ζ₀ y₀ := lt_of_lt_of_le hepos he
  have hbpos : 0 < b := by linarith
  unfold buEtaL cmpEta
  gcongr

theorem bu_branchC_le {β ζ₀ y₀ b : ℝ} (hβ : 0 < β) (hζ₀ : 0 < ζ₀) (hy₀ : 0 < y₀)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) : cmpBranchC b ζ₀ y₀ ≤ buBranchCU β ζ₀ y₀ := by
  have he := bu_epsL_le hβ hζ₀ hy₀ hb
  have hepos := buEpsL_pos hβ hζ₀ hy₀
  obtain ⟨hb0, hb1⟩ := hb
  have h1 : 2 * β * y₀ ≤ (1 - 2 * b) * y₀ := mul_le_mul_of_nonneg_right (by linarith) hy₀.le
  have hp : 0 < (1 - 2 * b) * y₀ := lt_of_lt_of_le (by positivity) h1
  have hb' : 0 ≤ b := by linarith
  have h3 : 2 * b / ((1 - 2 * b) * y₀) ≤ 1 / (2 * β * y₀) :=
    div_le_div₀ (by norm_num) (by linarith) (by positivity) h1
  have h4 : 2 * b * ζ₀⁻¹ ^ 2 ≤ ζ₀⁻¹ ^ 2 := by
    have := sq_nonneg ζ₀⁻¹
    nlinarith
  have hcpos : 0 < cmpEps b ζ₀ y₀ := lt_of_lt_of_le hepos he
  unfold buBranchCU cmpBranchC
  gcongr

/-!
## 4. Separate-port comparison with the branch clause, uniform in `b`
-/

/-- The uniform top lower bound (`cmpTopLow` with
`b ↦ β`, `ζ₀ = 2βα₀`, `ζ_lo = v_R = α₀/2`). -/
def buTopLow (β K α₀ : ℝ) : ℝ :=
  β * (2 * β * α₀ / (3 + K) ^ 2 / 2) * (α₀ / 2) /
    (2 * (1 + (K + (2 * β * α₀)⁻¹ + 2) ^ 2 / (α₀ / 2) ^ 2))

/-- **Deterministic separate-port comparison with verifiable branch hypotheses, uniform in
`b`** (separate clause of `cmp_comparison_branch`, with
`cmp_comparison_deterministic`, inlined). `β ∈ (0,1/4)`,
`κ > 0`, `K ≥ 0` first; then `d_* > 0`, `C ≥ 0`, `η₀ > 0`, `C''`; uniformly in
`b ∈ [β, 1/2 - β]`, `W ≥ 1`, Hermitian `X`, `E ∈ bulkInterval κ` with `d(X) ≤ d_*`: the
separate-port comparison solution exists (negative imaginary parts, within `C d(X)` of `a`)
and every approximate solution with residuals `≤ η ≤ η₀`, `-Im m̄_i ≥ 0`, `|m̄_i| ≤ K` is within
`C'' η` of it. -/
theorem bu_sepComparison {β κ K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1 / 4) (hκ : 0 < κ)
    (hK : 0 ≤ K) :
    ∃ dstar C η₀ C'' : ℝ, 0 < dstar ∧ 0 ≤ C ∧ 0 < η₀ ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
        ∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
          (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
          (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ∀ (η : ℝ) (mb ub r r' : Fin 2 → ℂ), 0 ≤ η → η ≤ η₀ → ‖r‖ ≤ η → ‖r'‖ ≤ η →
            (∀ i, 0 ≤ -(mb i).im) → (∀ i, ‖mb i‖ ≤ K) →
            (∀ i, mb i = blockTrace (twoPortTop b E X mb ub)⁻¹ i + r i ∧
              ub i = (boundaryZ b E - (b : ℂ) * mb i)⁻¹ + r' i) →
            ∀ i, ‖mb i - m i‖ + ‖ub i - u i‖ ≤ C'' * η := by
  obtain ⟨α₀, hα₀, hα₀1, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨ds, Cs, hds, hCs, hex⟩ := bu_twoPort_exists hβ0 hβ1 hκ
  set ζ₀ := 2 * β * α₀ with hζ₀def
  have hζ₀0 : 0 < ζ₀ := by positivity
  set tl := buTopLow β K α₀ with htl
  have htl0 : 0 < tl := by rw [htl]; unfold buTopLow; positivity
  set Y := min (tl / 2) (α₀ / 2) with hYdef
  have hY0 : 0 < Y := lt_min (by linarith) (by linarith)
  have hKs : 0 < 2 * (Cs + 1) := by linarith
  have hw0 : 0 < ζ₀ / (3 + K) ^ 2 / 2 := by positivity
  refine ⟨min (min ds (α₀ / 2)) (α₀ / (2 * (Cs + 1))), Cs,
    min (min (buEtaL β ζ₀ Y) (ζ₀ / (3 + K) ^ 2 / 2)) (min 1 (tl / 2)), buBranchCU β ζ₀ Y,
    lt_min (lt_min hds (by linarith)) (div_pos hα₀ hKs), hCs,
    lt_min (lt_min (buEtaL_pos hβ0 hζ₀0 hY0) hw0) (lt_min one_pos (by linarith)), ?_⟩
  intro b hb W hW X hX E hE hd
  obtain ⟨hb0', hb1'⟩ := hb
  have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb0'
  have hb1 : b < 1 / 2 := by linarith
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hds' : matchedDistance b E X ≤ ds := hd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdα : matchedDistance b E X ≤ α₀ / 2 := hd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdC : matchedDistance b E X ≤ α₀ / (2 * (Cs + 1)) := hd.trans (min_le_right _ _)
  have hCd : (Cs + 1) * matchedDistance b E X ≤ α₀ / 2 := by
    rw [le_div_iff₀ hKs] at hdC
    linarith
  have hCsd : Cs * matchedDistance b E X ≤ α₀ / 2 := by nlinarith
  obtain ⟨m, u, hsol, him, hclose⟩ := hex b ⟨hb0', hb1'⟩ W hW X hX E hE hds'
  refine ⟨m, u, hsol, him, hclose, ?_⟩
  intro η mb ub r r' hη0 hη hr hr' hpos hKm happ i
  have hηa : η ≤ buEtaL β ζ₀ Y := hη.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηb : η ≤ ζ₀ / (3 + K) ^ 2 / 2 := hη.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηc : η ≤ 1 := hη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηd : η ≤ tl / 2 := hη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hH := cmpTopH_isHermitian E hX
  have hEabs' := hEabs.le
  have h1b : 0 < 1 - b := by linarith
  -- the reference shift `s₀ = (1 - b) a`
  have hs₀im : -((1 - (b : ℂ)) * matchedA E).im = (1 - b) * (-(matchedA E).im) := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im]
    ring
  have haim1 : -(matchedA E).im ≤ 1 :=
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans ha1.le)
  have hs₀lo : α₀ / 2 ≤ -((1 - (b : ℂ)) * matchedA E).im := by
    rw [hs₀im]
    have := mul_le_mul_of_nonneg_left (show α₀ ≤ -(matchedA E).im by linarith) h1b.le
    nlinarith
  have hs₀hi : -((1 - (b : ℂ)) * matchedA E).im ≤ 1 := by
    rw [hs₀im]
    have := mul_le_mul (show 1 - b ≤ 1 by linarith) haim1 (by linarith) zero_le_one
    linarith
  have hs₀n : ‖(1 - (b : ℂ)) * matchedA E‖ ≤ 1 := by
    rw [norm_mul, ha1, mul_one, show (1 - (b : ℂ)) = ((1 - b : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg h1b.le]
    linarith
  have hvR : ∀ i, α₀ / 2 ≤ -(blockTrace (cmpInv (cmpTopH E X)
      (fun _ => (1 - (b : ℂ)) * matchedA E)) i).im := fun i => by
    have h := cmp_le_matchedDistance b E X i
    rw [cmp_resolvent_eq hEabs' X] at h
    have := Complex.im_le_norm (blockTrace (cmpInv (cmpTopH E X)
      (fun _ => (1 - (b : ℂ)) * matchedA E)) i - matchedA E)
    rw [Complex.sub_im] at this
    linarith
  have hzs : ζ₀ ≤ (boundaryZ b E).im := by
    rw [boundaryZ_im hEabs', hζ₀def]
    have := mul_le_mul_of_nonneg_left haim h1b.le
    nlinarith
  have hzs3 := norm_boundaryZ_le hb0.le (by linarith) hEabs'
  -- lower bound on the approximate top means
  have hlow : ∀ j, Y ≤ -(mb j).im := fun j => by
    have h := (cmp_sep_lower (cmpTopH E X) hH hb0 hb1 hζ₀0 hzs hzs3 hK hηb hηc
      (by linarith : (0 : ℝ) < α₀ / 2) hs₀lo hs₀hi hs₀n hvR mb ub r r' happ hr hr' hpos
      hKm j).1
    have hge : tl ≤ b * (ζ₀ / (3 + K) ^ 2 / 2) * (α₀ / 2) /
        (2 * (1 + (K + ζ₀⁻¹ + 2) ^ 2 / (α₀ / 2) ^ 2)) := by
      rw [htl]; unfold buTopLow
      rw [hζ₀def]
      gcongr
    have := min_le_left (tl / 2) (α₀ / 2)
    linarith
  -- lower bound on the exact solution
  have hv : ∀ j, Y ≤ -(m j).im := fun j => by
    have h1 := hclose j
    have h2 := norm_nonneg (u j - matchedA E)
    have h3 := Complex.im_le_norm (m j - matchedA E)
    rw [Complex.sub_im] at h3
    have := min_le_right (tl / 2) (α₀ / 2)
    linarith
  have hηe : η ≤ cmpEta b ζ₀ Y := hηa.trans (bu_etaL_le hβ0 hζ₀0 hY0 ⟨hb0', hb1'⟩)
  have h := cmp_sep_branch (cmpTopH E X) hH hb0 hb1 hζ₀0 hzs hzs3 hY0 hη0 hηe m u hsol hv
    mb ub r r' happ hr hr' hlow i
  exact h.trans (mul_le_mul_of_nonneg_right (bu_branchC_le hβ0 hζ₀0 hY0 ⟨hb0', hb1'⟩) hη0)

end BlockBand.Layers
