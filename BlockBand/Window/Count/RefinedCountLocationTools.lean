module

public import BlockBand.Window.Count.Statement
public import BlockBand.Window.Transfer.Semicircle
public import BlockBand.RankLocation.OrderedCountInversion
public import BlockBand.Model.Construction.SpectralPhysical

/-!
# The refined count, location clause: deterministic tools

Counting identities for Hermitian matrices, semicircle bounds in the bulk, and the multiscale real
inequality used in the location clause.

* `negativeCount_sub_smul_eq_countBelow` — for Hermitian `H` on any finite index type and
  every real `x`, `N_-(H - x) = #{i : λ_i(H) < x}` with the increasing enumeration
  (multiplicities retained), via the characteristic polynomial.
* `physicalCount_eq_countBelow`, `physicalOrderedEigenvalue_eq` — the physical versions
  (`N_H(x)`, `λ_α`, zero-based `α`) on Hermitian `H`.
* `semicircleDensity_ge` — `ρ_sc ≥ √(2δ)/(2π)` on `bulkInterval δ`, `0 < δ ≤ 2`.
* `semicircleCDF_sub_ge` — `F_sc(x) - F_sc(y) ≥ c (x - y)` for `y ≤ x` in `bulkInterval δ`.
* `classicalLocation_mem_bulk` — every `ϑ`-bulk rank has `e_α ∈ bulkInterval (πϑ/2)`.
* `abs_le_multiscale` — the real inequality behind the dyadic-free tail sum.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory Polynomial
open BlockBand.Model.Construction BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers
open BlockBand.RankLocation BlockBand.Foundations.Spectral

theorem isHermitian_sub_real_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (x : ℝ) :
    (H - (x : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  refine hH.sub ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- `N_-(M) = #{roots of the characteristic polynomial with negative real part}`
for Hermitian `M`. -/
theorem negativeCount_eq_card_roots {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    negativeCount M = Multiset.card ((M.charpoly.roots.map Complex.re).filter (· < 0)) := by
  classical
  unfold negativeCount
  simp only [hM, ↓reduceDIte]
  rw [hM.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  have : (Complex.re ∘ RCLike.ofReal ∘ hM.eigenvalues) = hM.eigenvalues := by
    funext k; simp
  rw [this, Multiset.filter_map, Multiset.card_map]
  rfl

/-- For Hermitian `H` and real `x`: `N_-(H - x) = #{i : λ_i(H) < x}` (increasing order,
multiplicities retained). -/
theorem negativeCount_sub_smul_eq_countBelow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (x : ℝ) :
    negativeCount (H - (x : ℂ) • (1 : Matrix ι ι ℂ)) =
      countBelow (increasingEigenvalue hH) x := by
  classical
  rw [negativeCount_eq_card_roots (isHermitian_sub_real_smul_one hH x)]
  have hsc : (x : ℂ) • (1 : Matrix ι ι ℂ) = Matrix.scalar ι (x : ℂ) := by
    simp [Matrix.smul_one_eq_diagonal]
  rw [hsc, Matrix.charpoly_sub_scalar]
  have hlin : (X + C (x : ℂ) : ℂ[X]) = C 1 * X + C (x : ℂ) := by simp
  rw [hlin, roots_comp_C_mul_X_add_C _ _ _ isUnit_one, Multiset.map_map,
    Multiset.filter_map, Multiset.card_map]
  rw [Multiset.filter_congr (q := fun z : ℂ => z.re < x) (fun z _ => by simp)]
  rw [hH.roots_charpoly_eq_eigenvalues₀, Multiset.filter_map, Multiset.card_map]
  rw [Multiset.filter_congr (q := fun i => hH.eigenvalues₀ i < x) (fun i _ => by simp)]
  unfold countBelow increasingEigenvalue
  change Multiset.card (Multiset.filter (fun i => hH.eigenvalues₀ i < x) Finset.univ.val) =
    (Finset.univ.filter fun j : Fin (Fintype.card ι) => hH.eigenvalues₀ j.rev < x).card
  rw [← Finset.filter_val, ← Finset.card_def]
  exact Finset.card_bij (fun i _ => i.rev) (by simp) (by simp)
    (fun j hj => ⟨j.rev, by simpa using hj, by simp⟩)

/-- Zero-based physical rank `α` on Hermitian `H`: `λ_α = increasingEigenvalue` at the
cast rank. -/
theorem physicalOrderedEigenvalue_eq (p : BlockBand.Parameters) {H : p.SiteMatrix}
    (hH : H.IsHermitian) (α : Fin p.N) :
    physicalOrderedEigenvalue p H α = increasingEigenvalue hH (physicalSpectralRank p α) := by
  unfold physicalOrderedEigenvalue
  rw [rawIncreasingEigenvalue_eq _ H hH]

theorem physicalCount_eq_countBelow (p : BlockBand.Parameters) {H : p.SiteMatrix}
    (hH : H.IsHermitian) (x : ℝ) :
    physicalCount p H x = countBelow (increasingEigenvalue hH) x := by
  unfold physicalCount
  exact negativeCount_sub_smul_eq_countBelow hH x

theorem physicalSpectralRank_val (p : BlockBand.Parameters) (α : Fin p.N) :
    (physicalSpectralRank p α).val = α.val := rfl

/-!
## Semicircle slope in the bulk
-/

theorem semicircleDensity_ge {δ x : ℝ} (hδ : 0 < δ) (hx : x ∈ bulkInterval δ) :
    Real.sqrt (2 * δ) / (2 * Real.pi) ≤ Parameters.semicircleDensity x := by
  obtain ⟨h1, h2⟩ := hx
  unfold Parameters.semicircleDensity
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_sqrt
  have ha : δ ≤ 2 - |x| := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hb : 2 ≤ 2 + |x| := by linarith [abs_nonneg x]
  have : 4 - x ^ 2 = (2 - |x|) * (2 + |x|) := by rw [← sq_abs]; ring
  rw [this]
  nlinarith

theorem semicircleCDF_sub_ge {δ x y : ℝ} (hδ : 0 < δ) (hy : y ∈ bulkInterval δ)
    (hx : x ∈ bulkInterval δ) (hyx : y ≤ x) :
    Real.sqrt (2 * δ) / (2 * Real.pi) * (x - y) ≤ semicircleCDF x - semicircleCDF y := by
  rw [BlockBand.Window.Transfer.semicircleCDF_sub]
  have h := intervalIntegral.integral_mono_on hyx
    (intervalIntegrable_const (c := Real.sqrt (2 * δ) / (2 * Real.pi)))
    (BlockBand.Window.Transfer.semicircleDensity_intervalIntegrable y x)
    (fun t ht => semicircleDensity_ge hδ
      ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-- Every `ϑ`-bulk rank (one-based `IsBulkRank`) has `e_α ∈ bulkInterval (πϑ/2)`. -/
theorem classicalLocation_mem_bulk (p : BlockBand.Parameters) {ϑ : ℝ} (hϑ : 0 < ϑ)
    {α : Fin p.N} (hα : IsBulkRank p ϑ α) :
    classicalLocation p α ∈ bulkInterval (Real.pi * ϑ / 2) := by
  have hF := BlockBand.Window.Transfer.semicircleCDF_classicalLocation p α
  obtain ⟨h1, h2⟩ := hα
  have hpi := Real.pi_pos
  set κ := Real.pi * ϑ / 2 with hκ
  have hL := BlockBand.Window.Transfer.abs_semicircleCDF_sub_le (-2 + κ) (-2)
  have hU := BlockBand.Window.Transfer.abs_semicircleCDF_sub_le 2 (2 - κ)
  rw [BlockBand.Window.Transfer.semicircleCDF_neg_two] at hL
  rw [BlockBand.Window.Transfer.semicircleCDF_two] at hU
  have hκπ : κ / Real.pi = ϑ / 2 := by rw [hκ]; field_simp
  have hκ0 : 0 ≤ κ := by positivity
  rw [show -2 + κ - -2 = κ by ring, abs_of_nonneg hκ0, hκπ] at hL
  rw [show 2 - (2 - κ) = κ by ring, abs_of_nonneg hκ0, hκπ] at hU
  constructor
  · by_contra h
    have := BlockBand.Window.Transfer.semicircleCDF_mono (le_of_lt (not_le.mp h))
    have := (abs_le.mp hL).2
    linarith
  · by_contra h
    have := BlockBand.Window.Transfer.semicircleCDF_mono (le_of_lt (not_le.mp h))
    have := (abs_le.mp hU).2
    linarith

/-!
## The multiscale real inequality
-/

/-- Partial counting step: if `Y` dominates `1` at every grid point `(k+1)s < x` with
`(k+1) s ≤ τ` (`k < K`), then `s Σ_{k<K'} Y((k+1)s) ≥ min(K' s, x - s)` for `K' ≤ K`. -/
theorem multiscale_partial {s τ x : ℝ} (hs : 0 < s) (Y : ℝ → ℝ) (hY0 : ∀ t, 0 ≤ Y t)
    (K : ℕ) (hK : (K : ℝ) * s ≤ τ)
    (hY : ∀ t, 0 < t → t ≤ τ → t < x → 1 ≤ Y t) :
    ∀ K' : ℕ, K' ≤ K →
      min ((K' : ℝ) * s) (x - s) ≤ s * ∑ k ∈ Finset.range K', Y ((k + 1) * s) := by
  intro K' hK'
  induction K' with
  | zero => simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.sum_empty, mul_zero]
            exact min_le_left _ _
  | succ m ih =>
    have ih := ih (by omega)
    rw [Finset.sum_range_succ, mul_add]
    have hm : ((m : ℝ) + 1) * s ≤ τ := by
      have : ((m + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK'
      push_cast at this
      nlinarith
    have hYm := hY0 ((m + 1) * s)
    push_cast
    by_cases hlt : ((m : ℝ) + 1) * s < x
    · have h1 := hY ((m + 1) * s) (by positivity) hm hlt
      have h2 : s ≤ s * Y ((m + 1) * s) := by nlinarith
      rcases le_total ((m : ℝ) * s) (x - s) with h | h
      · rw [min_eq_left h] at ih
        calc min (((m : ℝ) + 1) * s) (x - s) ≤ ((m : ℝ) + 1) * s := min_le_left _ _
          _ ≤ _ := by nlinarith
      · rw [min_eq_right h] at ih
        calc min (((m : ℝ) + 1) * s) (x - s) ≤ x - s := min_le_right _ _
          _ ≤ _ := by nlinarith
    · have hx : x - s ≤ (m : ℝ) * s := by nlinarith [not_lt.mp hlt]
      rw [min_eq_right hx] at ih
      calc min (((m : ℝ) + 1) * s) (x - s) ≤ x - s := min_le_right _ _
        _ ≤ _ := by nlinarith

/-- Multiscale inequality: `x ≥ 0`, `s, λ > 0`, `K = ⌊τ/s⌋`; `Y ≥ 0` with `Y(t) ≥ 1`
whenever `0 < t ≤ τ` and `t < x`. Then
`x ≤ s + s Σ_{k<K} Y((k+1)s) + x²/(2λ) + (λ/2) Y(τ)`. -/
theorem abs_le_multiscale {s τ x lam : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hlam : 0 < lam)
    (Y : ℝ → ℝ) (hY0 : ∀ t, 0 ≤ Y t)
    (hY : ∀ t, 0 < t → t ≤ τ → t < x → 1 ≤ Y t) :
    x ≤ s + s * ∑ k ∈ Finset.range ⌊τ / s⌋₊, Y ((k + 1) * s) + x ^ 2 / (2 * lam) +
      lam / 2 * Y τ := by
  set K := ⌊τ / s⌋₊ with hKdef
  have hK : (K : ℝ) * s ≤ τ := by
    have := Nat.floor_le (div_nonneg hτ.le hs.le)
    rw [← hKdef] at this
    calc (K : ℝ) * s ≤ τ / s * s := mul_le_mul_of_nonneg_right this hs.le
      _ = τ := by field_simp
  have hK1 : τ < ((K : ℝ) + 1) * s := by
    have := Nat.lt_floor_add_one (τ / s)
    rw [← hKdef] at this
    calc τ = τ / s * s := by field_simp
      _ < ((K : ℝ) + 1) * s := mul_lt_mul_of_pos_right this hs
  have hsum0 : 0 ≤ s * ∑ k ∈ Finset.range K, Y ((k + 1) * s) :=
    mul_nonneg hs.le (Finset.sum_nonneg fun k _ => hY0 _)
  have hq0 : 0 ≤ x ^ 2 / (2 * lam) := by positivity
  have hYτ := hY0 τ
  by_cases hxτ : τ < x
  · have h1 := hY τ hτ le_rfl hxτ
    have hamgm : x ≤ x ^ 2 / (2 * lam) + lam / 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (x - lam)]
    have : lam / 2 ≤ lam / 2 * Y τ := by nlinarith
    linarith
  · have hxτ' : x ≤ τ := not_lt.mp hxτ
    have h := multiscale_partial hs Y hY0 K hK hY K le_rfl
    have hm : min ((K : ℝ) * s) (x - s) = x - s := min_eq_right (by nlinarith)
    rw [hm] at h
    have : 0 ≤ lam / 2 * Y τ := by positivity
    linarith

end BlockBand.Window.Count
