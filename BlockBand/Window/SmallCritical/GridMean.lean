module

public import BlockBand.Window.SmallCritical.Common

/-!
# Grid means of continuous torus tests

`gridDefect p φ = N⁻¹ Σ_x (φ(x₁/n) - φ̄)` is the deterministic difference between the grid mean
`n⁻¹ Σ_k φ(k/n)` and `φ̄ = ∫_𝕋 φ` (Haar probability). For continuous `φ` it tends to zero
along every critical sequence (`n → ∞`): a Riemann-sum estimate with uniform continuity on
`[0,1]` and `AddCircle.intervalIntegral_preimage`. Only continuity of `φ` is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction
open scoped ENNReal NNReal

/-- `gridDefect p φ = N⁻¹ Σ_x (φ(x₁/n) - φ̄)`. -/
def gridDefect (p : Parameters) (φ : Torus → ℝ) : ℝ :=
  (p.N : ℝ)⁻¹ * ∑ x : p.Site, (φ (physicalProfileGrid p x.1) - ∫ r, φ r)

/-- `gridDefect p φ = n⁻¹ Σ_{i<n} φ(i/n) - φ̄`. -/
theorem gridDefect_eq (p : Parameters) (φ : Torus → ℝ) :
    gridDefect p φ =
      (1 / (p.n : ℝ)) * ∑ i ∈ Finset.range p.n, φ (((i : ℝ) / p.n : ℝ) : Torus) - ∫ r, φ r := by
  have : NeZero p.n := ⟨p.n_pos.ne'⟩
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hsum : ∑ k : ZMod p.n, φ (physicalProfileGrid p k) =
      ∑ i ∈ Finset.range p.n, φ (((i : ℝ) / p.n : ℝ) : Torus) := by
    refine Finset.sum_nbij' (fun k : ZMod p.n => k.val) (fun i : ℕ => (i : ZMod p.n))
      (fun k _ => Finset.mem_range.mpr (ZMod.val_lt k)) (fun _ _ => Finset.mem_univ _)
      (fun k _ => ZMod.natCast_zmod_val k)
      (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi)) (fun k _ => rfl)
  unfold gridDefect
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  unfold Parameters.N
  push_cast
  field_simp

/-- One cell: `|∫_a^{a+h} f - h f(a)| ≤ h δ` when `|f x - f a| ≤ δ` on the cell. -/
theorem abs_cell_sub_le {f : ℝ → ℝ} (hf : Continuous f) {a h δ : ℝ} (hh : 0 ≤ h)
    (hδ : ∀ x ∈ Icc a (a + h), |f x - f a| ≤ δ) :
    |(∫ x in a..a + h, f x) - h * f a| ≤ h * δ := by
  have hint : (∫ x in a..a + h, (f x - f a)) = (∫ x in a..a + h, f x) - h * f a := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
    simp
  rw [← hint]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + h) (C := δ)
    (f := fun x => f x - f a) (fun x hx => by
      rw [Set.uIoc_of_le (by linarith)] at hx
      exact hδ x ⟨hx.1.le, hx.2⟩)
  simpa [Real.norm_eq_abs, abs_of_nonneg hh, mul_comm] using this

/-- **Riemann sums on the torus.** For continuous `φ`, `n⁻¹ Σ_{i<n} φ(i/n) → ∫_𝕋 φ`. -/
theorem torus_riemann (φ : Torus → ℝ) (hφ : Continuous φ) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 0 < n →
      |(1 / (n : ℝ)) * ∑ i ∈ Finset.range n, φ (((i : ℝ) / n : ℝ) : Torus) - ∫ r, φ r| ≤ δ := by
  intro δ hδ
  set f : ℝ → ℝ := fun x => φ (x : Torus) with hfdef
  have hf : Continuous f := hφ.comp continuous_quotient_mk'
  obtain ⟨h₀, hh₀, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous hf.continuousOn) δ hδ
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / h₀)
  refine ⟨N₀, fun n hn hn0 => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set h : ℝ := 1 / n with hh
  have hh0 : 0 < h := by positivity
  have hhlt : h < h₀ := by
    rw [hh, div_lt_iff₀ hnR]
    have : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hh₀] at hN₀
    nlinarith
  have hcell : ∀ i ∈ Finset.range n,
      |(∫ x in (i : ℝ) * h..((i + 1 : ℕ) : ℝ) * h, f x) - h * f (i * h)| ≤ h * δ := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast (Finset.mem_range.mp hi)
    rw [show ((i + 1 : ℕ) : ℝ) * h = i * h + h by push_cast; ring]
    apply abs_cell_sub_le hf hh0.le
    intro x hx
    have hx0 : 0 ≤ (i : ℝ) * h := by positivity
    have hx1 : (i : ℝ) * h + h ≤ 1 := by
      rw [hh]; field_simp; linarith
    have := hunif x ⟨by linarith [hx.1], by linarith [hx.2]⟩ (i * h) ⟨hx0, by linarith⟩
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
    rw [Real.dist_eq] at this
    exact this.le
  have htot : (∑ i ∈ Finset.range n, ∫ x in (i : ℝ) * h..((i + 1 : ℕ) : ℝ) * h, f x) =
      ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ) * h)
      (fun k _ => hf.intervalIntegrable _ _)]
    simp only [Nat.cast_zero, zero_mul]
    congr 1
    rw [hh]; field_simp
  have hper : (∫ x in (0 : ℝ)..1, f x) = ∫ r, φ r := by
    have := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 φ
    rw [zero_add] at this
    exact this
  have hsum : |(∑ i ∈ Finset.range n, ((∫ x in (i : ℝ) * h..((i + 1 : ℕ) : ℝ) * h, f x) -
      h * f (i * h)))| ≤ ∑ i ∈ Finset.range n, h * δ :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hcell)
  rw [Finset.sum_sub_distrib, htot, hper, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  have hnh : (n : ℝ) * (h * δ) = δ := by rw [hh]; field_simp
  rw [hnh, abs_sub_comm] at hsum
  have he : ∀ i ∈ Finset.range n, f (i * h) = φ (((i : ℝ) / n : ℝ) : Torus) := by
    intro i _; simp only [hfdef, hh]; congr 2; ring
  rw [Finset.sum_congr rfl he] at hsum
  exact hsum

/-- Along every critical sequence with `τ > 0`, `gridDefect → 0`. -/
theorem gridDefect_tendsto {τ : ℝ} (s : CriticalSequence τ) (hτ : 0 < τ) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (φ : Torus → ℝ) (hφ : Continuous φ) :
    Tendsto (fun j => gridDefect (s.parameters b hb hb' j) φ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := torus_riemann φ hφ (δ / 2) (by positivity)
  have hev := (criticalSequence_n_real_tendsto_atTop s hτ).eventually
    (eventually_ge_atTop (N₀ : ℝ))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hev
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq, sub_zero, gridDefect_eq]
  have hn : N₀ ≤ s.n j := by exact_mod_cast hJ j hj
  have := hN₀ (s.n j) hn (Nat.lt_of_lt_of_le (by norm_num) (s.n_ge_four j))
  exact lt_of_le_of_lt this (by linarith)

end BlockBand.Window.SmallCritical
