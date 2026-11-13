module

public import BlockBand.SourceProcess.ContractingWords.LiftTools

/-!
# The `L²` size of the lifted one-layer bound

`eLpNorm_lifted_le`: the `L²` norm of a lifted majorant `C₁ e Σ_i |1_A Z_i| + C₁(e² + e^N + …)` is
bounded from `L⁴` bounds on `e` and on the products `Z_i` and from `L²` bounds on the powers of `e`
(Hölder and Minkowski); `stepErr_of_parts` is the resulting arithmetic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open scoped ENNReal

section Abstract

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem eLpNorm_const_prob' (c : ℝ) (hc : 0 ≤ c) (p : ℝ≥0∞) :
    eLpNorm (fun _ : Ω => c) p μ ≤ ENNReal.ofReal c := by
  refine (eLpNorm_le_of_ae_bound aestronglyMeasurable_const (C := c)
    (Eventually.of_forall fun _ => by rw [Real.norm_of_nonneg hc])).trans ?_
  simp

theorem eLpNorm_lifted_le {ι : Type*} (L : List ι) (Z : ι → Ω → ℂ) (A : Set Ω)
    (hA : MeasurableSet A) (e : Ω → ℝ) (hem : AEStronglyMeasurable e μ)
    (hZm : ∀ i, AEStronglyMeasurable (Z i) μ) (N : ℕ) {C₁ a₄ a₂ aN z c : ℝ} (hC₁ : 0 ≤ C₁)
    (ha₄ : 0 ≤ a₄) (hz : 0 ≤ z) (hc : 0 ≤ c) (ha₂ : 0 ≤ a₂) (haN : 0 ≤ aN)
    (h4 : eLpNorm e 4 μ ≤ ENNReal.ofReal a₄)
    (h2 : eLpNorm (fun ω => e ω ^ 2) 2 μ ≤ ENNReal.ofReal a₂)
    (hN : eLpNorm (fun ω => e ω ^ N) 2 μ ≤ ENNReal.ofReal aN)
    (hZ : ∀ i ∈ L, eLpNorm (A.indicator (Z i)) 4 μ ≤ ENNReal.ofReal z) :
    eLpNorm (fun ω => C₁ * (L.map fun i => e ω * ‖A.indicator (Z i) ω‖).sum +
        C₁ * (c + e ω ^ 2 + e ω ^ N)) 2 μ ≤
      ENNReal.ofReal (C₁ * (L.length * (a₄ * z)) + C₁ * (c + a₂ + aN)) := by
  have h12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hsplit : (fun ω => C₁ * (L.map fun i => e ω * ‖A.indicator (Z i) ω‖).sum +
      C₁ * (c + e ω ^ 2 + e ω ^ N)) =
      C₁ • (fun ω => (L.map fun i => e ω * ‖A.indicator (Z i) ω‖).sum) +
        C₁ • ((fun _ => c) + (fun ω => e ω ^ 2) + fun ω => e ω ^ N) := by
    funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsplit]
  refine (eLpNorm_add_le h12).trans ?_
  rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal hC₁]
  have hfirst : eLpNorm (fun ω => (L.map fun i => e ω * ‖A.indicator (Z i) ω‖).sum) 2 μ ≤
      ENNReal.ofReal (L.length * (a₄ * z)) := by
    refine (eLpNorm_listSum_le L (fun i ω => e ω * ‖A.indicator (Z i) ω‖) h12).trans ?_
    have hterm : ∀ i ∈ L, eLpNorm (fun ω => e ω * ‖A.indicator (Z i) ω‖) 2 μ ≤
        ENNReal.ofReal (a₄ * z) := fun i hi => by
      have hn : AEStronglyMeasurable (fun ω => ‖A.indicator (Z i) ω‖) μ :=
        ((hZm i).indicator hA).norm
      refine (eLpNorm_mul_le_four hem hn).trans ?_
      rw [eLpNorm_norm _ ((hZm i).indicator hA), ENNReal.ofReal_mul ha₄]
      exact mul_le_mul' h4 (hZ i hi)
    clear hsplit
    induction L with
    | nil => simp
    | cons i L ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      refine (add_le_add (hterm i (List.mem_cons_self ..))
        (ih (fun j hj => hZ j (List.mem_cons_of_mem _ hj))
          (fun j hj => hterm j (List.mem_cons_of_mem _ hj)))).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by push_cast; nlinarith [mul_nonneg ha₄ hz])
  have hsecond : eLpNorm ((fun _ => c) + (fun ω => e ω ^ 2) + fun ω => e ω ^ N) 2 μ ≤
      ENNReal.ofReal (c + a₂ + aN) := by
    refine (eLpNorm_add_le h12).trans ?_
    refine (add_le_add ((eLpNorm_add_le h12).trans (add_le_add (eLpNorm_const_prob' c hc 2) h2))
      hN).trans ?_
    rw [← ENNReal.ofReal_add hc ha₂, ← ENNReal.ofReal_add (by positivity) haN]
  calc ENNReal.ofReal C₁ * eLpNorm (fun ω => (L.map fun i => e ω * ‖A.indicator (Z i) ω‖).sum)
        2 μ + ENNReal.ofReal C₁ * eLpNorm ((fun _ => c) + (fun ω => e ω ^ 2) + fun ω => e ω ^ N)
        2 μ ≤ ENNReal.ofReal C₁ * ENNReal.ofReal (L.length * (a₄ * z)) +
          ENNReal.ofReal C₁ * ENNReal.ofReal (c + a₂ + aN) :=
        add_le_add (mul_le_mul' le_rfl hfirst) (mul_le_mul' le_rfl hsecond)
    _ = _ := by
        rw [← ENNReal.ofReal_mul hC₁, ← ENNReal.ofReal_mul hC₁,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end Abstract

/-- The arithmetic of the lifted bound. -/
theorem stepErr_of_parts {W : ℕ} (hW : 1 ≤ W) {C₁ Cz Ce M ρ m c₂ cN : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hC₁ : 0 ≤ C₁) (hρ : 0 ≤ ρ) (hm : 0 ≤ m) (hcN : 0 ≤ cN) (hρm : m = ρ) :
    C₁ * (M * (Ce / W * (Cz * (m + 1 / Real.sqrt W)))) +
        C₁ * ((W : ℝ)⁻¹ / Real.sqrt W + (c₂ / W) ^ 2 + (cN / W) ^ N) ≤
      (C₁ * M * Ce * Cz + C₁ * (1 + c₂ ^ 2 + cN ^ N)) / W * (ρ + 1 / Real.sqrt W) := by
  subst hρm
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  have hs1 : Real.sqrt W ≤ W := by
    rw [Real.sqrt_le_left hW0.le]; nlinarith
  have hsq := Real.sq_sqrt hW0.le
  have e2 : (c₂ / W) ^ 2 ≤ c₂ ^ 2 / W * (1 / Real.sqrt W) := by
    rw [div_pow, div_mul_eq_mul_div, mul_one_div, div_div]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith
  have eN : (cN / W) ^ N ≤ cN ^ N / W * (1 / Real.sqrt W) := by
    rw [div_pow, div_mul_eq_mul_div, mul_one_div, div_div]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    calc Real.sqrt W * (W : ℝ) ≤ W * W := mul_le_mul_of_nonneg_right hs1 hW0.le
      _ = W ^ 2 := by ring
      _ ≤ W ^ N := pow_le_pow_right₀ hW1 hN
  have e1 : (W : ℝ)⁻¹ / Real.sqrt W = 1 / W * (1 / Real.sqrt W) := by
    rw [one_div (W : ℝ), div_eq_mul_one_div]
  have hX : 0 ≤ 1 / (W : ℝ) * (1 / Real.sqrt W) := by positivity
  have hY : 0 ≤ 1 / Real.sqrt W := by positivity
  rw [e1]
  have key : C₁ * (M * (Ce / W * (Cz * (m + 1 / Real.sqrt W)))) =
      C₁ * M * Ce * Cz / W * (m + 1 / Real.sqrt W) := by ring
  rw [key, add_div, add_mul]
  refine add_le_add le_rfl ?_
  have h1 : C₁ * (1 / W * (1 / Real.sqrt W) + (c₂ / W) ^ 2 + (cN / W) ^ N) ≤
      C₁ * (1 + c₂ ^ 2 + cN ^ N) / W * (1 / Real.sqrt W) := by
    have : C₁ * (1 + c₂ ^ 2 + cN ^ N) / W * (1 / Real.sqrt W) =
        C₁ * (1 / W * (1 / Real.sqrt W) + c₂ ^ 2 / W * (1 / Real.sqrt W) +
          cN ^ N / W * (1 / Real.sqrt W)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hC₁
  refine h1.trans ?_
  have h0 : 0 ≤ C₁ * (1 + c₂ ^ 2 + cN ^ N) / W := by positivity
  nlinarith [mul_nonneg h0 hm]

end BlockBand.SourceProcess.ContractingWords
