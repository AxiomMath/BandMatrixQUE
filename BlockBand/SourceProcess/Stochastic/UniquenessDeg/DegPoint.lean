module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegBound
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerCauchy
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Pointwise Gronwall bounds in `ℝ≥0∞` for the degenerate comparisons

With `x = E_j` (Euler grid value), `y` (solution, or second scheme), `u` (interpolated scheme)
and the coefficients `c : LipCoef d` (constants `L`, `M`), `degLip c = 2 · eulLip c + 1`:
* **`coefSq_vsY`**: `|b(x) - b(y)|² + ∑_i qZ(gY) ≤ degLip · (|u - y|² + |u - x|² + 2 d² M² f)`
  with `f = frob(tikX s ε - pinvX s)`, `s = c.σ y`;
* **`coefSq_vsX`**: the analogous bound for two Euler schemes (`x, x'` grid values,
  `u, u'` interpolants), with `f = frob(tikX s ε - tikX s ε')`;
* `coefSq_off`: outside the stochastic interval, `|b(x) - b(x')|² + ∑_i qZ ≤ degLip (…)`.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open Matrix Filter Topology
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

variable {d : ℕ}

/-- The Lipschitz constant of the degenerate comparisons. -/
def degLip (c : LipCoef d) : ℝ≥0 := 2 * eulLip c + 1

theorem sq2_sigma_le (c : LipCoef d) (y : Fin d → ℝ) : sq2 (c.σ y) ≤ d ^ 2 * c.M ^ 2 := by
  unfold sq2
  calc ∑ i, ∑ k, c.σ y i k ^ 2 ≤ ∑ _i : Fin d, ∑ _k : Fin d, c.M ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (c.bd_σ y i k) 2
    _ = d ^ 2 * c.M ^ 2 := by simp; ring

theorem ofReal_two_sq2 (Γ Γ' : Matrix (Fin d) (Fin d) ℝ) :
    ENNReal.ofReal (2 * sq2 (fun i k => Γ i k - Γ' i k)) =
      2 * ∑ i, ∑ k, ‖Γ i k - Γ' i k‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, sq2,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofReal_sum_sq (fun k => Γ i k - Γ' i k)]

theorem degLip_bound (c : LipCoef d) {A B C E : ℝ≥0∞} (h : A + C ≤ (eulLip c : ℝ≥0∞) * B) :
    A + (2 * C + E) ≤ (degLip c : ℝ≥0∞) * (B + E) := by
  have h2 : A + 2 * C ≤ 2 * (eulLip c : ℝ≥0∞) * B := by
    calc A + 2 * C ≤ 2 * (A + C) := by
          rw [mul_add]
          gcongr
          calc A = 1 * A := (one_mul A).symm
            _ ≤ 2 * A := by gcongr; norm_num
      _ ≤ 2 * ((eulLip c : ℝ≥0∞) * B) := by gcongr
      _ = _ := by ring
  calc A + (2 * C + E) = (A + 2 * C) + E := by ring
    _ ≤ 2 * (eulLip c : ℝ≥0∞) * B + E := by gcongr
    _ ≤ (degLip c : ℝ≥0∞) * (B + E) := by
        simp only [degLip, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
          add_mul, mul_add, one_mul]
        calc 2 * (eulLip c : ℝ≥0∞) * B + E ≤ 2 * (eulLip c : ℝ≥0∞) * B + B + E := by
              gcongr; exact le_self_add
          _ ≤ _ := by
              rw [add_assoc, add_assoc]; gcongr; exact le_add_self

/-- **The pointwise bound against the solution.** -/
theorem coefSq_vsY (c : LipCoef d) (x y u : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑ i, ‖c.b x i - c.b y i‖ₑ ^ 2) + ENNReal.ofReal (∑ i, ∑ c₁, ∑ c₂,
      gY (c.σ y) (c.σ x) ε i c₁ * gY (c.σ y) (c.σ x) ε i c₂ * zDens (c.σ y) c₁ c₂) ≤
    (degLip c : ℝ≥0∞) * (((∑ i, ‖(u - y) i‖ₑ ^ 2) + (∑ i, ‖u i - x i‖ₑ ^ 2)) +
      ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 *
        frob (fun k c' => tikX (c.σ y) ε k c' + -pinvX (c.σ y) k c'))) := by
  have hq := quad_sum_vsY_le (c.σ y) (c.σ x) hε
  have hf := frob_nonneg (fun k c' => tikX (c.σ y) ε k c' + -pinvX (c.σ y) k c')
  have hs := sq2_sigma_le c y
  have hE := coefSq_euler_bound c x y u y
  simp only [sub_self, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, add_zero] at hE
  have h1 : ENNReal.ofReal (∑ i, ∑ c₁, ∑ c₂, gY (c.σ y) (c.σ x) ε i c₁ *
      gY (c.σ y) (c.σ x) ε i c₂ * zDens (c.σ y) c₁ c₂) ≤
      ENNReal.ofReal (2 * sq2 (fun i k => c.σ x i k - c.σ y i k)) +
        ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 *
          frob (fun k c' => tikX (c.σ y) ε k c' + -pinvX (c.σ y) k c')) := by
    rw [← ENNReal.ofReal_add (by have := sq2_nonneg (fun i k => c.σ x i k - c.σ y i k); positivity)
      (by positivity)]
    refine ENNReal.ofReal_le_ofReal (hq.trans ?_)
    have : sq2 (c.σ y) * frob (fun k c' => tikX (c.σ y) ε k c' + -pinvX (c.σ y) k c') ≤
        d ^ 2 * c.M ^ 2 * frob (fun k c' => tikX (c.σ y) ε k c' + -pinvX (c.σ y) k c') :=
      mul_le_mul_of_nonneg_right hs hf
    linarith
  rw [ofReal_two_sq2] at h1
  calc _ ≤ (∑ i, ‖c.b x i - c.b y i‖ₑ ^ 2) + (2 * ∑ i, ∑ k, ‖c.σ x i k - c.σ y i k‖ₑ ^ 2 +
        ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 *
          frob (fun k c' => tikX (c.σ y) ε k c' + -pinvX (c.σ y) k c'))) := by gcongr
    _ ≤ _ := degLip_bound c hE

/-- **The pointwise bound for two Euler schemes** (inside the stochastic interval). -/
theorem coefSq_vsX (c : LipCoef d) (x x' u u' y : Fin d → ℝ) {ε ε' : ℝ} (hε : 0 < ε) :
    (∑ i, ‖c.b x i - c.b x' i‖ₑ ^ 2) + ENNReal.ofReal (∑ i, ∑ c₁, ∑ c₂,
      gX (c.σ y) (c.σ x) (c.σ x') ε ε' i c₁ * gX (c.σ y) (c.σ x) (c.σ x') ε ε' i c₂ *
        zDens (c.σ y) c₁ c₂) ≤
    (degLip c : ℝ≥0∞) * (((∑ i, ‖(u - u') i‖ₑ ^ 2) +
      ((∑ i, ‖u i - x i‖ₑ ^ 2) + ∑ i, ‖u' i - x' i‖ₑ ^ 2)) +
      ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 *
        frob (fun k c' => tikX (c.σ y) ε k c' + -tikX (c.σ y) ε' k c'))) := by
  have hq := quad_sum_vsX_le (c.σ y) (c.σ x) (c.σ x') (ε' := ε') hε
  have hf := frob_nonneg (fun k c' => tikX (c.σ y) ε k c' + -tikX (c.σ y) ε' k c')
  have hs := sq2_sigma_le c x'
  have hE := coefSq_euler_bound c x x' u u'
  have h1 : ENNReal.ofReal (∑ i, ∑ c₁, ∑ c₂, gX (c.σ y) (c.σ x) (c.σ x') ε ε' i c₁ *
      gX (c.σ y) (c.σ x) (c.σ x') ε ε' i c₂ * zDens (c.σ y) c₁ c₂) ≤
      ENNReal.ofReal (2 * sq2 (fun i k => c.σ x i k - c.σ x' i k)) +
        ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 *
          frob (fun k c' => tikX (c.σ y) ε k c' + -tikX (c.σ y) ε' k c')) := by
    have hsq0 := sq2_nonneg (fun i k => c.σ x i k - c.σ x' i k)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (hq.trans ?_)
    have : sq2 (c.σ x') * frob (fun k c' => tikX (c.σ y) ε k c' + -tikX (c.σ y) ε' k c') ≤
        d ^ 2 * c.M ^ 2 * frob (fun k c' => tikX (c.σ y) ε k c' + -tikX (c.σ y) ε' k c') :=
      mul_le_mul_of_nonneg_right hs hf
    linarith
  rw [ofReal_two_sq2] at h1
  calc _ ≤ (∑ i, ‖c.b x i - c.b x' i‖ₑ ^ 2) + (2 * ∑ i, ∑ k, ‖c.σ x i k - c.σ x' i k‖ₑ ^ 2 +
        ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 *
          frob (fun k c' => tikX (c.σ y) ε k c' + -tikX (c.σ y) ε' k c'))) := by gcongr
    _ ≤ _ := degLip_bound c hE

/-- **The pointwise bound for two Euler schemes** (outside the stochastic interval). -/
theorem coefSq_off (c : LipCoef d) (x x' u u' : Fin d → ℝ) :
    (∑ i, ‖c.b x i - c.b x' i‖ₑ ^ 2) +
      ENNReal.ofReal (sq2 (fun i k => c.σ x i k - c.σ x' i k)) ≤
    (degLip c : ℝ≥0∞) * ((∑ i, ‖(u - u') i‖ₑ ^ 2) +
      ((∑ i, ‖u i - x i‖ₑ ^ 2) + ∑ i, ‖u' i - x' i‖ₑ ^ 2)) := by
  have hE := coefSq_euler_bound c x x' u u'
  have h := degLip_bound c (E := 0) hE
  rw [add_zero, add_zero] at h
  refine le_trans ?_ h
  gcongr
  have e := ofReal_two_sq2 (c.σ x) (c.σ x')
  have h2 : ENNReal.ofReal (sq2 fun i k => c.σ x i k - c.σ x' i k) ≤
      ENNReal.ofReal (2 * sq2 fun i k => c.σ x i k - c.σ x' i k) :=
    ENNReal.ofReal_le_ofReal (by have := sq2_nonneg (fun i k => c.σ x i k - c.σ x' i k); linarith)
  rw [e] at h2
  exact h2

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
