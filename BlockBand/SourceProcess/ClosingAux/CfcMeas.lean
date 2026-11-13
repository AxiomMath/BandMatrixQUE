module

public import BlockBand.SourceProcess.Closing.Defs

/-!
# Borel measurability of `X ↦ cfc f X` on matrices (indicator-type `f`)

* `measurable_cfc_of_continuous`: for continuous `f`, `X ↦ cfc f X` is measurable (continuous on
  the closed set of self-adjoint matrices, `0` off it).
* `tendsto_cfc_of_tendsto`: if `f_k → f` pointwise then `cfc f_k X → cfc f X` for every `X`
  (for Hermitian `X` through the eigen-decomposition `X = U diag(λ) Uᴴ`, otherwise all are `0`).
* `measurable_cfc_of_tendsto`: hence the class of `f` with `cfc f` measurable is closed under
  pointwise limits of sequences.
* `measurable_cfc_omitIndicator`, `measurable_cfc_pairWeight`: the cutoffs `1_{t≤h²}` and
  `1_{t≤h²}(1-t)^{-1/2}` (any real `h`) are pointwise limits of continuous functions.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingAux

open MeasureTheory Matrix Filter Topology
open BlockBand.SourceProcess.Closing

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
theorem measurable_cfc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun A : Matrix n n ℂ => cfc f A := by
  classical
  have hc : ContinuousOn (fun A : Matrix n n ℂ => cfc f A) {A | IsSelfAdjoint A} :=
    ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) _ (by simp) continuousOn_id
      (fun x hx => hx) hf.continuousOn
  have hS : IsClosed {A : Matrix n n ℂ | IsSelfAdjoint A} :=
    isClosed_eq continuous_star continuous_id
  have e : (fun A : Matrix n n ℂ => cfc f A) =
      Set.piecewise {A | IsSelfAdjoint A} (fun A => cfc f A) (fun _ => 0) := by
    funext A
    by_cases h : IsSelfAdjoint A
    · simp [Set.piecewise, h]
    · simp [Set.piecewise, h, cfc_apply_of_not_predicate A h]
  rw [e]
  exact hc.measurable_piecewise continuousOn_const hS.measurableSet

theorem tendsto_cfc_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hfg : ∀ t, Tendsto (fun k => f k t) atTop (𝓝 (g t))) (A : Matrix n n ℂ) :
    Tendsto (fun k => cfc (f k) A) atTop (𝓝 (cfc g A)) := by
  by_cases hA : IsSelfAdjoint A
  · have hH : A.IsHermitian := hA
    simp only [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    have hd : Tendsto (fun k => diagonal (RCLike.ofReal ∘ f k ∘ hH.eigenvalues)) atTop
        (𝓝 (diagonal (RCLike.ofReal ∘ g ∘ hH.eigenvalues) : Matrix n n ℂ)) := by
      have hc : Continuous fun d : n → ℂ => diagonal d := continuous_id.matrix_diagonal
      refine (hc.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
      exact (Complex.continuous_ofReal.tendsto _).comp (hfg _)
    exact (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).tendsto
      _).comp hd
  · simp only [cfc_apply_of_not_predicate A hA]
    exact tendsto_const_nhds

/-- The class of `f` with `X ↦ cfc f X` measurable is closed under pointwise sequential limits. -/
theorem measurable_cfc_of_tendsto {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ k, Measurable fun A : Matrix n n ℂ => cfc (f k) A)
    (hfg : ∀ t, Tendsto (fun k => f k t) atTop (𝓝 (g t))) :
    Measurable fun A : Matrix n n ℂ => cfc g A :=
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix n n ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (n → n → ℂ))
  measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 (tendsto_cfc_of_tendsto hfg))

/-!
## Continuous approximants of the cutoffs
-/

/-- `max 0 (min 1 (1 - k(t - c)))`, which tends to `1_{t ≤ c}`. -/
def stepLe (c : ℝ) (k : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (1 - k * (t - c)))

/-- `max 0 (min 1 (k(c - t)))`, which tends to `1_{t < c}`. -/
def stepLt (c : ℝ) (k : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (k * (c - t)))

/-- `(√(1-t) + (k+1)⁻¹)⁻¹`. -/
def regInvSqrt (k : ℕ) (t : ℝ) : ℝ := (Real.sqrt (1 - t) + ((k : ℝ) + 1)⁻¹)⁻¹

theorem continuous_stepLe (c : ℝ) (k : ℕ) : Continuous (stepLe c k) := by
  unfold stepLe; fun_prop

theorem continuous_stepLt (c : ℝ) (k : ℕ) : Continuous (stepLt c k) := by
  unfold stepLt; fun_prop

theorem continuous_regInvSqrt (k : ℕ) : Continuous (regInvSqrt k) := by
  unfold regInvSqrt
  refine Continuous.inv₀ (by fun_prop) fun t => ?_
  have : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
  have := Real.sqrt_nonneg (1 - t)
  linarith

theorem tendsto_stepLe (c t : ℝ) :
    Tendsto (fun k => stepLe c k t) atTop (𝓝 (if t ≤ c then 1 else 0)) := by
  split_ifs with ht
  · refine tendsto_const_nhds.congr fun k => ?_
    have : 0 ≤ (k : ℝ) * (c - t) := mul_nonneg k.cast_nonneg (by linarith)
    unfold stepLe
    rw [min_eq_left (by nlinarith), max_eq_right zero_le_one]
  · obtain ⟨K, hK⟩ := exists_nat_gt (1 / (t - c))
    have hpos : 0 < t - c := by linarith
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K] with k hk
    have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : 1 < (k : ℝ) * (t - c) := by
      rw [div_lt_iff₀ hpos] at hK; nlinarith
    unfold stepLe
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]

theorem tendsto_stepLt (c t : ℝ) :
    Tendsto (fun k => stepLt c k t) atTop (𝓝 (if t < c then 1 else 0)) := by
  split_ifs with ht
  · obtain ⟨K, hK⟩ := exists_nat_gt (1 / (c - t))
    have hpos : 0 < c - t := by linarith
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K] with k hk
    have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : 1 < (k : ℝ) * (c - t) := by
      rw [div_lt_iff₀ hpos] at hK; nlinarith
    unfold stepLt
    rw [min_eq_left h1.le, max_eq_right zero_le_one]
  · refine tendsto_const_nhds.congr fun k => ?_
    have : (k : ℝ) * (c - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg (by linarith)
    unfold stepLt
    rw [max_eq_left (le_trans (min_le_right _ _) this)]

theorem tendsto_regInvSqrt {t : ℝ} (ht : t < 1) :
    Tendsto (fun k => regInvSqrt k t) atTop (𝓝 (Real.sqrt (1 - t))⁻¹) := by
  have hs : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have h0 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.sqrt (1 - t)) atTop _).add h0
  rw [add_zero] at h1
  exact h1.inv₀ hs

theorem tendsto_pairWeight_approx (h t : ℝ) :
    Tendsto (fun k => stepLe (h ^ 2) k t * (stepLt 1 k t * regInvSqrt k t)) atTop
      (𝓝 (pairWeight h t)) := by
  by_cases ht : t < 1
  · have hL := (tendsto_stepLe (h ^ 2) t).mul ((tendsto_stepLt 1 t).mul (tendsto_regInvSqrt ht))
    convert hL using 2
    simp only [pairWeight, ht, ite_true, one_mul]
    split_ifs <;> simp
  · have hz : ∀ k, stepLt 1 k t = 0 := fun k => by
      have : (k : ℝ) * (1 - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg (by linarith)
      unfold stepLt
      rw [max_eq_left (le_trans (min_le_right _ _) this)]
    have hp : pairWeight h t = 0 := by
      unfold pairWeight
      split_ifs
      · rw [Real.sqrt_eq_zero'.2 (by linarith), _root_.inv_zero]
      · rfl
    simp only [hz, zero_mul, mul_zero, hp]
    exact tendsto_const_nhds

theorem measurable_cfc_omitIndicator (h : ℝ) :
    Measurable fun A : Matrix n n ℂ => cfc (omitIndicator h) A :=
  measurable_cfc_of_tendsto (fun k => measurable_cfc_of_continuous (continuous_stepLe _ k))
    fun t => by simpa [omitIndicator] using tendsto_stepLe (h ^ 2) t

theorem measurable_cfc_pairWeight (h : ℝ) :
    Measurable fun A : Matrix n n ℂ => cfc (pairWeight h) A :=
  measurable_cfc_of_tendsto (fun k => measurable_cfc_of_continuous
    ((continuous_stepLe _ k).mul ((continuous_stepLt _ k).mul (continuous_regInvSqrt k))))
    (tendsto_pairWeight_approx h)

end BlockBand.SourceProcess.ClosingAux
