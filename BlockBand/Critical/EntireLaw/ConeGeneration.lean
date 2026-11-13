module

public import BlockBand.Critical.Entire.RandomEntire

/-!
# The entire law: the positive rational cone values generate the Borel σ-algebra

A countable dense set of values determines an entire function by the identity theorem, applied
successively in each coordinate. In measurable form: a family `X : Ω → EntireFunction m` whose
values at the points `(i q_a)_a`, `q ∈ ℚ_{>0}^m`, are measurable is measurable
(`measurable_of_ratCone`).
* one variable (`measurable_iteratedDeriv_ratAxis`, `measurable_apply_of_ratAxis`): the iterated
  derivatives at `i t`, `t ∈ ℚ_{>0}`, are limits of difference quotients along `i/(k+1)`, and
  `f(z)` is the limit of the Taylor partial sums at `i` (Mathlib
  `Complex.hasSum_taylorSeries_of_entire`);
* several variables: induction on the number of coordinates already freed, each step applies the
  one-variable result to `ζ ↦ F(update z a ζ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology
open BlockBand.Critical.Entire

/-- One variable: the iterated derivatives at positive rational imaginary points are
measurable. -/
theorem measurable_iteratedDeriv_ratAxis {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℂ → ℂ}
    (hf : ∀ ω, Differentiable ℂ (f ω))
    (h : ∀ t : ℚ, 0 < t → Measurable fun ω => f ω ((t : ℂ) * Complex.I)) (n : ℕ) :
    ∀ t : ℚ, 0 < t → Measurable fun ω => iteratedDeriv n (f ω) ((t : ℂ) * Complex.I) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro t ht
    let s : ℕ → ℚ := fun k => ((k : ℚ) + 1)⁻¹
    have hs : ∀ k, 0 < s k := fun k => inv_pos.mpr (by positivity)
    have hs0 : Tendsto (fun k => ((s k : ℂ) * Complex.I)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        have h3 := h2.mul_const Complex.I
        simp only [Complex.ofReal_zero, zero_mul] at h3
        refine h3.congr fun k => ?_
        simp [s]
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero, Complex.I_ne_zero,
          or_false, Rat.cast_eq_zero]
        exact (hs k).ne'
    refine measurable_of_tendsto_metrizable (f := fun k ω =>
      ((s k : ℂ) * Complex.I)⁻¹ * (iteratedDeriv n (f ω) (((t + s k : ℚ) : ℂ) * Complex.I) -
        iteratedDeriv n (f ω) ((t : ℂ) * Complex.I))) (fun k => ?_) ?_
    · exact measurable_const.mul ((ih _ (add_pos ht (hs k))).sub (ih t ht))
    · rw [tendsto_pi_nhds]
      intro ω
      have hd : Differentiable ℂ (iteratedDeriv n (f ω)) :=
        ((hf ω).contDiff (n := ⊤)).differentiable_iteratedDeriv n (WithTop.coe_lt_top _)
      have hD := ((hd ((t : ℂ) * Complex.I)).hasDerivAt.tendsto_slope_zero).comp hs0
      rw [iteratedDeriv_succ]
      refine hD.congr fun k => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      congr 3
      push_cast
      ring

/-- One variable: an entire function is a measurable function of its values at the positive
rational imaginary points (Taylor series at `i`). -/
theorem measurable_apply_of_ratAxis {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℂ → ℂ}
    (hf : ∀ ω, Differentiable ℂ (f ω))
    (h : ∀ t : ℚ, 0 < t → Measurable fun ω => f ω ((t : ℂ) * Complex.I)) (z : ℂ) :
    Measurable fun ω => f ω z := by
  have hI : ∀ n, Measurable fun ω => iteratedDeriv n (f ω) Complex.I := fun n => by
    simpa using measurable_iteratedDeriv_ratAxis hf h n 1 one_pos
  refine measurable_of_tendsto_metrizable (f := fun N ω => ∑ n ∈ Finset.range N,
    ((n.factorial : ℂ)⁻¹ * ((z - Complex.I) ^ n * iteratedDeriv n (f ω) Complex.I)))
    (fun N => Finset.measurable_sum _ fun n _ => measurable_const.mul
      (measurable_const.mul (hI n))) ?_
  rw [tendsto_pi_nhds]
  intro ω
  simpa only [smul_eq_mul] using
    (Complex.hasSum_taylorSeries_of_entire (hf ω) Complex.I z).tendsto_sum_nat

/-- `ζ ↦ update z a ζ` is entire. -/
theorem differentiable_update_coord {m : ℕ} (z : Fin m → ℂ) (a : Fin m) :
    Differentiable ℂ fun ζ : ℂ => Function.update z a ζ := by
  refine differentiable_pi.mpr fun b => ?_
  by_cases hb : b = a
  · subst hb; simp
  · simp [Function.update_of_ne hb]

/-- **Cone values generate**: a family of entire functions whose values at the positive
rational points of the imaginary cone are measurable is a measurable random entire function
(identity theorem / Taylor series, successively in each coordinate). -/
theorem measurable_of_ratCone {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] {X : Ω → EntireFunction m}
    (h : ∀ q : Fin m → ℚ, (∀ a, 0 < q a) →
      Measurable fun ω => X ω (fun a => ((q a : ℚ) : ℂ) * Complex.I)) : Measurable X := by
  have key : ∀ k : ℕ, ∀ z : Fin m → ℂ,
      (∀ a : Fin m, k ≤ a.val → ∃ t : ℚ, 0 < t ∧ z a = (t : ℂ) * Complex.I) →
      Measurable fun ω => X ω z := by
    intro k
    induction k with
    | zero =>
      intro z hz
      choose q hq hzq using fun a => hz a (Nat.zero_le _)
      have : z = fun a => ((q a : ℚ) : ℂ) * Complex.I := funext hzq
      rw [this]
      exact h q hq
    | succ k ih =>
      intro z hz
      by_cases hk : k < m
      · let a0 : Fin m := ⟨k, hk⟩
        have hf : ∀ ω, Differentiable ℂ fun ζ => X ω (Function.update z a0 ζ) := fun ω =>
          (X ω).differentiable.comp (differentiable_update_coord z a0)
        have hmeas := measurable_apply_of_ratAxis hf (fun t ht => by
          refine ih _ fun a ha => ?_
          by_cases hae : a = a0
          · subst hae; exact ⟨t, ht, by simp⟩
          · rw [Function.update_of_ne hae]
            refine hz a ?_
            have : a.val ≠ k := fun h' => hae (Fin.ext h')
            omega) (z a0)
        simpa using hmeas
      · refine ih z fun a ha => ?_
        exact absurd (lt_of_lt_of_le a.isLt (by omega)) (lt_irrefl _)
  exact EntireFunction.measurable_iff_eval.mpr fun z => key m z fun a ha => absurd a.isLt (by omega)

end BlockBand.Critical.EntireLaw
