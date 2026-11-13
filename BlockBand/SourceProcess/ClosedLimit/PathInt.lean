module

public import BlockBand.SourceProcess.BornUnique.Pin
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time integrals along born Gram paths: measurability and continuity

A born path is `G_u = A_u + J_u` with `A` continuous and `J_u = Σ_f 1{β_f ≤ u} j_f` (see
`birthSum`). On the event that the birth pattern at time `u` is `S ⊆ F`, `J_u = Σ_{f∈S} j_f`, so
for continuous `f` the integrand `f(G_u)` is a finite sum of indicators times continuous functions
of `u` (`integrand_split`). Consequences:

* `measurable_uncurry_split`: joint measurability in `(s, ω)` for any σ-algebra on `Ω` in which the
  `β_f` and the `ω ↦ f(A_s ω + J_S)` are measurable (used with the past σ-algebra);
* `intervalIntegrable_path`, `continuous_integral_path`: for every path, `u ↦ f(G_u)` is
  locally bounded and measurable, so `t ↦ ∫_{(0,t]} f(G_s) ds` is continuous;
* `continuous_gramDriftEntry`, `continuous_gramCovEntry`: the Gram coefficients are continuous.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess BlockBand.SourceProcess.BornUnique
open scoped NNReal ENNReal

variable {c F : Type*} [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem continuous_gramDriftEntry [Fintype c] [DecidableEq c] (D0 : ℝ) (D : Matrix c c ℂ) (e : Fin 2 × c × c) :
    Continuous (gramDriftEntry D0 D e) := by
  unfold gramDriftEntry gramScalar
  split_ifs
  · exact continuous_const
  · fun_prop

omit [Fintype F] [DecidableEq F] in
theorem continuous_gramCovEntry [Fintype c] [DecidableEq c] (D0 : ℝ) (D : Matrix c c ℂ) (e e' : Fin 2 × c × c) :
    Continuous (gramCovEntry D0 D e e') := by
  rcases e with ⟨e1, a, b⟩; rcases e' with ⟨e2, a', b'⟩
  unfold gramCovEntry crossedBracket gramC0 gramC1 gramC2
  fin_cases e1 <;> fin_cases e2 <;> simp only <;> fun_prop

omit [Fintype F] [DecidableEq F] in
theorem continuous_gramEntry (e : Fin 2 × c × c) : Continuous (gramEntry (c := c) e) := by
  unfold gramEntry
  split_ifs
  · exact (continuous_fst.matrix_elem _ _)
  · exact (continuous_snd.matrix_elem _ _)

/-- The birth pattern `{f : β_f ≤ u}`. -/
def pattern (β : F → ℝ) (u : ℝ) : Finset F := Finset.univ.filter fun f => β f ≤ u

omit [DecidableEq F] in
theorem birthSum_eq_pattern (j : F → GramState c) (β : F → ℝ) (u : ℝ) :
    birthSum j β u = ∑ f ∈ pattern β u, j f := by
  simp only [birthSum, pattern, Finset.sum_filter]

theorem integrand_split (f : GramState c → ℂ) (j : F → GramState c) (A : GramState c)
    (β : F → ℝ) (u : ℝ) :
    f (A + birthSum j β u) =
      ∑ S : Finset F, (if pattern β u = S then (1 : ℂ) else 0) * f (A + ∑ g ∈ S, j g) := by
  rw [Finset.sum_eq_single (pattern β u) (fun S _ hS => by simp [Ne.symm hS]) (by simp)]
  simp [birthSum_eq_pattern]

/-- **Joint measurability of a born integrand** (any σ-algebra on `Ω'`). -/
theorem measurable_uncurry_split {Ω' : Type*} {m : MeasurableSpace Ω'} {f : GramState c → ℂ}
    (j : F → GramState c) {A : ℝ → Ω' → GramState c} {β : F → Ω' → ℝ} {τ : ℝ → ℝ}
    (hA : ∀ ω, Continuous fun s => A s ω) (hf : Continuous f)
    (hAm : ∀ (S : Finset F) s, Measurable fun ω => f (A s ω + ∑ g ∈ S, j g))
    (hβ : ∀ g, Measurable (β g)) (hτ : Measurable τ) :
    Measurable (Function.uncurry fun s ω => f (A s ω + birthSum j (fun g => β g ω) (τ s))) := by
  have e : (Function.uncurry fun s ω => f (A s ω + birthSum j (fun g => β g ω) (τ s))) =
      fun p : ℝ × Ω' => ∑ S : Finset F, (if pattern (fun g => β g p.2) (τ p.1) = S then (1 : ℂ)
        else 0) * f (A p.1 p.2 + ∑ g ∈ S, j g) := by
    funext p; exact integrand_split f j _ _ _
  rw [e]
  refine Finset.measurable_sum _ fun S _ => Measurable.mul ?_ ?_
  · refine Measurable.ite ?_ measurable_const measurable_const
    have : {p : ℝ × Ω' | pattern (fun g => β g p.2) (τ p.1) = S} =
        ⋂ g, {p : ℝ × Ω' | β g p.2 ≤ τ p.1 ↔ g ∈ S} := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter, pattern, Finset.ext_iff, Finset.mem_filter,
        Finset.mem_univ, true_and]
    rw [this]
    refine MeasurableSet.iInter fun g => ?_
    have h1 : MeasurableSet {p : ℝ × Ω' | β g p.2 ≤ τ p.1} :=
      measurableSet_le ((hβ g).comp measurable_snd) (hτ.comp measurable_fst)
    by_cases hg : g ∈ S
    · simpa [hg] using h1
    · convert h1.compl using 1
      ext p; simp [hg]
  · exact measurable_uncurry_of_continuous_of_measurable
      (u := fun s ω => f (A s ω + ∑ g ∈ S, j g))
      (fun ω => hf.comp ((hA ω).add continuous_const)) (hAm S)

/-- **Born integrands are interval integrable along every path.** -/
theorem intervalIntegrable_path {f : GramState c → ℂ} (hf : Continuous f) (j : F → GramState c)
    {A : ℝ → GramState c} (hA : Continuous A) (β : F → ℝ) {τ : ℝ → ℝ} (hτ : Measurable τ)
    (a b : ℝ) : IntervalIntegrable (fun s => f (A s + birthSum j β (τ s))) volume a b := by
  have hm : Measurable fun s => f (A s + birthSum j β (τ s)) := by
    have h := measurable_uncurry_split (Ω' := Unit) (m := ⊤) (f := f) j (A := fun s _ => A s)
      (β := fun g _ => β g) (fun _ => hA) hf (fun _ _ => measurable_const)
      (fun _ => measurable_const) hτ
    exact h.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : ℝ => ()))
  have hK : IsCompact (uIcc a b) := isCompact_uIcc
  have hB : ∀ S : Finset F, ∃ C, ∀ s ∈ uIcc a b, ‖f (A s + ∑ g ∈ S, j g)‖ ≤ C := fun S =>
    hK.exists_bound_of_continuousOn (hf.comp (hA.add continuous_const)).continuousOn
  choose C hC using hB
  refine intervalIntegrable_iff.2 (IntegrableOn.of_bound measure_Ioc_lt_top
    hm.aestronglyMeasurable (∑ S, |C S|) ?_)
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
  have hs' : s ∈ uIcc a b := uIoc_subset_uIcc hs
  rw [birthSum_eq_pattern]
  exact (hC _ s hs').trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun S => |C S|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)))

/-- **Continuity of the time integral along a born path.** -/
theorem continuous_integral_path {f : GramState c → ℂ} (hf : Continuous f) (j : F → GramState c)
    {G : ℝ≥0 → GramState c} (β : F → ℝ) (hc : Continuous fun t : ℝ≥0 => G t - birthSum j β t) :
    Continuous fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, f (G s.toNNReal) := by
  set A : ℝ → GramState c := fun s => G s.toNNReal - birthSum j β (s.toNNReal : ℝ)
  have hA : Continuous A := hc.comp continuous_real_toNNReal
  have e : (fun s : ℝ => f (G s.toNNReal)) =
      fun s => f (A s + birthSum j β ((s.toNNReal : ℝ))) := by
    funext s; simp only [A, sub_add_cancel]
  have hint : ∀ a b, IntervalIntegrable (fun s => f (G s.toNNReal)) volume a b := fun a b => by
    rw [e]
    exact intervalIntegrable_path hf j hA β (NNReal.continuous_coe.comp
      continuous_real_toNNReal).measurable a b
  have hp := intervalIntegral.continuous_primitive hint 0
  refine (hp.comp NNReal.continuous_coe).congr fun t => ?_
  exact intervalIntegral.integral_of_le (NNReal.coe_nonneg t)

end BlockBand.SourceProcess.ClosedLimit
