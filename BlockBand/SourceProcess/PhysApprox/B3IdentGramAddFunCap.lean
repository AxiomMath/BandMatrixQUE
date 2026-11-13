module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramAddFun
public import BlockBand.SourceProcess.PhysApprox.B3FddCoord
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramOff

/-!
# Additive functionals under fdd convergence on the conditioned closed process

The conditioned fdd limit `IsCapFddLimitAll` is put in the format of `FddConvOff`, so that
`fddConvOff_augProc` applies to the closed process.

* **`fddConvOff_of_isCapFddLimitAll`**: `IsCapFddLimitAll` is `FddConvOff (birthTimes s τ)` for
  `condL`, `b3ObsAll` and `complexObs` (via `Fdd.condObsTestAll_eq`).
* `eventually_isProbabilityMeasure_condL`: `condL` is eventually a probability measure once the
  cap masses are eventually nonzero.
* `measurable_uncurry_b3ObsAll` (from `Modul.measurable_b3X`, `hV : Measurable Vs`) and
  `measurable_uncurry_complexObs` (from `IsCapLimitData`: every-`ω` continuity of `G − gramJ`,
  `Kc − kJ` and the step jumps): joint measurability in `(u, ω)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.AddFun

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ}

/-- **`IsCapFddLimitAll` in the format of `FddConvOff`.** -/
theorem fddConvOff_of_isCapFddLimitAll (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {φ : ℕ → ℕ}
    {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
    {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}
    (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc) :
    FddConvOff (IdentGram.birthTimes s τ) (fun n => Fdd.condL b E s h K (φ n) np)
      (fun n => b3ObsAll b E s h τ m (φ n) (Vs (φ n))) Q (complexObs tseq G Kc) := by
  intro ι _ i u hu ψ
  exact (hF ι i u (fun l j hj => hu l ⟨j, hj⟩) ψ).congr fun n =>
    Fdd.condObsTestAll_eq hb hE1 hE2 s h τ m (Vs (φ n)) i u ψ

theorem eventually_isProbabilityMeasure_condL (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {φ : ℕ → ℕ}
    (h0 : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0) :
    ∀ᶠ n in atTop, IsProbabilityMeasure (Fdd.condL b E s h K (φ n) np) :=
  h0.mono fun _ hn => Fdd.isProbabilityMeasure_condL hb hE1 hE2 hn

/-- **Joint measurability of the finite-`W` observables.** -/
theorem measurable_uncurry_b3ObsAll {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (l : LIdx K np) : Measurable (Function.uncurry (b3ObsAll b E s h τ m W Vs l)) := by
  have hn : Measurable fun u : ℝ≥0 => limLenAll s W u :=
    (measurable_const.mul (measurable_const.add measurable_coe_nnreal_real)).nat_floor
  have hL : Measurable fun p : ℝ≥0 × (ProbedPath W np × ℝ) => (p.2, limLenAll s W p.1) :=
    measurable_snd.prodMk (hn.comp measurable_fst)
  rcases l with e | k | ij
  · have e1 : Function.uncurry (b3ObsAll b E s h τ m W Vs (Sum.inl e)) =
        fun p => b3X b E s h τ m W (limLenAll s W p.1) Vs (Sum.inl e) p.2 := by
      funext p
      simp only [Function.uncurry, b3ObsAll, b3X, cEntry]
    rw [e1]
    have h1 : ∀ n : ℕ, Measurable fun y : ProbedPath W np × ℝ =>
        b3X b E s h τ m W n Vs (Sum.inl e) y := fun n => Modul.measurable_b3X s h τ m hV (Sum.inl e)
    have h2 : Measurable fun q : (ProbedPath W np × ℝ) × ℕ =>
        b3X b E s h τ m W q.2 Vs (Sum.inl e) q.1 := measurable_from_prod_countable_left h1
    have h3 := h2.comp hL
    clear h1 h2 e1
    exact h3
  · exact (Complex.measurable_ofReal.comp ((CapLaw.measurable_physTseq b E s W k).comp
      (measurable_fst.comp measurable_fst))).comp measurable_snd
  · have e1 : Function.uncurry (b3ObsAll b E s h τ m W Vs (Sum.inr (Sum.inr ij))) =
        fun p => b3X b E s h τ m W (limLenAll s W p.1) Vs (Sum.inr ij) p.2 := by
      funext p
      simp only [Function.uncurry, b3ObsAll, b3X, cEntry]
    rw [e1]
    have h1 : ∀ n : ℕ, Measurable fun y : ProbedPath W np × ℝ =>
        b3X b E s h τ m W n Vs (Sum.inr ij) y := fun n => Modul.measurable_b3X s h τ m hV (Sum.inr ij)
    have h2 : Measurable fun q : (ProbedPath W np × ℝ) × ℕ =>
        b3X b E s h τ m W q.2 Vs (Sum.inr ij) q.1 := measurable_from_prod_countable_left h1
    have h3 := h2.comp hL
    clear h1 h2 e1
    exact h3

theorem stronglyMeasurable_gramJ (b s : ℝ) (τ m : Fin np → ℝ) :
    StronglyMeasurable fun u : ℝ≥0 => gramJ (K := K) b s τ m u := by
  unfold gramJ birthJump
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    StronglyMeasurable.ite (measurableSet_le measurable_const measurable_coe_nnreal_real)
      stronglyMeasurable_const stronglyMeasurable_const

theorem stronglyMeasurable_kJ (E s : ℝ) (τ m : Fin np → ℝ) :
    StronglyMeasurable fun u : ℝ≥0 => kJ E s τ m u := by
  unfold kJ kBirthJump
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    StronglyMeasurable.ite (measurableSet_le measurable_const measurable_coe_nnreal_real)
      stronglyMeasurable_const stronglyMeasurable_const

theorem gramEntry_add (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np))
    (A B : GramState (SrcCol K (Fin np))) :
    gramEntry e (A + B) = gramEntry e A + gramEntry e B := by
  unfold gramEntry
  split_ifs <;> simp

/-- **Joint measurability of the candidate's observables.** -/
theorem measurable_uncurry_complexObs {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {tseq : Ω' → ℕ → ℝ} {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ} (hD : IsCapLimitData b E s τ m K Q tseq G Kc)
    (l : LIdx K np) : Measurable (Function.uncurry (complexObs tseq G Kc l)) := by
  obtain ⟨_, htm, hG, hK, hGc, hKc⟩ := hD
  rcases l with e | k | ij
  · have hJ : Measurable fun u : ℝ≥0 => gramEntry e (gramJ (K := K) b s τ m u) :=
      ((continuous_gramEntry e).comp_stronglyMeasurable
        (stronglyMeasurable_gramJ b s τ m)).measurable
    have hC : Measurable (Function.uncurry fun u ω => gramEntry e (G u ω - gramJ b s τ m u)) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => (continuous_gramEntry e).comp (hGc ω))
        (fun u => ((continuous_gramEntry e).comp_stronglyMeasurable
          ((hG u).sub stronglyMeasurable_const)).measurable)
    have e1 : Function.uncurry (complexObs tseq G Kc (Sum.inl e)) = fun p =>
        gramEntry e (G p.1 p.2 - gramJ b s τ m p.1) + gramEntry e (gramJ b s τ m p.1) := by
      funext p
      simp only [Function.uncurry, complexObs]
      rw [← gramEntry_add, sub_add_cancel]
    rw [e1]
    exact hC.add (hJ.comp measurable_fst)
  · exact (Complex.measurable_ofReal.comp (measurable_pi_iff.1 htm k)).comp measurable_snd
  · have hJ : Measurable fun u : ℝ≥0 => kJ E s τ m u ij.1 ij.2 :=
      ((continuous_id.matrix_elem ij.1 ij.2).comp_stronglyMeasurable
        (stronglyMeasurable_kJ E s τ m)).measurable
    have hC : Measurable (Function.uncurry fun u ω => (Kc u ω - kJ E s τ m u) ij.1 ij.2) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => (continuous_id.matrix_elem ij.1 ij.2).comp (hKc ω))
        (fun u => ((continuous_id.matrix_elem ij.1 ij.2).comp_stronglyMeasurable
          ((hK u).sub stronglyMeasurable_const)).measurable)
    have e1 : Function.uncurry (complexObs tseq G Kc (Sum.inr (Sum.inr ij))) = fun p =>
        (Kc p.1 p.2 - kJ E s τ m p.1) ij.1 ij.2 + kJ E s τ m p.1 ij.1 ij.2 := by
      funext p
      simp only [Function.uncurry, complexObs, Matrix.sub_apply, sub_add_cancel]
    rw [e1]
    exact hC.add (hJ.comp measurable_fst)

end BlockBand.SourceProcess.PhysApprox.B3.AddFun
