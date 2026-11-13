module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularSigma
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularEuler

/-!
# The eigenvalue path is a functional of `(λ_0, W)` up to null sets

The strong-solution property of the eigenvalue SDE of the vector Dyson Brownian motion, used for
the conditional angular martingale problem clause of `DysonBrownianMotion`.

`Hyp.aesm_lam`: for every `v`, the eigenvalues `λ(F + G_{s+v})` are a.e. equal to a function
measurable for `𝓕_0 ⊔ σ(W)` (`sigB`), where `W = λ - ∫ b(λ)`: on every non-collision sample the
Euler scheme driven by the increments of `W` converges to `λ_v` (`euler_tendsto`), and the
scheme is `σ(W)`-measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale (rgrid)

variable {N : ℕ} {Ω : Type}

theorem measurable_euler {m : MeasurableSpace Ω} {w : ℕ → Ω → Fin N → ℝ}
    (hw : ∀ j, Measurable[m] (w j)) (h : ℝ) :
    ∀ j, Measurable[m] fun ω => euler N (fun k => w k ω) h j
  | 0 => hw 0
  | j + 1 => by
    have ih := measurable_euler hw h j
    exact ((ih.add ((hw (j + 1)).sub (hw j))).add
      ((measurable_bv.comp ih).const_smul h))

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0}
  {f : (Fin N → ℝ) → ℝ} {n : ℕ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
theorem Wp_eq (q : Fin N → ℂ) (r : ℝ) (hr : 0 ≤ r) (ω : Ω) (i : Fin N) :
    Wp (Yst N q G F s) r.toNNReal ω i = lamOf (Yst N q G F s r.toNNReal ω) i -
      ∫ x in Ioc 0 r, bv N (lamOf (Yst N q G F s x.toNNReal ω)) i := by
  simp only [Wp, phase, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Real.coe_toNNReal _ hr, bv]

omit [IsProbabilityMeasure Q] in
theorem euler_lam_tendsto (hG : IsHermitianBrownian Q 𝓖 N G) (hs : 0 < s) {ω : Ω}
    (hω : NoCollision N G F ω) (q : Fin N → ℂ) (v : ℝ≥0) :
    Tendsto (fun K : ℕ => euler N (fun j => Wp (Yst N q G F s) (rgrid 0 v K j).toNNReal ω)
      ((v : ℝ) / (K + 1)) (K + 1)) atTop (𝓝 (lamOf (Yst N q G F s v ω))) := by
  set lam : ℝ → Fin N → ℝ := fun r => lamOf (Yst N q G F s r.toNNReal ω)
  have hp : Continuous fun r : ℝ => F ω + G (s + r.toNNReal) ω :=
    (continuous_hermBM_add hG F ω).comp (continuous_const.add continuous_real_toNNReal)
  have hpos : ∀ r : ℝ, HasSimpleSpectrum N (F ω + G (s + r.toNNReal) ω) := fun r =>
    hω _ (add_pos_of_pos_of_nonneg hs zero_le)
  have hst : Continuous fun r : ℝ => Yst N q G F s r.toNNReal ω :=
    (continuousOn_dysonState q).comp_continuous hp hpos
  have hlam : Continuous lam :=
    continuous_pi fun i => (continuous_apply _).comp hst
  have hd : ∀ r ∈ Icc (0 : ℝ) v, ∀ i j, i ≠ j → lam r i ≠ lam r j := fun r _ i j hij => by
    have := dysonState_distinct (hpos r) q i j hij
    simpa [lam, lamOf_eq, Yst] using this
  have hbc : Continuous fun r => bv N (lam r) := by
    refine continuous_pi fun i => ?_
    have := (continuous_apply (finSumFinEquiv (Sum.inl i))).comp
      (continuous_drift_path hG hs hω q)
    refine this.congr fun r => ?_
    simp only [Function.comp, dysonStateDrift_inl, bv, lam, lamOf_eq, Yst]
    simp
  have h := euler_tendsto (lam := lam) (W := fun r => Wp (Yst N q G F s) r.toNNReal ω)
    (u := v) v.2 hlam.continuousOn hd hbc.continuousOn
    (fun r hr i => Wp_eq q r hr.1 ω i)
  simpa [lam] using h

omit [IsProbabilityMeasure Q] in
theorem Hyp.aesm_lam (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (v : ℝ≥0) :
    AEStronglyMeasurable[sigB (shiftFiltration 𝓖 s 0) (Yst N q G F s)]
      (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) Q := by
  have hW : ∀ t, Measurable[sigB (shiftFiltration 𝓖 s 0) (Yst N q G F s)]
      (Wp (Yst N q G F s) t) := fun t =>
    (comap_measurable (Wp (Yst N q G F s) t)).mono
      (le_sup_of_le_right (le_iSup (fun t => MeasurableSpace.comap (Wp (Yst N q G F s) t)
        inferInstance) t)) le_rfl
  have hE : ∀ K : ℕ, AEStronglyMeasurable[sigB (shiftFiltration 𝓖 s 0) (Yst N q G F s)]
      (fun ω => euler N (fun j => Wp (Yst N q G F s) (rgrid 0 v K j).toNNReal ω)
        ((v : ℝ) / (K + 1)) (K + 1)) Q := fun K =>
    (measurable_euler (w := fun j => Wp (Yst N q G F s) (rgrid 0 v K j).toNNReal)
      (fun j => hW _) _ _).stronglyMeasurable.aestronglyMeasurable
  refine Semimartingale.aestronglyMeasurable_of_tendsto_ae_sub hE ?_
  filter_upwards [H.hb1] with ω hω
  have := euler_lam_tendsto H.hG H.hs hω q v
  rwa [Yst, lamOf_dysonState] at this

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
