module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularStrong
public import BlockBand.SourceProcess.Stochastic.Dyson.Assembly

/-!
# Clause: the conditional angular martingale problem

`dysonAngular_of_b1 : DysonNonCollision N → DysonAngular N`. For `s > 0`, `q`, `n > 0`,
`f ∈ C²`, `u`, and bounded `Λ` measurable for `σ(λ(F + G_{s+v}) : v ≥ 0)`:
`E[Λ (f(X_{u∧σ_n}) - f(X_0) - ∫_0^{u∧σ_n} 𝒜_v f(X_v) dv)] = 0`, the integrand being integrable.

Route (no eigenvector process, no enlarged-filtration stochastic integral):
1. contract (b2) + Itô (a1) + stopping (a2) on the augmented state `(λ, X, ∫θ·b, ∫𝒜f, t)`:
   `e^{|θ|²u/(2N)} e^{iθ·W_u}` and its product with `Ms = (f(X) - ∫𝒜f)^{σ_n}` are martingales
   (`W = λ - ∫ b(λ)`; zero Itô drift uses the zero `λ`–`X` covariance of (b2) and the generator
   identity `angularGenerator_eq`), the part after `σ_n` by optional sampling;
2. induction over finite time sets and uniqueness of characteristic functions:
   `E[1_S (Ms_u - Ms_0)] = 0` for `S ∈ 𝓕_0 ⊔ σ(W)` (`Hyp.orth_sigma`);
3. strong-solution property (deterministic Euler scheme, non-collision (b1)): each `λ_v` is
   a.e. `𝓕_0 ⊔ σ(W)`-measurable (`Hyp.aesm_lam`);
4. conditional expectation on the σ-algebra of sets a.e. equal to `𝓕_0 ⊔ σ(W)`-sets.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)

section Generic
variable {Ω : Type*}

/-- Sets (`m₀`-measurable and) a.e. equal to `m`-measurable sets. -/
abbrev aeClosure (m₀ m : MeasurableSpace Ω) (Q : Measure[m₀] Ω) : MeasurableSpace Ω where
  MeasurableSet' S := MeasurableSet[m₀] S ∧ ∃ S', MeasurableSet[m] S' ∧ S =ᵐ[Q] S'
  measurableSet_empty := ⟨@MeasurableSet.empty _ m₀, ∅, @MeasurableSet.empty _ m, EventuallyEq.rfl⟩
  measurableSet_compl _ hS := ⟨hS.1.compl, hS.2.choose ᶜ, hS.2.choose_spec.1.compl,
    hS.2.choose_spec.2.compl⟩
  measurableSet_iUnion _ hf := ⟨MeasurableSet.iUnion fun i => (hf i).1,
    ⋃ i, (hf i).2.choose, MeasurableSet.iUnion fun i => (hf i).2.choose_spec.1,
    EventuallyEqSet.countable_iUnion fun i => (hf i).2.choose_spec.2⟩

theorem comap_le_aeClosure {m₀ m : MeasurableSpace Ω} {Q : Measure[m₀] Ω} {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] {g : Ω → E}
    (hg : Measurable[m₀] g) (hgm : AEStronglyMeasurable[m] g Q) :
    MeasurableSpace.comap g inferInstance ≤ aeClosure m₀ m Q := by
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨g', hg'm, hgg'⟩ := hgm
  exact ⟨hg hB, g' ⁻¹' B, hg'm.measurable hB, hgg'.preimage B⟩

/-- `E[Λ D] = 0` for bounded `aeClosure m`-measurable `Λ` when `D` integrates to zero on every
`m`-measurable set. -/
theorem integral_mul_eq_zero_of_aeClosure {m₀ m : MeasurableSpace Ω} {Q : Measure[m₀] Ω}
    [IsFiniteMeasure Q] {D : Ω → ℝ} (hD : Integrable D Q)
    (hD0 : ∀ S, MeasurableSet[m] S → ∫ ω in S, D ω ∂Q = 0)
    {Λ : Ω → ℝ} (hΛ : StronglyMeasurable[aeClosure m₀ m Q] Λ) {C : ℝ} (hC : ∀ ω, |Λ ω| ≤ C) :
    ∫ ω, Λ ω * D ω ∂Q = 0 := by
  have hle : aeClosure m₀ m Q ≤ m₀ := fun _ hS => hS.1
  have hΛD : Integrable (Λ * D) Q :=
    hD.bdd_mul (hΛ.mono hle).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  have h0 : (0 : Ω → ℝ) =ᵐ[Q] Q[D | aeClosure m₀ m Q] :=
    ae_eq_condExp_of_forall_setIntegral_eq hle hD (fun _ _ _ => integrableOn_zero)
      (fun S ⟨_, S', hS', hSS'⟩ _ => by
        rw [setIntegral_congr_set (f := D) hSS', hD0 S' hS']; simp)
      aestronglyMeasurable_zero
  have h1 := condExp_mul_of_stronglyMeasurable_left hΛ hΛD hD
  rw [show (fun ω => Λ ω * D ω) = Λ * D from rfl, ← integral_condExp hle, integral_congr_ae h1]
  have : (fun ω => (Λ * Q[D | aeClosure m₀ m Q]) ω) =ᵐ[Q] fun _ => (0 : ℝ) := by
    filter_upwards [h0] with ω hω
    simp [← hω]
  rw [integral_congr_ae this]; simp

end Generic

variable {N : ℕ} {Ω : Type} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
  {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- The contract's stopped angular process is `Dp`. -/
theorem contract_eq (q : Fin N → ℂ) (s : ℝ≥0) (n : ℕ) (f : (Fin N → ℝ) → ℝ) (u : ℝ≥0)
    (ω : Ω) :
    stoppedProcess (fun v ω =>
        f (fun i => dysonOverlap N q (F ω + G (s + v) ω) i) -
        f (fun i => dysonOverlap N q (F ω + G s ω) i) -
        ∫ r in Ioc (0 : ℝ) v, angularGenerator N
          (dysonEigenvalue N (F ω + G (s + r.toNNReal) ω)) f
          (fun i => dysonOverlap N q (F ω + G (s + r.toNNReal) ω) i))
      (gapStop N (fun t ω => F ω + G t ω) s n) u ω =
      Dp f (Yst N q G F s) (sig N G F s n) u ω := by
  have h0 : ∀ τ : WithTop ℝ≥0, stopTime τ 0 = 0 := fun τ =>
    le_antisymm (BlockBand.SourceProcess.Stochastic.Semimartingale.stopTime_le τ 0) zero_le
  simp only [stoppedProcess_eq_stopTime, Dp, Mt, Yst, xOf_dysonState, lamOf_dysonState, h0,
    add_zero, NNReal.coe_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure, sub_zero]
  ring

end BlockBand.SourceProcess.Stochastic.Dyson.Angular

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission Angular

/-- **Clause (b3) of `DysonBrownianMotion` from clause (b1).** -/
theorem dysonAngular_of_b1 (N : ℕ) (h1 : DysonNonCollision N) : DysonAngular N := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh s hs q n hn f hf u Λ hΛ hΛb
  have H : Hyp Q 𝓖 N G F s f n := ⟨hG, hF, hFh, h1 Ω Q 𝓖 G F hG hF hFh, hs, hf, hn⟩
  obtain ⟨C, hC⟩ := hΛb
  simp only [contract_eq]
  have hmle : sigB (shiftFiltration 𝓖 s 0) (Yst N q G F s) ≤ (inferInstance : MeasurableSpace Ω) := by
    refine sup_le ((shiftFiltration 𝓖 s).le 0) (iSup_le fun t => ?_)
    exact (H.measurable_Wp q t).comap_le
  have hlam : ∀ v : ℝ≥0, Measurable fun ω => dysonEigenvalue N (F ω + G (s + v) ω) := fun v =>
    (measurable_pi_iff.2 fun i => measurable_dysonEigenvalue i).comp
      ((measurable_hermBM_add hG hF (s + v)).mono ((𝓖).le (s + v)) le_rfl)
  have hsig : (⨆ v : ℝ≥0, MeasurableSpace.comap
      (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) inferInstance) ≤
      aeClosure inferInstance (sigB (shiftFiltration 𝓖 s 0) (Yst N q G F s)) Q :=
    iSup_le fun v => comap_le_aeClosure (hlam v) (H.aesm_lam q v)
  have hΛm : StronglyMeasurable[aeClosure inferInstance
      (sigB (shiftFiltration 𝓖 s 0) (Yst N q G F s)) Q] Λ :=
    (hΛ.mono hsig le_rfl).stronglyMeasurable
  have hD := H.integrable_D (f := f) q u
  refine ⟨hD.bdd_mul ((hΛm.mono fun _ hS => hS.1).aestronglyMeasurable)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω), ?_⟩
  exact integral_mul_eq_zero_of_aeClosure hD (fun S hS => H.orth_sigma q u hS) hΛm hC

end BlockBand.SourceProcess.Stochastic.Dyson
