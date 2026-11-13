module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramStop

/-!
# The Gram identities from cutoff generator martingales

The stop is removed from the limit passage. For a `C³` cutoff `χ` with compact support, set
`Y = G − J`, `s(Y) = Re Tr Y_M`, the cut drift `A^χ_e(t) = ∫_0^t b_e(G) χ(s(Y))`, and
`x_e = Y_e − Y_e(0) − A^χ_e`. The processes
* `genM1 χ e = χ(s(Y_0)) χ(s(Y_t)) x_e(t) − ∫_0^t lam1`,
* `genM2 χ e e' = χ(s(Y_0)) χ(s(Y_t)) x_e(t) x_{e'}(t) − ∫_0^t lam2`
are Itô's formula for `χ(s(Y_0)) χ(s(Y)) x_e` and `χ(s(Y_0)) χ(s(Y)) x_e x_{e'}` (generators
`lam1`, `lam2`; `d s = Σ_k dY_{(0,k,k)}`, real since `M` is Hermitian). They are bounded (on the
feasible set) and are functionals of the observables at finitely many times and of time
integrals of them: their tested identities need only fdd convergence (no stop functional).

Measure: the candidate's `Q`; filtration: the raw natural filtration of `complexObs`.

* Continuity for every `ω` (`continuous_genProc`, from the every-`ω` continuity of `G − gramJ`)
  and a.s. bounds on every `[0, T]` (`exists_bound_genProc`, from a.s. feasibility).
* Before `σ_L` and for `χ = 1` near `[−R, R]`, `R ≥ |L| + |Tr J|`: `genM1 = cComp`,
  `genM2 = cBr` (`genM1_eq_cComp`, `genM2_eq_cBr`).
* **Hypothesis `CapIdentGramGen`**: under `CapIdentPremise`, for every such `χ`, `genM1` and `genM2`
  have tested increments off the birth times.
* **`capIdentGram_of_gen : CapIdentGramGen → CapIdentGram`** (every level `L`): off the birth times
  to all times (`isTestedMart_of_off`), optional stopping at an a.s. version of `σ_L`
  (`isTestedMart_stoppedProcess_of_tested`), then `genM^{σ_L} = cComp^{σ_L}` a.s.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

variable {K np : ℕ}

/-- Gram coordinates. -/
abbrev GIdx (K np : ℕ) := Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)

/-- Gram states. -/
abbrev GSt (K np : ℕ) := GramState (SrcCol K (Fin np))

/-- The state `(Y_t, x(t), Y_0)` of the generator processes. -/
abbrev ZSt (K np : ℕ) := GSt K np × (GIdx K np → ℂ) × GSt K np

/-!
## Coefficients
-/

instance instPseudoMetrizableMatrix {c : Type*} [Fintype c] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix c c ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → c → ℂ))

/-- `Re Tr M`. -/
def trRe (y : GSt K np) : ℝ := (y.1.trace).re

def drE (b E : ℝ) (e : GIdx K np) (H : GSt K np) : ℂ :=
  gramDriftEntry (transportD0 b E) (srcSignature K (Fin np)) e H

def cvE (b E : ℝ) (e e' : GIdx K np) (H : GSt K np) : ℂ :=
  gramCovEntry (transportD0 b E) (srcSignature K (Fin np)) e e' H

def trDr (b E : ℝ) (H : GSt K np) : ℂ := ∑ k : SrcCol K (Fin np), drE b E (0, k, k) H

def trCv (b E : ℝ) (e : GIdx K np) (H : GSt K np) : ℂ :=
  ∑ k : SrcCol K (Fin np), cvE b E (0, k, k) e H

def trTr (b E : ℝ) (H : GSt K np) : ℂ :=
  ∑ k : SrcCol K (Fin np), ∑ k' : SrcCol K (Fin np), cvE b E (0, k, k) (0, k', k') H

/-- The cutoff `f(s(y))` as a complex number. -/
def cutC (f : ℝ → ℝ) (y : GSt K np) : ℂ := (f (trRe y) : ℂ)

@[fun_prop] theorem continuous_trRe : Continuous (trRe (K := K) (np := np)) :=
  Complex.continuous_re.comp (continuous_fst.matrix_trace)

@[fun_prop] theorem continuous_drE (b E : ℝ) (e : GIdx K np) : Continuous (drE b E e) :=
  ClosedLimit.continuous_gramDriftEntry _ _ e

@[fun_prop] theorem continuous_cvE (b E : ℝ) (e e' : GIdx K np) : Continuous (cvE b E e e') :=
  ClosedLimit.continuous_gramCovEntry _ _ e e'

@[fun_prop] theorem continuous_trDr (b E : ℝ) : Continuous (trDr (K := K) (np := np) b E) :=
  continuous_finsetSum _ fun _ _ => continuous_drE b E _

@[fun_prop] theorem continuous_trCv (b E : ℝ) (e : GIdx K np) : Continuous (trCv b E e) :=
  continuous_finsetSum _ fun _ _ => continuous_cvE b E _ _

@[fun_prop] theorem continuous_trTr (b E : ℝ) : Continuous (trTr (K := K) (np := np) b E) :=
  continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_cvE b E _ _

@[fun_prop] theorem continuous_cutC {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (cutC (K := K) (np := np) f) :=
  Complex.continuous_ofReal.comp (hf.comp continuous_trRe)

/-!
## The generator processes
-/

variable {Ω : Type*}

/-- `Y = G − J`. -/
def gY (b s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np) (u : ℝ≥0) (ω : Ω) : GSt K np :=
  G u ω - gramJ b s τ m u

/-- The cut drift integrand `b_e(y + J) χ(s(y))` at `(J, y)`. -/
def lamA (χ : ℝ → ℝ) (b E : ℝ) (e : GIdx K np) (p : GSt K np × GSt K np) : ℂ :=
  drE b E e (p.2 + p.1) * cutC χ p.2

/-- The cut drift `A^χ_e(t) = ∫_0^t b_e(G) χ(s(Y))`. -/
def genA (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np) (e : GIdx K np)
    (t : ℝ≥0) (ω : Ω) : ℂ :=
  ∫ u in Ioc (0 : ℝ) t, lamA χ b E e (gramJ b s τ m u.toNNReal, gY b s τ m G u.toNNReal ω)

/-- `x_e = Y_e − Y_e(0) − A^χ_e`. -/
def genX (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np) (e : GIdx K np)
    (t : ℝ≥0) (ω : Ω) : ℂ :=
  gramEntry e (gY b s τ m G t ω) - gramEntry e (gY b s τ m G 0 ω) - genA χ b E s τ m G e t ω

/-- The state `(Y_t, x(t), Y_0)`. -/
def stZ (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np) (t : ℝ≥0)
    (ω : Ω) : ZSt K np :=
  (gY b s τ m G t ω, fun e => genX χ b E s τ m G e t ω, gY b s τ m G 0 ω)

/-- The test function `χ(s(Y_0)) χ(s(Y)) x_e`. -/
def fun1 (χ : ℝ → ℝ) (e : GIdx K np) (z : ZSt K np) : ℂ :=
  cutC χ z.2.2 * cutC χ z.1 * z.2.1 e

/-- Its generator at `(J, (y, x, y_0))`, `H = y + J`. -/
def lam1 (χ : ℝ → ℝ) (b E : ℝ) (e : GIdx K np) (p : GSt K np × ZSt K np) : ℂ :=
  cutC χ p.2.2.2 *
    (cutC (deriv χ) p.2.1 * trDr b E (p.2.1 + p.1) * p.2.2.1 e +
      cutC χ p.2.1 * (drE b E e (p.2.1 + p.1) - drE b E e (p.2.1 + p.1) * cutC χ p.2.1) +
      cutC (deriv χ) p.2.1 * trCv b E e (p.2.1 + p.1) +
      (1 / 2 : ℂ) * cutC (deriv (deriv χ)) p.2.1 * trTr b E (p.2.1 + p.1) * p.2.2.1 e)

/-- The test function `χ(s(Y_0)) χ(s(Y)) x_e x_{e'}`. -/
def fun2 (χ : ℝ → ℝ) (e e' : GIdx K np) (z : ZSt K np) : ℂ :=
  cutC χ z.2.2 * cutC χ z.1 * z.2.1 e * z.2.1 e'

/-- Its generator. -/
def lam2 (χ : ℝ → ℝ) (b E : ℝ) (e e' : GIdx K np) (p : GSt K np × ZSt K np) : ℂ :=
  cutC χ p.2.2.2 *
    (cutC (deriv χ) p.2.1 * trDr b E (p.2.1 + p.1) * p.2.2.1 e * p.2.2.1 e' +
      cutC χ p.2.1 * ((drE b E e (p.2.1 + p.1) - drE b E e (p.2.1 + p.1) * cutC χ p.2.1) *
          p.2.2.1 e' +
        p.2.2.1 e * (drE b E e' (p.2.1 + p.1) - drE b E e' (p.2.1 + p.1) * cutC χ p.2.1)) +
      cutC χ p.2.1 * cvE b E e e' (p.2.1 + p.1) +
      cutC (deriv χ) p.2.1 * (trCv b E e (p.2.1 + p.1) * p.2.2.1 e' +
        p.2.2.1 e * trCv b E e' (p.2.1 + p.1)) +
      (1 / 2 : ℂ) * cutC (deriv (deriv χ)) p.2.1 * trTr b E (p.2.1 + p.1) * p.2.2.1 e *
        p.2.2.1 e')

/-- A generator process `F(Z_t) − ∫_0^t Λ(J_u, Z_u)`. -/
def genProc (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (F : ZSt K np → ℂ) (Λ : GSt K np × ZSt K np → ℂ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  F (stZ χ b E s τ m G t ω) -
    ∫ u in Ioc (0 : ℝ) t, Λ (gramJ b s τ m u.toNNReal, stZ χ b E s τ m G u.toNNReal ω)

/-- **The drift generator process** `genM1 χ e`. -/
def genM1 (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (e : GIdx K np) : ℝ≥0 → Ω → ℂ :=
  genProc χ b E s τ m G (fun1 χ e) (lam1 χ b E e)

/-- **The bracket generator process** `genM2 χ e e'`. -/
def genM2 (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (e e' : GIdx K np) : ℝ≥0 → Ω → ℂ :=
  genProc χ b E s τ m G (fun2 χ e e') (lam2 χ b E e e')

/-!
## Continuity for every `ω`
-/

variable {b E s : ℝ} {τ m : Fin np → ℝ} {G : ℝ≥0 → Ω → GSt K np}

theorem stronglyMeasurable_gramJ_comp (b s : ℝ) (τ m : Fin np → ℝ) :
    StronglyMeasurable fun u : ℝ => gramJ (K := K) b s τ m u.toNNReal := by
  unfold gramJ birthJump
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    StronglyMeasurable.ite (measurableSet_le measurable_const
      (NNReal.continuous_coe.comp continuous_real_toNNReal).measurable)
      stronglyMeasurable_const stronglyMeasurable_const

theorem finite_range_gramJ (b s : ℝ) (τ m : Fin np → ℝ) :
    (Set.range fun t : ℝ≥0 => gramJ (K := K) b s τ m t).Finite := by
  refine (Set.finite_range fun x : Fin np → Bool => (∑ j, if x j then
      ((((dStar b * m j : ℝ) : ℂ) • Matrix.single (Sum.inr j) (Sum.inr j) 1,
        ((dStar b * m j : ℝ) : ℂ) • Matrix.single (Sum.inr j) (Sum.inr j) 1) :
          GramState (SrcCol K (Fin np))) else 0)).subset ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨_, (gramJ_eq_sel b s τ m t).symm⟩

/-- **A primitive along the births is continuous.** -/
theorem continuous_primitive_gramJ {𝒵 : Type*} [TopologicalSpace 𝒵]
    [TopologicalSpace.PseudoMetrizableSpace 𝒵] {Λ : GSt K np × 𝒵 → ℂ} (hΛ : Continuous Λ)
    {Zp : ℝ≥0 → 𝒵} (hZ : Continuous Zp) :
    Continuous fun t : ℝ≥0 =>
      ∫ u in Ioc (0 : ℝ) t, Λ (gramJ b s τ m u.toNNReal, Zp u.toNNReal) := by
  refine continuous_primitive_Ioc ?_ fun T => ?_
  · exact (hΛ.comp_stronglyMeasurable ((stronglyMeasurable_gramJ_comp b s τ m).prodMk
      (hZ.comp continuous_real_toNNReal).stronglyMeasurable)).aestronglyMeasurable
  · obtain ⟨C, hC⟩ := exists_bound_finite_compact hΛ (finite_range_gramJ (K := K) b s τ m)
      ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T.toNNReal)).image hZ)
    refine ⟨C, fun u hu => hC _ ⟨_, rfl⟩ _ ⟨u.toNNReal, ⟨zero_le, ?_⟩, rfl⟩⟩
    exact Real.toNNReal_le_toNNReal hu

section Cont

variable (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
include hc

theorem continuous_genA {χ : ℝ → ℝ} (hχ : Continuous χ) (e : GIdx K np) (ω : Ω) :
    Continuous fun t => genA χ b E s τ m G e t ω := by
  have hl : Continuous (lamA χ b E e) :=
    ((continuous_drE b E e).comp (continuous_snd.add continuous_fst)).mul
      ((continuous_cutC hχ).comp continuous_snd)
  have hZ : Continuous fun u => gY b s τ m G u ω := hc ω
  have h := continuous_primitive_gramJ (K := K) (np := np) (b := b) (s := s) (τ := τ) (m := m)
    (𝒵 := GSt K np) hl hZ
  exact h

theorem continuous_stZ {χ : ℝ → ℝ} (hχ : Continuous χ) (ω : Ω) :
    Continuous fun t => stZ χ b E s τ m G t ω := by
  refine (hc ω).prodMk ((continuous_pi fun e => ?_).prodMk continuous_const)
  exact (((ClosedLimit.continuous_gramEntry e).comp (hc ω)).sub continuous_const).sub
    (continuous_genA hc hχ e ω)

theorem continuous_genProc {χ : ℝ → ℝ} (hχ : Continuous χ) {F : ZSt K np → ℂ}
    {Λ : GSt K np × ZSt K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ) (ω : Ω) :
    Continuous fun t => genProc χ b E s τ m G F Λ t ω :=
  (hF.comp (continuous_stZ hc hχ ω)).sub
    (continuous_primitive_gramJ hΛ (continuous_stZ hc hχ ω))

end Cont

theorem continuous_fun1 {χ : ℝ → ℝ} (hχ : Continuous χ) (e : GIdx K np) :
    Continuous (fun1 χ e) := by
  unfold fun1; fun_prop

theorem continuous_fun2 {χ : ℝ → ℝ} (hχ : Continuous χ) (e e' : GIdx K np) :
    Continuous (fun2 χ e e') := by
  unfold fun2; fun_prop

theorem continuous_lam1 {χ : ℝ → ℝ} (hχ : Continuous χ) (h1 : Continuous (deriv χ))
    (h2 : Continuous (deriv (deriv χ))) (b E : ℝ) (e : GIdx K np) :
    Continuous (lam1 χ b E e) := by
  unfold lam1; fun_prop

theorem continuous_lam2 {χ : ℝ → ℝ} (hχ : Continuous χ) (h1 : Continuous (deriv χ))
    (h2 : Continuous (deriv (deriv χ))) (b E : ℝ) (e e' : GIdx K np) :
    Continuous (lam2 χ b E e e') := by
  unfold lam2; fun_prop

/-!
## The cutoff
-/

theorem cut_continuity {χ : ℝ → ℝ} (h : ContDiff ℝ 3 χ) :
    Continuous χ ∧ Continuous (deriv χ) ∧ Continuous (deriv (deriv χ)) :=
  ⟨h.continuous, h.continuous_deriv (by norm_num),
    ((h.of_le (by norm_num) : ContDiff ℝ (2 + 1) χ).deriv').continuous_deriv (by norm_num)⟩

theorem exists_cut_radius {χ : ℝ → ℝ} (hχ : HasCompactSupport χ) :
    ∃ R : ℝ, ∀ c, R < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0 := by
  obtain ⟨R, hR⟩ := hχ.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun c hc => ?_⟩
  have hn : c ∉ tsupport χ := fun h => by
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  exact ⟨image_eq_zero_of_notMem_tsupport hn,
    image_eq_zero_of_notMem_tsupport fun h => hn (tsupport_deriv_subset h),
    image_eq_zero_of_notMem_tsupport fun h => hn (tsupport_deriv_subset (tsupport_deriv_subset h))⟩

/-- **A smooth cutoff equal to `1` on `(−R, R)`** (a `ContDiffBump`). -/
theorem exists_bump (R : ℝ) (hR : 0 < R) : ∃ χ : ℝ → ℝ, ContDiff ℝ 3 χ ∧ HasCompactSupport χ ∧
    ∀ c, |c| < R → χ c = 1 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0 := by
  let χb : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨χb, χb.contDiff, χb.hasCompactSupport, fun c hc => ?_⟩
  have hU : ∀ y ∈ Metric.ball (0 : ℝ) R, χb y = 1 := fun y hy =>
    χb.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hd : ∀ y ∈ Metric.ball (0 : ℝ) R, deriv χb y = 0 := fun y hy => by
    have h : (χb : ℝ → ℝ) =ᶠ[𝓝 y] fun _ => 1 :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy) hU
    rw [h.deriv_eq]
    exact deriv_const _ _
  have hc' : c ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hc
  refine ⟨hU c hc', hd c hc', ?_⟩
  have h : deriv (χb : ℝ → ℝ) =ᶠ[𝓝 c] fun _ => 0 :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hc') hd
  rw [h.deriv_eq]
  exact deriv_const _ _

/-!
## Vanishing outside the cut region
-/

section Vanish

variable {χ : ℝ → ℝ} {Rχ : ℝ}
  (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
include hR

theorem lamA_ne_zero (b E : ℝ) (e : GIdx K np) {p : GSt K np × GSt K np}
    (h : lamA χ b E e p ≠ 0) : |trRe p.2| ≤ Rχ := by
  by_contra h'
  obtain ⟨h1, -, -⟩ := hR _ (not_le.1 h')
  exact h (by simp [lamA, cutC, h1])

theorem fun1_ne_zero (e : GIdx K np) {z : ZSt K np} (h : fun1 χ e z ≠ 0) :
    |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h'
  · obtain ⟨h1, -, -⟩ := hR _ (not_le.1 h'); exact h (by simp [fun1, cutC, h1])
  · obtain ⟨h1, -, -⟩ := hR _ (not_le.1 h'); exact h (by simp [fun1, cutC, h1])

theorem fun2_ne_zero (e e' : GIdx K np) {z : ZSt K np} (h : fun2 χ e e' z ≠ 0) :
    |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h'
  · obtain ⟨h1, -, -⟩ := hR _ (not_le.1 h'); exact h (by simp [fun2, cutC, h1])
  · obtain ⟨h1, -, -⟩ := hR _ (not_le.1 h'); exact h (by simp [fun2, cutC, h1])

theorem lam1_ne_zero (b E : ℝ) (e : GIdx K np) {p : GSt K np × ZSt K np}
    (h : lam1 χ b E e p ≠ 0) : |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h'
  · obtain ⟨h1, h2, h3⟩ := hR _ (not_le.1 h'); exact h (by simp [lam1, cutC, h1, h2, h3])
  · obtain ⟨h1, -, -⟩ := hR _ (not_le.1 h'); exact h (by simp [lam1, cutC, h1])

theorem lam2_ne_zero (b E : ℝ) (e e' : GIdx K np) {p : GSt K np × ZSt K np}
    (h : lam2 χ b E e e' p ≠ 0) : |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h'
  · obtain ⟨h1, h2, h3⟩ := hR _ (not_le.1 h'); exact h (by simp [lam2, cutC, h1, h2, h3])
  · obtain ⟨h1, -, -⟩ := hR _ (not_le.1 h'); exact h (by simp [lam2, cutC, h1])

end Vanish

/-!
## Bounds on the feasible set
-/

theorem gramEntry_sub' (e : GIdx K np) (H J : GSt K np) :
    gramEntry e (H - J) = gramEntry e H - gramEntry e J := by
  simp only [gramEntry, Prod.fst_sub, Prod.snd_sub, Matrix.sub_apply]; split_ifs <;> rfl

theorem trRe_sub (H J : GSt K np) : trRe (H - J) = trRe H - trRe J := by
  simp [trRe, Matrix.trace_sub]

theorem abs_trRe_le (y : GSt K np) :
    |trRe y| ≤ ∑ k : SrcCol K (Fin np), ‖gramEntry ((0 : Fin 2), k, k) y‖ := by
  unfold trRe
  rw [Matrix.trace]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
  simp [gramEntry, Matrix.diag]

theorem abs_trRe_gramJ_le {CJ : ℝ} (hCJ : ∀ t e, ‖gramEntry e (gramJ (K := K) b s τ m t)‖ ≤ CJ)
    (t : ℝ≥0) :
    |trRe (gramJ (K := K) b s τ m t)| ≤ (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ := by
  refine (abs_trRe_le _).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.univ : Finset (SrcCol K (Fin np)))
    (fun k => ‖gramEntry ((0 : Fin 2), k, k) (gramJ (K := K) b s τ m t)‖) CJ
    (fun k _ => hCJ t _)
  simpa [nsmul_eq_mul] using this

theorem trRe_nonneg_of_feasible {H : GSt K np} (hH : GramFeasible (srcSignature K (Fin np)) H) :
    0 ≤ trRe H := by
  rcases isEmpty_or_nonempty (SrcCol K (Fin np)) with hE | ⟨⟨k⟩⟩
  · simp [trRe, Matrix.trace]
  · have h := ModelExist.norm_gramEntry_le_of_feasible hH ((0 : Fin 2), k, k)
    have : 0 ≤ 2 * (H.1.trace).re := (norm_nonneg _).trans h
    unfold trRe; linarith

theorem entry_sub_le_of_feasible {H J : GSt K np}
    (hH : GramFeasible (srcSignature K (Fin np)) H) {R CJ : ℝ}
    (hJ : ∀ e, ‖gramEntry e J‖ ≤ CJ)
    (hJt : |trRe J| ≤ (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) (hR : |trRe (H - J)| ≤ R)
    (e : GIdx K np) :
    ‖gramEntry e (H - J)‖ ≤ 2 * (R + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ := by
  rw [gramEntry_sub']
  refine (norm_sub_le _ _).trans ?_
  rw [trRe_sub] at hR
  have h1 : ‖gramEntry e H‖ ≤ 2 * trRe H := ModelExist.norm_gramEntry_le_of_feasible hH e
  have h2 := abs_le.1 hR
  have h3 := abs_le.1 hJt
  linarith [hJ e]

theorem isCompact_box (B : ℝ) :
    IsCompact {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ B} := by
  set Bm : Set (Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) :=
    Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall 0 B
  have hB : IsCompact Bm :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 B
  have hS : IsClosed {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ B} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun e =>
      isClosed_le (continuous_norm.comp (ClosedLimit.continuous_gramEntry e)) continuous_const
  refine (hB.prod hB).of_isClosed_subset hS fun H hH => ⟨fun i _ j _ => ?_, fun i _ j _ => ?_⟩
  · simpa [gramEntry] using hH (0, i, j)
  · simpa [gramEntry] using hH (1, i, j)

/-- **A generator process is a.s. bounded on every `[0, T]`.** -/
theorem exists_bound_genProc [MeasurableSpace Ω] {Q : Measure Ω}
    (hfe : ∀ᵐ ω ∂Q, ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    {χ : ℝ → ℝ} (hχ : Continuous χ) {Rχ : ℝ}
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
    {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ)
    (hFv : ∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ)
    (hΛv : ∀ p, Λ p ≠ 0 → |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ) (T : ℝ≥0) :
    ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ T, ‖genProc χ b E s τ m G F Λ v ω‖ ≤ C := by
  obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
  set BY := 2 * (Rχ + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ
  set box := {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ BY}
  have hbox : IsCompact box := isCompact_box BY
  have hY : ∀ ω, (∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) → ∀ u,
      |trRe (gY b s τ m G u ω)| ≤ Rχ → gY b s τ m G u ω ∈ box := fun ω hω u hu e =>
    entry_sub_le_of_feasible (hω u) (hCJ u) (abs_trRe_gramJ_le hCJ u) hu e
  have hAc : ∀ e : GIdx K np, ∃ C : ℝ, ∀ J ∈ Set.range (fun t : ℝ≥0 => gramJ (K := K) b s τ m t),
      ∀ y ∈ box, ‖lamA χ b E e (J, y)‖ ≤ C := fun e =>
    exists_bound_finite_compact (((continuous_drE b E e).comp
      (continuous_snd.add continuous_fst)).mul ((continuous_cutC hχ).comp continuous_snd))
      (finite_range_gramJ b s τ m) hbox
  choose CAf hCAf using hAc
  set CA := ∑ e : GIdx K np, |CAf e|
  have hCA0 : 0 ≤ CA := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCAe : ∀ e, |CAf e| ≤ CA := fun e =>
    Finset.single_le_sum (f := fun e => |CAf e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
  have hAb : ∀ ω, (∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) → ∀ (e : GIdx K np)
      (u : ℝ≥0), u ≤ T → ‖genA χ b E s τ m G e u ω‖ ≤ CA * T := fun ω hω e u hu => by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) u)
      (f := fun w => lamA χ b E e (gramJ b s τ m w.toNNReal, gY b s τ m G w.toNNReal ω))
      (C := CA) measure_Ioc_lt_top fun w _ => by
        by_cases h0 : lamA χ b E e (gramJ b s τ m w.toNNReal, gY b s τ m G w.toNNReal ω) = 0
        · rw [h0, norm_zero]; exact hCA0
        · exact (hCAf e _ ⟨_, rfl⟩ _ (hY ω hω _ (lamA_ne_zero hR b E e h0))).trans
            ((le_abs_self _).trans (hCAe e))
    rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg u)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hu) hCA0)
  set BX := BY + BY + CA * T
  set Kreg : Set (ZSt K np) := box ×ˢ (Set.pi univ fun _ => Metric.closedBall (0 : ℂ) BX) ×ˢ box
  have hKreg : IsCompact Kreg :=
    hbox.prod ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod hbox)
  have hZ : ∀ ω, (∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) → ∀ u ≤ T,
      |trRe (gY b s τ m G u ω)| ≤ Rχ → |trRe (gY b s τ m G 0 ω)| ≤ Rχ →
        stZ χ b E s τ m G u ω ∈ Kreg := fun ω hω u hu h1 h2 => by
    refine ⟨hY ω hω u h1, fun e _ => ?_, hY ω hω 0 h2⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (hY ω hω u h1 e) (hY ω hω 0 h2 e))) (hAb ω hω e u hu))
  obtain ⟨C1, hC1⟩ := exists_bound_finite_compact hΛ (finite_range_gramJ (K := K) b s τ m) hKreg
  obtain ⟨C2, hC2⟩ := hKreg.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C2 0 + max C1 0 * T, hfe.mono fun ω hω v hv => ?_⟩
  unfold genProc
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · by_cases h0 : F (stZ χ b E s τ m G v ω) = 0
    · rw [h0, norm_zero]; exact le_max_right _ _
    · obtain ⟨h1, h2⟩ := hFv _ h0
      exact (hC2 _ (hZ ω hω v hv h1 h2)).trans (le_max_left _ _)
  · have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) v)
      (f := fun w => Λ (gramJ b s τ m w.toNNReal, stZ χ b E s τ m G w.toNNReal ω))
      (C := max C1 0) measure_Ioc_lt_top fun w hw => by
        by_cases h0 : Λ (gramJ b s τ m w.toNNReal, stZ χ b E s τ m G w.toNNReal ω) = 0
        · rw [h0, norm_zero]; exact le_max_right _ _
        · obtain ⟨h1, h2⟩ := hΛv _ h0
          have hwT : w.toNNReal ≤ T :=
            (Real.toNNReal_le_iff_le_coe.2 hw.2).trans hv
          exact (hC1 _ ⟨_, rfl⟩ _ (hZ ω hω _ hwT h1 h2)).trans (le_max_left _ _)
    rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg v)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hv) (le_max_right _ _))

/-!
## Before the trace stop the generator processes are the coordinate clauses
-/

theorem abs_trRe_gY_le_stop {ω : Ω}
    (hfω : ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    (hcω : Continuous fun u => G u ω - gramJ b s τ m u) {CJ : ℝ}
    (hCJ : ∀ t e, ‖gramEntry e (gramJ (K := K) b s τ m t)‖ ≤ CJ) {L : ℝ} {u : ℝ≥0}
    (hu : (u : WithTop ℝ≥0) ≤ gramTraceStop G L ω)
    (hσ : (0 : WithTop ℝ≥0) < gramTraceStop G L ω) :
    |trRe (gY b s τ m G u ω)| ≤ |L| + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ := by
  set nc := (Fintype.card (SrcCol K (Fin np)) : ℝ)
  have hJ : ∀ t, |trRe (gramJ (K := K) b s τ m t)| ≤ nc * CJ := abs_trRe_gramJ_le hCJ
  have htr : ∀ t, trRe (gY b s τ m G t ω) = trRe (G t ω) - trRe (gramJ (K := K) b s τ m t) :=
    fun t => trRe_sub _ _
  have hlt : ∀ w : ℝ≥0, (w : WithTop ℝ≥0) < gramTraceStop G L ω →
      trRe (gY b s τ m G w ω) ≤ L + nc * CJ := fun w hw => by
    have h1 : ((G w ω).1.trace).re < L :=
      ModelExist.re_trace_lt_of_lt_pathStop (G := fun t => G t ω) (K := L) hw
    rw [htr]
    have h2 := abs_le.1 (hJ w)
    unfold trRe at h2 ⊢
    linarith
  have hup : trRe (gY b s τ m G u ω) ≤ L + nc * CJ := by
    rcases eq_or_lt_of_le hu with h | h
    · rcases eq_zero_or_pos u with h0 | h0
      · subst h0; exact hlt 0 hσ
      · have hcont : Continuous fun w => trRe (gY b s τ m G w ω) := continuous_trRe.comp hcω
        have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h0⟩
        refine le_of_tendsto ((hcont.tendsto u).mono_left (nhdsWithin_le_nhds (s := Iio u))) ?_
        filter_upwards [self_mem_nhdsWithin] with w (hw : w < u)
        exact hlt w (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hw) hu)
    · exact hlt u h
  have hlo : -(nc * CJ) ≤ trRe (gY b s τ m G u ω) := by
    rw [htr]
    have := trRe_nonneg_of_feasible (hfω u)
    linarith [(abs_le.1 (hJ u)).2]
  exact abs_le.2 ⟨by linarith [abs_nonneg L], by linarith [le_abs_self L]⟩

section Region

variable {χ : ℝ → ℝ} {ω : Ω} {v : ℝ≥0}
  (h0 : χ (trRe (gY b s τ m G 0 ω)) = 1)
  (hreg : ∀ u : ℝ≥0, 0 < u → u ≤ v → χ (trRe (gY b s τ m G u ω)) = 1 ∧
    deriv χ (trRe (gY b s τ m G u ω)) = 0 ∧ deriv (deriv χ) (trRe (gY b s τ m G u ω)) = 0)
include hreg

omit hreg in
theorem toNNReal_mem_of_Ioc {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) v) :
    0 < u.toNNReal ∧ u.toNNReal ≤ v :=
  ⟨Real.toNNReal_pos.2 hu.1, Real.toNNReal_le_iff_le_coe.2 hu.2⟩

theorem genX_eq_cComp (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (e : GIdx K np) :
    genX χ b E s τ m G e v ω = cComp b E s τ m G Kc (Sum.inl e) v ω := by
  have hA : genA χ b E s τ m G e v ω = ∫ u in Ioc (0 : ℝ) v,
      gramDriftEntry (transportD0 b E) (srcSignature K (Fin np)) e (G u.toNNReal ω) := by
    unfold genA
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    obtain ⟨h1, -, -⟩ := hreg _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    simp only [lamA, cutC]
    rw [h1]
    simp only [gY, sub_add_cancel, Complex.ofReal_one, mul_one, drE]
  unfold genX
  rw [hA]
  rfl

include h0

theorem genM1_eq_cComp (hv : 0 < v) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ)
    (e : GIdx K np) : genM1 χ b E s τ m G e v ω = cComp b E s τ m G Kc (Sum.inl e) v ω := by
  have hL : ∫ u in Ioc (0 : ℝ) v, lam1 χ b E e (gramJ b s τ m u.toNNReal,
      stZ χ b E s τ m G u.toNNReal ω) = 0 := by
    have hz : EqOn (fun u : ℝ => lam1 χ b E e (gramJ b s τ m u.toNNReal,
        stZ χ b E s τ m G u.toNNReal ω)) (fun _ => (0 : ℂ)) (Ioc (0 : ℝ) v) := fun u hu => by
      obtain ⟨h1, h2, h3⟩ := hreg _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
      simp only [lam1, stZ, cutC]
      rw [h0, h1, h2, h3]
      simp only [Complex.ofReal_one, Complex.ofReal_zero]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hz]
    simp
  obtain ⟨hv1, -, -⟩ := hreg v hv le_rfl
  unfold genM1 genProc
  rw [hL, sub_zero]
  simp only [fun1, stZ, cutC, h0, hv1, Complex.ofReal_one, one_mul]
  exact genX_eq_cComp hreg Kc e

theorem genM2_eq_cBr (hv : 0 < v) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ)
    (e e' : GIdx K np) :
    genM2 χ b E s τ m G e e' v ω = cBr b E s τ m G Kc (Sum.inl e) (Sum.inl e') v ω := by
  have hL : ∫ u in Ioc (0 : ℝ) v, lam2 χ b E e e' (gramJ b s τ m u.toNNReal,
      stZ χ b E s τ m G u.toNNReal ω) = ∫ u in Ioc (0 : ℝ) v,
        gramCovEntry (transportD0 b E) (srcSignature K (Fin np)) e e' (G u.toNNReal ω) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    obtain ⟨h1, h2, h3⟩ := hreg _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    simp only [lam2, stZ, cutC]
    rw [h0, h1, h2, h3]
    simp only [gY, sub_add_cancel, cvE, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  obtain ⟨hv1, -, -⟩ := hreg v hv le_rfl
  unfold genM2 genProc
  rw [hL]
  simp only [fun2, stZ, cutC, h0, hv1, Complex.ofReal_one, one_mul]
  rw [genX_eq_cComp hreg Kc e, genX_eq_cComp hreg Kc e']
  rfl

end Region

/-!
## The hypothesis and the reduction
-/

/-- **From the tested identities of a generator process off the birth times to the stopped
identities of a process equal to it before a stop.** -/
theorem isTestedMart_stopped_of_gen [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q]
    {tseq : Ω → ℕ → ℝ} {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
    (hfe : ∀ᵐ ω ∂Q, ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    {χ : ℝ → ℝ} (hχ : Continuous χ) {Rχ : ℝ}
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
    {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ)
    (hFv : ∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ)
    (hΛv : ∀ p, Λ p ≠ 0 → |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsAEStop Q (complexObs tseq G Kc) hobs σ)
    {X : ℝ≥0 → Ω → ℂ}
    (hXeq : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, (v : WithTop ℝ≥0) ≤ σ ω →
      genProc χ b E s τ m G F Λ v ω = X v ω)
    (hoff : IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
      (genProc χ b E s τ m G F Λ)) :
    IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess X σ) := by
  have hcont := continuous_genProc (E := E) hc hχ hF hΛ
  have hbd := exists_bound_genProc (b := b) (E := E) (s := s) (τ := τ) (m := m) hfe hχ hR hF hΛ
    hFv hΛv
  have hfull := isTestedMart_of_off (birthTimes_finite s τ) hobs
    (tendsto_complexObs_right hc hkc) hcont hbd hoff
  obtain ⟨ρ, hρ, hρe⟩ := hσ
  have hst := isTestedMart_stoppedProcess_of_tested hobs hfull hcont hbd hρ
  refine isTestedMart_of_ae_eq hst fun t => ?_
  filter_upwards [hρe, hXeq] with ω h1 h2
  simp only [stoppedProcess, h1]
  exact (h2 _ (by rw [coe_untopA_min']; exact min_le_right _ _)).symm

/-- **Hypothesis `CapIdentGramGen`** (, no stop): under `CapIdentPremise`, for every
`C³` cutoff `χ` with compact support, the generator processes `genM1 χ e` and `genM2 χ e e'`
have tested increments with all times off the birth times. -/
def CapIdentGramGen : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ χ : ℝ → ℝ, ContDiff ℝ 3 χ → HasCompactSupport χ →
      (∀ e : GIdx K np, IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
        (genM1 χ b E s τ m G e)) ∧
      ∀ e e' : GIdx K np, IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
        (genM2 χ b E s τ m G e e')

/-- **`CapIdentGram` from the generator hypothesis** (every level; no good-level restriction). -/
theorem capIdentGram_of_gen (hpin : CapIdentGramGen) : CapIdentGram := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  have hgen := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  obtain ⟨hD, hlim, hA, hne, hφ, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, hfdd⟩ := hP
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, hm, -⟩, hs, -, hh0, -, -⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  have hcap := hφ.eventually (eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh0 hA hne)
  have hfe := ae_feasible_all hD hφ hfdd hobs hcap hc
  have hlev : ∀ L, IsGramCoordTestedAt b E s τ m Q tseq G Kc (gramTraceStop G L) := fun L => by
    obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
    set R0 := max (|L| + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) 0 with hR0
    have hR0p : 0 < R0 + 1 := add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos
    obtain ⟨χ, hχ3, hχs, hχ1⟩ := exists_bump (R0 + 1) hR0p
    obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ3
    obtain ⟨Rχ, hRχ⟩ := exists_cut_radius hχs
    obtain ⟨h1, h2⟩ := hgen χ hχ3 hχs
    have hσ := isAEStop_gramTraceStop (Q := Q) hobs hc hb1 hm L
    have hreg : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω → 0 < v →
        χ (trRe (gY b s τ m G 0 ω)) = 1 ∧ ∀ u : ℝ≥0, 0 < u → u ≤ v →
          χ (trRe (gY b s τ m G u ω)) = 1 ∧ deriv χ (trRe (gY b s τ m G u ω)) = 0 ∧
            deriv (deriv χ) (trRe (gY b s τ m G u ω)) = 0 := by
      filter_upwards [hfe] with ω hω v hv hv0
      have hσ0 : (0 : WithTop ℝ≥0) < gramTraceStop G L ω :=
        lt_of_lt_of_le (WithTop.coe_lt_coe.2 hv0) hv
      have hb' : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ gramTraceStop G L ω →
          |trRe (gY b s τ m G u ω)| < R0 + 1 := fun u hu =>
        ((abs_trRe_gY_le_stop hω (hc ω) hCJ hu hσ0).trans (le_max_left _ _)).trans_lt
          (lt_add_one _)
      refine ⟨(hχ1 _ (hb' 0 (by rw [WithTop.coe_zero]; exact bot_le))).1, fun u _ huv => ?_⟩
      exact hχ1 _ (hb' u ((WithTop.coe_le_coe.2 huv).trans hv))
    refine ⟨fun e => isTestedMart_stopped_of_gen hobs hc hkc hfe hχc hRχ
      (continuous_fun1 hχc e) (continuous_lam1 hχc hχd hχdd b E e)
      (fun z hz => fun1_ne_zero hRχ e hz) (fun p hp => lam1_ne_zero hRχ b E e hp) hσ ?_ (h1 e),
      fun e e' => isTestedMart_stopped_of_gen hobs hc hkc hfe hχc hRχ
      (continuous_fun2 hχc e e') (continuous_lam2 hχc hχd hχdd b E e e')
      (fun z hz => fun2_ne_zero hRχ e e' hz) (fun p hp => lam2_ne_zero hRχ b E e e' hp) hσ ?_
      (h2 e e')⟩
    · filter_upwards [hreg] with ω hω v hv
      rcases eq_zero_or_pos v with h0 | h0
      · subst h0
        simp [genProc, fun1, stZ, genX, genA, cComp, cEntry]
      · obtain ⟨hz, hu⟩ := hω v hv h0
        exact genM1_eq_cComp hz hu h0 Kc e
    · filter_upwards [hreg] with ω hω v hv
      rcases eq_zero_or_pos v with h0 | h0
      · subst h0
        simp [genProc, fun2, stZ, genX, genA, cBr, cComp, cEntry]
      · obtain ⟨hz, hu⟩ := hω v hv h0
        exact genM2_eq_cBr hz hu h0 Kc e e'
  exact ⟨fun L e => (hlev L).drift e, fun L e e' => (hlev L).bracket e e'⟩

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram
