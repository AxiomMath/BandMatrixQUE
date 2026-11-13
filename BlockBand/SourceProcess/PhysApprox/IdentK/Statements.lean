module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramKGen

/-!
# Statements for the `𝒦` limit passage `CapIdentKDoubleGen`

**Drift-free form.** `genK1`, `genK2` and `genKC` never read the cut-drift slot
`x_e = Y_e − Y_e(0) − A^χ_e` of the state: their `F` and `Λ` are *A-blind* (`IsABlindF`,
`IsABlindL`, proved by `rfl`). Only `genKG` reads it. Its drift-free version `genKY` uses
`Ŷ_e = Y_e − Y_e(0)` (`kHatE`):
`lamKY = c₀[dCut x^𝒦 Ŷ + χξ(x^𝒦 b_e + kG) + χ'ξ(Ŷ trKG + x^𝒦 trCv) + χξ'(Ŷ qKK + x^𝒦 qG)]`.
Along every path, `genKG = genKY + D`, where `D_t = ∫_0^t β X − (∫_0^t β) X_t`, `X = genK1` and
`β = lamA χ e` (the `isTestedMart_ibp` process). This is `KGBridge`.

A drift-free process is `F(Z_t) − ∫_0^t Λ(J_r, Z_r)`, where `Z_t` is a function of the
observables at the times `t` and `0` only (`stZKObs`, `genObs`, drift slot set to `0`). The same
definition, applied to the finite-`W` observables `b3ObsAll`, gives the prelimit process. So no
additive functional has to be adjoined to the fdd (`fddConvOff_augProc` is not needed).

* `KTest`: the four drift-free tests; `KTest.fn`, `KTest.lam`, `KTest.gen`.
* `capIncW`: the cap-restricted, unnormalised tested increment of `genObs (b3ObsAll …)` under
  `closedLaw`.
* **`KFiniteW`**: it tends to `0` as `W → ∞`.
* **`KFddPassage`**: generic in `(F, Λ)`; along the candidate's fdd subsequence this gives
  `IsTestedMartOff` for `genObs (complexObs …)`.
* **`KGBridge`**: `genK1`, `genKY` tested off the births ⇒ `genKG` tested off the births.
* Proved: `genObs_complexObs` (A-blind `genObs` on `complexObs` is `genProcK`),
  **`capIdentKDoubleGenA0_of_parts`** and **`capIdentKDoubleGen_of_parts : KFiniteW →
  KFddPassage → KGBridge → CapIdentKDoubleGen`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal ComplexConjugate

variable {K np : ℕ}

/-!
## The drift-free `𝒦`–Gram test
-/

/-- `Ŷ_e = Y_e − Y_e(0)` at a `𝒦` state. -/
def kHatE (e : GIdx K np) (z : ZK K np) : ℂ := gramEntry e z.1.1 - gramEntry e z.1.2.2

/-- `Ŷ_e` at a point `(J, z)`. -/
def kHatP (e : GIdx K np) (p : GSt K np × ZK K np) : ℂ :=
  gramEntry e (pyG p) - gramEntry e (pyG0 p)

/-- The test function `c₀ χ(s) ξ(q) x^𝒦_a Ŷ_e`. -/
def funKY (χ ξ : ℝ → ℝ) (a : KIdx np) (e : GIdx K np) (z : ZK K np) : ℂ :=
  cutZ χ ξ z * z.2.2.1 a * kHatE e z

/-- Its generator (`lamKG` with `x_e ↦ Ŷ_e` and the cut drift `b_e(1 − χ) ↦ b_e`). -/
def lamKY (χ ξ : ℝ → ℝ) (b E : ℝ) (a : KIdx np) (e : GIdx K np) (p : GSt K np × ZK K np) : ℂ :=
  cut0 χ ξ p *
    (dCut χ ξ b E (pyG p) (pH p) (pyK p) * pxK p a * kHatP e p +
      cutC χ (pyG p) * cutK ξ (pyK p) * (pxK p a * drE b E e (pH p) + kG b E a e (pH p)) +
      cutC (deriv χ) (pyG p) * cutK ξ (pyK p) *
        (kHatP e p * trKG b E a (pH p) + pxK p a * trCv b E e (pH p)) +
      cutC χ (pyG p) * cutK (deriv ξ) (pyK p) *
        (kHatP e p * qKK b E a (pH p) (pyK p) + pxK p a * qG b E e (pH p) (pyK p)))

variable {Ω : Type*}

/-- **The drift-free `𝒦`–Gram generator process** `genKY`. -/
def genKY (χ ξ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (a : KIdx np) (e : GIdx K np) : ℝ≥0 → Ω → ℂ :=
  genProcK χ b E s τ m G Kc (funKY χ ξ a e) (lamKY χ ξ b E a e)

/-!
## The four drift-free tests
-/

/-- The four drift-free `𝒦` tests: `x^𝒦_a`, `x^𝒦_a x^𝒦_{a'}`, `x^𝒦_a Ŷ_e`, `x^𝒦_a conj x^𝒦_{a'}`. -/
inductive KTest (K np : ℕ) where
  | k1 (a : KIdx np)
  | k2 (a a' : KIdx np)
  | ky (a : KIdx np) (e : GIdx K np)
  | kc (a a' : KIdx np)

/-- The test function of a test. -/
def KTest.fn (χ ξ : ℝ → ℝ) : KTest K np → ZK K np → ℂ
  | .k1 a => funK1 χ ξ a
  | .k2 a a' => funK2 χ ξ a a'
  | .ky a e => funKY χ ξ a e
  | .kc a a' => funKC χ ξ a a'

/-- The generator of a test. -/
def KTest.lam (χ ξ : ℝ → ℝ) (b E : ℝ) : KTest K np → GSt K np × ZK K np → ℂ
  | .k1 a => lamK1 χ ξ b E a
  | .k2 a a' => lamK2 χ ξ b E a a'
  | .ky a e => lamKY χ ξ b E a e
  | .kc a a' => lamKC χ ξ b E a a'

/-- The generator process of a test (on the candidate; the state of `genProcK`). -/
def KTest.gen (χ ξ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (κ : KTest K np) : ℝ≥0 → Ω → ℂ :=
  genProcK χ b E s τ m G Kc (κ.fn χ ξ) (κ.lam χ ξ b E)

/-!
## Drift-blindness
-/

/-- `F` does not read the cut-drift slot `x` of the Gram component. -/
def IsABlindF (F : ZK K np → ℂ) : Prop :=
  ∀ (z : ZK K np) (x : GIdx K np → ℂ), F ((z.1.1, x, z.1.2.2), z.2) = F z

/-- `Λ` does not read the cut-drift slot `x` of the Gram component. -/
def IsABlindL (Λ : GSt K np × ZK K np → ℂ) : Prop :=
  ∀ (J : GSt K np) (z : ZK K np) (x : GIdx K np → ℂ), Λ (J, ((z.1.1, x, z.1.2.2), z.2)) = Λ (J, z)

theorem KTest.isABlindF (χ ξ : ℝ → ℝ) (κ : KTest K np) : IsABlindF (κ.fn χ ξ) := by
  cases κ <;> intro z x <;> rfl

theorem KTest.isABlindL (χ ξ : ℝ → ℝ) (b E : ℝ) (κ : KTest K np) :
    IsABlindL (κ.lam χ ξ b E) := by
  cases κ <;> intro J z x <;> rfl

/-!
## Continuity and vanishing off the cut region
-/

theorem continuous_kHatE (e : GIdx K np) : Continuous (kHatE (K := K) e) :=
  ((ClosedLimit.continuous_gramEntry e).comp (continuous_fst.comp continuous_fst)).sub
    ((ClosedLimit.continuous_gramEntry e).comp
      ((continuous_snd.comp continuous_snd).comp continuous_fst))

theorem continuous_kHatP (e : GIdx K np) : Continuous (kHatP (K := K) e) :=
  (continuous_kHatE e).comp continuous_snd

theorem continuous_funKY {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hξ : Continuous ξ) (a : KIdx np)
    (e : GIdx K np) : Continuous (funKY χ ξ a e) := by
  have := continuous_cutZ (K := K) (np := np) hχ hξ
  have := continuous_kHatE (K := K) (np := np) e
  unfold funKY; fun_prop

theorem continuous_lamKY {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
    (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
    (hξ2 : Continuous (deriv (deriv ξ))) (b E : ℝ) (a : KIdx np) (e : GIdx K np) :
    Continuous (lamKY χ ξ b E a e) := by
  have hd := continuous_dCut (K := K) (np := np) hχ hχ1 hχ2 hξ hξ1 hξ2 b E
  have hk := continuous_qKK (K := K) (np := np) b E a
  have hg := continuous_qG (K := K) (np := np) b E e
  have hh := continuous_kHatP (K := K) (np := np) e
  unfold lamKY cut0
  fun_prop

theorem KTest.continuous_fn {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hξ : Continuous ξ)
    (κ : KTest K np) : Continuous (κ.fn χ ξ) := by
  cases κ with
  | k1 a => exact continuous_funK1 hχ hξ a
  | k2 a a' => exact continuous_funK2 hχ hξ a a'
  | ky a e => exact continuous_funKY hχ hξ a e
  | kc a a' => exact continuous_funKC hχ hξ a a'

theorem KTest.continuous_lam {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
    (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
    (hξ2 : Continuous (deriv (deriv ξ))) (b E : ℝ) (κ : KTest K np) :
    Continuous (κ.lam χ ξ b E) := by
  cases κ with
  | k1 a => exact continuous_lamK1 hχ hχ1 hχ2 hξ hξ1 hξ2 b E a
  | k2 a a' => exact continuous_lamK2 hχ hχ1 hχ2 hξ hξ1 hξ2 b E a a'
  | ky a e => exact continuous_lamKY hχ hχ1 hχ2 hξ hξ1 hξ2 b E a e
  | kc a a' => exact continuous_lamKC hχ hχ1 hχ2 hξ hξ1 hξ2 b E a a'

section VanishKY

variable {χ ξ : ℝ → ℝ} {Rχ Rξ : ℝ}
  (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
  (hRξ : ∀ c, Rξ < |c| → ξ c = 0 ∧ deriv ξ c = 0 ∧ deriv (deriv ξ) c = 0)
include hR hRξ

theorem lamKY_cutReg (b E : ℝ) (a : KIdx np) (e : GIdx K np) {p : GSt K np × ZK K np}
    (hp : lamKY χ ξ b E a e p ≠ 0) : CutReg Rχ Rξ p :=
  cutReg_of_ne_zero hR hRξ
    (fun p ⟨h1, h2, h3⟩ => by simp [lamKY, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamKY, cut0, cutC, h1])
    (fun p ⟨h1, h2, h3⟩ => by simp [lamKY, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamKY, cut0, cutK, h1]) hp

theorem KTest.fn_cutReg (κ : KTest K np) {z : ZK K np} (hz : κ.fn χ ξ z ≠ 0) :
    CutReg Rχ Rξ ((0 : GSt K np), z) := by
  rcases κ with a | ⟨a, a'⟩ | ⟨a, e⟩ | ⟨a, a'⟩
  · exact funK_cutReg hR hRξ (P := fun z => z.2.2.1 a) (fun _ => rfl) hz
  · exact funK_cutReg hR hRξ (P := fun z => z.2.2.1 a * z.2.2.1 a')
      (fun _ => mul_assoc _ _ _) hz
  · exact funK_cutReg hR hRξ (P := fun z => z.2.2.1 a * kHatE e z)
      (fun _ => mul_assoc _ _ _) hz
  · exact funK_cutReg hR hRξ (P := fun z => z.2.2.1 a * conj (z.2.2.1 a'))
      (fun _ => mul_assoc _ _ _) hz

theorem KTest.lam_cutReg (b E : ℝ) (κ : KTest K np) {p : GSt K np × ZK K np}
    (hp : κ.lam χ ξ b E p ≠ 0) : CutReg Rχ Rξ p := by
  cases κ with
  | k1 a => exact lamK1_cutReg hR hRξ b E a hp
  | k2 a a' => exact lamK2_cutReg hR hRξ b E a a' hp
  | ky a e => exact lamKY_cutReg hR hRξ b E a e hp
  | kc a a' => exact lamKC_cutReg hR hRξ b E a a' hp

end VanishKY

/-!
## Drift-free processes read off observables
-/

/-- The Gram state read off the Gram-entry observables. -/
def gOfObs (obs : B3.LIdx K np → ℝ≥0 → Ω → ℂ) (u : ℝ≥0) (ω : Ω) : GSt K np :=
  gramOfEntries fun e => obs (Sum.inl e) u ω

/-- The `𝒦` matrix read off the `𝒦`-entry observables. -/
def kOfObs (obs : B3.LIdx K np → ℝ≥0 → Ω → ℂ) (u : ℝ≥0) (ω : Ω) : KSt np :=
  Matrix.of fun i j => obs (Sum.inr (Sum.inr (i, j))) u ω

/-- **The drift-free state at time `u`** from the observables at `u` and `0` (drift slot `0`):
`((Y_u, 0, Y_0), Y^𝒦_u, x^𝒦_u, Y^𝒦_0)`, `Y = G − J`, `Y^𝒦 = 𝒦 − J_𝒦`. -/
def stZKObs (b E s : ℝ) (τ m : Fin np → ℝ) (obs : B3.LIdx K np → ℝ≥0 → Ω → ℂ) (u : ℝ≥0)
    (ω : Ω) : ZK K np :=
  ((gOfObs obs u ω - gramJ b s τ m u, 0, gOfObs obs 0 ω - gramJ b s τ m 0),
    kOfObs obs u ω - kJ E s τ m u,
    fun a => (kOfObs obs u ω - kJ E s τ m u) a.1 a.2 - (kOfObs obs 0 ω - kJ E s τ m 0) a.1 a.2,
    kOfObs obs 0 ω - kJ E s τ m 0)

/-- **A drift-free generator process of observables**, `F(Z_t) − ∫_0^t Λ(J_u, Z_u)`. -/
def genObs (b E s : ℝ) (τ m : Fin np → ℝ) (obs : B3.LIdx K np → ℝ≥0 → Ω → ℂ)
    (F : ZK K np → ℂ) (Λ : GSt K np × ZK K np → ℂ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  F (stZKObs b E s τ m obs t ω) -
    ∫ u in Ioc (0 : ℝ) t, Λ (gramJ b s τ m u.toNNReal, stZKObs b E s τ m obs u.toNNReal ω)

theorem stZKObs_complexObs (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (tseq : Ω → ℕ → ℝ)
    (G : ℝ≥0 → Ω → GSt K np) (Kc : ℝ≥0 → Ω → KSt np) (u : ℝ≥0) (ω : Ω) :
    stZKObs b E s τ m (complexObs tseq G Kc) u ω =
      (((stZK χ b E s τ m G Kc u ω).1.1, 0, (stZK χ b E s τ m G Kc u ω).1.2.2),
        (stZK χ b E s τ m G Kc u ω).2) := by
  have hG : ∀ v, gOfObs (complexObs tseq G Kc) v ω = G v ω := fun v =>
    gramOfEntries_gramEntry (G v ω)
  have hK : ∀ v, kOfObs (complexObs tseq G Kc) v ω = Kc v ω := fun v => by
    ext i j; rfl
  simp only [stZKObs, hG, hK, stZK, stZ, gY, yKp]

/-- **On the candidate, an A-blind `genObs` is the `genProcK` process.** -/
theorem genObs_complexObs (χ : ℝ → ℝ) {b E s : ℝ} {τ m : Fin np → ℝ} {tseq : Ω → ℕ → ℝ}
    {G : ℝ≥0 → Ω → GSt K np} {Kc : ℝ≥0 → Ω → KSt np} {F : ZK K np → ℂ}
    {Λ : GSt K np × ZK K np → ℂ} (hF : IsABlindF F) (hΛ : IsABlindL Λ) :
    genObs b E s τ m (complexObs tseq G Kc) F Λ = genProcK χ b E s τ m G Kc F Λ := by
  funext t ω
  simp only [genObs, genProcK, stZKObs_complexObs χ]
  rw [hF]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun u => hΛ _ _ _)

/-!
## The finite-`W` tested increment
-/

/-- **The cap-restricted tested increment at width `W`** (unnormalised):
`E_W[1_cap ψ(obs_{i_l}(u_l)) (M_W(t') − M_W(t))]`, with `M_W = genObs (b3ObsAll …) F Λ`. -/
def capIncW (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (F : ZK K np → ℂ)
    (Λ : GSt K np × ZK K np → ℂ) {r : ℕ} (i : Fin r → B3.LIdx K np) (u : Fin r → ℝ≥0)
    (ψ : BoundedContinuousFunction (Fin r → ℂ) ℝ) (t t' : ℝ≥0) : ℂ :=
  ∫ y, ((physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y)) •
    (genObs b E s τ m (b3ObsAll b E s h τ m W Vs) F Λ t' y -
      genObs b E s τ m (b3ObsAll b E s h τ m W Vs) F Λ t y) ∂closedLaw b W np

/-!
## The three parts
-/

/-- **`KFiniteW`** (cutoff boundedness, the finite-`W` Taylor generator identity before the
auxiliary trace stop `σ_W^R`, removal of that stop by the stop tail): for every drift-free test,
the cap-restricted finite-`W` tested increment, at times off the births, tends to `0` as
`W → ∞`. -/
def KFiniteW : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
    ∀ χ ξ : ℝ → ℝ, ContDiff ℝ 3 χ → HasCompactSupport χ → ContDiff ℝ 3 ξ →
      HasCompactSupport ξ → ∀ (κ : KTest K np) (t t' : ℝ≥0), t ≤ t' →
      t ∉ birthTimes s τ → t' ∉ birthTimes s τ →
      ∀ (r : ℕ) (i : Fin r → B3.LIdx K np) (u : Fin r → ℝ≥0), (∀ l, u l ≤ t) →
        (∀ l, u l ∉ birthTimes s τ) → ∀ ψ : BoundedContinuousFunction (Fin r → ℂ) ℝ,
        Tendsto (fun W => capIncW b E s h τ m W (Vs W) (κ.fn χ ξ) (κ.lam χ ξ b E) i u ψ t t')
          atTop (𝓝 0)

/-- **`KFddPassage`** (drift-free; generic in `(F, Λ)`): for a candidate of `CapIdentPremise` and
continuous `F`, `Λ` vanishing off a cut region, if the finite-`W` tested increments vanish along
the fdd subsequence `φ`, then `genObs (complexObs …) F Λ` has tested increments off the birth
times. -/
def KFddPassage : Prop :=
  TransmissionLawContract →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ (F : ZK K np → ℂ) (Λ : GSt K np × ZK K np → ℂ) (Rχ Rξ : ℝ), Continuous F →
      Continuous Λ → (∀ z, F z ≠ 0 → CutReg Rχ Rξ ((0 : GSt K np), z)) →
      (∀ p, Λ p ≠ 0 → CutReg Rχ Rξ p) →
      (∀ t t' : ℝ≥0, t ≤ t' → t ∉ birthTimes s τ → t' ∉ birthTimes s τ →
        ∀ (r : ℕ) (i : Fin r → B3.LIdx K np) (u : Fin r → ℝ≥0), (∀ l, u l ≤ t) →
          (∀ l, u l ∉ birthTimes s τ) → ∀ ψ : BoundedContinuousFunction (Fin r → ℂ) ℝ,
          Tendsto (fun n => capIncW b E s h τ m (φ n) (Vs (φ n)) F Λ i u ψ t t') atTop
            (𝓝 0)) →
      IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
        (genObs b E s τ m (complexObs tseq G Kc) F Λ)

/-- **`KGBridge`** (integration by parts): along every path `genKG = genKY + D`, with
`D_t = ∫_0^t β X − (∫_0^t β) X_t`, `X = genK1 a`, `β = lamA χ e`; hence tested increments of
`genK1` and `genKY` off the births give those of `genKG` (`isTestedMart_of_off`,
`isTestedMart_ibp`). -/
def KGBridge : Prop :=
  TransmissionLawContract →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ χ ξ : ℝ → ℝ, ContDiff ℝ 3 χ → HasCompactSupport χ → ContDiff ℝ 3 ξ →
      HasCompactSupport ξ → ∀ (a : KIdx np) (e : GIdx K np),
      IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc) (genK1 χ ξ b E s τ m G Kc a) →
      IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
        (genKY χ ξ b E s τ m G Kc a e) →
      IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc) (genKG χ ξ b E s τ m G Kc a e)

/-!
## Assembly
-/

/-- The drift-free form of `CapIdentKDoubleGen`: all four drift-free tests (no Gram hypothesis). -/
def CapIdentKDoubleGenA0 : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ χ ξ : ℝ → ℝ, ContDiff ℝ 3 χ → HasCompactSupport χ → ContDiff ℝ 3 ξ →
      HasCompactSupport ξ → ∀ κ : KTest K np,
      IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc) (κ.gen χ ξ b E s τ m G Kc)

/-- **The drift-free form from the finite-`W` step and the passage.** -/
theorem capIdentKDoubleGenA0_of_parts (hW : KFiniteW) (hP : KFddPassage) :
    CapIdentKDoubleGenA0 := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hPr χ ξ hχ3 hχs
    hξ3 hξs κ
  obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ3
  obtain ⟨hξc, hξd, hξdd⟩ := cut_continuity hξ3
  obtain ⟨Rχ, hRχ⟩ := exists_cut_radius hχs
  obtain ⟨Rξ, hRξ⟩ := exists_cut_radius hξs
  have hφ : Tendsto φ atTop atTop := hPr.2.2.2.2.1
  have h := hP hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hPr (κ.fn χ ξ)
    (κ.lam χ ξ b E) Rχ Rξ (κ.continuous_fn hχc hξc)
    (κ.continuous_lam hχc hχd hχdd hξc hξd hξdd b E)
    (fun z hz => κ.fn_cutReg hRχ hRξ hz) (fun p hp => κ.lam_cutReg hRχ hRξ b E hp)
    (fun t t' htt' ht ht' r i u hu hub ψ =>
      (hW hTL hS hT hK hL b E np τ m T s h K Vs hPr.1 χ ξ hχ3 hχs hξ3 hξs κ t t' htt' ht ht'
        r i u hu hub ψ).comp hφ)
  rwa [genObs_complexObs χ (κ.isABlindF χ ξ) (κ.isABlindL χ ξ b E)] at h

/-- **`CapIdentKDoubleGen` from the three parts.** -/
theorem capIdentKDoubleGen_of_parts (hW : KFiniteW) (hP : KFddPassage) (hB : KGBridge) :
    CapIdentKDoubleGen := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hPr _ χ ξ hχ3 hχs
    hξ3 hξs
  have hA := capIdentKDoubleGenA0_of_parts hW hP hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P
    μ φ Ω' mΩ' Q tseq G Kc hPr χ ξ hχ3 hχs hξ3 hξs
  exact ⟨fun a => hA (.k1 a), fun a a' => hA (.k2 a a'),
    fun a e => hB hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hPr χ ξ hχ3 hχs hξ3
      hξs a e (hA (.k1 a)) (hA (.ky a e)),
    fun a a' => hA (.kc a a')⟩

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK
