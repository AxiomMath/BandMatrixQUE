module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramGen

/-!
# The `𝒦` identities from cutoff generator martingales

The `𝒦` analogue of the Gram generator processes. With `Y = G − J`, `Y^𝒦 = 𝒦 − J_𝒦`,
`s = Re Tr Y_M`, `q = Σ_a |Y^𝒦_a|²`, cutoffs `χ(s)` and `ξ(q)` (and their values at time `0`),
`x^𝒦_a = Y^𝒦_a − Y^𝒦_a(0)` and the Gram increments `x_e`, the processes `genK1 a`, `genK2 a a'`,
`genKG a e`, `genKC a a'` are Itô's formula for `c₀ χ(s) ξ(q) P` with
`P = x^𝒦_a, x^𝒦_a x^𝒦_{a'}, x^𝒦_a x_e, x^𝒦_a conj(x^𝒦_{a'})`. The generators use the brackets of
the limit model (`d𝒦 d𝒦 = 0`, `d𝒦 dG = kGramCov`, `d𝒦 d𝒦̄ = kConjCov`) and the Hermitian symmetry
`conj(dG_e) = dG_{e*}` (`e* = (σ, l, k)` for `e = (σ, k, l)`):
`dq = Σ_a (conj Y^𝒦_a d𝒦_a + Y^𝒦_a conj d𝒦_a) + Σ_a kConjCov_{aa} dt`,
`d⟨q, G_e⟩ = Σ_a (conj Y^𝒦_a kGramCov_{a,e} + Y^𝒦_a conj kGramCov_{a,e*})`,
`d⟨q, 𝒦_{a'}⟩ = Σ_a Y^𝒦_a conj kConjCov_{a,a'}`,
`d⟨q, conj 𝒦_{a'}⟩ = Σ_a conj Y^𝒦_a kConjCov_{a,a'}`.

Measure: the candidate's `Q`; filtration: the raw natural filtration of `complexObs`.

* Continuity for every `ω`, a.s. bounds on every `[0, T]` (`exists_bound_genProcK`).
* Before `σ_L ∧ ρ_M`, with `χ = 1` near `[−R, R]` and `ξ = 1` near `[0, n² max(M,0)²]`, the four
  processes are the four `𝒦` clauses (`genK1_eq`, `genK2_eq`, `genKG_eq`, `genKC_eq`).
* **`CapIdentKDoubleGen`**, stated as a hypothesis; **`capIdentKDouble_of_gen :
  CapIdentKDoubleGen → CapIdentKDouble`**; with `capIdentGram_of_gen`, `targetCapIdentAll_of_gen`
  and `targetCapCond'_of_gen`.
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
open scoped NNReal ENNReal ComplexConjugate

variable {K np : ℕ}

/-- `𝒦` coordinates. -/
abbrev KIdx (np : ℕ) := Fin np × Fin np

/-- `𝒦` states. -/
abbrev KSt (np : ℕ) := Matrix (Fin np) (Fin np) ℂ

/-- The state `((Y_t, x(t), Y_0), Y^𝒦_t, x^𝒦(t), Y^𝒦_0)` of the `𝒦` processes. -/
abbrev ZK (K np : ℕ) := ZSt K np × KSt np × (KIdx np → ℂ) × KSt np

/-! ## Coefficients -/

/-- `q = Σ_a |y_a|²`. -/
def qK (y : KSt np) : ℝ := ∑ a : KIdx np, ‖y a.1 a.2‖ ^ 2

/-- The cutoff `f(q(y))` as a complex number. -/
def cutK (f : ℝ → ℝ) (y : KSt np) : ℂ := (f (qK y) : ℂ)

def kG (b E : ℝ) (a : KIdx np) (e : GIdx K np) (H : GSt K np) : ℂ := kGramCov b E a e H

def kC (b E : ℝ) (a a' : KIdx np) (H : GSt K np) : ℂ := kConjCov (K := K) b E a a' H

/-- `e* = (σ, l, k)`. -/
def eStar (e : GIdx K np) : GIdx K np := (e.1, e.2.2, e.2.1)

def trKG (b E : ℝ) (a : KIdx np) (H : GSt K np) : ℂ :=
  ∑ k : SrcCol K (Fin np), kG b E a ((0 : Fin 2), k, k) H

def dQ (b E : ℝ) (H : GSt K np) : ℂ := ∑ a : KIdx np, kC b E a a H

def qG (b E : ℝ) (e : GIdx K np) (H : GSt K np) (y : KSt np) : ℂ :=
  ∑ a : KIdx np, (conj (y a.1 a.2) * kG b E a e H + y a.1 a.2 * conj (kG b E a (eStar e) H))

def qKK (b E : ℝ) (a' : KIdx np) (H : GSt K np) (y : KSt np) : ℂ :=
  ∑ a : KIdx np, y a.1 a.2 * conj (kC b E a a' H)

def qKc (b E : ℝ) (a' : KIdx np) (H : GSt K np) (y : KSt np) : ℂ :=
  ∑ a : KIdx np, conj (y a.1 a.2) * kC b E a a' H

def qQ (b E : ℝ) (H : GSt K np) (y : KSt np) : ℂ :=
  ∑ a : KIdx np, (conj (y a.1 a.2) * qKK b E a H y + y a.1 a.2 * qKc b E a H y)

def sQ (b E : ℝ) (H : GSt K np) (y : KSt np) : ℂ :=
  ∑ a : KIdx np, (conj (y a.1 a.2) * trKG b E a H + y a.1 a.2 * conj (trKG b E a H))

/-- The drift of `χ(s) ξ(q)`. -/
def dCut (χ ξ : ℝ → ℝ) (b E : ℝ) (yG H : GSt K np) (yK : KSt np) : ℂ :=
  cutC (deriv χ) yG * cutK ξ yK * trDr b E H + cutC χ yG * cutK (deriv ξ) yK * dQ b E H +
    (1 / 2 : ℂ) * cutC (deriv (deriv χ)) yG * cutK ξ yK * trTr b E H +
    cutC (deriv χ) yG * cutK (deriv ξ) yK * sQ b E H yK +
    (1 / 2 : ℂ) * cutC χ yG * cutK (deriv (deriv ξ)) yK * qQ b E H yK

@[fun_prop] theorem continuous_conj' : Continuous fun z : ℂ => conj z := Complex.continuous_conj

@[fun_prop] theorem continuous_qK : Continuous (qK (np := np)) :=
  continuous_finsetSum _ fun a _ =>
    (continuous_norm.comp ((continuous_id.matrix_elem a.1 a.2))).pow 2

@[fun_prop] theorem continuous_cutK {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (cutK (np := np) f) :=
  Complex.continuous_ofReal.comp (hf.comp continuous_qK)

@[fun_prop] theorem continuous_kG (b E : ℝ) (a : KIdx np) (e : GIdx K np) :
    Continuous (kG b E a e) := continuous_kGramCov a e

@[fun_prop] theorem continuous_kC (b E : ℝ) (a a' : KIdx np) :
    Continuous (kC (K := K) b E a a') := continuous_kConjCov a a'

@[fun_prop] theorem continuous_trKG (b E : ℝ) (a : KIdx np) :
    Continuous (trKG (K := K) b E a) :=
  continuous_finsetSum _ fun _ _ => continuous_kG b E a _

@[fun_prop] theorem continuous_dQ (b E : ℝ) : Continuous (dQ (K := K) (np := np) b E) :=
  continuous_finsetSum _ fun _ _ => continuous_kC b E _ _

theorem continuous_entry (a : KIdx np) : Continuous fun y : KSt np => y a.1 a.2 :=
  continuous_id.matrix_elem a.1 a.2

@[fun_prop] theorem continuous_qG (b E : ℝ) (e : GIdx K np) :
    Continuous fun p : GSt K np × KSt np => qG b E e p.1 p.2 := by
  unfold qG
  refine continuous_finsetSum _ fun a _ => ?_
  exact ((continuous_conj'.comp ((continuous_entry a).comp continuous_snd)).mul
    ((continuous_kG b E a e).comp continuous_fst)).add
    (((continuous_entry a).comp continuous_snd).mul
      (continuous_conj'.comp ((continuous_kG b E a (eStar e)).comp continuous_fst)))

@[fun_prop] theorem continuous_qKK (b E : ℝ) (a' : KIdx np) :
    Continuous fun p : GSt K np × KSt np => qKK b E a' p.1 p.2 := by
  unfold qKK
  exact continuous_finsetSum _ fun a _ => ((continuous_entry a).comp continuous_snd).mul
    (continuous_conj'.comp ((continuous_kC b E a a').comp continuous_fst))

@[fun_prop] theorem continuous_qKc (b E : ℝ) (a' : KIdx np) :
    Continuous fun p : GSt K np × KSt np => qKc b E a' p.1 p.2 := by
  unfold qKc
  exact continuous_finsetSum _ fun a _ =>
    (continuous_conj'.comp ((continuous_entry a).comp continuous_snd)).mul
      ((continuous_kC b E a a').comp continuous_fst)

@[fun_prop] theorem continuous_qQ (b E : ℝ) :
    Continuous fun p : GSt K np × KSt np => qQ b E p.1 p.2 := by
  unfold qQ
  exact continuous_finsetSum _ fun a _ =>
    ((continuous_conj'.comp ((continuous_entry a).comp continuous_snd)).mul
      (continuous_qKK b E a)).add
      (((continuous_entry a).comp continuous_snd).mul (continuous_qKc b E a))

@[fun_prop] theorem continuous_sQ (b E : ℝ) :
    Continuous fun p : GSt K np × KSt np => sQ b E p.1 p.2 := by
  unfold sQ
  exact continuous_finsetSum _ fun a _ =>
    ((continuous_conj'.comp ((continuous_entry a).comp continuous_snd)).mul
      ((continuous_trKG b E a).comp continuous_fst)).add
      (((continuous_entry a).comp continuous_snd).mul
        (continuous_conj'.comp ((continuous_trKG b E a).comp continuous_fst)))

/-! ## The generator processes -/

/-- The four components of a point `(J, z)`. -/
abbrev pyG (p : GSt K np × ZK K np) : GSt K np := p.2.1.1
abbrev pxG (p : GSt K np × ZK K np) : GIdx K np → ℂ := p.2.1.2.1
abbrev pyG0 (p : GSt K np × ZK K np) : GSt K np := p.2.1.2.2
abbrev pyK (p : GSt K np × ZK K np) : KSt np := p.2.2.1
abbrev pxK (p : GSt K np × ZK K np) : KIdx np → ℂ := p.2.2.2.1
abbrev pyK0 (p : GSt K np × ZK K np) : KSt np := p.2.2.2.2
abbrev pH (p : GSt K np × ZK K np) : GSt K np := p.2.1.1 + p.1

/-- The cut factor `c₀ = χ(s(Y_0)) ξ(q(Y^𝒦_0))`. -/
def cut0 (χ ξ : ℝ → ℝ) (p : GSt K np × ZK K np) : ℂ := cutC χ (pyG0 p) * cutK ξ (pyK0 p)

def lamK1 (χ ξ : ℝ → ℝ) (b E : ℝ) (a : KIdx np) (p : GSt K np × ZK K np) : ℂ :=
  cut0 χ ξ p *
    (dCut χ ξ b E (pyG p) (pH p) (pyK p) * pxK p a +
      cutC (deriv χ) (pyG p) * cutK ξ (pyK p) * trKG b E a (pH p) +
      cutC χ (pyG p) * cutK (deriv ξ) (pyK p) * qKK b E a (pH p) (pyK p))

def lamK2 (χ ξ : ℝ → ℝ) (b E : ℝ) (a a' : KIdx np) (p : GSt K np × ZK K np) : ℂ :=
  cut0 χ ξ p *
    (dCut χ ξ b E (pyG p) (pH p) (pyK p) * pxK p a * pxK p a' +
      cutC (deriv χ) (pyG p) * cutK ξ (pyK p) *
        (pxK p a' * trKG b E a (pH p) + pxK p a * trKG b E a' (pH p)) +
      cutC χ (pyG p) * cutK (deriv ξ) (pyK p) *
        (pxK p a' * qKK b E a (pH p) (pyK p) + pxK p a * qKK b E a' (pH p) (pyK p)))

def lamKG (χ ξ : ℝ → ℝ) (b E : ℝ) (a : KIdx np) (e : GIdx K np) (p : GSt K np × ZK K np) : ℂ :=
  cut0 χ ξ p *
    (dCut χ ξ b E (pyG p) (pH p) (pyK p) * pxK p a * pxG p e +
      cutC χ (pyG p) * cutK ξ (pyK p) *
        (pxK p a * (drE b E e (pH p) - drE b E e (pH p) * cutC χ (pyG p)) + kG b E a e (pH p)) +
      cutC (deriv χ) (pyG p) * cutK ξ (pyK p) *
        (pxG p e * trKG b E a (pH p) + pxK p a * trCv b E e (pH p)) +
      cutC χ (pyG p) * cutK (deriv ξ) (pyK p) *
        (pxG p e * qKK b E a (pH p) (pyK p) + pxK p a * qG b E e (pH p) (pyK p)))

def lamKC (χ ξ : ℝ → ℝ) (b E : ℝ) (a a' : KIdx np) (p : GSt K np × ZK K np) : ℂ :=
  cut0 χ ξ p *
    (dCut χ ξ b E (pyG p) (pH p) (pyK p) * pxK p a * conj (pxK p a') +
      cutC χ (pyG p) * cutK ξ (pyK p) * kC b E a a' (pH p) +
      cutC (deriv χ) (pyG p) * cutK ξ (pyK p) *
        (conj (pxK p a') * trKG b E a (pH p) + pxK p a * conj (trKG b E a' (pH p))) +
      cutC χ (pyG p) * cutK (deriv ξ) (pyK p) *
        (conj (pxK p a') * qKK b E a (pH p) (pyK p) + pxK p a * qKc b E a' (pH p) (pyK p)))

/-- The cut factor `c₀ χ(s) ξ(q)` at a state. -/
def cutZ (χ ξ : ℝ → ℝ) (z : ZK K np) : ℂ :=
  cutC χ z.1.2.2 * cutK ξ z.2.2.2 * (cutC χ z.1.1 * cutK ξ z.2.1)

def funK1 (χ ξ : ℝ → ℝ) (a : KIdx np) (z : ZK K np) : ℂ := cutZ χ ξ z * z.2.2.1 a

def funK2 (χ ξ : ℝ → ℝ) (a a' : KIdx np) (z : ZK K np) : ℂ :=
  cutZ χ ξ z * z.2.2.1 a * z.2.2.1 a'

def funKG (χ ξ : ℝ → ℝ) (a : KIdx np) (e : GIdx K np) (z : ZK K np) : ℂ :=
  cutZ χ ξ z * z.2.2.1 a * z.1.2.1 e

def funKC (χ ξ : ℝ → ℝ) (a a' : KIdx np) (z : ZK K np) : ℂ :=
  cutZ χ ξ z * z.2.2.1 a * conj (z.2.2.1 a')

variable {Ω : Type*}

/-- `Y^𝒦 = 𝒦 − J_𝒦`. -/
def yKp (E s : ℝ) (τ m : Fin np → ℝ) (Kc : ℝ≥0 → Ω → KSt np) (u : ℝ≥0) (ω : Ω) : KSt np :=
  Kc u ω - kJ E s τ m u

/-- The state of the `𝒦` generator processes. -/
def stZK (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (t : ℝ≥0) (ω : Ω) : ZK K np :=
  (stZ χ b E s τ m G t ω, yKp E s τ m Kc t ω,
    fun a => yKp E s τ m Kc t ω a.1 a.2 - yKp E s τ m Kc 0 ω a.1 a.2, yKp E s τ m Kc 0 ω)

/-- A `𝒦` generator process `F(Z_t) − ∫_0^t Λ(J_u, Z_u)`. -/
def genProcK (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (F : ZK K np → ℂ) (Λ : GSt K np × ZK K np → ℂ) (t : ℝ≥0)
    (ω : Ω) : ℂ :=
  F (stZK χ b E s τ m G Kc t ω) -
    ∫ u in Ioc (0 : ℝ) t, Λ (gramJ b s τ m u.toNNReal, stZK χ b E s τ m G Kc u.toNNReal ω)

def genK1 (χ ξ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (a : KIdx np) : ℝ≥0 → Ω → ℂ :=
  genProcK χ b E s τ m G Kc (funK1 χ ξ a) (lamK1 χ ξ b E a)

def genK2 (χ ξ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (a a' : KIdx np) : ℝ≥0 → Ω → ℂ :=
  genProcK χ b E s τ m G Kc (funK2 χ ξ a a') (lamK2 χ ξ b E a a')

def genKG (χ ξ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (a : KIdx np) (e : GIdx K np) : ℝ≥0 → Ω → ℂ :=
  genProcK χ b E s τ m G Kc (funKG χ ξ a e) (lamKG χ ξ b E a e)

def genKC (χ ξ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω → GSt K np)
    (Kc : ℝ≥0 → Ω → KSt np) (a a' : KIdx np) : ℝ≥0 → Ω → ℂ :=
  genProcK χ b E s τ m G Kc (funKC χ ξ a a') (lamKC χ ξ b E a a')

@[fun_prop] theorem continuous_dCut {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
    (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
    (hξ2 : Continuous (deriv (deriv ξ))) (b E : ℝ) :
    Continuous fun p : GSt K np × GSt K np × KSt np => dCut χ ξ b E p.1 p.2.1 p.2.2 := by
  unfold dCut
  have hs := continuous_sQ (K := K) (np := np) b E
  have hq := continuous_qQ (K := K) (np := np) b E
  fun_prop

theorem continuous_lamK1 {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
    (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
    (hξ2 : Continuous (deriv (deriv ξ))) (b E : ℝ) (a : KIdx np) :
    Continuous (lamK1 (K := K) χ ξ b E a) := by
  have hd := continuous_dCut (K := K) (np := np) hχ hχ1 hχ2 hξ hξ1 hξ2 b E
  have hk := continuous_qKK (K := K) (np := np) b E a
  unfold lamK1 cut0
  fun_prop

theorem continuous_lamK2 {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
    (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
    (hξ2 : Continuous (deriv (deriv ξ))) (b E : ℝ) (a a' : KIdx np) :
    Continuous (lamK2 (K := K) χ ξ b E a a') := by
  have hd := continuous_dCut (K := K) (np := np) hχ hχ1 hχ2 hξ hξ1 hξ2 b E
  have hk := continuous_qKK (K := K) (np := np) b E a
  have hk' := continuous_qKK (K := K) (np := np) b E a'
  unfold lamK2 cut0
  fun_prop

theorem continuous_lamKG {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
    (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
    (hξ2 : Continuous (deriv (deriv ξ))) (b E : ℝ) (a : KIdx np) (e : GIdx K np) :
    Continuous (lamKG χ ξ b E a e) := by
  have hd := continuous_dCut (K := K) (np := np) hχ hχ1 hχ2 hξ hξ1 hξ2 b E
  have hk := continuous_qKK (K := K) (np := np) b E a
  have hg := continuous_qG (K := K) (np := np) b E e
  unfold lamKG cut0
  fun_prop

theorem continuous_lamKC {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hχ1 : Continuous (deriv χ))
    (hχ2 : Continuous (deriv (deriv χ))) (hξ : Continuous ξ) (hξ1 : Continuous (deriv ξ))
    (hξ2 : Continuous (deriv (deriv ξ))) (b E : ℝ) (a a' : KIdx np) :
    Continuous (lamKC (K := K) χ ξ b E a a') := by
  have hd := continuous_dCut (K := K) (np := np) hχ hχ1 hχ2 hξ hξ1 hξ2 b E
  have hk := continuous_qKK (K := K) (np := np) b E a
  have hk' := continuous_qKc (K := K) (np := np) b E a'
  unfold lamKC cut0
  fun_prop

theorem continuous_cutZ {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hξ : Continuous ξ) :
    Continuous (cutZ (K := K) (np := np) χ ξ) := by
  unfold cutZ; fun_prop

theorem continuous_funK1 {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hξ : Continuous ξ) (a : KIdx np) :
    Continuous (funK1 (K := K) χ ξ a) := by
  have := continuous_cutZ (K := K) (np := np) hχ hξ
  unfold funK1; fun_prop

theorem continuous_funK2 {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hξ : Continuous ξ)
    (a a' : KIdx np) : Continuous (funK2 (K := K) χ ξ a a') := by
  have := continuous_cutZ (K := K) (np := np) hχ hξ
  unfold funK2; fun_prop

theorem continuous_funKG {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hξ : Continuous ξ) (a : KIdx np)
    (e : GIdx K np) : Continuous (funKG χ ξ a e) := by
  have := continuous_cutZ (K := K) (np := np) hχ hξ
  unfold funKG; fun_prop

theorem continuous_funKC {χ ξ : ℝ → ℝ} (hχ : Continuous χ) (hξ : Continuous ξ)
    (a a' : KIdx np) : Continuous (funKC (K := K) χ ξ a a') := by
  have := continuous_cutZ (K := K) (np := np) hχ hξ
  unfold funKC; fun_prop

/-! ## Vanishing outside the cut region -/

/-- The cut region of a point: both Gram traces and both `q` within the cutoff radii. -/
def CutReg (Rχ Rξ : ℝ) (p : GSt K np × ZK K np) : Prop :=
  |trRe (pyG p)| ≤ Rχ ∧ |trRe (pyG0 p)| ≤ Rχ ∧ |qK (pyK p)| ≤ Rξ ∧ |qK (pyK0 p)| ≤ Rξ

section VanishK

variable {χ ξ : ℝ → ℝ} {Rχ Rξ : ℝ}
  (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
  (hRξ : ∀ c, Rξ < |c| → ξ c = 0 ∧ deriv ξ c = 0 ∧ deriv (deriv ξ) c = 0)
include hR hRξ

theorem cutReg_of_ne_zero {f : GSt K np × ZK K np → ℂ}
    (h0 : ∀ p, (χ (trRe (pyG p)) = 0 ∧ deriv χ (trRe (pyG p)) = 0 ∧
        deriv (deriv χ) (trRe (pyG p)) = 0) → f p = 0)
    (h1 : ∀ p, χ (trRe (pyG0 p)) = 0 → f p = 0)
    (h2 : ∀ p, (ξ (qK (pyK p)) = 0 ∧ deriv ξ (qK (pyK p)) = 0 ∧
        deriv (deriv ξ) (qK (pyK p)) = 0) → f p = 0)
    (h3 : ∀ p, ξ (qK (pyK0 p)) = 0 → f p = 0) {p : GSt K np × ZK K np} (hp : f p ≠ 0) :
    CutReg Rχ Rξ p := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra h' <;> push Not at h'
  · exact hp (h0 p (hR _ h'))
  · exact hp (h1 p (hR _ h').1)
  · exact hp (h2 p (hRξ _ h'))
  · exact hp (h3 p (hRξ _ h').1)

theorem lamK1_cutReg (b E : ℝ) (a : KIdx np) {p : GSt K np × ZK K np}
    (hp : lamK1 χ ξ b E a p ≠ 0) : CutReg Rχ Rξ p :=
  cutReg_of_ne_zero hR hRξ
    (fun p ⟨h1, h2, h3⟩ => by simp [lamK1, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamK1, cut0, cutC, h1])
    (fun p ⟨h1, h2, h3⟩ => by simp [lamK1, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamK1, cut0, cutK, h1]) hp

theorem lamK2_cutReg (b E : ℝ) (a a' : KIdx np) {p : GSt K np × ZK K np}
    (hp : lamK2 χ ξ b E a a' p ≠ 0) : CutReg Rχ Rξ p :=
  cutReg_of_ne_zero hR hRξ
    (fun p ⟨h1, h2, h3⟩ => by simp [lamK2, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamK2, cut0, cutC, h1])
    (fun p ⟨h1, h2, h3⟩ => by simp [lamK2, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamK2, cut0, cutK, h1]) hp

theorem lamKG_cutReg (b E : ℝ) (a : KIdx np) (e : GIdx K np) {p : GSt K np × ZK K np}
    (hp : lamKG χ ξ b E a e p ≠ 0) : CutReg Rχ Rξ p :=
  cutReg_of_ne_zero hR hRξ
    (fun p ⟨h1, h2, h3⟩ => by simp [lamKG, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamKG, cut0, cutC, h1])
    (fun p ⟨h1, h2, h3⟩ => by simp [lamKG, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamKG, cut0, cutK, h1]) hp

theorem lamKC_cutReg (b E : ℝ) (a a' : KIdx np) {p : GSt K np × ZK K np}
    (hp : lamKC χ ξ b E a a' p ≠ 0) : CutReg Rχ Rξ p :=
  cutReg_of_ne_zero hR hRξ
    (fun p ⟨h1, h2, h3⟩ => by simp [lamKC, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamKC, cut0, cutC, h1])
    (fun p ⟨h1, h2, h3⟩ => by simp [lamKC, cut0, dCut, cutC, cutK, h1, h2, h3])
    (fun p h1 => by simp [lamKC, cut0, cutK, h1]) hp

/-- A state function `cutZ · P` vanishes off the cut region (read at `(0, z)`). -/
theorem funK_cutReg {F P : ZK K np → ℂ} (hF : ∀ z, F z = cutZ χ ξ z * P z)
    {z : ZK K np} (hz : F z ≠ 0) : CutReg Rχ Rξ ((0 : GSt K np), z) := by
  refine cutReg_of_ne_zero hR hRξ (f := fun p => F p.2)
    (fun p ⟨h1, _, _⟩ => by simp only [hF, cutZ, cutC, h1]; simp)
    (fun p h1 => by simp only [hF, cutZ, cutC, h1]; simp)
    (fun p ⟨h1, _, _⟩ => by simp only [hF, cutZ, cutK, h1]; simp)
    (fun p h1 => by simp only [hF, cutZ, cutK, h1]; simp) hz

end VanishK

/-! ## Continuity and bounds -/

variable {b E s : ℝ} {τ m : Fin np → ℝ} {G : ℝ≥0 → Ω → GSt K np} {Kc : ℝ≥0 → Ω → KSt np}

theorem continuous_stZK (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u) {χ : ℝ → ℝ} (hχ : Continuous χ)
    (ω : Ω) : Continuous fun t => stZK χ b E s τ m G Kc t ω :=
  (continuous_stZ hc hχ ω).prodMk ((hkc ω).prodMk ((continuous_pi fun (a : KIdx np) =>
    ((hkc ω).matrix_elem a.1 a.2).sub continuous_const).prodMk continuous_const))

theorem continuous_genProcK (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u) {χ : ℝ → ℝ} (hχ : Continuous χ)
    {F : ZK K np → ℂ} {Λ : GSt K np × ZK K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ)
    (ω : Ω) : Continuous fun t => genProcK χ b E s τ m G Kc F Λ t ω := by
  have hZ := continuous_stZK hc hkc hχ ω
  have h := continuous_primitive_gramJ (K := K) (np := np) (b := b) (s := s) (τ := τ) (m := m)
    (𝒵 := ZK K np) hΛ hZ
  exact (hF.comp hZ).sub h

/-- **A `𝒦` generator process is a.s. bounded on every `[0, T]`.** -/
theorem exists_bound_genProcK [MeasurableSpace Ω] {Q : Measure Ω}
    (hfe : ∀ᵐ ω ∂Q, ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    {χ : ℝ → ℝ} (hχ : Continuous χ) {Rχ Rξ : ℝ}
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
    {F : ZK K np → ℂ} {Λ : GSt K np × ZK K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ)
    (hFv : ∀ z, F z ≠ 0 → CutReg Rχ Rξ ((0 : GSt K np), z))
    (hΛv : ∀ p, Λ p ≠ 0 → CutReg Rχ Rξ p) (T : ℝ≥0) :
    ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ T, ‖genProcK χ b E s τ m G Kc F Λ v ω‖ ≤ C := by
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
  set BK := Rξ + 1
  set boxK : Set (KSt np) := Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall (0 : ℂ) BK
  have hboxK : IsCompact boxK :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hYK : ∀ y : KSt np, |qK y| ≤ Rξ → ∀ a : KIdx np, ‖y a.1 a.2‖ ≤ BK := fun y hy a => by
    have h1 : ‖y a.1 a.2‖ ^ 2 ≤ qK y :=
      Finset.single_le_sum (f := fun a : KIdx np => ‖y a.1 a.2‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ a)
    have h2 := norm_le_sq_add_one (y a.1 a.2)
    linarith [le_abs_self (qK y)]
  have hYKm : ∀ y : KSt np, |qK y| ≤ Rξ → y ∈ boxK := fun y hy i _ j _ => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hYK y hy (i, j)
  set KregK : Set (ZK K np) := Kreg ×ˢ boxK ×ˢ
    (Set.pi univ fun _ => Metric.closedBall (0 : ℂ) (BK + BK)) ×ˢ boxK
  have hKregK : IsCompact KregK :=
    hKreg.prod (hboxK.prod ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod hboxK))
  have hZK : ∀ ω, (∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) → ∀ u ≤ T,
      ∀ J : GSt K np, CutReg Rχ Rξ (J, stZK χ b E s τ m G Kc u ω) →
        stZK χ b E s τ m G Kc u ω ∈ KregK := fun ω hω u hu J ⟨h1, h2, h3, h4⟩ => by
    refine ⟨hZ ω hω u hu h1 h2, hYKm _ h3, fun (a : KIdx np) _ => ?_, hYKm _ h4⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_sub_le _ _).trans (add_le_add (hYK _ h3 a) (hYK _ h4 a))
  obtain ⟨C1, hC1⟩ := exists_bound_finite_compact hΛ (finite_range_gramJ (K := K) b s τ m)
    hKregK
  obtain ⟨C2, hC2⟩ := hKregK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C2 0 + max C1 0 * T, hfe.mono fun ω hω v hv => ?_⟩
  unfold genProcK
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · by_cases h0 : F (stZK χ b E s τ m G Kc v ω) = 0
    · rw [h0, norm_zero]; exact le_max_right _ _
    · exact (hC2 _ (hZK ω hω v hv 0 (hFv _ h0))).trans (le_max_left _ _)
  · have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) v)
      (f := fun w => Λ (gramJ b s τ m w.toNNReal, stZK χ b E s τ m G Kc w.toNNReal ω))
      (C := max C1 0) measure_Ioc_lt_top fun w hw => by
        by_cases h0 : Λ (gramJ b s τ m w.toNNReal, stZK χ b E s τ m G Kc w.toNNReal ω) = 0
        · rw [h0, norm_zero]; exact le_max_right _ _
        · have hwT : w.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hw.2).trans hv
          exact (hC1 _ ⟨_, rfl⟩ _ (hZK ω hω _ hwT _ (hΛv _ h0))).trans (le_max_left _ _)
    rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg v)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hv) (le_max_right _ _))

/-- **From a `𝒦` generator process off the birth times to the stopped identities.** -/
theorem isTestedMart_stopped_of_genK [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {tseq : Ω → ℕ → ℝ}
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
    (hfe : ∀ᵐ ω ∂Q, ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    {χ : ℝ → ℝ} (hχ : Continuous χ) {Rχ Rξ : ℝ}
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
    {F : ZK K np → ℂ} {Λ : GSt K np × ZK K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ)
    (hFv : ∀ z, F z ≠ 0 → CutReg Rχ Rξ ((0 : GSt K np), z))
    (hΛv : ∀ p, Λ p ≠ 0 → CutReg Rχ Rξ p)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsAEStop Q (complexObs tseq G Kc) hobs σ)
    {X : ℝ≥0 → Ω → ℂ}
    (hXeq : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, (v : WithTop ℝ≥0) ≤ σ ω →
      genProcK χ b E s τ m G Kc F Λ v ω = X v ω)
    (hoff : IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
      (genProcK χ b E s τ m G Kc F Λ)) :
    IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess X σ) := by
  have hcont := continuous_genProcK hc hkc hχ hF hΛ
  have hbd := exists_bound_genProcK (b := b) (E := E) (s := s) (τ := τ) (m := m) (Kc := Kc)
    hfe hχ hR hF hΛ hFv hΛv
  have hfull := isTestedMart_of_off (birthTimes_finite s τ) hobs
    (tendsto_complexObs_right hc hkc) hcont hbd hoff
  obtain ⟨ρ, hρ, hρe⟩ := hσ
  have hst := isTestedMart_stoppedProcess_of_tested hobs hfull hcont hbd hρ
  refine isTestedMart_of_ae_eq hst fun t => ?_
  filter_upwards [hρe, hXeq] with ω h1 h2
  simp only [stoppedProcess, h1]
  exact (h2 _ (by rw [coe_untopA_min']; exact min_le_right _ _)).symm

/-! ## Before `σ_L ∧ ρ_M` the processes are the `𝒦` clauses -/

section RegionK

variable {χ ξ : ℝ → ℝ} {ω : Ω} {v : ℝ≥0}
  (h0 : χ (trRe (gY b s τ m G 0 ω)) = 1) (h0K : ξ (qK (yKp E s τ m Kc 0 ω)) = 1)
  (hreg : ∀ u : ℝ≥0, 0 < u → u ≤ v → χ (trRe (gY b s τ m G u ω)) = 1 ∧
    deriv χ (trRe (gY b s τ m G u ω)) = 0 ∧ deriv (deriv χ) (trRe (gY b s τ m G u ω)) = 0)
  (hregK : ∀ u : ℝ≥0, 0 < u → u ≤ v → ξ (qK (yKp E s τ m Kc u ω)) = 1 ∧
    deriv ξ (qK (yKp E s τ m Kc u ω)) = 0 ∧ deriv (deriv ξ) (qK (yKp E s τ m Kc u ω)) = 0)
include h0 h0K hreg hregK

theorem genK1_eq (hv : 0 < v) (a : KIdx np) :
    genK1 χ ξ b E s τ m G Kc a v ω = cComp b E s τ m G Kc (Sum.inr a) v ω := by
  have hz : EqOn (fun u : ℝ => lamK1 χ ξ b E a (gramJ b s τ m u.toNNReal,
      stZK χ b E s τ m G Kc u.toNNReal ω)) (fun _ => (0 : ℂ)) (Ioc (0 : ℝ) v) := fun u hu => by
    obtain ⟨h1, h2, h3⟩ := hreg _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    obtain ⟨k1, k2, k3⟩ := hregK _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    simp only [lamK1, cut0, dCut, stZK, stZ, pyG, pyG0, pyK, pyK0, pxK, pH, cutC, cutK, h0, h0K,
      h1, h2, h3, k1, k2, k3, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  obtain ⟨hv1, -, -⟩ := hreg v hv le_rfl
  obtain ⟨hvK, -, -⟩ := hregK v hv le_rfl
  unfold genK1 genProcK
  rw [setIntegral_congr_fun measurableSet_Ioc hz, integral_zero, sub_zero]
  simp only [funK1, cutZ, stZK, stZ, cutC, cutK, h0, h0K, hv1, hvK, Complex.ofReal_one, one_mul]
  rw [cComp_inr]
  rfl

theorem genK2_eq (hv : 0 < v) (a a' : KIdx np) :
    genK2 χ ξ b E s τ m G Kc a a' v ω =
      cBr b E s τ m G Kc (Sum.inr a) (Sum.inr a') v ω := by
  have hz : EqOn (fun u : ℝ => lamK2 χ ξ b E a a' (gramJ b s τ m u.toNNReal,
      stZK χ b E s τ m G Kc u.toNNReal ω)) (fun _ => (0 : ℂ)) (Ioc (0 : ℝ) v) := fun u hu => by
    obtain ⟨h1, h2, h3⟩ := hreg _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    obtain ⟨k1, k2, k3⟩ := hregK _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    simp only [lamK2, cut0, dCut, stZK, stZ, pyG, pyG0, pyK, pyK0, pxK, pH, cutC, cutK, h0, h0K,
      h1, h2, h3, k1, k2, k3, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  obtain ⟨hv1, -, -⟩ := hreg v hv le_rfl
  obtain ⟨hvK, -, -⟩ := hregK v hv le_rfl
  have hb : cBr b E s τ m G Kc (Sum.inr a) (Sum.inr a') v ω =
      cComp b E s τ m G Kc (Sum.inr a) v ω * cComp b E s τ m G Kc (Sum.inr a') v ω := by
    simp [cBr, cCov]
  unfold genK2 genProcK
  rw [setIntegral_congr_fun measurableSet_Ioc hz, integral_zero, sub_zero, hb, cComp_inr,
    cComp_inr]
  simp only [funK2, cutZ, stZK, stZ, cutC, cutK, h0, h0K, hv1, hvK, Complex.ofReal_one, one_mul]
  rfl

theorem genKG_eq (hv : 0 < v) (a : KIdx np) (e : GIdx K np) :
    genKG χ ξ b E s τ m G Kc a e v ω =
      cBr b E s τ m G Kc (Sum.inr a) (Sum.inl e) v ω := by
  have hz : EqOn (fun u : ℝ => lamKG χ ξ b E a e (gramJ b s τ m u.toNNReal,
      stZK χ b E s τ m G Kc u.toNNReal ω))
      (fun u : ℝ => kGramCov b E a e (G u.toNNReal ω)) (Ioc (0 : ℝ) v) := fun u hu => by
    obtain ⟨h1, h2, h3⟩ := hreg _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    obtain ⟨k1, k2, k3⟩ := hregK _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    simp only [lamKG, cut0, dCut, stZK, stZ, pyG, pyG0, pyK, pyK0, pxK, pxG, pH, cutC, cutK, h0,
      h0K, h1, h2, h3, k1, k2, k3, Complex.ofReal_one, Complex.ofReal_zero]
    simp only [gY, sub_add_cancel, kG]
    ring
  obtain ⟨hv1, -, -⟩ := hreg v hv le_rfl
  obtain ⟨hvK, -, -⟩ := hregK v hv le_rfl
  unfold genKG genProcK
  rw [setIntegral_congr_fun measurableSet_Ioc hz]
  simp only [funKG, cutZ, stZK, stZ, cutC, cutK, h0, h0K, hv1, hvK, Complex.ofReal_one, one_mul]
  rw [genX_eq_cComp hreg Kc e, cBr, cComp_inr]
  rfl

theorem genKC_eq (hv : 0 < v) (a a' : KIdx np) :
    genKC χ ξ b E s τ m G Kc a a' v ω = kBr b E s τ m G Kc a a' v ω := by
  have hz : EqOn (fun u : ℝ => lamKC χ ξ b E a a' (gramJ b s τ m u.toNNReal,
      stZK χ b E s τ m G Kc u.toNNReal ω))
      (fun u : ℝ => kConjCov (K := K) b E a a' (G u.toNNReal ω)) (Ioc (0 : ℝ) v) :=
    fun u hu => by
    obtain ⟨h1, h2, h3⟩ := hreg _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    obtain ⟨k1, k2, k3⟩ := hregK _ (toNNReal_mem_of_Ioc hu).1 (toNNReal_mem_of_Ioc hu).2
    simp only [lamKC, cut0, dCut, stZK, stZ, pyG, pyG0, pyK, pyK0, pxK, pH, cutC, cutK, h0, h0K,
      h1, h2, h3, k1, k2, k3, Complex.ofReal_one, Complex.ofReal_zero]
    simp only [gY, sub_add_cancel, kC]
    ring
  obtain ⟨hv1, -, -⟩ := hreg v hv le_rfl
  obtain ⟨hvK, -, -⟩ := hregK v hv le_rfl
  unfold genKC genProcK
  rw [setIntegral_congr_fun measurableSet_Ioc hz]
  simp only [funKC, cutZ, stZK, stZ, cutC, cutK, h0, h0K, hv1, hvK, Complex.ofReal_one, one_mul]
  rw [kBr, cComp_inr, cComp_inr]
  rfl

end RegionK

/-! ## The generator hypothesis and the reductions -/

/-- **The generator hypothesis `CapIdentKDoubleGen`** (no stop): under the premises of
`CapIdentKDouble` and the Gram identities, for all `C³` cutoffs `χ`, `ξ` with compact support, the
four `𝒦` generator processes have tested increments with all times off the birth times. -/
def CapIdentKDoubleGen : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    IsGramCoordTested b E s τ m Q tseq G Kc (gramTraceStop G) →
    ∀ χ ξ : ℝ → ℝ, ContDiff ℝ 3 χ → HasCompactSupport χ → ContDiff ℝ 3 ξ →
      HasCompactSupport ξ →
      (∀ a : KIdx np, IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
        (genK1 χ ξ b E s τ m G Kc a)) ∧
      (∀ a a' : KIdx np, IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
        (genK2 χ ξ b E s τ m G Kc a a')) ∧
      (∀ (a : KIdx np) (e : GIdx K np), IsTestedMartOff (birthTimes s τ) Q
        (complexObs tseq G Kc) (genKG χ ξ b E s τ m G Kc a e)) ∧
      ∀ a a' : KIdx np, IsTestedMartOff (birthTimes s τ) Q (complexObs tseq G Kc)
        (genKC χ ξ b E s τ m G Kc a a')

/-- **`CapIdentKDouble` from `CapIdentKDoubleGen`** (every `L` and `M`). -/
theorem capIdentKDouble_of_gen (hpin : CapIdentKDoubleGen) : CapIdentKDouble := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr M
  have hgen := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr
  obtain ⟨hD, hlim, hA, hne, hφ, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, hfdd⟩ := hP
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, hm, -⟩, hs, hτ, hh0, -, -⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  have hcap := hφ.eventually (eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh0 hA hne)
  have hfe := ae_feasible_all hD hφ hfdd hobs hcap hc
  have hK0 : ∀ᵐ ω ∂Q, Kc 0 ω - kJ E s τ m 0 = 0 :=
    (ae_kc_zero hb1 hE1 hE2 hτ hfdd hobs hcap).mono fun ω hω => by rw [hω, kJ_zero hτ, sub_zero]
  have hlev : ∀ L, IsKCoordTestedAt b E s τ m Q tseq G Kc
      (fun ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω)) := fun L => by
    obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
    set R0 := max (|L| + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) 0 with hR0
    obtain ⟨χ, hχ3, hχs, hχ1⟩ :=
      exists_bump (R0 + 1) (add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos)
    set RK := (Fintype.card (KIdx np) : ℝ) * (max (M : ℝ) 0) ^ 2 with hRK
    have hRK0 : 0 ≤ RK := by positivity
    obtain ⟨ξ, hξ3, hξs, hξ1⟩ := exists_bump (RK + 1) (by linarith)
    obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ3
    obtain ⟨hξc, hξd, hξdd⟩ := cut_continuity hξ3
    obtain ⟨Rχ, hRχ⟩ := exists_cut_radius hχs
    obtain ⟨Rξ, hRξ⟩ := exists_cut_radius hξs
    obtain ⟨g1, g2, g3, g4⟩ := hgen χ ξ hχ3 hχs hξ3 hξs
    have hσ := (isAEStop_gramTraceStop (Q := Q) hobs hc hb1 hm L).min
      (isAEStop_kLevelStop hobs hkc (M : ℝ))
    have hreg : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0,
        (v : WithTop ℝ≥0) ≤ min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω) → 0 < v →
        χ (trRe (gY b s τ m G 0 ω)) = 1 ∧ ξ (qK (yKp E s τ m Kc 0 ω)) = 1 ∧
        (∀ u : ℝ≥0, 0 < u → u ≤ v → χ (trRe (gY b s τ m G u ω)) = 1 ∧
          deriv χ (trRe (gY b s τ m G u ω)) = 0 ∧
            deriv (deriv χ) (trRe (gY b s τ m G u ω)) = 0) ∧
        ∀ u : ℝ≥0, 0 < u → u ≤ v → ξ (qK (yKp E s τ m Kc u ω)) = 1 ∧
          deriv ξ (qK (yKp E s τ m Kc u ω)) = 0 ∧
            deriv (deriv ξ) (qK (yKp E s τ m Kc u ω)) = 0 := by
      filter_upwards [hfe, hK0] with ω hω h0 v hv hv0
      have hvσ : (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω := hv.trans (min_le_left _ _)
      have hvρ : (v : WithTop ℝ≥0) ≤ kLevelStop E s τ m Kc M ω := hv.trans (min_le_right _ _)
      have hσ0 : (0 : WithTop ℝ≥0) < gramTraceStop G L ω :=
        lt_of_lt_of_le (WithTop.coe_lt_coe.2 hv0) hvσ
      have hb' : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ gramTraceStop G L ω →
          |trRe (gY b s τ m G u ω)| < R0 + 1 := fun u hu =>
        ((abs_trRe_gY_le_stop hω (hc ω) hCJ hu hσ0).trans (le_max_left _ _)).trans_lt
          (lt_add_one _)
      have hq : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ kLevelStop E s τ m Kc M ω →
          |qK (yKp E s τ m Kc u ω)| < RK + 1 := fun u hu => by
        have hsum := kLevel_sum_le (hkc ω) h0 hu
        have hq0 : 0 ≤ qK (yKp E s τ m Kc u ω) := Finset.sum_nonneg fun _ _ => by positivity
        have hqle : qK (yKp E s τ m Kc u ω) ≤ RK := by
          have := Finset.sum_le_card_nsmul (Finset.univ : Finset (KIdx np))
            (fun a => ‖yKp E s τ m Kc u ω a.1 a.2‖ ^ 2) ((max (M : ℝ) 0) ^ 2) (fun a _ => by
              have h1 : ‖yKp E s τ m Kc u ω a.1 a.2‖ ≤ max (M : ℝ) 0 :=
                (norm_entry_le_sum (yKp E s τ m Kc u ω) a.1 a.2).trans hsum
              exact pow_le_pow_left₀ (norm_nonneg _) h1 2)
          simpa [nsmul_eq_mul, hRK, qK] using this
        rw [abs_of_nonneg hq0]
        linarith
      refine ⟨(hχ1 _ (hb' 0 (by rw [WithTop.coe_zero]; exact bot_le))).1,
        (hξ1 _ (hq 0 (by rw [WithTop.coe_zero]; exact bot_le))).1,
        fun u _ huv => hχ1 _ (hb' u ((WithTop.coe_le_coe.2 huv).trans hvσ)),
        fun u _ huv => hξ1 _ (hq u ((WithTop.coe_le_coe.2 huv).trans hvρ))⟩
    refine ⟨fun a => isTestedMart_stopped_of_genK hobs hc hkc hfe hχc hRχ
        (continuous_funK1 hχc hξc a) (continuous_lamK1 hχc hχd hχdd hξc hξd hξdd b E a)
        (fun z hz => funK_cutReg hRχ hRξ (P := fun z => z.2.2.1 a) (fun _ => rfl) hz)
        (fun p hp => lamK1_cutReg hRχ hRξ b E a hp) hσ ?_ (g1 a),
      fun a a' => isTestedMart_stopped_of_genK hobs hc hkc hfe hχc hRχ
        (continuous_funK2 hχc hξc a a') (continuous_lamK2 hχc hχd hχdd hξc hξd hξdd b E a a')
        (fun z hz => funK_cutReg hRχ hRξ (P := fun z => z.2.2.1 a * z.2.2.1 a')
          (fun _ => mul_assoc _ _ _) hz)
        (fun p hp => lamK2_cutReg hRχ hRξ b E a a' hp) hσ ?_ (g2 a a'),
      fun a e => isTestedMart_stopped_of_genK hobs hc hkc hfe hχc hRχ
        (continuous_funKG hχc hξc a e) (continuous_lamKG hχc hχd hχdd hξc hξd hξdd b E a e)
        (fun z hz => funK_cutReg hRχ hRξ (P := fun z => z.2.2.1 a * z.1.2.1 e)
          (fun _ => mul_assoc _ _ _) hz)
        (fun p hp => lamKG_cutReg hRχ hRξ b E a e hp) hσ ?_ (g3 a e),
      fun a a' => isTestedMart_stopped_of_genK hobs hc hkc hfe hχc hRχ
        (continuous_funKC hχc hξc a a') (continuous_lamKC hχc hχd hχdd hξc hξd hξdd b E a a')
        (fun z hz => funK_cutReg hRχ hRξ (P := fun z => z.2.2.1 a * conj (z.2.2.1 a'))
          (fun _ => mul_assoc _ _ _) hz)
        (fun p hp => lamKC_cutReg hRχ hRξ b E a a' hp) hσ ?_ (g4 a a')⟩
    · filter_upwards [hreg] with ω hω v hv
      rcases eq_zero_or_pos v with h0 | h0
      · subst h0
        simp [genProcK, funK1, stZK, cComp, cEntry]
      · obtain ⟨a1, a2, a3, a4⟩ := hω v hv h0
        exact genK1_eq a1 a2 a3 a4 h0 a
    · filter_upwards [hreg] with ω hω v hv
      rcases eq_zero_or_pos v with h0 | h0
      · subst h0
        simp [genProcK, funK2, stZK, cBr, cComp, cEntry]
      · obtain ⟨a1, a2, a3, a4⟩ := hω v hv h0
        exact genK2_eq a1 a2 a3 a4 h0 a a'
    · filter_upwards [hreg] with ω hω v hv
      rcases eq_zero_or_pos v with h0 | h0
      · subst h0
        simp [genProcK, funKG, stZK, cBr, cComp, cEntry]
      · obtain ⟨a1, a2, a3, a4⟩ := hω v hv h0
        exact genKG_eq a1 a2 a3 a4 h0 a e
    · filter_upwards [hreg] with ω hω v hv
      rcases eq_zero_or_pos v with h0 | h0
      · subst h0
        simp [genProcK, funKC, stZK, kBr, cComp, cEntry]
      · obtain ⟨a1, a2, a3, a4⟩ := hω v hv h0
        exact genKC_eq a1 a2 a3 a4 h0 a a'
  exact ⟨fun L a => (hlev L).drift a, fun L a a' => (hlev L).bracketK a a',
    fun L a e => (hlev L).bracketG a e, fun L a a' => (hlev L).conjBr a a'⟩

/-- **`TargetCapIdentAll` from the entrance, the two generator hypotheses and the `𝒦` stop.** -/
theorem targetCapIdentAll_of_gen (hEnt : CapIdentEntrance) (hGr : CapIdentGramGen)
    (hKD : CapIdentKDoubleGen) (hKS : CapIdentKStop) : TargetCapIdentAll :=
  targetCapIdentAll_of_pins hEnt (capIdentGram_of_gen hGr) (capIdentKDouble_of_gen hKD) hKS

/-- **`TargetCapCond'` from the entrance, the two generator hypotheses and the `𝒦` stop.** -/
theorem targetCapCond'_of_gen (hEnt : CapIdentEntrance) (hGr : CapIdentGramGen)
    (hKD : CapIdentKDoubleGen) (hKS : CapIdentKStop) : TargetCapCond' :=
  targetCapCond'_of_identPins hEnt (capIdentGram_of_gen hGr) (capIdentKDouble_of_gen hKD) hKS

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram
