module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWMeas

/-!
# The jets of the four drift-free tests and their generator

The basic increments of one step are indexed by `BI K np = GIdx ⊕ KIdx ⊕ KIdx`:
`inl e ↦ dG_e`, `inr (inl a) ↦ d𝒦_a`, `inr (inr a) ↦ conj d𝒦_a` (`bvec`). A conjugate Gram
increment is the Gram increment of `e*` (Hermitian symmetry), so it needs no index.

* `jF χ ξ κ z`: the jet `c₀ · (χ(s) ξ(q)) · P` of the test `κ` at the state `z`, built from the
  atomic jets of `s = Re Tr Y`, `q = Σ|Y^𝒦_a|²` and the coordinates in `P`
  (`(jF χ ξ κ z).v = κ.fn χ ξ z`, `jF_v`).
* **`gen_jF`**: `gen dvec Bmat (jF χ ξ κ z) = κ.lam χ ξ b E (J, z)` with `H = Y + J`, for all four
  tests. This is the generator computation (Itô's product and chain rules) as an identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate

variable {K np : ℕ}

/-- The basic increment indices. -/
abbrev BI (K np : ℕ) := GIdx K np ⊕ KIdx np ⊕ KIdx np

/-- The basis vector of index `i`. -/
def ev (i : BI K np) : BI K np → ℂ := fun i' => if i' = i then 1 else 0

/-!
## Bilinear algebra of `br`
-/

section Br

variable (B : BI K np → BI K np → ℂ)

theorem lin_ev (i : BI K np) (β : BI K np → ℂ) : lin (ev i) β = β i := by
  simp [lin, ev]

theorem br_ev_ev (i i' : BI K np) : br B (ev i) (ev i') = B i i' := by
  simp [br, ev, ite_mul]

theorem br_add_left (l l' m : BI K np → ℂ) :
    br B (fun i => l i + l' i) m = br B l m + br B l' m := by
  simp only [br, add_mul, sum_add_distrib]

theorem br_add_right (l m m' : BI K np → ℂ) :
    br B l (fun i => m i + m' i) = br B l m + br B l m' := by
  simp only [br, mul_add, add_mul, sum_add_distrib]

theorem br_smul_left (c : ℂ) (l m : BI K np → ℂ) :
    br B (fun i => c * l i) m = c * br B l m := by
  simp only [br, mul_sum, mul_assoc]

theorem br_smul_right (c : ℂ) (l m : BI K np → ℂ) :
    br B l (fun i => c * m i) = c * br B l m := by
  simp only [br, mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem br_sum_left {α : Type*} [Fintype α] (f : α → BI K np → ℂ) (m : BI K np → ℂ) :
    br B (fun i => ∑ k, f k i) m = ∑ k, br B (f k) m := by
  simp only [br, sum_mul]
  rw [eq_comm, Finset.sum_comm]
  exact sum_congr rfl fun _ _ => by rw [Finset.sum_comm]

theorem br_sum_right {α : Type*} [Fintype α] (l : BI K np → ℂ) (f : α → BI K np → ℂ) :
    br B l (fun i => ∑ k, f k i) = ∑ k, br B l (f k) := by
  simp only [br, mul_sum, sum_mul]
  rw [eq_comm, Finset.sum_comm]
  exact sum_congr rfl fun _ _ => by rw [Finset.sum_comm]

theorem br_zero_left (m : BI K np → ℂ) : br B (fun _ => 0) m = 0 := by simp [br]

end Br

/-!
## Atomic jets
-/

/-- The linear form of `s = Re Tr Y`: `Σ_k e_{(0,k,k)}`. -/
def lS : BI K np → ℂ := fun i => ∑ k : SrcCol K (Fin np), ev (Sum.inl ((0 : Fin 2), k, k)) i

/-- The linear form of `q = Σ_a |y_a|²`: `Σ_a (conj y_a e_{𝒦 a} + y_a e_{𝒦̄ a})`. -/
def lQ (y : KSt np) : BI K np → ℂ := fun i =>
  ∑ a : KIdx np, (conj (y a.1 a.2) * ev (Sum.inr (Sum.inl a)) i +
    y a.1 a.2 * ev (Sum.inr (Sum.inr a)) i)

/-- The quadratic form of `q`: `Σ_a e_{𝒦 a} ⊗ e_{𝒦̄ a}`. -/
def qQ0 : BI K np → BI K np → ℂ := fun i i' =>
  ∑ a : KIdx np, ev (Sum.inr (Sum.inl a)) i * ev (Sum.inr (Sum.inr a)) i'

def jS (z : ZK K np) : Jet (BI K np) := ⟨(trRe z.1.1 : ℂ), lS, fun _ _ => 0⟩

def jQ (z : ZK K np) : Jet (BI K np) := ⟨(qK z.2.1 : ℂ), lQ z.2.1, qQ0⟩

def jX (a : KIdx np) (z : ZK K np) : Jet (BI K np) :=
  ⟨z.2.2.1 a, ev (Sum.inr (Sum.inl a)), fun _ _ => 0⟩

def jXc (a : KIdx np) (z : ZK K np) : Jet (BI K np) :=
  ⟨conj (z.2.2.1 a), ev (Sum.inr (Sum.inr a)), fun _ _ => 0⟩

def jY (e : GIdx K np) (z : ZK K np) : Jet (BI K np) :=
  ⟨kHatE e z, ev (Sum.inl e), fun _ _ => 0⟩

/-- The jet of the polynomial part of a test. -/
def jP : KTest K np → ZK K np → Jet (BI K np)
  | .k1 a => jX a
  | .k2 a a' => fun z => (jX a z).mul (jX a' z)
  | .ky a e => fun z => (jX a z).mul (jY e z)
  | .kc a a' => fun z => (jX a z).mul (jXc a' z)

/-- The jet of `χ(s)`. -/
def jChi (χ : ℝ → ℝ) (z : ZK K np) : Jet (BI K np) :=
  Jet.chain χ (deriv χ) (deriv (deriv χ)) (trRe z.1.1) (jS z)

/-- The jet of `ξ(q)`. -/
def jXi (ξ : ℝ → ℝ) (z : ZK K np) : Jet (BI K np) :=
  Jet.chain ξ (deriv ξ) (deriv (deriv ξ)) (qK z.2.1) (jQ z)

/-- **The jet of a test** `c₀ · (χ(s) ξ(q)) · P`. -/
def jF (χ ξ : ℝ → ℝ) (κ : KTest K np) (z : ZK K np) : Jet (BI K np) :=
  (Jet.const (cutC χ z.1.2.2 * cutK ξ z.2.2.2)).mul (((jChi χ z).mul (jXi ξ z)).mul (jP κ z))

theorem jF_v (χ ξ : ℝ → ℝ) (κ : KTest K np) (z : ZK K np) : (jF χ ξ κ z).v = κ.fn χ ξ z := by
  rcases κ with a | ⟨a, a'⟩ | ⟨a, e⟩ | ⟨a, a'⟩ <;>
    simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jX, jY, jXc, KTest.fn, funK1,
      funK2, funKY, funKC, cutZ, cutC, cutK] <;> ring

/-!
## The coefficients of the model
-/

/-- The drift vector at `H`: `drE` on Gram coordinates, `0` on `𝒦` coordinates. -/
def dvec (b E : ℝ) (H : GSt K np) : BI K np → ℂ
  | Sum.inl e => drE b E e H
  | Sum.inr _ => 0

/-- The bracket matrix at `H`. -/
def Bmat (b E : ℝ) (H : GSt K np) : BI K np → BI K np → ℂ
  | Sum.inl e, Sum.inl e' => cvE b E e e' H
  | Sum.inl e, Sum.inr (Sum.inl a) => kG b E a e H
  | Sum.inl e, Sum.inr (Sum.inr a) => conj (kG b E a (eStar e) H)
  | Sum.inr (Sum.inl a), Sum.inl e => kG b E a e H
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl a), Sum.inr (Sum.inr a') => kC b E a a' H
  | Sum.inr (Sum.inr a), Sum.inl e => conj (kG b E a (eStar e) H)
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inl a') => conj (kC b E a a' H)
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => 0

section Coeff

variable (b E : ℝ) (H : GSt K np) (y : KSt np)

theorem gen_jS (z : ZK K np) : gen (dvec b E H) (Bmat b E H) (jS z) = trDr b E H := by
  simp only [gen, jS, zero_mul, sum_const_zero, add_zero, trDr]
  simp only [lin, lS, sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => ?_
  simp [ev, dvec]

theorem gen_jQ (z : ZK K np) : gen (dvec b E H) (Bmat b E H) (jQ z) = dQ b E H := by
  unfold gen jQ
  have h1 : lin (lQ (K := K) z.2.1) (dvec b E H) = 0 := by
    simp only [lin, lQ, sum_mul]
    refine sum_eq_zero fun i _ => sum_eq_zero fun a _ => ?_
    rcases i with e | a' | a' <;> simp [ev, dvec]
  have h2 : ∑ i, ∑ i', qQ0 (K := K) i i' * Bmat b E H i i' =
      ∑ a : KIdx np, br (Bmat b E H) (ev (Sum.inr (Sum.inl a))) (ev (Sum.inr (Sum.inr a))) := by
    simp only [qQ0, br, sum_mul]
    rw [eq_comm, Finset.sum_comm]
    exact sum_congr rfl fun _ _ => by rw [Finset.sum_comm]
  simp only [h1, h2, zero_add, br_ev_ev]
  rfl

theorem gen_jX (a : KIdx np) (z : ZK K np) : gen (dvec b E H) (Bmat b E H) (jX a z) = 0 := by
  simp [gen, jX, lin_ev, dvec]

theorem gen_jXc (a : KIdx np) (z : ZK K np) : gen (dvec b E H) (Bmat b E H) (jXc a z) = 0 := by
  simp [gen, jXc, lin_ev, dvec]

theorem gen_jY (e : GIdx K np) (z : ZK K np) :
    gen (dvec b E H) (Bmat b E H) (jY e z) = drE b E e H := by
  simp [gen, jY, lin_ev, dvec]

theorem br_lS_ev (i : BI K np) :
    br (Bmat b E H) lS (ev i) = ∑ k : SrcCol K (Fin np), Bmat b E H (Sum.inl (0, k, k)) i := by
  unfold lS; rw [br_sum_left]; simp only [br_ev_ev]

theorem br_lQ_ev (i : BI K np) :
    br (Bmat b E H) (lQ y) (ev i) = ∑ a : KIdx np, (conj (y a.1 a.2) *
      Bmat b E H (Sum.inr (Sum.inl a)) i + y a.1 a.2 * Bmat b E H (Sum.inr (Sum.inr a)) i) := by
  unfold lQ; rw [br_sum_left]
  refine sum_congr rfl fun a _ => ?_
  rw [br_add_left, br_smul_left, br_smul_left, br_ev_ev, br_ev_ev]

theorem br_lS_X (a : KIdx np) : br (Bmat b E H) (lS (K := K)) (ev (Sum.inr (Sum.inl a))) =
    trKG b E a H := by
  rw [br_lS_ev]; rfl

theorem br_lS_Xc (a : KIdx np) : br (Bmat b E H) (lS (K := K)) (ev (Sum.inr (Sum.inr a))) =
    conj (trKG b E a H) := by
  rw [br_lS_ev, trKG, map_sum]; rfl

theorem br_lS_Y (e : GIdx K np) : br (Bmat b E H) lS (ev (Sum.inl e)) = trCv b E e H := by
  rw [br_lS_ev]; rfl

theorem br_lQ_X (a : KIdx np) : br (Bmat b E H) (lQ (K := K) y) (ev (Sum.inr (Sum.inl a))) =
    qKK b E a H y := by
  rw [br_lQ_ev]; simp [Bmat, qKK]

theorem br_lQ_Xc (a : KIdx np) : br (Bmat b E H) (lQ (K := K) y) (ev (Sum.inr (Sum.inr a))) =
    qKc b E a H y := by
  rw [br_lQ_ev]; simp [Bmat, qKc]

theorem br_lQ_Y (e : GIdx K np) : br (Bmat b E H) (lQ y) (ev (Sum.inl e)) = qG b E e H y := by
  rw [br_lQ_ev]; simp [Bmat, qG]

theorem br_lS_lS : br (Bmat b E H) (lS (K := K) (np := np)) lS = trTr b E H := by
  conv_lhs => arg 3; rw [show (lS : BI K np → ℂ) = fun i => ∑ k : SrcCol K (Fin np),
    ev (Sum.inl ((0 : Fin 2), k, k)) i from rfl]
  rw [br_sum_right]
  simp only [br_lS_Y, trTr, trCv]
  exact Finset.sum_comm

theorem br_lS_lQ : br (Bmat b E H) lS (lQ y) = sQ b E H y := by
  conv_lhs => arg 3; unfold lQ
  rw [br_sum_right]
  simp only [br_add_right, br_smul_right, br_lS_X, br_lS_Xc, sQ]

theorem br_lQ_lQ : br (Bmat b E H) (lQ y) (lQ y) = qQ b E H y := by
  conv_lhs => arg 3; unfold lQ
  rw [br_sum_right]
  simp only [br_add_right, br_smul_right, br_lQ_X, br_lQ_Xc, qQ]

end Coeff

/-!
## The generator identity
-/

set_option linter.unusedSimpArgs false in
/-- **The generator of the jet of a test is the test's generator** (`H = Y + J`). -/
theorem gen_jF (χ ξ : ℝ → ℝ) (b E : ℝ) (κ : KTest K np) (J : GSt K np) (z : ZK K np) :
    gen (dvec b E (z.1.1 + J)) (Bmat b E (z.1.1 + J)) (jF χ ξ κ z) = κ.lam χ ξ b E (J, z) := by
  rw [jF, gen_mul, gen_const, gen_mul, gen_mul, jChi, jXi, gen_chain, gen_chain, gen_jS,
    gen_jQ]
  rcases κ with a | ⟨a, a'⟩ | ⟨a, e⟩ | ⟨a, a'⟩
  · simp only [jP, gen_jX]
    simp only [Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, br_zero_left, br_add_left,
      br_add_right, br_smul_left, br_smul_right, br_lS_lS, br_lS_lQ, br_lQ_lQ, br_lS_X,
      br_lS_Xc, br_lS_Y, br_lQ_X, br_lQ_Xc, br_lQ_Y, br_ev_ev]
    simp only [KTest.lam, lamK1, cut0, dCut, cutC, cutK, pyG, pyG0, pyK, pyK0, pxK, pH]
    push_cast; ring
  · simp only [jP, gen_mul, gen_jX]
    simp only [Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, br_zero_left, br_add_left,
      br_add_right, br_smul_left, br_smul_right, br_lS_lS, br_lS_lQ, br_lQ_lQ, br_lS_X,
      br_lS_Xc, br_lS_Y, br_lQ_X, br_lQ_Xc, br_lQ_Y, br_ev_ev]
    simp only [KTest.lam, lamK2, cut0, dCut, cutC, cutK, pyG, pyG0, pyK, pyK0, pxK, pH, Bmat]
    push_cast; ring
  · simp only [jP, gen_mul, gen_jX, gen_jY]
    simp only [Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, jY, br_zero_left, br_add_left,
      br_add_right, br_smul_left, br_smul_right, br_lS_lS, br_lS_lQ, br_lQ_lQ, br_lS_X,
      br_lS_Xc, br_lS_Y, br_lQ_X, br_lQ_Xc, br_lQ_Y, br_ev_ev]
    simp only [KTest.lam, lamKY, cut0, dCut, cutC, cutK, pyG, pyG0, pyK, pyK0, pxK, pH, Bmat,
      kHatP, kHatE]
    push_cast; ring
  · simp only [jP, gen_mul, gen_jX, gen_jXc]
    simp only [Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, jXc, br_zero_left, br_add_left,
      br_add_right, br_smul_left, br_smul_right, br_lS_lS, br_lS_lQ, br_lQ_lQ, br_lS_X,
      br_lS_Xc, br_lS_Y, br_lQ_X, br_lQ_Xc, br_lQ_Y, br_ev_ev]
    simp only [KTest.lam, lamKC, cut0, dCut, cutC, cutK, pyG, pyG0, pyK, pyK0, pxK, pH, Bmat]
    push_cast; ring

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
