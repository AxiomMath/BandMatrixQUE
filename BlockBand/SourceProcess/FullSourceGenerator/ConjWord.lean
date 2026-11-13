module

public import BlockBand.SourceProcess.FullSourceGenerator.MatchingCore
public import BlockBand.SourceProcess.FullSourceStops.WordValue
public import BlockBand.SourceProcess.ContractingWords.Alive

/-!
# The conjugate word: real and imaginary parts of trace words are ordinary trace polynomials

For Hermitian letters, the trace of the conjugate word `conjWord w` is the complex conjugate of
`Tr w`; hence `Re Tr w` and `Im Tr w` are values of ordinary trace polynomials (`rePoly`, `imPoly`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open Matrix MvPolynomial
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {nT nI : ℕ}

/-- `conjAux ℓ [(f₁,s₁),…,(f_k,s_k)] s = [(ℓ,s₁),(f₁,s₂),…,(f_k,s)]`. -/
def conjAux : TraceLetter nT nI → TraceWord nT nI → Separator → TraceWord nT nI
  | ℓ, [], s => [(ℓ, s)]
  | ℓ, (f, s') :: ys, s => (ℓ, s') :: conjAux f ys s

/-- The conjugate word (the adjoint product, rotated into normal form). -/
def conjWord (w : TraceWord nT nI) : TraceWord nT nI :=
  match w.reverse with
  | [] => []
  | (ℓ, s) :: ys => conjAux ℓ ys s

/-- `qprod ℓ [(f₁,s₁),…] = A_ℓ B_{s₁} A_{f₁} ⋯`. -/
def qprod (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ) :
    TraceLetter nT nI → TraceWord nT nI → Matrix ι ι ℂ
  | ℓ, [] => A ℓ
  | ℓ, (f, s') :: ys => A ℓ * B s' * qprod A B f ys

section Det

variable (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)

theorem segProd_conjAux (ys : TraceWord nT nI) :
    ∀ (ℓ : TraceLetter nT nI) (s : Separator),
      segProd A B (conjAux ℓ ys s) = qprod A B ℓ ys * B s := by
  induction ys with
  | nil => intro ℓ s; simp [conjAux, qprod]
  | cons y ys ih =>
    intro ℓ s
    obtain ⟨f, s'⟩ := y
    simp only [conjAux, segProd_cons, qprod, ih, Matrix.mul_assoc]

theorem qprod_eq (hA : ∀ ℓ, (A ℓ)ᴴ = A ℓ) (ys : TraceWord nT nI)
    (hB : ∀ y ∈ ys, (B y.2)ᴴ = B y.2) :
    ∀ ℓ, A ℓ * (segProd A B ys.reverse)ᴴ = qprod A B ℓ ys := by
  induction ys with
  | nil => intro ℓ; simp [qprod]
  | cons y ys ih =>
    intro ℓ
    obtain ⟨f, s'⟩ := y
    have ih' := ih (fun y hy => hB y (List.mem_cons_of_mem _ hy)) f
    have hs' : (B s')ᴴ = B s' := hB (f, s') List.mem_cons_self
    simp only [List.reverse_cons, segProd_append, segProd_singleton, Matrix.conjTranspose_mul,
      hA, hs', qprod, ← ih']
    simp only [Matrix.mul_assoc]

/-- **`Tr` of the conjugate word is the complex conjugate.** -/
theorem wval_conjWord (hA : ∀ ℓ, (A ℓ)ᴴ = A ℓ) (w : TraceWord nT nI)
    (hB : ∀ x ∈ w, (B x.2)ᴴ = B x.2) :
    wval A B (conjWord w) = star (wval A B w) := by
  unfold conjWord
  rcases h : w.reverse with _ | ⟨⟨ℓ, s⟩, ys⟩
  · have hw : w = [] := List.reverse_eq_nil_iff.mp h
    subst hw
    simp [wval]
  · have hw : w = ys.reverse ++ [(ℓ, s)] := by
      rw [← List.reverse_reverse w, h]; simp
    have hB' : ∀ y ∈ ys, (B y.2)ᴴ = B y.2 := fun y hy => hB y (by rw [hw]; simp [hy])
    have hs : (B s)ᴴ = B s := hB (ℓ, s) (by rw [hw]; simp)
    simp only [wval]
    rw [segProd_conjAux, ← qprod_eq A B hA ys hB', ← Matrix.trace_conjTranspose, hw,
      segProd_append, segProd_singleton, Matrix.trace_mul_comm]
    simp only [Matrix.conjTranspose_mul, hA, hs, Matrix.mul_assoc]

theorem mem_conjAux_sep (ys : TraceWord nT nI) :
    ∀ (ℓ : TraceLetter nT nI) (s : Separator), ∀ x ∈ conjAux ℓ ys s,
      x.2 = s ∨ ∃ y ∈ ys, x.2 = y.2 := by
  induction ys with
  | nil => intro ℓ s x hx; simp [conjAux] at hx; exact Or.inl (by rw [hx])
  | cons y ys ih =>
    intro ℓ s x hx
    obtain ⟨f, s'⟩ := y
    simp only [conjAux, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inr ⟨(f, s'), List.mem_cons_self, rfl⟩
    · rcases ih f s x hx with h | ⟨y', hy', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨y', List.mem_cons_of_mem _ hy', h⟩

theorem conjWord_ordinary {w : TraceWord nT nI} (hw : IsOrdinaryWord w) :
    IsOrdinaryWord (conjWord w) := by
  unfold conjWord
  rcases h : w.reverse with _ | ⟨⟨ℓ, s⟩, ys⟩
  · exact absurd (List.reverse_eq_nil_iff.mp h) hw.1
  · have hw' : w = ys.reverse ++ [(ℓ, s)] := by
      rw [← List.reverse_reverse w, h]; simp
    refine ⟨by cases ys <;> simp [conjAux], fun x hx => ?_⟩
    rcases mem_conjAux_sep ys ℓ s x hx with h1 | ⟨y, hy, h1⟩
    · rw [h1]; exact hw.2 (ℓ, s) (by rw [hw']; simp)
    · rw [h1]; exact hw.2 y (by rw [hw']; simp [hy])

end Det

/-!
### Real and imaginary parts
-/

/-- `Re Tr w = ½(Tr w + Tr w̄)`. -/
def rePoly (w : TraceWord nT nI) : TracePoly nT nI :=
  C (1 / 2 : ℂ) * (wv w + wv (conjWord w))

/-- `Im Tr w = -(i/2)(Tr w - Tr w̄)`. -/
def imPoly (w : TraceWord nT nI) : TracePoly nT nI :=
  C (-(Complex.I / 2)) * (wv w - wv (conjWord w))

theorem rePoly_ordinary {w : TraceWord nT nI} (hw : IsOrdinaryWord w) :
    IsOrdinaryPoly (rePoly w) := by
  intro v hv
  have h := (vars_mul _ _) hv
  rw [vars_C, Finset.empty_union] at h
  rcases Finset.mem_union.mp ((vars_add_subset _ _) h) with h | h <;>
    rw [vars_X, Finset.mem_singleton] at h <;> rw [h]
  exacts [hw, conjWord_ordinary hw]

theorem imPoly_ordinary {w : TraceWord nT nI} (hw : IsOrdinaryWord w) :
    IsOrdinaryPoly (imPoly w) := by
  intro v hv
  have h := (vars_mul _ _) hv
  rw [vars_C, Finset.empty_union] at h
  rcases Finset.mem_union.mp (vars_sub_subset _ h) with h | h <;>
    rw [vars_X, Finset.mem_singleton] at h <;> rw [h]
  exacts [hw, conjWord_ordinary hw]

variable {W : ℕ}

theorem letterMatrix_conjTranspose (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) (ℓ : TraceLetter nT nI) :
    (letterMatrix b E k q W j ω ℓ)ᴴ = letterMatrix b E k q W j ω ℓ := by
  have gram : ∀ a : Fin nT ⊕ Fin nI, (letterMatrix b E k q W j ω (sourceLetter a))ᴴ =
      letterMatrix b E k q W j ω (sourceLetter a) := fun a => by
    obtain ⟨s, c, -, he⟩ := FullSourceStops.sourceLetter_gram b E k q hq j ω a
    rw [he, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp
  cases ℓ with
  | current => exact ContractingWords.pathCurrent_isHermitian b E j ω
  | tag a => exact gram (Sum.inl a)
  | interval a => exact gram (Sum.inr a)

theorem wordValue_conjWord (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) {w : TraceWord nT nI}
    (hw : IsOrdinaryWord w) :
    wordValue b E k q W j ω (conjWord w) = conj (wordValue b E k q W j ω w) := by
  rw [wordValue_eq_wval, wordValue_eq_wval]
  refine wval_conjWord _ _ (letterMatrix_conjTranspose b E k q hq j ω) w fun x hx => ?_
  rcases hw.2 x hx with h | h <;> rw [h]
  · simp [separatorMatrix]
  · exact BlockBand.Transmission.Bridge.nearProjection_conjTranspose

theorem polyValue_rePoly (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) {w : TraceWord nT nI}
    (hw : IsOrdinaryWord w) :
    polyValue b E k q W j ω (rePoly w) = ((wordValue b E k q W j ω w).re : ℂ) := by
  simp only [polyValue, rePoly, wv, map_mul, map_add, eval_C, eval_X]
  rw [wordValue_conjWord b E k q hq j ω hw, Complex.add_conj]
  push_cast; ring

theorem polyValue_imPoly (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) {w : TraceWord nT nI}
    (hw : IsOrdinaryWord w) :
    polyValue b E k q W j ω (imPoly w) = ((wordValue b E k q W j ω w).im : ℂ) := by
  simp only [polyValue, imPoly, wv, map_mul, map_sub, eval_C, eval_X]
  rw [wordValue_conjWord b E k q hq j ω hw, Complex.sub_conj]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-(((wordValue b E k q W j ω w).im : ℂ))) * this

end BlockBand.SourceProcess.FullSourceGenerator
