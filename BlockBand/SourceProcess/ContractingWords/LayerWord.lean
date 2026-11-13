module

public import BlockBand.SourceProcess.ContractingWords.WordBounds
public import BlockBand.SourceProcess.ContractingWords.Interface
public import BlockBand.SourceProcess.CompleteSourceGap.Interface

/-!
# The one-step update of a product of trace words at one layer (deterministic)

Old letter matrices `A : TraceLetter → Matrix` (Hermitian, `Tr|A_ℓ| ≤ K`), injection weights
`c_ℓ` (`q_a((j+1)/W)/W²` for interval sources, `0` otherwise), the fresh transport `N`, the new
block row `D` (`Y_{j+1;j} = D*D`) and the new separators `S`:
* `newProd A c N D S Zs = Π_w Tr Π_{x∈w} ((N*A_{x₁}N + c_{x₁}D*D) S_{x₂})` (the new value);
* `coreProd A T Zs = Π_w Tr Π_{x∈w} (A_{x₁} T_{x₂})` (the old letters at separators `T`).
Results: `newWord_zero` (`c = 0`: the separators become `T = N S N*`); `newProd_sub_core_le`
(the injection costs `κ_d ρ^{(d+1)²}/W`, `ρ = 3(1+K+c₀)(1+‖N‖+‖D‖)²`); `coreProd_smul`
(`coreProd A (f·B) = (Π f) coreProd A B`) and `prod_gapFactor` (`Π gapFactor = meanFactor`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.PassiveCovariance BlockBand.SourceProcess.FullSource
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {W nT nI : ℕ}

/-- The matrix word of a trace word at letter matrices `A`. -/
def letWord (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (w : TraceWord nT nI) : List (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × Separator) :=
  w.map fun x => (A x.1, x.2)

/-- `Π_w Tr Π (A_{x₁} T_{x₂})`. -/
def coreProd (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (Zs : List (TraceWord nT nI)) : ℂ :=
  (Zs.map fun w => matWord T (letWord A w)).prod

/-- The new value of one word. -/
def newWord (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (S : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (w : TraceWord nT nI) : ℂ :=
  (w.map fun x => (Nᴴ * A x.1 * N + (c x.1 : ℂ) • (Dᴴ * D)) * S x.2).prod.trace

/-- The new value of a product of words. -/
def newProd (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (S : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Zs : List (TraceWord nT nI)) : ℂ :=
  (Zs.map (newWord A c N D S)).prod

variable (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
  (S : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)

/-- **No injection**: the separators become `N S N*`. -/
theorem newWord_zero (w : TraceWord nT nI) :
    newWord A (fun _ => 0) N D S w = matWord (fun σ => N * S σ * Nᴴ) (letWord A w) := by
  have h := trace_prod_conj N (w.map fun x => (A x.1, S x.2))
  simp only [List.map_map] at h
  simp only [newWord, matWord, letWord, List.map_map, Complex.ofReal_zero, zero_smul, add_zero]
  exact h

/-- **The injection, one word.** -/
theorem newWord_sub_le (c : TraceLetter nT nI → ℝ) (hS : ∀ σ, ‖S σ‖ ≤ 1) (w : TraceWord nT nI) :
    ‖newWord A c N D S w - newWord A (fun _ => 0) N D S w‖ ≤
      (w.map fun x => |c x.1|).sum * ((Dᴴ * D).trace.re * 1) *
        (w.map fun x => 1 + (‖Nᴴ * A x.1 * N‖ + |c x.1| * ‖Dᴴ * D‖) * 1).prod := by
  have h := trace_inj_le D zero_le_one (w.map fun x => (Nᴴ * A x.1 * N, c x.1, S x.2))
    (fun t ht => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht; exact hS _) 1
  simp only [List.map_map, Matrix.one_mul] at h
  have h1 := norm_one_matrix_le (n := Fin 2 × Fin W)
  refine le_trans ?_ (h.trans (mul_le_of_le_one_left (by
    refine mul_nonneg (mul_nonneg (List.sum_nonneg fun x hx => ?_) (by
      simpa using trace_factor_re_nonneg D)) (List.prod_nonneg fun x hx => ?_)
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; simp only [Function.comp_apply]; positivity)
    h1))
  simp only [newWord, Complex.ofReal_zero, zero_smul, add_zero]
  exact le_of_eq (by congr 2)

/-- `Π_x gapFactor` over a product of words is the mean factor. -/
theorem prod_gapFactor (b E : ℝ) (s : ℂ) (Zs : List (TraceWord nT nI)) :
    (Zs.map fun w => (w.map fun x => gapFactor b E s x.2).prod).prod = meanFactor b E s Zs := by
  have hw : ∀ w : TraceWord nT nI, (w.map fun x => gapFactor b E s x.2).prod =
      thetaStar b E s ^ (w.map fun x => x.2.unconj).sum *
        conj (thetaStar b E s) ^ (w.map fun x => x.2.conj).sum := fun w => by
    induction w with
    | nil => simp
    | cons x w ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, List.map_cons,
        List.sum_cons, pow_add, pow_add, gapFactor]; ring
  induction Zs with
  | nil => simp [meanFactor, unconjCount, conjCount]
  | cons w Zs ih =>
    rw [List.map_cons, List.prod_cons, ih, hw]
    simp only [meanFactor, unconjCount, conjCount, List.map_cons, List.sum_cons, pow_add]
    ring

/-- `coreProd A (f·B) = (Π_x f_{x₂}) coreProd A B`. -/
theorem coreProd_smul (f : Separator → ℂ) (B : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Zs : List (TraceWord nT nI)) :
    coreProd A (fun σ => f σ • B σ) Zs =
      (Zs.map fun w => (w.map fun x => f x.2).prod).prod * coreProd A B Zs := by
  have hw : ∀ w : TraceWord nT nI, matWord (fun σ => f σ • B σ) (letWord A w) =
      (w.map fun x => f x.2).prod * matWord B (letWord A w) := fun w => by
    simp only [matWord, letWord, List.map_map]
    have := list_prod_smul_sep w A B f
    simp only [Function.comp_def] at this ⊢
    rw [this, trace_smul, smul_eq_mul]
  induction Zs with
  | nil => simp [coreProd]
  | cons w Zs ih =>
    simp only [coreProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [hw, ih]; ring

end BlockBand.SourceProcess.ContractingWords
