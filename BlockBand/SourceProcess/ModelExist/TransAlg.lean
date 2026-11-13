module

public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# Congruence of Gram states: the Gram coefficients are covariant

For `L : Matrix c' c ℂ` with `L 𝖣 Lᴴ = 𝖣'` and a Gram state `H = (M, B)` on `c'`, the congruent
state `congrGram L H = (LᴴML, LᴴBL)` on `c` has
* entries `G_{r,i,j} = Σ_{x,x'} conj(L_{xi}) L_{x'j} H_{r,x,x'}` (`gramEntry_congr`);
* drift entries given by the same formula (`gramDriftEntry_congr`; `g` is invariant,
  `gramScalar_congr`);
* covariance entries `Γ_{(r,i,j),(r',k,l)} = Σ conj(L_{xi}) L_{x'j} conj(L_{zk}) L_{z'l}
  Γ'_{(r,x,x'),(r',z,z')}` (`gramCovEntry_congr`).
This is the Gram-level form of "the probe columns of zero signature do not enter `P'`".
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped ComplexConjugate

variable {c c' : Type*} [Fintype c] [Fintype c']

/-- The congruent Gram state `(LᴴML, LᴴBL)`. -/
def congrGram (L : Matrix c' c ℂ) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) :
    Matrix c c ℂ × Matrix c c ℂ :=
  (Lᴴ * H.1 * L, Lᴴ * H.2 * L)

/-- The coefficient `conj(L_{xi}) L_{x'j}`. -/
def cf (L : Matrix c' c ℂ) (i j : c) (x x' : c') : ℂ := star (L x i) * L x' j

omit [Fintype c] in
theorem sandwich_apply (L : Matrix c' c ℂ) (A : Matrix c' c' ℂ) (i l : c) :
    (Lᴴ * A * L) i l = ∑ x, ∑ x', cf L i l x x' * A x x' := by
  simp only [Matrix.mul_apply, conjTranspose_apply, cf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

omit [Fintype c] in
theorem gramEntry_congr (L : Matrix c' c ℂ) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (r : Fin 2)
    (i j : c) :
    gramEntry (r, i, j) (congrGram L H) = ∑ x, ∑ x', cf L i j x x' * gramEntry (r, x, x') H := by
  simp only [gramEntry, congrGram]
  split_ifs <;> exact sandwich_apply L _ i j

variable [DecidableEq c] [DecidableEq c']

omit [DecidableEq c] [DecidableEq c'] in
theorem gramScalar_congr {L : Matrix c' c ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
    (hL : L * D * Lᴴ = D') (M : Matrix c' c' ℂ) :
    gramScalar D (Lᴴ * M * L) = gramScalar D' M := by
  unfold gramScalar
  congr 1
  have e : D * (Lᴴ * M * L) * D * (Lᴴ * M * L) = (D * Lᴴ * M * L * D * Lᴴ * M) * L := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← hL]
  simp only [Matrix.mul_assoc]

omit [DecidableEq c] [DecidableEq c'] in
theorem gramDriftEntry_congr {L : Matrix c' c ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
    (hL : L * D * Lᴴ = D') (D0 : ℝ) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (r : Fin 2) (i j : c) :
    gramDriftEntry D0 D (r, i, j) (congrGram L H) =
      ∑ x, ∑ x', cf L i j x x' * gramDriftEntry D0 D' (r, x, x') H := by
  simp only [gramDriftEntry]
  split_ifs
  · simp
  · simp only [congrGram, gramScalar_congr hL, sandwich_apply L _ i j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    ring

omit [DecidableEq c] [DecidableEq c'] in
theorem congr_C0 {L : Matrix c' c ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
    (hL : L * D * Lᴴ = D') (M B : Matrix c' c' ℂ) :
    gramC0 (Lᴴ * M * L) (Lᴴ * B * L) D = Lᴴ * gramC0 M B D' * L := by
  simp only [gramC0, Matrix.mul_add, Matrix.add_mul, ← hL, Matrix.mul_assoc]

omit [DecidableEq c] [DecidableEq c'] in
theorem congr_C1 {L : Matrix c' c ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
    (hL : L * D * Lᴴ = D') (M B : Matrix c' c' ℂ) :
    gramC1 (Lᴴ * M * L) (Lᴴ * B * L) D = Lᴴ * gramC1 M B D' * L := by
  simp only [gramC1, Matrix.mul_add, Matrix.add_mul, ← hL, Matrix.mul_assoc]

omit [DecidableEq c] [DecidableEq c'] in
theorem congr_C2 {L : Matrix c' c ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
    (hL : L * D * Lᴴ = D') (B : Matrix c' c' ℂ) :
    gramC2 (Lᴴ * B * L) D = Lᴴ * gramC2 B D' * L := by
  simp only [gramC2, Matrix.mul_add, Matrix.add_mul, ← hL, Matrix.mul_assoc]

omit [Fintype c] [DecidableEq c] [DecidableEq c'] in
theorem congr_conjTranspose (L : Matrix c' c ℂ) (A : Matrix c' c' ℂ) :
    (Lᴴ * A * L)ᴴ = Lᴴ * Aᴴ * L := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The quadruple coefficient. -/
def cf4 (L : Matrix c' c ℂ) (i j k l : c) (x x' z z' : c') : ℂ :=
  cf L i j x x' * cf L k l z z'

omit [Fintype c] [DecidableEq c] [DecidableEq c'] in
theorem sum2_mul_sum2 (f g : c' → c' → ℂ) :
    (∑ a, ∑ b, f a b) * (∑ c, ∑ d, g c d) = ∑ a, ∑ b, ∑ c, ∑ d, f a b * g c d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

omit [Fintype c] [DecidableEq c] [DecidableEq c'] in
theorem crossedBracket_congr (D0 : ℝ) (L : Matrix c' c ℂ) (B Cl Cr : Matrix c' c' ℂ)
    (i j k l : c) :
    crossedBracket D0 (Lᴴ * B * L) (Lᴴ * Cl * L) (Lᴴ * Cr * L) i j k l =
      ∑ x, ∑ x', ∑ z, ∑ z', cf4 L i j k l x x' z z' * crossedBracket D0 B Cl Cr x x' z z' := by
  simp only [crossedBracket, sandwich_apply]
  rw [sum2_mul_sum2, sum2_mul_sum2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext z; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun z _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  simp only [cf4, cf]
  ring

omit [Fintype c] [DecidableEq c] [DecidableEq c'] in
theorem sum4_swap (f : c' → c' → c' → c' → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := Finset.sum_comm (s := (univ : Finset (c' × c'))) (t := (univ : Finset (c' × c')))
    (f := fun p q => f p.1 p.2 q.1 q.2)
  simpa only [Fintype.sum_prod_type] using h

omit [DecidableEq c] [DecidableEq c'] in
/-- **Covariance entries of a congruent Gram state.** -/
theorem gramCovEntry_congr {L : Matrix c' c ℂ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
    (hL : L * D * Lᴴ = D') (D0 : ℝ) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) (r r' : Fin 2)
    (i j k l : c) :
    gramCovEntry D0 D (r, i, j) (r', k, l) (congrGram L H) =
      ∑ x, ∑ x', ∑ z, ∑ z', cf4 L i j k l x x' z z' *
        gramCovEntry D0 D' (r, x, x') (r', z, z') H := by
  fin_cases r <;> fin_cases r' <;>
    simp only [gramCovEntry, congrGram, congr_C0 hL, congr_C1 hL, congr_C2 hL,
      congr_conjTranspose]
  · exact crossedBracket_congr D0 L _ _ _ i j k l
  · exact crossedBracket_congr D0 L _ _ _ i j k l
  · rw [crossedBracket_congr, sum4_swap]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
    simp only [cf4]
    ring
  · exact crossedBracket_congr D0 L _ _ _ i j k l

end BlockBand.SourceProcess.ModelExist
