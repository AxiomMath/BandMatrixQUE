module

public import BlockBand.Model.Construction.OrderedProjector
public import BlockBand.Model.Construction.SpectralEigenvalues
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Spectral sums of Hermitian matrices without simple spectrum, and a measurable `cfc`

The collar matrix `ℋ_X` is not known to have simple spectrum almost surely, so the fresh
selections of `WeightedDensity.Spectral` (which need simple spectrum) are not used. Instead:

* `specSum hA g = Σ_r g(λ_r) b_r b_r*` over the (non-measurable, fixed-matrix) increasing
  orthonormal eigenbasis `b_r` of a Hermitian `A`; `cfc f A = specSum hA f` (`cfc_eq_specSum`),
  `(A - z)⁻¹ = specSum hA (λ ↦ (λ - z)⁻¹)` for `Im z ≠ 0` (`inv_sub_eq_specSum`), quadratic forms
  `v* specSum g v = Σ_r g(λ_r)|b_r* v|²` (`dotProduct_specSum_mulVec`), entry bounds.
* `cfc_mulVec_of_eigen`: `A v = μ v ⇒ cfc f A v = f(μ) v`; hence `cfc f (A + θ) = cfc (f(· + θ)) A`
  (`cfc_add_smul_one`).
* `rawCfc f A = Σ_i f(λ_i)/m_i · Q_i(A)` with the measurable increasing eigenvalues `λ_i`, their
  multiplicities `m_i` and the multiplicity-aware Lagrange projectors `Q_i`; it is jointly Borel in
  `(parameter, A)` (`measurable_rawCfc`) and equals `cfc f A` on Hermitian `A` (`rawCfc_eq_cfc`),
  without any simplicity hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!
## Spectral sums over the increasing eigenbasis
-/

/-- `Σ_r g(λ_r) b_r b_r*` over the increasing orthonormal eigenbasis of a Hermitian `A`. -/
def specSum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) : Matrix ι ι ℂ :=
  ∑ r, g (increasingEigenvalue hA r) •
    vecMulVec (increasingEigenvector hA r) (star (increasingEigenvector hA r))

theorem star_dotProduct_increasingEigenvector {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (r s : Fin (Fintype.card ι)) :
    star (increasingEigenvector hA r) ⬝ᵥ increasingEigenvector hA s = if r = s then 1 else 0 := by
  rw [← increasingEigenvector_orthonormal hA r s]
  rfl

theorem specSum_mulVec {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) (v : ι → ℂ) :
    specSum hA g *ᵥ v = ∑ r, (g (increasingEigenvalue hA r) *
      (star (increasingEigenvector hA r) ⬝ᵥ v)) • increasingEigenvector hA r := by
  unfold specSum
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_mulVec, vecMulVec_mulVec]
  ext x
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

theorem specSum_mulVec_eigenvector {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ)
    (s : Fin (Fintype.card ι)) :
    specSum hA g *ᵥ increasingEigenvector hA s =
      g (increasingEigenvalue hA s) • increasingEigenvector hA s := by
  rw [specSum_mulVec]
  simp_rw [star_dotProduct_increasingEigenvector, mul_ite, mul_one, mul_zero, ite_smul,
    zero_smul]
  simp

/-- Completeness: `Σ_r b_r b_r* = I`. -/
theorem specSum_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specSum hA (fun _ => 1) = 1 := by
  refine matrix_eq_of_mulVec_increasingEigenvector_eq ⟨A, hA⟩ _ _ fun r => ?_
  change specSum hA (fun _ => 1) *ᵥ increasingEigenvector hA r = 1 *ᵥ increasingEigenvector hA r
  rw [specSum_mulVec_eigenvector, one_smul, one_mulVec]

/-- Expansion of a vector in the eigenbasis. -/
theorem eq_sum_increasingEigenvector {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    v = ∑ r, (star (increasingEigenvector hA r) ⬝ᵥ v) • increasingEigenvector hA r := by
  have h := specSum_mulVec hA (fun _ => 1) v
  rw [specSum_one, one_mulVec] at h
  simpa only [one_mul] using h

/-- `star b_r ⬝ᵥ (A v) = λ_r (star b_r ⬝ᵥ v)`. -/
theorem star_eigenvector_dotProduct_mulVec {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (r : Fin (Fintype.card ι)) (v : ι → ℂ) :
    star (increasingEigenvector hA r) ⬝ᵥ (A *ᵥ v) =
      (increasingEigenvalue hA r : ℂ) * (star (increasingEigenvector hA r) ⬝ᵥ v) := by
  have h1 : star (increasingEigenvector hA r) ᵥ* A = star (A *ᵥ increasingEigenvector hA r) := by
    rw [star_mulVec, hA.eq]
  rw [dotProduct_mulVec, h1, mulVec_increasingEigenvector, star_smul, smul_dotProduct, Complex.star_def,
    Complex.conj_ofReal, smul_eq_mul]

/-- `cfc f A = Σ_r f(λ_r) b_r b_r*` (no simple-spectrum hypothesis). -/
theorem cfc_eq_specSum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = specSum hA (fun x => ((f x : ℝ) : ℂ)) := by
  rw [hA.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [mul_apply, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, star_apply, IsHermitian.eigenvectorUnitary_apply, specSum,
    Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.star_apply,
    Function.comp_apply]
  rw [← Equiv.sum_comp increasingIndex]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [increasingEigenvector, increasingEigenbasis_apply, eigenvalue_increasingIndex,
    RCLike.ofReal_eq_complex_ofReal]
  ring

/-- `A v = μ v ⇒ cfc f A v = f(μ) v` (any eigenvector, any `f`). -/
theorem cfc_mulVec_of_eigen {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) {μ : ℝ}
    {v : ι → ℂ} (hv : A *ᵥ v = (μ : ℂ) • v) :
    cfc f A *ᵥ v = ((f μ : ℝ) : ℂ) • v := by
  rw [cfc_eq_specSum hA, specSum_mulVec]
  conv_rhs => rw [eq_sum_increasingEigenvector hA v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_smul]
  congr 1
  have h := star_eigenvector_dotProduct_mulVec hA r v
  rw [hv, dotProduct_smul, smul_eq_mul] at h
  by_cases h0 : star (increasingEigenvector hA r) ⬝ᵥ v = 0
  · rw [h0, mul_zero, mul_zero]
  · have : (increasingEigenvalue hA r : ℂ) = μ := (mul_right_cancel₀ h0 h).symm
    rw [Complex.ofReal_inj.1 this]

/-- Real scalar shift: `cfc f (A + θI) = cfc (f(· + θ)) A`. -/
theorem cfc_add_smul_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (θ : ℝ) :
    cfc f (A + (θ : ℂ) • (1 : Matrix ι ι ℂ)) = cfc (fun x => f (x + θ)) A := by
  have hAθ : (A + (θ : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian :=
    hA.add (isHermitian_one.smul (Complex.conj_ofReal θ))
  refine matrix_eq_of_mulVec_increasingEigenvector_eq ⟨A, hA⟩ _ _ fun r => ?_
  change cfc f (A + (θ : ℂ) • 1) *ᵥ increasingEigenvector hA r =
    cfc (fun x => f (x + θ)) A *ᵥ increasingEigenvector hA r
  have hv : (A + (θ : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ increasingEigenvector hA r =
      (((increasingEigenvalue hA r + θ : ℝ)) : ℂ) • increasingEigenvector hA r := by
    rw [add_mulVec, mulVec_increasingEigenvector, smul_mulVec, one_mulVec, ← add_smul,
      Complex.ofReal_add]
  rw [cfc_mulVec_of_eigen hAθ f hv, cfc_mulVec_of_eigen hA _ (mulVec_increasingEigenvector hA r)]

/-- Resolvent: `(A - z)⁻¹ = Σ_r (λ_r - z)⁻¹ b_r b_r*` for `Im z ≠ 0`. -/
theorem inv_sub_eq_specSum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (A - z • (1 : Matrix ι ι ℂ))⁻¹ = specSum hA (fun x => ((x : ℂ) - z)⁻¹) := by
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := fun x h => hz (by
    have := congrArg Complex.im h; simpa using this.symm)
  refine inv_eq_right_inv (matrix_eq_of_mulVec_increasingEigenvector_eq ⟨A, hA⟩ _ _ fun r => ?_)
  change ((A - z • 1) * specSum hA _) *ᵥ increasingEigenvector hA r = 1 *ᵥ increasingEigenvector hA r
  rw [← mulVec_mulVec, specSum_mulVec_eigenvector, mulVec_smul, sub_mulVec,
    mulVec_increasingEigenvector, smul_mulVec, one_mulVec, ← sub_smul, smul_smul,
    inv_mul_cancel₀ (hne _), one_smul]

/-- Quadratic form: `v* (Σ g(λ_r) b_r b_r*) v = Σ_r g(λ_r) |b_r* v|²`. -/
theorem dotProduct_specSum_mulVec {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ)
    (v : ι → ℂ) :
    star v ⬝ᵥ (specSum hA g *ᵥ v) = ∑ r, g (increasingEigenvalue hA r) *
      ((‖star (increasingEigenvector hA r) ⬝ᵥ v‖ ^ 2 : ℝ) : ℂ) := by
  rw [specSum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [dotProduct_smul, smul_eq_mul, mul_assoc]
  congr 1
  have : star v ⬝ᵥ increasingEigenvector hA r = star (star (increasingEigenvector hA r) ⬝ᵥ v) := by
    rw [star_dotProduct]
  rw [this, Complex.star_def, Complex.mul_conj']
  push_cast
  ring

theorem norm_increasingEigenvector_apply_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (r : Fin (Fintype.card ι)) (x : ι) : ‖increasingEigenvector hA r x‖ ≤ 1 := by
  have h := sum_norm_sq_increasingEigenvector hA r
  have hx : ‖increasingEigenvector hA r x‖ ^ 2 ≤ 1 := h ▸ Finset.single_le_sum
    (f := fun y => ‖increasingEigenvector hA r y‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  nlinarith [norm_nonneg (increasingEigenvector hA r x)]

/-- Entry formula `specSum hA g i j = Σ_r g(λ_r) b_r(i) conj(b_r(j))`. -/
theorem specSum_apply {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) (i j : ι) :
    specSum hA g i j = ∑ r, g (increasingEigenvalue hA r) *
      (increasingEigenvector hA r i * star (increasingEigenvector hA r j)) := by
  simp only [specSum, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Pi.star_apply]

theorem norm_specSum_apply_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {g : ℝ → ℂ} {B : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ B) (i j : ι) : ‖specSum hA g i j‖ ≤ Fintype.card ι * B := by
  rw [specSum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  calc ∑ r, ‖g (increasingEigenvalue hA r) *
        (increasingEigenvector hA r i * star (increasingEigenvector hA r j))‖
      ≤ ∑ _r : Fin (Fintype.card ι), B := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_mul, norm_mul, norm_star]
        have h1 := norm_increasingEigenvector_apply_le hA r i
        have h2 := norm_increasingEigenvector_apply_le hA r j
        calc ‖g (increasingEigenvalue hA r)‖ * (‖increasingEigenvector hA r i‖ *
              ‖increasingEigenvector hA r j‖) ≤ B * (1 * 1) := by gcongr; exact hg _
          _ = B := by ring
    _ = Fintype.card ι * B := by simp

/-!
## A Borel version of `cfc`
-/

/-- Multiplicity-aware Lagrange factor `(A - λ_j)/(λ_i - λ_j)`, or `I` if `λ_j = λ_i`
(measurable increasing eigenvalues, zero off the Hermitian locus). -/
def lagFactor (i j : Fin (Fintype.card ι)) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if rawIncreasingEigenvalue j A = rawIncreasingEigenvalue i A then 1 else
    (((rawIncreasingEigenvalue i A - rawIncreasingEigenvalue j A : ℝ) : ℂ)⁻¹) •
      (A - (rawIncreasingEigenvalue j A : ℂ) • 1)

/-- `Q_i(A) = Π_j lagFactor i j A`: the spectral projector onto the `λ_i`-eigenspace. -/
def lagProj (i : Fin (Fintype.card ι)) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((List.finRange (Fintype.card ι)).map (fun j => lagFactor i j A)).prod

/-- Multiplicity `m_i = #{j | λ_j = λ_i}` (as a real number). -/
def eigMult (i : Fin (Fintype.card ι)) (A : Matrix ι ι ℂ) : ℝ :=
  ∑ j, if rawIncreasingEigenvalue j A = rawIncreasingEigenvalue i A then (1 : ℝ) else 0

/-- `rawCfc f A = Σ_i f(λ_i)/m_i · Q_i(A)`; equals `cfc f A` on Hermitian `A`. -/
def rawCfc (f : ℝ → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ i, (((f (rawIncreasingEigenvalue i A) / eigMult i A : ℝ)) : ℂ) • lagProj i A

theorem measurable_matrix_of_entries {α : Type*} [MeasurableSpace α] {κ₁ κ₂ : Type*}
    {F : α → Matrix κ₁ κ₂ ℂ} (h : ∀ x y, Measurable fun a => F a x y) : Measurable F :=
  measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun y => h x y

theorem measurable_lagFactor {α : Type*} [MeasurableSpace α] {M : α → Matrix ι ι ℂ}
    (hM : Measurable M) (i j : Fin (Fintype.card ι)) :
    Measurable fun a => lagFactor i j (M a) := by
  have hi := (measurable_rawIncreasingEigenvalue i).comp hM
  have hj := (measurable_rawIncreasingEigenvalue j).comp hM
  refine Measurable.ite (measurableSet_eq_fun hj hi) measurable_const ?_
  refine measurable_matrix_of_entries fun x y => ?_
  have he : Measurable fun a => M a x y :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hM)
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  exact ((Complex.continuous_ofReal.measurable.comp (hi.sub hj)).inv).mul
    (he.sub ((Complex.continuous_ofReal.measurable.comp hj).mul measurable_const))

theorem measurable_list_prod_matrix {α : Type*} [MeasurableSpace α]
    (L : List (α → Matrix ι ι ℂ)) (hL : ∀ F ∈ L, Measurable F) :
    Measurable fun a => (L.map fun F => F a).prod := by
  induction L with
  | nil => exact measurable_const
  | cons F L ih =>
    simp only [List.map_cons, List.prod_cons]
    have hF := hL F (List.mem_cons_self ..)
    have hR := ih fun G hG => hL G (List.mem_cons_of_mem _ hG)
    refine measurable_matrix_of_entries fun x y => ?_
    simp only [mul_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp ((measurable_pi_apply x).comp hF)).mul
        ((measurable_pi_apply y).comp ((measurable_pi_apply k).comp hR))

theorem measurable_lagProj {α : Type*} [MeasurableSpace α] {M : α → Matrix ι ι ℂ}
    (hM : Measurable M) (i : Fin (Fintype.card ι)) :
    Measurable fun a => lagProj i (M a) := by
  have h := measurable_list_prod_matrix ((List.finRange (Fintype.card ι)).map
    fun j a => lagFactor i j (M a)) (by
      intro F hF
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hF
      exact measurable_lagFactor hM i j)
  simpa only [lagProj, List.map_map, Function.comp_def] using h

theorem measurable_eigMult {α : Type*} [MeasurableSpace α] {M : α → Matrix ι ι ℂ}
    (hM : Measurable M) (i : Fin (Fintype.card ι)) : Measurable fun a => eigMult i (M a) :=
  Finset.measurable_sum _ fun j _ => Measurable.ite
    (measurableSet_eq_fun ((measurable_rawIncreasingEigenvalue j).comp hM)
      ((measurable_rawIncreasingEigenvalue i).comp hM)) measurable_const measurable_const

/-- Joint Borel measurability of `(p, a) ↦ rawCfc (g p) (M a)` for a jointly measurable family. -/
theorem measurable_rawCfc {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {M : α → Matrix ι ι ℂ} (hM : Measurable M) {g : β → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (x y : ι) :
    Measurable fun p : β × α => rawCfc (g p.1) (M p.2) x y := by
  simp only [rawCfc, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ => ?_
  have hlam : Measurable fun p : β × α => rawIncreasingEigenvalue i (M p.2) :=
    (measurable_rawIncreasingEigenvalue i).comp (hM.comp measurable_snd)
  have hc : Measurable fun p : β × α => g p.1 (rawIncreasingEigenvalue i (M p.2)) :=
    hg.comp (measurable_fst.prodMk hlam)
  exact (Complex.continuous_ofReal.measurable.comp
    (hc.div ((measurable_eigMult hM i).comp measurable_snd))).mul
    ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp
      ((measurable_lagProj hM i).comp measurable_snd)))

/-- Action of a Lagrange factor on the eigenbasis. -/
theorem lagFactor_mulVec {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i j r : Fin (Fintype.card ι)) :
    lagFactor i j A *ᵥ increasingEigenvector hA r =
      (if increasingEigenvalue hA j = increasingEigenvalue hA i then (1 : ℂ) else
        ((increasingEigenvalue hA i - increasingEigenvalue hA j : ℝ) : ℂ)⁻¹ *
          ((increasingEigenvalue hA r : ℂ) - (increasingEigenvalue hA j : ℂ))) •
        increasingEigenvector hA r := by
  unfold lagFactor
  simp only [rawIncreasingEigenvalue_eq _ _ hA]
  split_ifs
  · rw [one_mulVec, one_smul]
  · rw [smul_mulVec, sub_mulVec, mulVec_increasingEigenvector, smul_mulVec, one_mulVec,
      ← sub_smul, smul_smul]

theorem lagProd_mulVec {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i r : Fin (Fintype.card ι))
    (L : List (Fin (Fintype.card ι))) :
    (L.map fun j => lagFactor i j A).prod *ᵥ increasingEigenvector hA r =
      (L.map fun j => (if increasingEigenvalue hA j = increasingEigenvalue hA i then (1 : ℂ) else
        ((increasingEigenvalue hA i - increasingEigenvalue hA j : ℝ) : ℂ)⁻¹ *
          ((increasingEigenvalue hA r : ℂ) - (increasingEigenvalue hA j : ℂ)))).prod •
        increasingEigenvector hA r := by
  induction L with
  | nil => simp [one_mulVec]
  | cons j L ih =>
    simp only [List.map_cons, List.prod_cons, ← mulVec_mulVec, ih, mulVec_smul,
      lagFactor_mulVec hA, smul_smul]
    rw [mul_comm]

theorem lagScalar_prod {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i r : Fin (Fintype.card ι)) :
    ((List.finRange (Fintype.card ι)).map fun j =>
      (if increasingEigenvalue hA j = increasingEigenvalue hA i then (1 : ℂ) else
        ((increasingEigenvalue hA i - increasingEigenvalue hA j : ℝ) : ℂ)⁻¹ *
          ((increasingEigenvalue hA r : ℂ) - (increasingEigenvalue hA j : ℂ)))).prod =
      if increasingEigenvalue hA r = increasingEigenvalue hA i then 1 else 0 := by
  split_ifs with hri
  · refine List.prod_eq_one fun z hz => ?_
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hz
    split_ifs with hji
    · rfl
    · have hne : ((increasingEigenvalue hA i - increasingEigenvalue hA j : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.2 (Ne.symm hji)
      rw [hri, ← Complex.ofReal_sub]
      exact inv_mul_cancel₀ hne
  · refine List.prod_eq_zero (List.mem_map.2 ⟨r, List.mem_finRange r, ?_⟩)
    rw [ite_eq_right hri, sub_self, mul_zero]

/-- Combinatorial step: `Σ_i f(λ_i)/m_i [λ_r = λ_i] = f(λ_r)`. -/
theorem sum_div_mult_indicator {n : ℕ} (lam : Fin n → ℝ) (f : ℝ → ℝ) (r : Fin n) :
    (∑ i, ((f (lam i) / ∑ j, (if lam j = lam i then (1 : ℝ) else 0) : ℝ) : ℂ) *
      (if lam r = lam i then (1 : ℂ) else 0)) = ((f (lam r) : ℝ) : ℂ) := by
  set m := ∑ j, if lam j = lam r then (1 : ℝ) else 0 with hm
  have hpos : 0 < m := by
    refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ?_
    have h1 := Finset.single_le_sum (f := fun j => if lam j = lam r then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ r)
    simp only [ite_true] at h1
    exact h1
  have hterm : ∀ i, ((f (lam i) / ∑ j, (if lam j = lam i then (1 : ℝ) else 0) : ℝ) : ℂ) *
      (if lam r = lam i then (1 : ℂ) else 0) =
      ((if lam i = lam r then f (lam r) / m else 0 : ℝ) : ℂ) := by
    intro i
    by_cases h : lam r = lam i
    · rw [ite_eq_left h, ite_eq_left h.symm, mul_one, hm, h]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero, Complex.ofReal_zero]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum]
  congr 1
  have hsum : (∑ i, if lam i = lam r then f (lam r) / m else 0) = f (lam r) / m * m := by
    rw [hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hsum, div_mul_cancel₀ _ hpos.ne']

/-- `rawCfc f A = cfc f A` for every Hermitian `A` and every `f` (no simplicity). -/
theorem rawCfc_eq_cfc {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rawCfc f A = cfc f A := by
  refine matrix_eq_of_mulVec_increasingEigenvector_eq ⟨A, hA⟩ _ _ fun r => ?_
  change rawCfc f A *ᵥ increasingEigenvector hA r = cfc f A *ᵥ increasingEigenvector hA r
  rw [cfc_mulVec_of_eigen hA f (mulVec_increasingEigenvector hA r)]
  have hQ : ∀ i, lagProj i A *ᵥ increasingEigenvector hA r =
      (if increasingEigenvalue hA r = increasingEigenvalue hA i then (1 : ℂ) else 0) •
        increasingEigenvector hA r := by
    intro i
    rw [lagProj, lagProd_mulVec hA, lagScalar_prod hA]
  have hm : ∀ i, eigMult i A =
      ∑ j, if increasingEigenvalue hA j = increasingEigenvalue hA i then (1 : ℝ) else 0 := by
    intro i
    simp only [eigMult, rawIncreasingEigenvalue_eq _ _ hA]
  unfold rawCfc
  rw [Matrix.sum_mulVec]
  have hterm : ∀ i, ((((f (rawIncreasingEigenvalue i A) / eigMult i A : ℝ)) : ℂ) • lagProj i A)
      *ᵥ increasingEigenvector hA r =
      (((f (increasingEigenvalue hA i) / ∑ j, (if increasingEigenvalue hA j =
          increasingEigenvalue hA i then (1 : ℝ) else 0) : ℝ) : ℂ) *
        (if increasingEigenvalue hA r = increasingEigenvalue hA i then (1 : ℂ) else 0)) •
        increasingEigenvector hA r := by
    intro i
    rw [smul_mulVec, hQ i, smul_smul, hm i, rawIncreasingEigenvalue_eq _ _ hA]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul,
    sum_div_mult_indicator (increasingEigenvalue hA) f r]

/-- Borel measurability of the entries of `ω ↦ rawCfc f (M ω)`. -/
theorem measurable_rawCfc_apply {Ω : Type*} [MeasurableSpace Ω]
    {M : Ω → Matrix ι ι ℂ} (hM : Measurable M) {f : ℝ → ℝ}
    (hf : Measurable f) (x y : ι) :
    Measurable (fun ω => rawCfc f (M ω) x y) := by
  have hg : Measurable (Function.uncurry fun (_ : Unit) => f) := hf.comp measurable_snd
  have h2 : Measurable fun p : Unit × Ω => rawCfc f (M p.2) x y := measurable_rawCfc hM hg x y
  have hp : Measurable fun ω : Ω => ((() : Unit), ω) := measurable_prodMk_left
  exact Measurable.comp (g := fun p : Unit × Ω => rawCfc f (M p.2) x y)
    (f := fun ω : Ω => ((() : Unit), ω)) h2 hp

theorem ae_rawCfc_apply_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : Ω → Matrix ι ι ℂ} (hH : ∀ᵐ ω ∂μ, (M ω).IsHermitian) (f : ℝ → ℝ)
    (x y : ι) : ∀ᵐ ω ∂μ, rawCfc f (M ω) x y = cfc f (M ω) x y := by
  filter_upwards [hH] with ω hω
  have := rawCfc_eq_cfc hω f
  exact congrFun (congrFun this x) y

/-- Almost-everywhere strong measurability of the entries of `cfc f (M ω)`, for Borel `f` and a
measurable `M` that is Hermitian almost surely. -/
theorem aestronglyMeasurable_cfc_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : Ω → Matrix ι ι ℂ} (hM : Measurable M) (hH : ∀ᵐ ω ∂μ, (M ω).IsHermitian) {f : ℝ → ℝ}
    (hf : Measurable f) (x y : ι) :
    AEStronglyMeasurable (fun ω => cfc f (M ω) x y) μ :=
  (measurable_rawCfc_apply hM hf x y).aestronglyMeasurable.congr (ae_rawCfc_apply_eq hH f x y)

end BlockBand.Critical.Collar.Density
