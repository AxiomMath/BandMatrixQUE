module

public import BlockBand.Critical.JointRecovery.FiniteIdentity
public import BlockBand.Critical.Assembly.CriticalOfContracts

/-!
# The entire law: the cone bound `|D(iy)| ≥ 1`

* `one_le_norm_det_one_add_I_smul`: `|det(I + iK)| ≥ 1` for Hermitian `K` (characteristic
  polynomial at `i`);
* `one_le_norm_finiteEntireDeterminant_conePoint`: deterministic finite-width bound
  (`D_W(iy) = det(I + i S^{1/2} R S^{1/2})`, Sylvester);
* `hasInverseConeBound_finiteEntireLaw`; `hasInverseConeBound_of_tendsto` (closed sets,
  portmanteau, any non-trivial filter);
* **`entireLaw_coneBound`**: exactly the field `EntireLawContract.coneBound`, with no hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ComplexConjugate

variable {p : Parameters}

/-!
## 1. `|det(I + iK)| ≥ 1` for Hermitian `K`
-/

/-- For Hermitian `K`, `|det(I + iK)| = Π_k |1 + iλ_k| ≥ 1`. -/
theorem one_le_norm_det_one_add_I_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) : 1 ≤ ‖(1 + Complex.I • K).det‖ := by
  have h1 : (1 : Matrix ι ι ℂ) + Complex.I • K = (-Complex.I) • (Matrix.scalar ι Complex.I - K) := by
    rw [smul_sub, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul, neg_smul, sub_neg_eq_add]
  rw [h1, Matrix.det_smul, ← Matrix.eval_charpoly, hK.charpoly_eq, Polynomial.eval_prod, norm_mul,
    norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul, norm_prod]
  refine Finset.one_le_prod₀ fun i _ => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  calc (1 : ℝ) = |(Complex.I - ((hK.eigenvalues i : ℝ) : ℂ)).im| := by simp
    _ ≤ _ := Complex.abs_im_le_norm _

/-!
## 2. Finite width: `|D_W(iy)| ≥ 1` on the closed positive imaginary cone
-/

/-- The diagonal weight `W⁻² Σ_a y_a Q_a(j/n)` of the cone source. -/
def coneWeight (p : Parameters) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (y : Fin m → ℝ) (x : p.Site) :
    ℝ :=
  ((p.W : ℝ)⁻¹) ^ 2 * ∑ a, y a * Q a (p.ringProfilePoint x.1)

theorem coneWeight_nonneg {m : ℕ} {Q : Fin m → C(Torus, ℝ)} (hQ : ∀ a t, 0 ≤ Q a t)
    {y : Fin m → ℝ} (hy : ∀ a, 0 ≤ y a) (x : p.Site) : 0 ≤ coneWeight p Q y x :=
  mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ => mul_nonneg (hy a) (hQ a _))

/-- The cone source of the pencil is `i diag(w)`. -/
theorem cone_source_eq {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (y : Fin m → ℝ) :
    BlockBand.Critical.widthSourceScale p.W • ∑ a, conePoint y a • p.profileSourceMatrix (Q a) =
      Complex.I • Matrix.diagonal (fun x => ((coneWeight p Q y x : ℝ) : ℂ)) := by
  ext x x'
  by_cases hxx : x = x'
  · subst hxx
    simp only [Matrix.smul_apply, Matrix.sum_apply, Parameters.profileSourceMatrix,
      Matrix.diagonal_apply_eq, smul_eq_mul, conePoint, coneWeight,
      BlockBand.Critical.widthSourceScale]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp [Matrix.smul_apply, Matrix.sum_apply, Parameters.profileSourceMatrix,
      Matrix.diagonal_apply_ne _ hxx]

/-- **Finite-width cone bound** (every inverse determinant on the positive
imaginary cone lies in the closed unit disk). For every Hermitian `H` with `det(H - E) ≠ 0`,
nonnegative profiles `Q` and `y ∈ [0,∞)^m`: `|D_W(iy)| ≥ 1`. Deterministic, every `p`. -/
theorem one_le_norm_finiteEntireDeterminant_conePoint (E : ℝ) {m : ℕ} {Q : Fin m → C(Torus, ℝ)}
    (hQ : ∀ a t, 0 ≤ Q a t) {H : p.SiteMatrix} (hH : H.IsHermitian)
    (hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0) {y : Fin m → ℝ} (hy : ∀ a, 0 ≤ y a) :
    1 ≤ ‖finiteEntireDeterminant p E Q H (conePoint y)‖ := by
  set A := H - (E : ℂ) • (1 : p.SiteMatrix) with hAdef
  have hAh : A.IsHermitian := by
    refine hH.sub ?_
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  set D : p.SiteMatrix := Matrix.diagonal fun x => ((Real.sqrt (coneWeight p Q y x) : ℝ) : ℂ)
  have hDD : D * Dᴴ = Matrix.diagonal (fun x => ((coneWeight p Q y x : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (coneWeight_nonneg hQ hy x)]
  have hpen : BlockBand.Critical.finiteCharacteristicPencil A (fun a => p.profileSourceMatrix (Q a))
      (BlockBand.Critical.widthSourceScale p.W) (conePoint y) =
      A * (1 + (Complex.I • (A⁻¹ * D)) * Dᴴ) := by
    unfold BlockBand.Critical.finiteCharacteristicPencil
    rw [cone_source_eq, ← hDD, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAu, Matrix.one_mul]
  have hK : (Dᴴ * A⁻¹ * Dᴴᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hAh.inv
  have hval : finiteEntireDeterminant p E Q H (conePoint y) = (1 + Complex.I • (Dᴴ * A⁻¹ * D)).det := by
    simp only [finiteEntireDeterminant, EntireFunction.coe_ofDifferentiable,
      BlockBand.Critical.finiteCharacteristicDeterminant]
    rw [hpen, Matrix.det_mul, Matrix.det_one_add_mul_comm, mul_comm A.det, mul_assoc,
      mul_inv_cancel₀ hA, mul_one, Matrix.mul_smul, Matrix.mul_assoc]
  rw [hval]
  rw [conjTranspose_conjTranspose] at hK
  exact one_le_norm_det_one_add_I_smul hK

/-- The finite law of `D_W` is cone-bounded (law: the exact physical Gaussian ring law of any
finite realization; every `E`; nonnegative profiles). -/
theorem hasInverseConeBound_finiteEntireLaw (R : FiniteRealization p) (E : ℝ) {m : ℕ}
    {Q : Fin m → C(Torus, ℝ)} (hQ : ∀ a t, 0 ≤ Q a t) :
    HasInverseConeBound (finiteEntireLaw R E Q) := by
  intro y hy
  have hC : MeasurableSet {F : EntireFunction m | 1 ≤ ‖F (conePoint y)‖} :=
    (isClosed_le continuous_const
      (continuous_norm.comp (EntireFunction.continuous_eval_const _))).measurableSet
  change ∀ᵐ F ∂((R.model.law : Measure p.SiteMatrix).map (finiteEntireDeterminant p E Q)),
    1 ≤ ‖F (conePoint y)‖
  rw [ae_map_iff (BlockBand.Critical.JointRecovery.measurable_finiteEntireDeterminant E Q).aemeasurable hC]
  filter_upwards [R.model.isPhysical.1, R.model.ae_baseDeterminant_ne_zero E] with H hH hA
  exact one_le_norm_finiteEntireDeterminant_conePoint E hQ hH hA hy

/-- **The cone bound passes to weak limits** (closed sets, portmanteau), along any non-trivial
filter. -/
theorem hasInverseConeBound_of_tendsto {m : ℕ} {ι : Type*} {L : Filter ι} [L.NeBot]
    {μs : ι → RandomEntire m} {μ : RandomEntire m} (h : Tendsto μs L (𝓝 μ))
    (hμs : ∀ i, HasInverseConeBound (μs i)) : HasInverseConeBound μ := by
  intro y hy
  have hC : IsClosed {F : EntireFunction m | 1 ≤ ‖F (conePoint y)‖} :=
    isClosed_le continuous_const (continuous_norm.comp (EntireFunction.continuous_eval_const _))
  have hj : ∀ i, (μs i : Measure (EntireFunction m)) {F | 1 ≤ ‖F (conePoint y)‖} = 1 := fun i =>
    (prob_compl_eq_zero_iff hC.measurableSet).mp (ae_iff.mp (hμs i y hy))
  have hls := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hC
  simp only [hj, limsup_const] at hls
  exact ae_iff.mpr ((prob_compl_eq_zero_iff hC.measurableSet).mpr (le_antisymm prob_le_one hls))

theorem fullProfile_nonneg {k : ℕ} {q : Fin k → C(Torus, ℝ)} (hq : IsProfileFamily q) :
    ∀ a t, 0 ≤ fullProfile q a t := by
  intro a t
  refine Fin.cases ?_ (fun i => ?_) a
  · simp [fullProfile]
  · simp only [fullProfile, Fin.cons_succ]; exact hq i t

/-- **`EntireLawContract.coneBound`**: every
limit has `|D(iy)| ≥ 1` on the positive imaginary cone. No hypothesis: one critical sequence and
one choice of realizations exist (`exists_criticalSequence`, `nonempty_finiteRealization`), the
finite laws are cone-bounded, and the bound is closed. -/
theorem entireLaw_coneBound : ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
    ∀ μ : RandomEntire (k + 1), IsEntireLimit b E hb hb' τ q μ → HasInverseConeBound μ := by
  intro b E hb hb' _ τ k q hq μ hμ
  obtain ⟨s⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
  let R : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j =>
    (BlockBand.Model.Construction.nonempty_finiteRealization _).some
  exact hasInverseConeBound_of_tendsto (hμ s R) fun j =>
    hasInverseConeBound_finiteEntireLaw (R j) E (fullProfile_nonneg hq)

end BlockBand.Critical.EntireLaw
