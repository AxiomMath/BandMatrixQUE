module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SChainGlobalCoordinates

/-!
# The linear resolvent functional on Euclidean coordinates

ER Proposition 5.4 (global law) input.  For a deterministic matrix `A` and a
nonreal `z`, `resolventFunctional A z x = Tr[(coordMatrix x - z)⁻¹ A]`.  It is smooth
on the whole coordinate space, its real and imaginary parts have Fréchet gradient
of squared norm at most `2 |Im z|⁻⁴ ‖A‖²_F`, and it is bounded by
`|Im z|⁻¹ ∑ᵢⱼ |Aᵢⱼ|`.  These are deterministic (Ward / operator-norm) facts.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSChainGlobal

open MeasureTheory ProbabilityTheory
open ERProfile ERConcrete ERGaussianPoincareIntermediate ERProductCoordinateAnalysis

open ERGaussianCoordinate

/-!
## Generic finite-matrix estimates
-/

section Generic

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum of squared entry moduli `∑ᵢⱼ |Mᵢⱼ|²` (squared Hilbert–Schmidt norm) of a
square complex matrix over an arbitrary finite index type. -/
def entrySqSum (M : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

omit [DecidableEq ι] in
theorem entrySqSum_nonneg (M : Matrix ι ι ℂ) : 0 ≤ entrySqSum M := by
  unfold entrySqSum
  positivity

omit [DecidableEq ι] in
theorem entrySqSum_conjTranspose (M : Matrix ι ι ℂ) :
    entrySqSum Mᴴ = entrySqSum M := by
  unfold entrySqSum
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- The sharp operator-norm bound for a Hermitian source-sign resolvent. -/
theorem norm_sourceInverse_le (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖sourceInverse H z‖ ≤ |z.im|⁻¹ := by
  unfold sourceInverse
  have hzero : (0 : Matrix ι ι ℂ).PosSemidef := Matrix.PosSemidef.zero
  let B := H - (z.re : ℂ) • (1 : Matrix ι ι ℂ)
  have hB : B.IsHermitian :=
    hH.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re))
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hshape :
        cauchyResolventPencil B 0 (-z.im) 0 = H - z • (1 : Matrix ι ι ℂ) := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [B, cauchyResolventPencil, Complex.ext_iff]
        ring
      · simp [B, cauchyResolventPencil, hab]
    have hb := norm_cauchyResolventPencil_nonsing_inv_le
      B 0 hB hzero (neg_pos.mpr hzneg) (show 0 ≤ (0 : ℂ).im by simp)
    rw [hshape] at hb
    simpa [abs_of_neg hzneg] using hb
  · have hshape :
        cauchyResolventPencil B 0 z.im 0 = (H - z • (1 : Matrix ι ι ℂ))ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hH.eq]
      ext a b
      by_cases hab : a = b
      · subst b
        simp [B, cauchyResolventPencil, Complex.ext_iff]
      · simp [B, cauchyResolventPencil, hab]
    have hb := norm_cauchyResolventPencil_nonsing_inv_le
      B 0 hB hzero hzpos (show 0 ≤ (0 : ℂ).im by simp)
    rw [hshape, ← Matrix.conjTranspose_nonsing_inv,
      Matrix.l2_opNorm_conjTranspose] at hb
    simpa [abs_of_pos hzpos] using hb

/-- Every entry is bounded by the `ℓ²` operator norm. -/
theorem norm_entry_le_l2_opNorm (M : Matrix ι ι ℂ) (i j : ι) :
    ‖M i j‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  let y : EuclideanSpace ℂ ι := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M e
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hyi : y.ofLp i = M i j := by simp [y, e]
  calc
    ‖M i j‖ = ‖y.ofLp i‖ := congrArg norm hyi.symm
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖ * ‖e‖ := hop
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, he, mul_one]

/-- Column form of the operator-norm bound. -/
theorem sum_norm_mulVec_sq_le (M : Matrix ι ι ℂ) (w : ι → ℂ) :
    ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ‖M‖ ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
  let w' : EuclideanSpace ℂ ι := WithLp.toLp 2 w
  have hop := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm w'
  rw [Matrix.l2_opNorm_toEuclideanCLM] at hop
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hop 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hsq
  simpa [w'] using hsq

/-- Left multiplication contracts the Hilbert–Schmidt norm by the operator norm. -/
theorem entrySqSum_mul_left_le (M B : Matrix ι ι ℂ) :
    entrySqSum (M * B) ≤ ‖M‖ ^ 2 * entrySqSum B := by
  unfold entrySqSum
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := sum_norm_mulVec_sq_le M (fun i => B i j)
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- Right multiplication contracts the Hilbert–Schmidt norm by the operator norm. -/
theorem entrySqSum_mul_right_le (B M : Matrix ι ι ℂ) :
    entrySqSum (B * M) ≤ ‖M‖ ^ 2 * entrySqSum B := by
  rw [← entrySqSum_conjTranspose, Matrix.conjTranspose_mul, ← entrySqSum_conjTranspose B,
    ← Matrix.l2_opNorm_conjTranspose M]
  exact entrySqSum_mul_left_le _ _

omit [DecidableEq ι] in
/-- Cauchy–Schwarz for the trace pairing. -/
theorem norm_trace_mul_sq_le (D Y : Matrix ι ι ℂ) :
    ‖Matrix.trace (D * Y)‖ ^ 2 ≤ entrySqSum D * entrySqSum Y := by
  have htri : ‖Matrix.trace (D * Y)‖ ≤ ∑ x : ι × ι, ‖D x.1 x.2‖ * ‖Y x.2 x.1‖ := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x : ι × ι => ‖D x.1 x.2‖) (fun x : ι × ι => ‖Y x.2 x.1‖)
  have hD : ∑ x : ι × ι, ‖D x.1 x.2‖ ^ 2 = entrySqSum D := by
    rw [Fintype.sum_prod_type]; rfl
  have hY : ∑ x : ι × ι, ‖Y x.2 x.1‖ ^ 2 = entrySqSum Y := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; rfl
  rw [hD, hY] at hcs
  calc ‖Matrix.trace (D * Y)‖ ^ 2 ≤ (∑ x : ι × ι, ‖D x.1 x.2‖ * ‖Y x.2 x.1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ _ := hcs

/-- Hermitian resolvent sandwich bound `‖G A G‖²_HS ≤ |Im z|⁻⁴ ‖A‖²_HS`. -/
theorem entrySqSum_sourceInverse_sandwich_le (H A : Matrix ι ι ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    entrySqSum (sourceInverse H z * A * sourceInverse H z) ≤
      |z.im|⁻¹ ^ 4 * entrySqSum A := by
  have hG := norm_sourceInverse_le H hH hz
  have hG2 : ‖sourceInverse H z‖ ^ 2 ≤ |z.im|⁻¹ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hG 2
  have hA := entrySqSum_nonneg A
  calc entrySqSum (sourceInverse H z * A * sourceInverse H z)
      ≤ ‖sourceInverse H z‖ ^ 2 * entrySqSum (sourceInverse H z * A) :=
        entrySqSum_mul_right_le _ _
    _ ≤ ‖sourceInverse H z‖ ^ 2 * (‖sourceInverse H z‖ ^ 2 * entrySqSum A) := by
        gcongr
        exact entrySqSum_mul_left_le _ _
    _ ≤ |z.im|⁻¹ ^ 2 * (|z.im|⁻¹ ^ 2 * entrySqSum A) := by
        gcongr
    _ = |z.im|⁻¹ ^ 4 * entrySqSum A := by ring

end Generic

/-- Squared Frobenius norm `∑ᵢⱼ |Aᵢⱼ|²`. -/
def frobSq {p : Params} (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- `Tr[(coordMatrix x - z)⁻¹ A]`. -/
def resolventFunctional {p : Params} (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (z : ℂ) (x : CoordSpace p) : ℂ :=
  Matrix.trace (sourceInverse (coordMatrix x) z * A)

/-!
## Linearity and size of the Hermitian reconstruction
-/

/-- The determinant of a matrix-valued map with real-smooth entries is real-smooth. -/
theorem contDiff_det_of_entries {κ E : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E → Matrix κ κ ℂ) (hM : ∀ i j, ContDiff ℝ ⊤ (fun x => M x i j)) :
    ContDiff ℝ ⊤ (fun x => (M x).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro k _
  exact hM (σ k) k

theorem siteLE_self {p : Params} (a : Site p.n p.W) : siteLE p a a := by
  unfold siteLE
  exact le_rfl

theorem matrixOfUpperCoordinates_diag {p : Params} (u : UpperPair p → ℂ)
    (a : Site p.n p.W) :
    matrixOfUpperCoordinates u a a = ((u ⟨(a, a), siteLE_self a⟩).re : ℂ) := by
  simp [matrixOfUpperCoordinates]

theorem matrixOfUpperCoordinates_of_siteLE {p : Params} (u : UpperPair p → ℂ)
    {a b : Site p.n p.W} (hab : a ≠ b) (h : siteLE p a b) :
    matrixOfUpperCoordinates u a b = u ⟨(a, b), h⟩ := by
  simp only [matrixOfUpperCoordinates, dite_eq_right hab, dite_eq_left h]

theorem matrixOfUpperCoordinates_of_not_siteLE {p : Params} (u : UpperPair p → ℂ)
    {a b : Site p.n p.W} (hab : a ≠ b) (h : ¬ siteLE p a b) :
    matrixOfUpperCoordinates u a b =
      star (u ⟨(b, a), siteLE_reverse_of_not a b h⟩) := by
  simp only [matrixOfUpperCoordinates, dite_eq_right hab, dite_eq_right h]

theorem matrixOfUpperCoordinates_add {p : Params} (u v : UpperPair p → ℂ) :
    matrixOfUpperCoordinates (u + v) =
      matrixOfUpperCoordinates u + matrixOfUpperCoordinates v := by
  ext a b
  rw [Matrix.add_apply]
  by_cases hab : a = b
  · subst b
    rw [matrixOfUpperCoordinates_diag, matrixOfUpperCoordinates_diag,
      matrixOfUpperCoordinates_diag]
    change (((u _ + v _).re : ℝ) : ℂ) = _
    simp
  · by_cases h : siteLE p a b
    · rw [matrixOfUpperCoordinates_of_siteLE _ hab h, matrixOfUpperCoordinates_of_siteLE _ hab h,
        matrixOfUpperCoordinates_of_siteLE _ hab h]
      rfl
    · rw [matrixOfUpperCoordinates_of_not_siteLE _ hab h,
        matrixOfUpperCoordinates_of_not_siteLE _ hab h,
        matrixOfUpperCoordinates_of_not_siteLE _ hab h]
      exact star_add _ _

theorem matrixOfUpperCoordinates_smul {p : Params} (t : ℝ) (u : UpperPair p → ℂ) :
    matrixOfUpperCoordinates (t • u) = t • matrixOfUpperCoordinates u := by
  ext a b
  rw [Matrix.smul_apply]
  by_cases hab : a = b
  · subst b
    rw [matrixOfUpperCoordinates_diag, matrixOfUpperCoordinates_diag]
    change (((t • u _).re : ℝ) : ℂ) = _
    simp
  · by_cases h : siteLE p a b
    · rw [matrixOfUpperCoordinates_of_siteLE _ hab h, matrixOfUpperCoordinates_of_siteLE _ hab h]
      rfl
    · rw [matrixOfUpperCoordinates_of_not_siteLE _ hab h,
        matrixOfUpperCoordinates_of_not_siteLE _ hab h]
      change star (t • u _) = _
      simp

theorem coordEntries_add {p : Params} (x y : CoordSpace p) :
    coordEntries (x + y) = coordEntries x + coordEntries y := by
  funext q
  simp [coordEntries]
  ring

theorem coordEntries_smul {p : Params} (t : ℝ) (x : CoordSpace p) :
    coordEntries (t • x) = t • coordEntries x := by
  funext q
  simp [coordEntries, Complex.ext_iff]

theorem coordMatrix_add {p : Params} (x y : CoordSpace p) :
    coordMatrix (x + y) = coordMatrix x + coordMatrix y := by
  rw [coordMatrix, coordEntries_add, matrixOfUpperCoordinates_add]
  rfl

theorem coordMatrix_smul {p : Params} (t : ℝ) (x : CoordSpace p) :
    coordMatrix (t • x) = t • coordMatrix x := by
  rw [coordMatrix, coordEntries_smul, matrixOfUpperCoordinates_smul]
  rfl

/-- One entry of the Hermitian reconstruction, as a real-linear functional. -/
def coordMatrixEntryLinear {p : Params} (a b : Site p.n p.W) :
    CoordSpace p →ₗ[ℝ] ℂ where
  toFun x := coordMatrix x a b
  map_add' x y := by rw [coordMatrix_add]; rfl
  map_smul' t x := by rw [coordMatrix_smul]; rfl

theorem contDiff_coordMatrix_entry {p : Params} (a b : Site p.n p.W) :
    ContDiff ℝ ⊤ (fun x : CoordSpace p => coordMatrix x a b) :=
  (LinearMap.toContinuousLinearMap (coordMatrixEntryLinear (p := p) a b)).contDiff

/-- The squared Hilbert–Schmidt norm of the reconstruction is at most twice the
squared size of its upper coordinates. -/
theorem entrySqSum_matrixOfUpperCoordinates_le {p : Params} (u : UpperPair p → ℂ) :
    entrySqSum (matrixOfUpperCoordinates u) ≤ 2 * ∑ q, ‖u q‖ ^ 2 := by
  let g : Site p.n p.W × Site p.n p.W → ℝ := fun x =>
    if h : siteLE p x.1 x.2 then ‖u ⟨x, h⟩‖ ^ 2 else 0
  have hg : ∀ a b (h : siteLE p a b), g (a, b) = ‖u ⟨(a, b), h⟩‖ ^ 2 := by
    intro a b h
    exact dite_eq_left (show siteLE p (a, b).1 (a, b).2 from h)
  have hg0 : ∀ a b, 0 ≤ g (a, b) := by
    intro a b
    simp only [g]
    split_ifs <;> positivity
  have hpt : ∀ a b, ‖matrixOfUpperCoordinates u a b‖ ^ 2 ≤ g (a, b) + g (b, a) := by
    intro a b
    by_cases hab : a = b
    · subst b
      have hle : siteLE p a a := by unfold siteLE; exact le_rfl
      have hM : matrixOfUpperCoordinates u a a = ((u ⟨(a, a), hle⟩).re : ℂ) := by
        simp [matrixOfUpperCoordinates]
      have hre : ‖(((u ⟨(a, a), hle⟩).re : ℂ))‖ ≤ ‖u ⟨(a, a), hle⟩‖ := by
        simpa using Complex.abs_re_le_norm (u ⟨(a, a), hle⟩)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hre 2
      rw [hM, hg a a hle]
      nlinarith [sq_nonneg ‖u ⟨(a, a), hle⟩‖]
    · by_cases h : siteLE p a b
      · have hM : matrixOfUpperCoordinates u a b = u ⟨(a, b), h⟩ := by
          simp only [matrixOfUpperCoordinates, dite_eq_right hab, dite_eq_left h]
        rw [hM, hg a b h]
        linarith [hg0 b a]
      · have hba := siteLE_reverse_of_not a b h
        have hM : matrixOfUpperCoordinates u a b = star (u ⟨(b, a), hba⟩) := by
          simp only [matrixOfUpperCoordinates, dite_eq_right hab, dite_eq_right h]
        rw [hM, norm_star, hg b a hba]
        linarith [hg0 a b]
  have hsum : ∑ x, g x = ∑ q : UpperPair p, ‖u q‖ ^ 2 := by
    symm
    apply Fintype.sum_of_injective (fun q : UpperPair p => q.1)
      (fun q r h => Subtype.ext h)
    · intro x hx
      simp only [g]
      rw [dite_eq_right]
      intro h
      exact hx ⟨⟨x, h⟩, rfl⟩
    · intro q
      exact (hg q.1.1 q.1.2 q.2).symm
  have hprod : ∑ x, g x = ∑ a, ∑ b, g (a, b) := Fintype.sum_prod_type' (fun a b => g (a, b))
  calc entrySqSum (matrixOfUpperCoordinates u)
      ≤ ∑ a, ∑ b, (g (a, b) + g (b, a)) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ = 2 * ∑ x, g x := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun a b => g (b, a)), hprod]
        ring
    _ = 2 * ∑ q, ‖u q‖ ^ 2 := by rw [hsum]

theorem sum_norm_coordEntries_sq {p : Params} (x : CoordSpace p) :
    ∑ q, ‖coordEntries x q‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
  simp [coordEntries]
  ring

theorem entrySqSum_coordMatrix_le {p : Params} (x : CoordSpace p) :
    entrySqSum (coordMatrix x) ≤ 2 * ‖x‖ ^ 2 := by
  rw [← sum_norm_coordEntries_sq]
  exact entrySqSum_matrixOfUpperCoordinates_le _

/-!
## Smoothness
-/

/-- Every source-inverse entry of the reconstruction is globally real-smooth at a
nonreal spectral parameter. -/
theorem contDiff_sourceInverse_coordMatrix_entry {p : Params} {z : ℂ} (hz : z.im ≠ 0)
    (i j : Site p.n p.W) :
    ContDiff ℝ ⊤ (fun x : CoordSpace p => sourceInverse (coordMatrix x) z i j) := by
  let P : CoordSpace p → Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
    fun x => coordMatrix x - z • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
  have hP : ∀ a b, ContDiff ℝ ⊤ (fun x => P x a b) := by
    intro a b
    simp only [P, Matrix.sub_apply]
    exact (contDiff_coordMatrix_entry a b).sub contDiff_const
  have hdet0 : ∀ x, (P x).det ≠ 0 := by
    intro x
    have hu := isUnit_resolventPencil (coordMatrix x) (coordMatrix_isHermitian x) hz
    have hPu : IsUnit (P x) := by simpa [P, neg_sub] using hu.neg
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hPu).ne_zero
  change ContDiff ℝ ⊤ (fun x => (P x)⁻¹ i j)
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((contDiff_det_of_entries P hP).inv hdet0).mul
  apply contDiff_det_of_entries
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hP _ _

theorem resolventFunctional_eq_sum {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (z : ℂ) (x : CoordSpace p) :
    resolventFunctional A z x =
      ∑ i, ∑ j, sourceInverse (coordMatrix x) z i j * A j i := by
  simp [resolventFunctional, Matrix.trace, Matrix.mul_apply]

/-- ER Proposition 5.4 input: for nonreal `z`, the map
`x ↦ Tr[(coordMatrix x - z)⁻¹ A]` is real-smooth on the whole coordinate space
(no restriction to the support of the Gaussian law). -/
theorem contDiff_resolventFunctional {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    ContDiff ℝ ⊤ (resolventFunctional (p := p) A z) := by
  have h : resolventFunctional (p := p) A z =
      fun x => ∑ i, ∑ j, sourceInverse (coordMatrix x) z i j * A j i :=
    funext (resolventFunctional_eq_sum A z)
  rw [h]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_sourceInverse_coordMatrix_entry hz i j).mul contDiff_const

/-!
## The derivative
-/

/-- Derivative along a straight line through the coordinate space. -/
theorem hasDerivAt_resolventFunctional_line {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (x v : CoordSpace p) :
    HasDerivAt (fun t : ℝ => resolventFunctional A z (x + t • v))
      (-Matrix.trace (sourceInverse (coordMatrix x) z * coordMatrix v *
        sourceInverse (coordMatrix x) z * A)) 0 := by
  have hline : ∀ t : ℝ, coordMatrix (x + t • v) = coordMatrix x + t • coordMatrix v := by
    intro t
    rw [coordMatrix_add, coordMatrix_smul]
  have hent := fun i j => ERSharpCoordinateIBP.hasDerivAt_sourceInverse_direction
    (coordMatrix x) (coordMatrix v) (coordMatrix_isHermitian x) (coordMatrix_isHermitian v)
    z hz i j 0
  simp only [zero_smul, add_zero] at hent
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i, ∑ j, sourceInverse (coordMatrix x + t • coordMatrix v) z i j * A j i)
      (∑ i, ∑ j, (-(sourceInverse (coordMatrix x) z * coordMatrix v *
        sourceInverse (coordMatrix x) z) i j) * A j i) 0 :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => (hent i j).mul_const (A j i)
  have hfun : (fun t : ℝ => resolventFunctional A z (x + t • v)) =
      fun t : ℝ => ∑ i, ∑ j, sourceInverse (coordMatrix x + t • coordMatrix v) z i j * A j i := by
    funext t
    rw [resolventFunctional_eq_sum, hline]
  rw [hfun]
  convert hsum using 1
  simp [Matrix.trace, Matrix.mul_apply, Finset.sum_neg_distrib]

/-- The Fréchet derivative applied to a direction `v` is `-Tr[G D_v G A]`. -/
theorem fderiv_resolventFunctional_apply {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (x v : CoordSpace p) :
    fderiv ℝ (resolventFunctional A z) x v =
      -Matrix.trace (sourceInverse (coordMatrix x) z * coordMatrix v *
        sourceInverse (coordMatrix x) z * A) := by
  have hdiff : DifferentiableAt ℝ (resolventFunctional A z) (x + (0 : ℝ) • v) :=
    ((contDiff_resolventFunctional A hz).differentiable (by simp)) _
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  simp only [zero_smul, add_zero] at hc
  exact hc.unique (hasDerivAt_resolventFunctional_line A hz x v)

open scoped Matrix.Norms.L2Operator in
/-- Directional bound: `|D_v F(x)| ≤ (2 |Im z|⁻⁴ ‖A‖²_F)^{1/2} ‖v‖`. -/
theorem norm_fderiv_resolventFunctional_apply_le {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (x v : CoordSpace p) :
    ‖fderiv ℝ (resolventFunctional A z) x v‖ ≤
      √(2 * |z.im|⁻¹ ^ 4 * frobSq A) * ‖v‖ := by
  rw [fderiv_resolventFunctional_apply A hz x v, norm_neg]
  set G := sourceInverse (coordMatrix x) z
  set D := coordMatrix v
  have htr : Matrix.trace (G * D * G * A) = Matrix.trace (D * (G * A * G)) := by
    rw [show G * D * G * A = G * (D * G * A) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show D * G * A * G = D * (G * A * G) by simp [Matrix.mul_assoc]]
  rw [htr]
  have h1 := norm_trace_mul_sq_le D (G * A * G)
  have h2 := entrySqSum_coordMatrix_le v
  have h3 := entrySqSum_sourceInverse_sandwich_le (coordMatrix x) A
    (coordMatrix_isHermitian x) hz
  have hA : 0 ≤ frobSq A := entrySqSum_nonneg A
  have hY := entrySqSum_nonneg (G * A * G)
  have hK : 0 ≤ 2 * |z.im|⁻¹ ^ 4 * frobSq A := by positivity
  have hsq : ‖Matrix.trace (D * (G * A * G))‖ ^ 2 ≤
      (√(2 * |z.im|⁻¹ ^ 4 * frobSq A) * ‖v‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]
    calc ‖Matrix.trace (D * (G * A * G))‖ ^ 2
        ≤ entrySqSum D * entrySqSum (G * A * G) := h1
      _ ≤ (2 * ‖v‖ ^ 2) * (|z.im|⁻¹ ^ 4 * frobSq A) := by
          gcongr
          exact h3
      _ = 2 * |z.im|⁻¹ ^ 4 * frobSq A * ‖v‖ ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- A real projection of the derivative inherits the directional bound. -/
theorem norm_comp_fderiv_resolventFunctional_sq_le {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordSpace p) (L : ℂ →L[ℝ] ℝ) (hL : ∀ c, ‖L c‖ ≤ ‖c‖) :
    ‖L.comp (fderiv ℝ (resolventFunctional A z) x)‖ ^ 2 ≤
      2 * |z.im|⁻¹ ^ 4 * frobSq A := by
  have hK : 0 ≤ 2 * |z.im|⁻¹ ^ 4 * frobSq A := by
    have := entrySqSum_nonneg A
    unfold frobSq
    positivity
  have hop : ‖L.comp (fderiv ℝ (resolventFunctional A z) x)‖ ≤
      √(2 * |z.im|⁻¹ ^ 4 * frobSq A) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v =>
      (hL _).trans (norm_fderiv_resolventFunctional_apply_le A hz x v)
  calc ‖L.comp (fderiv ℝ (resolventFunctional A z) x)‖ ^ 2
      ≤ √(2 * |z.im|⁻¹ ^ 4 * frobSq A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = 2 * |z.im|⁻¹ ^ 4 * frobSq A := Real.sq_sqrt hK

/-- ER Proposition 5.4 input (Ward/operator-norm gradient bound), real part:
for every coordinate point `x` and nonreal `z`,
`‖∇ Re Tr[G A](x)‖² ≤ 2 |Im z|⁻⁴ ∑ᵢⱼ |Aᵢⱼ|²`, uniformly in `x`. -/
theorem norm_fderiv_re_resolventFunctional_sq_le {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordSpace p) :
    ‖fderiv ℝ (fun y => (resolventFunctional A z y).re) x‖ ^ 2 ≤
      2 * |z.im|⁻¹ ^ 4 * frobSq A := by
  have hdiff : DifferentiableAt ℝ (resolventFunctional A z) x :=
    ((contDiff_resolventFunctional A hz).differentiable (by simp)) x
  have hfd : fderiv ℝ (fun y => (resolventFunctional A z y).re) x =
      Complex.reCLM.comp (fderiv ℝ (resolventFunctional A z) x) := by
    change fderiv ℝ (Complex.reCLM ∘ resolventFunctional A z) x = _
    exact (Complex.reCLM.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  rw [hfd]
  exact norm_comp_fderiv_resolventFunctional_sq_le A hz x _ fun c => by
    simpa using Complex.abs_re_le_norm c

/-- ER Proposition 5.4 input (Ward/operator-norm gradient bound), imaginary part:
for every coordinate point `x` and nonreal `z`,
`‖∇ Im Tr[G A](x)‖² ≤ 2 |Im z|⁻⁴ ∑ᵢⱼ |Aᵢⱼ|²`, uniformly in `x`. -/
theorem norm_fderiv_im_resolventFunctional_sq_le {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordSpace p) :
    ‖fderiv ℝ (fun y => (resolventFunctional A z y).im) x‖ ^ 2 ≤
      2 * |z.im|⁻¹ ^ 4 * frobSq A := by
  have hdiff : DifferentiableAt ℝ (resolventFunctional A z) x :=
    ((contDiff_resolventFunctional A hz).differentiable (by simp)) x
  have hfd : fderiv ℝ (fun y => (resolventFunctional A z y).im) x =
      Complex.imCLM.comp (fderiv ℝ (resolventFunctional A z) x) := by
    change fderiv ℝ (Complex.imCLM ∘ resolventFunctional A z) x = _
    exact (Complex.imCLM.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  rw [hfd]
  exact norm_comp_fderiv_resolventFunctional_sq_le A hz x _ fun c => by
    simpa using Complex.abs_im_le_norm c

open scoped Matrix.Norms.L2Operator in
/-- ER Proposition 5.4 input: the uniform bound
`|Tr[G A](x)| ≤ |Im z|⁻¹ ∑ᵢⱼ |Aᵢⱼ|` for every coordinate point `x`, from the
entrywise bound `|Gᵢⱼ| ≤ ‖G‖ ≤ |Im z|⁻¹`. -/
theorem norm_resolventFunctional_le {p : Params}
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (x : CoordSpace p) :
    ‖resolventFunctional A z x‖ ≤ |z.im|⁻¹ * ∑ i, ∑ j, ‖A i j‖ := by
  rw [resolventFunctional_eq_sum]
  set G := sourceInverse (coordMatrix x) z
  have hG : ∀ i j, ‖G i j‖ ≤ |z.im|⁻¹ := fun i j =>
    (norm_entry_le_l2_opNorm G i j).trans
      (norm_sourceInverse_le _ (coordMatrix_isHermitian x) hz)
  calc ‖∑ i, ∑ j, G i j * A j i‖ ≤ ∑ i, ∑ j, ‖G i j‖ * ‖A j i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (le_of_eq (by simp)))
    _ ≤ ∑ i, ∑ j, |z.im|⁻¹ * ‖A j i‖ := by
        gcongr with i _ j _
        exact hG i j
    _ = |z.im|⁻¹ * ∑ i, ∑ j, ‖A i j‖ := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]

end ERSChainGlobal
end GaussianRing
end ERNative.BlockBand

