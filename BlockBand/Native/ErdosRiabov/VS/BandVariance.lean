module

public import BlockBand.Native.ErdosRiabov.VS.Band
public import BlockBand.Adapters.ErdosRiabov.ShortRingLocalLawProfile

set_option autoImplicit false

/-!
# Coordinate variances and the matrix generator of the VS band process

The variances of the real Gaussian coordinates are given by the short-ring profile, and the
generator and bracket of the band process in coordinates are the matrix ones.

Setting: `p : BlockBand.Parameters`, the real Gaussian coordinates
`ringEquiv p : p.GaussianCoordinate ≃ Fin (ringDim p)`, their variances `ringVariance p`
(`gaussianCoordinateVariance`), the physical profile `S = p.entryVariance`, which is the
short-ring profile `shortRingProfile p.b p.n p.W` under the row-major site equivalence
`siteFinEquiv p` (`shortRingProfile_siteFinEquiv`).

* **`ringVariance_eq_profile`**: `v = S_aa` on the diagonal label of `a`, `v = S_ab / 2` on
  the real and imaginary labels of `a < b` (row-major order `siteIndex`), and `v = 0` on the
  redundant labels (`¬ siteIndex a < siteIndex b`), with `S = shortRingProfile p.b p.n p.W` read
  through `siteFinEquiv p`; the same with `S = p.entryVariance` is `ringVariance_diag`,
  `ringVariance_offDiag_of_lt`, `ringVariance_offDiag_of_not_lt`.
* `ringBasis p i = ringMatrix p (e_i)`, the matrix direction of coordinate `i`:
  `E_{aa} = e_{aa}` (`ringBasis_diag`), and for `a < b` the real direction
  `bandRe a b = e_{ab} + e_{ba}` and imaginary direction `bandIm a b = i e_{ab} - i e_{ba}`
  (`ringBasis_re`, `ringBasis_im`).
* `sum_ringVariance_smul`: for **any** `Q : SiteMatrix → M`,
  `∑_i v_i Q(E_i) = ∑_a S_aa Q(e_aa) + ∑_{a<b} (S_ab/2) (Q(bandRe a b) + Q(bandIm a b))`.
* **`generator_matrix`**: for every `ℂ`-bilinear form `B` on matrices,
  `∑_i v_i B(E_i, E_i) = ∑_{a,b} S_ab B(e_ab, e_ba)`; with `B = D²F(H)` for a holomorphic
  matrix function `F` this is `½∑_c v_c ∂_c² = ½∑_{a,b} S_ab ∂_ab ∂_ba` (`generator_matrix_re`
  for real parts, `generator_matrix_profile` for the short-ring profile).
* **`bracket_matrix`**: for every `ℂ`-linear form `L`,
  `∑_i v_i |L E_i|² = ∑_{a,b} S_ab |L e_ab|²`; with `L = DF(H)` this is
  `d⟨𝓜, 𝓜̄⟩ = ∑_{ab} S_ab |∂_ab F|² dt`.

The profile is `S`, not `tS`: the VS process has unit-rate increments.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Adapters.ErdosRiabov
open Matrix

variable (p : BlockBand.Parameters)

/-!
### The coordinate variances
-/

theorem ringVariance_ringEquiv (c : p.GaussianCoordinate) :
    ringVariance p (ringEquiv p c) = (p.gaussianCoordinateVariance c : ℝ) := by
  rw [ringVariance, Equiv.symm_apply_apply]

theorem ringVariance_diag (x : p.Site) :
    ringVariance p (ringEquiv p (.inl x)) = p.entryVariance x x := by
  rw [ringVariance_ringEquiv]
  rfl

theorem ringVariance_offDiag_of_lt {x y : p.Site} (h : p.siteIndex x < p.siteIndex y)
    (b : Bool) : ringVariance p (ringEquiv p (.inr (x, y, b))) = p.entryVariance x y / 2 := by
  rw [ringVariance_ringEquiv]
  simp only [BlockBand.Parameters.gaussianCoordinateVariance, h]
  rfl

theorem ringVariance_offDiag_of_not_lt {x y : p.Site} (h : ¬ p.siteIndex x < p.siteIndex y)
    (b : Bool) : ringVariance p (ringEquiv p (.inr (x, y, b))) = 0 := by
  rw [ringVariance_ringEquiv]
  simp [BlockBand.Parameters.gaussianCoordinateVariance, h]

/-- **The coordinate variances are the profile.** With
`S = shortRingProfile p.b p.n p.W` read through the row-major site equivalence `siteFinEquiv p`:
`v = S_aa` on the diagonal label of `a`; `v = S_ab / 2` on the real (`false`) and imaginary
(`true`) labels of `a < b`; `v = 0` on the redundant labels `(a, b, ·)` with `¬ a < b`. -/
theorem ringVariance_eq_profile :
    (∀ x : p.Site, ringVariance p (ringEquiv p (.inl x)) =
        shortRingProfile p.b p.n p.W (siteFinEquiv p x) (siteFinEquiv p x)) ∧
      (∀ (x y : p.Site) (b : Bool), p.siteIndex x < p.siteIndex y →
        ringVariance p (ringEquiv p (.inr (x, y, b))) =
          shortRingProfile p.b p.n p.W (siteFinEquiv p x) (siteFinEquiv p y) / 2) ∧
      (∀ (x y : p.Site) (b : Bool), ¬ p.siteIndex x < p.siteIndex y →
        ringVariance p (ringEquiv p (.inr (x, y, b))) = 0) := by
  refine ⟨fun x => ?_, fun x y b h => ?_, fun x y b h => ringVariance_offDiag_of_not_lt p h b⟩
  · rw [ringVariance_diag, shortRingProfile_siteFinEquiv]
  · rw [ringVariance_offDiag_of_lt p h, shortRingProfile_siteFinEquiv]

/-- The physical profile is symmetric (via the symmetric short-ring profile). -/
theorem entryVariance_swap (x y : p.Site) : p.entryVariance y x = p.entryVariance x y := by
  rw [← shortRingProfile_siteFinEquiv, ← shortRingProfile_siteFinEquiv]
  exact shortRingProfile_symm _ _ _ _ _

/-!
### The matrix directions of the coordinates
-/

/-- The matrix direction of coordinate `i`: `E_i = ringMatrix (e_i)`. -/
def ringBasis (i : Fin (ringDim p)) : p.SiteMatrix := ringMatrix p (Pi.single i 1)

/-- The real off-diagonal direction `e_ab + e_ba`. -/
def bandRe (x y : p.Site) : p.SiteMatrix := single x y 1 + single y x 1

/-- The imaginary off-diagonal direction `i e_ab - i e_ba`. -/
def bandIm (x y : p.Site) : p.SiteMatrix :=
  Complex.I • single x y (1 : ℂ) - Complex.I • single y x (1 : ℂ)

theorem ringBasis_ringEquiv (c : p.GaussianCoordinate) :
    ringBasis p (ringEquiv p c) = p.gaussianReconstruction (Pi.single c 1) := by
  rw [ringBasis, ringMatrix]
  congr 1
  funext c'
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]

theorem ringBasis_diag (x : p.Site) :
    ringBasis p (ringEquiv p (.inl x)) = single x x 1 := by
  rw [ringBasis_ringEquiv]
  ext a b
  simp only [BlockBand.Parameters.gaussianReconstruction, single_apply, Pi.single_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hx : x = a
    · subst hx
      simp
    · simp [hx, Ne.symm hx]
  · have hn : ¬ (x = a ∧ x = b) := fun h => hab (h.1.symm.trans h.2)
    simp [hab, hn]

theorem ringBasis_re {x y : p.Site} (h : p.siteIndex x < p.siteIndex y) :
    ringBasis p (ringEquiv p (.inr (x, y, false))) = bandRe p x y := by
  have hxy : x ≠ y := fun e => by subst e; exact lt_irrefl _ h
  rw [ringBasis_ringEquiv]
  ext a b
  simp only [BlockBand.Parameters.gaussianReconstruction, bandRe, Matrix.add_apply, single_apply,
    Pi.single_apply]
  by_cases h1 : a = x ∧ b = y
  · obtain ⟨rfl, rfl⟩ := h1
    simp [h, hxy, Ne.symm hxy]
  by_cases h2 : a = y ∧ b = x
  · obtain ⟨rfl, rfl⟩ := h2
    simp [hxy, Ne.symm hxy, not_lt_of_gt h]
  have h1' : ¬ (x = a ∧ y = b) := fun e => h1 ⟨e.1.symm, e.2.symm⟩
  have h2' : ¬ (y = a ∧ x = b) := fun e => h2 ⟨e.1.symm, e.2.symm⟩
  have h2'' : ¬ (b = x ∧ a = y) := fun e => h2 ⟨e.2, e.1⟩
  split_ifs <;> simp_all

theorem ringBasis_im {x y : p.Site} (h : p.siteIndex x < p.siteIndex y) :
    ringBasis p (ringEquiv p (.inr (x, y, true))) = bandIm p x y := by
  have hxy : x ≠ y := fun e => by subst e; exact lt_irrefl _ h
  rw [ringBasis_ringEquiv]
  ext a b
  simp only [BlockBand.Parameters.gaussianReconstruction, bandIm, Matrix.sub_apply,
    Matrix.smul_apply, single_apply, Pi.single_apply]
  by_cases h1 : a = x ∧ b = y
  · obtain ⟨rfl, rfl⟩ := h1
    simp [h, hxy, Ne.symm hxy]
  by_cases h2 : a = y ∧ b = x
  · obtain ⟨rfl, rfl⟩ := h2
    simp [hxy, Ne.symm hxy, not_lt_of_gt h]
  have h1' : ¬ (x = a ∧ y = b) := fun e => h1 ⟨e.1.symm, e.2.symm⟩
  have h2' : ¬ (y = a ∧ x = b) := fun e => h2 ⟨e.1.symm, e.2.symm⟩
  have h2'' : ¬ (b = x ∧ a = y) := fun e => h2 ⟨e.2, e.1⟩
  split_ifs <;> simp_all

/-!
### Reindexing sums over the coordinates
-/

/-- **Coordinate sums as matrix sums.** For every `Q : SiteMatrix → M`,
`∑_i v_i Q(E_i) = ∑_a S_aa Q(e_aa) + ∑_{a<b} (S_ab/2) (Q(bandRe a b) + Q(bandIm a b))`. -/
theorem sum_ringVariance_smul {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : p.SiteMatrix → M) :
    ∑ i, ringVariance p i • Q (ringBasis p i) =
      ∑ x, p.entryVariance x x • Q (single x x 1) +
        ∑ x, ∑ y, if p.siteIndex x < p.siteIndex y then
          (p.entryVariance x y / 2) • (Q (bandRe p x y) + Q (bandIm p x y)) else 0 := by
  rw [← (ringEquiv p).sum_comp, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [ringVariance_diag, ringBasis_diag]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.sum_bool]
    split_ifs with h
    · rw [ringVariance_offDiag_of_lt p h, ringVariance_offDiag_of_lt p h, ringBasis_re p h,
        ringBasis_im p h, smul_add, add_comm]
    · rw [ringVariance_offDiag_of_not_lt p h, ringVariance_offDiag_of_not_lt p h, zero_smul,
        zero_smul, add_zero]

/-- A double sum over sites splits into the diagonal and the strict upper triangle (for the
row-major order `siteIndex`). -/
theorem sum_sum_eq_diag_add_upper {M : Type*} [AddCommMonoid M] (g : p.Site → p.Site → M) :
    ∑ a, ∑ b, g a b = ∑ a, g a a +
      ∑ a, ∑ b, if p.siteIndex a < p.siteIndex b then g a b + g b a else 0 := by
  have key : ∀ a b, g a b = ((if a = b then g a b else 0) +
      (if p.siteIndex a < p.siteIndex b then g a b else 0)) +
      (if p.siteIndex b < p.siteIndex a then g a b else 0) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp
    · rcases lt_trichotomy (p.siteIndex a) (p.siteIndex b) with h | h | h
      · simp [hab, h, not_lt_of_gt h]
      · exact absurd (p.siteIndex_injective h) hab
      · simp [hab, h, not_lt_of_gt h]
  have hC : (∑ a, ∑ b, if p.siteIndex b < p.siteIndex a then g a b else 0) =
      ∑ a, ∑ b, if p.siteIndex a < p.siteIndex b then g b a else 0 := Finset.sum_comm
  calc ∑ a, ∑ b, g a b
      = ∑ a, ∑ b, (((if a = b then g a b else 0) +
          (if p.siteIndex a < p.siteIndex b then g a b else 0)) +
          (if p.siteIndex b < p.siteIndex a then g a b else 0)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = ∑ a, g a a + ((∑ a, ∑ b, if p.siteIndex a < p.siteIndex b then g a b else 0) +
          ∑ a, ∑ b, if p.siteIndex b < p.siteIndex a then g a b else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          add_assoc]
    _ = _ := by
        rw [hC, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp

/-!
### The matrix generator and bracket
-/

/-- **Matrix generator.** For every `ℂ`-bilinear form `B` on matrices,
`∑_i v_i B(E_i, E_i) = ∑_{a,b} S_ab B(e_ab, e_ba)`, `S = p.entryVariance`. With
`B = D²F(H)` for a holomorphic `F` this is `½∑_c v_c ∂_c² F = ½∑_{a,b} S_ab ∂_ab ∂_ba F`. -/
theorem generator_matrix (B : p.SiteMatrix →ₗ[ℂ] p.SiteMatrix →ₗ[ℂ] ℂ) :
    ∑ i, (ringVariance p i : ℂ) * B (ringBasis p i) (ringBasis p i) =
      ∑ a, ∑ b, (p.entryVariance a b : ℂ) * B (single a b 1) (single b a 1) := by
  have h := sum_ringVariance_smul p (M := ℂ) fun E => B E E
  simp only [Complex.real_smul] at h
  rw [h, sum_sum_eq_diag_add_upper p
    fun a b => (p.entryVariance a b : ℂ) * B (single a b 1) (single b a 1)]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hxy
  · rw [entryVariance_swap p x y]
    simp only [bandRe, bandIm, map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    linear_combination ((p.entryVariance x y : ℂ) / 2 *
      (B (single x y 1) (single x y 1) - B (single x y 1) (single y x 1) -
        B (single y x 1) (single x y 1) + B (single y x 1) (single y x 1))) * Complex.I_sq
  · rfl

/-- Real part of `generator_matrix` (real-valued test functions `Re F`). -/
theorem generator_matrix_re (B : p.SiteMatrix →ₗ[ℂ] p.SiteMatrix →ₗ[ℂ] ℂ) :
    ∑ i, ringVariance p i * (B (ringBasis p i) (ringBasis p i)).re =
      (∑ a, ∑ b, (p.entryVariance a b : ℂ) * B (single a b 1) (single b a 1)).re := by
  rw [← generator_matrix, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

/-- `generator_matrix` with the short-ring profile `shortRingProfile p.b p.n p.W`, read through
the row-major site equivalence. -/
theorem generator_matrix_profile (B : p.SiteMatrix →ₗ[ℂ] p.SiteMatrix →ₗ[ℂ] ℂ) :
    ∑ i, (ringVariance p i : ℂ) * B (ringBasis p i) (ringBasis p i) =
      ∑ a, ∑ b, (shortRingProfile p.b p.n p.W (siteFinEquiv p a) (siteFinEquiv p b) : ℂ) *
        B (single a b 1) (single b a 1) := by
  simp only [shortRingProfile_siteFinEquiv]
  exact generator_matrix p B

/-- **Matrix bracket.** For every `ℂ`-linear form `L` on matrices,
`∑_i v_i |L E_i|² = ∑_{a,b} S_ab |L e_ab|²`, `S = p.entryVariance`. With `L = DF(H)` this is
`d⟨𝓜, 𝓜̄⟩ = ∑_{ab} S_ab |∂_ab F|² dt`. -/
theorem bracket_matrix (L : p.SiteMatrix →ₗ[ℂ] ℂ) :
    ∑ i, ringVariance p i * ‖L (ringBasis p i)‖ ^ 2 =
      ∑ a, ∑ b, p.entryVariance a b * ‖L (single a b 1)‖ ^ 2 := by
  have h := sum_ringVariance_smul p (M := ℝ) fun E => ‖L E‖ ^ 2
  simp only [smul_eq_mul] at h
  rw [h, sum_sum_eq_diag_add_upper p fun a b => p.entryVariance a b * ‖L (single a b 1)‖ ^ 2]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hxy
  · rw [entryVariance_swap p x y]
    simp only [bandRe, bandIm, map_add, map_sub, map_smul, smul_eq_mul, Complex.sq_norm]
    rw [← mul_sub, Complex.normSq_mul, Complex.normSq_I, one_mul, Complex.normSq_add,
      Complex.normSq_sub]
    ring
  · rfl

/-- `bracket_matrix` with the short-ring profile `shortRingProfile p.b p.n p.W`. -/
theorem bracket_matrix_profile (L : p.SiteMatrix →ₗ[ℂ] ℂ) :
    ∑ i, ringVariance p i * ‖L (ringBasis p i)‖ ^ 2 =
      ∑ a, ∑ b, shortRingProfile p.b p.n p.W (siteFinEquiv p a) (siteFinEquiv p b) *
        ‖L (single a b 1)‖ ^ 2 := by
  simp only [shortRingProfile_siteFinEquiv]
  exact bracket_matrix p L

end BlockBand.Native.ErdosRiabov.VS
