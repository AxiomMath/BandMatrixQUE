module
public import BlockBand.Counting.SpectralScaling
public import BlockBand.Model.Observables

/-!
# Finite spectral count normalization

Multiplicity counts of finite spectra transform exactly under positive rescaling and under
the unfolding map `x ↦ q (x - E)`.  For the physical Gaussian ring this relates counts of
`H`, of `c^{-1/2} H`, and of the unfolded spectrum `N ρ (λ - E)` in closed intervals.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open Set Matrix
open BlockBand.Foundations.Spectral

variable {κ : Type*} [Fintype κ]

def eigenvalueCount (values : κ → ℝ) (J : Set ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => values i ∈ J)).card

theorem eigenvalueCount_le_dimension (values : κ → ℝ) (J : Set ℝ) :
    eigenvalueCount values J ≤ Fintype.card κ := by
  classical
  exact (Finset.card_filter_le (Finset.univ : Finset κ) (fun i => values i ∈ J)).trans_eq
    (Finset.card_univ : (Finset.univ : Finset κ).card = Fintype.card κ)

theorem eigenvalueCount_congr (values μ : κ → ℝ) (J K : Set ℝ)
    (h : ∀ i, values i ∈ J ↔ μ i ∈ K) :
    eigenvalueCount values J = eigenvalueCount μ K := by
  classical
  unfold eigenvalueCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h i

theorem mem_Icc_positiveScale (s : ℝ) (hs : 0 < s) (x a b : ℝ) :
    s * x ∈ Icc (s * a) (s * b) ↔ x ∈ Icc a b := by
  simp only [Set.mem_Icc, mul_le_mul_iff_right₀ hs]

theorem eigenvalueCount_positiveScale_Icc (values : κ → ℝ) (s : ℝ) (hs : 0 < s)
    (a b : ℝ) :
    eigenvalueCount (fun i => s * values i) (Icc (s * a) (s * b)) =
      eigenvalueCount values (Icc a b) := by
  exact eigenvalueCount_congr _ _ _ _ (fun i => mem_Icc_positiveScale s hs (values i) a b)

def orderedEigenvalueCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (J : Set ℝ) : ℕ :=
  eigenvalueCount (increasingEigenvalue hM) J

theorem orderedEigenvalueCount_positiveScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (s : ℝ) (hs : 0 < s)
    (hS : ((s : ℂ) • M).IsHermitian) (J : Set ℝ) :
    orderedEigenvalueCount hS J =
      orderedEigenvalueCount hM ((fun x => s * x) ⁻¹' J) := by
  apply eigenvalueCount_congr
  intro i
  rw [increasingEigenvalue_positiveScale hM s hs hS i]
  rfl

/-- Arbitrary spectral sets are transported by image, without endpoint conventions. -/
theorem mem_image_positiveScale (s : ℝ) (hs : 0 < s) (x : ℝ) (J : Set ℝ) :
    s * x ∈ (fun y => s * y) '' J ↔ x ∈ J := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy : y = x := mul_left_cancel₀ hs.ne' heq
    simpa only [hxy] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem orderedEigenvalueCount_positiveScale_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (s : ℝ) (hs : 0 < s)
    (hS : ((s : ℂ) • M).IsHermitian) (J : Set ℝ) :
    orderedEigenvalueCount hS ((fun x => s * x) '' J) =
      orderedEigenvalueCount hM J := by
  apply eigenvalueCount_congr
  intro i
  rw [increasingEigenvalue_positiveScale hM s hs hS i]
  exact mem_image_positiveScale s hs _ J

theorem orderedEigenvalueCount_positiveScale_Icc {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (s : ℝ) (hs : 0 < s)
    (hS : ((s : ℂ) • M).IsHermitian) (a b : ℝ) :
    orderedEigenvalueCount hS (Icc (s * a) (s * b)) =
      orderedEigenvalueCount hM (Icc a b) := by
  apply eigenvalueCount_congr
  intro i
  rw [increasingEigenvalue_positiveScale hM s hs hS i]
  exact mem_Icc_positiveScale s hs _ a b

/-- Exact microscopic-to-physical closed interval membership; arbitrary positive scale. -/
theorem mem_Icc_unfolding (q : ℝ) (hq : 0 < q) (E x a b : ℝ) :
    q * (x - E) ∈ Icc a b ↔ x ∈ Icc (E + a / q) (E + b / q) := by
  simp only [Set.mem_Icc]
  have ha : a ≤ q * (x - E) ↔ E + a / q ≤ x := by
    rw [mul_comm q, ← div_le_iff₀ hq]
    constructor <;> intro h <;> linarith
  have hb : q * (x - E) ≤ b ↔ x ≤ E + b / q := by
    rw [mul_comm q, ← le_div_iff₀ hq]
    constructor <;> intro h <;> linarith
  exact and_congr ha hb

theorem eigenvalueCount_unfolding (values : κ → ℝ) (q : ℝ) (hq : 0 < q)
    (E a b : ℝ) :
    eigenvalueCount (fun i => q * (values i - E)) (Icc a b) =
      eigenvalueCount values (Icc (E + a / q) (E + b / q)) := by
  exact eigenvalueCount_congr _ _ _ _ (fun i => mem_Icc_unfolding q hq E (values i) a b)

end BlockBand.Counting
namespace BlockBand.Parameters
open BlockBand.Counting BlockBand.Foundations.Spectral Set

theorem normalizedMatrix_hermitian (p : BlockBand.Parameters) {H : p.SiteMatrix}
    (hH : H.IsHermitian) : (p.normalizedMatrix H).IsHermitian := by
  apply hH.smul
  simp [IsSelfAdjoint]

theorem increasingEigenvalue_normalizedMatrix (p : BlockBand.Parameters) {H : p.SiteMatrix}
    (hH : H.IsHermitian) (i : Fin (Fintype.card p.Site)) :
    increasingEigenvalue (p.normalizedMatrix_hermitian hH) i =
      increasingEigenvalue hH i / Real.sqrt p.c := by
  have hs : 0 < (Real.sqrt p.c)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr p.c_pos)
  have h := increasingEigenvalue_positiveScale hH (Real.sqrt p.c)⁻¹ hs
    (by simpa only [normalizedMatrix, Complex.ofReal_inv] using p.normalizedMatrix_hermitian hH) i
  simpa only [normalizedMatrix, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using h

theorem orderedEigenvalueCount_normalizedMatrix (p : BlockBand.Parameters) {H : p.SiteMatrix}
    (hH : H.IsHermitian) (a b : ℝ) :
    orderedEigenvalueCount (p.normalizedMatrix_hermitian hH)
      (Icc (a / Real.sqrt p.c) (b / Real.sqrt p.c)) =
      orderedEigenvalueCount hH (Icc a b) := by
  apply eigenvalueCount_congr
  intro i
  rw [p.increasingEigenvalue_normalizedMatrix hH i]
  simpa only [div_eq_mul_inv, mul_comm] using
    mem_Icc_positiveScale (Real.sqrt p.c)⁻¹
      (inv_pos.mpr (Real.sqrt_pos.mpr p.c_pos)) (increasingEigenvalue hH i) a b

theorem orderedEigenvalueCount_normalizedMatrix_image (p : BlockBand.Parameters)
    {H : p.SiteMatrix} (hH : H.IsHermitian) (J : Set ℝ) :
    orderedEigenvalueCount (p.normalizedMatrix_hermitian hH)
      ((fun x => x / Real.sqrt p.c) '' J) = orderedEigenvalueCount hH J := by
  apply eigenvalueCount_congr
  intro i
  rw [p.increasingEigenvalue_normalizedMatrix hH i]
  simpa only [div_eq_mul_inv, mul_comm] using
    mem_image_positiveScale (Real.sqrt p.c)⁻¹
      (inv_pos.mpr (Real.sqrt_pos.mpr p.c_pos)) (increasingEigenvalue hH i) J

theorem orderedEigenvalueCount_normalizedDeformation (p : BlockBand.Parameters)
    {H A : p.SiteMatrix} (hH : H.IsHermitian) (hA : A.IsHermitian) (a b : ℝ) :
    orderedEigenvalueCount (p.normalizedMatrix_hermitian (hH.add hA))
      (Icc (a / Real.sqrt p.c) (b / Real.sqrt p.c)) =
      orderedEigenvalueCount (hH.add hA) (Icc a b) :=
  p.orderedEigenvalueCount_normalizedMatrix (hH.add hA) a b

theorem semicircleDensity_pos {E : ℝ} (hE : -2 < E ∧ E < 2) :
    0 < semicircleDensity E := by
  apply div_pos
  · apply Real.sqrt_pos.mpr
    nlinarith [hE.1, hE.2]
  · exact mul_pos (by norm_num) Real.pi_pos

theorem orderedEigenvalueCount_microscopic (p : BlockBand.Parameters)
    {H : p.SiteMatrix} (hH : H.IsHermitian) (E ρ : ℝ) (hρ : 0 < ρ) (a b : ℝ) :
    eigenvalueCount (fun i => (p.N : ℝ) * ρ * (increasingEigenvalue hH i - E))
      (Icc a b) = orderedEigenvalueCount hH
        (Icc (E + a / ((p.N : ℝ) * ρ)) (E + b / ((p.N : ℝ) * ρ))) := by
  exact eigenvalueCount_unfolding _ ((p.N : ℝ) * ρ)
    (mul_pos (by exact_mod_cast p.N_pos) hρ) E a b

theorem orderedEigenvalueCount_microscopic_normalized (p : BlockBand.Parameters)
    {H : p.SiteMatrix} (hH : H.IsHermitian) (E ρ : ℝ) (hρ : 0 < ρ) (a b : ℝ) :
    eigenvalueCount (fun i => (p.N : ℝ) * ρ * (increasingEigenvalue hH i - E))
      (Icc a b) = orderedEigenvalueCount (p.normalizedMatrix_hermitian hH)
        (Icc ((E + a / ((p.N : ℝ) * ρ)) / Real.sqrt p.c)
          ((E + b / ((p.N : ℝ) * ρ)) / Real.sqrt p.c)) := by
  rw [p.orderedEigenvalueCount_microscopic hH E ρ hρ a b]
  exact (p.orderedEigenvalueCount_normalizedMatrix hH _ _).symm

theorem SpectralRealization.unfoldedEigenvalueCount_Icc {p : BlockBand.Parameters}
    {model : p.GaussianRingModel} (spectral : p.SpectralRealization model)
    {E : ℝ} (hE : -2 < E ∧ E < 2) (H : p.SiteMatrix) (a b : ℝ) :
    eigenvalueCount (spectral.unfoldedEigenvalue E H) (Icc a b) =
      eigenvalueCount (spectral.eigenvalue H)
        (Icc (E + a / ((p.N : ℝ) * semicircleDensity E))
          (E + b / ((p.N : ℝ) * semicircleDensity E))) := by
  exact eigenvalueCount_unfolding _ ((p.N : ℝ) * semicircleDensity E)
    (mul_pos (by exact_mod_cast p.N_pos) (semicircleDensity_pos hE)) E a b

end BlockBand.Parameters
