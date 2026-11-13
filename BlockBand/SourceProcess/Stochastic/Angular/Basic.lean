module

public import BlockBand.Internal.Contracts.TransmissionAngular
public import BlockBand.SourceProcess.Stochastic.Dyson.Lagrange

/-!
# Complex angular contract: eigenvector selections and phases

* `canonEv`: the columns of Mathlib's eigenvector unitary in the decreasing labels; it is an
  `IsEigenSelection` (`isEigenSelection_canonEv`).
* `eigenSel_unit`: selected eigenvectors are unit vectors (`tr P_i = 1`).
* `exists_phase_ev`: two selections differ by unimodular phases, so
  `angularArray V (ev H) = θ · angularArray V (canonEv N H)`;
  `phaseInv_ev`: a phase-invariant test does not see the selection.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Matrix
open scoped Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

/-- The canonical eigenvector selection: column `π⁻¹ i` of Mathlib's eigenvector unitary. -/
def canonEv (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : Fin N → ℂ :=
  fun a => specU H a ((specPerm N).symm i)

theorem isEigenSelection_canonEv (N : ℕ) : IsEigenSelection N (canonEv N) := by
  intro H hH hs i
  rw [dysonProjection_eq_conj hH hs i]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, vecMulVec_apply, Matrix.star_apply, canonEv, Pi.star_apply]
  rw [Finset.sum_eq_single ((specPerm N).symm i)]
  · simp
  · intro k _ hk
    have : specPerm N k ≠ i := fun h => hk (by rw [← h, Equiv.symm_apply_apply])
    simp [this]
  · simp

/-- Selected eigenvectors are unit vectors. -/
theorem eigenSel_unit {ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ}
    (hev : IsEigenSelection N ev) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (i : Fin N) : star (ev H i) ⬝ᵥ ev H i = 1 := by
  have h := trace_proj hH hs i
  rw [hev H hH hs i, trace_vecMulVec, dotProduct_comm] at h
  exact h

theorem norm_sq_of_dot {u : Fin N → ℂ} (hu : star u ⬝ᵥ u = 1) : ∑ a, ‖u a‖ ^ 2 = 1 := by
  have h : ((∑ a, ‖u a‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Complex.mul_conj', mul_comm]; rfl
  rw [hu] at h; exact_mod_cast h

/-- Unit vectors with the same rank-one projection differ by a unimodular phase. -/
theorem eq_smul_of_vecMulVec_eq {u w : Fin N → ℂ} (hu : star u ⬝ᵥ u = 1)
    (hw : star w ⬝ᵥ w = 1) (h : vecMulVec u (star u) = vecMulVec w (star w)) :
    w = (star u ⬝ᵥ w) • u ∧ ‖star u ⬝ᵥ w‖ = 1 := by
  have e1 : vecMulVec w (star w) *ᵥ w = w := by
    rw [vecMulVec_mulVec, hw]; simp
  have e2 : vecMulVec u (star u) *ᵥ w = (star u ⬝ᵥ w) • u := by
    rw [vecMulVec_mulVec, op_smul_eq_smul]
  have hwu : w = (star u ⬝ᵥ w) • u := by rw [← e2, h, e1]
  refine ⟨hwu, ?_⟩
  set c := star u ⬝ᵥ w
  have hc : star w ⬝ᵥ w = star c * c := by
    conv_lhs => rw [hwu]
    rw [star_smul, smul_dotProduct, dotProduct_smul, hu]; simp [smul_eq_mul]
  rw [hw, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hc
  have h2 : ‖c‖ ^ 2 = 1 := by exact_mod_cast hc.symm
  have h0 : 0 ≤ ‖c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖c‖ - 1), sq_nonneg (‖c‖ + 1)]

theorem angularArray_smul (V : Matrix (Fin N) (Fin r) ℂ) (θ : Fin N → ℂ)
    (u : Fin N → Fin N → ℂ) :
    angularArray V (fun i => θ i • u i) = fun i a => θ i * angularArray V u i a := by
  funext i a
  simp [angularArray, Matrix.mulVec_smul]

/-- Two selections differ by phases on the angular array. -/
theorem exists_phase_ev {ev ev' : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ}
    (hev : IsEigenSelection N ev) (hev' : IsEigenSelection N ev')
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hs : HasSimpleSpectrum N H)
    (V : Matrix (Fin N) (Fin r) ℂ) :
    ∃ θ : Fin N → ℂ, (∀ i, ‖θ i‖ = 1) ∧
      angularArray V (ev H) = fun i a => θ i * angularArray V (ev' H) i a := by
  have key := fun i => eq_smul_of_vecMulVec_eq (eigenSel_unit hev' hH hs i)
    (eigenSel_unit hev hH hs i) ((hev' H hH hs i).symm.trans (hev H hH hs i))
  refine ⟨fun i => star (ev' H i) ⬝ᵥ ev H i, fun i => (key i).2, ?_⟩
  rw [← angularArray_smul]
  congr 1
  funext i
  exact (key i).1

/-- **Selection independence** of a phase-invariant test. -/
theorem phaseInv_ev {f : AngularArray N r → ℝ} (hf : IsPhaseInvariant f)
    {ev ev' : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ}
    (hev : IsEigenSelection N ev) (hev' : IsEigenSelection N ev')
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hs : HasSimpleSpectrum N H)
    (V : Matrix (Fin N) (Fin r) ℂ) :
    f (angularArray V (ev H)) = f (angularArray V (ev' H)) := by
  obtain ⟨θ, hθ, he⟩ := exists_phase_ev hev hev' hH hs V
  rw [he, hf θ hθ]

/-- Entries of an angular array at unit vectors are bounded by the frame column norms. -/
theorem norm_angularArray_le (V : Matrix (Fin N) (Fin r) ℂ) {u : Fin N → Fin N → ℂ}
    (hu : ∀ i, star (u i) ⬝ᵥ u i = 1) (i : Fin N) (a : Fin r) :
    ‖angularArray V u i a‖ ≤ ∑ b, ‖V b a‖ := by
  have hle : ∀ b, ‖u i b‖ ≤ 1 := fun b => by
    have h := norm_sq_of_dot (hu i)
    have : ‖u i b‖ ^ 2 ≤ 1 := h ▸ Finset.single_le_sum (f := fun b => ‖u i b‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
    nlinarith [norm_nonneg (u i b)]
  simp only [angularArray, Matrix.mulVec, dotProduct, conjTranspose_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_right (norm_nonneg _) (hle b)

end BlockBand.SourceProcess.Stochastic.ComplexAngular
