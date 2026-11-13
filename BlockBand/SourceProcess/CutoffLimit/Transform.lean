module

public import BlockBand.Internal.Contracts.TransmissionLaws
public import BlockBand.SourceProcess.SourceProcessLaw.DetBound
public import Mathlib.Analysis.Matrix.Order

/-!
# The bounded probe transform: values in `[0,1]` and uniform continuity

* `probeVal_mem`: `0 ≤ F(A) ≤ 1` for `A ⪰ 0`, `a ≥ 0` (Sylvester `det(I + D A) = det(I + D^{½}AD^{½})`
  and `re_inv_det_mem`);
* `probeVal_uc`: `F` is uniformly continuous on `{A ⪰ 0, |A_ij| ≤ L}` (a compact set on which `F`
  is continuous), with a modulus in the entrywise distance that depends only on `π`, `a`, `L`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.SourceProcessLaw
open scoped ComplexOrder

variable {π : Type*} [Fintype π] [DecidableEq π] {J : ℕ}

/-- `F(A) = Π_j Re det(I + diag(a_j) A)⁻¹`. -/
def probeVal (a : Fin J → π → ℝ) (A : Matrix π π ℂ) : ℝ :=
  ∏ j, ((1 + diagonal (fun i => (a j i : ℂ)) * A).det⁻¹).re

theorem sampledTransformValue_eq {K p M : ℕ} (a : Fin J → Fin p → ℝ)
    (G : GramState (SrcCol K (Fin p × Fin M))) :
    sampledTransformValue a G = probeVal (fun j (i : Fin p × Fin M) => a j i.1) (probeBlock G.1) :=
  rfl

/-- Sylvester: `det(I + diag(d) A) = det(I + diag(√d) A diag(√d))` for `d ≥ 0`. -/
theorem det_one_add_diag_mul {d : π → ℝ} (hd : ∀ i, 0 ≤ d i) (A : Matrix π π ℂ) :
    (1 + diagonal (fun i => (d i : ℂ)) * A).det =
      (1 + diagonal (fun i => (Real.sqrt (d i) : ℂ)) * A *
        diagonal (fun i => (Real.sqrt (d i) : ℂ))).det := by
  have h : diagonal (fun i => (d i : ℂ)) * A =
      diagonal (fun i => (Real.sqrt (d i) : ℂ)) * (diagonal (fun i => (Real.sqrt (d i) : ℂ)) * A) := by
    rw [← Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd i)]
  rw [h, Matrix.det_one_add_mul_comm, Matrix.mul_assoc]

theorem posSemidef_sandwich {d : π → ℝ} {A : Matrix π π ℂ} (hA : A.PosSemidef) :
    (diagonal (fun i => (Real.sqrt (d i) : ℂ)) * A *
      diagonal (fun i => (Real.sqrt (d i) : ℂ))).PosSemidef := by
  have hc : (diagonal (fun i => (Real.sqrt (d i) : ℂ)))ᴴ =
      diagonal (fun i => (Real.sqrt (d i) : ℂ)) := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  have := hA.mul_mul_conjTranspose_same (diagonal (fun i => (Real.sqrt (d i) : ℂ)))
  rwa [hc] at this

theorem re_inv_det_diag_mem {d : π → ℝ} (hd : ∀ i, 0 ≤ d i) {A : Matrix π π ℂ}
    (hA : A.PosSemidef) :
    0 < ((1 + diagonal (fun i => (d i : ℂ)) * A).det⁻¹).re ∧
      ((1 + diagonal (fun i => (d i : ℂ)) * A).det⁻¹).re ≤ 1 := by
  rw [det_one_add_diag_mul hd]
  exact re_inv_det_mem (posSemidef_sandwich hA)

theorem det_one_add_diag_ne {d : π → ℝ} (hd : ∀ i, 0 ≤ d i) {A : Matrix π π ℂ}
    (hA : A.PosSemidef) : (1 + diagonal (fun i => (d i : ℂ)) * A).det ≠ 0 := by
  intro h0
  have := (re_inv_det_diag_mem hd hA).1
  rw [h0, _root_.inv_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- **`0 ≤ F(A) ≤ 1`** on positive semidefinite probe blocks. -/
theorem probeVal_mem {a : Fin J → π → ℝ} (ha : ∀ j i, 0 ≤ a j i) {A : Matrix π π ℂ}
    (hA : A.PosSemidef) : 0 ≤ probeVal a A ∧ probeVal a A ≤ 1 :=
  ⟨Finset.prod_nonneg fun j _ => (re_inv_det_diag_mem (ha j) hA).1.le,
    Finset.prod_le_one₀ (fun j _ => (re_inv_det_diag_mem (ha j) hA).1.le)
      fun j _ => (re_inv_det_diag_mem (ha j) hA).2⟩

/-- The bounded positive semidefinite set `{A ⪰ 0, |A_ij| ≤ L}`. -/
def psdBox (π : Type*) [Fintype π] [DecidableEq π] (L : ℝ) : Set (Matrix π π ℂ) :=
  {A | A.PosSemidef} ∩ {A | ∀ i j, ‖A i j‖ ≤ L}

theorem isCompact_psdBox (L : ℝ) : IsCompact (psdBox π L) := by
  have hbox : IsCompact {A : Matrix π π ℂ | ∀ i j, ‖A i j‖ ≤ L} := by
    have h := isCompact_univ_pi fun _ : π =>
      isCompact_univ_pi fun _ : π => isCompact_closedBall (0 : ℂ) L
    have he : {A : Matrix π π ℂ | ∀ i j, ‖A i j‖ ≤ L} =
        Set.univ.pi fun _ : π => Set.univ.pi fun _ : π => Metric.closedBall (0 : ℂ) L := by
      ext A
      refine ⟨fun hA => Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_,
        fun hA i j => ?_⟩
      · simpa using hA i j
      · simpa using Set.mem_univ_pi.1 (Set.mem_univ_pi.1 hA i) j
    rw [he]
    exact h
  exact hbox.inter_left Matrix.posSemidef_is_closed

theorem continuousOn_probeVal {a : Fin J → π → ℝ} (ha : ∀ j i, 0 ≤ a j i) (L : ℝ) :
    ContinuousOn (probeVal a) (psdBox π L) := by
  intro A hA
  refine ContinuousAt.continuousWithinAt ?_
  refine tendsto_finsetProd _ fun j _ => ?_
  refine Complex.continuous_re.continuousAt.comp (ContinuousAt.inv₀ ?_ (det_one_add_diag_ne (ha j) hA.1))
  exact (Continuous.matrix_det (continuous_const.add (continuous_const.mul continuous_id))).continuousAt

/-- **Uniform continuity of `F` on `{A ⪰ 0, |A_ij| ≤ L}`**, in the entrywise distance. -/
theorem probeVal_uc {a : Fin J → π → ℝ} (ha : ∀ j i, 0 ≤ a j i) (L ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A B : Matrix π π ℂ, A ∈ psdBox π L → B ∈ psdBox π L →
      (∀ i j, ‖A i j - B i j‖ < δ) → |probeVal a A - probeVal a B| < ε := by
  have huc : UniformContinuousOn (α := π → π → ℂ) (probeVal a) (psdBox π L) :=
    (isCompact_psdBox (π := π) L).uniformContinuousOn_of_continuous (continuousOn_probeVal ha L)
  obtain ⟨δ, hδ, hδε⟩ := (Metric.uniformContinuousOn_iff (α := π → π → ℂ)).1 huc ε hε
  refine ⟨δ, hδ, fun A B hA hB hAB => ?_⟩
  have hd : dist (α := π → π → ℂ) A B < δ := by
    refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => ?_
    rw [dist_eq_norm]
    exact hAB i j
  have := hδε A hA B hB hd
  rwa [Real.dist_eq] at this

end BlockBand.SourceProcess.CutoffLimit
