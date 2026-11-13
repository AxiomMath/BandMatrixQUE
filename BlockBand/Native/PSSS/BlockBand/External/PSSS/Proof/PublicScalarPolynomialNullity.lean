module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicScalarAbsoluteContinuity
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEShiftedCompressionNull

/-!
# Polynomial nullity for the heterogeneous public scalar product

A complex polynomial in all flattened public block coordinates has an
almost-surely nonzero evaluation as soon as it has one real witness.  Unlike
the single-GUE result, the coordinate variances may differ from block to block;
absolute continuity is supplied by `publicScalarMeasure_absolutelyContinuous`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory MvPolynomial

/-- Nonzero complex polynomials have null zero sets under the complete
heterogeneous public scalar product. -/
theorem ae_eval_ne_zero_publicScalarMeasure
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j)
    (F : MvPolynomial (BlockGUE.PublicScalarIndex d) ℂ)
    (x₀ : BlockGUE.PublicScalarSample d)
    (h₀ : MvPolynomial.eval (fun c => (x₀ c : ℂ)) F ≠ 0) :
    ∀ᵐ x ∂BlockGUE.publicScalarMeasure d hd,
      MvPolynomial.eval (fun c => (x c : ℂ)) F ≠ 0 := by
  let e := Fintype.equivFin (BlockGUE.PublicScalarIndex d)
  let R : MvPolynomial (BlockGUE.PublicScalarIndex d) ℝ :=
    mvPolynomialRealPart F ^ 2 + mvPolynomialImagPart F ^ 2
  have hR (y : BlockGUE.PublicScalarSample d) :
      MvPolynomial.eval y R =
        Complex.normSq (MvPolynomial.eval (fun c => (y c : ℂ)) F) := by
    simp only [R, map_add, map_pow, eval_mvPolynomialRealPart,
      eval_mvPolynomialImagPart, Complex.normSq_apply]
    ring
  let Q : MvPolynomial
      (Fin (Fintype.card (BlockGUE.PublicScalarIndex d))) ℝ :=
    MvPolynomial.rename e R
  have hQ (y : Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) → ℝ) :
      MvPolynomial.eval y Q = MvPolynomial.eval (y ∘ e) R :=
    MvPolynomial.eval_rename _ _ _
  have hQne : Q ≠ 0 := by
    intro hQ0
    have h := hQ (x₀ ∘ e.symm)
    rw [hQ0, map_zero, hR] at h
    apply h₀
    have hx : (fun c => (((x₀ ∘ e.symm) ∘ e) c : ℂ)) =
        fun c => (x₀ c : ℂ) := by
      funext c
      simp
    rw [hx] at h
    exact Complex.normSq_eq_zero.mp h.symm
  have hnullQ := volume_mvPolynomial_zeroSet _ Q hQne
  have hnullR : (volume : Measure (BlockGUE.PublicScalarSample d))
      {x | MvPolynomial.eval x R = 0} = 0 := by
    let E : (BlockGUE.PublicScalarSample d) ≃ᵐ
        (Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
    have hvol : Measure.map E
        (volume : Measure (BlockGUE.PublicScalarSample d)) =
          (volume : Measure
            (Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) → ℝ)) := by
      simpa [E, MeasureTheory.volume_pi] using
        (Measure.pi_map_piCongrLeft e
          (fun _ : Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) =>
            (volume : Measure ℝ)))
    let S := {y : Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) → ℝ |
      MvPolynomial.eval y Q = 0}
    have hS : MeasurableSet S :=
      Q.continuous_eval.measurable (measurableSet_singleton 0)
    have hpre : E ⁻¹' S = {x | MvPolynomial.eval x R = 0} := by
      ext x
      simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, E]
      rw [hQ]
      have hfun :
          ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) x) ∘ e = x := by
        funext i
        exact @MeasurableEquiv.piCongrLeft_apply_apply
          (BlockGUE.PublicScalarIndex d)
          (Fin (Fintype.card (BlockGUE.PublicScalarIndex d))) e
          (fun _ => ℝ) _ x i
      rw [hfun]
    have hmp : MeasurePreserving E
        (volume : Measure (BlockGUE.PublicScalarSample d))
        (volume : Measure
          (Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) → ℝ)) :=
      ⟨E.measurable, hvol⟩
    rw [← hpre, hmp.measure_preimage hS.nullMeasurableSet]
    exact hnullQ
  rw [ae_iff]
  refine measure_mono_null ?_
    (publicScalarMeasure_absolutelyContinuous d hd hnullR)
  intro x hx
  simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hx ⊢
  rw [hR]
  simpa using hx

end PSSSNative.BlockBand.PSSS
