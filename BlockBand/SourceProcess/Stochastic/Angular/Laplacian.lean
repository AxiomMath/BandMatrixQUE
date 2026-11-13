module

public import BlockBand.SourceProcess.Stochastic.Angular.Interface

/-!
# Complex angular contract: tools for the Laplacian identity

A first building block of the proposition `ArrayLaplacianDiag`, towards
`TransmissionAngular.ComplexAngularContract`.

`trace_bilin_eq_of_complete`: the coordinate trace `∑_a B e_a e_a` of a bilinear form on `ℝ^d`
equals `∑_b B w_b w_b` for every family `w` with the completeness relation
`∑_b w_b ⊗ w_b = I`. With `w_b = hermVec` of the eigen-adapted orthonormal basis
`u_k u_k^*`, `(u_i u_j^* ± u_j u_i^*)/√2` this turns the coordinate Laplacian into a sum of
second derivatives along adapted directions.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular

/-- **The trace of a bilinear form in any complete family.** -/
theorem trace_bilin_eq_of_complete {d : ℕ} {ι : Type*} [Fintype ι]
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (w : ι → Fin d → ℝ)
    (hw : ∀ k l : Fin d, ∑ b, w b k * w b l = if k = l then 1 else 0) :
    ∑ a : Fin d, B (Pi.single a 1) (Pi.single a 1) = ∑ b, B (w b) (w b) := by
  have hexp : ∀ v : Fin d → ℝ, v = ∑ k, v k • (Pi.single k 1 : Fin d → ℝ) := fun v => by
    funext m; simp [Finset.sum_apply, Pi.single_apply]
  have hB : ∀ b, B (w b) (w b) =
      ∑ k, ∑ l, w b k * w b l * B (Pi.single l 1) (Pi.single k 1) := fun b => by
    conv_lhs => rw [hexp (w b)]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hB]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hw, ite_mul, one_mul, zero_mul]
  simp

end BlockBand.SourceProcess.Stochastic.ComplexAngular
