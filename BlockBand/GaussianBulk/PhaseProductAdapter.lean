module
public import BlockBand.GaussianBulk.LocalKernelEnvelope
public import BlockBand.External.Johansson.SourceStatement

/-!
# The exponentiated saddle phase as a product

`N` times the normalized mean is the sum, so the exponential of `N` times a saddle phase
difference is an explicit Gaussian factor times the product ratio `∏_j (w - d_j)/(z - d_j)`,
with no branch ambiguity, for any (possibly repeated) real source `d`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open scoped BigOperators

/-- `N · complexMean f = Σ_j f j`. -/
theorem dimension_mul_complexMean {N : ℕ} (hN : 0 < N) (f : Fin N → ℂ) :
    (N:ℂ)*complexMean f=∑ j,f j := by
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have he : (N:ℂ)*(((N:ℝ)⁻¹:ℝ):ℂ)=1 := by
    rw [Complex.ofReal_inv,Complex.ofReal_natCast,mul_inv_cancel₀ hn]
  unfold complexMean
  rw [← mul_assoc,he,one_mul]

/-- The exponential of `N` times the saddle phase difference is the Gaussian factor times the
product ratio over the source points; the integer factor `N` removes the branch ambiguities of
the logarithms. -/
theorem exp_saddlePhase_difference_product {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t : ℝ) (z w : ℂ)
    (hz : ∀ j,z-(d j:ℂ)≠0) (hw : ∀ j,w-(d j:ℂ)≠0) :
    Complex.exp ((N:ℂ)*(saddlePhase d E t w-saddlePhase d E t z)) =
      Complex.exp ((N:ℂ)*(((w-(E:ℂ))^2-(z-(E:ℂ))^2)/(2*(t:ℂ))))*
        ∏ j,(w-(d j:ℂ))/(z-(d j:ℂ)) := by
  have hp : (N:ℂ)*(saddlePhase d E t w-saddlePhase d E t z)=
      (N:ℂ)*(((w-(E:ℂ))^2-(z-(E:ℂ))^2)/(2*(t:ℂ)))+
        ∑ j,(Complex.log (w-(d j:ℂ))-Complex.log (z-(d j:ℂ))) := by
    unfold saddlePhase
    simp only [mul_sub,mul_add]
    rw [dimension_mul_complexMean hN,dimension_mul_complexMean hN,Finset.sum_sub_distrib]
    ring
  rw [hp,Complex.exp_add,Complex.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [sub_eq_add_neg,Complex.exp_add,Complex.exp_neg,Complex.exp_log (hw j),
    Complex.exp_log (hz j),div_eq_mul_inv]

end BlockBand.GaussianBulk
