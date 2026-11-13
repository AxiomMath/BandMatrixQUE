module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWickDefs
public import BlockBand.Endpoints.Response.TaggedConvexOrderWickMomentComb
public import BlockBand.Endpoints.Response.TaggedConvexOrderWickMomentGauss
public import BlockBand.Endpoints.Response.NearSchattenClock

/-!
# The complex Wick formula `TcxWickMoment`

**Statement** (`tcx_wickMoment : TcxWickMoment`): for every `m`, every finite `ι` and every
positive semidefinite `Q`, with `h ~ circularVectorLaw ι` (`CoareaPalm`; `E hh* = I`),
`E_h (h*Qh)^m = Σ_{π ∈ S_m} Π_{c cycle of π} Tr Q^{|c|}` (fixed points are cycles of length `1`).
No hypothesis beyond `Q ⪰ 0`; the identity is exact and uniform in `ι`.

**Proof.**
1. Unitary reduction (`tco_quadForm_eq_sum`, `tco_circularVectorLaw_map_unitary`):
   `h*Qh =ᵈ Σ_i λ_i |g_i|²`, `λ` the eigenvalues of `Q`.
2. Expansion over colourings `f : Fin m → ι`:
   `(Σ_i λ_i |g_i|²)^m = Σ_f (Π_a λ_{f a}) Π_i |g_i|^{2 k_i(f)}`, `k_i(f) = #f⁻¹(i)`.
3. `E Π_i |g_i|^{2k_i} = Π_i k_i!` (`wk_integral_prod_normSq_pow`).
4. `Σ_π Π_{r ∈ parts π} p_r = Σ_f (Π_a λ_{f a}) Π_i k_i(f)!`, `p_r = Σ_i λ_i^r = Tr Q^r`
   (`wk_sum_perm_parts_eq`, `ns_trace_pow`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm

/-- **Unitary reduction.** `E (h*Qh)^m = E (Σ_i λ_i |g_i|²)^m` for Hermitian `Q`. -/
theorem wk_integral_quadForm_pow_eq (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) :
    ∫ h, quadForm Q h ^ m ∂circularVectorLaw ι =
      ∫ g, (∑ i, hQ.eigenvalues i * Complex.normSq (g i)) ^ m ∂circularVectorLaw ι := by
  set U : Matrix ι ι ℂ := (hQ.eigenvectorUnitary).1
  have hU : star U ∈ Matrix.unitaryGroup ι ℂ := (hQ.eigenvectorUnitary)⁻¹.2
  set G : (ι → ℂ) → ℝ := fun g => (∑ i, hQ.eigenvalues i * Complex.normSq (g i)) ^ m
  have hG : Continuous G :=
    (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply i))).pow m
  have hmeas : Measurable (fun h : ι → ℂ => star U *ᵥ h) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  calc ∫ h, quadForm Q h ^ m ∂circularVectorLaw ι
      = ∫ h, G (star U *ᵥ h) ∂circularVectorLaw ι := by
        refine integral_congr_ae (ae_of_all _ fun h => ?_)
        simp only [G]
        rw [tco_quadForm_eq_sum hQ h]
    _ = ∫ g, G g ∂((circularVectorLaw ι).map (fun h => star U *ᵥ h)) :=
        (integral_map hmeas.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ g, G g ∂circularVectorLaw ι := by
        rw [tco_circularVectorLaw_map_unitary (star U) hU]

/-- **Colouring expansion.** `(Σ_i λ_i x_i)^m = Σ_{f : Fin m → ι} (Π_a λ_{f a}) Π_i x_i^{k_i(f)}`. -/
theorem wk_sum_pow_eq (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (lam x : ι → ℝ) :
    (∑ i, lam i * x i) ^ m =
      ∑ f : Fin m → ι, (∏ a, lam (f a)) * ∏ i, x i ^ wk_fib f i := by
  have h : (∑ i, lam i * x i) ^ m = ∏ _a : Fin m, ∑ i, lam i * x i := by
    simp [Finset.prod_const]
  rw [h, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_fiberwise_of_maps_to' (s := univ) (t := univ) (g := f)
    (fun _ _ => Finset.mem_univ _) x]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const]
  rfl

/-- **(a) The complex Wick formula** `E_h (h*Qh)^m = Σ_{π ∈ S_m} Π_{c cycle of π} Tr Q^{|c|}`. -/
theorem tcx_wickMoment : TcxWickMoment := by
  intro m ι _ _ Q hQ
  set lam := hQ.1.eigenvalues
  rw [wk_integral_quadForm_pow_eq m hQ.1]
  have hexp : ∀ g : ι → ℂ, (∑ i, lam i * Complex.normSq (g i)) ^ m =
      ∑ f : Fin m → ι, (∏ a, lam (f a)) * ∏ i, Complex.normSq (g i) ^ wk_fib f i :=
    fun g => wk_sum_pow_eq m lam _
  have hint : ∀ f : Fin m → ι, Integrable
      (fun g : ι → ℂ => (∏ a, lam (f a)) * ∏ i, Complex.normSq (g i) ^ wk_fib f i)
      (circularVectorLaw ι) := by
    intro f
    refine Integrable.const_mul (Integrable.of_integral_ne_zero ?_) _
    rw [wk_integral_prod_normSq_pow]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by positivity
  rw [integral_congr_ae (ae_of_all _ hexp), integral_finsetSum _ fun f _ => hint f]
  rw [Finset.sum_congr rfl fun f _ => by rw [integral_const_mul, wk_integral_prod_normSq_pow]]
  have htr : ∀ r, (Q ^ r).trace = ∑ i, ((lam i : ℝ) : ℂ) ^ r := fun r => ns_trace_pow Q hQ.1 r
  rw [show (fun r => (Q ^ r).trace) = (fun r => ∑ i, ((lam i : ℝ) : ℂ) ^ r) from funext htr,
    wk_sum_perm_parts_eq (fun i => ((lam i : ℝ) : ℂ))]
  push_cast
  rfl

end BlockBand.Endpoints
