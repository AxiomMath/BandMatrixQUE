module

public import BlockBand.SourceProcess.Stochastic.Angular.Interface
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Complex angular contract: local smooth eigenvector frames

Near a point `y` of simple spectrum, pick for each label `i` an index `κ_i` with
`(P_i)_{κ_i κ_i} > 0`. Then `w_i = P_i e_{κ_i} / √((P_i)_{κ_i κ_i})` (`frameCol`) is a unit
eigenvector with `w_i w_i^* = P_i`, smooth in `y` (`contDiffAt_frameArr`), on a neighbourhood
(`eventually_frame`). By phase invariance, a test sees the same value on `frameArr V κ` and on
the canonical array `arrZ V` (`phaseInv_frame`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix
open scoped Matrix ComplexConjugate ContDiff Matrix.Norms.Operator
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

/-- A matrix entry as a continuous real-linear map. -/
def entryCLM (a k : Fin N) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] theorem entryCLM_apply (a k : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) :
    entryCLM a k M = M a k := rfl

/-- The local frame column `P_i e_k / √((P_i)_{kk})`. -/
def frameCol (N : ℕ) (k i : Fin N) (y : Fin (N * N) → ℝ) : Fin N → ℂ :=
  fun a => (((Real.sqrt (proj N i y k k).re)⁻¹ : ℝ) : ℂ) * proj N i y a k

/-- The angular array of the local frame. -/
def frameArr (V : Matrix (Fin N) (Fin r) ℂ) (κ : Fin N → Fin N) (y : Fin (N * N) → ℝ) :
    AngularArray N r :=
  angularArray V fun i => frameCol N (κ i) i y

theorem proj_eq_canon {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    proj N i y = vecMulVec (canonEv N (vecHerm N y) i) (star (canonEv N (vecHerm N y) i)) :=
  isEigenSelection_canonEv N _ (vecHerm_isHermitian y) hy i

theorem canon_unit {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    star (canonEv N (vecHerm N y) i) ⬝ᵥ canonEv N (vecHerm N y) i = 1 :=
  eigenSel_unit (isEigenSelection_canonEv N) (vecHerm_isHermitian y) hy i

/-- `w w^* = P_i` for the local frame column. -/
theorem frameCol_proj {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) {i k : Fin N}
    (hk : 0 < (proj N i y k k).re) :
    vecMulVec (frameCol N k i y) (star (frameCol N k i y)) = proj N i y := by
  set u := canonEv N (vecHerm N y) i
  have hP := proj_eq_canon hy i
  have hkk : proj N i y k k = ((Complex.normSq (u k) : ℝ) : ℂ) := by
    rw [hP, vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj]
  have hre : (proj N i y k k).re = Complex.normSq (u k) := by rw [hkk, Complex.ofReal_re]
  rw [hre] at hk
  set ρ := Complex.normSq (u k)
  have hs : (((Real.sqrt ρ)⁻¹ : ℝ) : ℂ) * (((Real.sqrt ρ)⁻¹ : ℝ) : ℂ) * (ρ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hk.le,
      inv_mul_cancel₀ hk.ne']; simp
  have hρ : u k * conj (u k) = (ρ : ℂ) := Complex.mul_conj _
  ext a b
  rw [vecMulVec_apply, Pi.star_apply]
  unfold frameCol
  rw [hre, hP]
  simp only [vecMulVec_apply, Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal,
    Complex.conj_conj]
  linear_combination (u a * conj (u b)) * hs +
    ((((Real.sqrt ρ)⁻¹ : ℝ) : ℂ) * (((Real.sqrt ρ)⁻¹ : ℝ) : ℂ) * u a * conj (u b)) * hρ

theorem frameCol_unit {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) {i k : Fin N}
    (hk : 0 < (proj N i y k k).re) : star (frameCol N k i y) ⬝ᵥ frameCol N k i y = 1 := by
  have h := trace_proj (vecHerm_isHermitian y) hy i
  change trace (proj N i y) = 1 at h
  rw [← frameCol_proj hy hk, trace_vecMulVec, dotProduct_comm] at h
  exact h

/-- **Phase invariance sees the local frame as the canonical array.** -/
theorem phaseInv_frame {g : AngularArray N r → ℝ} (hg : IsPhaseInvariant g)
    (V : Matrix (Fin N) (Fin r) ℂ) {κ : Fin N → Fin N} {y : Fin (N * N) → ℝ}
    (hy : y ∈ simpleSet N) (hκ : ∀ i, 0 < (proj N i y (κ i) (κ i)).re) :
    g (arrZ V y) = g (frameArr V κ y) := by
  have key := fun i => eq_smul_of_vecMulVec_eq (frameCol_unit hy (hκ i)) (canon_unit hy i)
    ((frameCol_proj hy (hκ i)).trans (proj_eq_canon hy i))
  have e : arrZ V y = fun i a => (star (frameCol N (κ i) i y) ⬝ᵥ canonEv N (vecHerm N y) i) *
      frameArr V κ y i a := by
    rw [frameArr, ← angularArray_smul, arrZ]
    congr 1; funext i; exact (key i).1
  rw [e, hg _ fun i => (key i).2]

/-- The same for the generator, with any couplings. -/
theorem gen_frame {f : AngularArray N r → ℝ} (hf : IsPhaseInvariant f) (lam : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) {κ : Fin N → Fin N} {y : Fin (N * N) → ℝ}
    (hy : y ∈ simpleSet N) (hκ : ∀ i, 0 < (proj N i y (κ i) (κ i)).re) :
    complexAngularGenerator N r lam f (arrZ V y) =
      complexAngularGenerator N r lam f (frameArr V κ y) := by
  have key := fun i => eq_smul_of_vecMulVec_eq (frameCol_unit hy (hκ i)) (canon_unit hy i)
    ((frameCol_proj hy (hκ i)).trans (proj_eq_canon hy i))
  have e : arrZ V y = fun i a => (star (frameCol N (κ i) i y) ⬝ᵥ canonEv N (vecHerm N y) i) *
      frameArr V κ y i a := by
    rw [frameArr, ← angularArray_smul, arrZ]
    congr 1; funext i; exact (key i).1
  rw [e, complexAngularGenerator_phase hf lam _ fun i => (key i).2]

/-- **Smoothness of the local frame.** -/
theorem contDiffAt_frameArr {n : WithTop ℕ∞} (V : Matrix (Fin N) (Fin r) ℂ)
    {κ : Fin N → Fin N} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (hκ : ∀ i, 0 < (proj N i y (κ i) (κ i)).re) : ContDiffAt ℝ n (frameArr V κ) y := by
  have hent : ∀ i a k, ContDiffAt ℝ n (fun y => proj N i y a k) y := fun i a k =>
    (entryCLM a k).contDiff.contDiffAt.comp y (contDiffAt_proj hy i)
  have hcol : ∀ i b, ContDiffAt ℝ n (fun y => frameCol N (κ i) i y b) y := by
    intro i b
    have hre : ContDiffAt ℝ n (fun y => (proj N i y (κ i) (κ i)).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (hent i (κ i) (κ i))
    have hsq : ContDiffAt ℝ n (fun y => Real.sqrt (proj N i y (κ i) (κ i)).re) y :=
      (Real.contDiffAt_sqrt (hκ i).ne').comp y hre
    have hinv : ContDiffAt ℝ n (fun y => (Real.sqrt (proj N i y (κ i) (κ i)).re)⁻¹) y :=
      hsq.inv (Real.sqrt_pos.2 (hκ i)).ne'
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y hinv).mul (hent i b (κ i))
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun a => ?_
  simp only [frameArr, angularArray, Matrix.mulVec, dotProduct]
  exact ContDiffAt.sum fun b _ => contDiffAt_const.mul (hcol i b)

/-- **Local frames exist near every point of simple spectrum.** -/
theorem eventually_frame {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    ∃ κ : Fin N → Fin N, ∀ᶠ y' in 𝓝 y, y' ∈ simpleSet N ∧
      ∀ i, 0 < (proj N i y' (κ i) (κ i)).re := by
  have hex : ∀ i, ∃ k, 0 < (proj N i y k k).re := by
    intro i
    by_contra hne
    push Not at hne
    have h1 := norm_sq_of_dot (canon_unit hy i)
    have h0 : ∀ k, ‖canonEv N (vecHerm N y) i k‖ ^ 2 = 0 := by
      intro k
      have hkk : (proj N i y k k).re = ‖canonEv N (vecHerm N y) i k‖ ^ 2 := by
        rw [proj_eq_canon hy i, vecMulVec_apply, Pi.star_apply, Complex.star_def,
          Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      exact le_antisymm (hkk ▸ hne k) (sq_nonneg _)
    simp [h0] at h1
  choose κ hκ using hex
  refine ⟨κ, (eventually_simpleSet hy).and (eventually_all.2 fun i => ?_)⟩
  have hc : ContinuousAt (fun y => (proj N i y (κ i) (κ i)).re) y :=
    (Complex.reCLM.contDiff.contDiffAt.comp y
      ((entryCLM (κ i) (κ i)).contDiff.contDiffAt.comp y
        (contDiffAt_proj (n := 0) hy i))).continuousAt
  exact hc.eventually (lt_mem_nhds (hκ i))

end BlockBand.SourceProcess.Stochastic.ComplexAngular
