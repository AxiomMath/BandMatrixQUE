module

public import Mathlib
public import BlockBand.External.Johansson.SourceStatement
public import BlockBand.QUE.Invariance.Frobenius

/-!
# Unitary invariance of the Johansson Gaussian Hermitian law

Unitary invariance of `G_N`, which lets one take the external source `F` diagonal. Law: the
Johansson coordinate law
`Johansson.coordinateMeasure N S` (independent upper coordinates: diagonal `N(0,S)`, strict-upper
real and imaginary parts `N(0,S/2)`), pushed to raw complex matrices by
`Johansson.gaussianMatrixRaw`; this raw law is `gueRawLaw N S`. Domain: every `N` (including
`N = 0`) and every `S ≥ 0`; no bound on the source, no asymptotics.

## Main results

* `integral_exp_re_trace_gueRawLaw`: the Hermitian trace characteristic function
  `E exp(i Re Tr(K G)) = exp(-S ‖K‖_F² / 2)` for every Hermitian `K`;
* `measure_eq_of_hermitianTrace`: finite measures on raw matrices supported on Hermitian
  matrices are determined by these Hermitian trace characteristic functions (Mathlib's
  `Measure.ext_of_charFunDual` on `Fin N → Fin N → ℂ`);
* `gueRawLaw_map_conj`: invariance under `G ↦ U G U*` for every unitary `U`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory ProbabilityTheory Matrix Finset
open BlockBand.External
open scoped NNReal ENNReal

/-- The raw-matrix Gaussian law of the Johansson sample `G` (total complex entry variance `S`):
the pushforward of `Johansson.coordinateMeasure N S` by `Johansson.gaussianMatrixRaw`. -/
def gueRawLaw (N : ℕ) (S : ℝ≥0) : Measure (Matrix (Fin N) (Fin N) ℂ) :=
  (Johansson.coordinateMeasure N S).map Johansson.gaussianMatrixRaw

/-- Borel measurability of the raw Johansson reconstruction (every `N`). -/
theorem measurable_gaussianMatrixRaw (N : ℕ) :
    Measurable (@Johansson.gaussianMatrixRaw N) :=
  measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix

/-- `gueRawLaw N S` is a probability measure (every `N`, `S`). -/
instance gueRawLaw_isProbability (N : ℕ) (S : ℝ≥0) : IsProbabilityMeasure (gueRawLaw N S) := by
  have := Johansson.coordinateMeasure_probability N S
  unfold gueRawLaw
  infer_instance

/-- Unitary conjugation `G ↦ U G U*` on raw matrices. -/
def conjMatrix {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) (G : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (U : Matrix (Fin N) (Fin N) ℂ) * G * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ

/-- Unitary conjugation is continuous on raw matrices. -/
theorem continuous_conjMatrix {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Continuous (conjMatrix U) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/-- The Hermitian matrices form a (closed, hence) Borel set. -/
theorem measurableSet_isHermitian (N : ℕ) :
    MeasurableSet {G : Matrix (Fin N) (Fin N) ℂ | G.IsHermitian} :=
  (isClosed_eq (by fun_prop : Continuous (fun G : Matrix (Fin N) (Fin N) ℂ => G.conjTranspose))
    continuous_id).measurableSet

/-- The trace test `G ↦ exp(i Re Tr(K G))` is continuous. -/
theorem continuous_traceTest {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) :
    Continuous (fun G : Matrix (Fin N) (Fin N) ℂ =>
      Complex.exp (Complex.I * ((Matrix.trace (K * G)).re : ℂ))) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace)))

/-- A symmetric real array summed over all ordered pairs equals the diagonal plus twice the
strict upper triangle, indexed by Johansson's upper pairs. -/
theorem sum_sum_eq_sum_upperPair {N : ℕ} (g : Fin N → Fin N → ℝ)
    (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, g i j = ∑ q : Johansson.UpperPair N,
      (if q.1.1 = q.1.2 then g q.1.1 q.1.2 else 2 * g q.1.1 q.1.2) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin N × Fin N => p.1 ≤ p.2))
    (by simp) (fun p : Fin N × Fin N => if p.1 = p.2 then g p.1 p.2 else 2 * g p.1 p.2)]
  rw [← Fintype.sum_prod_type' g,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin N × Fin N => p.1 ≤ p.2)]
  have hswap : ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => ¬ p.1 ≤ p.2), g p.1 p.2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), g p.1 p.2 := by
    apply Finset.sum_nbij' Prod.swap Prod.swap
    · intro p hp
      simpa using hp
    · intro p hp
      simpa using hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; exact hg _ _
  have hsplit : ∀ p : Fin N × Fin N, (if p.1 = p.2 then g p.1 p.2 else 2 * g p.1 p.2) =
      g p.1 p.2 + (if p.1 = p.2 then 0 else g p.1 p.2) := by
    intro p; split_ifs <;> ring
  rw [hswap, Finset.sum_congr rfl (fun p _ => hsplit p), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h.le, h.ne⟩, fun h => lt_of_le_of_ne h.1 h.2⟩

/-- Linear coordinate test of the upper coordinate `q` attached to a test matrix `K`. -/
def upperTest {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (q : Johansson.UpperPair N)
    (z : ℝ × ℝ) : ℝ :=
  if q.1.1 = q.1.2 then (K q.1.1 q.1.1).re * z.1
  else 2 * ((K q.1.2 q.1.1).re * z.1 - (K q.1.2 q.1.1).im * z.2)

/-- `Re Tr(K G)` of a Johansson sample `G` is the sum of the upper coordinate tests. -/
theorem re_trace_mul_gaussianMatrixRaw {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (hK : K.IsHermitian) (z : Johansson.UpperPair N → ℝ × ℝ) :
    (Matrix.trace (K * Johansson.gaussianMatrixRaw z)).re = ∑ q, upperTest K q (z q) := by
  set G := Johansson.gaussianMatrixRaw z with hGdef
  have hG : G.IsHermitian := Johansson.gaussianMatrixRaw_isHermitian z
  have htr : (Matrix.trace (K * G)).re = ∑ i, ∑ j, (K j i * G i j).re := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag_apply, Complex.re_sum]
    exact Finset.sum_comm
  have hsym : ∀ i j, (K j i * G i j).re = (K i j * G j i).re := by
    intro i j
    rw [← hK.apply i j, ← hG.apply i j]
    simp [Complex.mul_re]
  rw [htr, sum_sum_eq_sum_upperPair _ hsym]
  apply Finset.sum_congr rfl
  rintro ⟨⟨i, j⟩, hij⟩ _
  by_cases h : i = j
  · subst h
    simp [upperTest, hGdef, Johansson.gaussianMatrixRaw, Complex.mul_re]
  · simp [upperTest, h, hGdef, Johansson.gaussianMatrixRaw, hij, Johansson.complexPair,
      Complex.mul_re]

/-- Per-coordinate variance weight of a test matrix (diagonal `|K_ii|²`, off-diagonal
`2|K_ij|²`). -/
def upperWeight {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (q : Johansson.UpperPair N) : ℝ :=
  if q.1.1 = q.1.2 then Complex.normSq (K q.1.1 q.1.2) else 2 * Complex.normSq (K q.1.1 q.1.2)

/-- Squared Frobenius norm of a Hermitian test as a sum over upper coordinates. -/
theorem frobeniusSq_eq_sum_upperWeight {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (hK : K.IsHermitian) :
    QUE.Invariance.frobeniusSq K = ∑ q, upperWeight K q := by
  unfold QUE.Invariance.frobeniusSq upperWeight
  refine sum_sum_eq_sum_upperPair _ (fun i j => ?_)
  rw [← hK.apply i j, Complex.star_def, Complex.normSq_conj]

/-- The characteristic function of one upper coordinate. -/
theorem integral_upperEntry {N : ℕ} (S : ℝ≥0) (K : Matrix (Fin N) (Fin N) ℂ)
    (hK : K.IsHermitian) (q : Johansson.UpperPair N) :
    ∫ x, Complex.exp (Complex.I * (upperTest K q x : ℂ)) ∂Johansson.upperEntryMeasure S q =
      Complex.exp (-(((S : ℝ) * upperWeight K q : ℝ) : ℂ) / 2) := by
  rcases q with ⟨⟨i, j⟩, hij⟩
  by_cases h : i = j
  · subst h
    have hre : (K i i).im = 0 := by
      have := congrArg Complex.im (hK.apply i i)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    simp only [Johansson.upperEntryMeasure, ite_true, upperTest, upperWeight]
    rw [integral_map (by fun_prop) (by fun_prop)]
    have hc := charFun_gaussianReal (μ := 0) (v := S) ((K i i).re)
    rw [charFun_apply_real] at hc
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub] at hc
    have h1 : ∀ x : ℝ, Complex.exp (Complex.I * (((K i i).re * (x, (0 : ℝ)).1 : ℝ) : ℂ)) =
        Complex.exp (((K i i).re : ℂ) * (x : ℂ) * Complex.I) := by
      intro x; congr 1; push_cast; ring
    simp_rw [h1, hc, Complex.normSq_apply, hre]
    congr 1
    push_cast
    ring
  · simp only [Johansson.upperEntryMeasure, h, ite_false, upperTest, upperWeight]
    set a := (K j i).re
    set b := (K j i).im
    have h1 : ∀ p : ℝ × ℝ, Complex.exp (Complex.I * ((2 * (a * p.1 - b * p.2) : ℝ) : ℂ)) =
        Complex.exp (((2 * a : ℝ) : ℂ) * (p.1 : ℂ) * Complex.I) *
          Complex.exp (((-(2 * b) : ℝ) : ℂ) * (p.2 : ℂ) * Complex.I) := by
      intro p; rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [h1]
    rw [integral_prod_mul (fun x : ℝ => Complex.exp (((2 * a : ℝ) : ℂ) * (x : ℂ) * Complex.I))
      (fun y : ℝ => Complex.exp (((-(2 * b) : ℝ) : ℂ) * (y : ℂ) * Complex.I))]
    rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
      ← Complex.exp_add]
    have hnorm : Complex.normSq (K i j) = a ^ 2 + b ^ 2 := by
      rw [← hK.apply i j, Complex.star_def, Complex.normSq_conj, Complex.normSq_apply]; ring
    rw [hnorm]
    congr 1
    push_cast
    ring

/-- Hermitian trace characteristic function of the raw Johansson Gaussian law:
`∫ exp(i Re Tr(K G)) d(gueRawLaw N S)(G) = exp(-S ‖K‖_F²/2)` for Hermitian `K`. -/
theorem integral_exp_re_trace_gueRawLaw (N : ℕ) (S : ℝ≥0) (K : Matrix (Fin N) (Fin N) ℂ)
    (hK : K.IsHermitian) :
    ∫ G, Complex.exp (Complex.I * ((Matrix.trace (K * G)).re : ℂ)) ∂gueRawLaw N S =
      Complex.exp (-(((S : ℝ) * QUE.Invariance.frobeniusSq K : ℝ) : ℂ) / 2) := by
  have hint : ∀ q, IsProbabilityMeasure (Johansson.upperEntryMeasure S q) :=
    Johansson.upperEntryMeasure_probability (N := N) S
  rw [gueRawLaw, integral_map (measurable_gaussianMatrixRaw N).aemeasurable
    (continuous_traceTest K).aestronglyMeasurable]
  simp_rw [re_trace_mul_gaussianMatrixRaw K hK]
  have hprod : ∀ z : Johansson.UpperPair N → ℝ × ℝ,
      Complex.exp (Complex.I * ((∑ q, upperTest K q (z q) : ℝ) : ℂ)) =
        ∏ q, Complex.exp (Complex.I * (upperTest K q (z q) : ℂ)) := by
    intro z
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp_rw [hprod]
  rw [Johansson.coordinateMeasure,
    integral_fintype_prod_eq_prod (fun q x => Complex.exp (Complex.I * (upperTest K q x : ℂ)))]
  simp_rw [integral_upperEntry S K hK]
  rw [← Complex.exp_sum, frobeniusSq_eq_sum_upperWeight K hK]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]

/-- Every real-linear functional on raw matrices is, on Hermitian matrices, a Hermitian trace
test `Re Tr(K G)`. -/
theorem exists_hermitian_trace_rep {N : ℕ}
    (L : StrongDual ℝ (Fin N → Fin N → ℂ)) :
    ∃ K : Matrix (Fin N) (Fin N) ℂ, K.IsHermitian ∧
      ∀ v : Fin N → Fin N → ℂ, (Matrix.of v).IsHermitian →
        L v = (Matrix.trace (K * Matrix.of v)).re := by
  classical
  let e : Fin N → Fin N → (Fin N → Fin N → ℂ) := fun i j => Pi.single i (Pi.single j 1)
  let e' : Fin N → Fin N → (Fin N → Fin N → ℂ) := fun i j => Pi.single i (Pi.single j Complex.I)
  let c : Fin N → Fin N → ℂ := fun i j => (L (e i j) : ℂ) - Complex.I * (L (e' i j) : ℂ)
  -- `B = cᵀ`, `K = (B + Bᴴ)/2`
  let K : Matrix (Fin N) (Fin N) ℂ := fun a b => (c b a + star (c a b)) / 2
  have hK : K.IsHermitian := by
    refine Matrix.IsHermitian.ext (fun a b => ?_)
    simp [K, add_comm]
  have hdecomp : ∀ G : Fin N → Fin N → ℂ,
      G = ∑ i, ∑ j, ((G i j).re • e i j + (G i j).im • e' i j) := by
    intro G
    funext a b
    simp only [e, e', Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single a (by intro i _ hi; simp [hi]) (by simp)]
    rw [Finset.sum_eq_single b (by intro j _ hj; simp [hj]) (by simp)]
    apply Complex.ext <;> simp
  have hL : ∀ G : Fin N → Fin N → ℂ, L G = ∑ i, ∑ j, (c i j * G i j).re := by
    intro G
    conv_lhs => rw [hdecomp G]
    simp only [map_sum, map_add, map_smul, smul_eq_mul, c, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.sub_im]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  refine ⟨K, hK, fun G hG => ?_⟩
  rw [hL]
  have htr : (Matrix.trace (K * Matrix.of G)).re = ∑ a, ∑ b, (K a b * G b a).re := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.re_sum]
  rw [htr]
  have hterm : ∀ a b, (K a b * G b a).re =
      ((c b a * G b a).re + (c a b * G a b).re) / 2 := by
    intro a b
    have hGab : G b a = star (G a b) := by
      have := hG.apply a b
      simp only [Matrix.of_apply] at this
      rw [← this, star_star]
    simp only [K, hGab]
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    ring
  simp_rw [hterm, add_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => (c b a * G b a).re / 2)]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- Finite measures on raw matrices, supported on Hermitian matrices, with the same Hermitian
trace characteristic functions are equal. -/
theorem measure_eq_of_hermitianTrace {N : ℕ} {μ ν : Measure (Matrix (Fin N) (Fin N) ℂ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ G ∂μ, G.IsHermitian) (hν : ∀ᵐ G ∂ν, G.IsHermitian)
    (h : ∀ K : Matrix (Fin N) (Fin N) ℂ, K.IsHermitian →
      ∫ G, Complex.exp (Complex.I * ((Matrix.trace (K * G)).re : ℂ)) ∂μ =
        ∫ G, Complex.exp (Complex.I * ((Matrix.trace (K * G)).re : ℂ)) ∂ν) : μ = ν := by
  let μ' : Measure (Fin N → Fin N → ℂ) := μ
  let ν' : Measure (Fin N → Fin N → ℂ) := ν
  have : IsFiniteMeasure μ' := ‹IsFiniteMeasure μ›
  have : IsFiniteMeasure ν' := ‹IsFiniteMeasure ν›
  change μ' = ν'
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply]
  obtain ⟨K, hK, hrep⟩ := exists_hermitian_trace_rep L
  have hμ' : (fun v => Complex.exp ((L v : ℂ) * Complex.I)) =ᵐ[μ']
      (fun v => Complex.exp (Complex.I * ((Matrix.trace (K * Matrix.of v)).re : ℂ))) := by
    filter_upwards [hμ] with G hG
    rw [hrep G hG, mul_comm]
  have hν' : (fun v => Complex.exp ((L v : ℂ) * Complex.I)) =ᵐ[ν']
      (fun v => Complex.exp (Complex.I * ((Matrix.trace (K * Matrix.of v)).re : ℂ))) := by
    filter_upwards [hν] with G hG
    rw [hrep G hG, mul_comm]
  rw [integral_congr_ae hμ', integral_congr_ae hν']
  exact h K hK

/-- Unitary invariance of the raw Johansson Gaussian law: for every `N`, `S` and unitary `U`,
the pushforward of `gueRawLaw N S` by `G ↦ U G U*` is `gueRawLaw N S`. -/
theorem gueRawLaw_map_conj (N : ℕ) (S : ℝ≥0) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    (gueRawLaw N S).map (conjMatrix U) = gueRawLaw N S := by
  have hmeas := (continuous_conjMatrix U).measurable
  have hsupp : ∀ᵐ G ∂gueRawLaw N S, G.IsHermitian := by
    rw [gueRawLaw, ae_map_iff (measurable_gaussianMatrixRaw N).aemeasurable
      (measurableSet_isHermitian N)]
    exact Filter.Eventually.of_forall Johansson.gaussianMatrixRaw_isHermitian
  apply measure_eq_of_hermitianTrace
  · rw [ae_map_iff hmeas.aemeasurable (measurableSet_isHermitian N)]
    filter_upwards [hsupp] with G hG
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hG
  · exact hsupp
  · intro K hK
    rw [integral_map hmeas.aemeasurable (continuous_traceTest K).aestronglyMeasurable]
    let V : Matrix (Fin N) (Fin N) ℂ := (U : Matrix (Fin N) (Fin N) ℂ)
    have htr : ∀ G : Matrix (Fin N) (Fin N) ℂ,
        Matrix.trace (K * conjMatrix U G) = Matrix.trace ((Vᴴ * K * V) * G) := by
      intro G
      change Matrix.trace (K * (V * G * Vᴴ)) = _
      rw [show K * (V * G * Vᴴ) = (K * V * G) * Vᴴ by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    simp_rw [htr]
    have hK' : (Vᴴ * K * V).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul _ hK
    rw [integral_exp_re_trace_gueRawLaw N S _ hK', integral_exp_re_trace_gueRawLaw N S _ hK]
    have hstar : ((star U : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Vᴴ := rfl
    rw [← hstar, QUE.Invariance.frobeniusSq_unitary_both]

end BlockBand.GaussianBulk
