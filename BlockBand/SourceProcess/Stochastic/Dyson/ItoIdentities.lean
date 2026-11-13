module

public import BlockBand.SourceProcess.Stochastic.Dyson.SecondDeriv
public import BlockBand.SourceProcess.Stochastic.Dyson.Partials

/-!
# Dyson Brownian motion: the Itô characteristics of `(λ, X)` in GUE coordinates

For `ψ_k(y) = dysonState N q (vecHerm N y) k`, at every `y ∈ simpleSet N` (simple spectrum):
* `contDiffAt_stateFn`: `ψ_k` is `C^n`;
* `itoDrift_dysonState`: the contract's `itoDrift` of `(t, y) ↦ ψ_k(y)` with zero drift and the
  GUE covariance `gueCovVec N = I/N` equals `dysonStateDrift`;
* `gradPair_dysonState`: `(1/N) ∑_a ∂_a ψ_k ∂_a ψ_l = dysonStateCov k l`, hence
  `itoBracket_dysonState`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix Filter Topology
open scoped Matrix ContDiff Matrix.Norms.Operator NNReal ComplexConjugate
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

theorem vecHerm_single (a : Fin (N * N)) :
    vecHerm N (Pi.single a 1) = hermBasis (finProdFinEquiv.symm a) := by
  unfold vecHerm hermOfCoord
  rw [Finset.sum_eq_single (finProdFinEquiv.symm a)]
  · simp only [Equiv.apply_symm_apply, Pi.single_eq_same, Complex.ofReal_one, one_smul]
  · intro x _ hx
    have : finProdFinEquiv x ≠ a := fun h => hx (by rw [← h, Equiv.symm_apply_apply])
    simp [this]
  · simp

theorem sum_coord {M : Type*} [AddCommMonoid M] (f : Matrix (Fin N) (Fin N) ℂ → M) :
    ∑ a : Fin (N * N), f (vecHerm N (Pi.single a 1)) = ∑ x, f (hermBasis x) := by
  simp_rw [vecHerm_single]
  exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)

theorem gueCovVec_eq : gueCovVec N = Matrix.of fun a b => if a = b then (1 / (N : ℝ)) else 0 := by
  ext a b; rw [gueCovVec_apply]; rfl

theorem trace_proj_mul_hermBasis_re {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    (x : Fin N × Fin N) :
    (((trace (proj N i y * hermBasis x)).re : ℝ) : ℂ) = trace (proj N i y * hermBasis x) :=
  trace_mul_re_eq (proj_isHermitian (vecHerm_isHermitian y) hy i) (hermBasis_isHermitian x)

theorem qf_conj_of_isHermitian (q : Fin N → ℂ) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.IsHermitian) : conj (qf q M) = qf q M := by
  rw [qf_eq_trace]
  change star (trace _) = _
  rw [← trace_conjTranspose, conjTranspose_mul, hM.eq, trace_mul_comm,
    show (vecMulVec q (star q))ᴴ = vecMulVec q (star q) from ?_]
  ext a b; simp [vecMulVec_apply, mul_comm]

theorem dProjAt_isHermitian {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N)
    {E : Matrix (Fin N) (Fin N) ℂ} (hE : E.IsHermitian) : (dProjAt N y i E).IsHermitian := by
  have hP : ∀ j, (proj N j y).IsHermitian := fun j =>
    proj_isHermitian (vecHerm_isHermitian y) hy j
  unfold dProjAt SpecFamily.dProj IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_mul, conjTranspose_mul, (hP i).eq, (hP j).eq, hE.eq, add_comm]
  congr 1
  · simp [Complex.conj_ofReal]
  · simp only [Matrix.mul_assoc]

theorem re_mul_re_of_real {a b : ℂ} (ha : ((a.re : ℝ) : ℂ) = a) (hb : ((b.re : ℝ) : ℂ) = b) :
    a.re * b.re = (a * b).re := by
  have ha' : a.im = 0 := by rw [← ha, Complex.ofReal_im]
  have hb' : b.im = 0 := by rw [← hb, Complex.ofReal_im]
  rw [Complex.mul_re, ha', hb', mul_zero, sub_zero]

theorem qf_real_of_isHermitian (q : Fin N → ℂ) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.IsHermitian) : (((qf q M).re : ℝ) : ℂ) = qf q M :=
  Complex.conj_eq_iff_re.mp (qf_conj_of_isHermitian q hM)

theorem ne_zero_of_fin (i : Fin N) : (N : ℝ) ≠ 0 := by
  have : 0 < N := Fin.pos i
  exact_mod_cast this.ne'

/-- Coordinate Laplacian of an eigenvalue: `∑_a ∂_a² λ_i = 2 ∑_{j ≠ i} (λ_i - λ_j)⁻¹`. -/
theorem lapl_lam {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    ∑ a, fderiv ℝ (fderiv ℝ (lam N i)) y (Pi.single a 1) (Pi.single a 1) =
      2 * ∑ j ∈ Finset.univ.erase i, (lam N i y - lam N j y)⁻¹ := by
  simp_rw [fderiv2_lam hy i]
  rw [sum_coord (fun E => (trace (dProjAt N y i E * E)).re), ← Complex.re_sum]
  unfold dProjAt
  rw [(specFamily_coord hy).sum_trace_dProj_mul i]
  rw [show (2 : ℂ) * ∑ j ∈ Finset.univ.erase i, (((lam N i y : ℝ) : ℂ) - ((lam N j y : ℝ) : ℂ))⁻¹ =
    ((2 * ∑ j ∈ Finset.univ.erase i, (lam N i y - lam N j y)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

/-- Coordinate Laplacian of an overlap:
`∑_a ∂_a² X_i = N ∑_{j ≠ i} 2 (λ_i - λ_j)⁻² (z_j - z_i)`, `z = Re q* P q`. -/
theorem lapl_ovl {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ) (i : Fin N) :
    ∑ a, fderiv ℝ (fderiv ℝ (ovl N q i)) y (Pi.single a 1) (Pi.single a 1) =
      (N : ℝ) * ∑ j ∈ Finset.univ.erase i, 2 * ((lam N i y - lam N j y)⁻¹) ^ 2 *
        ((qf q (proj N j y)).re - (qf q (proj N i y)).re) := by
  simp_rw [fderiv2_ovl hy q i]
  rw [sum_coord (fun E => overlapForm N q (SpecFamily.d2Proj (fun j => proj N j y)
    (fun j => ((lam N j y : ℝ) : ℂ)) i E)), ← map_sum, (specFamily_coord hy).sum_d2Proj i,
    overlapForm_apply, qf_sum, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qf_smul, show (2 : ℂ) * ((((lam N i y : ℝ) : ℂ) - ((lam N j y : ℝ) : ℂ))⁻¹) ^ 2 =
    ((2 * ((lam N i y - lam N j y)⁻¹) ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
    show proj N j y - proj N i y = proj N j y + (-1 : ℂ) • proj N i y by
      rw [neg_one_smul, sub_eq_add_neg], qf_add, qf_smul]
  simp only [Complex.add_re, neg_one_mul, Complex.neg_re]
  ring

/-- A component of the joint state in coordinates. -/
def stateFn (N : ℕ) (q : Fin N → ℂ) (k : Fin (N + N)) (y : Fin (N * N) → ℝ) : ℝ :=
  dysonState N q (vecHerm N y) k

theorem stateFn_inl (q : Fin N → ℂ) (i : Fin N) :
    stateFn N q (finSumFinEquiv (Sum.inl i)) = lam N i := by
  funext y; exact dysonState_inl q _ i

theorem stateFn_inr (q : Fin N → ℂ) (i : Fin N) :
    stateFn N q (finSumFinEquiv (Sum.inr i)) = ovl N q i := by
  funext y; exact dysonState_inr q _ i

theorem contDiffAt_stateFn {n : WithTop ℕ∞} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (q : Fin N → ℂ) (k : Fin (N + N)) : ContDiffAt ℝ n (stateFn N q k) y := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | i
  · rw [stateFn_inl]; exact contDiffAt_eigenvalue hy i
  · rw [stateFn_inr]; exact contDiffAt_ovl hy q i

theorem state_inl (q : Fin N → ℂ) (y : Fin (N * N) → ℝ) :
    (fun a => dysonState N q (vecHerm N y) (finSumFinEquiv (Sum.inl a))) = fun a => lam N a y := by
  funext a; exact dysonState_inl q _ a

theorem state_inr (q : Fin N → ℂ) (y : Fin (N * N) → ℝ) :
    (fun a => dysonState N q (vecHerm N y) (finSumFinEquiv (Sum.inr a))) =
      fun a => (N : ℝ) * (qf q (proj N a y)).re := by
  funext a; exact dysonState_inr q _ a

/-- **Itô drift of the joint state** (deterministic half of (b2)): with zero drift and the GUE
covariance, the Itô drift of `ψ_k` equals `dysonStateDrift`. -/
theorem itoDrift_dysonState {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ)
    (k : Fin (N + N)) (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin (N * N) → ℝ) => stateFn N q k p.2) y t 0 (gueCovVec N) =
      dysonStateDrift N (dysonState N q (vecHerm N y)) k := by
  rw [gueCovVec_eq, itoDrift_comp_snd (contDiffAt_stateFn hy q k)]
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with i | i
  · rw [stateFn_inl, lapl_lam hy i, dysonStateDrift_inl, state_inl, dysonDrift]
    simp only [one_div]
    ring
  · have hN := ne_zero_of_fin i
    rw [stateFn_inr, lapl_ovl hy q i, dysonStateDrift_inr, state_inl, Finset.mul_sum,
      Finset.mul_sum]
    simp only [dysonState_inr, dysonOverlap, qf, proj]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold dysonCoupling
    field_simp

theorem fderiv_stateFn_inl {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ)
    (i : Fin N) (a : Fin (N * N)) :
    fderiv ℝ (stateFn N q (finSumFinEquiv (Sum.inl i))) y (Pi.single a 1) =
      (trace (proj N i y * hermBasis (finProdFinEquiv.symm a))).re := by
  rw [stateFn_inl, fderiv_lam_eq hy i, vecHerm_single]

theorem fderiv_stateFn_inr {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ)
    (i : Fin N) (a : Fin (N * N)) :
    fderiv ℝ (stateFn N q (finSumFinEquiv (Sum.inr i))) y (Pi.single a 1) =
      (N : ℝ) * (qf q (dProjAt N y i (hermBasis (finProdFinEquiv.symm a)))).re := by
  rw [stateFn_inr, fderiv_ovl_eq hy q i, vecHerm_single, overlapForm_apply]

theorem sum_coord' {M : Type*} [AddCommMonoid M] (f : Fin N × Fin N → M) :
    ∑ a : Fin (N * N), f (finProdFinEquiv.symm a) = ∑ x, f x :=
  Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)

theorem sum_trace_mul_qf_dProj {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ)
    (i k : Fin N) :
    ∑ x, trace (proj N k y * hermBasis x) * qf q (dProjAt N y i (hermBasis x)) = 0 := by
  simp_rw [← qf_smul]
  rw [← qf_sum]
  unfold dProjAt
  rw [(specFamily_coord hy).sum_trace_smul_dProj i k]
  simp [qf]

theorem dysonState_inr' (q : Fin N → ℂ) (y : Fin (N * N) → ℝ) (m : Fin N) :
    dysonState N q (vecHerm N y) (finSumFinEquiv (Sum.inr m)) = (N : ℝ) * (qf q (proj N m y)).re :=
  dysonState_inr q _ m

/-- **Itô brackets of the joint state** (deterministic half of (b2)):
`(1/N) ∑_a ∂_a ψ_k ∂_a ψ_l = dysonStateCov k l`. -/
theorem gradPair_dysonState {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ)
    (k l : Fin (N + N)) :
    (1 / (N : ℝ)) * ∑ a, fderiv ℝ (stateFn N q k) y (Pi.single a 1) *
        fderiv ℝ (stateFn N q l) y (Pi.single a 1) =
      dysonStateCov N (dysonState N q (vecHerm N y)) k l := by
  have hP : ∀ j, (proj N j y).IsHermitian := fun j =>
    proj_isHermitian (vecHerm_isHermitian y) hy j
  have htr : ∀ j x, (((trace (proj N j y * hermBasis x)).re : ℝ) : ℂ) =
      trace (proj N j y * hermBasis x) := fun j x => trace_proj_mul_hermBasis_re hy j x
  have hqf : ∀ j x, (((qf q (dProjAt N y j (hermBasis x))).re : ℝ) : ℂ) =
      qf q (dProjAt N y j (hermBasis x)) := fun j x =>
    qf_real_of_isHermitian q (dProjAt_isHermitian hy j (hermBasis_isHermitian x))
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective l
  rcases k with i | i <;> rcases l with j | j
  · simp_rw [fderiv_stateFn_inl hy]
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [ dysonStateCov_inl_inl]
    simp_rw [re_mul_re_of_real (htr i _) (htr j _)]
    rw [← Complex.re_sum, sum_trace_mul_trace_mul, (specFamily_coord hy).trace_proj_mul_proj]
    split_ifs <;> simp
  · simp_rw [fderiv_stateFn_inl hy, fderiv_stateFn_inr hy]
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [ dysonStateCov_inl_inr]
    simp_rw [mul_left_comm _ (N : ℝ), re_mul_re_of_real (htr i _) (hqf j _), ← Finset.mul_sum]
    rw [← Complex.re_sum, sum_trace_mul_qf_dProj hy q j i]
    simp
  · simp_rw [fderiv_stateFn_inl hy, fderiv_stateFn_inr hy]
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [ dysonStateCov_inr_inl]
    simp_rw [mul_assoc, mul_comm (qf q _).re, re_mul_re_of_real (htr j _) (hqf i _),
      ← Finset.mul_sum]
    rw [← Complex.re_sum, sum_trace_mul_qf_dProj hy q i j]
    simp
  · have hN : (N : ℝ) ≠ 0 := ne_zero_of_fin i
    simp_rw [fderiv_stateFn_inr hy]
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rw [
      dysonStateCov_inr_inr]
    have e : ∀ x, ((N : ℝ) * (qf q (dProjAt N y i (hermBasis x))).re) *
        ((N : ℝ) * (qf q (dProjAt N y j (hermBasis x))).re) =
        (N : ℝ) ^ 2 * (qf q (dProjAt N y i (hermBasis x)) *
          qf q (dProjAt N y j (hermBasis x))).re := fun x => by
      rw [← re_mul_re_of_real (hqf i x) (hqf j x)]; ring
    simp_rw [e, ← Finset.mul_sum]
    rw [← Complex.re_sum]
    unfold dProjAt
    rw [(specFamily_coord hy).sum_qf_dProj_mul q i j]
    simp only [dysonState_inr', state_inl]
    set z : Fin N → ℝ := fun m => (qf q (proj N m y)).re with hzdef
    have hz : ∀ m, qf q (proj N m y) = (z m : ℂ) := fun m =>
      (qf_real_of_isHermitian q (hP m)).symm
    simp only [hz, Complex.ofReal_re]
    split_ifs with hij
    · subst hij
      rw [show (2 : ℂ) * ∑ m ∈ Finset.univ.erase i,
          (((lam N i y : ℝ) : ℂ) - ((lam N m y : ℝ) : ℂ))⁻¹ ^ 2 * ((z i : ℂ) * (z m : ℂ)) =
          ((2 * ∑ m ∈ Finset.univ.erase i, (lam N i y - lam N m y)⁻¹ ^ 2 * (z i * z m) : ℝ) : ℂ)
          by push_cast; ring, Complex.ofReal_re, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      unfold dysonCoupling
      field_simp
    · rw [show (-2 : ℂ) * (((lam N i y : ℝ) : ℂ) - ((lam N j y : ℝ) : ℂ))⁻¹ ^ 2 *
          ((z i : ℂ) * (z j : ℂ)) =
          ((-2 * (lam N i y - lam N j y)⁻¹ ^ 2 * (z i * z j)) : ℝ) by push_cast; ring,
        Complex.ofReal_re]
      unfold dysonCoupling
      field_simp

/-- **Itô bracket of a component** (contract `itoBracket` form). -/
theorem itoBracket_dysonState {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (q : Fin N → ℂ)
    (k : Fin (N + N)) (t : ℝ≥0) :
    itoBracket (fun p : ℝ × (Fin (N * N) → ℝ) => stateFn N q k p.2) y t (gueCovVec N) =
      dysonStateCov N (dysonState N q (vecHerm N y)) k k := by
  rw [gueCovVec_eq, itoBracket_comp_snd ((contDiffAt_stateFn (n := 1) hy q k).differentiableAt
    (by norm_num)), gradPair_dysonState hy q k k]

/-- **Itô bracket of a sum of two components**: `Cov kk + 2 Cov kl + Cov ll` (polarization). -/
theorem itoBracket_dysonState_add {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (q : Fin N → ℂ) (k l : Fin (N + N)) (t : ℝ≥0) :
    itoBracket (fun p : ℝ × (Fin (N * N) → ℝ) => stateFn N q k p.2 + stateFn N q l p.2) y t
        (gueCovVec N) =
      dysonStateCov N (dysonState N q (vecHerm N y)) k k +
        2 * dysonStateCov N (dysonState N q (vecHerm N y)) k l +
        dysonStateCov N (dysonState N q (vecHerm N y)) l l := by
  have hk := (contDiffAt_stateFn (n := 1) hy q k).differentiableAt (by norm_num)
  have hl := (contDiffAt_stateFn (n := 1) hy q l).differentiableAt (by norm_num)
  rw [gueCovVec_eq, itoBracket_comp_snd (g := fun y => stateFn N q k y + stateFn N q l y)
    (hk.add hl), ← gradPair_dysonState hy q k k, ← gradPair_dysonState hy q k l,
    ← gradPair_dysonState hy q l l]
  simp only [fderiv_fun_add hk hl, FunLike.coe_add, Pi.add_apply]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end BlockBand.SourceProcess.Stochastic.Dyson
