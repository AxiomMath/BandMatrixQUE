module

public import BlockBand.Palm.MomentFlow.MultiPermPoint
public import BlockBand.Palm.MomentFlow.MultiIto

/-!
# Itô drift of a generic configuration-weighted mass with fixed centres

`gTilted K w (t, y) = e^{-Kt} Σ_q w_q(λ, c) v_q`.

* `itoDrift_gTilted`, `itoDrift_gTilted_nonpos` (covariance `gCov`: `δ_kl/N` on the eigenvalue
  block, zero elsewhere; drift `0` on the centre block);
* `hasDerivAt_pW_line`, `hasDerivAt_permD1_line`, `permW_contDiff`: the matching weight is such a
  family with `d1 = ζ! Σ_y permD1`, `d2 = ζ! Σ_y permD2`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.Transmission BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N r M : ℕ}

/-- Coordinate of `λ_m`. -/
def glIdx (m : Fin N) : Fin (N + (r + M)) := finSumFinEquiv (Sum.inl m)

/-- Coordinate of the centre `c_m`. -/
def gcIdx (m : Fin r) : Fin (N + (r + M)) := finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl m)))

/-- Coordinate of `v_q`. -/
def gvIdx (q : Fin M) : Fin (N + (r + M)) := finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr q)))

theorem sum_split3 (g : Fin (N + (r + M)) → ℝ) :
    ∑ i, g i = ∑ m, g (glIdx m) + ∑ m, g (gcIdx (M := M) m) + ∑ q, g (gvIdx (r := r) q) := by
  rw [← Equiv.sum_comp finSumFinEquiv g, Fintype.sum_sum_type]
  rw [← Equiv.sum_comp finSumFinEquiv (fun x => g (finSumFinEquiv (Sum.inr x))),
    Fintype.sum_sum_type]
  simp only [glIdx, gcIdx, gvIdx]; ring

theorem gl_single_gl (i m : Fin N) :
    (Pi.single (glIdx (r := r) (M := M) i) (1 : ℝ) : Fin (N + (r + M)) → ℝ) (glIdx m) =
      if m = i then 1 else 0 := by
  rw [Pi.single_apply]
  by_cases h : m = i
  · subst h; simp
  · rw [ite_eq_right (fun e => h (by simpa [glIdx] using e)), ite_eq_right h]

theorem gl_single_gc (i : Fin N) (m : Fin r) :
    (Pi.single (glIdx (r := r) (M := M) i) (1 : ℝ) : Fin (N + (r + M)) → ℝ) (gcIdx m) = 0 := by
  rw [Pi.single_apply, ite_eq_right (fun e => by have := congrArg finSumFinEquiv.symm e; simp [glIdx, gcIdx] at this)]

theorem gl_single_gv (i : Fin N) (q : Fin M) :
    (Pi.single (glIdx (r := r) (M := M) i) (1 : ℝ) : Fin (N + (r + M)) → ℝ) (gvIdx q) = 0 := by
  rw [Pi.single_apply, ite_eq_right (fun e => by have := congrArg finSumFinEquiv.symm e; simp [glIdx, gvIdx] at this)]

theorem gv_single_gl (q : Fin M) (m : Fin N) :
    (Pi.single (gvIdx (r := r) q) (1 : ℝ) : Fin (N + (r + M)) → ℝ) (glIdx m) = 0 := by
  rw [Pi.single_apply, ite_eq_right (fun e => by have := congrArg finSumFinEquiv.symm e; simp [glIdx, gvIdx] at this)]

theorem gv_single_gc (q : Fin M) (m : Fin r) :
    (Pi.single (gvIdx (N := N) q) (1 : ℝ) : Fin (N + (r + M)) → ℝ) (gcIdx m) = 0 := by
  refine (Pi.single_apply _ _ _).trans (ite_eq_right fun e => ?_)
  have h1 := congrArg finSumFinEquiv.symm e
  simp only [gcIdx, gvIdx, Equiv.symm_apply_apply, Sum.inr.injEq] at h1
  have h2 := congrArg finSumFinEquiv.symm h1
  simp at h2

theorem gv_single_gv (q p : Fin M) :
    (Pi.single (gvIdx (N := N) (r := r) q) (1 : ℝ) : Fin (N + (r + M)) → ℝ) (gvIdx p) =
      if p = q then 1 else 0 := by
  rw [Pi.single_apply]
  by_cases h : p = q
  · subst h; simp
  · rw [ite_eq_right (fun e => h (by simpa [gvIdx] using e)), ite_eq_right h]

/-- Covariance: `δ_kl/N` on the eigenvalue block, zero elsewhere. -/
def gCov (N r M : ℕ) : Matrix (Fin (N + (r + M))) (Fin (N + (r + M))) ℝ :=
  blockCov (e := r + M) (Matrix.of fun k l : Fin N => if k = l then 1 / (N : ℝ) else 0)

theorem gCov_ll (k l : Fin N) :
    gCov N r M (glIdx k) (glIdx l) = if k = l then 1 / (N : ℝ) else 0 := by
  simp [gCov, blockCov, glIdx]

theorem gCov_c_left (m : Fin r) (j : Fin (N + (r + M))) : gCov N r M (gcIdx m) j = 0 := by
  simp only [gCov, blockCov, gcIdx, Matrix.of_apply, Equiv.symm_apply_apply]

theorem gCov_v_left (q : Fin M) (j : Fin (N + (r + M))) : gCov N r M (gvIdx q) j = 0 := by
  simp only [gCov, blockCov, gvIdx, Matrix.of_apply, Equiv.symm_apply_apply]

theorem gCov_l_c (k : Fin N) (m : Fin r) : gCov N r M (glIdx k) (gcIdx m) = 0 := by
  simp only [gCov, blockCov, gcIdx, glIdx, Matrix.of_apply, Equiv.symm_apply_apply]

theorem gCov_l_v (k : Fin N) (q : Fin M) : gCov N r M (glIdx k) (gvIdx q) = 0 := by
  simp only [gCov, blockCov, gvIdx, glIdx, Matrix.of_apply, Equiv.symm_apply_apply]

/-- `e^{-Kt} Σ_q w_q(λ, c) v_q`. -/
def gTilted (K : ℝ) (w : Fin M → (Fin N → ℝ) → (Fin r → ℝ) → ℝ)
    (p : ℝ × (Fin (N + (r + M)) → ℝ)) : ℝ :=
  Real.exp (-(K * p.1)) *
    ∑ q, w q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)) * p.2 (gvIdx q)

variable {K : ℝ} {w : Fin M → (Fin N → ℝ) → (Fin r → ℝ) → ℝ}
  {d1 d2 : Fin M → (Fin N → ℝ) → (Fin r → ℝ) → Fin N → ℝ}

theorem gTilted_contDiff
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2)) :
    ContDiff ℝ 2 (gTilted (N := N) (r := r) (M := M) K w) := by
  unfold gTilted
  refine ((contDiff_fst.const_smul K).neg.exp).mul ?_
  refine ContDiff.sum fun q _ => ?_
  refine ContDiff.mul ?_ ((contDiff_apply ℝ ℝ (gvIdx q)).comp contDiff_snd)
  have hproj : ContDiff ℝ 2 (fun p : ℝ × (Fin (N + (r + M)) → ℝ) =>
      ((fun m => p.2 (glIdx m)), (fun m => p.2 (gcIdx m)))) :=
    (contDiff_pi.2 fun m => (contDiff_apply ℝ ℝ (glIdx m)).comp contDiff_snd).prodMk
      (contDiff_pi.2 fun m => (contDiff_apply ℝ ℝ (gcIdx m)).comp contDiff_snd)
  exact (hw q).comp hproj

theorem gTilted_differentiableAt
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2))
    (p : ℝ × (Fin (N + (r + M)) → ℝ)) :
    DifferentiableAt ℝ (gTilted (N := N) (r := r) (M := M) K w) p :=
  (gTilted_contDiff hw).differentiable (by norm_num) p

theorem g_line_time (p : ℝ × (Fin (N + (r + M)) → ℝ)) :
    HasDerivAt (fun s : ℝ => gTilted K w (p + s • ((1 : ℝ), (0 : Fin (N + (r + M)) → ℝ))))
      (-K * gTilted K w p) 0 := by
  have h : (fun s : ℝ => gTilted K w (p + s • ((1 : ℝ), (0 : Fin (N + (r + M)) → ℝ)))) =
      fun s => Real.exp (-(K * (p.1 + s))) *
        ∑ q, w q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)) * p.2 (gvIdx q) := by
    funext s; simp [gTilted]
  rw [h]
  have h1 : HasDerivAt (fun s : ℝ => -(K * (p.1 + s))) (-K) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_add p.1).const_mul K).fun_neg
    simpa using this
  refine ((h1.exp).mul_const _).congr_deriv ?_
  simp [gTilted]; ring

theorem g_line_lam (hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => w q (fun m => lam m + if m = i then s else 0) c) (d1 q lam c i) 0)
    (p : ℝ × (Fin (N + (r + M)) → ℝ)) (i : Fin N) :
    HasDerivAt (fun s : ℝ => gTilted K w (p + s • ((0 : ℝ), Pi.single (glIdx i) (1 : ℝ))))
      (Real.exp (-(K * p.1)) * ∑ q, d1 q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)) i *
        p.2 (gvIdx q)) 0 := by
  have h : (fun s : ℝ => gTilted K w (p + s • ((0 : ℝ), Pi.single (glIdx i) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ q,
        w q (fun m => p.2 (glIdx m) + if m = i then s else 0) (fun m => p.2 (gcIdx m)) *
          p.2 (gvIdx q) := by
    funext s
    simp only [gTilted, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, gl_single_gl, gl_single_gc, gl_single_gv]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    funext m
    split_ifs <;> simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun q s =>
      w q (fun m => p.2 (glIdx m) + if m = i then s else 0) (fun m => p.2 (gcIdx m)) *
        p.2 (gvIdx q))
    (A' := fun q => d1 q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)) i * p.2 (gvIdx q))
    (x := 0) (fun q _ => (hd1 q _ _ i).mul_const _)
  exact hs.const_mul _

theorem g_line_mass (p : ℝ × (Fin (N + (r + M)) → ℝ)) (q : Fin M) :
    HasDerivAt (fun s : ℝ => gTilted K w (p + s • ((0 : ℝ), Pi.single (gvIdx q) (1 : ℝ))))
      (Real.exp (-(K * p.1)) * w q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m))) 0 := by
  classical
  have h : (fun s : ℝ => gTilted K w (p + s • ((0 : ℝ), Pi.single (gvIdx q) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ p', w p' (fun m => p.2 (glIdx m))
        (fun m => p.2 (gcIdx m)) * (p.2 (gvIdx p') + if p' = q then s else 0) := by
    funext s
    simp only [gTilted, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, gv_single_gl, gv_single_gc, gv_single_gv]
    congr 1
    refine Finset.sum_congr rfl fun p' _ => ?_
    split_ifs <;> simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun p' s =>
      w p' (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)) *
        (p.2 (gvIdx p') + if p' = q then s else 0))
    (A' := fun p' => if p' = q then w p' (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m))
      else 0) (x := 0)
    (fun p' _ => by
      by_cases hp : p' = q
      · simp only [hp, ite_true]
        have := ((hasDerivAt_id' (0 : ℝ)).const_add (p.2 (gvIdx q))).const_mul
          (w q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)))
        simpa using this
      · simp only [hp, ite_false, add_zero]
        exact hasDerivAt_const _ _)
  refine (hs.const_mul (Real.exp (-(K * p.1)))).congr_deriv ?_
  simp

theorem partialSpace2_gTilted_lam
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2))
    (hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => w q (fun m => lam m + if m = i then s else 0) c) (d1 q lam c i) 0)
    (hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => d1 q (fun m => lam m + if m = i then s else 0) c i) (d2 q lam c i) 0)
    (p : ℝ × (Fin (N + (r + M)) → ℝ)) (i : Fin N) :
    partialSpace2 (gTilted K w) p (glIdx i) (glIdx i) = Real.exp (-(K * p.1)) *
      ∑ q, d2 q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)) i * p.2 (gvIdx q) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (gTilted (N := N) (r := r) (M := M) K w)) p :=
    ((gTilted_contDiff hw).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) p
  unfold partialSpace2
  rw [fderiv_fderiv_apply hdiff]
  set Gf : ℝ × (Fin (N + (r + M)) → ℝ) → ℝ := fun p' => Real.exp (-(K * p'.1)) *
      ∑ q, d1 q (fun m => p'.2 (glIdx m)) (fun m => p'.2 (gcIdx m)) i * p'.2 (gvIdx q) with hG
  have hfun : (fun p' => fderiv ℝ (gTilted K w) p'
      ((0 : ℝ), Pi.single (glIdx i) (1 : ℝ))) = Gf :=
    funext fun p' => fderiv_apply_of_line (gTilted_differentiableAt hw p') (g_line_lam hd1 p' i)
  have hGd : DifferentiableAt ℝ Gf p := by
    rw [← hfun]
    exact hdiff.clm_apply (differentiableAt_const _)
  rw [hfun]
  refine fderiv_apply_of_line hGd ?_
  have h : (fun s : ℝ => Gf (p + s • ((0 : ℝ), Pi.single (glIdx i) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ q,
        d1 q (fun m => p.2 (glIdx m) + if m = i then s else 0) (fun m => p.2 (gcIdx m)) i *
          p.2 (gvIdx q) := by
    funext s
    simp only [hG, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, gl_single_gl, gl_single_gc, gl_single_gv]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    funext m
    split_ifs <;> simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun q s =>
      d1 q (fun m => p.2 (glIdx m) + if m = i then s else 0) (fun m => p.2 (gcIdx m)) i *
        p.2 (gvIdx q))
    (A' := fun q => d2 q (fun m => p.2 (glIdx m)) (fun m => p.2 (gcIdx m)) i * p.2 (gvIdx q))
    (x := 0) (fun q _ => (hd2 q _ _ i).mul_const _)
  exact hs.const_mul _

/-- **Itô drift of the generic tilted mass** (fixed centres: zero drift on the centre block). -/
theorem itoDrift_gTilted
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2))
    (hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => w q (fun m => lam m + if m = i then s else 0) c) (d1 q lam c i) 0)
    (hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => d1 q (fun m => lam m + if m = i then s else 0) c i) (d2 q lam c i) 0)
    (y : Fin (N + (r + M)) → ℝ) (t : ℝ≥0) (b : Fin (N + (r + M)) → ℝ)
    (hbc : ∀ m, b (gcIdx m) = 0) :
    itoDrift (gTilted K w) y t b (gCov N r M) =
      Real.exp (-(K * t)) * (-K * ∑ q, w q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) *
          y (gvIdx q) +
        ∑ i, b (glIdx i) * ∑ q, d1 q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) i *
          y (gvIdx q) +
        ∑ q, b (gvIdx q) * w q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) +
        (1 / 2 : ℝ) * ∑ i, (1 / (N : ℝ)) *
          ∑ q, d2 q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) i * y (gvIdx q)) := by
  classical
  unfold itoDrift
  rw [partialTime, fderiv_apply_of_line (gTilted_differentiableAt hw _) (g_line_time _),
    sum_split3]
  simp only [hbc, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [partialSpace, fderiv_apply_of_line (gTilted_differentiableAt hw _)
    (g_line_lam hd1 _ _), fderiv_apply_of_line (gTilted_differentiableAt hw _) (g_line_mass _ _)]
  have h2 : ∑ i, ∑ j, gCov N r M i j * partialSpace2 (gTilted K w) ((t : ℝ), y) i j =
      ∑ i, (1 / (N : ℝ)) * (Real.exp (-(K * t)) *
        ∑ q, d2 q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) i * y (gvIdx q)) := by
    rw [sum_split3]
    simp only [gCov_c_left, gCov_v_left, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_split3]
    simp only [gCov_l_c, gCov_l_v, zero_mul, Finset.sum_const_zero, add_zero, gCov_ll,
      ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [partialSpace2_gTilted_lam hw hd1 hd2]
  rw [h2]
  simp only [gTilted, mul_add, Finset.mul_sum]
  ring_nf

/-- **Nonpositive generic tilted drift.** -/
theorem itoDrift_gTilted_nonpos
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2))
    (hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => w q (fun m => lam m + if m = i then s else 0) c) (d1 q lam c i) 0)
    (hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => d1 q (fun m => lam m + if m = i then s else 0) c i) (d2 q lam c i) 0)
    (y : Fin (N + (r + M)) → ℝ) (t : ℝ≥0) (L : Fin M → Fin M → ℝ) {κ : ℝ} (hκ : κ ≤ K)
    (hS : 0 ≤ ∑ q, w q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) * y (gvIdx q))
    (hQ : ∑ q, w q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) *
          ∑ q', L q q' * y (gvIdx q') +
        ∑ q, y (gvIdx q) * ∑ i, (dysonDrift N (fun m => y (glIdx m)) i *
          d1 q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) i +
          d2 q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) i / (2 * N)) ≤
      κ * ∑ q, w q (fun m => y (glIdx m)) (fun m => y (gcIdx m)) * y (gvIdx q))
    (b : Fin (N + (r + M)) → ℝ) (hbl : ∀ i, b (glIdx i) = dysonDrift N (fun m => y (glIdx m)) i)
    (hbc : ∀ m, b (gcIdx m) = 0) (hbm : ∀ q, b (gvIdx q) = ∑ q', L q q' * y (gvIdx q')) :
    itoDrift (gTilted K w) y t b (gCov N r M) ≤ 0 := by
  rw [itoDrift_gTilted hw hd1 hd2 y t b hbc]
  simp only [hbl, hbm]
  set lam := fun m => y (glIdx m)
  set cc := fun m => y (gcIdx (M := M) m)
  set S := ∑ q, w q lam cc * y (gvIdx q)
  have ha : ∑ i, dysonDrift N lam i * ∑ q, d1 q lam cc i * y (gvIdx q) =
      ∑ q, y (gvIdx q) * ∑ i, dysonDrift N lam i * d1 q lam cc i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring
  have hb : (1 / 2 : ℝ) * ∑ i, (1 / (N : ℝ)) * ∑ q, d2 q lam cc i * y (gvIdx q) =
      ∑ q, y (gvIdx q) * ∑ i, d2 q lam cc i / (2 * N) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne (N : ℝ) 0 with hN | hN
    · rw [hN]; simp
    · field_simp
  have hc' : ∑ q, (∑ q', L q q' * y (gvIdx q')) * w q lam cc =
      ∑ q, w q lam cc * ∑ q', L q q' * y (gvIdx q') :=
    Finset.sum_congr rfl fun q _ => mul_comm _ _
  have hd : ∑ q, y (gvIdx q) * ∑ i, (dysonDrift N lam i * d1 q lam cc i +
        d2 q lam cc i / (2 * N)) =
      ∑ q, y (gvIdx q) * ∑ i, dysonDrift N lam i * d1 q lam cc i +
        ∑ q, y (gvIdx q) * ∑ i, d2 q lam cc i / (2 * N) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [Finset.sum_add_distrib, mul_add]
  have key : -K * S + (∑ i, dysonDrift N lam i * ∑ q, d1 q lam cc i * y (gvIdx q) +
      ∑ q, (∑ q', L q q' * y (gvIdx q')) * w q lam cc +
      (1 / 2 : ℝ) * ∑ i, (1 / (N : ℝ)) * ∑ q, d2 q lam cc i * y (gvIdx q)) ≤ 0 := by
    rw [ha, hb, hc']
    rw [hd] at hQ
    nlinarith
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  linarith

/-!
### The matching weight as a smooth family
-/

theorem hasDerivAt_pW_line {φ φ1 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) (i : Fin N) :
    HasDerivAt (fun s : ℝ => pW φ (fun m => lam m + if m = i then s else 0) c y)
      (permD1 φ φ1 lam c y i) 0 := by
  classical
  have hf : ∀ m ∈ (univ : Finset (Fin r)), HasDerivAt
      (fun s : ℝ => φ (lam (y m) + (if y m = i then s else 0) - c m))
      (if y m = i then φ1 (lam i - c m) else 0) 0 := by
    intro m _
    by_cases hm : y m = i
    · simp only [hm, ite_true]
      have := HasDerivAt.comp_const_add (lam i - c m) (0 : ℝ)
        (by simpa using hφ (lam i - c m))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only; ring_nf
    · simp only [hm, ite_false, add_zero]; exact hasDerivAt_const _ _
  have h := HasDerivAt.fun_finsetProd hf
  unfold pW permD1
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [smul_eq_mul, add_zero, ite_self, pWx]
  by_cases hm : y m = i
  · rw [ite_eq_left hm, ite_eq_left hm]
    subst hm
    ring
  · rw [ite_eq_right hm, ite_eq_right hm, mul_zero]

theorem pWx_shift (φ : ℝ → ℝ) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) (i : Fin N)
    (m : Fin r) (s : ℝ) :
    pWx φ (fun m => lam m + if m = i then s else 0) c y m =
      ∏ m' ∈ univ.erase m, φ (lam (y m') + (if y m' = i then s else 0) - c m') := rfl

theorem hasDerivAt_pWx_line {φ φ1 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N) (i : Fin N) (m : Fin r) :
    HasDerivAt (fun s : ℝ => pWx φ (fun m => lam m + if m = i then s else 0) c y m)
      (∑ m' ∈ univ.erase m, if y m' = i then φ1 (lam i - c m') * pWxx φ lam c y m m' else 0)
      0 := by
  classical
  have hf : ∀ m' ∈ univ.erase m, HasDerivAt
      (fun s : ℝ => φ (lam (y m') + (if y m' = i then s else 0) - c m'))
      (if y m' = i then φ1 (lam i - c m') else 0) 0 := by
    intro m' _
    by_cases hm : y m' = i
    · simp only [hm, ite_true]
      have := HasDerivAt.comp_const_add (lam i - c m') (0 : ℝ)
        (by simpa using hφ (lam i - c m'))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only; ring_nf
    · simp only [hm, ite_false, add_zero]; exact hasDerivAt_const _ _
  have h := HasDerivAt.fun_finsetProd hf
  simp only [pWx_shift]
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun m' _ => ?_
  simp only [smul_eq_mul, add_zero, ite_self, pWxx]
  by_cases hm : y m' = i
  · rw [ite_eq_left hm, ite_eq_left hm]
    subst hm
    ring
  · rw [ite_eq_right hm, ite_eq_right hm, mul_zero]

theorem hasDerivAt_permD1_line {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (lam : Fin N → ℝ) (c : Fin r → ℝ) (y : Fin r → Fin N)
    (i : Fin N) :
    HasDerivAt (fun s : ℝ => permD1 φ φ1 (fun m => lam m + if m = i then s else 0) c y i)
      (permD2 φ φ1 φ2 lam c y i) 0 := by
  classical
  unfold permD1 permD2
  refine HasDerivAt.fun_sum fun m _ => ?_
  by_cases hm : y m = i
  · simp only [hm, ite_true]
    have h1 : HasDerivAt (fun s : ℝ => φ1 (lam i + s - c m)) (φ2 (lam i - c m)) 0 := by
      have := HasDerivAt.comp_const_add (lam i - c m) (0 : ℝ)
        (by simpa using hφ1 (lam i - c m))
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only; ring_nf
    have h2 := hasDerivAt_pWx_line hφ lam c y i m
    have h3 := h1.mul h2
    refine HasDerivAt.congr_of_eventuallyEq (h3.congr_deriv ?_)
      (Filter.Eventually.of_forall fun s => ?_)
    · simp only [add_zero, ite_self]
    · simp
  · simp only [hm, ite_false]; exact hasDerivAt_const _ _

theorem permW_contDiff {φ : ℝ → ℝ} (hφc : ContDiff ℝ 2 φ) (ζ : Occ N) :
    ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => permW φ z.1 z.2 ζ) := by
  unfold permW pW
  refine contDiff_const.mul (ContDiff.sum fun y _ => contDiff_prod fun m _ => ?_)
  exact hφc.comp (((contDiff_apply ℝ ℝ (y m)).comp contDiff_fst).sub
    ((contDiff_apply ℝ ℝ m).comp contDiff_snd))

theorem hasDerivAt_permW_line {φ φ1 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (lam : Fin N → ℝ) (c : Fin r → ℝ) (ζ : Occ N) (i : Fin N) :
    HasDerivAt (fun s : ℝ => permW φ (fun m => lam m + if m = i then s else 0) c ζ)
      (cfgFact ζ * ∑ y ∈ labs r ζ, permD1 φ φ1 lam c y i) 0 := by
  unfold permW
  exact (HasDerivAt.fun_sum fun y _ => hasDerivAt_pW_line hφ lam c y i).const_mul _

theorem hasDerivAt_permWD1_line {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (lam : Fin N → ℝ) (c : Fin r → ℝ) (ζ : Occ N)
    (i : Fin N) :
    HasDerivAt (fun s : ℝ => cfgFact ζ * ∑ y ∈ labs r ζ,
        permD1 φ φ1 (fun m => lam m + if m = i then s else 0) c y i)
      (cfgFact ζ * ∑ y ∈ labs r ζ, permD2 φ φ1 φ2 lam c y i) 0 :=
  (HasDerivAt.fun_sum fun y _ => hasDerivAt_permD1_line hφ hφ1 lam c y i).const_mul _

end BlockBand.Palm.MomentFlow
