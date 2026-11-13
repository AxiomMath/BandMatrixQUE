module

public import BlockBand.Palm.MomentFlow.MultiMat
public import BlockBand.Palm.RelativeLocalizationIto
public import BlockBand.Palm.RelativeLocalizationSemimart

/-!
# `r`-particle finite speed: Itô drift of the tilted configuration-weighted mass

State `y ∈ ℝ^{N+M}` in the `finSumFinEquiv` layout: eigenvalues `y (mlIdx m)`, masses
`y (mvIdx q)` indexed by an arbitrary family of configurations `σ : Fin M → Occ N` (in the use,
the enumeration of the `r`-particle sector). The function is
`cfgTilted K φ σ (t, y) = e^{-Kt} Σ_q W_φ(λ, σ_q) v_q` with the product weight of
`MultiDrift`, and the covariance is `cfgCov N M` (the eigenvalue block `δ_kl/N`, zero on the
mass block; this is `blockCov` of the covariance of `flowLam_semimartingale`).

* `cfgTilted_contDiff` (`C²`, as required by `SemimartingaleItoFormula`);
* `partialTime_cfgTilted`, `partialSpace_cfgTilted_lam`, `partialSpace_cfgTilted_mass`,
  `partialSpace2_cfgTilted_lam` (the derivatives are `cfgD1`, `cfgD2` of `MultiDrift`);
* `itoDrift_cfgTilted` (explicit Itô drift) and `itoDrift_cfgTilted_nonpos` (drift `≤ 0` from
  the summed drift inequality `Q ≤ κ S` with `κ ≤ K`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.Transmission BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N M : ℕ}

/-- Coordinate of `λ_m`. -/
def mlIdx (m : Fin N) : Fin (N + M) := finSumFinEquiv (Sum.inl m)

/-- Coordinate of `v_q`. -/
def mvIdx (q : Fin M) : Fin (N + M) := finSumFinEquiv (Sum.inr q)

theorem mlIdx_injective : Function.Injective (mlIdx (N := N) (M := M)) := by
  intro k m h; simpa [mlIdx] using h

theorem mvIdx_injective : Function.Injective (mvIdx (N := N) (M := M)) := by
  intro k m h; simpa [mvIdx] using h

theorem mlIdx_ne_mvIdx (k : Fin N) (q : Fin M) : (mlIdx k : Fin (N + M)) ≠ mvIdx q := by
  intro h
  have := congrArg finSumFinEquiv.symm h
  simp [mlIdx, mvIdx] at this

theorem sum_split2 (g : Fin (N + M) → ℝ) :
    ∑ i, g i = ∑ m, g (mlIdx m) + ∑ q, g (mvIdx q) := by
  rw [← Equiv.sum_comp finSumFinEquiv g, Fintype.sum_sum_type]; rfl

theorem single_ml_ml (i m : Fin N) :
    (Pi.single (mlIdx i) (1 : ℝ) : Fin (N + M) → ℝ) (mlIdx m) = if m = i then 1 else 0 := by
  rw [Pi.single_apply]
  by_cases h : m = i
  · subst h; simp
  · rw [ite_eq_right fun e => h (mlIdx_injective e), ite_eq_right h]

theorem single_ml_mv (i : Fin N) (q : Fin M) :
    (Pi.single (mlIdx i) (1 : ℝ) : Fin (N + M) → ℝ) (mvIdx q) = 0 := by
  rw [Pi.single_apply, ite_eq_right fun e => mlIdx_ne_mvIdx i q e.symm]

theorem single_mv_ml (q : Fin M) (m : Fin N) :
    (Pi.single (mvIdx q) (1 : ℝ) : Fin (N + M) → ℝ) (mlIdx m) = 0 := by
  rw [Pi.single_apply, ite_eq_right (mlIdx_ne_mvIdx m q)]

theorem single_mv_mv (q p : Fin M) :
    (Pi.single (mvIdx q) (1 : ℝ) : Fin (N + M) → ℝ) (mvIdx p) = if p = q then 1 else 0 := by
  rw [Pi.single_apply]
  by_cases h : p = q
  · subst h; simp
  · rw [ite_eq_right fun e => h (mvIdx_injective e), ite_eq_right h]

/-- `e^{-Kt} Σ_q W_φ(λ, σ_q) v_q`. -/
def cfgTilted (K : ℝ) (φ : ℝ → ℝ) (σ : Fin M → Occ N) (p : ℝ × (Fin (N + M) → ℝ)) : ℝ :=
  Real.exp (-(K * p.1)) * ∑ q, cfgWeight φ (fun m => p.2 (mlIdx m)) (σ q) * p.2 (mvIdx q)

/-- Covariance: `δ_kl/N` on the eigenvalue block, zero elsewhere. -/
def cfgCov (N M : ℕ) : Matrix (Fin (N + M)) (Fin (N + M)) ℝ :=
  blockCov (e := M) (Matrix.of fun k l : Fin N => if k = l then 1 / (N : ℝ) else 0)

theorem cfgCov_ll (k l : Fin N) :
    cfgCov N M (mlIdx k) (mlIdx l) = if k = l then 1 / (N : ℝ) else 0 := by
  simp [cfgCov, blockCov, mlIdx]

theorem cfgCov_mv_left (q : Fin M) (j : Fin (N + M)) : cfgCov N M (mvIdx q) j = 0 := by
  simp only [cfgCov, blockCov, mvIdx, Matrix.of_apply, Equiv.symm_apply_apply]

theorem cfgCov_mv_right (i : Fin (N + M)) (q : Fin M) : cfgCov N M i (mvIdx q) = 0 := by
  simp only [cfgCov, blockCov, mvIdx, Matrix.of_apply, Equiv.symm_apply_apply]
  split <;> simp_all

/-!
### Line derivatives of the weight
-/

theorem cfgWeight_shift_eq (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (i : Fin N) (s : ℝ) :
    cfgWeight φ (fun m => lam m + if m = i then s else 0) ξ =
      φ (lam i + s) ^ ξ i * ∏ m ∈ univ.erase i, φ (lam m) ^ ξ m := by
  rw [cfgWeight_split _ _ ξ i]
  simp only [ite_true]
  congr 1
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [ite_eq_right (mem_erase.1 hm).1, add_zero]

theorem cfgWeight_remove_eq (φ : ℝ → ℝ) (lam : Fin N → ℝ) (ξ : Occ N) (i : Fin N) :
    cfgWeight φ lam (remove ξ i) = φ (lam i) ^ (ξ i - 1) * ∏ m ∈ univ.erase i, φ (lam m) ^ ξ m :=
  cfgWeight_update φ lam ξ i (ξ i - 1)

/-- `d/ds W_φ(λ + s e_i, ξ) |_{s=0} = cfgD1`. -/
theorem hasDerivAt_cfgWeight_line {φ φ1 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (lam : Fin N → ℝ) (ξ : Occ N) (i : Fin N) :
    HasDerivAt (fun s : ℝ => cfgWeight φ (fun m => lam m + if m = i then s else 0) ξ)
      (cfgD1 φ φ1 lam ξ i) 0 := by
  simp only [cfgWeight_shift_eq]
  have h1 : HasDerivAt (fun s : ℝ => φ (lam i + s)) (φ1 (lam i)) 0 :=
    HasDerivAt.comp_const_add (lam i) (0 : ℝ) (by simpa using hφ (lam i))
  have h2 := (h1.fun_pow (ξ i)).mul_const (∏ m ∈ univ.erase i, φ (lam m) ^ ξ m)
  refine h2.congr_deriv ?_
  simp only [add_zero, cfgD1, cfgWeight_remove_eq]
  ring

/-- `d/ds cfgD1(λ + s e_i, ξ, i) |_{s=0} = cfgD2`. -/
theorem hasDerivAt_cfgD1_line {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (lam : Fin N → ℝ) (ξ : Occ N) (i : Fin N) :
    HasDerivAt (fun s : ℝ => cfgD1 φ φ1 (fun m => lam m + if m = i then s else 0) ξ i)
      (cfgD2 φ φ1 φ2 lam ξ i) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => φ1 (lam i + s)) (φ2 (lam i)) 0 :=
    HasDerivAt.comp_const_add (lam i) (0 : ℝ) (by simpa using hφ1 (lam i))
  have h2 := hasDerivAt_cfgWeight_line hφ lam (remove ξ i) i
  have h3 := (h1.const_mul (ξ i : ℝ)).mul h2
  have hfun : (fun s : ℝ => cfgD1 φ φ1 (fun m => lam m + if m = i then s else 0) ξ i) =
      fun s => (ξ i : ℝ) * φ1 (lam i + s) *
        cfgWeight φ (fun m => lam m + if m = i then s else 0) (remove ξ i) := by
    funext s; simp [cfgD1]
  rw [hfun]
  refine h3.congr_deriv ?_
  simp only [cfgD1, cfgD2, remove_apply_self, ite_self, add_zero]
  rcases Nat.eq_zero_or_pos (ξ i) with h | h
  · simp [h]
  · rw [Nat.cast_sub (by omega)]; push_cast; ring

/-!
### Partial derivatives of `cfgTilted`
-/

variable {K : ℝ} {φ φ1 φ2 : ℝ → ℝ} {σ : Fin M → Occ N}

theorem cfgTilted_contDiff (hc : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (cfgTilted (N := N) (M := M) K φ σ) := by
  unfold cfgTilted
  refine ((contDiff_fst.const_smul K).neg.exp).mul ?_
  refine ContDiff.sum fun q _ => ?_
  refine ContDiff.mul ?_ ((contDiff_apply ℝ ℝ (mvIdx q)).comp contDiff_snd)
  unfold cfgWeight
  exact contDiff_prod fun m _ =>
    (hc.comp ((contDiff_apply ℝ ℝ (mlIdx m)).comp contDiff_snd)).pow _

theorem cfgTilted_differentiableAt (hc : ContDiff ℝ 2 φ) (p : ℝ × (Fin (N + M) → ℝ)) :
    DifferentiableAt ℝ (cfgTilted (N := N) (M := M) K φ σ) p :=
  (cfgTilted_contDiff hc).differentiable (by norm_num) p

theorem cfg_line_time (p : ℝ × (Fin (N + M) → ℝ)) :
    HasDerivAt (fun s : ℝ => cfgTilted K φ σ (p + s • ((1 : ℝ), (0 : Fin (N + M) → ℝ))))
      (-K * cfgTilted K φ σ p) 0 := by
  have h : (fun s : ℝ => cfgTilted K φ σ (p + s • ((1 : ℝ), (0 : Fin (N + M) → ℝ)))) =
      fun s => Real.exp (-(K * (p.1 + s))) *
        ∑ q, cfgWeight φ (fun m => p.2 (mlIdx m)) (σ q) * p.2 (mvIdx q) := by
    funext s; simp [cfgTilted]
  rw [h]
  have h1 : HasDerivAt (fun s : ℝ => -(K * (p.1 + s))) (-K) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_add p.1).const_mul K).fun_neg
    simpa using this
  have := (h1.exp).mul_const (∑ q, cfgWeight φ (fun m => p.2 (mlIdx m)) (σ q) * p.2 (mvIdx q))
  refine this.congr_deriv ?_
  simp [cfgTilted]; ring

theorem cfg_line_lam (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (p : ℝ × (Fin (N + M) → ℝ)) (i : Fin N) :
    HasDerivAt (fun s : ℝ => cfgTilted K φ σ (p + s • ((0 : ℝ), Pi.single (mlIdx i) (1 : ℝ))))
      (Real.exp (-(K * p.1)) *
        ∑ q, cfgD1 φ φ1 (fun m => p.2 (mlIdx m)) (σ q) i * p.2 (mvIdx q)) 0 := by
  have h : (fun s : ℝ => cfgTilted K φ σ (p + s • ((0 : ℝ), Pi.single (mlIdx i) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ q,
        cfgWeight φ (fun m => p.2 (mlIdx m) + if m = i then s else 0) (σ q) * p.2 (mvIdx q) := by
    funext s
    simp only [cfgTilted, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, single_ml_ml, single_ml_mv]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    funext m
    split_ifs <;> simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun q s =>
      cfgWeight φ (fun m => p.2 (mlIdx m) + if m = i then s else 0) (σ q) * p.2 (mvIdx q))
    (A' := fun q => cfgD1 φ φ1 (fun m => p.2 (mlIdx m)) (σ q) i * p.2 (mvIdx q)) (x := 0)
    (fun q _ => (hasDerivAt_cfgWeight_line hφ _ (σ q) i).mul_const _)
  exact hs.const_mul _

theorem cfg_line_mass (p : ℝ × (Fin (N + M) → ℝ)) (q : Fin M) :
    HasDerivAt (fun s : ℝ => cfgTilted K φ σ (p + s • ((0 : ℝ), Pi.single (mvIdx q) (1 : ℝ))))
      (Real.exp (-(K * p.1)) * cfgWeight φ (fun m => p.2 (mlIdx m)) (σ q)) 0 := by
  classical
  have h : (fun s : ℝ => cfgTilted K φ σ (p + s • ((0 : ℝ), Pi.single (mvIdx q) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ p', cfgWeight φ (fun m => p.2 (mlIdx m)) (σ p') *
        (p.2 (mvIdx p') + if p' = q then s else 0) := by
    funext s
    simp only [cfgTilted, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, single_mv_ml, single_mv_mv]
    congr 1
    refine Finset.sum_congr rfl fun p' _ => ?_
    split_ifs <;> simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun p' s =>
      cfgWeight φ (fun m => p.2 (mlIdx m)) (σ p') * (p.2 (mvIdx p') + if p' = q then s else 0))
    (A' := fun p' => if p' = q then cfgWeight φ (fun m => p.2 (mlIdx m)) (σ p') else 0) (x := 0)
    (fun p' _ => by
      by_cases hp : p' = q
      · simp only [hp, ite_true]
        have := ((hasDerivAt_id' (0 : ℝ)).const_add (p.2 (mvIdx q))).const_mul
          (cfgWeight φ (fun m => p.2 (mlIdx m)) (σ q))
        simpa using this
      · simp only [hp, ite_false, add_zero]
        exact hasDerivAt_const _ _)
  refine (hs.const_mul (Real.exp (-(K * p.1)))).congr_deriv ?_
  simp

theorem partialTime_cfgTilted (hc : ContDiff ℝ 2 φ) (p : ℝ × (Fin (N + M) → ℝ)) :
    partialTime (cfgTilted K φ σ) p = -K * cfgTilted K φ σ p :=
  fderiv_apply_of_line (cfgTilted_differentiableAt hc p) (cfg_line_time p)

theorem partialSpace_cfgTilted_lam (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hc : ContDiff ℝ 2 φ)
    (p : ℝ × (Fin (N + M) → ℝ)) (i : Fin N) :
    partialSpace (cfgTilted K φ σ) p (mlIdx i) = Real.exp (-(K * p.1)) *
      ∑ q, cfgD1 φ φ1 (fun m => p.2 (mlIdx m)) (σ q) i * p.2 (mvIdx q) :=
  fderiv_apply_of_line (cfgTilted_differentiableAt hc p) (cfg_line_lam hφ p i)

theorem partialSpace_cfgTilted_mass (hc : ContDiff ℝ 2 φ) (p : ℝ × (Fin (N + M) → ℝ))
    (q : Fin M) :
    partialSpace (cfgTilted K φ σ) p (mvIdx q) =
      Real.exp (-(K * p.1)) * cfgWeight φ (fun m => p.2 (mlIdx m)) (σ q) :=
  fderiv_apply_of_line (cfgTilted_differentiableAt hc p) (cfg_line_mass p q)

theorem partialSpace2_cfgTilted_lam (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hc : ContDiff ℝ 2 φ)
    (p : ℝ × (Fin (N + M) → ℝ)) (i : Fin N) :
    partialSpace2 (cfgTilted K φ σ) p (mlIdx i) (mlIdx i) = Real.exp (-(K * p.1)) *
      ∑ q, cfgD2 φ φ1 φ2 (fun m => p.2 (mlIdx m)) (σ q) i * p.2 (mvIdx q) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (cfgTilted (N := N) (M := M) K φ σ)) p :=
    ((cfgTilted_contDiff hc).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) p
  unfold partialSpace2
  rw [fderiv_fderiv_apply hdiff]
  set G : ℝ × (Fin (N + M) → ℝ) → ℝ := fun p' => Real.exp (-(K * p'.1)) *
      ∑ q, cfgD1 φ φ1 (fun m => p'.2 (mlIdx m)) (σ q) i * p'.2 (mvIdx q) with hG
  have hfun : (fun p' => fderiv ℝ (cfgTilted K φ σ) p'
      ((0 : ℝ), Pi.single (mlIdx i) (1 : ℝ))) = G :=
    funext fun p' => partialSpace_cfgTilted_lam hφ hc p' i
  rw [hfun]
  have hd1 : Differentiable ℝ φ1 := fun z => (hφ1 z).differentiableAt
  have hd0 : Differentiable ℝ φ := fun z => (hφ z).differentiableAt
  have hGd : DifferentiableAt ℝ G p := by
    simp only [hG, cfgD1, cfgWeight]
    fun_prop
  refine fderiv_apply_of_line hGd ?_
  have h : (fun s : ℝ => G (p + s • ((0 : ℝ), Pi.single (mlIdx i) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ q,
        cfgD1 φ φ1 (fun m => p.2 (mlIdx m) + if m = i then s else 0) (σ q) i * p.2 (mvIdx q) := by
    funext s
    simp only [hG, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, single_ml_ml, single_ml_mv]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    funext m
    split_ifs <;> simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun q s =>
      cfgD1 φ φ1 (fun m => p.2 (mlIdx m) + if m = i then s else 0) (σ q) i * p.2 (mvIdx q))
    (A' := fun q => cfgD2 φ φ1 φ2 (fun m => p.2 (mlIdx m)) (σ q) i * p.2 (mvIdx q)) (x := 0)
    (fun q _ => (hasDerivAt_cfgD1_line hφ hφ1 _ (σ q) i).mul_const _)
  exact hs.const_mul _

/-- **Itô drift of the tilted configuration-weighted mass** (covariance `cfgCov`). -/
theorem itoDrift_cfgTilted (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hc : ContDiff ℝ 2 φ) (y : Fin (N + M) → ℝ) (t : ℝ≥0)
    (b : Fin (N + M) → ℝ) :
    itoDrift (cfgTilted K φ σ) y t b (cfgCov N M) =
      Real.exp (-(K * t)) * (-K * ∑ q, cfgWeight φ (fun m => y (mlIdx m)) (σ q) * y (mvIdx q) +
        ∑ i, b (mlIdx i) * ∑ q, cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q) +
        ∑ q, b (mvIdx q) * cfgWeight φ (fun m => y (mlIdx m)) (σ q) +
        (1 / 2 : ℝ) * ∑ i, (1 / (N : ℝ)) *
          ∑ q, cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q)) := by
  classical
  unfold itoDrift
  rw [partialTime_cfgTilted hc, sum_split2]
  simp only [partialSpace_cfgTilted_lam hφ hc, partialSpace_cfgTilted_mass hc]
  have h2 : ∑ i, ∑ j, cfgCov N M i j * partialSpace2 (cfgTilted K φ σ) ((t : ℝ), y) i j =
      ∑ i, (1 / (N : ℝ)) * (Real.exp (-(K * t)) *
        ∑ q, cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q)) := by
    rw [sum_split2]
    simp only [cfgCov_mv_left, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_split2]
    simp only [cfgCov_mv_right, zero_mul, Finset.sum_const_zero, add_zero, cfgCov_ll,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [partialSpace2_cfgTilted_lam hφ hφ1 hc]
  rw [h2]
  simp only [cfgTilted, mul_add, Finset.mul_sum]
  ring_nf

/-- **Nonpositive tilted drift**: `b_λ = Dyson drift`, `b_v = L v`, the summed drift inequality
`Σ_q W_q (Lv)_q + Σ_q v_q Σ_i (D_i ∂_iW_q + ∂²_iW_q/(2N)) ≤ κ Σ_q W_q v_q`, `v ≥ 0`-weighted
mass `S ≥ 0`, and `κ ≤ K` give `itoDrift ≤ 0`. -/
theorem itoDrift_cfgTilted_nonpos (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hc : ContDiff ℝ 2 φ) (y : Fin (N + M) → ℝ) (t : ℝ≥0)
    (L : Fin M → Fin M → ℝ) {κ : ℝ} (hκ : κ ≤ K)
    (hS : 0 ≤ ∑ q, cfgWeight φ (fun m => y (mlIdx m)) (σ q) * y (mvIdx q))
    (hQ : ∑ q, cfgWeight φ (fun m => y (mlIdx m)) (σ q) * ∑ q', L q q' * y (mvIdx q') +
        ∑ q, y (mvIdx q) * ∑ i, (dysonDrift N (fun m => y (mlIdx m)) i *
          cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i +
          cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i / (2 * N)) ≤
      κ * ∑ q, cfgWeight φ (fun m => y (mlIdx m)) (σ q) * y (mvIdx q))
    (b : Fin (N + M) → ℝ) (hbl : ∀ i, b (mlIdx i) = dysonDrift N (fun m => y (mlIdx m)) i)
    (hbm : ∀ q, b (mvIdx q) = ∑ q', L q q' * y (mvIdx q')) :
    itoDrift (cfgTilted K φ σ) y t b (cfgCov N M) ≤ 0 := by
  rw [itoDrift_cfgTilted hφ hφ1 hc]
  simp only [hbl, hbm]
  set S := ∑ q, cfgWeight φ (fun m => y (mlIdx m)) (σ q) * y (mvIdx q)
  have hrw : ∑ i, dysonDrift N (fun m => y (mlIdx m)) i *
        ∑ q, cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q) +
      ∑ q, (∑ q', L q q' * y (mvIdx q')) * cfgWeight φ (fun m => y (mlIdx m)) (σ q) +
      (1 / 2 : ℝ) * ∑ i, (1 / (N : ℝ)) *
        ∑ q, cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q) =
      ∑ q, cfgWeight φ (fun m => y (mlIdx m)) (σ q) * ∑ q', L q q' * y (mvIdx q') +
        ∑ q, y (mvIdx q) * ∑ i, (dysonDrift N (fun m => y (mlIdx m)) i *
          cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i +
          cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i / (2 * N)) := by
    have ha : ∑ i, dysonDrift N (fun m => y (mlIdx m)) i *
          ∑ q, cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q) =
        ∑ q, y (mvIdx q) * ∑ i, dysonDrift N (fun m => y (mlIdx m)) i *
          cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring
    have hb : (1 / 2 : ℝ) * ∑ i, (1 / (N : ℝ)) *
          ∑ q, cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q) =
        ∑ q, y (mvIdx q) * ∑ i, cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i / (2 * N) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
      rcases eq_or_ne (N : ℝ) 0 with hN | hN
      · rw [hN]; simp
      · field_simp
    have hc' : ∑ q, (∑ q', L q q' * y (mvIdx q')) * cfgWeight φ (fun m => y (mlIdx m)) (σ q) =
        ∑ q, cfgWeight φ (fun m => y (mlIdx m)) (σ q) * ∑ q', L q q' * y (mvIdx q') :=
      Finset.sum_congr rfl fun q _ => mul_comm _ _
    have hd : ∑ q, y (mvIdx q) * ∑ i, (dysonDrift N (fun m => y (mlIdx m)) i *
          cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i +
          cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i / (2 * N)) =
        ∑ q, y (mvIdx q) * ∑ i, dysonDrift N (fun m => y (mlIdx m)) i *
          cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i +
        ∑ q, y (mvIdx q) * ∑ i, cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i / (2 * N) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by rw [Finset.sum_add_distrib, mul_add]
    rw [ha, hb, hc', hd]
    ring
  have : -K * S + (∑ i, dysonDrift N (fun m => y (mlIdx m)) i *
        ∑ q, cfgD1 φ φ1 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q) +
      ∑ q, (∑ q', L q q' * y (mvIdx q')) * cfgWeight φ (fun m => y (mlIdx m)) (σ q) +
      (1 / 2 : ℝ) * ∑ i, (1 / (N : ℝ)) *
        ∑ q, cfgD2 φ φ1 φ2 (fun m => y (mlIdx m)) (σ q) i * y (mvIdx q)) ≤ 0 := by
    rw [hrw]; nlinarith
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  linarith

end BlockBand.Palm.MomentFlow
