module

public import BlockBand.Palm.RelativeLocalizationSpectral
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Relative localization: the Itô drift of the tilted weighted mass

* `itoDrift_tiltedMass` :
  `itoDrift = e^{-Kt} (-K S + Σ_k b_{λ_k} φ'(λ_k) v_k + Σ_k b_{v_k} φ(λ_k) + ½ Σ_k φ''(λ_k) v_k / N)`;
* `itoBracket_tiltedMass` : `itoBracket = Σ_k (e^{-Kt} φ'(λ_k) v_k)² / N`;
* `itoDrift_tiltedMass_nonpos` : with the drift `b_{λ_k} = dysonDrift_k`, `b_{v_k} = (L v)_k`,
  `v ≥ 0` and the weighted drift bound `Q ≤ κ S`, `itoDrift ≤ 0` as soon as `κ ≤ K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Finset BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

variable {N : ℕ}

/-- Coordinate of `λ_k`. -/
def lamIdx (k : Fin N) : Fin (N + N) := finSumFinEquiv (Sum.inl k)

/-- Coordinate of `v_k`. -/
def massIdx (k : Fin N) : Fin (N + N) := finSumFinEquiv (Sum.inr k)

theorem lamIdx_injective : Function.Injective (lamIdx (N := N)) := by
  intro k m h; simpa [lamIdx] using h

theorem massIdx_injective : Function.Injective (massIdx (N := N)) := by
  intro k m h; simpa [massIdx] using h

theorem lamIdx_ne_massIdx (k m : Fin N) : lamIdx k ≠ massIdx m := by
  intro h
  have := congrArg Fin.val h
  simp [lamIdx, massIdx] at this
  omega

theorem sum_split (g : Fin (N + N) → ℝ) :
    ∑ i, g i = ∑ k, g (lamIdx k) + ∑ k, g (massIdx k) := by
  rw [← Equiv.sum_comp finSumFinEquiv g, Fintype.sum_sum_type]; rfl

/-- `e^{-Kt} Σ_k φ(λ_k) v_k`. -/
def tiltedMass (K : ℝ) (φ : ℝ → ℝ) (p : ℝ × (Fin (N + N) → ℝ)) : ℝ :=
  Real.exp (-(K * p.1)) * ∑ k, φ (p.2 (lamIdx k)) * p.2 (massIdx k)

/-- The covariance: `δ_kl/N` on the eigenvalue block, zero elsewhere. -/
def lamCov (N : ℕ) : Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
  Matrix.of fun i j => match finSumFinEquiv.symm i, finSumFinEquiv.symm j with
    | Sum.inl k, Sum.inl l => if k = l then 1 / (N : ℝ) else 0
    | _, _ => 0

theorem lamCov_lam_lam (k l : Fin N) :
    lamCov N (lamIdx k) (lamIdx l) = if k = l then 1 / (N : ℝ) else 0 := by
  simp [lamCov, lamIdx]

theorem lamCov_mass_left (k : Fin N) (j : Fin (N + N)) : lamCov N (massIdx k) j = 0 := by
  simp only [lamCov, massIdx, Matrix.of_apply, Equiv.symm_apply_apply]

theorem lamCov_mass_right (i : Fin (N + N)) (k : Fin N) : lamCov N i (massIdx k) = 0 := by
  simp only [lamCov, massIdx, Matrix.of_apply, Equiv.symm_apply_apply]
  split <;> simp_all

/-!
### Directional derivatives
-/

/-- `fderiv f p v` is the derivative at `0` of `s ↦ f (p + s • v)`. -/
theorem fderiv_apply_of_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {p v : E} {c : ℝ} (hf : DifferentiableAt ℝ f p)
    (hc : HasDerivAt (fun s : ℝ => f (p + s • v)) c 0) : fderiv ℝ f p v = c := by
  have hγ : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hf' : HasFDerivAt f (fderiv ℝ f p) (p + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℝ) hγ).unique hc

/-- Second derivatives as derivatives of first partials. -/
theorem fderiv_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {p : E} (hf : DifferentiableAt ℝ (fderiv ℝ f) p) (v w : E) :
    fderiv ℝ (fderiv ℝ f) p v w = fderiv ℝ (fun q => fderiv ℝ f q w) p v := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

/-!
### The partial derivatives of `tiltedMass`
-/

variable {K : ℝ} {φ φ1 φ2 : ℝ → ℝ}

theorem tiltedMass_contDiff (hc : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (tiltedMass (N := N) K φ) := by
  unfold tiltedMass
  refine ((contDiff_fst.const_smul K).neg.exp).mul ?_
  refine ContDiff.sum fun k _ => ?_
  exact (hc.comp ((contDiff_apply ℝ ℝ (lamIdx k)).comp contDiff_snd)).mul
    ((contDiff_apply ℝ ℝ (massIdx k)).comp contDiff_snd)

theorem line_time (p : ℝ × (Fin (N + N) → ℝ)) :
    HasDerivAt (fun s : ℝ => tiltedMass K φ (p + s • ((1 : ℝ), (0 : Fin (N + N) → ℝ))))
      (-K * tiltedMass K φ p) 0 := by
  have h : (fun s : ℝ => tiltedMass K φ (p + s • ((1 : ℝ), (0 : Fin (N + N) → ℝ)))) =
      fun s => Real.exp (-(K * (p.1 + s))) * ∑ k, φ (p.2 (lamIdx k)) * p.2 (massIdx k) := by
    funext s; simp [tiltedMass]
  rw [h]
  have h1 : HasDerivAt (fun s : ℝ => -(K * (p.1 + s))) (-K) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_add p.1).const_mul K).fun_neg
    simpa using this
  have := (h1.exp).mul_const (∑ k, φ (p.2 (lamIdx k)) * p.2 (massIdx k))
  refine this.congr_deriv ?_
  simp [tiltedMass]; ring

theorem line_lam (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (p : ℝ × (Fin (N + N) → ℝ)) (k : Fin N) :
    HasDerivAt (fun s : ℝ => tiltedMass K φ (p + s • ((0 : ℝ), Pi.single (lamIdx k) (1 : ℝ))))
      (Real.exp (-(K * p.1)) * (φ1 (p.2 (lamIdx k)) * p.2 (massIdx k))) 0 := by
  classical
  have h : (fun s : ℝ => tiltedMass K φ (p + s • ((0 : ℝ), Pi.single (lamIdx k) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ m, φ (p.2 (lamIdx m) + if m = k then s else 0) *
        p.2 (massIdx m) := by
    funext s
    simp only [tiltedMass, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.single_apply, Pi.single_apply, ite_eq_right (lamIdx_ne_massIdx k m).symm]
    by_cases hm : m = k
    · subst hm; simp
    · rw [ite_eq_right (fun e => hm (lamIdx_injective e)), ite_eq_right hm]; simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun m s =>
      φ (p.2 (lamIdx m) + if m = k then s else 0) * p.2 (massIdx m))
    (A' := fun m => if m = k then φ1 (p.2 (lamIdx m)) * p.2 (massIdx m) else 0) (x := 0)
    (fun m _ => by
      by_cases hm : m = k
      · simp only [hm, ite_true]
        have := (HasDerivAt.comp_const_add (p.2 (lamIdx k)) (0 : ℝ)
          (by simpa using hφ (p.2 (lamIdx k)))).mul_const (p.2 (massIdx k))
        simpa using this
      · simp only [hm, ite_false, add_zero]
        exact hasDerivAt_const _ _)
  refine (hs.const_mul (Real.exp (-(K * p.1)))).congr_deriv ?_
  simp

theorem line_mass (p : ℝ × (Fin (N + N) → ℝ)) (k : Fin N) :
    HasDerivAt (fun s : ℝ => tiltedMass K φ (p + s • ((0 : ℝ), Pi.single (massIdx k) (1 : ℝ))))
      (Real.exp (-(K * p.1)) * φ (p.2 (lamIdx k))) 0 := by
  classical
  have h : (fun s : ℝ => tiltedMass K φ (p + s • ((0 : ℝ), Pi.single (massIdx k) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * ∑ m, φ (p.2 (lamIdx m)) *
        (p.2 (massIdx m) + if m = k then s else 0) := by
    funext s
    simp only [tiltedMass, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.single_apply, Pi.single_apply, ite_eq_right (lamIdx_ne_massIdx m k)]
    by_cases hm : m = k
    · subst hm; simp
    · rw [ite_eq_right (fun e => hm (massIdx_injective e)), ite_eq_right hm]; simp
  rw [h]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (A := fun m s =>
      φ (p.2 (lamIdx m)) * (p.2 (massIdx m) + if m = k then s else 0))
    (A' := fun m => if m = k then φ (p.2 (lamIdx m)) else 0) (x := 0)
    (fun m _ => by
      by_cases hm : m = k
      · simp only [hm, ite_true]
        have := ((hasDerivAt_id' (0 : ℝ)).const_add (p.2 (massIdx k))).const_mul
          (φ (p.2 (lamIdx k)))
        simpa using this
      · simp only [hm, ite_false, add_zero]
        exact hasDerivAt_const _ _)
  refine (hs.const_mul (Real.exp (-(K * p.1)))).congr_deriv ?_
  simp

theorem tiltedMass_differentiableAt (hc : ContDiff ℝ 2 φ) (p : ℝ × (Fin (N + N) → ℝ)) :
    DifferentiableAt ℝ (tiltedMass (N := N) K φ) p :=
  (tiltedMass_contDiff hc).differentiable (by norm_num) p

theorem partialTime_tiltedMass (hc : ContDiff ℝ 2 φ) (p : ℝ × (Fin (N + N) → ℝ)) :
    partialTime (tiltedMass K φ) p = -K * tiltedMass K φ p :=
  fderiv_apply_of_line (tiltedMass_differentiableAt hc p) (line_time p)

theorem partialSpace_lam (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hc : ContDiff ℝ 2 φ)
    (p : ℝ × (Fin (N + N) → ℝ)) (k : Fin N) :
    partialSpace (tiltedMass K φ) p (lamIdx k) =
      Real.exp (-(K * p.1)) * (φ1 (p.2 (lamIdx k)) * p.2 (massIdx k)) :=
  fderiv_apply_of_line (tiltedMass_differentiableAt hc p) (line_lam hφ p k)

theorem partialSpace_mass (hc : ContDiff ℝ 2 φ) (p : ℝ × (Fin (N + N) → ℝ)) (k : Fin N) :
    partialSpace (tiltedMass K φ) p (massIdx k) = Real.exp (-(K * p.1)) * φ (p.2 (lamIdx k)) :=
  fderiv_apply_of_line (tiltedMass_differentiableAt hc p) (line_mass p k)

theorem partialSpace2_lam (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hc : ContDiff ℝ 2 φ)
    (p : ℝ × (Fin (N + N) → ℝ)) (k : Fin N) :
    partialSpace2 (tiltedMass K φ) p (lamIdx k) (lamIdx k) =
      Real.exp (-(K * p.1)) * (φ2 (p.2 (lamIdx k)) * p.2 (massIdx k)) := by
  classical
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (tiltedMass (N := N) K φ)) p :=
    ((tiltedMass_contDiff hc).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) p
  unfold partialSpace2
  rw [fderiv_fderiv_apply hdiff]
  set G : ℝ × (Fin (N + N) → ℝ) → ℝ :=
    fun q => Real.exp (-(K * q.1)) * (φ1 (q.2 (lamIdx k)) * q.2 (massIdx k)) with hG
  have hfun : (fun q => fderiv ℝ (tiltedMass K φ) q ((0 : ℝ), Pi.single (lamIdx k) (1 : ℝ))) = G :=
    funext fun q => partialSpace_lam hφ hc q k
  rw [hfun]
  have hd1 : Differentiable ℝ φ1 := fun z => (hφ1 z).differentiableAt
  have hGd : DifferentiableAt ℝ G p := by
    simp only [hG]
    fun_prop
  refine fderiv_apply_of_line hGd ?_
  have h : (fun s : ℝ => G (p + s • ((0 : ℝ), Pi.single (lamIdx k) (1 : ℝ)))) =
      fun s => Real.exp (-(K * p.1)) * (φ1 (p.2 (lamIdx k) + s) * p.2 (massIdx k)) := by
    funext s
    simp only [hG, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, Pi.single_eq_same,
      Pi.single_apply, ite_eq_right (lamIdx_ne_massIdx k k).symm, mul_one]
  rw [h]
  have := ((HasDerivAt.comp_const_add (p.2 (lamIdx k)) (0 : ℝ)
    (by simpa using hφ1 (p.2 (lamIdx k)))).mul_const (p.2 (massIdx k))).const_mul
      (Real.exp (-(K * p.1)))
  simpa using this

/-- **Itô drift of the tilted weighted mass** (`itoDrift`, covariance `lamCov`). -/
theorem itoDrift_tiltedMass (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hc : ContDiff ℝ 2 φ) (y : Fin (N + N) → ℝ) (t : ℝ≥0)
    (b : Fin (N + N) → ℝ) :
    itoDrift (tiltedMass K φ) y t b (lamCov N) =
      Real.exp (-(K * t)) * (-K * ∑ k, φ (y (lamIdx k)) * y (massIdx k) +
        ∑ k, b (lamIdx k) * (φ1 (y (lamIdx k)) * y (massIdx k)) +
        ∑ k, b (massIdx k) * φ (y (lamIdx k)) +
        (1 / 2 : ℝ) * ∑ k, (1 / (N : ℝ)) * (φ2 (y (lamIdx k)) * y (massIdx k))) := by
  classical
  unfold itoDrift
  rw [partialTime_tiltedMass hc, sum_split]
  simp only [partialSpace_lam hφ hc, partialSpace_mass hc]
  have h2 : ∑ i, ∑ j, lamCov N i j * partialSpace2 (tiltedMass K φ) ((t : ℝ), y) i j =
      ∑ k, (1 / (N : ℝ)) * (Real.exp (-(K * t)) * (φ2 (y (lamIdx k)) * y (massIdx k))) := by
    rw [sum_split]
    simp only [lamCov_mass_left, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_split]
    simp only [lamCov_mass_right, zero_mul, Finset.sum_const_zero, add_zero, lamCov_lam_lam,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [partialSpace2_lam hφ hφ1 hc]
  rw [h2]
  simp only [tiltedMass, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Itô bracket of the tilted weighted mass**. -/
theorem itoBracket_tiltedMass (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hc : ContDiff ℝ 2 φ)
    (y : Fin (N + N) → ℝ) (t : ℝ≥0) :
    itoBracket (tiltedMass K φ) y t (lamCov N) =
      ∑ k, (1 / (N : ℝ)) * (Real.exp (-(K * t)) * (φ1 (y (lamIdx k)) * y (massIdx k))) ^ 2 := by
  classical
  unfold itoBracket
  rw [sum_split]
  simp only [lamCov_mass_left, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_split]
  simp only [lamCov_mass_right, zero_mul, Finset.sum_const_zero, add_zero, lamCov_lam_lam,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, partialSpace_lam hφ hc]
  ring

/-- **Nonpositive tilted drift.** If the state has `v ≥ 0`, drift `b_{λ_k} = dysonDrift_k`,
`b_{v_k} = (L v)_k`, the weighted drift bound `Q ≤ κ S` holds and `κ ≤ K`, then `itoDrift ≤ 0`. -/
theorem itoDrift_tiltedMass_nonpos (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hc : ContDiff ℝ 2 φ) (hφ0 : ∀ z, 0 ≤ φ z)
    (y : Fin (N + N) → ℝ) (t : ℝ≥0) (L : Fin N → Fin N → ℝ)
    (hv : ∀ k, 0 ≤ y (massIdx k)) {κ : ℝ} (hκ : κ ≤ K)
    (hQ : ∑ k, φ (y (lamIdx k)) * ∑ l, L k l * y (massIdx l) +
        ∑ k, y (massIdx k) * (φ1 (y (lamIdx k)) * dysonDrift N (fun l => y (lamIdx l)) k +
          φ2 (y (lamIdx k)) / (2 * N)) ≤ κ * ∑ k, φ (y (lamIdx k)) * y (massIdx k))
    (b : Fin (N + N) → ℝ) (hbl : ∀ k, b (lamIdx k) = dysonDrift N (fun l => y (lamIdx l)) k)
    (hbm : ∀ k, b (massIdx k) = ∑ l, L k l * y (massIdx l)) :
    itoDrift (tiltedMass K φ) y t b (lamCov N) ≤ 0 := by
  rw [itoDrift_tiltedMass hφ hφ1 hc]
  simp only [hbl, hbm]
  have hS : 0 ≤ ∑ k, φ (y (lamIdx k)) * y (massIdx k) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hφ0 _) (hv k)
  have hrw : ∑ k, dysonDrift N (fun l => y (lamIdx l)) k * (φ1 (y (lamIdx k)) * y (massIdx k)) +
      ∑ k, (∑ l, L k l * y (massIdx l)) * φ (y (lamIdx k)) +
      (1 / 2 : ℝ) * ∑ k, (1 / (N : ℝ)) * (φ2 (y (lamIdx k)) * y (massIdx k)) =
      ∑ k, φ (y (lamIdx k)) * ∑ l, L k l * y (massIdx l) +
        ∑ k, y (massIdx k) * (φ1 (y (lamIdx k)) * dysonDrift N (fun l => y (lamIdx l)) k +
          φ2 (y (lamIdx k)) / (2 * N)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have : -K * ∑ k, φ (y (lamIdx k)) * y (massIdx k) +
      ∑ k, dysonDrift N (fun l => y (lamIdx l)) k * (φ1 (y (lamIdx k)) * y (massIdx k)) +
      ∑ k, (∑ l, L k l * y (massIdx l)) * φ (y (lamIdx k)) +
      (1 / 2 : ℝ) * ∑ k, (1 / (N : ℝ)) * (φ2 (y (lamIdx k)) * y (massIdx k)) ≤ 0 := by
    have := hrw ▸ hQ
    nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this

/-- **Nonpositive drift, pointwise in time, for the concrete weight.** At a state `y` whose
eigenvalue block satisfies the (relaxed) long-gap clauses, with `v ≥ 0` and any generator
dominated by the short one, the Itô drift of `e^{-Kt} Σ φ(λ_k) v_k` is `≤ 0` once `K` dominates
the explicit rate `κ` of `rlPhi_drift_le`. -/
theorem itoDrift_rlPhi_nonpos {ν E d R r₀ c₁ C₁ K : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R)
    (hρ : d + 2 * R ≤ r₀ / 8) (hc₁ : 0 < c₁) (ℓ : ℕ) (y : Fin (N + N) → ℝ) (t : ℝ≥0)
    (L : Fin N → Fin N → ℝ) (hv : ∀ k, 0 ≤ y (massIdx k))
    (hLS : ∀ k, ∑ l, L k l * y (massIdx l) ≤
      ∑ l, shortGen N (fun m => y (lamIdx m)) ℓ k l * y (massIdx l))
    (h1 : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * labelDist i j / N ≤ |y (lamIdx i) - y (lamIdx j)|)
    (h2 : ∀ i j : Fin N, labelDist i j < ℓ →
      min |y (lamIdx i) - E| |y (lamIdx j) - E| ≤ r₀ / 8 →
      |y (lamIdx i) - y (lamIdx j)| ≤ C₁ * ℓ / N)
    (hK : 2 * ℓ * (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
            Real.exp (ν * weightConst * (C₁ * ℓ / N)) / N +
          2 * (ν * weightConst) * (1 + Real.log N) / c₁ +
          (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N) ≤ K)
    (b : Fin (N + N) → ℝ) (hbl : ∀ k, b (lamIdx k) = dysonDrift N (fun l => y (lamIdx l)) k)
    (hbm : ∀ k, b (massIdx k) = ∑ l, L k l * y (massIdx l)) :
    itoDrift (tiltedMass K (rlPhi ν E d R)) y t b (lamCov N) ≤ 0 :=
  itoDrift_tiltedMass_nonpos (rlPhi_hasDerivAt hd hR) (rlPhi1_hasDerivAt hd hR)
    (rlPhi_contDiff hd hR) (fun z => (rlPhi_pos z).le) y t L hv hK
    (rlPhi_drift_le hν hd hR hρ hc₁ (fun m => y (lamIdx m)) ℓ L (fun k => y (massIdx k)) hv hLS
      h1 h2) b hbl hbm

end BlockBand.Palm.RelativeLocalization
