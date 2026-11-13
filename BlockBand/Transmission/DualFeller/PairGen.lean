module

public import BlockBand.Transmission.DualFeller.Interface
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The coupled pair of lifted SDEs: generator of the squared distance

Deterministic; no measure appears. Two copies of the lifted SDE driven by the same noise form
the SDE on `P6 = ℝ⁶ × ℝ⁶` with drift `pairDrift D₀ (u, v) = (b u, b v)` and noise columns
`pairSigma D₀ a (u, v) = (σ_a u, σ_a v)`. For the squared Euclidean distance
`pairDist (u, v) = Σ_i (u_i − v_i)²`:
* `genAt_pairDist`: `𝓛 pairDist (u, v) = Σ_i [2Δ_i (b u − b v)_i + Σ_a (σ_a u − σ_a v)_i²]`
  (`Δ = u − v`), by the generator calculus `GenAt`;
* `exists_gen_pairDist_le`: for every radius `m` there is `K ≥ 0` with
  `𝓛 pairDist (u, v) ≤ K · pairDist (u, v)` whenever `‖u‖, ‖v‖ ≤ m` (sup norm). The proof uses
  that `b` and `σ_a` are `C¹` (`contDiff_liftDrift`, `contDiff_liftSigma`), hence Lipschitz
  on the convex compact ball.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open BlockBand.Transmission.DualLift BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.GramUniqueness

/-- The state space of the coupled pair. -/
abbrev P6 : Type := (Fin 6 → ℝ) × (Fin 6 → ℝ)

/-- Drift of the coupled pair. -/
def pairDrift (D0 : ℝ) (p : P6) : P6 := (liftDrift D0 p.1, liftDrift D0 p.2)

/-- Noise columns of the coupled pair (the same driver for both copies). -/
def pairSigma (D0 : ℝ) (a : Fin 5) (p : P6) : P6 := (liftSigma D0 a p.1, liftSigma D0 a p.2)

/-- Squared Euclidean distance of the two copies. -/
def pairDist (p : P6) : ℝ := ∑ i, (p.1 i - p.2 i) * (p.1 i - p.2 i)

theorem pairDist_nonneg (p : P6) : 0 ≤ pairDist p :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem contDiff_pairDist : ContDiff ℝ 2 pairDist := by
  unfold pairDist; fun_prop

theorem sq_norm_le_pairDist (p : P6) : ‖p.1 - p.2‖ ^ 2 ≤ pairDist p := by
  have h0 : 0 ≤ pairDist p := pairDist_nonneg p
  have h : ‖p.1 - p.2‖ ≤ √(pairDist p) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs, ← Real.sqrt_mul_self_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    exact Finset.single_le_sum (f := fun i => (p.1 i - p.2 i) * (p.1 i - p.2 i))
      (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)
  calc ‖p.1 - p.2‖ ^ 2 ≤ √(pairDist p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = pairDist p := Real.sq_sqrt h0

theorem pairDist_le_sq_norm (p : P6) : pairDist p ≤ 6 * ‖p.1 - p.2‖ ^ 2 := by
  unfold pairDist
  calc ∑ i, (p.1 i - p.2 i) * (p.1 i - p.2 i) ≤ ∑ _i : Fin 6, ‖p.1 - p.2‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_le_pi_norm (p.1 - p.2) i
        rw [Pi.sub_apply, Real.norm_eq_abs] at h
        nlinarith [abs_nonneg (p.1 i - p.2 i), abs_mul_abs_self (p.1 i - p.2 i)]
    _ = 6 * ‖p.1 - p.2‖ ^ 2 := by simp

variable {κ : Type*} [Fintype κ]

theorem GenAt.sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : E → E}
    {σ : κ → E → E} {y : E} {ι : Type*} (s : Finset ι) {g : ι → E → ℝ} {L : ι → ℝ}
    {Γ : ι → κ → ℝ} (H : ∀ i ∈ s, GenAt b σ (g i) y (L i) (Γ i)) :
    GenAt b σ (fun q => ∑ i ∈ s, g i q) y (∑ i ∈ s, L i) (fun a => ∑ i ∈ s, Γ i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GenAt.const (b := b) (σ := σ) (y := y) (0 : ℝ))
  | insert j s hj ih =>
    have h1 := H j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi => H i (Finset.mem_insert_of_mem hi)
    refine ((h1.add h2).congr_fun ?_).congr ?_ fun a => ?_
    · funext q; rw [Finset.sum_insert hj]
    · rw [Finset.sum_insert hj]
    · rw [Finset.sum_insert hj]

/-- Coordinate differences on the pair. -/
theorem genAt_diff (b : P6 → P6) (σ : κ → P6 → P6) (y : P6) (i : Fin 6) :
    GenAt b σ (fun q : P6 => q.1 i - q.2 i) y ((b y).1 i - (b y).2 i)
      (fun a => (σ a y).1 i - (σ a y).2 i) := by
  set ℓ : P6 →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _) with hℓ
  have hfun : (fun q : P6 => q.1 i - q.2 i) = fun q => ℓ q := by
    funext q; simp [hℓ]
  have hc : ContDiff ℝ 2 (fun q : P6 => ℓ q) := ℓ.contDiff
  refine ⟨hfun ▸ hc, ?_, fun a => ?_⟩
  · rw [hfun, sdeGenerator_eq_vecGen]
    have h := vecGen_clm b σ ℓ (G := fun q => q) contDiff_id y
    rw [h, vecGen_id]
    simp [hℓ]
  · rw [hfun, ℓ.fderiv]
    simp [hℓ]

/-- **Generator of the squared distance.** -/
theorem genAt_pairDist (b : P6 → P6) (σ : κ → P6 → P6) (y : P6) :
    GenAt b σ pairDist y (∑ i, (2 * (y.1 i - y.2 i) * ((b y).1 i - (b y).2 i) +
        ∑ a, ((σ a y).1 i - (σ a y).2 i) * ((σ a y).1 i - (σ a y).2 i)))
      (fun a => ∑ i, 2 * (y.1 i - y.2 i) * ((σ a y).1 i - (σ a y).2 i)) :=
  (GenAt.sum Finset.univ fun i _ => (genAt_diff b σ y i).sq).congr_fun rfl

/-- `C¹` maps are Lipschitz on sup-norm balls. -/
theorem exists_lip_ball {f : (Fin 6 → ℝ) → (Fin 6 → ℝ)} (hf : ContDiff ℝ 1 f) (m : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : Fin 6 → ℝ, ‖u‖ ≤ m → ‖v‖ ≤ m → ‖f u - f v‖ ≤ K * ‖u - v‖ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin 6 → ℝ) m).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  have hL := (convex_closedBall (0 : Fin 6 → ℝ) m).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (C := (max C 0).toNNReal) (fun x _ => hf.differentiable one_ne_zero x)
    (fun x hx => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
      exact (hC x hx).trans (le_max_left _ _))
  refine ⟨max C 0, le_max_right _ _, fun u v hu hv => ?_⟩
  have h := hL.dist_le_mul u (mem_closedBall_zero_iff.2 hu) v (mem_closedBall_zero_iff.2 hv)
  rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)] at h

/-- **The squared distance is a Lyapunov function of the pair on every ball.** -/
theorem exists_gen_pairDist_le {D0 : ℝ} (hD0 : 0 < D0) (m : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : P6, ‖y.1‖ ≤ m → ‖y.2‖ ≤ m →
      sdeGenerator (pairDrift D0) (pairSigma D0) pairDist y ≤ K * pairDist y := by
  obtain ⟨Kb, hKb0, hKb⟩ := exists_lip_ball ((contDiff_liftDrift D0).of_le le_top) m
  have hs := fun a : Fin 5 => exists_lip_ball ((contDiff_liftSigma hD0 a).of_le le_top) m
  choose Ks hKs0 hKs using hs
  set M : ℝ := Kb + ∑ a, Ks a with hM
  have hM0 : 0 ≤ M := add_nonneg hKb0 (Finset.sum_nonneg fun a _ => hKs0 a)
  have hKsM : ∀ a, Ks a ≤ M := fun a => by
    have := Finset.single_le_sum (f := Ks) (fun a _ => hKs0 a) (Finset.mem_univ a)
    linarith
  have hKbM : Kb ≤ M := by
    have := Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => hKs0 a
    linarith
  refine ⟨6 * (2 * M + 5 * M ^ 2), by positivity, fun y h1 h2 => ?_⟩
  rw [(genAt_pairDist (pairDrift D0) (pairSigma D0) y).gen]
  set d := ‖y.1 - y.2‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hcoord : ∀ (u v : Fin 6 → ℝ) (i : Fin 6), |u i - v i| ≤ ‖u - v‖ := fun u v i => by
    have := norm_le_pi_norm (u - v) i
    rwa [Pi.sub_apply, Real.norm_eq_abs] at this
  have hterm : ∀ i : Fin 6, 2 * (y.1 i - y.2 i) * ((pairDrift D0 y).1 i - (pairDrift D0 y).2 i) +
      ∑ a, ((pairSigma D0 a y).1 i - (pairSigma D0 a y).2 i) *
        ((pairSigma D0 a y).1 i - (pairSigma D0 a y).2 i) ≤ (2 * M + 5 * M ^ 2) * d ^ 2 := by
    intro i
    have hb : |(pairDrift D0 y).1 i - (pairDrift D0 y).2 i| ≤ M * d :=
      (hcoord _ _ i).trans ((hKb _ _ h1 h2).trans (mul_le_mul_of_nonneg_right hKbM hd0))
    have hσ : ∀ a, |(pairSigma D0 a y).1 i - (pairSigma D0 a y).2 i| ≤ M * d := fun a =>
      (hcoord _ _ i).trans ((hKs a _ _ h1 h2).trans (mul_le_mul_of_nonneg_right (hKsM a) hd0))
    have hΔ : |y.1 i - y.2 i| ≤ d := hcoord _ _ i
    have e1 : 2 * (y.1 i - y.2 i) * ((pairDrift D0 y).1 i - (pairDrift D0 y).2 i) ≤
        2 * M * d ^ 2 := by
      have := abs_mul (y.1 i - y.2 i) ((pairDrift D0 y).1 i - (pairDrift D0 y).2 i)
      have h3 : |(y.1 i - y.2 i) * ((pairDrift D0 y).1 i - (pairDrift D0 y).2 i)| ≤ d * (M * d) :=
        this ▸ mul_le_mul hΔ hb (abs_nonneg _) hd0
      nlinarith [le_abs_self ((y.1 i - y.2 i) * ((pairDrift D0 y).1 i - (pairDrift D0 y).2 i))]
    have e2 : ∑ a, ((pairSigma D0 a y).1 i - (pairSigma D0 a y).2 i) *
        ((pairSigma D0 a y).1 i - (pairSigma D0 a y).2 i) ≤ ∑ _a : Fin 5, (M * d) ^ 2 := by
      refine Finset.sum_le_sum fun a _ => ?_
      have h := hσ a
      have h0 : 0 ≤ M * d := mul_nonneg hM0 hd0
      nlinarith [abs_nonneg ((pairSigma D0 a y).1 i - (pairSigma D0 a y).2 i),
        abs_mul_abs_self ((pairSigma D0 a y).1 i - (pairSigma D0 a y).2 i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e2
    have e3 : ((5 : ℕ) : ℝ) * (M * d) ^ 2 = 5 * M ^ 2 * d ^ 2 := by push_cast; ring
    have e4 : (2 * M + 5 * M ^ 2) * d ^ 2 = 2 * M * d ^ 2 + 5 * M ^ 2 * d ^ 2 := by ring
    linarith
  calc _ ≤ ∑ _i : Fin 6, (2 * M + 5 * M ^ 2) * d ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = 6 * (2 * M + 5 * M ^ 2) * d ^ 2 := by simp; ring
    _ ≤ 6 * (2 * M + 5 * M ^ 2) * pairDist y :=
        mul_le_mul_of_nonneg_left (sq_norm_le_pairDist y) (by positivity)

end BlockBand.Transmission.DualFeller
