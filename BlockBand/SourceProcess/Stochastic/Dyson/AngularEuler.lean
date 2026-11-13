module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularLip

/-!
# Euler scheme for the eigenvalue equation driven by `W` (deterministic)

If `λ` is continuous on `[0, u]` with pairwise distinct coordinates, `r ↦ b(λ_r)` is continuous,
and `W_r = λ_r - ∫_0^r b(λ_x) dx`, then the explicit Euler scheme driven by the increments of
`W` on the uniform grid with `K + 1` steps,
`y_0 = W_0`, `y_{j+1} = y_j + (W_{t_{j+1}} - W_{t_j}) + h b(y_j)`,
converges to `λ_u` (`euler_tendsto`). Proof: uniform gap `δ` along the path, the `2/(δ/2)²`
Lipschitz bound of `b` near the path, and the discrete Gronwall estimate
`‖y_j - λ_{t_j}‖ ≤ j h ε (1 + hL)^j` with `ε` the grid oscillation of `b(λ)`. This gives the
eigenvalue path as a measurable functional of `(W_t)_t`, the only "strong uniqueness" input of
clause (b3).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open Filter Topology Set MeasureTheory
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale (rgrid rgrid_zero rgrid_last rgrid_succ
  rgrid_mono rgrid_mem eventually_mesh_le)

variable {N : ℕ}

/-- The Euler scheme driven by the increments of `w`. -/
def euler (N : ℕ) (w : ℕ → Fin N → ℝ) (h : ℝ) : ℕ → Fin N → ℝ
  | 0 => w 0
  | j + 1 => euler N w h j + (w (j + 1) - w j) + h • bv N (euler N w h j)

theorem pow_le_exp {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : (1 + x) ^ j ≤ Real.exp (x * j) := by
  calc (1 + x) ^ j ≤ Real.exp x ^ j :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) j
    _ = Real.exp (x * j) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **Convergence of the Euler scheme to the eigenvalue path.** -/
theorem euler_tendsto {lam W : ℝ → Fin N → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn lam (Icc 0 u)) (hd : ∀ r ∈ Icc 0 u, ∀ i j, i ≠ j → lam r i ≠ lam r j)
    (hbc : ContinuousOn (fun r => bv N (lam r)) (Icc 0 u))
    (hW : ∀ r ∈ Icc 0 u, ∀ i, W r i = lam r i - ∫ x in Ioc 0 r, bv N (lam x) i) :
    Tendsto (fun K : ℕ => euler N (fun j => W (rgrid 0 u K j)) (u / (K + 1)) (K + 1)) atTop
      (𝓝 (lam u)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap_lower hu hc hd
  set L : ℝ := 2 / (δ / 2) ^ 2
  have hL : 0 ≤ L := by positivity
  set M : ℝ := u * Real.exp (L * u) + 1
  have hM : 0 < M := by positivity
  refine Metric.tendsto_nhds.2 fun ε' hε' => ?_
  set ε : ℝ := min (ε' / 2) (δ / 8) / M
  have hε : 0 < ε := div_pos (lt_min (by linarith) (by linarith)) hM
  have hint : ∀ i, IntegrableOn (fun x => bv N (lam x) i) (Icc 0 u) := fun i =>
    ((continuous_apply i).comp_continuousOn hbc).integrableOn_Icc
  filter_upwards [eventually_mesh_le hu hbc hε] with K hK
  set h : ℝ := u / (K + 1)
  have hh : 0 ≤ h := by positivity
  set t : ℕ → ℝ := rgrid 0 u K
  set E := euler N (fun j => W (t j)) h
  have ht0 : t 0 = 0 := rgrid_zero 0 u K
  have htmem : ∀ j ≤ K + 1, t j ∈ Icc 0 u := fun j hj => rgrid_mem hu K hj
  have htsucc : ∀ j, t (j + 1) = t j + h := fun j => by
    simp only [t, h, rgrid_succ, sub_zero]
  have hglob : ∀ j ≤ K + 1, (j : ℝ) * h * ε * (1 + h * L) ^ j ≤ min (ε' / 2) (δ / 8) := by
    intro j hj
    have hjh : (j : ℝ) * h ≤ u := by
      have : (j : ℝ) ≤ K + 1 := by exact_mod_cast hj
      calc (j : ℝ) * h ≤ (K + 1) * h := mul_le_mul_of_nonneg_right this hh
        _ = u := by simp only [h]; field_simp
    have hpow : (1 + h * L) ^ j ≤ Real.exp (L * u) :=
      (pow_le_exp (mul_nonneg hh hL) j).trans (Real.exp_le_exp.2 (by nlinarith))
    calc (j : ℝ) * h * ε * (1 + h * L) ^ j ≤ u * ε * Real.exp (L * u) := by
          have := mul_le_mul hjh hpow (by positivity) hu
          nlinarith [hε.le]
      _ ≤ M * ε := by nlinarith [Real.exp_pos (L * u)]
      _ = min (ε' / 2) (δ / 8) := by simp only [ε]; field_simp
  -- one step of the scheme
  have hstep : ∀ j < K + 1, ∀ i, (E (j + 1) - lam (t (j + 1))) i = (E j - lam (t j)) i +
      h * (bv N (E j) i - bv N (lam (t j)) i) -
      ∫ x in (t j)..(t (j + 1)), (bv N (lam x) i - bv N (lam (t j)) i) := by
    intro j hj i
    have h1 := htmem j hj.le
    have h2 := htmem (j + 1) hj
    have hle : t j ≤ t (j + 1) := by rw [htsucc]; linarith
    have hi1 : IntervalIntegrable (fun x => bv N (lam x) i) volume 0 (t j) :=
      ((hint i).mono_set (by rw [uIcc_of_le h1.1]; exact Icc_subset_Icc le_rfl h1.2)).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x => bv N (lam x) i) volume (t j) (t (j + 1)) :=
      ((hint i).mono_set (by rw [uIcc_of_le hle]; exact Icc_subset_Icc h1.1 h2.2)).intervalIntegrable
    have hdiff : t (j + 1) - t j = h := by rw [htsucc]; ring
    rw [intervalIntegral.integral_sub hi2 intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, hdiff]
    have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    rw [intervalIntegral.integral_of_le h1.1, intervalIntegral.integral_of_le h2.1] at hadd
    simp only [Pi.sub_apply, E, euler, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hW _ h2 i, hW _ h1 i, ← hadd, intervalIntegral.integral_of_le hle]
    ring
  have hR : ∀ j < K + 1, ∀ i, |∫ x in (t j)..(t (j + 1)), (bv N (lam x) i - bv N (lam (t j)) i)|
      ≤ ε * h := by
    intro j hj i
    have hle : t j ≤ t (j + 1) := by rw [htsucc]; linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t j) (b := t (j + 1))
      (C := ε) (f := fun x => bv N (lam x) i - bv N (lam (t j)) i) (fun x hx => by
        rw [uIoc_of_le hle] at hx
        have hd := hK j hj x ⟨hx.1.le, hx.2⟩
        rw [Real.norm_eq_abs]
        exact (dist_le_pi_dist _ _ i).trans hd)
    have hdiff : t (j + 1) - t j = h := by rw [htsucc]; ring
    rwa [Real.norm_eq_abs, hdiff, abs_of_nonneg hh] at this
  -- discrete Gronwall
  have hgron : ∀ j ≤ K + 1, ‖E j - lam (t j)‖ ≤ (j : ℝ) * h * ε * (1 + h * L) ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      have : E 0 = lam (t 0) := by
        funext i; simp only [E, euler]; rw [hW _ (htmem 0 (Nat.zero_le _)) i, ht0]; simp
      simp [this]
    | succ j ih =>
      intro hj
      have hj' : j < K + 1 := hj
      have hej := ih hj'.le
      have hsmall : ‖E j - lam (t j)‖ ≤ δ / 4 :=
        hej.trans ((hglob j hj'.le).trans ((min_le_right _ _).trans (by linarith)))
      have hgj := hgap _ (htmem j hj'.le)
      have hlip := bv_lip (N := N) (by positivity : (0 : ℝ) < δ / 2) (gap_of_near hgj hsmall)
        (hgj.mono (by linarith))
      have hcoord : ∀ i, |(E (j + 1) - lam (t (j + 1))) i| ≤
          (1 + h * L) * ((j : ℝ) * h * ε * (1 + h * L) ^ j) + ε * h := by
        intro i
        rw [hstep j hj' i]
        have a1 : |(E j - lam (t j)) i| ≤ ‖E j - lam (t j)‖ := by
          have := norm_le_pi_norm (E j - lam (t j)) i; rwa [Real.norm_eq_abs] at this
        have a2 : |bv N (E j) i - bv N (lam (t j)) i| ≤ L * ‖E j - lam (t j)‖ := by
          have := norm_le_pi_norm (bv N (E j) - bv N (lam (t j))) i
          rw [Real.norm_eq_abs, Pi.sub_apply] at this; exact this.trans hlip
        calc |(E j - lam (t j)) i + h * (bv N (E j) i - bv N (lam (t j)) i) -
              ∫ x in (t j)..(t (j + 1)), (bv N (lam x) i - bv N (lam (t j)) i)|
            ≤ |(E j - lam (t j)) i| + h * |bv N (E j) i - bv N (lam (t j)) i| + ε * h := by
              have := abs_sub (((E j - lam (t j)) i + h * (bv N (E j) i - bv N (lam (t j)) i)))
                (∫ x in (t j)..(t (j + 1)), (bv N (lam x) i - bv N (lam (t j)) i))
              have h2 := abs_add_le ((E j - lam (t j)) i) (h * (bv N (E j) i - bv N (lam (t j)) i))
              rw [abs_mul, abs_of_nonneg hh] at h2
              linarith [hR j hj' i]
          _ ≤ ‖E j - lam (t j)‖ + h * (L * ‖E j - lam (t j)‖) + ε * h := by
              gcongr
          _ = (1 + h * L) * ‖E j - lam (t j)‖ + ε * h := by ring
          _ ≤ _ := by gcongr
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      refine (hcoord i).trans ?_
      have hp : 1 ≤ (1 + h * L) ^ (j + 1) := one_le_pow₀ (by nlinarith)
      have key : ε * h ≤ h * ε * ((1 + h * L) ^ j * (1 + h * L)) := by
        rw [← pow_succ]; nlinarith [hp, mul_nonneg hh hε.le]
      push_cast
      rw [pow_succ]
      linarith [key]
  have hfin := hgron (K + 1) le_rfl
  rw [show t (K + 1) = u from rgrid_last 0 u K] at hfin
  rw [dist_eq_norm]
  calc ‖E (K + 1) - lam u‖ ≤ ((K + 1 : ℕ) : ℝ) * h * ε * (1 + h * L) ^ (K + 1) := hfin
    _ ≤ min (ε' / 2) (δ / 8) := hglob (K + 1) le_rfl
    _ < ε' := (min_le_left _ _).trans_lt (by linarith)

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
