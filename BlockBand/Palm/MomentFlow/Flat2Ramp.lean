module

public import BlockBand.Palm.MomentFlow.Tail6
public import BlockBand.Palm.MomentFlow.MultiMatch

/-!
# The flattening ramp and its commutator with the short propagator

* `rampDist k₀ ξ`: the largest `|x - k₀|` over the particles `x` of `ξ` (computed on the sorted
  label list `occLabels ξ`); `rampDist_sub_le_occDist`: it is 1-Lipschitz for the ordered
  matching distance `occDist` (same sector).
* `ramp wd k₀ ξ = min 1 (max 0 (2 - 2 rampDist/wd))`: `ramp_eq_one` (distance `≤ wd/2`),
  `ramp_eq_zero` (distance `≥ wd`), `0 ≤ ramp ≤ 1`, `abs_ramp_sub_le` (Lipschitz constant `2/wd`).
* `commutator_row`: for a probability row `w`, `|Σ w a f - a(ξ) Σ w f| ≤ M (L + Σ_{ζ∉W} w)` when
  `|a(ζ) - a(ξ)| ≤ L` on `W` and `≤ 1` everywhere.
* **`flat2_commutator`**: `|U_{s,u}(Av f)(ξ) - Av(U_{s,u} f)(ξ)| ≤ (M+1)(2rR/wd + tail)`, with
  `Av f = a f + (1-a)`, `U_{s,u}` realised by the backward row `w` (`IsBackwardMomentFlow`), and
  the tail over `occBall r R ξ`, which is the finite-speed tail of `tail6_multi`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- `max_{x ∈ L} |x - k₀|` for a list of labels. -/
def listMaxDist (k₀ : ℕ) (L : List ℕ) : ℕ :=
  L.foldr (fun (x : ℕ) (acc : ℕ) => max (Int.natAbs ((x : ℤ) - (k₀ : ℤ))) acc) 0

/-- Distance of a configuration from the label `k₀`: the largest `|x - k₀|` over its particles. -/
def rampDist (k₀ : ℕ) (ξ : Occ N) : ℕ := listMaxDist k₀ (occLabels ξ)

/-- Matching sum of two label lists (the fold defining `occDist`). -/
def zipDist (L₁ L₂ : List ℕ) : ℕ :=
  (L₁.zip L₂).foldr (fun p acc => Int.natAbs ((p.1 : ℤ) - p.2) + acc) 0

theorem abs_natAbs_sub_natAbs_le (x y k : ℕ) :
    |((Int.natAbs ((x : ℤ) - k) : ℕ) : ℝ) - (Int.natAbs ((y : ℤ) - k) : ℕ)| ≤
      ((Int.natAbs ((x : ℤ) - y) : ℕ) : ℝ) := by
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast]
  have := abs_abs_sub_abs_le_abs_sub ((x : ℝ) - k) ((y : ℝ) - k)
  simpa using this

theorem abs_max_step {a b c d e f : ℝ} (h1 : |a - c| ≤ e) (h2 : |b - d| ≤ f) (he : 0 ≤ e)
    (hf : 0 ≤ f) : |max a b - max c d| ≤ e + f :=
  (abs_max_sub_max_le_max a b c d).trans
    (max_le (h1.trans (le_add_of_nonneg_right hf)) (h2.trans (le_add_of_nonneg_left he)))

theorem listMaxDist_sub_le (k₀ : ℕ) :
    ∀ L₁ L₂ : List ℕ, L₁.length = L₂.length →
      |(listMaxDist k₀ L₁ : ℝ) - listMaxDist k₀ L₂| ≤ zipDist L₁ L₂
  | [], [], _ => by simp [listMaxDist, zipDist]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: L₁, y :: L₂, h => by
    have ih := listMaxDist_sub_le k₀ L₁ L₂ (by simpa using h)
    simp only [listMaxDist, List.foldr_cons, zipDist, List.zip_cons_cons, Nat.cast_max,
      Nat.cast_add] at ih ⊢
    exact abs_max_step (abs_natAbs_sub_natAbs_le x y k₀) ih (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)

/-- **Ramp distance is 1-Lipschitz for the ordered matching distance.** -/
theorem rampDist_sub_le_occDist {r : ℕ} {ξ ζ : Occ N} (hξ : ξ ∈ sector N r)
    (hζ : ζ ∈ sector N r) (k₀ : ℕ) :
    |(rampDist k₀ ξ : ℝ) - rampDist k₀ ζ| ≤ occDist ξ ζ := by
  have h := listMaxDist_sub_le k₀ (occLabels ξ) (occLabels ζ)
    (by rw [length_occLabels hξ, length_occLabels hζ])
  exact h

/-- **The flattening ramp** `a_ξ`: `1` at ramp distance `≤ w/2`, linear, `0` at distance `≥ w`. -/
def ramp (w : ℝ) (k₀ : ℕ) (ξ : Occ N) : ℝ := min 1 (max 0 (2 - 2 * (rampDist k₀ ξ : ℝ) / w))

theorem ramp_nonneg (w : ℝ) (k₀ : ℕ) (ξ : Occ N) : 0 ≤ ramp w k₀ ξ :=
  le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (w : ℝ) (k₀ : ℕ) (ξ : Occ N) : ramp w k₀ ξ ≤ 1 := min_le_left _ _

theorem ramp_eq_one {w : ℝ} (hw : 0 < w) {k₀ : ℕ} {ξ : Occ N}
    (h : (rampDist k₀ ξ : ℝ) ≤ w / 2) : ramp w k₀ ξ = 1 := by
  unfold ramp
  have : 1 ≤ 2 - 2 * (rampDist k₀ ξ : ℝ) / w := by
    rw [le_sub_comm, div_le_iff₀ hw]; linarith
  rw [max_eq_right (by linarith), min_eq_left this]

theorem ramp_eq_zero {w : ℝ} (hw : 0 < w) {k₀ : ℕ} {ξ : Occ N}
    (h : w ≤ (rampDist k₀ ξ : ℝ)) : ramp w k₀ ξ = 0 := by
  unfold ramp
  have : 2 - 2 * (rampDist k₀ ξ : ℝ) / w ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hw]; linarith
  rw [max_eq_left this, min_eq_right zero_le_one]

/-- Lipschitz bound of the ramp: `|a_ξ - a_ζ| ≤ (2/w) |d(ξ) - d(ζ)|`. -/
theorem abs_ramp_sub_le {w : ℝ} (hw : 0 < w) (k₀ : ℕ) (ξ ζ : Occ N) :
    |ramp w k₀ ξ - ramp w k₀ ζ| ≤ 2 / w * |(rampDist k₀ ξ : ℝ) - rampDist k₀ ζ| := by
  unfold ramp
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
  rw [show (2 - 2 * (rampDist k₀ ξ : ℝ) / w) - (2 - 2 * (rampDist k₀ ζ : ℝ) / w) =
    -(2 / w * ((rampDist k₀ ξ : ℝ) - rampDist k₀ ζ)) by ring, abs_neg, abs_mul,
    abs_of_pos (by positivity : 0 < 2 / w)]

/-- On the ordered-matching ball of radius `ρ`, the ramp moves by at most `2ρ/w`. -/
theorem abs_ramp_sub_le_occDist {w : ℝ} (hw : 0 < w) (k₀ : ℕ) {r : ℕ} {ξ ζ : Occ N}
    (hξ : ξ ∈ sector N r) (hζ : ζ ∈ sector N r) :
    |ramp w k₀ ζ - ramp w k₀ ξ| ≤ 2 / w * (occDist ζ ξ : ℝ) :=
  (abs_ramp_sub_le hw k₀ ζ ξ).trans
    (mul_le_mul_of_nonneg_left (rampDist_sub_le_occDist hζ hξ k₀) (by positivity))

/-- **Generic commutator bound for a probability row.** -/
theorem commutator_row {S W : Finset (Occ N)} {w a f : Occ N → ℝ} {ξ : Occ N} {L M : ℝ}
    (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hw0 : ∀ ζ ∈ S, 0 ≤ w ζ) (hw1 : ∑ ζ ∈ S, w ζ = 1) (hM : ∀ ζ ∈ S, |f ζ| ≤ M)
    (hnear : ∀ ζ ∈ S, ζ ∈ W → |a ζ - a ξ| ≤ L) (hfar : ∀ ζ ∈ S, |a ζ - a ξ| ≤ 1) :
    |∑ ζ ∈ S, w ζ * (a ζ * f ζ) - a ξ * ∑ ζ ∈ S, w ζ * f ζ| ≤
      M * (L + ∑ ζ ∈ S \ W, w ζ) := by
  classical
  have e : ∑ ζ ∈ S, w ζ * (a ζ * f ζ) - a ξ * ∑ ζ ∈ S, w ζ * f ζ =
      ∑ ζ ∈ S, w ζ * ((a ζ - a ξ) * f ζ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ζ _ => by ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ζ => ζ ∈ W)]
  have hsd : S.filter (fun ζ => ζ ∉ W) = S \ W := by ext ζ; simp [Finset.mem_sdiff]
  rw [hsd]
  have hA : ∑ ζ ∈ S.filter (fun ζ => ζ ∈ W), |w ζ * ((a ζ - a ξ) * f ζ)| ≤ M * L := by
    calc ∑ ζ ∈ S.filter (fun ζ => ζ ∈ W), |w ζ * ((a ζ - a ξ) * f ζ)|
        ≤ ∑ ζ ∈ S.filter (fun ζ => ζ ∈ W), w ζ * (L * M) := by
          refine Finset.sum_le_sum fun ζ hζ => ?_
          obtain ⟨hζS, hζW⟩ := Finset.mem_filter.1 hζ
          rw [abs_mul, abs_of_nonneg (hw0 ζ hζS), abs_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hnear ζ hζS hζW) (hM ζ hζS)
            (abs_nonneg _) ((abs_nonneg _).trans (hnear ζ hζS hζW))) (hw0 ζ hζS)
      _ = L * M * ∑ ζ ∈ S.filter (fun ζ => ζ ∈ W), w ζ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ L * M * 1 := by
          have hL : 0 ≤ L * M := mul_nonneg hL0 hM0
          by_cases hW : (S.filter (fun ζ => ζ ∈ W)).Nonempty
          · refine mul_le_mul_of_nonneg_left ?_ hL
            rw [← hw1]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun ζ hζ _ => hw0 ζ hζ
          · rw [Finset.not_nonempty_iff_eq_empty] at hW; simp [hW]
            exact hL
      _ = M * L := by ring
  have hB : ∑ ζ ∈ S \ W, |w ζ * ((a ζ - a ξ) * f ζ)| ≤ M * ∑ ζ ∈ S \ W, w ζ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ζ hζ => ?_
    have hζS := (Finset.mem_sdiff.1 hζ).1
    rw [abs_mul, abs_of_nonneg (hw0 ζ hζS), abs_mul, mul_comm M]
    refine mul_le_mul_of_nonneg_left ?_ (hw0 ζ hζS)
    calc |a ζ - a ξ| * |f ζ| ≤ 1 * M :=
          mul_le_mul (hfar ζ hζS) (hM ζ hζS) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  linarith

/-- **Flattening commutator along the short propagator.** For a backward row `w` of a
symmetric nonnegative moment flow ending at `δ_ξ` (so `Σ_ζ w(s,ζ)f(ζ) = (U_{s,u}f)(ξ)`), the
flattening `Av f = a f + (1 - a)` with the ramp `a = ramp wd k₀` nearly commutes with `U_{s,u}`:
`|U(Av f)(ξ) - Av(U f)(ξ)| ≤ (M+1)(2rR/wd + Σ_{occDist(ξ,ζ) > rR} w(s,ζ))`. With the finite-speed
bound `tail6_multi` the tail is `≤ N^{-D}`, and `rR/wd = r N^ε ℓ/wd` is the `ℓ/w` gain. -/
theorem flat2_commutator {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ} (hsu : s ≤ u)
    (hc : ∀ v ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c v i j)
    (hsym : ∀ v ∈ Ioo s u, ∀ i j, c v i j = c v j i) {w : ℝ → Occ N → ℝ}
    (hw : IsBackwardMomentFlow c r s u w) {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (hwu : ∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) {f : Occ N → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hf : ∀ ζ ∈ sector N r, |f ζ| ≤ M) {wd : ℝ} (hwd : 0 < wd) (k₀ : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    |∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * f ζ + (1 - ramp wd k₀ ζ)) -
        (ramp wd k₀ ξ * ∑ ζ ∈ sector N r, w s ζ * f ζ + (1 - ramp wd k₀ ξ))| ≤
      (M + 1) * (2 / wd * ((r : ℝ) * R) + ∑ ζ ∈ sector N r \ occBall r R ξ, w s ζ) := by
  classical
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu⟩
  have hw0 : ∀ ζ ∈ sector N r, 0 ≤ w s ζ := fun ζ hζ =>
    hw.nonneg hc (fun ζ hζ => by rw [hwu ζ hζ]; unfold deltaCfg; split_ifs <;> norm_num) s hs ζ hζ
  have hw1 : ∑ ζ ∈ sector N r, w s ζ = 1 := by
    rw [hw.mass_eq hsym s hs, Finset.sum_congr rfl fun ζ hζ => hwu ζ hζ]
    simpa using sum_deltaCfg_mul hξ (fun _ => (1 : ℝ))
  have hL0 : 0 ≤ 2 / wd * ((r : ℝ) * R) := by positivity
  have hnear : ∀ ζ ∈ sector N r, ζ ∈ occBall r R ξ →
      |ramp wd k₀ ζ - ramp wd k₀ ξ| ≤ 2 / wd * ((r : ℝ) * R) := by
    intro ζ hζ hζW
    have hd : ¬ ((r : ℝ) * R < (occDist ξ ζ : ℝ)) := (Finset.mem_filter.1 hζW).2
    rw [abs_sub_comm]
    refine (abs_ramp_sub_le hwd k₀ ξ ζ).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact (rampDist_sub_le_occDist hξ hζ k₀).trans (not_lt.1 hd)
  have hfar : ∀ ζ ∈ sector N r, |ramp wd k₀ ζ - ramp wd k₀ ξ| ≤ 1 := fun ζ _ =>
    abs_sub_le_iff.2 ⟨by linarith [ramp_le_one wd k₀ ζ, ramp_nonneg wd k₀ ξ],
      by linarith [ramp_le_one wd k₀ ξ, ramp_nonneg wd k₀ ζ]⟩
  have h1 := commutator_row hL0 hM0 hw0 hw1 hf hnear hfar
  have h2 := commutator_row (f := fun _ => (1 : ℝ)) hL0 zero_le_one hw0 hw1
    (fun _ _ => by simp) hnear hfar
  have e : ∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * f ζ + (1 - ramp wd k₀ ζ)) -
      (ramp wd k₀ ξ * ∑ ζ ∈ sector N r, w s ζ * f ζ + (1 - ramp wd k₀ ξ)) =
      (∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * f ζ) -
        ramp wd k₀ ξ * ∑ ζ ∈ sector N r, w s ζ * f ζ) -
      (∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * 1) -
        ramp wd k₀ ξ * ∑ ζ ∈ sector N r, w s ζ * 1) := by
    have hsplit : ∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * f ζ + (1 - ramp wd k₀ ζ)) =
        ∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * f ζ) + ∑ ζ ∈ sector N r, w s ζ -
          ∑ ζ ∈ sector N r, w s ζ * (ramp wd k₀ ζ * 1) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ζ _ => by ring
    have h1' : ∑ ζ ∈ sector N r, w s ζ * 1 = 1 := by simpa using hw1
    rw [hsplit, hw1, h1']; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have := add_le_add h1 h2
  linarith

end BlockBand.Palm.MomentFlow
