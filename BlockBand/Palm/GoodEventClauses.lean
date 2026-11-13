module

public import BlockBand.Palm.GoodEventCount

/-!
# Good spectral event: the six clauses at one time from the counts at a nearby mesh time

Deterministic, for sequences. `lam'` is the increasing spectrum at a mesh time where the fixed-time
upper count (`2NhC₀((y-x)/h + 2)` on every `[x,y]`) and the fixed-time centred lower count
(`(v₀³/64) N min(L,1)` for `|x₀ - E| ≤ r₀/2`, `L ≥ 16h/v₀²`) hold; `lam` is the increasing spectrum
at a time with `|lam i - lam' i| ≤ h` (Weyl). Then `lam` satisfies: the global upper count with
constant `8C₀`, the bulk lower count on `[E - r₀/4, E + r₀/4]` with `c' = (v₀³/64) min(1/4, 2/r₀)`
for lengths `≥ 64h/v₀² + 4h`, the two long-gap bounds (`c₁ d(i,j)/N ≤ |λ_i - λ_j|` with
`c₁ = min(1/(16C₀), c')`, and the companion upper bound with `C₁ = 1 + 1/c'`), the lower count of
the good event, and both bounds on the total long coupling (`4/c₁²`, `c'²/9`), under the scale
conditions `16 C₀ N h ≤ ℓ`, `64h/v₀² + 4h ≤ ℓ/N` (and the two variants), `3ℓ/(c'N) ≤ r₀/8`,
`(1 + 1/c')ℓ/N ≤ r₀/8`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- The bulk lower-count constant `c' = (v₀³/64) min(1/4, 2/r₀)`. -/
def goodC' (v₀ r₀ : ℝ) : ℝ := v₀ ^ 3 / 64 * min (1 / 4) (2 / r₀)

/-- The long-gap constant `c₁ = min(1/(16 C₀), c')`. -/
def goodc₁ (C₀ v₀ r₀ : ℝ) : ℝ := min (1 / (16 * C₀)) (goodC' v₀ r₀)

theorem goodC'_pos {v₀ r₀ : ℝ} (hv₀ : 0 < v₀) (hr₀ : 0 < r₀) : 0 < goodC' v₀ r₀ := by
  unfold goodC'
  have : 0 < min (1 / 4 : ℝ) (2 / r₀) := lt_min (by norm_num) (by positivity)
  positivity

theorem goodc₁_pos {C₀ v₀ r₀ : ℝ} (hC₀ : 0 < C₀) (hv₀ : 0 < v₀) (hr₀ : 0 < r₀) :
    0 < goodc₁ C₀ v₀ r₀ :=
  lt_min (by positivity) (goodC'_pos hv₀ hr₀)

/-- Upper count at the time of `lam`, from the mesh time. -/
theorem upper_of_mesh (hN : 0 < N) {C₀ h : ℝ} (hC₀ : 0 < C₀) (hh : 0 < h)
    (lam lam' : Fin N → ℝ) (hW : ∀ i, |lam i - lam' i| ≤ h)
    (hU' : ∀ x y, x ≤ y → ((Finset.univ.filter fun i => lam' i ∈ Set.Icc x y).card : ℝ) ≤
      2 * N * h * C₀ * ((y - x) / h + 2))
    (x y : ℝ) (hxy : x ≤ y) :
    ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ) ≤ 8 * C₀ * N * ((y - x) + h) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ) ≤
      ((Finset.univ.filter fun i => lam' i ∈ Set.Icc (x - h) (y + h)).card : ℝ) := by
    exact_mod_cast count_upper_transfer lam lam' hW x y
  have h2 := hU' (x - h) (y + h) (by linarith)
  have h3 : 2 * N * h * C₀ * ((y + h - (x - h)) / h + 2) = 2 * C₀ * N * ((y - x) + 4 * h) := by
    field_simp; ring
  rw [h3] at h2
  have : 2 * C₀ * N * ((y - x) + 4 * h) ≤ 8 * C₀ * N * ((y - x) + h) := by
    have : 0 ≤ y - x := by linarith
    nlinarith [mul_pos hC₀ hNr]
  linarith

/-- Lower count on the internal window at the time of `lam`, from the mesh time. -/
theorem lower_of_mesh (hN : 0 < N) {v₀ r₀ h E : ℝ} (hv₀ : 0 < v₀) (hr₀ : 0 < r₀) (hh : 0 < h)
    (lam lam' : Fin N → ℝ) (hW : ∀ i, |lam i - lam' i| ≤ h)
    (hL' : ∀ x₀ L, |x₀ - E| ≤ r₀ / 2 → 16 * h / v₀ ^ 2 ≤ L →
      v₀ ^ 3 / 64 * N * min L 1 ≤
        ((Finset.univ.filter fun k => |lam' k - x₀| ≤ L).card : ℝ))
    (x y : ℝ) (hx : E - r₀ / 4 ≤ x) (hy : y ≤ E + r₀ / 4) (hlen : 64 * h / v₀ ^ 2 + 4 * h ≤ y - x) :
    goodC' v₀ r₀ * N * (y - x) ≤ ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv2 : 0 < v₀ ^ 2 := by positivity
  set x₀ := (x + y) / 2 with hx₀
  set L := (y - x) / 2 - h with hLdef
  have h64 : 0 ≤ 64 * h / v₀ ^ 2 := by positivity
  have hyx4 : 4 * h ≤ y - x := by linarith
  have hL4 : (y - x) / 4 ≤ L := by rw [hLdef]; linarith
  have hLf : 16 * h / v₀ ^ 2 ≤ L := by
    have : 16 * h / v₀ ^ 2 = (64 * h / v₀ ^ 2) / 4 := by ring
    rw [this]; linarith
  have hxE : |x₀ - E| ≤ r₀ / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hcnt := hL' x₀ L hxE hLf
  have hset : (Finset.univ.filter fun k => |lam' k - x₀| ≤ L) =
      (Finset.univ.filter fun k => lam' k ∈ Set.Icc (x + h) (y - h)) := by
    apply Finset.filter_congr
    intro k _
    rw [abs_le, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [hset] at hcnt
  have htr : ((Finset.univ.filter fun k => lam' k ∈ Set.Icc (x + h) (y - h)).card : ℝ) ≤
      ((Finset.univ.filter fun i => lam i ∈ Set.Icc x y).card : ℝ) := by
    exact_mod_cast count_lower_transfer lam lam' hW x y
  have hmin : min (1 / 4) (2 / r₀) * (y - x) ≤ min L 1 := by
    apply le_min
    · calc min (1 / 4) (2 / r₀) * (y - x) ≤ 1 / 4 * (y - x) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
        _ ≤ L := by linarith
    · have hyx : y - x ≤ r₀ / 2 := by linarith
      calc min (1 / 4) (2 / r₀) * (y - x) ≤ 2 / r₀ * (y - x) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ ≤ 2 / r₀ * (r₀ / 2) := mul_le_mul_of_nonneg_left hyx (by positivity)
        _ = 1 := by field_simp
  have : goodC' v₀ r₀ * N * (y - x) ≤ v₀ ^ 3 / 64 * N * min L 1 := by
    unfold goodC'
    have := mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ v₀ ^ 3 / 64 * N)
    nlinarith
  linarith

/-- **The six clauses at one time** (deterministic part; clause 5 is separate). -/
theorem clauses_of_mesh (hN : 0 < N) {C₀ v₀ r₀ h E : ℝ} {ℓ : ℕ}
    (hC₀ : 0 < C₀) (hv₀ : 0 < v₀) (hr₀ : 0 < r₀) (hh : 0 < h)
    (lam lam' : Fin N → ℝ) (hmono : Monotone lam)
    (hW : ∀ i, |lam i - lam' i| ≤ h)
    (hU' : ∀ x y, x ≤ y → ((Finset.univ.filter fun i => lam' i ∈ Set.Icc x y).card : ℝ) ≤
      2 * N * h * C₀ * ((y - x) / h + 2))
    (hL' : ∀ x₀ L, |x₀ - E| ≤ r₀ / 2 → 16 * h / v₀ ^ 2 ≤ L →
      v₀ ^ 3 / 64 * N * min L 1 ≤
        ((Finset.univ.filter fun k => |lam' k - x₀| ≤ L).card : ℝ))
    (hℓ1 : 1 ≤ ℓ) (hsc1 : 16 * C₀ * N * h ≤ ℓ)
    (hsc3 : 64 * h / v₀ ^ 2 + 4 * h ≤ ℓ / N)
    (hsc3' : 64 * h / v₀ ^ 2 + 4 * h ≤ ℓ / (goodC' v₀ r₀ * N))
    (hsc3'' : 64 * h / v₀ ^ 2 + 4 * h ≤ 3 / goodC' v₀ r₀ * ℓ / N)
    (hsc4 : (1 + 1 / goodC' v₀ r₀) * ℓ / N ≤ r₀ / 8)
    (hsc4' : 3 / goodC' v₀ r₀ * ℓ / N ≤ r₀ / 8) :
    (∀ i j : Fin N, ℓ ≤ labelDist i j →
      goodc₁ C₀ v₀ r₀ * (labelDist i j : ℝ) / N ≤ |lam i - lam j|) ∧
    (∀ i j : Fin N, labelDist i j < ℓ → min |lam i - E| |lam j - E| ≤ r₀ / 8 →
      |lam i - lam j| ≤ (1 + 1 / goodC' v₀ r₀) * ℓ / N) ∧
    (∀ x y : ℝ, x ≤ y →
      ((Finset.univ.filter fun i : Fin N => lam i ∈ Set.Icc x y).card : ℝ) ≤
        8 * C₀ * N * ((y - x) + h)) ∧
    (∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
      goodc₁ C₀ v₀ r₀ * N * (y - x) ≤
        ((Finset.univ.filter fun i : Fin N => lam i ∈ Set.Icc x y).card : ℝ)) ∧
    (∀ i : Fin N,
      ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m), ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹ ≤
        4 / goodc₁ C₀ v₀ r₀ ^ 2 * N / ℓ ∧
      (|lam i - E| ≤ r₀ / 8 → goodC' v₀ r₀ ^ 2 / 9 * N / ℓ ≤
        ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist i m),
          ((N : ℝ) * (lam i - lam m) ^ 2)⁻¹)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' := goodC'_pos hv₀ hr₀
  have hc₁ := goodc₁_pos hC₀ hv₀ hr₀
  have hup := upper_of_mesh hN hC₀ hh lam lam' hW hU'
  have hlowW := lower_of_mesh hN hv₀ hr₀ hh lam lam' hW hL' (E := E)
  have hc₁16 : goodc₁ C₀ v₀ r₀ ≤ 1 / (16 * C₀) := min_le_left _ _
  have hc₁c' : goodc₁ C₀ v₀ r₀ ≤ goodC' v₀ r₀ := min_le_right _ _
  -- the long-gap lower bound
  have hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      goodc₁ C₀ v₀ r₀ * (labelDist i j : ℝ) / N ≤ |lam i - lam j| := by
    intro i j hij
    have hg := longGap_of_upper lam hmono (by positivity : 0 < 8 * C₀) hN hup i j
    have hd : (ℓ : ℝ) ≤ labelDist i j := by exact_mod_cast hij
    set d : ℝ := (labelDist i j : ℝ) with hd'
    have hd0 : 0 ≤ d := by positivity
    have e1 : goodc₁ C₀ v₀ r₀ * d / N ≤ d / (16 * C₀ * N) := by
      rw [div_le_div_iff₀ hNr (by positivity)]
      have := mul_le_mul_of_nonneg_right hc₁16 hd0
      have h2 : 1 / (16 * C₀) * d * (16 * C₀ * N) = d * N := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 16 * C₀ * N)]
    have e2 : h ≤ d / (16 * C₀ * N) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have e3 : d / (16 * C₀ * N) + d / (16 * C₀ * N) ≤ (d + 1) / (8 * C₀ * N) := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hC₀ hNr]
    linarith
  refine ⟨hgap, ?_, ?_, ?_, ?_⟩
  · intro i j hij hE
    exact shortGap_of_lower lam hmono hc' hN hlowW hsc3' hsc4 i j hij hE
  · exact hup
  · intro x y hx hy hlen
    have hxy : 64 * h / v₀ ^ 2 + 4 * h ≤ y - x := hsc3.trans hlen
    have h1 := hlowW x y (by linarith) (by linarith) hxy
    have h0 : 0 ≤ y - x := le_trans (by positivity) hxy
    have : goodc₁ C₀ v₀ r₀ * N * (y - x) ≤ goodC' v₀ r₀ * N * (y - x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁c' hNr.le) h0
    linarith
  · intro i
    exact ⟨longCoupling_sum_le lam hc₁ hℓ1 hN hgap i,
      fun hi => longCoupling_sum_ge lam hmono hc' hc₁ hℓ1 hN hlowW hgap hsc4' hsc3'' i hi⟩

end BlockBand.Palm.GoodEvent
