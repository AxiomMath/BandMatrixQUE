module

public import BlockBand.Palm.GoodEventClauses
public import BlockBand.Palm.GoodEventLower
public import BlockBand.Palm.GoodEventUpper
public import BlockBand.Palm.GoodEventBrownian
public import BlockBand.Palm.GoodEventNumeric
public import BlockBand.Palm.CoarseRelativeHolds

/-!
# Good spectral event: deterministic assembly on the mesh events

`GoodAt` is the conjunction of the six clauses of the contract at one time `s`.
`good_of_events` is deterministic: if the initial matrix is Hermitian, the dyadic chaining
event of the Brownian part holds, and at every dyadic mesh time `s_j = a + j t 2^{-m}` the
normalized matrix `G_{s_j}` avoids the upper-mesh failure set `upperBad`, the coarse local-law
failure set `localBad` (the bad set of `CoarseRelativeContract` with no directions) and the norm
failure set `{R₂ < opB G}`, then `GoodAt` holds at every `s ∈ [a, c]`, under explicit scale
conditions. Transfer from `s_j` to `s` is Weyl's inequality with the chaining modulus.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Palm.CoarseRelative BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

variable {N : ℕ}

/-- The six clauses of `SpectralGoodEventContract` at one time `s`. -/
def GoodAt (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (E r₀ c₁ C₁ C b₀ : ℝ)
    (ℓ : ℕ) (h t s : ℝ) : Prop :=
  (∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j|) ∧
  (∀ i j : Fin N, labelDist i j < ℓ →
      min |flowEigenvalue F a ω s i - E| |flowEigenvalue F a ω s j - E| ≤ r₀ / 8 →
      |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| ≤ C₁ * ℓ / N) ∧
  (∀ x y : ℝ, x ≤ y →
      ((Finset.univ.filter fun i : Fin N =>
          flowEigenvalue F a ω s i ∈ Set.Icc x y).card : ℝ) ≤ C * N * ((y - x) + h)) ∧
  (∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
      c₁ * N * (y - x) ≤
        ((Finset.univ.filter fun i : Fin N =>
          flowEigenvalue F a ω s i ∈ Set.Icc x y).card : ℝ)) ∧
  (∀ i : Fin N, longCoupling F a ω ℓ s i ≤ C * N / ℓ ∧
      (|flowEigenvalue F a ω s i - E| ≤ r₀ / 8 → b₀ * N / ℓ ≤ longCoupling F a ω ℓ s i)) ∧
  (∀ x : Fin N → ℂ, l2Norm ((flowMatrix F a ω s - flowMatrix F a ω a) *ᵥ x) ≤
      C * Real.sqrt t * l2Norm x)

/-- Upper-mesh failure at time `σ`: some mesh point `kh`, `|k| ≤ K₀ + 1`, has
`Im⟨(F + √σ G - kh - ih)⁻¹⟩ > 3 + 1/σ`. -/
def upperBad (F : Matrix (Fin N) (Fin N) ℂ) (σ h : ℝ) (K₀ : ℕ) : Set (Matrix (Fin N) (Fin N) ℂ) :=
  {G | ∃ k : ℤ, |k| ≤ (K₀ : ℤ) + 1 ∧
    3 + 1 / σ < ((N : ℂ)⁻¹ * (coarseResolvent F G σ ⟨(k : ℝ) * h, h⟩).trace).im}

/-- The failure set of `CoarseRelativeContract` at time `σ` with no directions. -/
def localBad (F : Matrix (Fin N) (Fin N) ℂ) (E r₀ σ : ℝ) : Set (Matrix (Fin N) (Fin N) ℂ) :=
  {G | ∃ x η : ℝ, |x - E| ≤ r₀ / 2 ∧ (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η ∧ η ≤ 1 ∧
    let z : ℂ := ⟨x, η⟩
    let R := (F + (Real.sqrt σ : ℂ) • G - z • 1)⁻¹
    (N : ℝ) ^ (-(1 / 3 : ℝ)) < ‖(N : ℂ)⁻¹ * R.trace - freshDyson F σ z‖ ∨
      ∃ q ∈ (∅ : Finset (Fin N → ℂ)), (N : ℝ) ^ (-(1 / 3 : ℝ)) * (star q ⬝ᵥ (freshM F σ z *ᵥ q)).im <
        ‖star q ⬝ᵥ ((R - freshM F σ z) *ᵥ q)‖}

theorem hermitianBrownian_isHermitian (B : FlowNoise N) (u : ℝ) :
    (hermitianBrownian B u).IsHermitian := by
  rw [hermitianBrownian_eq_gueCoord]
  exact gueCoord_isHermitian _ _

theorem flowMatrix_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) : (flowMatrix F a ω σ).IsHermitian := by
  unfold flowMatrix
  exact (hF.add hω).add (hermitianBrownian_isHermitian _ _)

theorem flowMatrix_sub (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ σ' : ℝ) :
    flowMatrix F a ω σ - flowMatrix F a ω σ' =
      hermitianBrownian ω.2 (σ - a) - hermitianBrownian ω.2 (σ' - a) := by
  unfold flowMatrix
  abel

/-- A point of `[0,T]` lies in a dyadic cell of level `m`. -/
theorem exists_cell {T u : ℝ} (hT : 0 < T) (hu0 : 0 ≤ u) (huT : u ≤ T) (m : ℕ) :
    ∃ k : ℕ, k < 2 ^ m ∧ (k : ℝ) * T / 2 ^ m ≤ u ∧ u ≤ ((k : ℝ) + 1) * T / 2 ^ m := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  set r := u * 2 ^ m / T with hr
  have hr0 : 0 ≤ r := by positivity
  have hrle : r ≤ 2 ^ m := by
    rw [hr, div_le_iff₀ hT]; nlinarith
  by_cases hfl : ⌊r⌋₊ < 2 ^ m
  · refine ⟨⌊r⌋₊, hfl, ?_, ?_⟩
    · have := Nat.floor_le hr0
      rw [div_le_iff₀ h2]
      have : (⌊r⌋₊ : ℝ) * T ≤ r * T := mul_le_mul_of_nonneg_right this hT.le
      rw [hr] at this
      field_simp at this
      linarith
    · have := Nat.lt_floor_add_one r
      rw [le_div_iff₀ h2]
      have : r * T ≤ ((⌊r⌋₊ : ℝ) + 1) * T := mul_le_mul_of_nonneg_right this.le hT.le
      rw [hr] at this
      field_simp at this
      linarith
  · push Not at hfl
    have hge : (2 ^ m : ℝ) ≤ r := by
      have := Nat.floor_le hr0
      have : ((2 ^ m : ℕ) : ℝ) ≤ (⌊r⌋₊ : ℝ) := by exact_mod_cast hfl
      push_cast at this
      linarith
    have hr2 : r = 2 ^ m := le_antisymm hrle hge
    have huT' : u = T := by
      rw [hr, div_eq_iff hT.ne'] at hr2
      have : u * 2 ^ m = T * 2 ^ m := by linarith
      exact mul_right_cancel₀ h2.ne' this
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    refine ⟨2 ^ m - 1, Nat.sub_lt (by positivity) one_pos, ?_, ?_⟩
    · rw [div_le_iff₀ h2, huT']
      have : ((2 ^ m - 1 : ℕ) : ℝ) ≤ 2 ^ m := by
        rw [Nat.cast_sub hpos]; push_cast; linarith
      nlinarith
    · rw [le_div_iff₀ h2, huT']
      have : ((2 ^ m - 1 : ℕ) : ℝ) + 1 = 2 ^ m := by
        rw [Nat.cast_sub hpos]; push_cast; ring
      rw [this, mul_comm]

/-- **Deterministic assembly.** On the mesh events, every time `s ∈ [a, c]` is good. -/
theorem good_of_events (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {a t K₁ R₂ : ℝ} {ℓ m K₀ : ℕ} (ht : 0 < t) (hat : a = c - t) (has₀ : c - s₀ ≤ a)
    (hK₁ : 0 ≤ K₁)
    (hmod : K₁ * Real.sqrt t * chainRatio ^ m / (1 - chainRatio) ≤ (N : ℝ) ^ (-(1 / 100 : ℝ)))
    (hK₀ : (N : ℝ) ^ A + R₂ ≤ (K₀ : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)))
    (hℓ1 : 1 ≤ ℓ) (hsc1 : 16 * (3 + 2 / c) * N * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ ℓ)
    (hsc3 : 64 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 + 4 * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ ℓ / N)
    (hsc3' : 64 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 + 4 * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤
      ℓ / (goodC' v₀ r₀ * N))
    (hsc3'' : 64 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 + 4 * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤
      3 / goodC' v₀ r₀ * ℓ / N)
    (hsc4 : (1 + 1 / goodC' v₀ r₀) * ℓ / N ≤ r₀ / 8)
    (hsc4' : 3 / goodC' v₀ r₀ * ℓ / N ≤ r₀ / 8)
    (hsm : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ v₀ / 2) (hsm' : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ v₀⁻¹)
    (hh1 : 16 * (N : ℝ) ^ (-(1 / 100 : ℝ)) / v₀ ^ 2 ≤ 1)
    {ω : FlowSample N} (hω1 : ω.1.IsHermitian) (hω2 : ChainGood K₁ t ω.2)
    (hj : ∀ j : ℕ, j < 2 ^ m →
      flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω ∉
          upperBad F (a + (j : ℝ) * t / 2 ^ m) ((N : ℝ) ^ (-(1 / 100 : ℝ))) K₀ ∧
        flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω ∉ localBad F E r₀ (a + (j : ℝ) * t / 2 ^ m) ∧
        ¬ R₂ < opB (flowNormalized a (a + (j : ℝ) * t / 2 ^ m) ω))
    {C : ℝ} (hC8 : 8 * (3 + 2 / c) ≤ C) (hC4 : 4 / goodc₁ (3 + 2 / c) v₀ r₀ ^ 2 ≤ C)
    (hCK : K₁ / (1 - chainRatio) ≤ C) :
    ∀ s ∈ Set.Icc a c, GoodAt F a ω E r₀ (goodc₁ (3 + 2 / c) v₀ r₀) (1 + 1 / goodC' v₀ r₀) C
      (goodC' v₀ r₀ ^ 2 / 9) ℓ ((N : ℝ) ^ (-(1 / 100 : ℝ))) t s := by
  intro s hs
  obtain ⟨hc0, hc1, hr₀, hs₀, hs₀c, hv₀⟩ := hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set h := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos hNr _
  set C₀ : ℝ := 3 + 2 / c with hC₀def
  have hC₀ : 0 < C₀ := by positivity
  have hq1 : 0 < 1 - chainRatio := sub_pos.mpr chainRatio_lt_one
  set u := s - a with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; linarith [hs.1]
  have huT : u ≤ t := by rw [hudef]; linarith [hs.2]
  obtain ⟨k, hk, hk1, hk2⟩ := exists_cell ht hu0 huT m
  set sk := a + (k : ℝ) * t / 2 ^ m with hskdef
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hkt : (k : ℝ) * t / 2 ^ m ≤ t := by
    rw [div_le_iff₀ h2m]
    have : (k : ℝ) ≤ 2 ^ m := by exact_mod_cast hk.le
    nlinarith
  have hska : a ≤ sk := by
    have : 0 ≤ (k : ℝ) * t / 2 ^ m := by positivity
    rw [hskdef]; linarith
  have hskc : sk ≤ c := by rw [hskdef]; linarith
  have hsk_pos : 0 < sk := by linarith
  have hsk_reg : sk ∈ Set.Icc (c - s₀) c := ⟨by linarith, hskc⟩
  have hsk1 : sk ≤ 1 := by linarith
  set G := flowNormalized a sk ω with hGdef
  obtain ⟨hUp, hLL, hNorm⟩ := hj k hk
  have hF := hC.1
  have hH := flowMatrix_isHermitian hF a hω1 s
  have hH' := flowMatrix_isHermitian hF a hω1 sk
  have hH'eq : flowMatrix F a ω sk = F + (Real.sqrt sk : ℂ) • G :=
    flowMatrix_eq_normalized F a ω hsk_pos
  -- Weyl transfer from the mesh time
  have hW : ∀ i, |flowEigenvalue F a ω s i - flowEigenvalue F a ω sk i| ≤ h := by
    intro i
    have h1 := freshEigenvalue_weyl_opB hH hH' i
    rw [flowMatrix_sub] at h1
    have hska' : sk - a = (k : ℝ) * t / 2 ^ m := by rw [hskdef]; ring
    rw [hska'] at h1
    have hm := chainGood_modulus hK₁ ht hω2 m k hk hk1 hk2
    exact h1.trans (hm.trans hmod)
  -- fixed-time upper count at the mesh time
  have hsq1 : Real.sqrt sk ≤ 1 := Real.sqrt_le_one.mpr hsk1
  have hrange : ∀ i, |flowEigenvalue F a ω sk i| ≤ (K₀ : ℝ) * h := by
    intro i
    have h1 := freshEigenvalue_abs_le_opB hH' i
    have hFn : opB F ≤ (N : ℝ) ^ A := opB_le_of F (by positivity) hC.2.1
    have hGn : opB G ≤ R₂ := not_lt.mp hNorm
    have h2 : opB (flowMatrix F a ω sk) ≤ (N : ℝ) ^ A + R₂ := by
      rw [hH'eq]
      refine (opB_add_le _ _).trans ?_
      rw [opB_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have : Real.sqrt sk * opB G ≤ opB G := by
        have := opB_nonneg G
        nlinarith
      linarith
    exact h1.trans (h2.trans hK₀)
  have hmesh : ∀ k' : ℤ, |k'| ≤ (K₀ : ℤ) + 1 →
      ((Finset.univ.filter fun i => |flowEigenvalue F a ω sk i - (k' : ℝ) * h| ≤ h).card : ℝ) ≤
        2 * N * h * C₀ := by
    intro k' hk'
    have h1 := count_le_im hH' hN ((k' : ℝ) * h) h hh
    have h2 : ((N : ℂ)⁻¹ * ((flowMatrix F a ω sk -
        (⟨(k' : ℝ) * h, h⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im ≤ 3 + 1 / sk := by
      by_contra hcon
      push Not at hcon
      apply hUp
      refine ⟨k', hk', ?_⟩
      have : coarseResolvent F G sk ⟨(k' : ℝ) * h, h⟩ = (flowMatrix F a ω sk -
          (⟨(k' : ℝ) * h, h⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
        rw [hH'eq]; rfl
      rw [this]
      exact hcon
    have h3 : 3 + 1 / sk ≤ C₀ := by
      rw [hC₀def]
      have : 1 / sk ≤ 2 / c := by
        rw [div_le_div_iff₀ hsk_pos hc0]; linarith
      linarith
    calc _ ≤ 2 * N * h * ((N : ℂ)⁻¹ * ((flowMatrix F a ω sk -
          (⟨(k' : ℝ) * h, h⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace).im := h1
      _ ≤ 2 * N * h * C₀ := by
          apply mul_le_mul_of_nonneg_left (h2.trans h3); positivity
  have hU' : ∀ x y, x ≤ y →
      ((Finset.univ.filter fun i => flowEigenvalue F a ω sk i ∈ Set.Icc x y).card : ℝ) ≤
        2 * N * h * C₀ * ((y - x) / h + 2) :=
    fun x y hxy => count_le_of_mesh _ hh K₀ hrange hmesh x y hxy
  -- fixed-time lower count at the mesh time
  have hloc : ∀ x η : ℝ, |x - E| ≤ r₀ / 2 → h ≤ η → η ≤ 1 →
      ‖(N : ℂ)⁻¹ * ((flowMatrix F a ω sk - (⟨x, η⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace - freshDyson F sk ⟨x, η⟩‖ ≤
        (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
    intro x η hx hη1 hη2
    by_contra hcon
    push Not at hcon
    apply hLL
    refine ⟨x, η, hx, hη1, hη2, Or.inl ?_⟩
    rw [hH'eq] at hcon
    exact hcon
  have hL' : ∀ x₀ L, |x₀ - E| ≤ r₀ / 2 → 16 * h / v₀ ^ 2 ≤ L →
      v₀ ^ 3 / 64 * N * min L 1 ≤
        ((Finset.univ.filter fun i => |flowEigenvalue F a ω sk i - x₀| ≤ L).card : ℝ) :=
    fun x₀ L hx₀ hL => lower_count_fixed hN hH' hC.2.2 hsk_reg hv₀ hr₀ hloc hsm hsm' hh1 hx₀ hL
  obtain ⟨c1, c2, c3, c4, c5⟩ := clauses_of_mesh hN hC₀ hv₀ hr₀ hh
    (flowEigenvalue F a ω s) (flowEigenvalue F a ω sk) (freshEigenvalue_monotone hH) hW hU' hL'
    hℓ1 hsc1 hsc3 hsc3' hsc3'' hsc4 hsc4'
  refine ⟨c1, c2, ?_, c4, ?_, ?_⟩
  · intro x y hxy
    refine (c3 x y hxy).trans ?_
    have : 0 ≤ (y - x) + h := add_nonneg (sub_nonneg.mpr hxy) hh.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC8 hNr.le) this
  · intro i
    obtain ⟨b1, b2⟩ := c5 i
    refine ⟨?_, b2⟩
    refine b1.trans ?_
    have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    rw [div_le_div_iff_of_pos_right hℓr]
    exact mul_le_mul_of_nonneg_right hC4 hNr.le
  · intro x
    refine (l2Norm_mulVec_le _ x).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [flowMatrix_sub, sub_self]
    have h1 := chainGood_sup hK₁ ht hω2 hu0 huT
    refine h1.trans ?_
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hCK (Real.sqrt_nonneg _)

/-- The mesh exponent: some level `m` has `K₁ q^m/(1-q) ≤ h`, and the least one has
`2^m ≤ 1 + 2 (K₁/(1-q))⁴ h⁻⁴`. -/
theorem exists_mesh_level {K₁ h : ℝ} (hK₁ : 0 < K₁) (hh : 0 < h) :
    ∃ m : ℕ, K₁ * chainRatio ^ m / (1 - chainRatio) ≤ h ∧
      (2 : ℝ) ^ m ≤ 1 + 2 * (K₁ / (1 - chainRatio)) ^ 4 * (h⁻¹) ^ 4 := by
  classical
  have hq0 := chainRatio_pos
  have hq1 : 0 < 1 - chainRatio := sub_pos.mpr chainRatio_lt_one
  have hex : ∃ m : ℕ, K₁ * chainRatio ^ m / (1 - chainRatio) ≤ h := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < h * (1 - chainRatio) / K₁)
      chainRatio_lt_one
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ hq1]
    rw [lt_div_iff₀ hK₁] at hn
    linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  set m := Nat.find hex with hm
  have hQ : 0 ≤ 2 * (K₁ / (1 - chainRatio)) ^ 4 * (h⁻¹) ^ 4 := by positivity
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0, pow_zero]; linarith
  · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hmin : ¬ K₁ * chainRatio ^ m' / (1 - chainRatio) ≤ h := by
      apply Nat.find_min hex
      omega
    push Not at hmin
    rw [lt_div_iff₀ hq1] at hmin
    have hz : h * (1 - chainRatio) / K₁ < chainRatio ^ m' := by
      rw [div_lt_iff₀ hK₁]; linarith
    have hz0 : 0 < h * (1 - chainRatio) / K₁ := by positivity
    have h4 : (h * (1 - chainRatio) / K₁) ^ 4 < (chainRatio ^ m') ^ 4 :=
      pow_lt_pow_left₀ hz hz0.le (by norm_num)
    have hq4 : (chainRatio ^ m') ^ 4 = (1 / 2 : ℝ) ^ m' := by
      rw [← pow_mul, mul_comm, pow_mul, chainRatio_pow_four]
    rw [hq4] at h4
    have h2 : (2 : ℝ) ^ m' * (1 / 2 : ℝ) ^ m' = 1 := by
      rw [← mul_pow]; norm_num
    have h2m : (2 : ℝ) ^ m' < ((h * (1 - chainRatio) / K₁) ^ 4)⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) (by positivity)]
      have : ((2 : ℝ) ^ m')⁻¹ = (1 / 2 : ℝ) ^ m' := by rw [one_div, inv_pow]
      rw [this]; exact h4
    have hid : ((h * (1 - chainRatio) / K₁) ^ 4)⁻¹ = (K₁ / (1 - chainRatio)) ^ 4 * (h⁻¹) ^ 4 := by
      field_simp
    rw [hid] at h2m
    rw [hm', pow_succ]
    have : 0 ≤ (K₁ / (1 - chainRatio)) ^ 4 * (h⁻¹) ^ 4 := by positivity
    linarith

end BlockBand.Palm.GoodEvent
