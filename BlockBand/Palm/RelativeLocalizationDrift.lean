module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.Palm.RelativeLocalizationWeight
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Relative localization: the drift cancellation (deterministic part)

Everything here is at one fixed time: a label-indexed vector `lam : Fin N → ℝ` (the
eigenvalues at that time), a nonnegative mass vector `v`, and a `C²` weight `φ` with
derivatives `φ1`, `φ2`. No measure, no stochastic calculus.

The Itô drift of the weighted mass `S = Σ_k φ(λ_k) v_k` along `dv = L v du` and the Dyson
SDE `dλ_k = N^{-1/2} dB_k + dysonDrift_k du` is
`Q = Σ_k φ(λ_k) (L v)_k + Σ_k v_k (φ'(λ_k) dysonDrift_k + φ''(λ_k)/(2N))`
(`Σ_k α_kk ∂_k²/2` with `α_kk = 1/N`; `v` has no martingale part). Proved:

* `sum_mul_shortGen_eq` : symmetrization `Σ φ_k (S v)_k = Σ v_k Σ_{short} c_kl (φ_l - φ_k)`;
* `short_term_le` : the key cancellation — for a short pair the jump term plus the pair's
  Dyson drift contribution is `c_kl (φ_l - φ_k - φ'_k (λ_l - λ_k)) ≤ M/N` (Taylor);
* `sum_inv_labelDist_le`, `card_short_le` : `Σ_{l≠k} 1/|k-l| ≤ 2(1 + log N)`,
  `#{0 < |k-l| < ℓ} ≤ 2ℓ`;
* `weighted_drift_le` : `Q ≤ κ S` with
  `κ = 2ℓ B K / N + 2 A (1 + log N)/c₁ + B/(2N)`, for any generator dominated by the
  short generator (covers the short and the reference generators: killing is `≤ 0`);
* `weighted_bracket_le` : `Σ_k (v_k φ'_k)² / N ≤ (A²/N) S²`.

Hypotheses on the spectrum (abstract, at the fixed time): long pairs `|k-l| ≥ ℓ` have
`|λ_k - λ_l| ≥ c₁|k-l|/N` (the long-gap lower bound); every short pair is either
`G`-close or lies where the weight is flat (`φ'_k = 0`, `φ_l = φ_k`). They are derived
from `SpectralGoodEventContract` separately.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Finset BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-!
### Abstract rates and generators at one time
-/

/-- `c_kl = 1/(N (λ_k - λ_l)²)` (Lean: `0` on a collision). -/
def pairRate (N : ℕ) (lam : Fin N → ℝ) (k l : Fin N) : ℝ := ((N : ℝ) * (lam k - lam l) ^ 2)⁻¹

/-- The short generator with rates `pairRate`, same shape as `shortGenerator`. -/
def shortGen (N : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (k l : Fin N) : ℝ := by
  classical
  exact if k = l then
      -∑ m ∈ Finset.univ.filter (fun m => m ≠ k ∧ labelDist k m < ℓ), pairRate N lam k m
    else if labelDist k l < ℓ then pairRate N lam k l else 0

/-- Total long coupling with rates `pairRate`. -/
def longCoup (N : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (k : Fin N) : ℝ := by
  classical
  exact ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist k m), pairRate N lam k m

theorem flowRate_eq_pairRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (σ : ℝ) : flowRate F a ω σ = pairRate N (flowEigenvalue F a ω σ) := rfl

theorem shortGenerator_eq_shortGen (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) : shortGenerator F a ω ℓ σ = shortGen N (flowEigenvalue F a ω σ) ℓ := rfl

theorem longCoupling_eq_longCoup (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) : longCoupling F a ω ℓ σ = longCoup N (flowEigenvalue F a ω σ) ℓ := rfl

theorem pairRate_nonneg (lam : Fin N → ℝ) (k l : Fin N) : 0 ≤ pairRate N lam k l := by
  unfold pairRate; positivity

theorem pairRate_symm (lam : Fin N → ℝ) (k l : Fin N) : pairRate N lam k l = pairRate N lam l k := by
  unfold pairRate; congr 2; ring

theorem labelDist_symm (k l : Fin N) : labelDist k l = labelDist l k := by
  unfold labelDist; omega

theorem longCoup_nonneg (lam : Fin N → ℝ) (ℓ : ℕ) (k : Fin N) : 0 ≤ longCoup N lam ℓ k := by
  classical
  unfold longCoup
  exact Finset.sum_nonneg fun m _ => pairRate_nonneg lam k m

/-- Off-diagonal entries of the short generator are nonnegative. -/
theorem shortGen_offdiag_nonneg (lam : Fin N → ℝ) (ℓ : ℕ) {k l : Fin N} (hkl : k ≠ l) :
    0 ≤ shortGen N lam ℓ k l := by
  classical
  unfold shortGen
  simp only [hkl, ite_false]
  split_ifs
  · exact pairRate_nonneg lam k l
  · exact le_rfl

/-- The application of the short generator: `(S v)_k = Σ_{0<|k-l|<ℓ} c_kl (v_l - v_k)`. -/
theorem shortGen_apply (lam : Fin N → ℝ) (ℓ : ℕ) (v : Fin N → ℝ) (k : Fin N) :
    ∑ l, shortGen N lam ℓ k l * v l =
      ∑ l, if l ≠ k ∧ labelDist k l < ℓ then pairRate N lam k l * (v l - v k) else 0 := by
  classical
  have hpt : ∀ l, shortGen N lam ℓ k l * v l =
      (if l ≠ k ∧ labelDist k l < ℓ then pairRate N lam k l * v l else 0) -
        (if l = k then (∑ m ∈ univ.filter (fun m => m ≠ k ∧ labelDist k m < ℓ),
          pairRate N lam k m) * v k else 0) := by
    intro l
    unfold shortGen
    by_cases h : l = k
    · subst h; simp
    · have h' : k ≠ l := fun e => h e.symm
      simp only [h', h, ite_false, ne_eq, not_false_eq_true, true_and, sub_zero]
      split_ifs <;> simp
  rw [Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have : ∀ l, (if l ≠ k ∧ labelDist k l < ℓ then pairRate N lam k l * (v l - v k) else 0) =
      (if l ≠ k ∧ labelDist k l < ℓ then pairRate N lam k l * v l else 0) -
        (if l ≠ k ∧ labelDist k l < ℓ then pairRate N lam k l else 0) * v k := by
    intro l; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  simp only [Finset.sum_filter]

/-- Symmetrization of the jump term (`c` and the short relation are symmetric). -/
theorem sum_mul_shortGen_eq (lam : Fin N → ℝ) (ℓ : ℕ) (v φ : Fin N → ℝ) :
    ∑ k, φ k * ∑ l, shortGen N lam ℓ k l * v l =
      ∑ k, v k * ∑ l, if l ≠ k ∧ labelDist k l < ℓ then
        pairRate N lam k l * (φ l - φ k) else 0 := by
  classical
  simp_rw [shortGen_apply, Finset.mul_sum]
  set m : Fin N → Fin N → ℝ := fun k l =>
    if l ≠ k ∧ labelDist k l < ℓ then pairRate N lam k l else 0 with hm
  have hmsymm : ∀ k l, m k l = m l k := by
    intro k l
    simp only [hm, ne_eq, labelDist_symm k l, pairRate_symm lam k l]
    by_cases h : l = k
    · subst h; rfl
    · have h' : ¬ k = l := fun e => h e.symm
      simp [h, h']
  have e1 : ∀ k l, φ k * (if l ≠ k ∧ labelDist k l < ℓ then
      pairRate N lam k l * (v l - v k) else 0) = m k l * (φ k * v l) - m k l * (φ k * v k) := by
    intro k l; simp only [hm]; split_ifs <;> ring
  have e2 : ∀ k l, v k * (if l ≠ k ∧ labelDist k l < ℓ then
      pairRate N lam k l * (φ l - φ k) else 0) = m k l * (v k * φ l) - m k l * (φ k * v k) := by
    intro k l; simp only [hm]; split_ifs <;> ring
  simp_rw [e1, e2, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hmsymm]; ring

/-!
### Counting lemmas
-/

/-- The injective code `l ↦ (|k - l| - 1, l < k)` of the labels `l ≠ k`. -/
def distCode (k l : Fin N) : ℕ × Bool := (labelDist k l - 1, decide (l < k))

theorem labelDist_pos {k l : Fin N} (h : l ≠ k) : 0 < labelDist k l := by
  unfold labelDist
  have : (k : ℤ) ≠ (l : ℤ) := by
    intro e; exact h (Fin.ext (by exact_mod_cast e.symm))
  omega

theorem labelDist_lt (k l : Fin N) : labelDist k l < N := by
  unfold labelDist
  have := k.isLt; have := l.isLt
  omega

theorem distCode_injOn (k : Fin N) :
    Set.InjOn (distCode k) {l | l ≠ k} := by
  intro l hl l' hl' he
  simp only [distCode, Prod.mk.injEq, decide_eq_decide] at he
  obtain ⟨h1, h2⟩ := he
  have p1 := labelDist_pos (Set.mem_ofPred.mp hl)
  have p2 := labelDist_pos (Set.mem_ofPred.mp hl')
  have hd : labelDist k l = labelDist k l' := by omega
  unfold labelDist at hd
  apply Fin.ext
  have hl1 : (l : ℕ) ≠ k := fun e => hl (Fin.ext e)
  have hl2 : (l' : ℕ) ≠ k := fun e => hl' (Fin.ext e)
  rw [Fin.lt_def, Fin.lt_def] at h2
  omega

/-- `#{l : 0 < |k-l| < ℓ} ≤ 2ℓ`. -/
theorem card_short_le (k : Fin N) (ℓ : ℕ) :
    ((Finset.univ.filter fun l : Fin N => l ≠ k ∧ labelDist k l < ℓ).card : ℝ) ≤ 2 * ℓ := by
  classical
  have hsub : (Finset.univ.filter fun l : Fin N => l ≠ k ∧ labelDist k l < ℓ).image (distCode k)
      ⊆ Finset.range ℓ ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨l, ⟨_, hl⟩, rfl⟩ := hp
    simp only [distCode, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    omega
  have hinj : Set.InjOn (distCode k)
      ↑(Finset.univ.filter fun l : Fin N => l ≠ k ∧ labelDist k l < ℓ) := by
    intro l hl l' hl' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl hl'
    exact distCode_injOn k hl.1 hl'.1 he
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
    Finset.card_univ, Fintype.card_bool] at this
  have : ((Finset.univ.filter fun l : Fin N => l ≠ k ∧ labelDist k l < ℓ).card : ℝ) ≤
      ((ℓ * 2 : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this; linarith

/-- `Σ_{l ≠ k} 1/|k - l| ≤ 2 (1 + log N)`. -/
theorem sum_inv_labelDist_le (k : Fin N) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin N => l ≠ k), ((labelDist k l : ℝ))⁻¹ ≤
      2 * (1 + Real.log N) := by
  classical
  set S := Finset.univ.filter (fun l : Fin N => l ≠ k)
  let g : ℕ × Bool → ℝ := fun p => ((p.1 + 1 : ℕ) : ℝ)⁻¹
  have hinj : Set.InjOn (distCode k) ↑S := by
    intro l hl l' hl' he
    simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl hl'
    exact distCode_injOn k hl hl' he
  have hrw : ∑ l ∈ S, ((labelDist k l : ℝ))⁻¹ = ∑ l ∈ S, g (distCode k l) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have := labelDist_pos hl
    simp only [g, distCode]
    congr 2; omega
  have hsub : S.image (distCode k) ⊆ Finset.range N ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨l, _, rfl⟩ := hp
    simp only [distCode, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    have := labelDist_lt k l
    omega
  rw [hrw, ← Finset.sum_image hinj]
  calc ∑ p ∈ S.image (distCode k), g p
      ≤ ∑ p ∈ Finset.range N ×ˢ (Finset.univ : Finset Bool), g p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    _ = 2 * (harmonic N : ℝ) := by
        rw [Finset.sum_product]
        simp only [g, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        rw [harmonic, ← Finset.mul_sum]
        push_cast
        ring
    _ ≤ 2 * (1 + Real.log N) := by
        have := harmonic_le_one_add_log N
        linarith

/-!
### The key cancellation for one short pair
-/

/-- **Key cancellation.** For one pair `(k,l)`, the jump term
`c_kl (φ_l - φ_k)` plus the pair's contribution `φ'_k /(N(λ_k - λ_l))` to the Dyson drift
equals `c_kl (φ_l - φ_k - φ'_k (λ_l - λ_k))`; if the second derivative is bounded by `M`
on the segment, it is at most `M/N`. If the weight is flat on the pair it vanishes. -/
theorem short_term_le {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hN : 0 < N) {x y M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ Set.uIcc x y, |φ2 z| ≤ M) :
    ((N : ℝ) * (x - y) ^ 2)⁻¹ * (φ y - φ x) + φ1 x * ((1 / (N : ℝ)) * (1 / (x - y))) ≤
      M / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hxy : x = y
  · subst hxy; simp; positivity
  · have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hd2 : 0 < (x - y) ^ 2 := by positivity
    have ht := abs_taylor2_le hφ hφ1 hM
    have heq : ((N : ℝ) * (x - y) ^ 2)⁻¹ * (φ y - φ x) + φ1 x * ((1 / (N : ℝ)) * (1 / (x - y))) =
        (φ y - φ x - φ1 x * (y - x)) / ((N : ℝ) * (x - y) ^ 2) := by
      field_simp; ring
    rw [heq, div_le_div_iff₀ (by positivity) hNr]
    have : (y - x) ^ 2 = (x - y) ^ 2 := by ring
    rw [this] at ht
    have := (abs_le.mp ht).2
    nlinarith

/-- Flat case: if `φ'_k = 0` and `φ_l = φ_k`, the combined pair term vanishes. -/
theorem short_term_flat {φ φ1 : ℝ → ℝ} {x y : ℝ} (h1 : φ1 x = 0) (h2 : φ y = φ x) :
    ((N : ℝ) * (x - y) ^ 2)⁻¹ * (φ y - φ x) + φ1 x * ((1 / (N : ℝ)) * (1 / (x - y))) = 0 := by
  rw [h1, h2]; ring

/-!
### The weighted drift inequality
-/

/-- Splitting of the Dyson drift into short and long pairs. -/
theorem dysonDrift_split (lam : Fin N → ℝ) (ℓ : ℕ) (k : Fin N) :
    dysonDrift N lam k =
      (∑ l, if l ≠ k ∧ labelDist k l < ℓ then (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0) +
      ∑ l, if l ≠ k ∧ ℓ ≤ labelDist k l then (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0 := by
  classical
  unfold dysonDrift
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l = k)]
  have h1 : ∑ l ∈ Finset.univ.filter (fun l => l = k),
      ((if l ≠ k ∧ labelDist k l < ℓ then (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0) +
        if l ≠ k ∧ ℓ ≤ labelDist k l then (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    simp [hl]
  rw [h1, zero_add]
  have herase : Finset.univ.erase k = Finset.univ.filter (fun l => ¬ l = k) := by
    ext l; simp
  rw [herase]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  by_cases h : labelDist k l < ℓ
  · simp [hl, h, not_le.mpr h]
  · simp [hl, h, le_of_not_gt h]

/-- Per-label bound: `Σ_{short} c_kl(φ_l - φ_k) + φ'_k dysonDrift_k + φ''_k/(2N) ≤ κ φ_k`. -/
theorem label_drift_le (lam : Fin N → ℝ) (ℓ : ℕ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁) (k : Fin N)
    (hshort : ∀ l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k) = 0 ∧ φ (lam l) = φ (lam k)))
    (hlong : ∀ l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|) :
    (∑ l, if l ≠ k ∧ labelDist k l < ℓ then
          pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
        (φ1 (lam k) * dysonDrift N lam k + φ2 (lam k) / (2 * N)) ≤
      (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) * φ (lam k) := by
  classical
  have hN : 0 < N := Fin.pos k
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hφk := hφ0 (lam k)
  rw [dysonDrift_split lam ℓ k, mul_add, Finset.mul_sum, Finset.mul_sum]
  -- short pairs
  have hS : (∑ l, if l ≠ k ∧ labelDist k l < ℓ then
        pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
      ∑ l, φ1 (lam k) * (if l ≠ k ∧ labelDist k l < ℓ then
        (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0) ≤
      2 * ℓ * B * K / N * φ (lam k) := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ l, ((if l ≠ k ∧ labelDist k l < ℓ then
          pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
        φ1 (lam k) * (if l ≠ k ∧ labelDist k l < ℓ then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)) ≤
        if l ≠ k ∧ labelDist k l < ℓ then B * K * φ (lam k) / N else 0 := by
      intro l
      by_cases hl : l ≠ k ∧ labelDist k l < ℓ
      · rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left hl]
        rcases hshort l hl.1 hl.2 with hc | hf
        · have := short_term_le (N := N) hφ hφ1 hN (x := lam k) (y := lam l)
            (M := B * K * φ (lam k)) (by positivity) ?_
          · simpa only [pairRate, mul_div_assoc] using this
          intro z hz
          refine (hB z).trans ?_
          have hz' : |z - lam k| ≤ G := by
            refine le_trans ?_ hc
            rw [Set.mem_uIcc] at hz
            rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
            · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          have := hcomp (lam k) z hz'
          calc B * φ z ≤ B * (K * φ (lam k)) := mul_le_mul_of_nonneg_left this hB0
            _ = B * K * φ (lam k) := by ring
        · rw [show pairRate N lam k l = ((N : ℝ) * (lam k - lam l) ^ 2)⁻¹ from rfl,
            short_term_flat hf.1 hf.2]
          positivity
      · simp [hl]
    refine (Finset.sum_le_sum fun l _ => hpt l).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := card_short_le k ℓ
    have : 0 ≤ B * K * φ (lam k) / N := by positivity
    calc _ ≤ (2 * ℓ) * (B * K * φ (lam k) / N) := mul_le_mul_of_nonneg_right hc this
      _ = _ := by ring
  -- long pairs
  have hL : ∑ l, φ1 (lam k) * (if l ≠ k ∧ ℓ ≤ labelDist k l then
        (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0) ≤
      2 * A * (1 + Real.log N) / c₁ * φ (lam k) := by
    have hpt : ∀ l, φ1 (lam k) * (if l ≠ k ∧ ℓ ≤ labelDist k l then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0) ≤
        if l ≠ k then A * φ (lam k) / c₁ * ((labelDist k l : ℝ))⁻¹ else 0 := by
      intro l
      by_cases hl : l ≠ k ∧ ℓ ≤ labelDist k l
      · rw [ite_eq_left hl, ite_eq_left hl.1]
        have hd := hlong l hl.1 hl.2
        have hdp : (0 : ℝ) < labelDist k l := by exact_mod_cast labelDist_pos hl.1
        have hgap : 0 < |lam k - lam l| := lt_of_lt_of_le (by positivity) hd
        calc φ1 (lam k) * ((1 / (N : ℝ)) * (1 / (lam k - lam l)))
            ≤ |φ1 (lam k) * ((1 / (N : ℝ)) * (1 / (lam k - lam l)))| := le_abs_self _
          _ = |φ1 (lam k)| * ((1 / (N : ℝ)) * (1 / |lam k - lam l|)) := by
              rw [abs_mul, abs_mul, abs_div, abs_div, abs_one, abs_of_pos hNr]
          _ ≤ (A * φ (lam k)) * ((1 / (N : ℝ)) * (N / (c₁ * labelDist k l))) := by
              refine mul_le_mul (hA _) ?_ (by positivity) (by positivity)
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [div_le_div_iff₀ hgap (by positivity)]
              rw [div_le_iff₀ hNr] at hd
              linarith
          _ = A * φ (lam k) / c₁ * ((labelDist k l : ℝ))⁻¹ := by field_simp
      · rw [ite_eq_right hl, mul_zero]
        split_ifs
        · positivity
        · exact le_rfl
    refine (Finset.sum_le_sum fun l _ => hpt l).trans ?_
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have := sum_inv_labelDist_le k
    calc A * φ (lam k) / c₁ * ∑ l ∈ Finset.univ.filter (fun l : Fin N => l ≠ k),
          ((labelDist k l : ℝ))⁻¹ ≤ A * φ (lam k) / c₁ * (2 * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  -- Itô correction
  have hI : φ2 (lam k) / (2 * N) ≤ B / (2 * N) * φ (lam k) := by
    have := (le_abs_self _).trans (hB (lam k))
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    linarith
  calc _ = ((∑ l, if l ≠ k ∧ labelDist k l < ℓ then
          pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
        ∑ l, φ1 (lam k) * (if l ≠ k ∧ labelDist k l < ℓ then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)) +
        (∑ l, φ1 (lam k) * (if l ≠ k ∧ ℓ ≤ labelDist k l then
          (1 / (N : ℝ)) * (1 / (lam k - lam l)) else 0)) + φ2 (lam k) / (2 * N) := by ring
    _ ≤ 2 * ℓ * B * K / N * φ (lam k) + 2 * A * (1 + Real.log N) / c₁ * φ (lam k) +
        B / (2 * N) * φ (lam k) := add_le_add (add_le_add hS hL) hI
    _ = _ := by ring

/-- **Weighted drift inequality** (deterministic part). At one time, for
a nonnegative mass vector `v`, any generator `L` with `(L v)_k ≤ (S v)_k` (short generator
`S`; this covers the reference generator, whose killing is nonpositive), and a weight `φ`
with `|φ'| ≤ A φ`, `|φ''| ≤ B φ`, `φ(z) ≤ K φ(x)` for `|z - x| ≤ G`:
`Σ_k φ(λ_k)(L v)_k + Σ_k v_k (φ'(λ_k) dysonDrift_k + φ''(λ_k)/(2N)) ≤ κ Σ_k φ(λ_k) v_k`,
`κ = 2ℓBK/N + 2A(1 + log N)/c₁ + B/(2N)`. -/
theorem weighted_drift_le (lam : Fin N → ℝ) (ℓ : ℕ) (L : Fin N → Fin N → ℝ)
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hLS : ∀ k, ∑ l, L k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l)
    (hshort : ∀ k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k) = 0 ∧ φ (lam l) = φ (lam k)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|) :
    ∑ k, φ (lam k) * ∑ l, L k l * v l +
        ∑ k, v k * (φ1 (lam k) * dysonDrift N lam k + φ2 (lam k) / (2 * N)) ≤
      (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) *
        ∑ k, φ (lam k) * v k := by
  classical
  set κ := 2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)
  have h1 : ∑ k, φ (lam k) * ∑ l, L k l * v l ≤
      ∑ k, φ (lam k) * ∑ l, shortGen N lam ℓ k l * v l :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hLS k) (hφ0 _)
  calc _ ≤ ∑ k, φ (lam k) * ∑ l, shortGen N lam ℓ k l * v l +
        ∑ k, v k * (φ1 (lam k) * dysonDrift N lam k + φ2 (lam k) / (2 * N)) :=
        add_le_add_left h1 _
    _ = ∑ k, v k * ((∑ l, if l ≠ k ∧ labelDist k l < ℓ then
          pairRate N lam k l * (φ (lam l) - φ (lam k)) else 0) +
        (φ1 (lam k) * dysonDrift N lam k + φ2 (lam k) / (2 * N))) := by
        rw [sum_mul_shortGen_eq lam ℓ v (fun k => φ (lam k)), ← Finset.sum_add_distrib]
        simp only [mul_add]
    _ ≤ ∑ k, v k * (κ * φ (lam k)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (label_drift_le lam ℓ hφ hφ1 hφ0 hA hA0 hB hB0 hK0 hcomp hc₁ k (hshort k)
            (hlong k)) (hv k)
    _ = κ * ∑ k, φ (lam k) * v k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- **Bracket bound**: `Σ_k (v_k φ'(λ_k))² / N ≤ (A²/N) (Σ_k φ(λ_k) v_k)²`. -/
theorem weighted_bracket_le (lam : Fin N → ℝ) (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k)
    {φ φ1 : ℝ → ℝ} {A : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) :
    ∑ k, (v k * φ1 (lam k)) ^ 2 / N ≤ A ^ 2 / N * (∑ k, φ (lam k) * v k) ^ 2 := by
  have hpt : ∀ k, (v k * φ1 (lam k)) ^ 2 ≤ A ^ 2 * (φ (lam k) * v k) ^ 2 := by
    intro k
    have h := hA (lam k)
    have : |v k * φ1 (lam k)| ≤ A * (φ (lam k) * v k) := by
      rw [abs_mul, abs_of_nonneg (hv k)]
      calc v k * |φ1 (lam k)| ≤ v k * (A * φ (lam k)) := mul_le_mul_of_nonneg_left h (hv k)
        _ = _ := by ring
    calc (v k * φ1 (lam k)) ^ 2 = |v k * φ1 (lam k)| ^ 2 := (sq_abs _).symm
      _ ≤ (A * (φ (lam k) * v k)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = _ := by ring
  have hsq : ∑ k, (φ (lam k) * v k) ^ 2 ≤ (∑ k, φ (lam k) * v k) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => mul_nonneg (hφ0 _) (hv k)
  rw [← Finset.sum_div, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  calc ∑ k, (v k * φ1 (lam k)) ^ 2 ≤ ∑ k, A ^ 2 * (φ (lam k) * v k) ^ 2 :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = A ^ 2 * ∑ k, (φ (lam k) * v k) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ A ^ 2 * (∑ k, φ (lam k) * v k) ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg A)

end BlockBand.Palm.RelativeLocalization
