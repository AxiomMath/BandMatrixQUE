module

public import BlockBand.Palm.MomentFlow.MaxShell
public import BlockBand.Palm.MomentFlow.MaxDamp
public import BlockBand.Palm.MomentFlow.Flat2Ramp

/-!
# The induction statement `CM(k, M)` and the propagation and flattening propositions

## Scales

`τ = N^{-θ}`, `η = N^{-ε}τ`, `ℓ = ⌊N^{1-θ/3}⌋`, `w = N^{1-θ/6}` (`cmTau`, `cmEta`, `cmEll`,
`cmW`); the flow has base variance `a = c₀ - τ` and final variance `c₀`; start-time fractions
`t_k = 1 - 2^{-(k+1)}` (`cmT`): `t_0 = 1/2` (times between `τ/2` and `τ`) and the step
`k-1 → k` has damping time `(t_k - t_{k-1})τ = 2^{-(k+1)}τ`.

## Windows and ramp

The flattening uses the ramp `ramp wd k₀ ξ`: it is `1` when every particle
of `ξ` is within `wd/2` labels of the centre label `k₀`, `0` beyond `wd`, linear in between
(the distance to the target is measured from a centre label). `InRank k₀ ρ ξ`: all
occupied labels within `ρ` of `k₀`. Proved: `rampDist_le_iff` (`rampDist k₀ ξ ≤ X` iff every
particle is within `X`), `occDist_move_le` (`occDist (ξ^{ij}) ξ ≤ r |i-j|`).

## `CM(k, M)` (the induction hypothesis), `CMWin k M`

For the flow with base `a = c₀ - τ` and `𝓛 = pathSigma F a a c₀` (exactly the conditioning of
`ConditionalMomentsStatement`): there are `κ > 0` and `C` such that for every `D` and large `N`,
outside one `𝓛`-measurable set of probability `≤ N^{-D}`, for every regular version `Φ` of the
`k`-particle conditional moments and a.e. path, there is a **continuous** error `e ≥ 0` on
`[a + t_kτ, c₀]` with `∫ e ≤ N^{-D}` and `e(c₀) ≤ N^{-D}` such that
`|Φ(σ, ξ) - 1| ≤ C N^{-κ} + e(σ)` for all `σ ∈ [a + t_kτ, c₀]`, all centres `k₀` with
`|λ_{k₀}(σ) - E| ≤ M w/N` and all `k`-particle `ξ` with every particle within `M w` labels of `k₀`
(the shrinking bulk windows; nested windows = varying `M`).

## Propagation and flattening propositions

* `PropagationP6` (finite speed, column form): the short flow started from the
  indicator of the ramp window `{rampDist k₀ ≤ wd}` is `≤ e(u)` on `{rampDist k₀ > 2wd}`.
* `LongShortPropagation` (long versus short moments, on the whole local window):
  `|Φ(u,ζ) - (U_{a,u}Φ(a))(ζ)| ≤ C₂N^{C₁ε} Nτ/ℓ + e(u)` for `rampDist k₀ ζ ≤ wd`.
* `Flattening` (flattening): rough bound `0 ≤ Φ(a,ζ) ≤ C₂N^{C₁ε}` on the
  ramp window, energies `|λ_j(u) - E| ≤ C₂(M + Kw)w/N` for labels within `4wd` of the centre at
  all times, and the commutator `|U_{a,u}(Av Φ(a)) - Av(U_{a,u}Φ(a))| ≤ C₂N^{C₁ε} ℓ/w + e(u)`
  globally.

Here `wd = Kw·w`, the centre `k₀` satisfies `|λ_{k₀}(σ₀) - E| ≤ M w/N` at some `σ₀ ∈ [a, c₀]`, and
the constants `C₁, C₂` may depend on `(A, c₀, r₀, s₀, v₀, r, M, Kw)` but not on `ε, D, N, F, E, q`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

variable {N : ℕ}

/-!
## Scales
-/

/-- `τ = N^{-1/100}`. -/
def cmTau (N : ℕ) : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
/-- `η = N^{-ε} τ`. -/
def cmEta (N : ℕ) (ε : ℝ) : ℝ := (N : ℝ) ^ (-ε) * cmTau N
/-- `ℓ = ⌊N^{1-θ/3}⌋`. -/
def cmEll (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
/-- `w = N^{1-θ/6}`. -/
def cmW (N : ℕ) : ℝ := (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 6)
/-- Start-time fraction of `CM(k)`: `t_k = 1 - 2^{-(k+1)}`. -/
def cmT (k : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (k + 1)

/-!
## Windows
-/

/-- Every occupied label of `ξ` is within `ρ` labels of `k₀`. -/
def InRank (k₀ : Fin N) (ρ : ℝ) (ξ : Occ N) : Prop := ∀ j, 0 < ξ j → (labelDist j k₀ : ℝ) ≤ ρ

theorem listMaxDist_le_iff (k₀ X : ℕ) :
    ∀ L : List ℕ, listMaxDist k₀ L ≤ X ↔ ∀ x ∈ L, Int.natAbs ((x : ℤ) - k₀) ≤ X
  | [] => by simp [listMaxDist]
  | x :: L => by
    have ih := listMaxDist_le_iff k₀ X L
    simp only [listMaxDist, List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]

theorem mem_occLabels {ξ : Occ N} {x : ℕ} : x ∈ occLabels ξ ↔ ∃ j : Fin N, 0 < ξ j ∧ (j : ℕ) = x := by
  rw [occLabels_eq, Multiset.mem_sort, occBag, Multiset.mem_bind]
  constructor
  · rintro ⟨j, -, hj⟩
    have := Multiset.mem_replicate.1 hj
    exact ⟨j, Nat.pos_of_ne_zero this.1, this.2.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_univ_val j, Multiset.mem_replicate.2 ⟨hj.ne', rfl⟩⟩

/-- `rampDist k₀ ξ ≤ X` iff every particle of `ξ` lies within `X` labels of `k₀`. -/
theorem rampDist_le_iff (k₀ : Fin N) (ξ : Occ N) (X : ℕ) :
    rampDist (k₀ : ℕ) ξ ≤ X ↔ ∀ j, 0 < ξ j → labelDist j k₀ ≤ X := by
  unfold rampDist
  rw [listMaxDist_le_iff]
  constructor
  · intro h j hj
    exact h j (mem_occLabels.2 ⟨j, hj, rfl⟩)
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := mem_occLabels.1 hx
    exact h j hj

theorem inRank_of_rampDist_le {k₀ : Fin N} {ξ : Occ N} {ρ : ℝ}
    (h : (rampDist (k₀ : ℕ) ξ : ℝ) ≤ ρ) : InRank k₀ ρ ξ := by
  intro j hj
  have := (rampDist_le_iff k₀ ξ _).1 le_rfl j hj
  exact (Nat.cast_le.2 this).trans h

theorem rampDist_le_of_inRank {k₀ : Fin N} {ξ : Occ N} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : InRank k₀ ρ ξ) : (rampDist (k₀ : ℕ) ξ : ℝ) ≤ ρ := by
  have : rampDist (k₀ : ℕ) ξ ≤ ⌊ρ⌋₊ :=
    (rampDist_le_iff k₀ ξ _).2 fun j hj => Nat.le_floor (h j hj)
  exact (Nat.cast_le.2 this).trans (Nat.floor_le hρ)

theorem inRank_remove {k₀ : Fin N} {ξ : Occ N} {ρ : ℝ} (h : InRank k₀ ρ ξ) (i : Fin N) :
    InRank k₀ ρ (remove ξ i) := by
  intro j hj
  refine h j ?_
  unfold remove at hj
  by_cases hji : j = i
  · subst hji; simp at hj; omega
  · rwa [Function.update_of_ne hji] at hj

/-- One move changes the ordered matching distance by at most `r |i - j|`. -/
theorem occDist_move_le {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {i j : Fin N} (hij : i ≠ j)
    (hi : 0 < ξ i) : occDist (move ξ i j) ξ ≤ r * labelDist i j := by
  classical
  obtain ⟨x, hx⟩ := exists_occOf r ξ hξ
  have hxi : 0 < occOf x i := by rw [hx]; exact hi
  obtain ⟨p, hp⟩ : ∃ p, x p = i := by
    obtain ⟨p, hp⟩ := Finset.card_pos.1 hxi
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  have hx' : Function.update x p j ∈ labs r (move ξ i j) := by
    rw [mem_labs, occOf_update (by rw [hp]; exact hij), hp, hx]
  refine occDist_le_of_labs hx' (mem_labs.2 hx) fun m => ?_
  by_cases hm : m = p
  · subst hm; rw [Function.update_self, hp, labelDist_comm]
  · rw [Function.update_of_ne hm]; simp [labelDist]

/-- The ramp moves by at most `min(1, 2r|i - j|/wd)` under one move. -/
theorem ramp_remTarget_le {r : ℕ} {wd : ℝ} (hwd : 0 < wd) (k₀ : ℕ) {ξ : Occ N}
    (hξ : ξ ∈ sector N r) {i : Fin N} (hi : 0 < ξ i) (j : Fin N) :
    |ramp wd k₀ (remTarget ξ i j) - ramp wd k₀ ξ| ≤
      min 1 (2 * r / wd * (labelDist i j : ℝ)) := by
  by_cases hji : j = i
  · subst hji
    have : remTarget ξ j j = ξ := by simp [remTarget]
    rw [this, sub_self, abs_zero]
    exact le_min zero_le_one (by positivity)
  have hij : i ≠ j := Ne.symm hji
  have ht : remTarget ξ i j = move ξ i j := by simp [remTarget, hji]
  rw [ht]
  refine le_min ?_ ?_
  · rw [abs_le]; constructor <;>
      linarith [ramp_nonneg wd k₀ (move ξ i j), ramp_le_one wd k₀ (move ξ i j),
        ramp_nonneg wd k₀ ξ, ramp_le_one wd k₀ ξ]
  · refine (abs_ramp_sub_le_occDist hwd k₀ hξ (move_mem_sector hξ hij hi)).trans ?_
    have h := occDist_move_le hξ hij hi
    have h' : (occDist (move ξ i j) ξ : ℝ) ≤ r * labelDist i j := by exact_mod_cast h
    calc 2 / wd * (occDist (move ξ i j) ξ : ℝ) ≤ 2 / wd * (r * labelDist i j) :=
          mul_le_mul_of_nonneg_left h' (by positivity)
      _ = 2 * r / wd * (labelDist i j : ℝ) := by ring

/-!
## Errors and versions
-/

/-- The error `e_D`: a nonnegative error, interval integrable on `[s, c]`, with `∫_s^c e ≤ b` and
`e c ≤ b`. -/
def IntErr (e : ℝ → ℝ) (s c b : ℝ) : Prop :=
  (∀ u ∈ Icc s c, 0 ≤ e u) ∧ IntervalIntegrable e volume s c ∧ (∫ u in s..c, e u) ≤ b ∧ e c ≤ b

/-- A continuous integrated error (the form produced and consumed by the induction). -/
def ContErr (e : ℝ → ℝ) (s c b : ℝ) : Prop :=
  ContinuousOn e (Icc s c) ∧ (∀ u ∈ Icc s c, 0 ≤ e u) ∧ (∫ u in s..c, e u) ≤ b ∧ e c ≤ b

/-- A regular version of the `r`-particle conditional moments on `[a, c]`. -/
def RegVersion (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (r : ℕ)
    (Φ : ℝ → Occ N → FlowSample N → ℝ) : Prop :=
  (∀ σ ∈ Icc a c, ∀ ξ ∈ sector N r, Φ σ ξ =ᵐ[flowLaw N a] condMoment F a c q σ ξ) ∧
    ∀ᵐ ω ∂flowLaw N a, IsMomentFlowSolution (flowRate F a ω) r a c (fun σ ξ => Φ σ ξ ω)

/-- Short-flow solutions (`|i - j| < ℓ`) on `[a, c]` along the path `ω`. -/
def ShortSol (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (ω : FlowSample N) (ℓ r : ℕ)
    (g : ℝ → Occ N → ℝ) : Prop :=
  IsMomentFlowSolution (shortFlowRate F a ω ℓ) r a c g

/-!
## The induction statement
-/

/-- **`CM(k, M)`**, the induction statement. -/
def CMWin (k : ℕ) (M : ℝ) : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ →
  ∃ κ C : ℝ, 0 < κ ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
      ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
        flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ Φ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F (c₀ - cmTau N) c₀ q k Φ →
          ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B →
            ∃ e : ℝ → ℝ, ContErr e (c₀ - cmTau N + cmT k * cmTau N) c₀ ((N : ℝ) ^ (-D)) ∧
              ∀ σ ∈ Icc (c₀ - cmTau N + cmT k * cmTau N) c₀, ∀ k₀ : Fin N,
                |flowEigenvalue F (c₀ - cmTau N) ω σ k₀ - E| ≤ M * cmW N / N →
                ∀ ξ ∈ sector N k, InRank k₀ (M * cmW N) ξ →
                  |Φ σ ξ ω - 1| ≤ C * (N : ℝ) ^ (-κ) + e σ

/-!
## Propagation and flattening propositions

Proved in `propagationP6_holds`, `longShortPropagation_holds`, `flattening_holds`.
-/

/-- Column finite speed of the short flow out of the ramp window. -/
def PropagationP6 : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ r : ℕ, 1 ≤ r → ∀ M Kw : ℝ, 0 < Kw →
  ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
        flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B →
          ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D)) ∧
            ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
              |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
              ∀ h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
                (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ =
                  if (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N then 1 else 0) →
                ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
                  2 * (Kw * cmW N) < (rampDist (k₀ : ℕ) ζ : ℝ) → h u ζ ≤ e u

/-- Full versus short flow on the ramp window. -/
def LongShortPropagation : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ r : ℕ, 1 ≤ r → ∀ M Kw : ℝ, 0 < Kw →
  ∃ C₁ C₂ : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 1000 → ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
      ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
        flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ Φ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F (c₀ - cmTau N) c₀ q r Φ →
          ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B →
            ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D)) ∧
              ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
                |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
                ∀ h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
                  (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ = Φ (c₀ - cmTau N) ζ ω) →
                  ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
                    (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
                    |Φ u ζ ω - h u ζ| ≤
                      C₂ * (N : ℝ) ^ (C₁ * ε) * ((N : ℝ) * cmTau N / cmEll N) + e u

/-- Flattening: rough bound, window energies, and the commutator bound. -/
def Flattening : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ r : ℕ, 1 ≤ r → ∀ M Kw : ℝ, 0 < Kw →
  ∃ C₁ C₂ : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 1000 → ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
      ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
        flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ Φ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F (c₀ - cmTau N) c₀ q r Φ →
          ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B →
            ∃ e : ℝ → ℝ, IntErr e (c₀ - cmTau N) c₀ ((N : ℝ) ^ (-D)) ∧
              ∀ σ₀ ∈ Icc (c₀ - cmTau N) c₀, ∀ k₀ : Fin N,
                |flowEigenvalue F (c₀ - cmTau N) ω σ₀ k₀ - E| ≤ M * cmW N / N →
                (∀ ζ ∈ sector N r, (rampDist (k₀ : ℕ) ζ : ℝ) ≤ Kw * cmW N →
                  0 ≤ Φ (c₀ - cmTau N) ζ ω ∧
                    Φ (c₀ - cmTau N) ζ ω ≤ C₂ * (N : ℝ) ^ (C₁ * ε)) ∧
                (∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ j : Fin N,
                  (labelDist j k₀ : ℝ) ≤ 4 * (Kw * cmW N) →
                  |flowEigenvalue F (c₀ - cmTau N) ω u j - E| ≤ C₂ * (M + Kw) * cmW N / N) ∧
                ∀ g h : ℝ → Occ N → ℝ, ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r g →
                  ShortSol F (c₀ - cmTau N) c₀ ω (cmEll N) r h →
                  (∀ ζ ∈ sector N r, g (c₀ - cmTau N) ζ =
                    avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (fun ζ' => Φ (c₀ - cmTau N) ζ' ω) ζ) →
                  (∀ ζ ∈ sector N r, h (c₀ - cmTau N) ζ = Φ (c₀ - cmTau N) ζ ω) →
                  ∀ u ∈ Icc (c₀ - cmTau N) c₀, ∀ ζ ∈ sector N r,
                    |g u ζ - avFlat (ramp (Kw * cmW N) (k₀ : ℕ)) (h u) ζ| ≤
                      C₂ * (N : ℝ) ^ (C₁ * ε) * ((cmEll N : ℝ) / cmW N) + e u

end BlockBand.Palm.MomentFlow
