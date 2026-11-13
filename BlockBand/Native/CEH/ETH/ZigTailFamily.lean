module

public import BlockBand.Native.CEH.ETH.ZigTail

/-!
# CEH ETH: the tail-event family of the two-resolvent zig and its good event

The finite family of chains whose martingale parts are controlled along the flow, and the good
event on which all their controls hold, with a union bound on its complement.

**Members** (`ztl_Idx L = ((Bool × Bool) × Bool × Bool × Fin (L+1)) ⊕ Fin (L+1)`):
* `inl ((c₁, c₂), p, k, ℓ)`: the chain `Re tr(K R₁' A' R₂')` of `ztl_mX` with
  * constellation `(c₁, c₂)`: `R_i' = R_i` (`c_i = true`) or `R_i' = R(z̄_i, m̄_i) = R_iᴴ`
    (`c_i = false`), i.e. parameters `(ztl_cz c_i z_i, ztl_cz c_i m_i)`;
  * part `p`: `K = ztl_evK p (ztl_avgK N)`, i.e. `N⁻¹ · 1` (`Re⟨·⟩`, `p = true`) or
    `-i N⁻¹ · 1` (`Im⟨·⟩`, `p = false`), see `ztl_reTr_evK_avgK_true/false`;
  * kind `k`: `X` (`A' = A`, `k = true`) or `Y` (`A' = 1`, `k = false`);
  * grid level `ℓ ≤ L`.
* `inr ℓ`: the imaginary chain `Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩` at level `ℓ ≤ L` (one constellation
  suffices: `Z` changes only by a sign under conjugation of either point).
`#ztl_Idx L = 17 (L + 1)` (`ztl_card_Idx`).

**Results.**
* `ztl_measure_eventF_le`: each member's tail event has `Q ≤ 2 exp(-q)` when `q ≤ a²/(2b)`.
* `ztl_controlF_of_not_mem`: off its event, each member satisfies the control
  `∀ t ∈ Set.Icc 0 (s:ℝ), (∫ r in Set.Ioc 0 t, brk r) ≤ b → |m t| < a`.
* `ztl_measure_le_of_violatesF` (union bound, mirrors `measure_le_of_martGood`): for an arbitrary
  set `S` (no measurability) all of whose points violate some member's control,
  `Q S ≤ 17 (L+1) · 2 exp(-q)`.
* `ztl_goodEvent` / `ztl_goodEvent_levels`: `Q {ω | ¬ (all controls hold)} ≤ 17 (L+1) · 2 exp(-q)`,
  for thresholds indexed by the member (resp. by kind and level).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.Internal.Contracts.Transmission
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.LocalLaw
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {Ω : Type} {N : ℕ}

/-!
### Parameters of the members
-/

/-- `w` (`c = true`) or `w̄` (`c = false`). -/
def ztl_cz (c : Bool) (w : ℂ) : ℂ := if c then w else conj w

/-- `K` (`p = true`, real part) or `-i K` (`p = false`, imaginary part). -/
def ztl_evK (p : Bool) (K : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if p then K else (-Complex.I) • K

/-- `N⁻¹ · 1`, so that `Re tr(ztl_avgK N · X) = Re⟨X⟩`. -/
def ztl_avgK (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := (N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)

theorem ztl_reTr_evK_avgK_true (X : Matrix (Fin N) (Fin N) ℂ) :
    reTr (ztl_evK true (ztl_avgK N)) X = (normalizedTrace X).re := by
  simp only [ztl_evK, ↓reduceIte]
  rw [ztl_avgK, reTr_avgRe, Matrix.mul_one]

theorem ztl_reTr_evK_avgK_false (X : Matrix (Fin N) (Fin N) ℂ) :
    reTr (ztl_evK false (ztl_avgK N)) X = (normalizedTrace X).im := by
  simp only [ztl_evK, Bool.false_eq_true, ↓reduceIte]
  rw [ztl_avgK, smul_smul, reTr_avgIm, Matrix.mul_one]

theorem ztl_cz_im_ne_zero (c : Bool) {z : ℂ} (hz : z.im ≠ 0) : (ztl_cz c z).im ≠ 0 := by
  cases c <;> simpa [ztl_cz] using hz

theorem ztl_cz_hm (c : Bool) {z m : ℂ} (hm : 0 ≤ z.im * m.im) :
    0 ≤ (ztl_cz c z).im * (ztl_cz c m).im := by
  cases c
  · exact fz_conj_hm hm
  · exact hm

/-- **Adjoint constellations along the path**: `R(w̄, n̄)(t) = R(w, n)(t)ᴴ` (`c = false`). -/
theorem ztl_pathR_cz (c : Bool) {F : Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} (z m : ℂ) (s : ℝ≥0) (ω : Ω)
    (hH : ∀ σ, (F + G σ ω).IsHermitian) (t : ℝ) :
    pathR F G (ztl_cz c z) (ztl_cz c m) s ω t =
      if c then pathR F G z m s ω t else (pathR F G z m s ω t)ᴴ := by
  cases c
  · exact fz_flowResolvent_conj z m s t.toNNReal ω (hH _)
  · rfl

/-!
### The family
-/

/-- Member index: X/Y chains `(constellation, Re/Im, X/Y, level)` and `Z` at each level. -/
abbrev ztl_Idx (L : ℕ) : Type := ((Bool × Bool) × Bool × Bool × Fin (L + 1)) ⊕ Fin (L + 1)

theorem ztl_card_Idx (L : ℕ) : Fintype.card (ztl_Idx L) = 17 * (L + 1) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

/-- The matrix `K` of a chain member. -/
def ztl_KF (p : Bool) : Matrix (Fin N) (Fin N) ℂ := ztl_evK p (ztl_avgK N)

/-- The observable of a chain member: `A` (X) or `1` (Y). -/
def ztl_AF (A : Matrix (Fin N) (Fin N) ℂ) (k : Bool) : Matrix (Fin N) (Fin N) ℂ :=
  if k then A else 1

/-- The path function `m` of each member (`ztl_mX` / `ztl_mZ`). -/
def ztl_mF {L : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) : ztl_Idx L → Ω → ℝ → ℝ
  | Sum.inl ((c₁, c₂), p, k, _) => ztl_mX F G (ztl_cz c₁ z₁) (ztl_cz c₁ m₁) (ztl_cz c₂ z₂)
      (ztl_cz c₂ m₂) s (ztl_KF p) (ztl_AF A k)
  | Sum.inr _ => ztl_mZ F G z₁ m₁ z₂ m₂ s A

/-- The bracket density `brk` of each member (`ztl_brkX` / `ztl_brkZ`). -/
def ztl_brkF {L : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) : ztl_Idx L → Ω → ℝ → ℝ
  | Sum.inl ((c₁, c₂), p, k, _) => ztl_brkX F G (ztl_cz c₁ z₁) (ztl_cz c₁ m₁) (ztl_cz c₂ z₂)
      (ztl_cz c₂ m₂) s (ztl_KF p) (ztl_AF A k)
  | Sum.inr _ => ztl_brkZ F G z₁ m₁ z₂ m₂ s A

/-- The tail event of each member, with thresholds `a j`, `b j`. -/
def ztl_eventF {L : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) (a b : ztl_Idx L → ℝ) :
    ztl_Idx L → Set Ω
  | j@(Sum.inl ((c₁, c₂), p, k, _)) => ztl_eventX F G (ztl_cz c₁ z₁) (ztl_cz c₁ m₁)
      (ztl_cz c₂ z₂) (ztl_cz c₂ m₂) s (ztl_KF p) (ztl_AF A k) (a j) (b j)
  | j@(Sum.inr _) => ztl_eventZ F G z₁ m₁ z₂ m₂ s A (a j) (b j)

variable {F : Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
  {z₁ m₁ z₂ m₂ : ℂ} {s : ℝ≥0} {A : Matrix (Fin N) (Fin N) ℂ} {L : ℕ}

/-- **Off its tail event, each member satisfies the control.** -/
theorem ztl_controlF_of_not_mem (a b : ztl_Idx L → ℝ) (j : ztl_Idx L) {ω : Ω}
    (hω : ω ∉ ztl_eventF F G z₁ m₁ z₂ m₂ s A a b j) :
    ∀ t ∈ Set.Icc 0 (s : ℝ), (∫ r in Set.Ioc 0 t, ztl_brkF F G z₁ m₁ z₂ m₂ s A j ω r) ≤ b j →
      |ztl_mF F G z₁ m₁ z₂ m₂ s A j ω t| < a j := by
  rcases j with ⟨⟨c₁, c₂⟩, p, k, ℓ⟩ | ℓ
  · exact ztl_controlX hω
  · exact ztl_controlZ hω

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Exponential tail of each member**: `Q(event j) ≤ 2 exp(-q)` if `q ≤ a_j²/(2b_j)`. -/
theorem ztl_measure_eventF_le (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (a b : ztl_Idx L → ℝ) {q : ℝ} (j : ztl_Idx L) (ha : 0 < a j) (hb : 0 < b j)
    (hq : q ≤ a j ^ 2 / (2 * b j)) :
    Q (ztl_eventF F G z₁ m₁ z₂ m₂ s A a b j) ≤ ENNReal.ofReal (2 * Real.exp (-q)) := by
  rcases j with ⟨⟨c₁, c₂⟩, p, k, ℓ⟩ | ℓ
  · exact ztl_measure_event_le_exp (ztl_semimartingaleX hG hF (ztl_cz_im_ne_zero c₁ hz₁)
      (ztl_cz_hm c₁ hm₁) (ztl_cz_im_ne_zero c₂ hz₂) (ztl_cz_hm c₂ hm₂) s _ _) ha hb hq
  · exact ztl_measure_event_le_exp (ztl_semimartingaleZ hG hF hz₁ hm₁ hz₂ hm₂ s A) ha hb hq

/-- **Union bound over the family**.
If every `ω ∈ S`
violates the control of some member, then `Q S ≤ 17 (L+1) · 2 exp(-q)`, where
`q ≤ a_j²/(2b_j)` for every member.
`S` is arbitrary (no measurability).
-/
theorem ztl_measure_le_of_violatesF (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (a b : ztl_Idx L → ℝ) (q : ℝ) (hq : ∀ j, 0 < a j ∧ 0 < b j ∧ q ≤ a j ^ 2 / (2 * b j))
    (S : Set Ω)
    (hS : ∀ ω ∈ S, ∃ j : ztl_Idx L, ¬ ∀ t ∈ Set.Icc 0 (s : ℝ),
      (∫ r in Set.Ioc 0 t, ztl_brkF F G z₁ m₁ z₂ m₂ s A j ω r) ≤ b j →
        |ztl_mF F G z₁ m₁ z₂ m₂ s A j ω t| < a j) :
    Q S ≤ ENNReal.ofReal (((17 * (L + 1) : ℕ) : ℝ) * (2 * Real.exp (-q))) := by
  rw [← ztl_card_Idx L]
  exact ztl_measure_le_of_violates (ztl_eventF F G z₁ m₁ z₂ m₂ s A a b)
    (fun j ω => ∀ t ∈ Set.Icc 0 (s : ℝ),
      (∫ r in Set.Ioc 0 t, ztl_brkF F G z₁ m₁ z₂ m₂ s A j ω r) ≤ b j →
        |ztl_mF F G z₁ m₁ z₂ m₂ s A j ω t| < a j)
    (fun j => ztl_measure_eventF_le hG hF hz₁ hm₁ hz₂ hm₂ a b j (hq j).1 (hq j).2.1 (hq j).2.2)
    (fun j _ hω => ztl_controlF_of_not_mem a b j hω) S hS

/-- **Good event, member form**: with probability `≥ 1 - 17 (L+1) · 2 exp(-q)`, all the controls
of the family hold simultaneously along the sample path. -/
theorem ztl_goodEvent (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (a b : ztl_Idx L → ℝ) (q : ℝ) (hq : ∀ j, 0 < a j ∧ 0 < b j ∧ q ≤ a j ^ 2 / (2 * b j)) :
    Q {ω | ¬ ∀ j : ztl_Idx L, ∀ t ∈ Set.Icc 0 (s : ℝ),
      (∫ r in Set.Ioc 0 t, ztl_brkF F G z₁ m₁ z₂ m₂ s A j ω r) ≤ b j →
        |ztl_mF F G z₁ m₁ z₂ m₂ s A j ω t| < a j} ≤
      ENNReal.ofReal (((17 * (L + 1) : ℕ) : ℝ) * (2 * Real.exp (-q))) :=
  ztl_measure_le_of_violatesF hG hF hz₁ hm₁ hz₂ hm₂ a b q hq _ fun _ hω => by
    simpa only [mem_ofPred_eq, not_forall, exists_prop] using hω

/-- **Good event, level form.** Thresholds `aX ℓ, bX ℓ` (X chains), `aY ℓ, bY ℓ` (Y chains),
`aZ ℓ, bZ ℓ` (Z), `ℓ ≤ L`, each with `q ≤ a²/(2b)`. With probability
`≥ 1 - 17 (L+1) · 2 exp(-q)`, simultaneously for all constellations `(c₁, c₂)`, both parts `p`
(Re: `p = true`, Im: `p = false`) and all levels `ℓ ≤ L`:
* `X`: `K = ztl_evK p (ztl_avgK N)`, observable `A`;
* `Y`: the same with observable `1`;
* `Z`: `Re⟨Im R₁ A Im R₂ Aᴴ⟩`;
each satisfies the control `∀ t ∈ Set.Icc 0 (s:ℝ), (∫ r in Set.Ioc 0 t, brk r) ≤ b →
|m t| < a`. -/
theorem ztl_goodEvent_levels (hG : IsHermitianBrownian Q 𝓖 N G) (hF : F.IsHermitian)
    (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im) (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im)
    (aX bX aY bY aZ bZ : ℕ → ℝ) (q : ℝ)
    (hqX : ∀ ℓ ≤ L, 0 < aX ℓ ∧ 0 < bX ℓ ∧ q ≤ aX ℓ ^ 2 / (2 * bX ℓ))
    (hqY : ∀ ℓ ≤ L, 0 < aY ℓ ∧ 0 < bY ℓ ∧ q ≤ aY ℓ ^ 2 / (2 * bY ℓ))
    (hqZ : ∀ ℓ ≤ L, 0 < aZ ℓ ∧ 0 < bZ ℓ ∧ q ≤ aZ ℓ ^ 2 / (2 * bZ ℓ)) :
    Q {ω | ¬ ((∀ c₁ c₂ p : Bool, ∀ ℓ ≤ L, ∀ t ∈ Set.Icc 0 (s : ℝ),
          (∫ r in Set.Ioc 0 t, ztl_brkX F G (ztl_cz c₁ z₁) (ztl_cz c₁ m₁) (ztl_cz c₂ z₂)
            (ztl_cz c₂ m₂) s (ztl_evK p (ztl_avgK N)) A ω r) ≤ bX ℓ →
          |ztl_mX F G (ztl_cz c₁ z₁) (ztl_cz c₁ m₁) (ztl_cz c₂ z₂) (ztl_cz c₂ m₂) s
            (ztl_evK p (ztl_avgK N)) A ω t| < aX ℓ) ∧
        (∀ c₁ c₂ p : Bool, ∀ ℓ ≤ L, ∀ t ∈ Set.Icc 0 (s : ℝ),
          (∫ r in Set.Ioc 0 t, ztl_brkX F G (ztl_cz c₁ z₁) (ztl_cz c₁ m₁) (ztl_cz c₂ z₂)
            (ztl_cz c₂ m₂) s (ztl_evK p (ztl_avgK N)) 1 ω r) ≤ bY ℓ →
          |ztl_mX F G (ztl_cz c₁ z₁) (ztl_cz c₁ m₁) (ztl_cz c₂ z₂) (ztl_cz c₂ m₂) s
            (ztl_evK p (ztl_avgK N)) 1 ω t| < aY ℓ) ∧
        (∀ ℓ ≤ L, ∀ t ∈ Set.Icc 0 (s : ℝ),
          (∫ r in Set.Ioc 0 t, ztl_brkZ F G z₁ m₁ z₂ m₂ s A ω r) ≤ bZ ℓ →
          |ztl_mZ F G z₁ m₁ z₂ m₂ s A ω t| < aZ ℓ))} ≤
      ENNReal.ofReal (((17 * (L + 1) : ℕ) : ℝ) * (2 * Real.exp (-q))) := by
  set a : ztl_Idx L → ℝ := fun j => match j with
    | Sum.inl (_, _, k, ℓ) => if k then aX ℓ else aY ℓ
    | Sum.inr ℓ => aZ ℓ
  set b : ztl_Idx L → ℝ := fun j => match j with
    | Sum.inl (_, _, k, ℓ) => if k then bX ℓ else bY ℓ
    | Sum.inr ℓ => bZ ℓ
  refine ztl_measure_le_of_violatesF hG hF hz₁ hm₁ hz₂ hm₂ (s := s) (A := A) a b q ?_ _ ?_
  · rintro (⟨⟨c₁, c₂⟩, p, k, ℓ⟩ | ℓ)
    · cases k
      · exact hqY ℓ (Nat.lt_succ_iff.1 ℓ.2)
      · exact hqX ℓ (Nat.lt_succ_iff.1 ℓ.2)
    · exact hqZ ℓ (Nat.lt_succ_iff.1 ℓ.2)
  · intro ω hω
    by_contra hall
    push Not at hall
    refine hω ⟨fun c₁ c₂ p ℓ hℓ => ?_, fun c₁ c₂ p ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
    · exact hall (Sum.inl ((c₁, c₂), p, true, ⟨ℓ, Nat.lt_succ_of_le hℓ⟩))
    · exact hall (Sum.inl ((c₁, c₂), p, false, ⟨ℓ, Nat.lt_succ_of_le hℓ⟩))
    · exact hall (Sum.inr ⟨ℓ, Nat.lt_succ_of_le hℓ⟩)

end BlockBand.Native.CEH.ETH
