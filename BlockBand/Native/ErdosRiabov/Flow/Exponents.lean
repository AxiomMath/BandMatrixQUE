module

public import BlockBand.Native.ErdosRiabov.Flow.Const

/-!
# The exponent inequality

**Result** (`exponentIneq`): for `N ≥ 1`, `0 < ξ ≤ δ₀/100`, `ν = ξ/640`, `X ≥ N^{δ₀}`,
`0 < Y ≤ N^{-δ₀/2}` (the scale bounds) and `1 ≤ k ≤ 8`, every monomial of the
expansion (`√(1+x) ≤ 1+√x`) of `φ^{iso}_k` is `≤ N^ξ` or `≤ N^{-ν/2} ψ^iso_k`, and likewise for
`φ^{av}_k` with `ψ^av_k`. Hence (`phi_le`)
`φ^{iso/av}_k ≤ C (N^ξ + N^{-ν/2} ψ^{iso/av}_k)` with `C` the number of monomials.

**Proof.** Each monomial is `≤ N^{aξ - gδ₀ - sδ₀/2}` (`Mono.value_le`). With rational brackets
`α₆ ∈ [0.35355, 0.35356]`, `α₇ ∈ [0.43301, 0.43302]` the inequality `aξ - gδ₀ - sδ₀/2 ≤ cξ`
is linear in `ξ ∈ (0, δ₀/100]`, so it reduces to the rational test `Mono.okB c` at the two
endpoints (`Mono.exponent_le_of_okB`). The finitely many tests are checked by `decide +kernel`
(`monos_okB`) on `ℚ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Flow.Expo

/-!
## Symbolic monomials
-/

/-- Exponent data of `N^{aξ} X^{-(g₀ + g₆α₆ + g₇α₇)} Y^{s}`. -/
structure Mono where
  a : ℚ
  g0 : ℚ
  g6 : ℚ
  g7 : ℚ
  s : ℚ

namespace Mono

/-- The monomial `1`. -/
def one : Mono := ⟨0, 0, 0, 0, 0⟩

/-- Product of monomials. -/
def mul (m m' : Mono) : Mono := ⟨m.a + m'.a, m.g0 + m'.g0, m.g6 + m'.g6, m.g7 + m'.g7, m.s + m'.s⟩

/-- Quotient of monomials. -/
def div (m m' : Mono) : Mono := ⟨m.a - m'.a, m.g0 - m'.g0, m.g6 - m'.g6, m.g7 - m'.g7, m.s - m'.s⟩

/-- Square root of a monomial. -/
def half (m : Mono) : Mono := ⟨m.a / 2, m.g0 / 2, m.g6 / 2, m.g7 / 2, m.s / 2⟩

instance : Mul Mono := ⟨mul⟩
instance : Div Mono := ⟨div⟩

@[simp] theorem mul_a (m m' : Mono) : (m * m').a = m.a + m'.a := rfl
@[simp] theorem mul_g0 (m m' : Mono) : (m * m').g0 = m.g0 + m'.g0 := rfl
@[simp] theorem mul_g6 (m m' : Mono) : (m * m').g6 = m.g6 + m'.g6 := rfl
@[simp] theorem mul_g7 (m m' : Mono) : (m * m').g7 = m.g7 + m'.g7 := rfl
@[simp] theorem mul_s (m m' : Mono) : (m * m').s = m.s + m'.s := rfl

/-- `ψ^iso_j = N^{ξ+jν}`, `ν = ξ/640`. -/
def pI (j : ℕ) : Mono := ⟨1 + (j : ℚ) / 640, 0, 0, 0, 0⟩

/-- `ψ^av_j = N^{ξ+(j+3/2)ν}`. -/
def pA (j : ℕ) : Mono := ⟨1 + ((j : ℚ) + 3 / 2) / 640, 0, 0, 0, 0⟩

/-- `(ℓη)^{-q}` for a rational `q`. -/
def lossC (q : ℚ) : Mono := ⟨0, q, 0, 0, 0⟩

/-- `Y = √(Nη)/(ℓη)`. -/
def sqY : Mono := ⟨0, 0, 0, 0, 1⟩

/-- `(ℓη)^{-α_k}` for the Erdős–Riabov loss exponents at `K = 8`:
`α_k = 0` (`k ≤ 4`), `α₅ = 1/4`, `α₆ = √2/4`, `α₇ = √3/4`, `α₈ = 1/2` (valid for `k ≤ 8`). -/
def alphaM (k : ℕ) : Mono :=
  if k ≤ 4 then one else if k = 5 then lossC (1 / 4) else if k = 6 then ⟨0, 0, 1, 0, 0⟩
  else if k = 7 then ⟨0, 0, 0, 1, 0⟩ else lossC (1 / 2)

/-- `(ℓη)^{-β_k}`: `β_k = α_{k+1}` (`k ≤ 7`), `β₈ = 1/2 + α₅`. -/
def betaM (k : ℕ) : Mono := if k ≤ 7 then alphaM (k + 1) else alphaM 5 * lossC (1 / 2)

/-!
## Values
-/

/-- `α₆ = √2/4`. -/
def a6 : ℝ := Real.sqrt 2 / 4

/-- `α₇ = √3/4`. -/
def a7 : ℝ := Real.sqrt 3 / 4

/-- The loss exponent `g₀ + g₆ α₆ + g₇ α₇`. -/
def gval (m : Mono) : ℝ := (m.g0 : ℝ) + (m.g6 : ℝ) * a6 + (m.g7 : ℝ) * a7

/-- The value `N^{aξ} X^{-g} Y^{s}`. -/
def value (N ξ X Y : ℝ) (m : Mono) : ℝ :=
  N ^ ((m.a : ℝ) * ξ) * X ^ (-gval m) * Y ^ (m.s : ℝ)

/-!
## The rational test
-/

/-- Rational brackets for `α₆` and `α₇`. -/
def lo6 : ℚ := 35355 / 100000
def hi6 : ℚ := 35356 / 100000
def lo7 : ℚ := 43301 / 100000
def hi7 : ℚ := 43302 / 100000

/-- Rational lower bound of the loss exponent. -/
def glo (m : Mono) : ℚ :=
  m.g0 + (if 0 ≤ m.g6 then m.g6 * lo6 else m.g6 * hi6) +
    (if 0 ≤ m.g7 then m.g7 * lo7 else m.g7 * hi7)

/-- The endpoint test for `aξ - gδ₀ - sδ₀/2 ≤ cξ` on `0 < ξ ≤ δ₀/100`. -/
def okB (c : ℚ) (m : Mono) : Bool :=
  decide (0 ≤ m.s) && decide (0 ≤ glo m) && decide ((m.a - c) / 100 ≤ glo m + m.s / 2)

end Mono

open Mono

/-!
## Terms and the control parameters
-/

/-- Terms of the control parameters: `m`, `√m`, `√(1+m)`, `m √(1+m')`. -/
inductive Term where
  | mono : Mono → Term
  | sqrtMono : Mono → Term
  | sqrtOne : Mono → Term
  | monoSqrtOne : Mono → Mono → Term

namespace Term

/-- The value of a term. -/
def value (N ξ X Y : ℝ) : Term → ℝ
  | mono m => m.value N ξ X Y
  | sqrtMono m => Real.sqrt (m.value N ξ X Y)
  | sqrtOne m => Real.sqrt (1 + m.value N ξ X Y)
  | monoSqrtOne m m' => m.value N ξ X Y * Real.sqrt (1 + m'.value N ξ X Y)

/-- The monomials of a term after `√(1+x) ≤ 1 + √x`. -/
def expand : Term → List Mono
  | mono m => [m]
  | sqrtMono m => [m.half]
  | sqrtOne m => [Mono.one, m.half]
  | monoSqrtOne m m' => [m, m * m'.half]

end Term

open Term

/-- The terms of `φ^{iso}_{k,t}` (`1 ≤ k ≤ 8`, `K = 8`), in the order: `ψ_{k,0} = 1`;
forcing: `Σ_{j=2}^{k-1} ψ_j/(ℓη)^{α_k-α_j}`, `Σ_{i=1}^{k} Y ψ^av_1 ψ_i ψ_{k-i+1}`,
`ψ^av_1/√(ℓη)`, `Σ_{j=2}^{k} ψ_jψ_{k-j+2}/√(ℓη)` (`k-j+2 ≤ K`),
`ψ^av_k/(ℓη)^{1/2+α_k-β_k}`; QV: `ψ_k√ψ_2/(ℓη)^{1/4}`,
`Σ_{j=2}^{⌊(k+1)/2⌋} ψ_{k-j+1}/(ℓη)^{α_k-α_{k-j+1}} √(1+ψ_{2j}/(ℓη)^{1/2-α_{2j}})`, and `φ̃`. -/
def isoTerms (k : ℕ) : List Term :=
  [mono Mono.one] ++
  (List.range' 2 (k - 2)).map (fun j => mono (pI j * (alphaM k / alphaM j))) ++
  (List.range' 1 k).map (fun i => mono (sqY * pA 1 * pI i * pI (k - i + 1))) ++
  [mono (pA 1 * lossC (1 / 2))] ++
  ((List.range' 2 (k - 1)).filter (fun j => k - j + 2 ≤ 8)).map
    (fun j => mono (pI j * pI (k - j + 2) * lossC (1 / 2))) ++
  [mono (pA k * (alphaM k / betaM k) * lossC (1 / 2))] ++
  [mono (pI k * (pI 2).half * lossC (1 / 4))] ++
  (List.range' 2 ((k + 1) / 2 - 1)).map (fun j =>
    monoSqrtOne (pI (k - j + 1) * (alphaM k / alphaM (k - j + 1)))
      (pI (2 * j) * (lossC (1 / 2) / alphaM (2 * j)))) ++
  [if k ≤ 4 then sqrtOne (pI (2 * k) * (lossC (1 / 2) / alphaM (2 * k)))
   else if k ≤ 7 then
     sqrtMono (pI (k - 1) * pI (k + 1) * (alphaM k * alphaM k / alphaM (k - 1) / alphaM (k + 1)))
   else monoSqrtOne (pI 4) (pA 8 * (lossC 1 / betaM 8))]

/-- The terms of `φ^{av}_{k,t}` (`1 ≤ k ≤ 8`), in the order: `ψ_{k,0} = 1`; forcing sums
`Σ_{j=2}^{k-1} ψ^av_j/(ℓη)^{β_k-β_j}` and
`Σ_{j=2}^{k-1} ψ^av_j ψ_{k+2-j}/(ℓη)^{β_k-β_j+1/2-α_{k+2-j}}`,
`ψ_2ψ^av_k/√(ℓη)`; QV `φ^{av,qv}_k`; the remaining forcing terms (`Y ψ^av_1 ψ_2` at `k = 1`;
`Y ψ^av_1 ψ_{k+1}` and `ψ^av_1/(ℓη)^{β_k}` for `2 ≤ k ≤ 7`; `Y ψ^av_1 ψ_4 ψ_5` at `k = 8`);
the saturated bracket (`k` even): `ψ^av_{k-1}/(ℓη)^{β_k-β_{k-1}}` and, for `k ≥ 4`,
`ψ^av_{k-2}/(ℓη)^{β_k-β_{k-2}}`. -/
def avTerms (k : ℕ) : List Term :=
  [mono Mono.one] ++
  (List.range' 2 (k - 2)).flatMap (fun j =>
    [mono (pA j * (betaM k / betaM j)),
     mono (pA j * (betaM k / betaM j) * pI (k + 2 - j) *
       (lossC (1 / 2) / alphaM (k + 2 - j)))]) ++
  [mono (pI 2 * pA k * lossC (1 / 2))] ++
  [if k ≤ 3 then sqrtOne (pI (2 * k + 2) * (lossC (1 / 2) / alphaM (2 * k + 2)))
   else if k ≤ 7 then mono (pI (k + 1))
   else monoSqrtOne (pI 5) (pA 8 * (lossC 1 / betaM 8))] ++
  (if k = 1 then [mono (sqY * pA 1 * pI 2)]
   else if k ≤ 7 then [mono (sqY * pA 1 * pI (k + 1)), mono (pA 1 * betaM k)]
   else [mono (sqY * pA 1 * pI 4 * pI 5)]) ++
  (if k % 2 = 0 then
     [mono (pA (k - 1) * (betaM k / betaM (k - 1)))] ++
       (if 4 ≤ k then [mono (pA (k - 2) * (betaM k / betaM (k - 2)))] else [])
   else [])

/-- The monomials of `φ^{iso}_k`. -/
def isoMonos (k : ℕ) : List Mono := (isoTerms k).flatMap Term.expand

/-- The monomials of `φ^{av}_k`. -/
def avMonos (k : ℕ) : List Mono := (avTerms k).flatMap Term.expand

/-- `φ^{iso}_{k,t}` as a function of `N, ξ, X = ℓ_tη_t, Y = √(Nη_t)/(ℓ_tη_t)`. -/
def phiIso (N ξ X Y : ℝ) (k : ℕ) : ℝ := ((isoTerms k).map (Term.value N ξ X Y)).sum

/-- `φ^{av}_{k,t}`. -/
def phiAv (N ξ X Y : ℝ) (k : ℕ) : ℝ := ((avTerms k).map (Term.value N ξ X Y)).sum

/-- Rational exponent of `N^{-ν/2} ψ^iso_k`, in units of `ξ`. -/
def isoTarget (k : ℕ) : ℚ := 1 + (k : ℚ) / 640 - 1 / 1280

/-- Rational exponent of `N^{-ν/2} ψ^av_k`, in units of `ξ`. -/
def avTarget (k : ℕ) : ℚ := 1 + ((k : ℚ) + 3 / 2) / 640 - 1 / 1280

/-- The finite rational check: every monomial passes the test with `c = 1` (it is `≤ N^ξ`) or the
test with the exponent of `N^{-ν/2} ψ_k`. -/
theorem monos_okB :
    (List.range' 1 8).all (fun k =>
      (isoMonos k).all (fun m => m.okB 1 || m.okB (isoTarget k)) &&
      (avMonos k).all (fun m => m.okB 1 || m.okB (avTarget k))) = true := by
  decide +kernel

/-!
## Analytic bridge
-/

/-- `ψ^iso_k = N^{ξ+kν}` with `ν = ξ/640`. -/
def thrIso (N ξ : ℝ) (k : ℕ) : ℝ := N ^ (ξ + k * (ξ / 640))

/-- `ψ^av_k = N^{ξ+(k+3/2)ν}` with `ν = ξ/640`. -/
def thrAv (N ξ : ℝ) (k : ℕ) : ℝ := N ^ (ξ + (k + 3 / 2) * (ξ / 640))

theorem a6_bounds : (lo6 : ℝ) ≤ a6 ∧ a6 ≤ hi6 := by
  unfold lo6 hi6 a6
  constructor
  · rw [le_div_iff₀ (by norm_num), Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [div_le_iff₀ (by norm_num), Real.sqrt_le_left (by norm_num)]
    norm_num

theorem a7_bounds : (lo7 : ℝ) ≤ a7 ∧ a7 ≤ hi7 := by
  unfold lo7 hi7 a7
  constructor
  · rw [le_div_iff₀ (by norm_num), Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [div_le_iff₀ (by norm_num), Real.sqrt_le_left (by norm_num)]
    norm_num

theorem Mono.glo_le_gval (m : Mono) : (glo m : ℝ) ≤ gval m := by
  have h6 := a6_bounds
  have h7 := a7_bounds
  unfold glo gval
  have e6 : ((if 0 ≤ m.g6 then m.g6 * lo6 else m.g6 * hi6 : ℚ) : ℝ) ≤ (m.g6 : ℝ) * a6 := by
    split_ifs with h
    · push_cast
      exact mul_le_mul_of_nonneg_left h6.1 (by exact_mod_cast h)
    · push_cast
      have : (m.g6 : ℝ) < 0 := by exact_mod_cast not_le.mp h
      nlinarith
  have e7 : ((if 0 ≤ m.g7 then m.g7 * lo7 else m.g7 * hi7 : ℚ) : ℝ) ≤ (m.g7 : ℝ) * a7 := by
    split_ifs with h
    · push_cast
      exact mul_le_mul_of_nonneg_left h7.1 (by exact_mod_cast h)
    · push_cast
      have : (m.g7 : ℝ) < 0 := by exact_mod_cast not_le.mp h
      nlinarith
  push_cast at e6 e7 ⊢
  linarith

/-- Size of a monomial: `N^{aξ} X^{-g} Y^{s} ≤ N^{aξ - gδ₀ - sδ₀/2}` when `g, s ≥ 0`,
`X ≥ N^{δ₀}`, `0 < Y ≤ N^{-δ₀/2}`, `N ≥ 1`. -/
theorem Mono.value_le {N ξ δ₀ X Y : ℝ} (hN : 1 ≤ N) (hX : N ^ δ₀ ≤ X) (hY0 : 0 < Y)
    (hY : Y ≤ N ^ (-δ₀ / 2)) (m : Mono) (hg : 0 ≤ gval m) (hs : (0 : ℝ) ≤ m.s) :
    m.value N ξ X Y ≤ N ^ ((m.a : ℝ) * ξ - gval m * δ₀ - (m.s : ℝ) * δ₀ / 2) := by
  have hN0 : 0 < N := by linarith
  have hNd : 0 < N ^ δ₀ := Real.rpow_pos_of_pos hN0 _
  have h1 : X ^ (-gval m) ≤ N ^ (-gval m * δ₀) := by
    rw [mul_comm, Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow_of_nonpos hNd hX (by linarith)
  have h2 : Y ^ (m.s : ℝ) ≤ N ^ ((m.s : ℝ) * (-δ₀ / 2)) := by
    rw [mul_comm, Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow hY0.le hY hs
  unfold Mono.value
  rw [show (m.a : ℝ) * ξ - gval m * δ₀ - (m.s : ℝ) * δ₀ / 2 =
      (m.a : ℝ) * ξ + -gval m * δ₀ + (m.s : ℝ) * (-δ₀ / 2) by ring,
    Real.rpow_add hN0, Real.rpow_add hN0]
  have hA : 0 ≤ N ^ ((m.a : ℝ) * ξ) := (Real.rpow_pos_of_pos hN0 _).le
  have hXg : 0 ≤ X ^ (-gval m) := Real.rpow_nonneg (hNd.le.trans hX) _
  have hYs : 0 ≤ Y ^ (m.s : ℝ) := Real.rpow_nonneg hY0.le _
  calc N ^ ((m.a : ℝ) * ξ) * X ^ (-gval m) * Y ^ (m.s : ℝ)
      ≤ N ^ ((m.a : ℝ) * ξ) * N ^ (-gval m * δ₀) * Y ^ (m.s : ℝ) := by gcongr
    _ ≤ N ^ ((m.a : ℝ) * ξ) * N ^ (-gval m * δ₀) * N ^ ((m.s : ℝ) * (-δ₀ / 2)) := by gcongr

/-- The endpoint reduction: if `okB c m`, then `0 ≤ g`, `0 ≤ s` and, for
`0 < ξ ≤ δ₀/100`, `aξ - gδ₀ - sδ₀/2 ≤ cξ`. -/
theorem Mono.exponent_le_of_okB {c : ℚ} {m : Mono} (h : m.okB c = true) {ξ δ₀ : ℝ}
    (hξ : 0 < ξ) (hξδ : ξ ≤ δ₀ / 100) :
    0 ≤ gval m ∧ (0 : ℝ) ≤ m.s ∧
      (m.a : ℝ) * ξ - gval m * δ₀ - (m.s : ℝ) * δ₀ / 2 ≤ (c : ℝ) * ξ := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, hg⟩, hlin⟩ := h
  have hgl := m.glo_le_gval
  have hs' : (0 : ℝ) ≤ m.s := by exact_mod_cast hs
  have hg' : (0 : ℝ) ≤ glo m := by exact_mod_cast hg
  have hlin' : ((m.a : ℝ) - c) / 100 ≤ glo m + (m.s : ℝ) / 2 := by exact_mod_cast hlin
  have hδ : 0 < δ₀ := by linarith
  refine ⟨hg'.trans hgl, hs', ?_⟩
  have key : ((m.a : ℝ) - c) * ξ ≤ (gval m + (m.s : ℝ) / 2) * δ₀ := by
    rcases le_or_gt ((m.a : ℝ) - c) 0 with hac | hac
    · have : 0 ≤ (gval m + (m.s : ℝ) / 2) * δ₀ := by
        apply mul_nonneg _ hδ.le
        linarith
      nlinarith
    · calc ((m.a : ℝ) - c) * ξ ≤ ((m.a : ℝ) - c) * (δ₀ / 100) :=
            mul_le_mul_of_nonneg_left hξδ hac.le
        _ = ((m.a : ℝ) - c) / 100 * δ₀ := by ring
        _ ≤ (glo m + (m.s : ℝ) / 2) * δ₀ := mul_le_mul_of_nonneg_right hlin' hδ.le
        _ ≤ (gval m + (m.s : ℝ) / 2) * δ₀ := by nlinarith
  nlinarith

/-- A monomial passing `okB c` is `≤ N^{cξ}`. -/
theorem Mono.value_le_of_okB {c : ℚ} {m : Mono} (h : m.okB c = true) {N ξ δ₀ X Y : ℝ}
    (hN : 1 ≤ N) (hξ : 0 < ξ) (hξδ : ξ ≤ δ₀ / 100) (hX : N ^ δ₀ ≤ X) (hY0 : 0 < Y)
    (hY : Y ≤ N ^ (-δ₀ / 2)) :
    m.value N ξ X Y ≤ N ^ ((c : ℝ) * ξ) := by
  obtain ⟨hg, hs, hlin⟩ := m.exponent_le_of_okB h hξ hξδ
  exact (m.value_le hN hX hY0 hY hg hs).trans (Real.rpow_le_rpow_of_exponent_le hN hlin)

theorem rpow_isoTarget {N : ℝ} (hN : 0 < N) (ξ : ℝ) (k : ℕ) :
    N ^ ((isoTarget k : ℝ) * ξ) = N ^ (-(ξ / 640) / 2) * thrIso N ξ k := by
  unfold thrIso isoTarget
  rw [← Real.rpow_add hN]
  congr 1
  push_cast
  ring

theorem rpow_avTarget {N : ℝ} (hN : 0 < N) (ξ : ℝ) (k : ℕ) :
    N ^ ((avTarget k : ℝ) * ξ) = N ^ (-(ξ / 640) / 2) * thrAv N ξ k := by
  unfold thrAv avTarget
  rw [← Real.rpow_add hN]
  congr 1
  push_cast
  ring

/-- Let `K = 8`, `N ≥ 1`, `0 < ξ ≤ δ₀/100`, `ν = ξ/640`, and let `X, Y` satisfy
`X ≥ N^{δ₀}`, `0 < Y ≤ N^{-δ₀/2}` (for `X = ℓ_tη_t`, `Y = √(Nη_t)/(ℓ_tη_t)` these are Lemma
*scales* (a), (c)).
Then for every `1 ≤ k ≤ 8`, every monomial of `φ^{iso}_{k,t}` is
`≤ N^ξ` or `≤ N^{-ν/2} ψ^iso_k`, and every monomial of `φ^{av}_{k,t}` is `≤ N^ξ` or
`≤ N^{-ν/2} ψ^av_k`.
Uniform in `N, X, Y, ξ, δ₀` (no `N₀`).
-/
theorem exponentIneq {N ξ δ₀ X Y : ℝ} (hN : 1 ≤ N) (hξ : 0 < ξ) (hξδ : ξ ≤ δ₀ / 100)
    (hX : N ^ δ₀ ≤ X) (hY0 : 0 < Y) (hY : Y ≤ N ^ (-δ₀ / 2)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk8 : k ≤ 8) :
    (∀ m ∈ isoMonos k, m.value N ξ X Y ≤ N ^ ξ ∨
        m.value N ξ X Y ≤ N ^ (-(ξ / 640) / 2) * thrIso N ξ k) ∧
      (∀ m ∈ avMonos k, m.value N ξ X Y ≤ N ^ ξ ∨
        m.value N ξ X Y ≤ N ^ (-(ξ / 640) / 2) * thrAv N ξ k) := by
  have hN0 : 0 < N := by linarith
  have hall := monos_okB
  rw [List.all_eq_true] at hall
  have hk := hall k (List.mem_range'_1.mpr ⟨hk1, by omega⟩)
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hk
  obtain ⟨hiso, hav⟩ := hk
  have one_case : ∀ m : Mono, m.okB 1 = true → m.value N ξ X Y ≤ N ^ ξ := by
    intro m hm
    have := m.value_le_of_okB hm hN hξ hξδ hX hY0 hY
    simpa using this
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rcases hiso m hm with h | h
    · exact Or.inl (one_case m h)
    · right
      rw [← rpow_isoTarget hN0]
      exact m.value_le_of_okB h hN hξ hξδ hX hY0 hY
  · rcases hav m hm with h | h
    · exact Or.inl (one_case m h)
    · right
      rw [← rpow_avTarget hN0]
      exact m.value_le_of_okB h hN hξ hξδ hX hY0 hY

/-!
## From monomials to the control parameters
-/

theorem Mono.value_nonneg {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y) (m : Mono) :
    0 ≤ m.value N ξ X Y := by
  unfold Mono.value
  have := Real.rpow_pos_of_pos hN ((m.a : ℝ) * ξ)
  have := Real.rpow_pos_of_pos hX (-gval m)
  have := Real.rpow_pos_of_pos hY (m.s : ℝ)
  positivity

theorem Mono.value_one (N ξ X Y : ℝ) : Mono.one.value N ξ X Y = 1 := by
  simp [Mono.value, Mono.one, gval]

theorem Mono.value_mul {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y) (m m' : Mono) :
    (m * m').value N ξ X Y = m.value N ξ X Y * m'.value N ξ X Y := by
  simp only [Mono.value, gval, mul_a, mul_g0, mul_g6, mul_g7, mul_s]
  push_cast
  rw [show ((m.a : ℝ) + m'.a) * ξ = m.a * ξ + m'.a * ξ by ring, Real.rpow_add hN,
    show -((m.g0 : ℝ) + m'.g0 + (m.g6 + m'.g6) * a6 + (m.g7 + m'.g7) * a7) =
      -(m.g0 + m.g6 * a6 + m.g7 * a7) + -(m'.g0 + m'.g6 * a6 + m'.g7 * a7) by ring,
    Real.rpow_add hX, Real.rpow_add hY]
  ring

theorem Mono.value_half {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y) (m : Mono) :
    m.half.value N ξ X Y = Real.sqrt (m.value N ξ X Y) := by
  simp only [Mono.value, half, gval]
  push_cast
  have hA := Real.rpow_pos_of_pos hN ((m.a : ℝ) * ξ)
  have hB := Real.rpow_pos_of_pos hX (-((m.g0 : ℝ) + m.g6 * a6 + m.g7 * a7))
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hA.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le, ← Real.rpow_mul hX.le, ← Real.rpow_mul hY.le]
  congr 1
  · congr 1
    · congr 1
      ring
    · congr 1
      ring
  · congr 1
    ring

theorem sqrt_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt hx
  nlinarith [Real.sqrt_nonneg x]

theorem Term.value_le_expand {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y) (T : Term) :
    T.value N ξ X Y ≤ (T.expand.map (Mono.value N ξ X Y)).sum := by
  cases T with
  | mono m => simp [Term.value, Term.expand]
  | sqrtMono m => simp [Term.value, Term.expand, Mono.value_half hN hX hY]
  | sqrtOne m =>
    simp only [Term.value, Term.expand, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Mono.value_one, Mono.value_half hN hX hY, add_zero]
    exact sqrt_one_add_le (m.value_nonneg (ξ := ξ) hN hX hY)
  | monoSqrtOne m m' =>
    simp only [Term.value, Term.expand, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Mono.value_mul hN hX hY, Mono.value_half hN hX hY, add_zero]
    have h := sqrt_one_add_le (m'.value_nonneg (ξ := ξ) hN hX hY)
    have h0 := m.value_nonneg (ξ := ξ) hN hX hY
    nlinarith

theorem sum_value_le_expand {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y)
    (L : List Term) :
    (L.map (Term.value N ξ X Y)).sum ≤ ((L.flatMap Term.expand).map (Mono.value N ξ X Y)).sum := by
  induction L with
  | nil => simp
  | cons T L ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    exact add_le_add (T.value_le_expand hN hX hY) ih

theorem sum_le_length_mul {L : List Mono} {f : Mono → ℝ} {B : ℝ} (h : ∀ m ∈ L, f m ≤ B) :
    (L.map f).sum ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    have h1 := h m List.mem_cons_self
    have h2 := ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
    linarith

/-- **Consequence of the exponent inequality**: under the hypotheses of `exponentIneq`, for
`1 ≤ k ≤ 8`, `φ^{iso}_k ≤ C^{iso}_k (N^ξ + N^{-ν/2} ψ^iso_k)` and
`φ^{av}_k ≤ C^{av}_k (N^ξ + N^{-ν/2} ψ^av_k)`, with `C` the number of monomials (absolute
constants). -/
theorem phi_le {N ξ δ₀ X Y : ℝ} (hN : 1 ≤ N) (hξ : 0 < ξ) (hξδ : ξ ≤ δ₀ / 100)
    (hX : N ^ δ₀ ≤ X) (hY0 : 0 < Y) (hY : Y ≤ N ^ (-δ₀ / 2)) {k : ℕ} (hk1 : 1 ≤ k)
    (hk8 : k ≤ 8) :
    phiIso N ξ X Y k ≤
        (isoMonos k).length * (N ^ ξ + N ^ (-(ξ / 640) / 2) * thrIso N ξ k) ∧
      phiAv N ξ X Y k ≤
        (avMonos k).length * (N ^ ξ + N ^ (-(ξ / 640) / 2) * thrAv N ξ k) := by
  have hN0 : 0 < N := by linarith
  have hδ : 0 < δ₀ := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hX
  obtain ⟨hiso, hav⟩ := exponentIneq hN hξ hξδ hX hY0 hY hk1 hk8
  have hA : 0 ≤ N ^ ξ := (Real.rpow_pos_of_pos hN0 _).le
  have hB : 0 ≤ N ^ (-(ξ / 640) / 2) := (Real.rpow_pos_of_pos hN0 _).le
  have hI : 0 ≤ thrIso N ξ k := (Real.rpow_pos_of_pos hN0 _).le
  have hV : 0 ≤ thrAv N ξ k := (Real.rpow_pos_of_pos hN0 _).le
  constructor
  · refine (sum_value_le_expand hN0 hX0 hY0 _).trans (sum_le_length_mul fun m hm => ?_)
    rcases hiso m hm with h | h
    · nlinarith
    · nlinarith
  · refine (sum_value_le_expand hN0 hX0 hY0 _).trans (sum_le_length_mul fun m hm => ?_)
    rcases hav m hm with h | h
    · nlinarith
    · nlinarith

/-!
## Faithfulness of the symbolic data
-/

/-- Real Erdős–Riabov loss exponents at `K = 8`: `α_k = 0` for `k ≤ 4` and
`α_k = ½√(2k/8 - 1)` otherwise. -/
def lossAlpha (k : ℕ) : ℝ := if k ≤ 4 then 0 else Real.sqrt (2 * (k : ℝ) / 8 - 1) / 2

/-- `β_k = α_{k+1}` (`k ≤ 7`), `β₈ = 1/2 + α₅`. -/
def lossBeta (k : ℕ) : ℝ := if k ≤ 7 then lossAlpha (k + 1) else 1 / 2 + lossAlpha 5

theorem gval_alphaM {k : ℕ} (hk : k ≤ 8) : gval (alphaM k) = lossAlpha k := by
  rcases (show k ≤ 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with h | h | h | h | h
  · simp [alphaM, lossAlpha, h, gval, Mono.one]
  · subst h
    rw [show alphaM 5 = lossC (1 / 4) by simp [alphaM],
      show lossAlpha 5 = Real.sqrt (2 * ((5 : ℕ) : ℝ) / 8 - 1) / 2 by simp [lossAlpha],
      show 2 * ((5 : ℕ) : ℝ) / 8 - 1 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp only [gval, lossC]
    push_cast
    ring
  · subst h
    rw [show alphaM 6 = ⟨0, 0, 1, 0, 0⟩ by simp [alphaM],
      show lossAlpha 6 = Real.sqrt (2 * ((6 : ℕ) : ℝ) / 8 - 1) / 2 by simp [lossAlpha],
      show 2 * ((6 : ℕ) : ℝ) / 8 - 1 = (Real.sqrt 2 / 2) ^ 2 by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num,
      Real.sqrt_sq (by positivity)]
    simp only [gval, a6]
    push_cast
    ring
  · subst h
    rw [show alphaM 7 = ⟨0, 0, 0, 1, 0⟩ by simp [alphaM],
      show lossAlpha 7 = Real.sqrt (2 * ((7 : ℕ) : ℝ) / 8 - 1) / 2 by simp [lossAlpha],
      show 2 * ((7 : ℕ) : ℝ) / 8 - 1 = (Real.sqrt 3 / 2) ^ 2 by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num,
      Real.sqrt_sq (by positivity)]
    simp only [gval, a7]
    push_cast
    ring
  · subst h
    rw [show alphaM 8 = lossC (1 / 2) by simp [alphaM],
      show lossAlpha 8 = Real.sqrt (2 * ((8 : ℕ) : ℝ) / 8 - 1) / 2 by simp [lossAlpha],
      show 2 * ((8 : ℕ) : ℝ) / 8 - 1 = 1 by norm_num, Real.sqrt_one]
    simp only [gval, lossC]
    push_cast
    ring

theorem gval_mul (m m' : Mono) : gval (m * m') = gval m + gval m' := by
  simp only [gval, mul_g0, mul_g6, mul_g7]
  push_cast
  ring

theorem gval_betaM {k : ℕ} (hk : k ≤ 8) : gval (betaM k) = lossBeta k := by
  unfold betaM lossBeta
  split_ifs with h
  · exact gval_alphaM (by omega)
  · rw [gval_mul, gval_alphaM (by norm_num)]
    simp only [gval, lossC]
    push_cast
    ring

/-- The symbolic data are the stated quantities: `pI j` is `ψ^iso_j`, `pA j` is `ψ^av_j`,
`alphaM k` and `betaM k` are `(ℓη)^{-α_k}`, `(ℓη)^{-β_k}` (`k ≤ 8`), `lossC q` is `(ℓη)^{-q}`
and `sqY` is `Y`. -/
theorem value_basic (N ξ X Y : ℝ) {k : ℕ} (hk : k ≤ 8) (j : ℕ) (q : ℚ) :
    (pI j).value N ξ X Y = thrIso N ξ j ∧ (pA j).value N ξ X Y = thrAv N ξ j ∧
      (alphaM k).value N ξ X Y = X ^ (-lossAlpha k) ∧
      (betaM k).value N ξ X Y = X ^ (-lossBeta k) ∧
      (lossC q).value N ξ X Y = X ^ (-(q : ℝ)) ∧ sqY.value N ξ X Y = Y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Mono.value, pI, gval, thrIso]
    push_cast
    simp only [zero_mul, add_zero, neg_zero, Real.rpow_zero, mul_one]
    congr 1
    ring
  · simp only [Mono.value, pA, gval, thrAv]
    push_cast
    simp only [zero_mul, add_zero, neg_zero, Real.rpow_zero, mul_one]
    congr 1
    ring
  · have hz : ((alphaM k).a : ℝ) = 0 ∧ ((alphaM k).s : ℝ) = 0 := by
      unfold alphaM
      split_ifs <;> simp [Mono.one, lossC]
    simp only [Mono.value, hz.1, hz.2, zero_mul, Real.rpow_zero, one_mul, mul_one,
      gval_alphaM hk]
  · have hz : ((betaM k).a : ℝ) = 0 ∧ ((betaM k).s : ℝ) = 0 := by
      unfold betaM alphaM
      split_ifs <;> simp [Mono.one, lossC]
    simp only [Mono.value, hz.1, hz.2, zero_mul, Real.rpow_zero, one_mul, mul_one,
      gval_betaM hk]
  · simp [Mono.value, lossC, gval]
  · simp [Mono.value, sqY, gval]

/-- The thresholds `ψ^iso`, `ψ^av` at `ξ = d.xi` are `thrIso`, `thrAv`. -/
theorem psi_eq_thr (d : VSData) (N : ℕ) (k : ℕ) :
    d.psiIso N k = thrIso N d.xi k ∧ d.psiAv N k = thrAv N d.xi k := by
  unfold VSData.psiIso VSData.psiAv thrIso thrAv VSData.nu
  exact ⟨rfl, rfl⟩

end BlockBand.Native.ErdosRiabov.Flow.Expo
