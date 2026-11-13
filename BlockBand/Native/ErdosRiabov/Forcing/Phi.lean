module

public import BlockBand.Native.ErdosRiabov.Forcing.Defs

/-!
# Forcing bounds: the forcing control parameters `Φ`

* `phiIsoF ψ^I ψ^A X Y k`, `phiAvF ψ^I ψ^A X Y k` (`X = ℓη`, `Y = √(Nη)/(ℓη)`): the forcing
  control parameters `Φ^{iso,f}_k`, `Φ^{av,f}_k` (from the Erdős–Riabov forcing bounds, the
  isotropic one with the boundary slots `j = 0`, `j = k-1` included), evaluated at arbitrary
  values of the thresholds;
* the monomial bounds `*_le_phi*` used by the assembly (every listed monomial is `≤ Φ`);
* `phiIsoF_le_phiIso`, `phiAvF_le_phiAv`: at the thresholds `thrIso N ξ`, `thrAv N ξ`,
  `Φ` is the sum of the forcing terms of `Flow.Expo.isoTerms`/`avTerms` and hence `≤` the
  control parameters `phiIso`/`phiAv` of the exponent inequality.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Forcing

open Finset
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo
open BlockBand.Native.ErdosRiabov.Flow.Expo.Mono

/-!
## Definitions
-/

/-- The isotropic forcing control parameter `Φ^{iso,f}_k`. -/
def phiIsoF (psiI psiA : ℕ → ℝ) (X Y : ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ range (k - 2), psiI (2 + i) * X ^ (-(lossAlpha k - lossAlpha (2 + i)))) +
  (∑ i ∈ range k, Y * psiA 1 * psiI (1 + i) * psiI (k - (1 + i) + 1)) +
  psiA 1 * X ^ (-(1 / 2 : ℝ)) +
  (∑ i ∈ range (k - 1), psiI (2 + i) * psiI (k - (2 + i) + 2) * X ^ (-(1 / 2 : ℝ))) +
  psiA k * X ^ (-(lossAlpha k - lossBeta k)) * X ^ (-(1 / 2 : ℝ))

/-- The averaged forcing control parameter `Φ^{av,f}_k`. -/
def phiAvF (psiI psiA : ℕ → ℝ) (X Y : ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ range (k - 2), (psiA (2 + i) * X ^ (-(lossBeta k - lossBeta (2 + i))) +
    psiA (2 + i) * X ^ (-(lossBeta k - lossBeta (2 + i))) * psiI (k + 2 - (2 + i)) *
      X ^ (-(1 / 2 - lossAlpha (k + 2 - (2 + i)))))) +
  psiI 2 * psiA k * X ^ (-(1 / 2 : ℝ)) +
  (if k = 1 then Y * psiA 1 * psiI 2
   else if k ≤ 7 then Y * psiA 1 * psiI (k + 1) + psiA 1 * X ^ (-lossBeta k)
   else Y * psiA 1 * psiI 4 * psiI 5)

/-!
## Monomials are below `Φ`
-/

section Monomials

variable {psiI psiA : ℕ → ℝ} {X Y : ℝ} (hpsi : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n) (hX : 0 ≤ X)
  (hY : 0 ≤ Y)
include hpsi hX hY

theorem phiIsoF_parts (k : ℕ) :
    0 ≤ ∑ i ∈ range (k - 2), psiI (2 + i) * X ^ (-(lossAlpha k - lossAlpha (2 + i))) ∧
    0 ≤ ∑ i ∈ range k, Y * psiA 1 * psiI (1 + i) * psiI (k - (1 + i) + 1) ∧
    0 ≤ psiA 1 * X ^ (-(1 / 2 : ℝ)) ∧
    0 ≤ ∑ i ∈ range (k - 1), psiI (2 + i) * psiI (k - (2 + i) + 2) * X ^ (-(1 / 2 : ℝ)) ∧
    0 ≤ psiA k * X ^ (-(lossAlpha k - lossBeta k)) * X ^ (-(1 / 2 : ℝ)) := by
  have hr : ∀ e : ℝ, 0 ≤ X ^ e := fun e => Real.rpow_nonneg hX e
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hpsi _).1 (hr _),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (mul_nonneg hY (hpsi _).2) (hpsi _).1)
      (hpsi _).1, mul_nonneg (hpsi _).2 (hr _),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hpsi _).1 (hpsi _).1) (hr _),
    mul_nonneg (mul_nonneg (hpsi _).2 (hr _)) (hr _)⟩

theorem iso_fm_le_phi {k p : ℕ} (hp2 : 2 ≤ p) (hpk : p + 1 ≤ k) :
    psiI p * X ^ (-(lossAlpha k - lossAlpha p)) ≤ phiIsoF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phiIsoF_parts hpsi hX hY k
  have h := Finset.single_le_sum (f := fun i => psiI (2 + i) *
    X ^ (-(lossAlpha k - lossAlpha (2 + i)))) (fun i _ => mul_nonneg (hpsi _).1
      (Real.rpow_nonneg hX _)) (Finset.mem_range.mpr (show p - 2 < k - 2 by omega))
  simp only [show 2 + (p - 2) = p by omega] at h
  unfold phiIsoF
  linarith

theorem iso_f1_le_phi {k j : ℕ} (hj : j < k) :
    Y * psiA 1 * psiI (j + 1) * psiI (k - j) ≤ phiIsoF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phiIsoF_parts hpsi hX hY k
  have h := Finset.single_le_sum (f := fun i => Y * psiA 1 * psiI (1 + i) *
    psiI (k - (1 + i) + 1)) (fun i _ => mul_nonneg (mul_nonneg (mul_nonneg hY (hpsi _).2)
      (hpsi _).1) (hpsi _).1) (Finset.mem_range.mpr hj)
  simp only [show 1 + j = j + 1 by omega, show k - (j + 1) + 1 = k - j by omega] at h
  unfold phiIsoF
  linarith

theorem iso_fq_le_phi {k p : ℕ} (hp2 : 2 ≤ p) (hpk : p ≤ k) :
    psiI p * psiI (k + 2 - p) * X ^ (-(1 / 2 : ℝ)) ≤ phiIsoF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phiIsoF_parts hpsi hX hY k
  have h := Finset.single_le_sum (f := fun i => psiI (2 + i) * psiI (k - (2 + i) + 2) *
    X ^ (-(1 / 2 : ℝ))) (fun i _ => mul_nonneg (mul_nonneg (hpsi _).1 (hpsi _).1)
      (Real.rpow_nonneg hX _)) (Finset.mem_range.mpr (show p - 2 < k - 1 by omega))
  simp only [show 2 + (p - 2) = p by omega, show k - p + 2 = k + 2 - p by omega] at h
  unfold phiIsoF
  linarith

theorem iso_last_le_phi (k : ℕ) :
    psiA k * X ^ (-(lossAlpha k - lossBeta k)) * X ^ (-(1 / 2 : ℝ)) ≤
      phiIsoF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phiIsoF_parts hpsi hX hY k
  unfold phiIsoF
  linarith

theorem phiIsoF_nonneg (k : ℕ) : 0 ≤ phiIsoF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := phiIsoF_parts hpsi hX hY k
  unfold phiIsoF
  linarith

theorem phiAvF_parts (k : ℕ) :
    0 ≤ ∑ i ∈ range (k - 2), (psiA (2 + i) * X ^ (-(lossBeta k - lossBeta (2 + i))) +
      psiA (2 + i) * X ^ (-(lossBeta k - lossBeta (2 + i))) * psiI (k + 2 - (2 + i)) *
        X ^ (-(1 / 2 - lossAlpha (k + 2 - (2 + i))))) ∧
    0 ≤ psiI 2 * psiA k * X ^ (-(1 / 2 : ℝ)) ∧
    0 ≤ (if k = 1 then Y * psiA 1 * psiI 2
      else if k ≤ 7 then Y * psiA 1 * psiI (k + 1) + psiA 1 * X ^ (-lossBeta k)
      else Y * psiA 1 * psiI 4 * psiI 5) := by
  have hr : ∀ e : ℝ, 0 ≤ X ^ e := fun e => Real.rpow_nonneg hX e
  refine ⟨Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg (hpsi _).2 (hr _))
    (mul_nonneg (mul_nonneg (mul_nonneg (hpsi _).2 (hr _)) (hpsi _).1) (hr _)),
    mul_nonneg (mul_nonneg (hpsi _).1 (hpsi _).2) (hr _), ?_⟩
  have h1 := hpsi 1
  split_ifs
  · exact mul_nonneg (mul_nonneg hY h1.2) (hpsi _).1
  · exact add_nonneg (mul_nonneg (mul_nonneg hY h1.2) (hpsi _).1) (mul_nonneg h1.2 (hr _))
  · exact mul_nonneg (mul_nonneg (mul_nonneg hY h1.2) (hpsi _).1) (hpsi _).1

theorem phiAvF_nonneg (k : ℕ) : 0 ≤ phiAvF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3⟩ := phiAvF_parts hpsi hX hY k
  unfold phiAvF
  linarith

/-- The `j`-th summand of the first sum of `Φ^{av}` (both parts). -/
theorem av_sum_le_phi {k r : ℕ} (hr2 : 2 ≤ r) (hrk : r + 1 ≤ k) :
    psiA r * X ^ (-(lossBeta k - lossBeta r)) +
      psiA r * X ^ (-(lossBeta k - lossBeta r)) * psiI (k + 2 - r) *
        X ^ (-(1 / 2 - lossAlpha (k + 2 - r))) ≤ phiAvF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3⟩ := phiAvF_parts hpsi hX hY k
  have hr : ∀ e : ℝ, 0 ≤ X ^ e := fun e => Real.rpow_nonneg hX e
  have h := Finset.single_le_sum (f := fun i => psiA (2 + i) *
      X ^ (-(lossBeta k - lossBeta (2 + i))) +
    psiA (2 + i) * X ^ (-(lossBeta k - lossBeta (2 + i))) * psiI (k + 2 - (2 + i)) *
      X ^ (-(1 / 2 - lossAlpha (k + 2 - (2 + i)))))
    (fun i _ => add_nonneg (mul_nonneg (hpsi _).2 (hr _))
      (mul_nonneg (mul_nonneg (mul_nonneg (hpsi _).2 (hr _)) (hpsi _).1) (hr _)))
    (Finset.mem_range.mpr (show r - 2 < k - 2 by omega))
  simp only [show 2 + (r - 2) = r by omega] at h
  unfold phiAvF
  linarith

theorem av_fm_le_phi {k r : ℕ} (hr2 : 2 ≤ r) (hrk : r + 1 ≤ k) :
    psiA r * X ^ (-(lossBeta k - lossBeta r)) ≤ phiAvF psiI psiA X Y k := by
  have h := av_sum_le_phi hpsi hX hY hr2 hrk
  have : 0 ≤ psiA r * X ^ (-(lossBeta k - lossBeta r)) * psiI (k + 2 - r) *
      X ^ (-(1 / 2 - lossAlpha (k + 2 - r))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hpsi _).2 (Real.rpow_nonneg hX _)) (hpsi _).1)
      (Real.rpow_nonneg hX _)
  linarith

theorem av_fq_le_phi {k r : ℕ} (hr2 : 2 ≤ r) (hrk : r + 1 ≤ k) :
    psiA r * X ^ (-(lossBeta k - lossBeta r)) * psiI (k + 2 - r) *
      X ^ (-(1 / 2 - lossAlpha (k + 2 - r))) ≤ phiAvF psiI psiA X Y k := by
  have h := av_sum_le_phi hpsi hX hY hr2 hrk
  have : 0 ≤ psiA r * X ^ (-(lossBeta k - lossBeta r)) :=
    mul_nonneg (hpsi _).2 (Real.rpow_nonneg hX _)
  linarith

theorem av_fq2_le_phi (k : ℕ) : psiI 2 * psiA k * X ^ (-(1 / 2 : ℝ)) ≤ phiAvF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3⟩ := phiAvF_parts hpsi hX hY k
  unfold phiAvF
  linarith

theorem av_last_le_phi (k : ℕ) :
    (if k = 1 then Y * psiA 1 * psiI 2
      else if k ≤ 7 then Y * psiA 1 * psiI (k + 1) + psiA 1 * X ^ (-lossBeta k)
      else Y * psiA 1 * psiI 4 * psiI 5) ≤ phiAvF psiI psiA X Y k := by
  obtain ⟨h1, h2, h3⟩ := phiAvF_parts hpsi hX hY k
  unfold phiAvF
  linarith

end Monomials

/-!
## `Φ` at the thresholds is part of the control parameters
-/

section Thresholds

theorem sum_map_range' (F : ℕ → ℝ) (n : ℕ) :
    ∀ s : ℕ, ((List.range' s n).map F).sum = ∑ i ∈ range n, F (s + i) := by
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih (s + 1), Finset.sum_range_succ']
    simp only [add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]

theorem sum_flatMap_range' {α : Type*} (G : ℕ → List α) (v : α → ℝ) (n : ℕ) :
    ∀ s : ℕ, (((List.range' s n).flatMap G).map v).sum =
      ∑ i ∈ range n, ((G (s + i)).map v).sum := by
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [List.range'_succ, List.flatMap_cons, List.map_append, List.sum_append, ih (s + 1),
      Finset.sum_range_succ']
    simp only [add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]

theorem gval_div (m m' : Mono) : gval (m / m') = gval m - gval m' := by
  show gval (Mono.div m m') = _
  simp only [gval, Mono.div]
  push_cast
  ring

/-- The value of a pure `X`-monomial (`a = s = 0`). -/
theorem value_pureX {N ξ X Y : ℝ} {m : Mono} (ha : m.a = 0) (hs : m.s = 0) :
    m.value N ξ X Y = X ^ (-gval m) := by
  simp [Mono.value, ha, hs]

theorem alphaM_as (k : ℕ) : (alphaM k).a = 0 ∧ (alphaM k).s = 0 := by
  unfold alphaM
  split_ifs <;> simp [Mono.one, lossC]

theorem betaM_as (k : ℕ) : (betaM k).a = 0 ∧ (betaM k).s = 0 := by
  unfold betaM alphaM
  split_ifs <;> simp [Mono.one, lossC]

variable {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y)
include hN hX hY

omit hN hX hY in
theorem value_div_alpha {k j : ℕ} (hk : k ≤ 8) (hj : j ≤ 8) :
    (alphaM k / alphaM j).value N ξ X Y = X ^ (-(lossAlpha k - lossAlpha j)) := by
  rw [value_pureX (by show (alphaM k).a - (alphaM j).a = 0; simp [(alphaM_as k).1,
    (alphaM_as j).1]) (by show (alphaM k).s - (alphaM j).s = 0; simp [(alphaM_as k).2,
    (alphaM_as j).2]), gval_div, gval_alphaM hk, gval_alphaM hj]

omit hN hX hY in
theorem value_div_beta {k j : ℕ} (hk : k ≤ 8) (hj : j ≤ 8) :
    (betaM k / betaM j).value N ξ X Y = X ^ (-(lossBeta k - lossBeta j)) := by
  rw [value_pureX (by show (betaM k).a - (betaM j).a = 0; simp [(betaM_as k).1,
    (betaM_as j).1]) (by show (betaM k).s - (betaM j).s = 0; simp [(betaM_as k).2,
    (betaM_as j).2]), gval_div, gval_betaM hk, gval_betaM hj]

omit hN hX hY in
theorem value_div_alpha_beta {k : ℕ} (hk : k ≤ 8) :
    (alphaM k / betaM k).value N ξ X Y = X ^ (-(lossAlpha k - lossBeta k)) := by
  rw [value_pureX (by show (alphaM k).a - (betaM k).a = 0; simp [(alphaM_as k).1,
    (betaM_as k).1]) (by show (alphaM k).s - (betaM k).s = 0; simp [(alphaM_as k).2,
    (betaM_as k).2]), gval_div, gval_alphaM hk, gval_betaM hk]

omit hN hX hY in
theorem value_half_div_alpha {j : ℕ} (hj : j ≤ 8) :
    (lossC (1 / 2) / alphaM j).value N ξ X Y = X ^ (-(1 / 2 - lossAlpha j)) := by
  rw [value_pureX (by show (lossC (1 / 2)).a - (alphaM j).a = 0; simp [lossC,
    (alphaM_as j).1]) (by show (lossC (1 / 2)).s - (alphaM j).s = 0; simp [lossC,
    (alphaM_as j).2]), gval_div, gval_alphaM hj]
  simp only [gval, lossC]
  push_cast
  ring_nf

omit hN hX hY in
theorem value_lossC_half : (lossC (1 / 2)).value N ξ X Y = X ^ (-(1 / 2 : ℝ)) := by
  rw [(value_basic N ξ X Y (k := 0) (by norm_num) 0 (1 / 2)).2.2.2.2.1]
  push_cast
  ring_nf

theorem Term.value_nonneg' (T : Term) : 0 ≤ T.value N ξ X Y := by
  cases T with
  | mono m => exact m.value_nonneg hN hX hY
  | sqrtMono m => exact Real.sqrt_nonneg _
  | sqrtOne m => exact Real.sqrt_nonneg _
  | monoSqrtOne m m' => exact mul_nonneg (m.value_nonneg hN hX hY) (Real.sqrt_nonneg _)

theorem sum_value_nonneg (L : List Term) : 0 ≤ (L.map (Term.value N ξ X Y)).sum :=
  List.sum_nonneg fun y hy => by
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hy
    exact Term.value_nonneg' hN hX hY T

/-- **Isotropic case.** At the thresholds, `Φ^{iso}_k ≤ φ^{iso}_k`. -/
theorem phiIsoF_le_phiIso {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) :
    phiIsoF (thrIso N ξ) (thrAv N ξ) X Y k ≤ phiIso N ξ X Y k := by
  have vb := fun j => value_basic N ξ X Y (k := 0) (by norm_num) j 0
  have hmul := fun m m' => Mono.value_mul (ξ := ξ) hN hX hY m m'
  unfold phiIso isoTerms
  have hfil : ((List.range' 2 (k - 1)).filter (fun j => k - j + 2 ≤ 8)) =
      List.range' 2 (k - 1) := List.filter_eq_self.mpr fun j hj => by
    simp only [List.mem_range'_1] at hj
    simp only [decide_eq_true_eq]
    omega
  rw [hfil]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.map_map]
  rw [sum_map_range', sum_map_range', sum_map_range']
  have e1 : ∑ i ∈ range (k - 2), (Term.value N ξ X Y ∘ fun j =>
      Term.mono (pI j * (alphaM k / alphaM j))) (2 + i) =
      ∑ i ∈ range (k - 2), thrIso N ξ (2 + i) * X ^ (-(lossAlpha k - lossAlpha (2 + i))) :=
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.mp hi
      simp only [Function.comp_apply, Term.value, hmul, (vb _).1,
        value_div_alpha hk (show 2 + i ≤ 8 by omega)]
  have e2 : ∑ i ∈ range k, (Term.value N ξ X Y ∘ fun i =>
      Term.mono (sqY * pA 1 * pI i * pI (k - i + 1))) (1 + i) =
      ∑ i ∈ range k, Y * thrAv N ξ 1 * thrIso N ξ (1 + i) * thrIso N ξ (k - (1 + i) + 1) :=
    Finset.sum_congr rfl fun i _ => by
      simp only [Function.comp_apply, Term.value, hmul, (vb _).1, (vb _).2.1,
        (vb 0).2.2.2.2.2]
  have e3 : ∑ i ∈ range (k - 1), (Term.value N ξ X Y ∘ fun j =>
      Term.mono (pI j * pI (k - j + 2) * lossC (1 / 2))) (2 + i) =
      ∑ i ∈ range (k - 1), thrIso N ξ (2 + i) * thrIso N ξ (k - (2 + i) + 2) *
        X ^ (-(1 / 2 : ℝ)) :=
    Finset.sum_congr rfl fun i _ => by
      simp only [Function.comp_apply, Term.value, hmul, (vb _).1,
        value_lossC_half]
  rw [e1, e2, e3]
  have e4 : Term.value N ξ X Y (Term.mono (pA 1 * lossC (1 / 2))) =
      thrAv N ξ 1 * X ^ (-(1 / 2 : ℝ)) := by
    simp only [Term.value, hmul, (vb _).2.1, value_lossC_half]
  have e5 : Term.value N ξ X Y (Term.mono (pA k * (alphaM k / betaM k) * lossC (1 / 2))) =
      thrAv N ξ k * X ^ (-(lossAlpha k - lossBeta k)) * X ^ (-(1 / 2 : ℝ)) := by
    simp only [Term.value, hmul, (vb _).2.1, value_div_alpha_beta hk,
      value_lossC_half]
  rw [e4, e5]
  unfold phiIsoF
  have h0 := Term.value_nonneg' (ξ := ξ) hN hX hY (Term.mono Mono.one)
  have hq1 := Term.value_nonneg' (ξ := ξ) hN hX hY (Term.mono (pI k * (pI 2).half * lossC (1 / 4)))
  have hq2 := sum_value_nonneg (ξ := ξ) hN hX hY ((List.range' 2 ((k + 1) / 2 - 1)).map
    (fun j => Term.monoSqrtOne (pI (k - j + 1) * (alphaM k / alphaM (k - j + 1)))
      (pI (2 * j) * (lossC (1 / 2) / alphaM (2 * j)))))
  have hq3 := Term.value_nonneg' (ξ := ξ) hN hX hY (if k ≤ 4 then
      Term.sqrtOne (pI (2 * k) * (lossC (1 / 2) / alphaM (2 * k)))
    else if k ≤ 7 then
      Term.sqrtMono (pI (k - 1) * pI (k + 1) *
        (alphaM k * alphaM k / alphaM (k - 1) / alphaM (k + 1)))
    else Term.monoSqrtOne (pI 4) (pA 8 * (lossC 1 / betaM 8)))
  rw [List.map_map] at hq2
  linarith

/-- **Averaged case.** At the thresholds, `Φ^{av}_k ≤ φ^{av}_k`. -/
theorem phiAvF_le_phiAv {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) :
    phiAvF (thrIso N ξ) (thrAv N ξ) X Y k ≤ phiAv N ξ X Y k := by
  have vb := fun j => value_basic N ξ X Y (k := 0) (by norm_num) j 0
  have hmul := fun m m' => Mono.value_mul (ξ := ξ) hN hX hY m m'
  unfold phiAv avTerms
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [sum_flatMap_range']
  have e1 : ∑ i ∈ range (k - 2), (([Term.mono (pA (2 + i) * (betaM k / betaM (2 + i))),
      Term.mono (pA (2 + i) * (betaM k / betaM (2 + i)) * pI (k + 2 - (2 + i)) *
        (lossC (1 / 2) / alphaM (k + 2 - (2 + i))))]).map (Term.value N ξ X Y)).sum =
      ∑ i ∈ range (k - 2), (thrAv N ξ (2 + i) * X ^ (-(lossBeta k - lossBeta (2 + i))) +
        thrAv N ξ (2 + i) * X ^ (-(lossBeta k - lossBeta (2 + i))) * thrIso N ξ (k + 2 - (2 + i)) *
          X ^ (-(1 / 2 - lossAlpha (k + 2 - (2 + i))))) :=
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.mp hi
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Term.value, hmul, (vb _).1, (vb _).2.1, value_div_beta hk (show 2 + i ≤ 8 by omega),
        value_half_div_alpha (show k + 2 - (2 + i) ≤ 8 by omega)]
  rw [e1]
  have e2 : Term.value N ξ X Y (Term.mono (pI 2 * pA k * lossC (1 / 2))) =
      thrIso N ξ 2 * thrAv N ξ k * X ^ (-(1 / 2 : ℝ)) := by
    simp only [Term.value, hmul, (vb _).1, (vb _).2.1, value_lossC_half]
  rw [e2]
  have e3 : ((if k = 1 then [Term.mono (sqY * pA 1 * pI 2)]
      else if k ≤ 7 then [Term.mono (sqY * pA 1 * pI (k + 1)), Term.mono (pA 1 * betaM k)]
      else [Term.mono (sqY * pA 1 * pI 4 * pI 5)]).map (Term.value N ξ X Y)).sum =
      (if k = 1 then Y * thrAv N ξ 1 * thrIso N ξ 2
       else if k ≤ 7 then Y * thrAv N ξ 1 * thrIso N ξ (k + 1) + thrAv N ξ 1 * X ^ (-lossBeta k)
       else Y * thrAv N ξ 1 * thrIso N ξ 4 * thrIso N ξ 5) := by
    split_ifs with h1 h7
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Term.value, hmul, (vb _).1, (vb _).2.1, (vb 0).2.2.2.2.2]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Term.value, hmul, (vb _).1, (vb _).2.1, (vb 0).2.2.2.2.2,
        (value_basic N ξ X Y hk 0 0).2.2.2.1]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Term.value, hmul, (vb _).1, (vb _).2.1, (vb 0).2.2.2.2.2]
  rw [e3]
  unfold phiAvF
  have h0 := Term.value_nonneg' (ξ := ξ) hN hX hY (Term.mono Mono.one)
  have hq := Term.value_nonneg' (ξ := ξ) hN hX hY (if k ≤ 3 then
      Term.sqrtOne (pI (2 * k + 2) * (lossC (1 / 2) / alphaM (2 * k + 2)))
    else if k ≤ 7 then Term.mono (pI (k + 1))
    else Term.monoSqrtOne (pI 5) (pA 8 * (lossC 1 / betaM 8)))
  have hD := sum_value_nonneg (ξ := ξ) hN hX hY (if k % 2 = 0 then
      [Term.mono (pA (k - 1) * (betaM k / betaM (k - 1)))] ++
        (if 4 ≤ k then [Term.mono (pA (k - 2) * (betaM k / betaM (k - 2)))] else [])
    else [])
  linarith

end Thresholds

end BlockBand.Native.ErdosRiabov.Forcing
