module

public import BlockBand.Native.ErdosRiabov.Prop.GoodProps
public import BlockBand.Native.ErdosRiabov.Prop.OneStep

/-!
# Regularized propagator estimates

Bounds on the saturated tensor propagator composed with one or two regularized kernels, acting on
the averaged size function.

Setting as for `goodProps_av`, with all factors saturated: `P̂^{⊗k} = goodProp S P.z
(fun _ => .sat) s t`. The regularized kernel on coordinate `j` with anchor `a` is
`ringOp S z t j a f x = Σ_b Θ̊^{x_a}_t(x_j, b) f(x[j ↦ b])` (the Erdős–Riabov `Θ̊^{(j)}_t`), and
`ringKer` is its
entrywise absolute value. With `k` sites (0-based), `Θ̊^{(k)}` is `j = k-1`, anchor `k-2`,
and `Θ̊^{(k-2)}` is `j = k-3`, anchor `k-4`. `C_reg = onestepConst d`, `C_P = kernelActionConst d`.

* `regProps_oneRing` (one ring, `k = n+2`):
  `Σ_y |P̂^{⊗k}(x,y)| |Θ̊^{(k)}|[s^av_{k,s}](y) ≤ C_reg C_P^k η_t⁻¹ s^av_{k,t}(x)`;
* `regProps_twoRings` (two rings, `k = n+4`):
  `Σ_y |P̂^{⊗k}(x,y)| |Θ̊^{(k-2)}| |Θ̊^{(k)}|[s^av_{k,s}](y) ≤`
  `C_reg² C_P^k η_t⁻² (L_t/L_s) s^av_{k,t}(x)`;
* `*_apply`: the same for `|P̂^{⊗k} ∘ Θ̊ [f]|` when `|f| ≤ φ s^av_{k,s}`.

The parity hypothesis "`k` even" plays no role and is not assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.LemmaK
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open Matrix
open scoped BigOperators ComplexConjugate

/-!
## The regularized one-coordinate operators
-/

/-- `Θ̊^{(j)}_t f (x) = Σ_b Θ̊^{x_a}_t(x_j, b) f(x[j ↦ b])` (anchor coordinate `a`). -/
def ringOp {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a : Fin k)
    (f : (Fin k → Fin N) → ℂ) : (Fin k → Fin N) → ℂ :=
  fun x => ∑ b, vsThetaRing S (semicircleM z) (conj (semicircleM z)) t (x a) (x j) b *
    f (Function.update x j b)

/-- The entrywise absolute value of the kernel of `ringOp`. -/
def ringKer {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a : Fin k) :
    (Fin k → Fin N) → Fin N → ℝ :=
  fun x b => ‖vsThetaRing S (semicircleM z) (conj (semicircleM z)) t (x a) (x j) b‖

theorem norm_ringOp_le {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) (j a : Fin k)
    (f : (Fin k → Fin N) → ℂ) (x : Fin k → Fin N) :
    ‖ringOp S z t j a f x‖ ≤ slotOp j (ringKer S z t j a) (fun y => ‖f y‖) x := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [norm_mul]
  rfl

/-- Interior step with both endpoints equal to the last coordinate. -/
private theorem slotOp_sqrt_linkProd_le_end {N n : ℕ} (j : Fin (n + 2)) (hj : j.val + 1 < n + 2)
    {K : (Fin (n + 2) → Fin N) → Fin N → ℝ} {V V' : ℕ → Fin N → Fin N → ℝ}
    (hVV : ∀ i, i ≠ j.val → i ≠ j.val + 1 → V i = V' i) (hV : ∀ i u w, 0 ≤ V i u w)
    (x : Fin (n + 2) → Fin N) {κ : ℝ}
    (hstep : ∑ c, K x c * Real.sqrt (V j.val
        (Psi.isoPoint (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) x j.val) c *
        V (j.val + 1) c (Psi.isoPoint (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) x
          (j.val + 2))) ≤
      κ * Real.sqrt (V' j.val
        (Psi.isoPoint (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) x j.val) (x j) *
        V' (j.val + 1) (x j) (Psi.isoPoint (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) x
          (j.val + 2)))) :
    slotOp j K
        (fun y => Real.sqrt (linkProd V (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y)) x ≤
      κ * Real.sqrt (linkProd V' (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) x) := by
  have hne : Fin.last (n + 1) ≠ j := by
    intro h
    rw [← h] at hj
    simp at hj
  have heq : slotOp j K
      (fun y => Real.sqrt (linkProd V (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y)) x =
      slotOp j K
      (fun y => Real.sqrt (linkProd V (x (Fin.last (n + 1))) (x (Fin.last (n + 1))) y)) x := by
    unfold slotOp
    refine Finset.sum_congr rfl fun c _ => ?_
    beta_reduce
    rw [Function.update_of_ne hne]
  rw [heq]
  exact slotOp_sqrt_linkProd_le j hj hVV hV _ _ x hstep

/-!
## Steps for saturated factors and the ring
-/

section Steps

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
  (ht1 : t ≤ 1)
include hm hW hz hs0 hst ht1

/-- Step C for `P̂` (item (P5) of `kernelActions`):
`Σ_a |P̂(u,a)| √(Υ_t(w,a)Υ_t(a,w')) ≤ C_P (η_s/η_t) √(Υ_t(w,u)Υ_t(u,w'))`. -/
theorem goodProp_stepC_sat (u w w' : Fin (m * W)) :
    ∑ a, ‖goodPropFactor (shortRingProfile d.b m W) z .sat s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w a *
          polynomialControl (m * W) W d.D (vsHeight z t) a w') ≤
      kernelActionConst d * (vsHeight z s / vsHeight z t) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
          polynomialControl (m * W) W d.D (vsHeight z t) u w') :=
  (kernelActions d hm hW hz hs0 hst ht1 hs0 (hst.trans ht1) hs0 (hst.trans ht1)).2.2.2.2.2.2.2
    u w w'

/-- Step B with the links swapped (`(s,t) → (t,t)`), every factor. -/
theorem goodProp_stepB_swap (c : PropFactor) (u w w' : Fin (m * W)) :
    ∑ a, ‖goodPropFactor (shortRingProfile d.b m W) z c s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) w a *
          polynomialControl (m * W) W d.D (vsHeight z t) a w') ≤
      kernelActionConst d *
        Real.sqrt ((ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s) /
          (ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t)) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
          polynomialControl (m * W) W d.D (vsHeight z t) u w') := by
  have h := goodProp_stepB d hm hW hz hs0 hst ht1 c u w' w
  have hsym : ∀ r (x y : Fin (m * W)), polynomialControl (m * W) W d.D (vsHeight z r) x y =
      polynomialControl (m * W) W d.D (vsHeight z r) y x :=
    fun r x y => polynomialControl_symm _ _ _ _ x y
  calc _ = ∑ a, ‖goodPropFactor (shortRingProfile d.b m W) z c s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w' a *
          polynomialControl (m * W) W d.D (vsHeight z s) a w) :=
        Finset.sum_congr rfl fun a _ => by
          rw [hsym s w a, hsym t a w', mul_comm (polynomialControl _ _ _ (vsHeight z s) a w)]
    _ ≤ _ := h
    _ = _ := by rw [hsym t w' u, hsym t u w, mul_comm (polynomialControl _ _ _ _ u w')]

omit hs0 in
/-- `onestepScale` at `r = s`: `η_s⁻¹ (ℓ_sℓ_tη_t/W²) √(Υ_t(p,u)Υ_t(u,q))`. -/
theorem onestepScale_self (p u q : Fin (m * W)) :
    onestepScale d m W z s t s p u q =
      1 / vsHeight z s * (ErdosRiabov.localizationLength (m * W) W (vsHeight z s) *
        ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t / (W : ℝ) ^ 2) *
      Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) p u *
        polynomialControl (m * W) W d.D (vsHeight z t) u q) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hLs := mul_pos (loc_pos hN hW hηs) hηs
  unfold onestepScale
  rw [div_self hLs.ne', Real.sqrt_one, mul_one]

end Steps

/-!
## One ring
-/

section Rings

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : Psi.PsiData (m * W))
  (hPW : P.W = W) (hPD : P.D = d.D) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
  {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
include hm hW hPW hPD hz hs0 hst ht1

/-- For chain length
`k = n+2`, all sites `x`:
`Σ_y |P̂^{⊗k}(x,y)| (|Θ̊^{(k)}_t| s^av_{k,s})(y) ≤ C_reg C_P^k η_t⁻¹ s^av_{k,t}(x)`, where
`|Θ̊^{(k)}_t|` acts on the last coordinate with anchor `x_{k-2}`.
-/
theorem regProps_oneRing {n : ℕ} (x : Fin (n + 2) → Fin (m * W)) :
    ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
        slotOp (Fin.last (n + 1))
          (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 1)) ⟨n, by omega⟩)
          (fun y' => P.sAv y' s) y ≤
      onestepConst d * kernelActionConst d ^ (n + 2) / vsHeight P.z t * P.sAv x t := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  have hs1 : s ≤ 1 := hst.trans ht1
  have ht0 : 0 ≤ t := hs0.trans hst
  obtain ⟨hηs, -, hLs, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW hs0 hs1
  obtain ⟨hηt, -, hLt, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW ht0 ht1
  have hu : ∀ r, P.ups r = polynomialControl (m * W) W d.D (vsHeight P.z r) := by
    intro r
    unfold Psi.PsiData.ups
    rw [hPW, hPD]
  have hl : ∀ r, P.lEta r =
      ErdosRiabov.localizationLength (m * W) W (vsHeight P.z r) * vsHeight P.z r := by
    intro r
    unfold Psi.PsiData.lEta
    rw [hPW]
  have hUp : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ u w, 0 ≤ P.ups r u w := fun r _ hr u w => by
    rw [hu]; exact (polynomialControl_pos hN hW d.D (vsHeight_pos hη hr) u w).le
  have hCP := kernelActionConst_ge_one d
  have hCreg : 0 ≤ onestepConst d := by
    unfold onestepConst
    have := vsCK_pos d
    have := d.cm_pos
    have := d.one_le_C1pp
    positivity
  set Fn := goodPropNorm (shortRingProfile d.b m W) P.z (fun _ : Fin (n + 2) => PropFactor.sat)
    s t with hFn
  have hF0 : ∀ j u v, 0 ≤ Fn j u v := fun j u v => norm_nonneg _
  set ls := ErdosRiabov.localizationLength (m * W) W (vsHeight P.z s) with hls
  set lt := ErdosRiabov.localizationLength (m * W) W (vsHeight P.z t) with hlt
  set κR := onestepConst d * (1 / vsHeight P.z s * (ls * lt * vsHeight P.z t / (W : ℝ) ^ 2))
    with hκR
  have hκR0 : 0 ≤ κR := by
    have := loc_pos hN hW hηs
    have := loc_pos hN hW hηt
    positivity
  set V : ℕ → ℕ → Fin (m * W) → Fin (m * W) → ℝ :=
    fun m' i => P.ups (if i ≤ m' ∨ i = n + 1 then t else s) with hV
  have hVn : ∀ m' i u w, 0 ≤ V m' i u w := by
    intro m' i u w
    rw [hV]
    dsimp only
    split_ifs
    · exact hUp t ht0 ht1 u w
    · exact hUp s hs0 hs1 u w
  have hVt : ∀ m' i, i ≤ m' ∨ i = n + 1 → V m' i = P.ups t := by
    intro m' i h
    rw [hV]; dsimp only; rw [ite_eq_left h]
  have hVs : ∀ m' i, ¬(i ≤ m' ∨ i = n + 1) → V m' i = P.ups s := by
    intro m' i h
    rw [hV]; dsimp only; rw [ite_eq_right h]
  -- the ring step
  have hR : ∀ y : Fin (n + 2) → Fin (m * W),
      slotOp (Fin.last (n + 1))
        (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 1)) ⟨n, by omega⟩)
        (fun y' => Real.sqrt (linkProd (fun _ => P.ups s) (y' (Fin.last (n + 1)))
          (y' (Fin.last (n + 1))) y')) y ≤
      κR * Real.sqrt (linkProd (V 0) (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y) := by
    intro y
    refine slotOp_sqrt_linkProd_last_le (fun i h0 h1 => (hVs 0 i (by omega)).symm)
      (fun i u w => hUp s hs0 hs1 u w) y ?_
    rw [hVt 0 (n + 1) (Or.inr rfl), hVt 0 0 (Or.inl le_rfl), hu, hu]
    have h := (thetaringAction d hm hW hz hs0 hst ht1 (Or.inl rfl) (y ⟨n, by omega⟩)
      (y (Fin.last (n + 1))) (y 0)).1
    rw [onestepScale_self d hm hW hz hst ht1] at h
    refine le_of_eq_of_le ?_ (h.trans (le_of_eq ?_))
    · rfl
    · rw [hκR]; ring
  -- the propagators
  set ρ := Real.sqrt (P.lEta s / P.lEta t) with hρ
  set κ : ℕ → ℝ := fun i => if i < n then kernelActionConst d * ρ
    else kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) with hκ
  have hκ0 : ∀ i, 0 ≤ κ i := by
    intro i
    rw [hκ]
    dsimp only
    split_ifs
    · exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    · exact mul_nonneg (by linarith) (div_nonneg hηs.le hηt.le)
  have hVV : ∀ m' i, i ≠ m' → i ≠ m' + 1 → V m' i = V (m' + 1) i := by
    intro m' i h1 h2
    by_cases h : i ≤ m' ∨ i = n + 1
    · rw [hVt m' i h, hVt (m' + 1) i (by omega)]
    · rw [hVs m' i h, hVs (m' + 1) i (by omega)]
  have hstep : ∀ (m' : ℕ) (hm' : m' + 1 < n + 2) (y : Fin (n + 2) → Fin (m * W)),
      ∑ e, Fn ⟨m', by omega⟩ (y ⟨m', by omega⟩) e *
          Real.sqrt (V m' m' (Psi.isoPoint (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y m')
            e * V m' (m' + 1) e
              (Psi.isoPoint (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y (m' + 2))) ≤
        κ m' * Real.sqrt (V (m' + 1) m'
            (Psi.isoPoint (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y m') (y ⟨m', by omega⟩) *
          V (m' + 1) (m' + 1) (y ⟨m', by omega⟩)
            (Psi.isoPoint (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y (m' + 2))) := by
    intro m' hm' y
    rw [hVt m' m' (Or.inl le_rfl), hVt (m' + 1) m' (Or.inl (by omega)),
      hVt (m' + 1) (m' + 1) (Or.inl le_rfl)]
    by_cases hlt' : m' < n
    · rw [hVs m' (m' + 1) (by omega), hu, hu, hκ]
      dsimp only
      rw [ite_eq_left hlt', hρ, hl s, hl t]
      exact goodProp_stepB d hm hW hz hs0 hst ht1 _ _ _ _
    · rw [hVt m' (m' + 1) (Or.inr (by omega)), hu, hκ]
      dsimp only
      rw [ite_eq_right hlt']
      exact goodProp_stepC_sat d hm hW hz hs0 hst ht1 _ _ _
  have hit := tensorRSet_iter_le Fn hF0 V hVn (fun y => y (Fin.last (n + 1)))
    (fun y => y (Fin.last (n + 1)))
    (fun y j e hj => Function.update_of_ne (by intro h; subst h; simp at hj) _ _)
    (fun y j e hj => Function.update_of_ne (by intro h; subst h; simp at hj) _ _)
    κ hκ0 hVV hstep (n + 1) (by omega)
  have hlinkT : ∀ y : Fin (n + 2) → Fin (m * W), linkProd (V (n + 1)) (y (Fin.last (n + 1)))
      (y (Fin.last (n + 1))) y = linkProd (fun _ => P.ups t) (y (Fin.last (n + 1)))
      (y (Fin.last (n + 1))) y :=
    fun y => linkProd_congr (fun i hi => hVt (n + 1) i (Or.inl (by omega))) _ _ y
  have hprod : ∏ i ∈ Finset.range (n + 1), κ i = (kernelActionConst d * ρ) ^ n *
      (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t)) := by
    rw [Finset.prod_range_succ, hκ]
    dsimp only
    rw [ite_eq_right (lt_irrefl n), Finset.prod_congr rfl (fun i hi =>
      ite_eq_left (Finset.mem_range.mp hi)), Finset.prod_const, Finset.card_range]
  have huniv : (Finset.univ : Finset (Fin (n + 2))) =
      insert (Fin.last (n + 1)) (slotsBelow (n + 2) (n + 1)) := by
    ext j
    simp only [slotsBelow, Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and,
      Fin.ext_iff, Fin.val_last, true_iff]
    omega
  have hnot : Fin.last (n + 1) ∉ slotsBelow (n + 2) (n + 1) := by simp [slotsBelow]
  set e : ℝ := -((n + 2 : ℕ) : ℝ) / 2 with he
  have hAe : 0 ≤ P.lEta s ^ e := Real.rpow_nonneg hLs.le _
  -- assemble
  have hstep1 : ∀ y : Fin (n + 2) → Fin (m * W),
      slotOp (Fin.last (n + 1))
          (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 1)) ⟨n, by omega⟩)
          (fun y' => P.sAv y' s) y ≤
        P.lEta s ^ e * (κR * Real.sqrt (linkProd (V 0) (y (Fin.last (n + 1)))
          (y (Fin.last (n + 1))) y)) := by
    intro y
    have hfun : (fun y' : Fin (n + 2) → Fin (m * W) => P.sAv y' s) = fun y' => P.lEta s ^ e *
        Real.sqrt (linkProd (fun _ => P.ups s) (y' (Fin.last (n + 1))) (y' (Fin.last (n + 1)))
          y') := funext fun y' => sAv_eq_linkProd P y' s
    rw [hfun, slotOp_const_mul]
    exact mul_le_mul_of_nonneg_left (hR y) hAe
  have hK0 : ∀ (y : Fin (n + 2) → Fin (m * W)) (c : Fin (m * W)),
      0 ≤ Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) c := fun y c => hF0 _ _ _
  have hlast := slotOp_sqrt_linkProd_last_le (K := fun y c =>
      Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) c) (V := fun _ => P.ups t)
    (V' := fun _ => P.ups t) (fun _ _ _ => rfl) (fun i u w => hUp t ht0 ht1 u w) x
    (κ := kernelActionConst d * (vsHeight P.z s / vsHeight P.z t)) (by
      simp only [hFn, goodPropNorm, hu]
      exact goodProp_stepC_sat d hm hW hz hs0 hst ht1 _ _ _)
  have hPi0 : 0 ≤ ∏ i ∈ Finset.range (n + 1), κ i := Finset.prod_nonneg fun i _ => hκ0 i
  have hmain : ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
      slotOp (Fin.last (n + 1))
        (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 1)) ⟨n, by omega⟩)
        (fun y' => P.sAv y' s) y ≤
      P.lEta s ^ e * κR * ((∏ i ∈ Finset.range (n + 1), κ i) *
        (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
          Real.sqrt (linkProd (fun _ => P.ups t) (x (Fin.last (n + 1)))
            (x (Fin.last (n + 1))) x))) := by
    calc _ ≤ ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
          (P.lEta s ^ e * (κR * Real.sqrt (linkProd (V 0) (y (Fin.last (n + 1)))
            (y (Fin.last (n + 1))) y))) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hstep1 y) (norm_nonneg _)
      _ = P.lEta s ^ e * κR * (tensorR Fn *ᵥ fun y => Real.sqrt (linkProd (V 0)
            (y (Fin.last (n + 1))) (y (Fin.last (n + 1))) y)) x := by
          simp only [norm_goodProp, Matrix.mulVec, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hAe hκR0)
          rw [← tensorRSet_univ, huniv, (tensorRSet_insert Fn hnot).1, ← Matrix.mulVec_mulVec,
            mulVec_tensorRSet_single]
          calc _ ≤ slotOp (Fin.last (n + 1))
                (fun y c => Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) c)
                (fun y => (∏ i ∈ Finset.range (n + 1), κ i) *
                  Real.sqrt (linkProd (fun _ => P.ups t) (y (Fin.last (n + 1)))
                    (y (Fin.last (n + 1))) y)) x :=
                slotOp_mono _ hK0 (fun y => (hit y).trans_eq (by rw [hlinkT y])) x
            _ = _ := by rw [slotOp_const_mul]
            _ ≤ _ := mul_le_mul_of_nonneg_left hlast hPi0
  refine hmain.trans ?_
  -- arithmetic
  have hpow := goodProp_rpow_av hLs hLt n
  have hsav := sAv_eq_linkProd P x t
  have hlsp := loc_pos hN hW hηs
  have hltp := loc_pos hN hW hηt
  have hWr : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hsq : lt ^ 2 * vsHeight P.z t ≤ (W : ℝ) ^ 2 := (loc_sq_mul hN hηt).1
  set Q := 1 / vsHeight P.z s * (ls * lt * vsHeight P.z t / (W : ℝ) ^ 2) *
    (vsHeight P.z s / vsHeight P.z t) ^ 2 * (P.lEta t / P.lEta s) with hQ
  have hQv : Q = lt ^ 2 / (W : ℝ) ^ 2 := by
    rw [hQ, hl s, hl t, ← hls, ← hlt]
    have h1 : ls ≠ 0 := hlsp.ne'
    have h2 : lt ≠ 0 := hltp.ne'
    have h3 := hηs.ne'
    have h4 := hηt.ne'
    field_simp
  have hQle : Q ≤ 1 / vsHeight P.z t := by
    rw [hQv, div_le_div_iff₀ (by positivity) hηt]
    linarith
  have hsAv0 : 0 ≤ P.sAv x t := by
    rw [hsav]; exact mul_nonneg (Real.rpow_nonneg hLt.le _) (Real.sqrt_nonneg _)
  calc P.lEta s ^ e * κR * ((∏ i ∈ Finset.range (n + 1), κ i) *
        (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
          Real.sqrt (linkProd (fun _ => P.ups t) (x (Fin.last (n + 1)))
            (x (Fin.last (n + 1))) x)))
      = onestepConst d * kernelActionConst d ^ (n + 2) * Q * P.sAv x t := by
        rw [hprod, hκR, hsav, hQ, mul_pow, ← he]
        have h2 := hpow
        rw [← hρ] at h2
        calc _ = onestepConst d * kernelActionConst d ^ (n + 2) *
              (1 / vsHeight P.z s * (ls * lt * vsHeight P.z t / (W : ℝ) ^ 2) *
                (vsHeight P.z s / vsHeight P.z t) ^ 2) * (P.lEta s ^ e * ρ ^ n) *
              Real.sqrt (linkProd (fun _ => P.ups t) (x (Fin.last (n + 1)))
                (x (Fin.last (n + 1))) x) := by ring
          _ = _ := by rw [h2]; ring
    _ ≤ onestepConst d * kernelActionConst d ^ (n + 2) * (1 / vsHeight P.z t) * P.sAv x t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle
          (mul_nonneg hCreg (pow_nonneg (by linarith) _))) hsAv0
    _ = _ := by ring

/-- For chain length
`k = n+4`, all sites `x`:
`Σ_y |P̂^{⊗k}(x,y)| (|Θ̊^{(k-2)}_t| |Θ̊^{(k)}_t| s^av_{k,s})(y) ≤
C_reg² C_P^k η_t⁻² (L_t/L_s) s^av_{k,t}(x)`, where `|Θ̊^{(k)}_t|` acts on the last coordinate with
anchor `x_{k-2}` and `|Θ̊^{(k-2)}_t|` on coordinate `k-3` with anchor `x_{k-4}` (0-based).
-/
theorem regProps_twoRings {n : ℕ} (x : Fin (n + 2 + 2) → Fin (m * W)) :
    ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
        slotOp ⟨n + 1, by omega⟩
          (ringKer (shortRingProfile d.b m W) P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩)
          (slotOp (Fin.last (n + 2 + 1))
            (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩)
            (fun y' => P.sAv y' s)) y ≤
      onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z t ^ 2 *
        (P.lEta t / P.lEta s) * P.sAv x t := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  have hs1 : s ≤ 1 := hst.trans ht1
  have ht0 : 0 ≤ t := hs0.trans hst
  obtain ⟨hηs, -, hLs, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW hs0 hs1
  obtain ⟨hηt, -, hLt, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW ht0 ht1
  have hu : ∀ r, P.ups r = polynomialControl (m * W) W d.D (vsHeight P.z r) := by
    intro r
    unfold Psi.PsiData.ups
    rw [hPW, hPD]
  have hl : ∀ r, P.lEta r =
      ErdosRiabov.localizationLength (m * W) W (vsHeight P.z r) * vsHeight P.z r := by
    intro r
    unfold Psi.PsiData.lEta
    rw [hPW]
  have hUp : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ u w, 0 ≤ P.ups r u w := fun r _ hr u w => by
    rw [hu]; exact (polynomialControl_pos hN hW d.D (vsHeight_pos hη hr) u w).le
  have hCP := kernelActionConst_ge_one d
  have hCreg : 0 ≤ onestepConst d := by
    unfold onestepConst
    have := vsCK_pos d
    have := d.cm_pos
    have := d.one_le_C1pp
    positivity
  set Fn := goodPropNorm (shortRingProfile d.b m W) P.z
    (fun _ : Fin (n + 2 + 2) => PropFactor.sat) s t with hFn
  have hF0 : ∀ j u v, 0 ≤ Fn j u v := fun j u v => norm_nonneg _
  set ls := ErdosRiabov.localizationLength (m * W) W (vsHeight P.z s) with hls
  set lt := ErdosRiabov.localizationLength (m * W) W (vsHeight P.z t) with hlt
  have hlsp : 0 < ls := loc_pos hN hW hηs
  have hltp : 0 < lt := loc_pos hN hW hηt
  set X := 1 / vsHeight P.z s * (ls * lt * vsHeight P.z t / (W : ℝ) ^ 2) with hX
  have hX0 : 0 ≤ X := by positivity
  set ρ := Real.sqrt (P.lEta s / P.lEta t) with hρ
  have hρ' : Real.sqrt (ls * vsHeight P.z s / (lt * vsHeight P.z t)) = ρ := by
    rw [hρ, hl s, hl t]
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set L : Fin (n + 2 + 2) := Fin.last (n + 2 + 1) with hL
  set R1 := ringKer (shortRingProfile d.b m W) P.z t L ⟨n + 2, by omega⟩ with hR1
  set R3 := ringKer (shortRingProfile d.b m W) P.z t (⟨n + 1, by omega⟩ : Fin (n + 2 + 2))
    ⟨n, by omega⟩ with hR3d
  -- V1: links 0, n+3;  V2: links 0, n+2, n+3;  V3 = family below at stage 0
  set V1 : ℕ → Fin (m * W) → Fin (m * W) → ℝ :=
    fun i => P.ups (if i = 0 ∨ i = n + 3 then t else s) with hV1
  set V2 : ℕ → Fin (m * W) → Fin (m * W) → ℝ :=
    fun i => P.ups (if i = 0 ∨ i = n + 2 ∨ i = n + 3 then t else s) with hV2
  set V : ℕ → ℕ → Fin (m * W) → Fin (m * W) → ℝ :=
    fun m' i => P.ups (if i ≤ m' ∨ (n + 1 ≤ i ∧ i ≤ n + 3) then t else s) with hV
  have hpos1 : ∀ i u w, 0 ≤ V1 i u w := by
    intro i u w; rw [hV1]; dsimp only; split_ifs
    · exact hUp t ht0 ht1 u w
    · exact hUp s hs0 hs1 u w
  have hpos2 : ∀ i u w, 0 ≤ V2 i u w := by
    intro i u w; rw [hV2]; dsimp only; split_ifs
    · exact hUp t ht0 ht1 u w
    · exact hUp s hs0 hs1 u w
  have hVn : ∀ m' i u w, 0 ≤ V m' i u w := by
    intro m' i u w; rw [hV]; dsimp only; split_ifs
    · exact hUp t ht0 ht1 u w
    · exact hUp s hs0 hs1 u w
  have hVt : ∀ m' i, i ≤ m' ∨ (n + 1 ≤ i ∧ i ≤ n + 3) → V m' i = P.ups t := by
    intro m' i h; rw [hV]; dsimp only; rw [ite_eq_left h]
  have hVs : ∀ m' i, ¬(i ≤ m' ∨ (n + 1 ≤ i ∧ i ≤ n + 3)) → V m' i = P.ups s := by
    intro m' i h; rw [hV]; dsimp only; rw [ite_eq_right h]
  -- (1) the ring on the last coordinate (r = s)
  set κR := onestepConst d * X with hκR
  have hκR0 : 0 ≤ κR := mul_nonneg hCreg hX0
  have hR : ∀ y : Fin (n + 2 + 2) → Fin (m * W),
      slotOp L R1 (fun y' => Real.sqrt (linkProd (fun _ => P.ups s) (y' L) (y' L) y')) y ≤
      κR * Real.sqrt (linkProd V1 (y L) (y L) y) := by
    intro y
    refine slotOp_sqrt_linkProd_last_le (n := n + 2)
      (fun i h0 h1 => by rw [hV1]; dsimp only; rw [ite_eq_right (by omega)])
      (fun i u w => hUp s hs0 hs1 u w) y ?_
    have e1 : V1 (n + 2 + 1) = P.ups t := by
      rw [hV1]; dsimp only; rw [ite_eq_left (Or.inr rfl)]
    have e0 : V1 0 = P.ups t := by rw [hV1]; dsimp only; rw [ite_eq_left (Or.inl rfl)]
    rw [e1, e0, hu, hu]
    have h := (thetaringAction d hm hW hz hs0 hst ht1 (Or.inl rfl) (y ⟨n + 2, by omega⟩)
      (y L) (y 0)).1
    rw [onestepScale_self d hm hW hz hst ht1] at h
    refine le_of_eq_of_le ?_ (h.trans (le_of_eq ?_))
    · rfl
    · rw [hκR, hX]; ring
  -- (2) the propagator on coordinate n+2, case (s,t)
  have hO : ∀ y : Fin (n + 2 + 2) → Fin (m * W),
      slotOp ⟨n + 2, by omega⟩ (fun x c => Fn ⟨n + 2, by omega⟩ (x ⟨n + 2, by omega⟩) c)
        (fun y' => Real.sqrt (linkProd V1 (y' L) (y' L) y')) y ≤
      kernelActionConst d * ρ * Real.sqrt (linkProd V2 (y L) (y L) y) := by
    intro y
    refine slotOp_sqrt_linkProd_le_end (n := n + 2) (V := V1) (V' := V2) ⟨n + 2, by omega⟩
      (by simp) (fun i h1 h2 => by
        rw [hV1, hV2]; dsimp only at h1 h2 ⊢
        by_cases h : i = 0
        · rw [ite_eq_left (Or.inl h), ite_eq_left (Or.inl h)]
        · rw [ite_eq_right (by omega), ite_eq_right (by omega)]) hpos1 y ?_
    dsimp only
    have e1 : V1 (n + 2) = P.ups s := by rw [hV1]; dsimp only; rw [ite_eq_right (by omega)]
    have e2 : V1 (n + 2 + 1) = P.ups t := by rw [hV1]; dsimp only; rw [ite_eq_left (by omega)]
    have e3 : V2 (n + 2) = P.ups t := by rw [hV2]; dsimp only; rw [ite_eq_left (by omega)]
    have e4 : V2 (n + 2 + 1) = P.ups t := by rw [hV2]; dsimp only; rw [ite_eq_left (by omega)]
    rw [e1, e2, e3, e4, hu, hu, ← hρ']
    simp only [hFn, goodPropNorm]
    exact goodProp_stepB_swap d hm hW hz hs0 hst ht1 _ _ _ _
  -- (3) the ring on coordinate n+1 (r = t)
  set κR' := onestepConst d * X * ρ with hκR'
  have hκR'0 : 0 ≤ κR' := mul_nonneg hκR0 hρ0
  have hR3 : ∀ y : Fin (n + 2 + 2) → Fin (m * W),
      slotOp ⟨n + 1, by omega⟩ R3 (fun y' => Real.sqrt (linkProd V2 (y' L) (y' L) y')) y ≤
      κR' * Real.sqrt (linkProd (V 0) (y L) (y L) y) := by
    intro y
    refine slotOp_sqrt_linkProd_le_end (n := n + 2) (V := V2) (V' := V 0) ⟨n + 1, by omega⟩
      (by simp) (fun i h1 h2 => by
        rw [hV2]; dsimp only at h1 h2 ⊢
        by_cases h : i = 0 ∨ i = n + 2 ∨ i = n + 3
        · rw [ite_eq_left h, hVt 0 i (by omega)]
        · rw [ite_eq_right h, hVs 0 i (by omega)]) hpos2 y ?_
    dsimp only
    have e1 : V2 (n + 1) = P.ups s := by rw [hV2]; dsimp only; rw [ite_eq_right (by omega)]
    have e2 : V2 (n + 1 + 1) = P.ups t := by rw [hV2]; dsimp only; rw [ite_eq_left (by omega)]
    have p1 : Psi.isoPoint (y L) (y L) y (n + 1) = y ⟨n, by omega⟩ :=
      isoPoint_succ (y L) (y L) y ⟨n, by omega⟩ (by simp)
    have p3 : Psi.isoPoint (y L) (y L) y (n + 1 + 2) = y ⟨n + 2, by omega⟩ :=
      isoPoint_succ (y L) (y L) y ⟨n + 2, by omega⟩ (by simp)
    rw [e1, e2, hVt 0 (n + 1) (by omega), hVt 0 (n + 1 + 1) (by omega), hu, hu,
      p1, p3]
    have h := (thetaringAction d hm hW hz hs0 hst ht1 (Or.inr rfl) (y ⟨n, by omega⟩)
      (y ⟨n + 1, by omega⟩) (y ⟨n + 2, by omega⟩)).1
    unfold onestepScale at h
    rw [← hls, ← hlt, hρ'] at h
    refine le_of_eq_of_le ?_ (h.trans (le_of_eq ?_))
    · rfl
    · rw [hκR', hX]; ring
  -- (4) the remaining propagators
  set κ : ℕ → ℝ := fun i => if i < n then kernelActionConst d * ρ
    else kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) with hκ
  have hκ0 : ∀ i, 0 ≤ κ i := by
    intro i
    rw [hκ]
    dsimp only
    split_ifs
    · exact mul_nonneg (by linarith) hρ0
    · exact mul_nonneg (by linarith) (div_nonneg hηs.le hηt.le)
  have hVV : ∀ m' i, i ≠ m' → i ≠ m' + 1 → V m' i = V (m' + 1) i := by
    intro m' i h1 h2
    by_cases h : i ≤ m' ∨ (n + 1 ≤ i ∧ i ≤ n + 3)
    · rw [hVt m' i h, hVt (m' + 1) i (by omega)]
    · rw [hVs m' i h, hVs (m' + 1) i (by omega)]
  have hstep : ∀ (m' : ℕ) (hm' : m' + 1 < n + 2 + 2) (y : Fin (n + 2 + 2) → Fin (m * W)),
      ∑ e, Fn ⟨m', by omega⟩ (y ⟨m', by omega⟩) e *
          Real.sqrt (V m' m' (Psi.isoPoint (y L) (y L) y m') e *
            V m' (m' + 1) e (Psi.isoPoint (y L) (y L) y (m' + 2))) ≤
        κ m' * Real.sqrt (V (m' + 1) m' (Psi.isoPoint (y L) (y L) y m') (y ⟨m', by omega⟩) *
          V (m' + 1) (m' + 1) (y ⟨m', by omega⟩) (Psi.isoPoint (y L) (y L) y (m' + 2))) := by
    intro m' hm' y
    rw [hVt m' m' (Or.inl le_rfl), hVt (m' + 1) m' (Or.inl (by omega)),
      hVt (m' + 1) (m' + 1) (Or.inl le_rfl)]
    by_cases hlt' : m' < n
    · rw [hVs m' (m' + 1) (by omega), hu, hu, hκ]
      dsimp only
      rw [ite_eq_left hlt', hρ, hl s, hl t]
      exact goodProp_stepB d hm hW hz hs0 hst ht1 _ _ _ _
    · rw [hVt m' (m' + 1) (by omega), hu, hκ]
      dsimp only
      rw [ite_eq_right hlt']
      exact goodProp_stepC_sat d hm hW hz hs0 hst ht1 _ _ _
  have hinv : ∀ (y : Fin (n + 2 + 2) → Fin (m * W)) (j : Fin (n + 2 + 2)) (e : Fin (m * W)),
      j.val + 1 < n + 2 + 2 → Function.update y j e L = y L := by
    intro y j e hj
    refine Function.update_of_ne ?_ _ _
    intro h
    rw [hL] at h
    subst h
    simp at hj
  have hit := tensorRSet_iter_le Fn hF0 V hVn (fun y => y L) (fun y => y L) hinv hinv
    κ hκ0 hVV hstep (n + 2) (by omega)
  have hlinkT : ∀ y : Fin (n + 2 + 2) → Fin (m * W),
      linkProd (V (n + 2)) (y L) (y L) y = linkProd (fun _ => P.ups t) (y L) (y L) y :=
    fun y => linkProd_congr (k := n + 2 + 2) (fun i hi => hVt (n + 2) i (by omega))
      _ _ y
  have hprod : ∏ i ∈ Finset.range (n + 2), κ i = (kernelActionConst d * ρ) ^ n *
      (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t)) ^ 2 := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, hκ]
    dsimp only
    rw [ite_eq_right (lt_irrefl n), ite_eq_right (by omega), Finset.prod_congr rfl (fun i hi =>
      ite_eq_left (Finset.mem_range.mp hi)), Finset.prod_const, Finset.card_range]
    ring
  have hK0 : ∀ (y : Fin (n + 2 + 2) → Fin (m * W)) (c : Fin (m * W)),
      0 ≤ Fn L (y L) c := fun y c => hF0 _ _ _
  have hlast := slotOp_sqrt_linkProd_last_le (n := n + 2) (K := fun y c => Fn L (y L) c)
    (V := fun _ => P.ups t) (V' := fun _ => P.ups t) (fun _ _ _ => rfl)
    (fun i u w => hUp t ht0 ht1 u w) x
    (κ := kernelActionConst d * (vsHeight P.z s / vsHeight P.z t)) (by
      simp only [hFn, goodPropNorm, hu]
      exact goodProp_stepC_sat d hm hW hz hs0 hst ht1 _ _ _)
  have hPi0 : 0 ≤ ∏ i ∈ Finset.range (n + 2), κ i := Finset.prod_nonneg fun i _ => hκ0 i
  -- assembly
  set e : ℝ := -((n + 2 + 2 : ℕ) : ℝ) / 2 with he
  have hAe : 0 ≤ P.lEta s ^ e := Real.rpow_nonneg hLs.le _
  have hR3K : ∀ y c, 0 ≤ R3 y c := fun y c => norm_nonneg _
  have hstep12 : ∀ y : Fin (n + 2 + 2) → Fin (m * W),
      slotOp ⟨n + 1, by omega⟩ R3 (slotOp L R1 (fun y' => P.sAv y' s)) y ≤
        P.lEta s ^ e * κR * slotOp ⟨n + 1, by omega⟩ R3
          (fun y' => Real.sqrt (linkProd V1 (y' L) (y' L) y')) y := by
    intro y
    have hfun : (fun y' : Fin (n + 2 + 2) → Fin (m * W) => P.sAv y' s) = fun y' =>
        P.lEta s ^ e * Real.sqrt (linkProd (fun _ => P.ups s) (y' L) (y' L) y') :=
      funext fun y' => sAv_eq_linkProd P (n := n + 2) y' s
    rw [hfun, mul_assoc, ← slotOp_const_mul, ← slotOp_const_mul]
    refine slotOp_mono _ hR3K (fun y' => ?_) y
    rw [slotOp_const_mul]
    exact mul_le_mul_of_nonneg_left (hR y') hAe
  have huniv : (Finset.univ : Finset (Fin (n + 2 + 2))) =
      insert ⟨n + 2, by omega⟩ (insert L (slotsBelow (n + 2 + 2) (n + 2))) := by
    ext j
    simp only [slotsBelow, Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and,
      Fin.ext_iff, hL, Fin.val_last, true_iff]
    omega
  have hnot1 : (⟨n + 2, by omega⟩ : Fin (n + 2 + 2)) ∉
      insert L (slotsBelow (n + 2 + 2) (n + 2)) := by
    simp [slotsBelow, hL, Fin.ext_iff]
  have hnot2 : L ∉ slotsBelow (n + 2 + 2) (n + 2) := by simp [slotsBelow, hL]
  have hcomm : ∀ g : (Fin (n + 2 + 2) → Fin (m * W)) → ℝ,
      slotOp ⟨n + 2, by omega⟩ (fun x c => Fn ⟨n + 2, by omega⟩ (x ⟨n + 2, by omega⟩) c)
        (slotOp ⟨n + 1, by omega⟩ R3 g) =
      slotOp ⟨n + 1, by omega⟩ R3
        (slotOp ⟨n + 2, by omega⟩ (fun x c => Fn ⟨n + 2, by omega⟩ (x ⟨n + 2, by omega⟩) c) g) :=
    fun g => slotOp_comm (j := (⟨n + 2, by omega⟩ : Fin (n + 2 + 2))) (j' := ⟨n + 1, by omega⟩)
      (K := fun x c => Fn ⟨n + 2, by omega⟩ (x ⟨n + 2, by omega⟩) c) (K' := R3)
      (by simp [Fin.ext_iff])
      (fun x c c' => by rw [Function.update_of_ne (by simp [Fin.ext_iff])])
      (fun x c c' => by
        rw [hR3d]
        unfold ringKer
        rw [Function.update_of_ne (by simp [Fin.ext_iff]),
          Function.update_of_ne (by simp [Fin.ext_iff])]) g
  have hmain : ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
      slotOp ⟨n + 1, by omega⟩ R3 (slotOp L R1 (fun y' => P.sAv y' s)) y ≤
      P.lEta s ^ e * κR * (kernelActionConst d * ρ) * κR' *
        ((∏ i ∈ Finset.range (n + 2), κ i) *
          (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
            Real.sqrt (linkProd (fun _ => P.ups t) (x L) (x L) x))) := by
    calc _ ≤ ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
          (P.lEta s ^ e * κR * slotOp ⟨n + 1, by omega⟩ R3
            (fun y' => Real.sqrt (linkProd V1 (y' L) (y' L) y')) y) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hstep12 y) (norm_nonneg _)
      _ = P.lEta s ^ e * κR * (tensorR Fn *ᵥ slotOp ⟨n + 1, by omega⟩ R3
            (fun y' => Real.sqrt (linkProd V1 (y' L) (y' L) y'))) x := by
          simp only [norm_goodProp, Matrix.mulVec, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ _ := by
          rw [mul_assoc (P.lEta s ^ e * κR * (kernelActionConst d * ρ)), mul_assoc
            (P.lEta s ^ e * κR)]
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hAe hκR0)
          rw [← tensorRSet_univ, huniv, (tensorRSet_insert Fn hnot1).2, ← Matrix.mulVec_mulVec,
            mulVec_tensorRSet_single, hcomm, (tensorRSet_insert Fn hnot2).1,
            ← Matrix.mulVec_mulVec, mulVec_tensorRSet_single]
          have hG0 : ∀ x y, 0 ≤ tensorRSet Fn (slotsBelow (n + 2 + 2) (n + 2)) x y :=
            tensorRSet_nonneg hF0 _
          -- inner bound: ring 3 after the propagator on n+2
          have hin : ∀ y, slotOp ⟨n + 1, by omega⟩ R3 (slotOp ⟨n + 2, by omega⟩
              (fun x c => Fn ⟨n + 2, by omega⟩ (x ⟨n + 2, by omega⟩) c)
              (fun y' => Real.sqrt (linkProd V1 (y' L) (y' L) y'))) y ≤
              kernelActionConst d * ρ * (κR' * Real.sqrt (linkProd (V 0) (y L) (y L) y)) := by
            intro y
            calc _ ≤ slotOp ⟨n + 1, by omega⟩ R3 (fun y' => kernelActionConst d * ρ *
                  Real.sqrt (linkProd V2 (y' L) (y' L) y')) y :=
                  slotOp_mono _ hR3K (fun y' => hO y') y
              _ = _ := by rw [slotOp_const_mul]
              _ ≤ _ := mul_le_mul_of_nonneg_left (hR3 y)
                  (mul_nonneg (by linarith) hρ0)
          calc slotOp L (fun x c => Fn L (x L) c) (tensorRSet Fn (slotsBelow (n + 2 + 2) (n + 2))
                *ᵥ slotOp ⟨n + 1, by omega⟩ R3 (slotOp ⟨n + 2, by omega⟩
                  (fun x c => Fn ⟨n + 2, by omega⟩ (x ⟨n + 2, by omega⟩) c)
                  (fun y' => Real.sqrt (linkProd V1 (y' L) (y' L) y')))) x
              ≤ slotOp L (fun x c => Fn L (x L) c) (tensorRSet Fn (slotsBelow (n + 2 + 2) (n + 2))
                *ᵥ fun y => kernelActionConst d * ρ * κR' *
                  Real.sqrt (linkProd (V 0) (y L) (y L) y)) x := by
                refine slotOp_mono _ hK0 (fun y => mulVec_mono_of_nonneg hG0 (fun y' => ?_) y) x
                exact (hin y').trans_eq (by ring)
            _ = kernelActionConst d * ρ * κR' * slotOp L (fun x c => Fn L (x L) c)
                (tensorRSet Fn (slotsBelow (n + 2 + 2) (n + 2)) *ᵥ
                  fun y => Real.sqrt (linkProd (V 0) (y L) (y L) y)) x := by
                rw [← slotOp_const_mul]
                congr 1
                funext y
                rw [show (fun y => kernelActionConst d * ρ * κR' *
                    Real.sqrt (linkProd (V 0) (y L) (y L) y)) =
                  (kernelActionConst d * ρ * κR') • (fun y : Fin (n + 2 + 2) → Fin (m * W) =>
                    Real.sqrt (linkProd (V 0) (y L) (y L) y)) from rfl, Matrix.mulVec_smul]
                rfl
            _ ≤ kernelActionConst d * ρ * κR' * slotOp L (fun x c => Fn L (x L) c)
                (fun y => (∏ i ∈ Finset.range (n + 2), κ i) *
                  Real.sqrt (linkProd (fun _ => P.ups t) (y L) (y L) y)) x := by
                refine mul_le_mul_of_nonneg_left (slotOp_mono _ hK0
                  (fun y => (hit y).trans_eq (by rw [hlinkT y])) x)
                  (mul_nonneg (mul_nonneg (by linarith) hρ0) hκR'0)
            _ = kernelActionConst d * ρ * κR' * ((∏ i ∈ Finset.range (n + 2), κ i) *
                slotOp L (fun x c => Fn L (x L) c)
                  (fun y => Real.sqrt (linkProd (fun _ => P.ups t) (y L) (y L) y)) x) := by
                rw [slotOp_const_mul]
            _ ≤ kernelActionConst d * ρ * κR' * ((∏ i ∈ Finset.range (n + 2), κ i) *
                (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
                  Real.sqrt (linkProd (fun _ => P.ups t) (x L) (x L) x))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hPi0)
                  (mul_nonneg (mul_nonneg (by linarith) hρ0) hκR'0)
            _ = _ := by ring
  refine hmain.trans ?_
  -- arithmetic
  have hpow := goodProp_rpow_av hLs hLt (n + 2)
  rw [← hρ] at hpow
  have hsav := sAv_eq_linkProd P (n := n + 2) x t
  have hWr : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hsqt : lt ^ 2 * vsHeight P.z t ≤ (W : ℝ) ^ 2 := (loc_sq_mul hN hηt).1
  have hsqs : ls ^ 2 * vsHeight P.z s ≤ (W : ℝ) ^ 2 := (loc_sq_mul hN hηs).1
  set Y := X ^ 2 * (vsHeight P.z s / vsHeight P.z t) ^ 3 with hY
  have hYv : Y = ls ^ 2 * vsHeight P.z s * (lt ^ 2 * vsHeight P.z t) /
      ((W : ℝ) ^ 4 * vsHeight P.z t ^ 2) := by
    rw [hY, hX]
    have h3 := hηs.ne'
    have h4 := hηt.ne'
    field_simp
  have hYle : Y ≤ 1 / vsHeight P.z t ^ 2 := by
    rw [hYv, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ls ^ 2 * vsHeight P.z s * (lt ^ 2 * vsHeight P.z t) ≤ (W : ℝ) ^ 2 * (W : ℝ) ^ 2 :=
      mul_le_mul hsqs hsqt (by positivity) (by positivity)
    nlinarith
  have hsAv0 : 0 ≤ P.sAv x t := by
    rw [hsav]; exact mul_nonneg (Real.rpow_nonneg hLt.le _) (Real.sqrt_nonneg _)
  have hrat : 0 ≤ P.lEta t / P.lEta s := div_nonneg hLt.le hLs.le
  calc P.lEta s ^ e * κR * (kernelActionConst d * ρ) * κR' *
        ((∏ i ∈ Finset.range (n + 2), κ i) *
          (kernelActionConst d * (vsHeight P.z s / vsHeight P.z t) *
            Real.sqrt (linkProd (fun _ => P.ups t) (x L) (x L) x)))
      = onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) * Y * (P.lEta t / P.lEta s) *
          P.sAv x t := by
        rw [hprod, hκR, hκR', hsav, hY, ← he]
        calc _ = onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) *
              (X ^ 2 * (vsHeight P.z s / vsHeight P.z t) ^ 3) * (P.lEta s ^ e * ρ ^ (n + 2)) *
              Real.sqrt (linkProd (fun _ => P.ups t) (x L) (x L) x) := by ring
          _ = _ := by rw [hpow]; ring
    _ ≤ onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) * (1 / vsHeight P.z t ^ 2) *
          (P.lEta t / P.lEta s) * P.sAv x t := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hYle (by positivity)) hrat) hsAv0
    _ = _ := by ring

/-- `regProps_oneRing` for functions: if `|f(y)| ≤ φ s^av_{k,s}(y)` then
`|P̂^{⊗k} Θ̊^{(k)}_t [f](x)| ≤ C_reg C_P^k φ η_t⁻¹ s^av_{k,t}(x)` (`k = n+2`). -/
theorem regProps_oneRing_apply {n : ℕ} {φ : ℝ} (hφ : 0 ≤ φ)
    (f : (Fin (n + 2) → Fin (m * W)) → ℂ) (hf : ∀ y, ‖f y‖ ≤ φ * P.sAv y s)
    (x : Fin (n + 2) → Fin (m * W)) :
    ‖propOp (goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t)
        (ringOp (shortRingProfile d.b m W) P.z t (Fin.last (n + 1)) ⟨n, by omega⟩ f) x‖ ≤
      onestepConst d * kernelActionConst d ^ (n + 2) / vsHeight P.z t * φ * P.sAv x t := by
  have hR0 : ∀ y c, 0 ≤ ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 1))
      ⟨n, by omega⟩ y c := fun y c => norm_nonneg _
  rw [propOp_apply]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
        (φ * slotOp (Fin.last (n + 1))
          (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 1)) ⟨n, by omega⟩)
          (fun y' => P.sAv y' s) y) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ((norm_ringOp_le _ _ _ _ _ f y).trans ?_) (norm_nonneg _)
        rw [← slotOp_const_mul]
        exact slotOp_mono _ hR0 hf y
    _ = φ * ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
        slotOp (Fin.last (n + 1))
          (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 1)) ⟨n, by omega⟩)
          (fun y' => P.sAv y' s) y := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ φ * (onestepConst d * kernelActionConst d ^ (n + 2) / vsHeight P.z t * P.sAv x t) :=
        mul_le_mul_of_nonneg_left (regProps_oneRing d hm hW P hPW hPD hz hs0 hst ht1 x) hφ
    _ = _ := by ring

/-- `regProps_twoRings` for functions: if `|f(y)| ≤ φ s^av_{k,s}(y)` then
`|P̂^{⊗k} Θ̊^{(k-2)}_t Θ̊^{(k)}_t [f](x)| ≤ C_reg² C_P^k φ η_t⁻² (L_t/L_s) s^av_{k,t}(x)`
(`k = n+4`). -/
theorem regProps_twoRings_apply {n : ℕ} {φ : ℝ} (hφ : 0 ≤ φ)
    (f : (Fin (n + 2 + 2) → Fin (m * W)) → ℂ) (hf : ∀ y, ‖f y‖ ≤ φ * P.sAv y s)
    (x : Fin (n + 2 + 2) → Fin (m * W)) :
    ‖propOp (goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t)
        (ringOp (shortRingProfile d.b m W) P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
          (ringOp (shortRingProfile d.b m W) P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ f))
        x‖ ≤
      onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z t ^ 2 *
        (P.lEta t / P.lEta s) * φ * P.sAv x t := by
  have hR1 : ∀ y c, 0 ≤ ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 2 + 1))
      ⟨n + 2, by omega⟩ y c := fun y c => norm_nonneg _
  have hR3 : ∀ y c, 0 ≤ ringKer (shortRingProfile d.b m W) P.z t
      (⟨n + 1, by omega⟩ : Fin (n + 2 + 2)) ⟨n, by omega⟩ y c := fun y c => norm_nonneg _
  rw [propOp_apply]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
        (φ * slotOp ⟨n + 1, by omega⟩
          (ringKer (shortRingProfile d.b m W) P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩)
          (slotOp (Fin.last (n + 2 + 1))
            (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩)
            (fun y' => P.sAv y' s)) y) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ((norm_ringOp_le _ _ _ _ _ _ y).trans ?_)
          (norm_nonneg _)
        rw [← slotOp_const_mul]
        refine slotOp_mono _ hR3 (fun y' => (norm_ringOp_le _ _ _ _ _ f y').trans ?_) y
        rw [← slotOp_const_mul]
        exact slotOp_mono _ hR1 hf y'
    _ = φ * ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t x y‖ *
        slotOp ⟨n + 1, by omega⟩
          (ringKer (shortRingProfile d.b m W) P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩)
          (slotOp (Fin.last (n + 2 + 1))
            (ringKer (shortRingProfile d.b m W) P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩)
            (fun y' => P.sAv y' s)) y := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ φ * (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z t ^ 2 *
          (P.lEta t / P.lEta s) * P.sAv x t) :=
        mul_le_mul_of_nonneg_left (regProps_twoRings d hm hW P hPW hPD hz hs0 hst ht1 x) hφ
    _ = _ := by ring

end Rings

end BlockBand.Native.ErdosRiabov.Propagator
