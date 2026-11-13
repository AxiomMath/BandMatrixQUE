module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWGen

/-!
# The Taylor remainder of one step of a test

A step of the state `z` is `zstep z dY dK` (`Y ↦ Y + dY`, `Y^𝒦 ↦ Y^𝒦 + dK`, `x^𝒦 ↦ x^𝒦 + dK`,
initial values fixed); its basic increments are `bvec dY dK`. A state is **admissible** with
constant `D` (`Adm D`) if every Gram coordinate of `Y` and of `Y_0` is at most `|Re Tr| + D` and
`x^𝒦 = Y^𝒦 − Y^𝒦_0`: this holds for the finite-`W` states (`|G_e| ≤ Re Tr M`, bounded jumps).

* `cut_data`: a compactly supported `C³` cutoff has derivatives at every point and bounded
  derivatives up to order three.
* `isJet_jF`: on a box of states and for `‖β‖₁ ≤ 1`, `jF` describes the step (product and chain
  rules of the atomic jets).
* **`exists_taylor_bound`**: one constant `C` with `|κ.fn z| ≤ C`, all jet coefficients `≤ C`
  for admissible `z`, and `|F(z') − F(z) − lin − quad| ≤ C ‖β‖₁³` for admissible `z, z'`,
  `z' = zstep z dY dK` with a real-diagonal `dY` (any size of the step).
* `continuous_jF_l`, `continuous_jF_q`: the jet coefficients are continuous in the state.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate

variable {K np : ℕ}

/-!
## Cutoffs
-/

theorem cut_data {f : ℝ → ℝ} (h3 : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∀ x, HasDerivAt f (deriv f x) x) ∧ (∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x) ∧
      (∀ x, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x) ∧
      ∃ M, ∀ x, |f x| ≤ M ∧ |deriv f x| ≤ M ∧ |deriv (deriv f) x| ≤ M ∧
        |deriv (deriv (deriv f)) x| ≤ M := by
  have h2 : ContDiff ℝ 2 (deriv f) := (h3.of_le (by norm_num) : ContDiff ℝ (2 + 1) f).deriv'
  have h1 : ContDiff ℝ 1 (deriv (deriv f)) := (h2 : ContDiff ℝ (1 + 1) _).deriv'
  have h0 : ContDiff ℝ 0 (deriv (deriv (deriv f))) := (h1 : ContDiff ℝ (0 + 1) _).deriv'
  refine ⟨fun x => ((h3.differentiable (by norm_num)) x).hasDerivAt,
    fun x => ((h2.differentiable (by norm_num)) x).hasDerivAt,
    fun x => ((h1.differentiable (by norm_num)) x).hasDerivAt, ?_⟩
  obtain ⟨C0, hC0⟩ := h3.continuous.bounded_above_of_compact_support hc
  obtain ⟨C1, hC1⟩ := h2.continuous.bounded_above_of_compact_support hc.deriv
  obtain ⟨C2, hC2⟩ := h1.continuous.bounded_above_of_compact_support hc.deriv.deriv
  obtain ⟨C3, hC3⟩ := h0.continuous.bounded_above_of_compact_support hc.deriv.deriv.deriv
  have p0 := (norm_nonneg _).trans (hC0 0)
  have p1 := (norm_nonneg _).trans (hC1 0)
  have p2 := (norm_nonneg _).trans (hC2 0)
  have p3 := (norm_nonneg _).trans (hC3 0)
  refine ⟨C0 + C1 + C2 + C3, fun x => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := hC0 x; rw [Real.norm_eq_abs] at this; linarith
  · have := hC1 x; rw [Real.norm_eq_abs] at this; linarith
  · have := hC2 x; rw [Real.norm_eq_abs] at this; linarith
  · have := hC3 x; rw [Real.norm_eq_abs] at this; linarith

/-!
## Steps and boxes
-/

/-- A step of the state. -/
def zstep (z : ZK K np) (dY : GSt K np) (dK : KSt np) : ZK K np :=
  ((z.1.1 + dY, z.1.2.1, z.1.2.2), z.2.1 + dK, fun a => z.2.2.1 a + dK a.1 a.2, z.2.2.2)

/-- The basic increments of a step. -/
def bvec (dY : GSt K np) (dK : KSt np) : BI K np → ℂ
  | Sum.inl e => gramEntry e dY
  | Sum.inr (Sum.inl a) => dK a.1 a.2
  | Sum.inr (Sum.inr a) => conj (dK a.1 a.2)

/-- The diagonal of the `M`-part of a Gram increment is real. -/
def DiagReal (dY : GSt K np) : Prop := ∀ k, (dY.1 k k).im = 0

/-- A box of states. -/
def InBox (B : ℝ) (z : ZK K np) : Prop :=
  (∀ a : KIdx np, ‖z.2.1 a.1 a.2‖ ≤ B) ∧ (∀ a : KIdx np, ‖z.2.2.1 a‖ ≤ B) ∧
    ∀ e : GIdx K np, ‖kHatE e z‖ ≤ B

/-- Admissible states. -/
def Adm (D : ℝ) (z : ZK K np) : Prop :=
  (∀ e : GIdx K np, ‖gramEntry e z.1.1‖ ≤ |trRe z.1.1| + D) ∧
    (∀ e : GIdx K np, ‖gramEntry e z.1.2.2‖ ≤ |trRe z.1.2.2| + D) ∧
    ∀ a : KIdx np, z.2.2.1 a = z.2.1 a.1 a.2 - z.2.2.2 a.1 a.2

theorem gramEntry_add' (e : GIdx K np) (H J : GSt K np) :
    gramEntry e (H + J) = gramEntry e H + gramEntry e J := by
  simp only [gramEntry, Prod.fst_add, Prod.snd_add, Matrix.add_apply]; split_ifs <;> rfl

theorem norm_ev_le (i i' : BI K np) : ‖ev i i'‖ ≤ 1 := by
  unfold ev; split_ifs <;> simp

theorem norm_bvec_le (dY : GSt K np) (dK : KSt np) (i : BI K np) :
    ‖bvec dY dK i‖ ≤ nrm (bvec dY dK) := norm_le_nrm _ i

theorem lin_lS (β : BI K np → ℂ) :
    lin lS β = ∑ k : SrcCol K (Fin np), β (Sum.inl ((0 : Fin 2), k, k)) := by
  simp only [lin, lS, sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun k _ => by simp [ev]

theorem lin_lQ (y : KSt np) (β : BI K np → ℂ) :
    lin (lQ y) β = ∑ a : KIdx np, (conj (y a.1 a.2) * β (Sum.inr (Sum.inl a)) +
      y a.1 a.2 * β (Sum.inr (Sum.inr a))) := by
  simp only [lin, lQ, sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  simp [ev, add_mul, sum_add_distrib]

theorem quad_qQ0 (β : BI K np → ℂ) :
    quad qQ0 β = ∑ a : KIdx np, β (Sum.inr (Sum.inl a)) * β (Sum.inr (Sum.inr a)) := by
  have h : ∀ a : KIdx np, ∑ i : BI K np, ∑ i' : BI K np, ev (Sum.inr (Sum.inl a)) i *
      ev (Sum.inr (Sum.inr a)) i' * (β i * β i') =
        β (Sum.inr (Sum.inl a)) * β (Sum.inr (Sum.inr a)) := fun a => by
    simp [ev, ite_mul]
  calc quad qQ0 β = ∑ i : BI K np, ∑ i' : BI K np, ∑ a : KIdx np, ev (Sum.inr (Sum.inl a)) i *
        ev (Sum.inr (Sum.inr a)) i' * (β i * β i') := by simp only [quad, qQ0, sum_mul]
    _ = ∑ i : BI K np, ∑ a : KIdx np, ∑ i' : BI K np, ev (Sum.inr (Sum.inl a)) i *
        ev (Sum.inr (Sum.inr a)) i' * (β i * β i') := sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a : KIdx np, ∑ i : BI K np, ∑ i' : BI K np, ev (Sum.inr (Sum.inl a)) i *
        ev (Sum.inr (Sum.inr a)) i' * (β i * β i') := Finset.sum_comm
    _ = _ := sum_congr rfl fun a _ => h a

theorem ofReal_norm_sq_eq (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-!
## The atomic jets describe a step
-/

theorem jS_exact (z : ZK K np) {dY : GSt K np} (hd : DiagReal dY) (dK : KSt np) :
    ((trRe (zstep z dY dK).1.1 - trRe z.1.1 : ℝ) : ℂ) =
      lin (jS z).l (bvec dY dK) + quad (jS z).q (bvec dY dK) := by
  have htr : trRe (zstep z dY dK).1.1 - trRe z.1.1 = (dY.1.trace).re := by
    simp [zstep, trRe, Matrix.trace_add]
  have hq : quad (fun _ _ => (0 : ℂ)) (bvec (K := K) dY dK) = 0 := by simp [quad]
  have e1 : ∑ k : SrcCol K (Fin np), bvec (K := K) dY dK (Sum.inl ((0 : Fin 2), k, k)) =
      dY.1.trace := by simp [bvec, gramEntry, Matrix.trace]
  simp only [jS]
  rw [htr, lin_lS, hq, add_zero, e1]
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, Matrix.trace, Matrix.diag, Complex.im_sum]
    exact (sum_eq_zero fun k _ => hd k).symm

theorem jQ_exact (z : ZK K np) (dY : GSt K np) (dK : KSt np) :
    ((qK (zstep z dY dK).2.1 - qK z.2.1 : ℝ) : ℂ) =
      lin (jQ z).l (bvec dY dK) + quad (jQ z).q (bvec dY dK) := by
  simp only [jQ, zstep]
  rw [lin_lQ, quad_qQ0, ← sum_add_distrib]
  simp only [qK, Complex.ofReal_sub, Complex.ofReal_sum, ← sum_sub_distrib, Matrix.add_apply,
    ofReal_norm_sq_eq, bvec, map_add]
  exact sum_congr rfl fun a _ => by ring

/-!
## The jet of a test on a box
-/

section Box

variable {χ ξ : ℝ → ℝ} {Mχ Mξ : ℝ}
  (hχ1 : ∀ x, HasDerivAt χ (deriv χ x) x) (hχ2 : ∀ x, HasDerivAt (deriv χ) (deriv (deriv χ) x) x)
  (hχ3 : ∀ x, HasDerivAt (deriv (deriv χ)) (deriv (deriv (deriv χ)) x) x)
  (hMχ : ∀ x, |χ x| ≤ Mχ ∧ |deriv χ x| ≤ Mχ ∧ |deriv (deriv χ) x| ≤ Mχ ∧
    |deriv (deriv (deriv χ)) x| ≤ Mχ)
  (hξ1 : ∀ x, HasDerivAt ξ (deriv ξ x) x) (hξ2 : ∀ x, HasDerivAt (deriv ξ) (deriv (deriv ξ) x) x)
  (hξ3 : ∀ x, HasDerivAt (deriv (deriv ξ)) (deriv (deriv (deriv ξ)) x) x)
  (hMξ : ∀ x, |ξ x| ≤ Mξ ∧ |deriv ξ x| ≤ Mξ ∧ |deriv (deriv ξ) x| ≤ Mξ ∧
    |deriv (deriv (deriv ξ)) x| ≤ Mξ)
include hχ1 hχ2 hχ3 hMχ hξ1 hξ2 hξ3 hMξ

omit hχ1 hχ2 hχ3 hMχ hξ1 hξ2 hξ3 hMξ in
/-- The constant of `isJet_jF`. -/
def cJ (K np : ℕ) (Mχ Mξ B : ℝ) : ℝ :=
  10 * (Mχ * Mξ) * (10 * (10 * (4 * Mχ * (1 + (Fintype.card (SrcCol K (Fin np)) : ℝ)) ^ 3) *
    (4 * Mξ * (1 + (2 * (Fintype.card (KIdx np) : ℝ) * B + Fintype.card (KIdx np))) ^ 3)) *
    (10 * B * B))

theorem isJet_jF (κ : KTest K np) {B : ℝ} (hB : 1 ≤ B) {z : ZK K np} (hz : InBox B z)
    {dY : GSt K np} (hd : DiagReal dY) (dK : KSt np) (hN : nrm (bvec dY dK) ≤ 1) :
    IsJet (cJ K np Mχ Mξ B) (jF χ ξ κ z) (κ.fn χ ξ (zstep z dY dK)) (bvec dY dK) := by
  set β := bvec dY dK
  set nS : ℝ := (Fintype.card (SrcCol K (Fin np)) : ℝ)
  set nK : ℝ := (Fintype.card (KIdx np) : ℝ)
  have hnS : 0 ≤ nS := Nat.cast_nonneg _
  have hnK : 0 ≤ nK := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by linarith
  have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0).1
  have hMξ0 : 0 ≤ Mξ := (abs_nonneg _).trans (hMξ 0).1
  obtain ⟨hzK, hzx, hzY⟩ := hz
  -- the `χ(s)` jet
  have hlS : ∀ i, ‖(jS z).l i‖ ≤ nS := fun i => by
    simp only [jS, lS]
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul (univ : Finset (SrcCol K (Fin np)))
      (fun k => ‖ev (Sum.inl ((0 : Fin 2), k, k)) i‖) 1 (fun k _ => norm_ev_le _ _)
    simpa [nS] using this
  have hqS : ∀ i i', ‖(jS z).q i i'‖ ≤ nS := fun i i' => by simp [jS, hnS]
  have jχ := isJet_chain hχ1 hχ2 hχ3 hMχ hnS hlS hqS (jS_exact z hd dK) hN
  -- the `ξ(q)` jet
  set CQ := 2 * nK * B + nK
  have hlQ : ∀ i, ‖(jQ z).l i‖ ≤ CQ := fun i => by
    simp only [jQ, lQ]
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ a ∈ (univ : Finset (KIdx np)), ‖conj (z.2.1 a.1 a.2) * ev (Sum.inr (Sum.inl a)) i +
        z.2.1 a.1 a.2 * ev (Sum.inr (Sum.inr a)) i‖ ≤ 2 * B := fun a _ => by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have := hzK a
      have e1 := norm_ev_le (Sum.inr (Sum.inl a) : BI K np) i
      have e2 := norm_ev_le (Sum.inr (Sum.inr a) : BI K np) i
      nlinarith [norm_nonneg (z.2.1 a.1 a.2), norm_nonneg (ev (Sum.inr (Sum.inl a) : BI K np) i)]
    have := Finset.sum_le_card_nsmul _ _ _ h1
    simp only [card_univ, nsmul_eq_mul] at this
    nlinarith
  have hqQ : ∀ i i', ‖(jQ z).q i i'‖ ≤ CQ := fun i i' => by
    simp only [jQ, qQ0]
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ a ∈ (univ : Finset (KIdx np)), ‖ev (Sum.inr (Sum.inl a)) i *
        ev (Sum.inr (Sum.inr a)) i'‖ ≤ 1 := fun a _ => by
      rw [norm_mul]
      exact (mul_le_mul (norm_ev_le _ _) (norm_ev_le _ _) (norm_nonneg _) zero_le_one).trans
        (by norm_num)
    have := Finset.sum_le_card_nsmul _ _ _ h1
    simp only [card_univ, nsmul_eq_mul, mul_one] at this
    nlinarith
  have hCQ : 0 ≤ CQ := by positivity
  have jξ := isJet_chain hξ1 hξ2 hξ3 hMξ hCQ hlQ hqQ (jQ_exact z dY dK) hN
  -- the atoms
  have hev : ∀ i i' : BI K np, ‖ev i i'‖ ≤ B := fun i i' => (norm_ev_le i i').trans hB
  have hB10 : B ≤ 10 * B * B := by nlinarith
  have jXa : ∀ a, IsJet B (jX a z) (jX a (zstep z dY dK)).v β := fun a =>
    isJet_exact (hzx a) (fun i => hev _ _) (fun _ _ => by simp [jX, hB0])
      (by simp [jX, zstep, lin_ev, quad, β, bvec])
  have jXca : ∀ a, IsJet B (jXc a z) (jXc a (zstep z dY dK)).v β := fun a =>
    isJet_exact (by simpa [jXc] using hzx a) (fun i => hev _ _) (fun _ _ => by simp [jXc, hB0])
      (by simp [jXc, zstep, lin_ev, quad, β, bvec])
  have jYe : ∀ e, IsJet B (jY e z) (jY e (zstep z dY dK)).v β := fun e =>
    isJet_exact (hzY e) (fun i => hev _ _) (fun _ _ => by simp [jY, hB0]) (by
      simp only [jY, zstep, kHatE, lin_ev, β, bvec, gramEntry_add']
      simp [quad]; ring)
  have jP' : IsJet (10 * B * B) (jP κ z) (jP κ (zstep z dY dK)).v β := by
    rcases κ with a | ⟨a, a'⟩ | ⟨a, e⟩ | ⟨a, a'⟩
    · exact (jXa a).mono hB10
    · exact (jXa a).mul (jXa a') hN
    · exact (jXa a).mul (jYe e) hN
    · exact (jXa a).mul (jXca a') hN
  have jc : IsJet (Mχ * Mξ) (Jet.const (cutC χ z.1.2.2 * cutK ξ z.2.2.2) : Jet (BI K np))
      (cutC χ z.1.2.2 * cutK ξ z.2.2.2) β := by
    refine isJet_const ?_ β
    rw [norm_mul, cutC, cutK, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact mul_le_mul (hMχ _).1 (hMξ _).1 (abs_nonneg _) hMχ0
  have hF := jc.mul ((jχ.mul jξ hN).mul jP' hN) hN
  rw [← jF_v]
  exact hF

end Box

/-!
## Vanishing off the cut region
-/

/-- A zero jet. -/
def IsZJ {I : Type*} (x : Jet I) : Prop := x.v = 0 ∧ (∀ i, x.l i = 0) ∧ ∀ i i', x.q i i' = 0

theorem IsZJ.mul_left {I : Type*} {x : Jet I} (h : IsZJ x) (y : Jet I) : IsZJ (x.mul y) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simp [Jet.mul, h1], fun i => by simp [Jet.mul, h1, h2],
    fun i i' => by simp [Jet.mul, h1, h2, h3]⟩

theorem IsZJ.mul_right {I : Type*} (x : Jet I) {y : Jet I} (h : IsZJ y) : IsZJ (x.mul y) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simp [Jet.mul, h1], fun i => by simp [Jet.mul, h1, h2],
    fun i i' => by simp [Jet.mul, h1, h2, h3]⟩

theorem isZJ_chain {I : Type*} {f f1 f2 : ℝ → ℝ} {x0 : ℝ} (h0 : f x0 = 0) (h1 : f1 x0 = 0)
    (h2 : f2 x0 = 0) (x : Jet I) : IsZJ (Jet.chain f f1 f2 x0 x) :=
  ⟨by simp [Jet.chain, h0], fun i => by simp [Jet.chain, h1],
    fun i i' => by simp [Jet.chain, h1, h2]⟩

theorem isZJ_const {I : Type*} : IsZJ (Jet.const 0 : Jet I) := ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- **Off the cut region the jet of a test vanishes.** -/
theorem isZJ_jF {χ ξ : ℝ → ℝ} {Rχ Rξ : ℝ}
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
    (hRξ : ∀ c, Rξ < |c| → ξ c = 0 ∧ deriv ξ c = 0 ∧ deriv (deriv ξ) c = 0) (κ : KTest K np)
    {z : ZK K np} (hz : ¬ CutReg Rχ Rξ ((0 : GSt K np), z)) : IsZJ (jF χ ξ κ z) := by
  unfold CutReg at hz
  simp only [pyG, pyG0, pyK, pyK0, not_and_or, not_le] at hz
  unfold jF
  rcases hz with h | h | h | h
  · obtain ⟨h0, h1, h2⟩ := hR _ h
    exact IsZJ.mul_right _ (IsZJ.mul_left (IsZJ.mul_left (isZJ_chain h0 h1 h2 _) _) _)
  · have : cutC χ z.1.2.2 * cutK ξ z.2.2.2 = 0 := by simp [cutC, (hR _ h).1]
    rw [this]; exact IsZJ.mul_left isZJ_const _
  · obtain ⟨h0, h1, h2⟩ := hRξ _ h
    exact IsZJ.mul_right _ (IsZJ.mul_left (IsZJ.mul_right _ (isZJ_chain h0 h1 h2 _)) _)
  · have : cutC χ z.1.2.2 * cutK ξ z.2.2.2 = 0 := by simp [cutK, (hRξ _ h).1]
    rw [this]; exact IsZJ.mul_left isZJ_const _

theorem norm_le_sq_add_one' (x : ℝ) : x ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg (x - 1)]

/-- An admissible state in the cut region lies in a fixed box. -/
theorem inBox_of_cutReg {D Rχ Rξ : ℝ} (hD : 0 ≤ D) {z : ZK K np} (hz : Adm D z)
    (hc : CutReg Rχ Rξ ((0 : GSt K np), z)) :
    InBox (2 * (Rχ + D) + 2 * (Rξ + 1)) z := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only [pyG, pyG0, pyK, pyK0] at h1 h2 h3 h4
  have hRχ : 0 ≤ Rχ := (abs_nonneg _).trans h1
  have hRξ : 0 ≤ Rξ := (abs_nonneg _).trans h3
  have hK : ∀ y : KSt np, |qK y| ≤ Rξ → ∀ a : KIdx np, ‖y a.1 a.2‖ ≤ Rξ + 1 := fun y hy a => by
    have e1 : ‖y a.1 a.2‖ ^ 2 ≤ qK y :=
      Finset.single_le_sum (f := fun a : KIdx np => ‖y a.1 a.2‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ a)
    linarith [norm_le_sq_add_one' ‖y a.1 a.2‖, le_abs_self (qK y)]
  refine ⟨fun a => (hK _ h3 a).trans (by linarith), fun a => ?_, fun e => ?_⟩
  · rw [hz.2.2 a]
    refine (norm_sub_le _ _).trans ?_
    linarith [hK _ h3 a, hK _ h4 a]
  · unfold kHatE
    refine (norm_sub_le _ _).trans ?_
    linarith [hz.1 e, hz.2.1 e]

/-!
## The uniform Taylor bound
-/

/-- **The uniform Taylor bound of one step of a test**: bounded test and jet
coefficients on admissible states, and a cubic remainder for every admissible step. -/
theorem exists_taylor_bound {χ ξ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) (hχs : HasCompactSupport χ)
    (hξ : ContDiff ℝ 3 ξ) (hξs : HasCompactSupport ξ) (κ : KTest K np) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ z : ZK K np, Adm D z → ‖κ.fn χ ξ z‖ ≤ C ∧ (∀ i, ‖(jF χ ξ κ z).l i‖ ≤ C) ∧
        ∀ i i', ‖(jF χ ξ κ z).q i i'‖ ≤ C) ∧
      ∀ (z : ZK K np) (dY : GSt K np) (dK : KSt np), Adm D z → Adm D (zstep z dY dK) →
        DiagReal dY →
        ‖κ.fn χ ξ (zstep z dY dK) - κ.fn χ ξ z - lin (jF χ ξ κ z).l (bvec dY dK) -
          quad (jF χ ξ κ z).q (bvec dY dK)‖ ≤ C * nrm (bvec dY dK) ^ 3 := by
  obtain ⟨hχ1, hχ2, hχ3, Mχ, hMχ⟩ := cut_data hχ hχs
  obtain ⟨hξ1, hξ2, hξ3, Mξ, hMξ⟩ := cut_data hξ hξs
  obtain ⟨Rχ0, hRχ0⟩ := exists_cut_radius hχs
  obtain ⟨Rξ0, hRξ0⟩ := exists_cut_radius hξs
  set Rχ := max Rχ0 0
  set Rξ := max Rξ0 0
  have hRχ : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0 := fun c hc =>
    hRχ0 c ((le_max_left _ _).trans_lt hc)
  have hRξ : ∀ c, Rξ < |c| → ξ c = 0 ∧ deriv ξ c = 0 ∧ deriv (deriv ξ) c = 0 := fun c hc =>
    hRξ0 c ((le_max_left _ _).trans_lt hc)
  have hRχp : 0 ≤ Rχ := le_max_right _ _
  have hRξp : 0 ≤ Rξ := le_max_right _ _
  set B0 := 2 * (Rχ + D) + 2 * (Rξ + 1) with hB0d
  set B := B0 + 1 with hBd
  have hB : 1 ≤ B := by linarith
  set Cb := cJ K np Mχ Mξ B
  have hloc := fun z (hz : InBox B z) dY (hd : DiagReal dY) dK hN =>
    isJet_jF hχ1 hχ2 hχ3 hMχ hξ1 hξ2 hξ3 hMξ κ hB (z := z) hz (dY := dY) hd dK hN
  have hd0 : DiagReal (0 : GSt K np) := fun k => by simp
  have hN0 : nrm (bvec (K := K) (0 : GSt K np) (0 : KSt np)) = 0 := by
    unfold nrm; refine sum_eq_zero fun i _ => ?_
    rcases i with e | a | a <;> simp [bvec, gramEntry]
  have hz0 : ∀ z : ZK K np, zstep z 0 0 = z := fun z => by
    simp only [zstep, add_zero, Matrix.zero_apply]
  have hbox : ∀ z : ZK K np, Adm D z → CutReg Rχ Rξ ((0 : GSt K np), z) → InBox B z :=
    fun z hz hc => by
      obtain ⟨h1, h2, h3⟩ := inBox_of_cutReg hD hz hc
      exact ⟨fun a => (h1 a).trans (by linarith [hB0d, hBd]),
        fun a => (h2 a).trans (by linarith [hB0d, hBd]),
        fun e => (h3 e).trans (by linarith [hB0d, hBd])⟩
  -- coefficient bounds on admissible states
  have hcoef : ∀ z : ZK K np, Adm D z → ‖κ.fn χ ξ z‖ ≤ Cb ∧ (∀ i, ‖(jF χ ξ κ z).l i‖ ≤ Cb) ∧
      ∀ i i', ‖(jF χ ξ κ z).q i i'‖ ≤ Cb := fun z hz => by
    by_cases hc : CutReg Rχ Rξ ((0 : GSt K np), z)
    · have hj := hloc z (hbox z hz hc) 0 hd0 0 (by rw [hN0]; exact zero_le_one)
      rw [hz0] at hj
      exact ⟨by rw [← jF_v]; exact hj.1, hj.2.1, hj.2.2.1⟩
    · obtain ⟨h1, h2, h3⟩ := isZJ_jF hRχ hRξ κ hc
      have hC0 : 0 ≤ Cb := by
        have hj := hloc (0 : ZK K np)
          ⟨fun a => by simp; linarith, fun a => by simp; linarith, fun e => by
            simp [kHatE, gramEntry]; linarith⟩ 0 hd0 0 (by rw [hN0]; exact zero_le_one)
        exact hj.nonneg
      exact ⟨by rw [← jF_v, h1, norm_zero]; exact hC0, fun i => by rw [h2, norm_zero]; exact hC0,
        fun i i' => by rw [h3, norm_zero]; exact hC0⟩
  have hCb0 : 0 ≤ Cb := by
    have hj := hloc (0 : ZK K np)
      ⟨fun a => by simp; linarith, fun a => by simp; linarith, fun e => by
        simp [kHatE, gramEntry]; linarith⟩ 0 hd0 0 (by rw [hN0]; exact zero_le_one)
    exact hj.nonneg
  refine ⟨4 * Cb, by positivity, fun z hz => ?_, fun z dY dK hz hz' hd => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hcoef z hz
    exact ⟨h1.trans (by linarith), fun i => (h2 i).trans (by linarith),
      fun i i' => (h3 i i').trans (by linarith)⟩
  set β := bvec dY dK
  set N := nrm β
  have hN0' : 0 ≤ N := nrm_nonneg β
  obtain ⟨hF1, hl1, hq1⟩ := hcoef z hz
  have hF2 := (hcoef _ hz').1
  have hL := norm_lin_le hl1 β
  have hQ := norm_quad_le hq1 β
  by_cases hN : N ≤ 1
  · by_cases hzb : InBox B z
    · have hr := (hloc z hzb dY hd dK hN).2.2.2
      rw [jF_v] at hr
      exact hr.trans
        (mul_le_mul_of_nonneg_right (by change Cb ≤ 4 * Cb; linarith) (pow_nonneg hN0' 3))
    · have hc : ¬ CutReg Rχ Rξ ((0 : GSt K np), z) := fun hc => hzb (hbox z hz hc)
      obtain ⟨h1, h2, h3⟩ := isZJ_jF hRχ hRξ κ hc
      have hc' : ¬ CutReg Rχ Rξ ((0 : GSt K np), zstep z dY dK) := by
        intro hc'
        obtain ⟨b1, b2, b3⟩ := inBox_of_cutReg hD hz' hc'
        refine hzb ⟨fun a => ?_, fun a => ?_, fun e => ?_⟩
        · have e1 : z.2.1 a.1 a.2 = (zstep z dY dK).2.1 a.1 a.2 - β (Sum.inr (Sum.inl a)) := by
            simp [zstep, β, bvec]
          rw [e1]
          refine (norm_sub_le _ _).trans ?_
          have := (norm_le_nrm β (Sum.inr (Sum.inl a))).trans hN
          linarith [b1 a]
        · have e1 : z.2.2.1 a = (zstep z dY dK).2.2.1 a - β (Sum.inr (Sum.inl a)) := by
            simp [zstep, β, bvec]
          rw [e1]
          refine (norm_sub_le _ _).trans ?_
          have := (norm_le_nrm β (Sum.inr (Sum.inl a))).trans hN
          linarith [b2 a]
        · have e1 : kHatE e z = kHatE e (zstep z dY dK) - β (Sum.inl e) := by
            simp only [kHatE, zstep, β, bvec, gramEntry_add']; ring
          rw [e1]
          refine (norm_sub_le _ _).trans ?_
          have := (norm_le_nrm β (Sum.inl e)).trans hN
          linarith [b3 e]
      obtain ⟨h1', -, -⟩ := isZJ_jF hRχ hRξ κ hc'
      rw [← jF_v, ← jF_v, h1, h1']
      have hl0 : lin (jF χ ξ κ z).l β = 0 := by simp [lin, h2]
      have hq0 : quad (jF χ ξ κ z).q β = 0 := by simp [quad, h3]
      rw [hl0, hq0]
      simp only [sub_zero, norm_zero]
      positivity
  · push Not at hN
    have hN2 : N ≤ N ^ 3 := by nlinarith
    have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
    have h1N : 1 ≤ N ^ 3 := by nlinarith
    calc _ ≤ ‖κ.fn χ ξ (zstep z dY dK)‖ + ‖κ.fn χ ξ z‖ + ‖lin (jF χ ξ κ z).l β‖ +
          ‖quad (jF χ ξ κ z).q β‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
      _ ≤ Cb + Cb + Cb * N + Cb * N ^ 2 := by linarith
      _ ≤ 4 * Cb * N ^ 3 := by nlinarith

/-!
## Continuity of the jet coefficients
-/

section Cont

variable {χ ξ : ℝ → ℝ} (hχ0 : Continuous χ) (hχ1 : Continuous (deriv χ))
  (hχ2 : Continuous (deriv (deriv χ))) (hξ0 : Continuous ξ) (hξ1 : Continuous (deriv ξ))
  (hξ2 : Continuous (deriv (deriv ξ)))
include hχ0 hχ1 hχ2 hξ0 hξ1 hξ2

omit hχ2 hξ2 in
theorem continuous_jF_l (κ : KTest K np) (i : BI K np) :
    Continuous fun z : ZK K np => (jF χ ξ κ z).l i := by
  rcases κ with a | ⟨a, a'⟩ | ⟨a, e⟩ | ⟨a, a'⟩
  · simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, lQ, cutC, cutK]
    fun_prop
  · simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, lQ, cutC, cutK]
    fun_prop
  · have := continuous_kHatE (K := K) (np := np) e
    simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, jY, lQ, cutC, cutK]
    fun_prop
  · simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, jXc, lQ, cutC,
      cutK]
    fun_prop

theorem continuous_jF_q (κ : KTest K np) (i i' : BI K np) :
    Continuous fun z : ZK K np => (jF χ ξ κ z).q i i' := by
  rcases κ with a | ⟨a, a'⟩ | ⟨a, e⟩ | ⟨a, a'⟩
  · simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, lQ, cutC, cutK]
    fun_prop
  · simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, lQ, cutC, cutK]
    fun_prop
  · have := continuous_kHatE (K := K) (np := np) e
    simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, jY, lQ, cutC, cutK]
    fun_prop
  · simp only [jF, jP, jChi, jXi, Jet.mul, Jet.const, Jet.chain, jS, jQ, jX, jXc, lQ, cutC,
      cutK]
    fun_prop

end Cont

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
