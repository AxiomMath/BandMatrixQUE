module

public import BlockBand.Native.ErdosRiabov.QV.Path

/-!
# Quadratic variation: local contractions on site lists

Contraction bounds (C1)–(C9) for the squared size functions on site lists. All bounds are at a
single time `t` for the squared list sizes `qvIsoSq`, `qvAvSq`
(`Υ = P.ups t`, `L = P.lEta t`, `η = vsHeight P.z t`). The inputs are collected in
`QVInputs d P t`: the fields of `Contr.ContrVSInputs` (the properties (U2), (U4)–(U7) of the
control at one height), the exact diagonal `Υ(a,a) = 1/L`, and (K4) for the profile `S = P.S`
(`lemmaK_K4_explicit`), both clauses with the constant `qvCS d = √(C₀+1)(1+2√(C₀+1))^D`.
`qvInputs_of` builds them from VS data. Constants: `C₁ = d.C1pp`, `C_w = d.Cwc`, `C_S = qvCS d`.

* (C2) `qvIsoQj`: `Σ_c s(a,u,c)² s(c,v,b)² ≤ C_w/η s(a,u++v,b)²` (the squared convolution bound;
  this list form is used in place of `Contr.isoQj_vs`);
* (C3) `qvIsoConcat`: `s(a,u,c)² s(c,v,b)² ≤ C₁/L s(a,u++v,b)²` (the isotropic concatenation,
  squared);
* (C1) `qvIsoS`: `Σ_{a,b} S_ab s(a,c::r,b)² ≤ C_S C_w/η s^av(c::r)²` (the `S`-bound);
* (C4) `qvIsoDiag`: `Σ_b s(b,c::r,b)² ≤ C_w/η s^av(c::r)²` (all lengths, by the exact diagonal);
* (C5) `qvSSchwarz`, (C6) `qvSTriangle`, `qvSTriangleSqrt`, (C7) `qvSWeight`;
* (C8) `qvQKdiag`: `Σ_b s(b,c::u,q)² S_bq s(b,f::w,b)² ≤ C_S C₁ s^av(c :: u ++ q :: f :: w)²`
  (no `η⁻¹`);
* (C9) `qvQKoff`: `Σ_b s(b,c::u,q)² s(q,w,b)² ≤ C_w/η · L · s^av(c :: u ++ q :: w)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl shortRingProfile)

variable {N : ℕ}

/-- The (K4) constant `C_S = √(C₀+1) (1+2√(C₀+1))^D` (both clauses of `lemmaK_K4_explicit`). -/
def qvCS (d : VSData) : ℝ := Real.sqrt (d.C0 + 1) * (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D

theorem qvCS_ge_one (d : VSData) : 1 ≤ qvCS d := by
  have h1 : 1 ≤ Real.sqrt (d.C0 + 1) := Real.one_le_sqrt.mpr (by linarith [d.C0_ge_one])
  have h2 : 1 ≤ (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D :=
    Real.one_le_rpow (by linarith) (by linarith [d.D_ge_six])
  unfold qvCS
  nlinarith

/-- The single-time inputs of the quadratic-variation contractions. -/
structure QVInputs (d : VSData) (P : PsiData N) (t : ℝ) : Prop
    extends Contr.ContrVSInputs d P t where
  diag : ∀ a, P.ups t a a = (P.lEta t)⁻¹
  sNonneg : ∀ x y, 0 ≤ P.S x y
  sSymm : ∀ x y, P.S x y = P.S y x
  sLe : ∀ x y, P.S x y ≤ qvCS d * P.ups t x y
  sConv : ∀ x y, ∑ a, P.S x a * P.ups t a y ≤ qvCS d * P.ups t x y

/-- **The QV inputs from VS data** (`Contr.contrVSInputs_of`, `lemmaK_K4_explicit`, the exact
diagonal).
-/
theorem qvInputs_of (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W))
    (hPW : P.W = W) (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
    (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QVInputs d P t := by
  have hin := Contr.contrVSInputs_of d hm hW P hPW hPD hz ht0 ht1
  have hS := shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (m := m) (by omega) hW
  have hu : P.ups t = polynomialControl (m * W) W d.D (vsHeight P.z t) := by
    unfold PsiData.ups
    rw [hPW, hPD]
  have hK4 := fun x y => LemmaK.lemmaK_K4_explicit d.b_pos d.b_lt_half hm hW d.C0_ge_one
    (D := d.D) (by linarith [d.D_ge_six]) hin.height_pos hin.height_le x y
  have hr1 : 1 ≤ Real.sqrt (d.C0 + 1) := Real.one_le_sqrt.mpr (by linarith [d.C0_ge_one])
  have hpow0 : 0 ≤ (1 + 2 * Real.sqrt (d.C0 + 1)) ^ d.D :=
    Real.rpow_nonneg (by positivity) _
  refine ⟨hin, qv_ups_diag P t, fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [hPS]; exact hS.nonneg x y
  · rw [hPS]; exact hS.symm x y
  · rw [hPS, hu]; exact (hK4 x y).1
  · rw [hPS, hu]
    have h2 := (hK4 x y).2
    rw [Matrix.mul_apply] at h2
    refine h2.trans ?_
    unfold qvCS
    have hU := (Adapters.ErdosRiabov.polynomialControl_pos (Nat.mul_pos (by omega) hW) hW d.D
      hin.height_pos x y).le
    nlinarith [mul_le_mul_of_nonneg_right hr1 (mul_nonneg hpow0 hU)]

section Generic

variable {P : PsiData N} {t : ℝ}

/-!
### Decompositions
-/

/-- The open path `L^{-|u|} Π Υ` along `a :: u` (the last link to `b` removed). -/
def qvIsoOpen (P : PsiData N) (t : ℝ) (a : Fin N) (u : List (Fin N)) : ℝ :=
  (P.lEta t)⁻¹ ^ u.length * qvPath (P.ups t) (a :: u)

theorem qvIsoOpen_nonneg (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) (a : Fin N)
    (u : List (Fin N)) : 0 ≤ qvIsoOpen P t a u :=
  mul_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) _) (qvPath_nonneg hU _)

/-- Removing the last link: `s(a,u,b)² = open(a,u) · Υ(e,b)`, `e` the last site of `a :: u`. -/
theorem qvIsoSq_last (a : Fin N) (u : List (Fin N)) (b : Fin N) :
    qvIsoSq P t a u b =
      qvIsoOpen P t a u * P.ups t ((a :: u).getLast (List.cons_ne_nil a u)) b := by
  unfold qvIsoSq qvIsoOpen
  rw [List.cons_append, ← List.cons_append, qvPath_snoc _ _ (List.cons_ne_nil a u)]
  ring

/-- Joining at the last site: `s(a, u ++ v, b)² = open(a,u) · s(e, v, b)²`. -/
theorem qvIsoSq_join (a : Fin N) (u v : List (Fin N)) (b : Fin N) :
    qvIsoSq P t a (u ++ v) b =
      qvIsoOpen P t a u * qvIsoSq P t ((a :: u).getLast (List.cons_ne_nil a u)) v b := by
  unfold qvIsoSq qvIsoOpen
  set e := (a :: u).getLast (List.cons_ne_nil a u)
  have hd := List.dropLast_append_getLast (List.cons_ne_nil a u)
  have h1 : a :: (u ++ v) ++ [b] = (a :: u).dropLast ++ e :: (v ++ [b]) := by
    have h3 : (a :: u).dropLast ++ e :: (v ++ [b]) = ((a :: u).dropLast ++ [e]) ++ (v ++ [b]) :=
      by simp
    rw [h3, hd]; simp
  have h2 : qvPath (P.ups t) (a :: u) = qvPath (P.ups t) ((a :: u).dropLast ++ [e]) := by
    rw [hd]
  rw [h1, qvPath_append, ← h2, List.length_append, pow_add]
  simp only [List.cons_append]
  ring

/-- Removing the first link: `s(a, c :: r, b)² = L⁻¹ Υ(a,c) s(c,r,b)²`. -/
theorem qvIsoSq_cons (a c : Fin N) (r : List (Fin N)) (b : Fin N) :
    qvIsoSq P t a (c :: r) b = (P.lEta t)⁻¹ * P.ups t a c * qvIsoSq P t c r b := by
  have h := qvIsoSq_split P t a [] c r b
  rw [List.nil_append, qvIsoSq_nil] at h
  exact h

/-!
### The two middle-point contractions
-/

/-- Generic summed middle-point contraction from a two-link bound. -/
theorem qvIsoSq_contract_sum (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (hK : ∀ e f, ∑ c, P.ups t e c * P.ups t c f ≤ K * P.ups t e f)
    (a : Fin N) (u v : List (Fin N)) (b : Fin N) :
    ∑ c, qvIsoSq P t a u c * qvIsoSq P t c v b ≤ K * qvIsoSq P t a (u ++ v) b := by
  set e := (a :: u).getLast (List.cons_ne_nil a u)
  have ho := qvIsoOpen_nonneg hU hL a u
  simp_rw [qvIsoSq_last a u, qvIsoSq_join a u v b]
  cases v with
  | nil =>
    simp_rw [qvIsoSq_nil]
    calc ∑ c, qvIsoOpen P t a u * P.ups t e c * P.ups t c b
        = qvIsoOpen P t a u * ∑ c, P.ups t e c * P.ups t c b := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ qvIsoOpen P t a u * (K * P.ups t e b) := mul_le_mul_of_nonneg_left (hK e b) ho
      _ = _ := by ring
  | cons f v' =>
    simp_rw [qvIsoSq_cons _ f v' b]
    have hq := qvIsoSq_nonneg P t hU hL f v' b
    calc ∑ c, qvIsoOpen P t a u * P.ups t e c *
          ((P.lEta t)⁻¹ * P.ups t c f * qvIsoSq P t f v' b)
        = qvIsoOpen P t a u * (P.lEta t)⁻¹ * qvIsoSq P t f v' b *
            ∑ c, P.ups t e c * P.ups t c f := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ qvIsoOpen P t a u * (P.lEta t)⁻¹ * qvIsoSq P t f v' b * (K * P.ups t e f) :=
          mul_le_mul_of_nonneg_left (hK e f)
            (mul_nonneg (mul_nonneg ho (inv_nonneg.mpr hL.le)) hq)
      _ = _ := by ring

/-- Generic pointwise middle-point contraction from a two-link bound. -/
theorem qvIsoSq_contract_pt (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (hK : ∀ e c f, P.ups t e c * P.ups t c f ≤ K * P.ups t e f)
    (a : Fin N) (u : List (Fin N)) (c : Fin N) (v : List (Fin N)) (b : Fin N) :
    qvIsoSq P t a u c * qvIsoSq P t c v b ≤ K * qvIsoSq P t a (u ++ v) b := by
  set e := (a :: u).getLast (List.cons_ne_nil a u)
  have ho := qvIsoOpen_nonneg hU hL a u
  rw [qvIsoSq_last a u, qvIsoSq_join a u v b]
  cases v with
  | nil =>
    rw [qvIsoSq_nil, qvIsoSq_nil]
    calc qvIsoOpen P t a u * P.ups t e c * P.ups t c b
        = qvIsoOpen P t a u * (P.ups t e c * P.ups t c b) := by ring
      _ ≤ qvIsoOpen P t a u * (K * P.ups t e b) := mul_le_mul_of_nonneg_left (hK e c b) ho
      _ = _ := by ring
  | cons f v' =>
    rw [qvIsoSq_cons c f v' b, qvIsoSq_cons e f v' b]
    have hq := qvIsoSq_nonneg P t hU hL f v' b
    calc qvIsoOpen P t a u * P.ups t e c * ((P.lEta t)⁻¹ * P.ups t c f * qvIsoSq P t f v' b)
        = qvIsoOpen P t a u * (P.lEta t)⁻¹ * qvIsoSq P t f v' b *
            (P.ups t e c * P.ups t c f) := by ring
      _ ≤ qvIsoOpen P t a u * (P.lEta t)⁻¹ * qvIsoSq P t f v' b * (K * P.ups t e f) :=
          mul_le_mul_of_nonneg_left (hK e c f)
            (mul_nonneg (mul_nonneg ho (inv_nonneg.mpr hL.le)) hq)
      _ = _ := by ring

end Generic

section Contractions

variable {d : VSData} {P : PsiData N} {t : ℝ} (hin : QVInputs d P t)
include hin

/-- **(C2) contraction.** `Σ_c s(a,u,c)² s(c,v,b)² ≤ C_w/η · s(a,u++v,b)²`. -/
theorem qvIsoQj (a : Fin N) (u v : List (Fin N)) (b : Fin N) :
    ∑ c, qvIsoSq P t a u c * qvIsoSq P t c v b ≤
      d.Cwc / vsHeight P.z t * qvIsoSq P t a (u ++ v) b :=
  qvIsoSq_contract_sum hin.nonneg hin.lEta_pos hin.convol a u v b

/-- **(C3), squared.** `s(a,u,c)² s(c,v,b)² ≤ C₁/L · s(a,u++v,b)²`. -/
theorem qvIsoConcat (a : Fin N) (u : List (Fin N)) (c : Fin N) (v : List (Fin N))
    (b : Fin N) :
    qvIsoSq P t a u c * qvIsoSq P t c v b ≤ d.C1pp / P.lEta t * qvIsoSq P t a (u ++ v) b :=
  qvIsoSq_contract_pt hin.nonneg hin.lEta_pos hin.triangle a u c v b

/-!
### Diagonal and profile contractions
-/

/-- **(C4) isoDiag.** `Σ_b s(b, c:: r, b)² ≤ C_w/η · s^av(c:: r)²` (every length, including
`r = []`, by the exact diagonal built into `qvAvSq`).
-/
theorem qvIsoDiag (c : Fin N) (r : List (Fin N)) :
    ∑ b, qvIsoSq P t b (c :: r) b ≤ d.Cwc / vsHeight P.z t * qvAvSq P t c r := by
  set e := (c :: r).getLast (List.cons_ne_nil c r)
  have ho := qvIsoOpen_nonneg hin.nonneg hin.lEta_pos c r
  have hLi := inv_nonneg.mpr hin.lEta_pos.le
  simp_rw [qvIsoSq_cons _ c r, qvIsoSq_last c r]
  rw [qvAvSq_eq, qvIsoSq_last c r c]
  calc ∑ b, (P.lEta t)⁻¹ * P.ups t b c * (qvIsoOpen P t c r * P.ups t e b)
      = (P.lEta t)⁻¹ * qvIsoOpen P t c r * ∑ b, P.ups t e b * P.ups t b c := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ (P.lEta t)⁻¹ * qvIsoOpen P t c r * (d.Cwc / vsHeight P.z t * P.ups t e c) :=
        mul_le_mul_of_nonneg_left (hin.convol e c) (mul_nonneg hLi ho)
    _ = _ := by ring

/-- **(C1).** `Σ_a Σ_b S_ab s(a, c:: r, b)² ≤ C_S C_w/η · s^av(c:: r)²`. -/
theorem qvIsoS (c : Fin N) (r : List (Fin N)) :
    ∑ a, ∑ b, P.S a b * qvIsoSq P t a (c :: r) b ≤
      qvCS d * (d.Cwc / vsHeight P.z t) * qvAvSq P t c r := by
  set e := (c :: r).getLast (List.cons_ne_nil c r)
  have ho := qvIsoOpen_nonneg hin.nonneg hin.lEta_pos c r
  have hLi := inv_nonneg.mpr hin.lEta_pos.le
  have hCS : 0 ≤ qvCS d := by linarith [qvCS_ge_one d]
  simp_rw [qvIsoSq_cons _ c r, qvIsoSq_last c r]
  rw [Finset.sum_comm, qvAvSq_eq, qvIsoSq_last c r c]
  have hin1 : ∀ b, ∑ a, P.S a b * ((P.lEta t)⁻¹ * P.ups t a c *
      (qvIsoOpen P t c r * P.ups t e b)) ≤
      (P.lEta t)⁻¹ * qvIsoOpen P t c r * qvCS d * (P.ups t e b * P.ups t b c) := by
    intro b
    have e1 : ∑ a, P.S a b * ((P.lEta t)⁻¹ * P.ups t a c * (qvIsoOpen P t c r * P.ups t e b))
        = (P.lEta t)⁻¹ * qvIsoOpen P t c r * P.ups t e b * ∑ a, P.S b a * P.ups t a c := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hin.sSymm a b]; ring
    rw [e1]
    calc (P.lEta t)⁻¹ * qvIsoOpen P t c r * P.ups t e b * ∑ a, P.S b a * P.ups t a c
        ≤ (P.lEta t)⁻¹ * qvIsoOpen P t c r * P.ups t e b * (qvCS d * P.ups t b c) :=
          mul_le_mul_of_nonneg_left (hin.sConv b c)
            (mul_nonneg (mul_nonneg hLi ho) (hin.nonneg _ _))
      _ = _ := by ring
  calc ∑ b, ∑ a, P.S a b * ((P.lEta t)⁻¹ * P.ups t a c * (qvIsoOpen P t c r * P.ups t e b))
      ≤ ∑ b, (P.lEta t)⁻¹ * qvIsoOpen P t c r * qvCS d * (P.ups t e b * P.ups t b c) :=
        Finset.sum_le_sum fun b _ => hin1 b
    _ = (P.lEta t)⁻¹ * qvIsoOpen P t c r * qvCS d * ∑ b, P.ups t e b * P.ups t b c := by
        rw [Finset.mul_sum]
    _ ≤ (P.lEta t)⁻¹ * qvIsoOpen P t c r * qvCS d * (d.Cwc / vsHeight P.z t * P.ups t e c) :=
        mul_le_mul_of_nonneg_left (hin.convol e c) (mul_nonneg (mul_nonneg hLi ho) hCS)
    _ = _ := by ring

/-- **(C7) sWeight.** `Σ_a S_xa s(a,u,b)² ≤ C_S s(x,u,b)²`. -/
theorem qvSWeight (x : Fin N) (u : List (Fin N)) (b : Fin N) :
    ∑ a, P.S x a * qvIsoSq P t a u b ≤ qvCS d * qvIsoSq P t x u b := by
  cases u with
  | nil =>
    simp_rw [qvIsoSq_nil]
    exact hin.sConv x b
  | cons c r =>
    simp_rw [qvIsoSq_cons _ c r b]
    have hq := qvIsoSq_nonneg P t hin.nonneg hin.lEta_pos c r b
    have hLi := inv_nonneg.mpr hin.lEta_pos.le
    calc ∑ a, P.S x a * ((P.lEta t)⁻¹ * P.ups t a c * qvIsoSq P t c r b)
        = (P.lEta t)⁻¹ * qvIsoSq P t c r b * ∑ a, P.S x a * P.ups t a c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      _ ≤ (P.lEta t)⁻¹ * qvIsoSq P t c r b * (qvCS d * P.ups t x c) :=
          mul_le_mul_of_nonneg_left (hin.sConv x c) (mul_nonneg hLi hq)
      _ = _ := by ring

/-- **(C6) sTriangle.** `S_xb Υ(b,y) ≤ C_S C₁/L · Υ(x,y)`. -/
theorem qvSTriangle (x b y : Fin N) :
    P.S x b * P.ups t b y ≤ qvCS d * (d.C1pp / P.lEta t) * P.ups t x y := by
  calc P.S x b * P.ups t b y ≤ qvCS d * P.ups t x b * P.ups t b y :=
        mul_le_mul_of_nonneg_right (hin.sLe x b) (hin.nonneg _ _)
    _ = qvCS d * (P.ups t x b * P.ups t b y) := by ring
    _ ≤ qvCS d * (d.C1pp / P.lEta t * P.ups t x y) :=
        mul_le_mul_of_nonneg_left (hin.triangle x b y) (by linarith [qvCS_ge_one d])
    _ = _ := by ring

/-- **(C6), square-root form.** `S_xb √(Υ(b,y)Υ(b,w)) ≤ C_S C₁/L · √(Υ(x,y)Υ(x,w))`. -/
theorem qvSTriangleSqrt (x b y w : Fin N) :
    P.S x b * Real.sqrt (P.ups t b y * P.ups t b w) ≤
      qvCS d * (d.C1pp / P.lEta t) * Real.sqrt (P.ups t x y * P.ups t x w) := by
  have hK : 0 ≤ d.C1pp / P.lEta t := div_nonneg (by linarith [d.one_le_C1pp]) hin.lEta_pos.le
  have h1 := hin.triangle x b y
  have h2 := hin.triangle x b w
  have hxb := hin.nonneg x b
  have hsq : Real.sqrt (P.ups t x b * P.ups t b y * (P.ups t x b * P.ups t b w)) ≤
      Real.sqrt (d.C1pp / P.lEta t * P.ups t x y * (d.C1pp / P.lEta t * P.ups t x w)) :=
    Real.sqrt_le_sqrt (mul_le_mul h1 h2 (mul_nonneg hxb (hin.nonneg _ _))
      (mul_nonneg hK (hin.nonneg _ _)))
  have hl : Real.sqrt (P.ups t x b * P.ups t b y * (P.ups t x b * P.ups t b w)) =
      P.ups t x b * Real.sqrt (P.ups t b y * P.ups t b w) := by
    rw [show P.ups t x b * P.ups t b y * (P.ups t x b * P.ups t b w) =
      P.ups t x b ^ 2 * (P.ups t b y * P.ups t b w) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hxb]
  have hr : Real.sqrt (d.C1pp / P.lEta t * P.ups t x y * (d.C1pp / P.lEta t * P.ups t x w)) =
      d.C1pp / P.lEta t * Real.sqrt (P.ups t x y * P.ups t x w) := by
    rw [show d.C1pp / P.lEta t * P.ups t x y * (d.C1pp / P.lEta t * P.ups t x w) =
      (d.C1pp / P.lEta t) ^ 2 * (P.ups t x y * P.ups t x w) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]
  rw [hl, hr] at hsq
  calc P.S x b * Real.sqrt (P.ups t b y * P.ups t b w)
      ≤ qvCS d * P.ups t x b * Real.sqrt (P.ups t b y * P.ups t b w) :=
        mul_le_mul_of_nonneg_right (hin.sLe x b) (Real.sqrt_nonneg _)
    _ = qvCS d * (P.ups t x b * Real.sqrt (P.ups t b y * P.ups t b w)) := by ring
    _ ≤ qvCS d * (d.C1pp / P.lEta t * Real.sqrt (P.ups t x y * P.ups t x w)) :=
        mul_le_mul_of_nonneg_left hsq (by linarith [qvCS_ge_one d])
    _ = _ := by ring

/-- **(C5) sSchwarz.** `Σ_q S_xq √(Υ(q,y)Υ(q,w)) ≤ C_S √(Υ(x,y)Υ(x,w))` (weighted
Cauchy–Schwarz and (K4)).
-/
theorem qvSSchwarz (x y w : Fin N) :
    ∑ q, P.S x q * Real.sqrt (P.ups t q y * P.ups t q w) ≤
      qvCS d * Real.sqrt (P.ups t x y * P.ups t x w) := by
  have hCS : 0 ≤ qvCS d := by linarith [qvCS_ge_one d]
  have e : ∀ q, P.S x q * Real.sqrt (P.ups t q y * P.ups t q w) =
      Real.sqrt (P.S x q * P.ups t q y) * Real.sqrt (P.S x q * P.ups t q w) := by
    intro q
    rw [← Real.sqrt_mul (mul_nonneg (hin.sNonneg _ _) (hin.nonneg _ _)),
      show P.S x q * P.ups t q y * (P.S x q * P.ups t q w) =
        P.S x q ^ 2 * (P.ups t q y * P.ups t q w) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hin.sNonneg _ _)]
  simp_rw [e]
  refine (Real.sum_sqrt_mul_sqrt_le _ (fun q => mul_nonneg (hin.sNonneg _ _) (hin.nonneg _ _))
    (fun q => mul_nonneg (hin.sNonneg _ _) (hin.nonneg _ _))).trans ?_
  calc Real.sqrt (∑ q, P.S x q * P.ups t q y) * Real.sqrt (∑ q, P.S x q * P.ups t q w)
      ≤ Real.sqrt (qvCS d * P.ups t x y) * Real.sqrt (qvCS d * P.ups t x w) :=
        mul_le_mul (Real.sqrt_le_sqrt (hin.sConv x y)) (Real.sqrt_le_sqrt (hin.sConv x w))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = qvCS d * Real.sqrt (P.ups t x y * P.ups t x w) := by
        rw [← Real.sqrt_mul (mul_nonneg hCS (hin.nonneg _ _)),
          show qvCS d * P.ups t x y * (qvCS d * P.ups t x w) =
            qvCS d ^ 2 * (P.ups t x y * P.ups t x w) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCS]

/-!
### The two contractions of the `K`-cut
-/

/-- **(C8) QKdiag**:
`Σ_b s(b,c::u,q)² S_bq s(b,f::w,b)² ≤ C_S C₁ · s^av(c:: u ++ q:: f:: w)²`.
-/
theorem qvQKdiag (c : Fin N) (u : List (Fin N)) (q f : Fin N) (w : List (Fin N)) :
    ∑ b, qvIsoSq P t b (c :: u) q * P.S b q * qvIsoSq P t b (f :: w) b ≤
      qvCS d * d.C1pp * qvAvSq P t c (u ++ q :: f :: w) := by
  have hLi := inv_nonneg.mpr hin.lEta_pos.le
  have hA := qvIsoSq_nonneg P t hin.nonneg hin.lEta_pos c u q
  have ho := qvIsoOpen_nonneg hin.nonneg hin.lEta_pos f w
  have hCS : 0 ≤ qvCS d := by linarith [qvCS_ge_one d]
  simp_rw [qvIsoSq_cons _ c u q, qvIsoSq_cons _ f w, qvIsoSq_last f w]
  rw [qvAvSq_eq, qvIsoSq_split, qvIsoSq_cons q f w c, qvIsoSq_last f w c]
  set g := (f :: w).getLast (List.cons_ne_nil f w)
  set X := (P.lEta t)⁻¹ * (P.lEta t)⁻¹ * qvIsoSq P t c u q * qvIsoOpen P t f w
  have hX : 0 ≤ X := mul_nonneg (mul_nonneg (mul_nonneg hLi hLi) hA) ho
  have hpt : ∀ b, (P.lEta t)⁻¹ * P.ups t b c * qvIsoSq P t c u q * P.S b q *
      ((P.lEta t)⁻¹ * P.ups t b f * (qvIsoOpen P t f w * P.ups t g b)) ≤
      X * (d.C1pp / P.lEta t * P.ups t g c) * (P.S q b * P.ups t b f) := by
    intro b
    have h1 : P.ups t g b * P.ups t b c ≤ d.C1pp / P.lEta t * P.ups t g c := hin.triangle g b c
    have hSb : 0 ≤ P.S q b * P.ups t b f := mul_nonneg (hin.sNonneg _ _) (hin.nonneg _ _)
    calc (P.lEta t)⁻¹ * P.ups t b c * qvIsoSq P t c u q * P.S b q *
          ((P.lEta t)⁻¹ * P.ups t b f * (qvIsoOpen P t f w * P.ups t g b))
        = X * (P.ups t g b * P.ups t b c) * (P.S q b * P.ups t b f) := by
          rw [hin.sSymm b q]; ring
      _ ≤ X * (d.C1pp / P.lEta t * P.ups t g c) * (P.S q b * P.ups t b f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hX) hSb
  refine (Finset.sum_le_sum fun b _ => hpt b).trans ?_
  rw [← Finset.mul_sum]
  have hK : 0 ≤ X * (d.C1pp / P.lEta t * P.ups t g c) :=
    mul_nonneg hX (mul_nonneg (div_nonneg (by linarith [d.one_le_C1pp]) hin.lEta_pos.le)
      (hin.nonneg _ _))
  calc X * (d.C1pp / P.lEta t * P.ups t g c) * ∑ b, P.S q b * P.ups t b f
      ≤ X * (d.C1pp / P.lEta t * P.ups t g c) * (qvCS d * P.ups t q f) :=
        mul_le_mul_of_nonneg_left (hin.sConv q f) hK
    _ = _ := by unfold X; field_simp

/-- **(C9) QKoff.** `Σ_b s(b,c::u,q)² s(q,w,b)² ≤ C_w/η · L · s^av(c:: u ++ q:: w)²`. -/
theorem qvQKoff (c : Fin N) (u : List (Fin N)) (q : Fin N) (w : List (Fin N)) :
    ∑ b, qvIsoSq P t b (c :: u) q * qvIsoSq P t q w b ≤
      d.Cwc / vsHeight P.z t * P.lEta t * qvAvSq P t c (u ++ q :: w) := by
  have hLi := inv_nonneg.mpr hin.lEta_pos.le
  have hA := qvIsoSq_nonneg P t hin.nonneg hin.lEta_pos c u q
  have ho := qvIsoOpen_nonneg hin.nonneg hin.lEta_pos q w
  simp_rw [qvIsoSq_cons _ c u q, qvIsoSq_last q w]
  rw [qvAvSq_eq, qvIsoSq_split, qvIsoSq_last q w c]
  set g := (q :: w).getLast (List.cons_ne_nil q w)
  have hX : 0 ≤ (P.lEta t)⁻¹ * qvIsoSq P t c u q * qvIsoOpen P t q w :=
    mul_nonneg (mul_nonneg hLi hA) ho
  calc ∑ b, (P.lEta t)⁻¹ * P.ups t b c * qvIsoSq P t c u q * (qvIsoOpen P t q w * P.ups t g b)
      = (P.lEta t)⁻¹ * qvIsoSq P t c u q * qvIsoOpen P t q w *
          ∑ b, P.ups t g b * P.ups t b c := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ (P.lEta t)⁻¹ * qvIsoSq P t c u q * qvIsoOpen P t q w *
          (d.Cwc / vsHeight P.z t * P.ups t g c) :=
        mul_le_mul_of_nonneg_left (hin.convol g c) hX
    _ = _ := by
        have hL := hin.lEta_pos.ne'
        field_simp

end Contractions

end BlockBand.Native.ErdosRiabov.QV
