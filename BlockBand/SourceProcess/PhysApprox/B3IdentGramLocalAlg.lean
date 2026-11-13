module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalDefs
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalTaylor

/-!
# The exact one-step expansion of the cutoff tests

A step of the state `z = (y, x, y₀)` to `z' = (y', x + δ − ℓλ, y₀)`, with the Gram increment
`δ_c = y'_c − y_c` (`dlt`), the cut drift `λ_e = lamA χ b E e (J, y)` and a cell length `ℓ`.
With `h = Σ_k δ_{(0,k,k)}` (real on Hermitian states) and the Taylor remainder `ρ` of `χ`:
* `ip1`, `ip2`, `vE`, `vD`, `otm`: coordinate pairings, the unit vector of `e`, the diagonal
  `M`-vector, outer products;
* **`expand1`, `expand2`**: `F(z') − F(z) = a₀ + Σ_c a₁_c δ_c + Σ_{c,c'} a₂_{cc'} δ_c δ_{c'} + rest`
  for `fun1`, `fun2`, with the polynomial parts exact and `rest` explicit;
* **`gen1`, `gen2`**: replacing `δ_c` by `w b_c` and `δ_c δ_{c'}` by `w Γ_{cc'}` (`w = ℓ`)
  gives `w Λ + w² Γ` (`lam1`, `lam2`);
* **`IsGenPair.taylorData`**: the data packaged for a generator pair, with the rest bounded by
  `C (η³ + η⁴)`, `η = Σ_c |δ_c| + ℓ B`, when `|x|, |λ| ≤ B`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory Filter Topology Matrix Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

variable {K np : ℕ}

/-!
## Coordinate pairings
-/

def vE (e : GIdx K np) : GIdx K np → ℂ := fun c => if c = e then 1 else 0

def vD : GIdx K np → ℂ := fun c => if c.1 = 0 ∧ c.2.1 = c.2.2 then 1 else 0

def ip1 (a δ : GIdx K np → ℂ) : ℂ := ∑ c, a c * δ c

def ip2 (a δ : GIdx K np → GIdx K np → ℂ) : ℂ := ∑ c, ∑ c', a c c' * δ c c'

def otm (u v : GIdx K np → ℂ) : GIdx K np → GIdx K np → ℂ := fun c c' => u c * v c'

def sq2 (δ : GIdx K np → ℂ) : GIdx K np → GIdx K np → ℂ := fun c c' => δ c * δ c'

theorem ip1_vE (e : GIdx K np) (δ : GIdx K np → ℂ) : ip1 (vE e) δ = δ e := by
  simp [ip1, vE]

theorem ip1_vD (δ : GIdx K np → ℂ) : ip1 vD δ = ∑ k, δ (0, k, k) := by
  simp [ip1, vD, Fintype.sum_prod_type, Fin.sum_univ_two, ite_mul]

theorem ip1_add (a a' δ : GIdx K np → ℂ) : ip1 (a + a') δ = ip1 a δ + ip1 a' δ := by
  simp [ip1, add_mul, Finset.sum_add_distrib]

theorem ip1_smul (r : ℂ) (a δ : GIdx K np → ℂ) : ip1 (r • a) δ = r * ip1 a δ := by
  simp [ip1, Finset.mul_sum, mul_assoc]

theorem ip1_mul_right (a δ : GIdx K np → ℂ) (w : ℂ) :
    ip1 a (fun c => w * δ c) = w * ip1 a δ := by
  simp only [ip1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ip2_add (A A' δ : GIdx K np → GIdx K np → ℂ) :
    ip2 (A + A') δ = ip2 A δ + ip2 A' δ := by
  simp [ip2, add_mul, Finset.sum_add_distrib]

theorem ip2_smul (r : ℂ) (A δ : GIdx K np → GIdx K np → ℂ) : ip2 (r • A) δ = r * ip2 A δ := by
  simp [ip2, Finset.mul_sum, mul_assoc]

theorem ip2_mul_right (A δ : GIdx K np → GIdx K np → ℂ) (w : ℂ) :
    ip2 A (fun c c' => w * δ c c') = w * ip2 A δ := by
  simp only [ip2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ip2_otm (u v : GIdx K np → ℂ) (δ : GIdx K np → GIdx K np → ℂ) :
    ip2 (otm u v) δ = ip1 u (fun c => ip1 v (δ c)) := by
  simp only [ip2, otm, ip1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ip2_otm_sq2 (u v δ : GIdx K np → ℂ) :
    ip2 (otm u v) (sq2 δ) = ip1 u δ * ip1 v δ := by
  simp only [ip2, otm, sq2, ip1]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-!
## The step and the scalars
-/

/-- The Gram increment `δ_c = y'_c − y_c`. -/
def dlt (y y' : GSt K np) : GIdx K np → ℂ := fun c => gramEntry c y' - gramEntry c y

/-- The next state: `(y', x + δ − ℓλ, y₀)`. -/
def nextZ (χ : ℝ → ℝ) (b E : ℝ) (J y' : GSt K np) (ℓ : ℝ) (z : ZSt K np) : ZSt K np :=
  (y', fun e => z.2.1 e + dlt z.1 y' e - (ℓ : ℂ) * lamA χ b E e (J, z.1), z.2.2)

section Scalars

variable (χ : ℝ → ℝ) (b E : ℝ) (p : GSt K np × ZSt K np × ℝ)

/-- `χ(s(y₀))`. -/
abbrev sc0 : ℂ := cutC χ p.2.1.2.2
/-- `χ(s(y))`, `χ'(s(y))`, `χ''(s(y))`. -/
abbrev sk0 : ℂ := cutC χ p.2.1.1
abbrev sk1 : ℂ := cutC (deriv χ) p.2.1.1
abbrev sk2 : ℂ := cutC (deriv (deriv χ)) p.2.1.1
/-- The cell length. -/
abbrev sl : ℂ := (p.2.2 : ℂ)
/-- The cut drift `λ_e`. -/
abbrev sla (e : GIdx K np) : ℂ := lamA χ b E e (p.1, p.2.1.1)

end Scalars

/-!
## `fun1`
-/

section F1

variable (χ : ℝ → ℝ) (b E : ℝ) (e : GIdx K np)

def a0F1 (p : GSt K np × ZSt K np × ℝ) : ℂ :=
  -(sc0 χ p * sk0 χ p * sl p * sla χ b E p e)

def a1F1 (p : GSt K np × ZSt K np × ℝ) : GIdx K np → ℂ :=
  (sc0 χ p * sk0 χ p) • vE e +
    (sc0 χ p * sk1 χ p * p.2.1.2.1 e - sc0 χ p * sk1 χ p * sl p * sla χ b E p e) • vD

def a2F1 (p : GSt K np × ZSt K np × ℝ) : GIdx K np → GIdx K np → ℂ :=
  (sc0 χ p * sk1 χ p) • otm vD (vE e) + (sc0 χ p * sk2 χ p * p.2.1.2.1 e / 2) • otm vD vD

/-- The rest of `fun1`: `c₀ (χ''/2 h² ξ_e + ρ (x_e + ξ_e))`. -/
def rest1 (c0 k2 ρ h ξ x : ℂ) : ℂ := c0 * (k2 / 2 * h ^ 2 * ξ + ρ * (x + ξ))

def gam1 (q : GSt K np × ZSt K np) : ℂ :=
  -(cutC χ q.2.2.2 * cutC (deriv χ) q.2.1 * lamA χ b E e (q.1, q.2.1) * trDr b E (q.2.1 + q.1))

theorem expand1 (J y' : GSt K np) (z : ZSt K np) (ℓ : ℝ)
    (hh : ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ)) :
    fun1 χ e (nextZ χ b E J y' ℓ z) - fun1 χ e z =
      a0F1 χ b E e (J, z, ℓ) + ip1 (a1F1 χ b E e (J, z, ℓ)) (dlt z.1 y') +
        ip2 (a2F1 χ e (J, z, ℓ)) (sq2 (dlt z.1 y')) +
        rest1 (cutC χ z.2.2) (cutC (deriv (deriv χ)) z.1)
          (taylorRem χ (trRe z.1) (trRe y' - trRe z.1) : ℂ) (∑ k, dlt z.1 y' (0, k, k))
          (dlt z.1 y' e - (ℓ : ℂ) * lamA χ b E e (J, z.1)) (z.2.1 e) := by
  have hρ : χ (trRe y') = χ (trRe z.1) + deriv χ (trRe z.1) * (trRe y' - trRe z.1) +
      deriv (deriv χ) (trRe z.1) * (trRe y' - trRe z.1) ^ 2 / 2 +
      taylorRem χ (trRe z.1) (trRe y' - trRe z.1) := by
    simp only [taylorRem, add_sub_cancel]; ring
  simp only [a1F1, a2F1, ip1_add, ip1_smul, ip2_add, ip2_smul, ip2_otm_sq2, ip1_vE, ip1_vD]
  rw [hh]
  simp only [fun1, nextZ, a0F1, rest1, cutC, sc0, sk0, sk1, sk2, sl, sla]
  rw [hρ]
  push_cast
  ring

theorem gen1 (J : GSt K np) (z : ZSt K np) (w : ℝ) :
    a0F1 χ b E e (J, z, w) + ip1 (a1F1 χ b E e (J, z, w)) (fun c => (w : ℂ) * drE b E c (z.1 + J)) +
      ip2 (a2F1 χ e (J, z, w)) (fun c c' => (w : ℂ) * cvE b E c c' (z.1 + J)) -
      (w : ℂ) * lam1 χ b E e (J, z) = (w : ℂ) ^ 2 * gam1 χ b E e (J, z) := by
  simp only [a1F1, a2F1, ip1_add, ip1_smul, ip2_add, ip2_smul, ip1_mul_right, ip2_mul_right,
    ip2_otm, ip1_vE, ip1_vD]
  simp only [a0F1, gam1, lam1, sc0, sk0, sk1, sk2, sl, sla, lamA, trDr, trCv, trTr]
  ring

end F1

/-!
## `fun2`
-/

section F2

variable (χ : ℝ → ℝ) (b E : ℝ) (e f : GIdx K np)

def a0F2 (p : GSt K np × ZSt K np × ℝ) : ℂ :=
  sc0 χ p * sk0 χ p * (-(sl p * sla χ b E p e * p.2.1.2.1 f) - sl p * sla χ b E p f * p.2.1.2.1 e +
    sl p ^ 2 * sla χ b E p e * sla χ b E p f)

def a1F2 (p : GSt K np × ZSt K np × ℝ) : GIdx K np → ℂ :=
  (sc0 χ p * sk0 χ p * (p.2.1.2.1 f - sl p * sla χ b E p f)) • vE e +
    (sc0 χ p * sk0 χ p * (p.2.1.2.1 e - sl p * sla χ b E p e)) • vE f +
    (sc0 χ p * sk1 χ p * (p.2.1.2.1 e * p.2.1.2.1 f) -
      sc0 χ p * sk1 χ p * sl p * (sla χ b E p e * p.2.1.2.1 f + sla χ b E p f * p.2.1.2.1 e)) • vD

def a2F2 (p : GSt K np × ZSt K np × ℝ) : GIdx K np → GIdx K np → ℂ :=
  (sc0 χ p * sk0 χ p) • otm (vE e) (vE f) + (sc0 χ p * sk1 χ p * p.2.1.2.1 f) • otm vD (vE e) +
    (sc0 χ p * sk1 χ p * p.2.1.2.1 e) • otm vD (vE f) +
    (sc0 χ p * sk2 χ p * (p.2.1.2.1 e * p.2.1.2.1 f) / 2) • otm vD vD

/-- The rest of `fun2`: `c₀ (χ' h ξ_e ξ_f + χ''/2 h² ΔP + ρ (P + ΔP))`. -/
def rest2 (c0 k1 k2 ρ h ξe ξf xe xf : ℂ) : ℂ :=
  c0 * (k1 * h * ξe * ξf + k2 / 2 * h ^ 2 * (ξe * xf + xe * ξf + ξe * ξf) +
    ρ * (xe * xf + (ξe * xf + xe * ξf + ξe * ξf)))

def gam2 (q : GSt K np × ZSt K np) : ℂ :=
  cutC χ q.2.2.2 * (cutC χ q.2.1 * (lamA χ b E e (q.1, q.2.1) * lamA χ b E f (q.1, q.2.1) -
      lamA χ b E f (q.1, q.2.1) * drE b E e (q.2.1 + q.1) -
      lamA χ b E e (q.1, q.2.1) * drE b E f (q.2.1 + q.1)) -
    cutC (deriv χ) q.2.1 * (lamA χ b E e (q.1, q.2.1) * q.2.2.1 f +
      lamA χ b E f (q.1, q.2.1) * q.2.2.1 e) * trDr b E (q.2.1 + q.1))

theorem expand2 (J y' : GSt K np) (z : ZSt K np) (ℓ : ℝ)
    (hh : ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ)) :
    fun2 χ e f (nextZ χ b E J y' ℓ z) - fun2 χ e f z =
      a0F2 χ b E e f (J, z, ℓ) + ip1 (a1F2 χ b E e f (J, z, ℓ)) (dlt z.1 y') +
        ip2 (a2F2 χ e f (J, z, ℓ)) (sq2 (dlt z.1 y')) +
        rest2 (cutC χ z.2.2) (cutC (deriv χ) z.1) (cutC (deriv (deriv χ)) z.1)
          (taylorRem χ (trRe z.1) (trRe y' - trRe z.1) : ℂ) (∑ k, dlt z.1 y' (0, k, k))
          (dlt z.1 y' e - (ℓ : ℂ) * lamA χ b E e (J, z.1))
          (dlt z.1 y' f - (ℓ : ℂ) * lamA χ b E f (J, z.1)) (z.2.1 e) (z.2.1 f) := by
  have hρ : χ (trRe y') = χ (trRe z.1) + deriv χ (trRe z.1) * (trRe y' - trRe z.1) +
      deriv (deriv χ) (trRe z.1) * (trRe y' - trRe z.1) ^ 2 / 2 +
      taylorRem χ (trRe z.1) (trRe y' - trRe z.1) := by
    simp only [taylorRem, add_sub_cancel]; ring
  simp only [a1F2, a2F2, ip1_add, ip1_smul, ip2_add, ip2_smul, ip2_otm_sq2, ip1_vE, ip1_vD]
  rw [hh]
  simp only [fun2, nextZ, a0F2, rest2, cutC, sc0, sk0, sk1, sk2, sl, sla]
  rw [hρ]
  push_cast
  ring

theorem gen2 (J : GSt K np) (z : ZSt K np) (w : ℝ) :
    a0F2 χ b E e f (J, z, w) +
      ip1 (a1F2 χ b E e f (J, z, w)) (fun c => (w : ℂ) * drE b E c (z.1 + J)) +
      ip2 (a2F2 χ e f (J, z, w)) (fun c c' => (w : ℂ) * cvE b E c c' (z.1 + J)) -
      (w : ℂ) * lam2 χ b E e f (J, z) = (w : ℂ) ^ 2 * gam2 χ b E e f (J, z) := by
  simp only [a1F2, a2F2, ip1_add, ip1_smul, ip2_add, ip2_smul, ip1_mul_right, ip2_mul_right,
    ip2_otm, ip1_vE, ip1_vD]
  simp only [a0F2, gam2, lam2, sc0, sk0, sk1, sk2, sl, sla, lamA, trDr, trCv, trTr]
  ring

end F2

/-!
## Bounds on the rests
-/

section RestBounds

variable {c0 k1 k2 ρ h ξ ξe ξf x xe xf : ℂ} {M0 M1 M2 M B η : ℝ}

theorem norm_rest1_le (hc0 : ‖c0‖ ≤ M0) (hk2 : ‖k2‖ ≤ M2) (hρ2 : ‖ρ‖ ≤ M * η ^ 2)
    (hρ3 : ‖ρ‖ ≤ M * η ^ 3) (hh : ‖h‖ ≤ η) (hξ : ‖ξ‖ ≤ η) (hx : ‖x‖ ≤ B) (hM2 : 0 ≤ M2)
    (hM : 0 ≤ M) (hη : 0 ≤ η) :
    ‖rest1 c0 k2 ρ h ξ x‖ ≤ M0 * (M2 / 2 + M * B + M) * η ^ 3 := by
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans hc0
  have e1 : ‖k2 / 2 * h ^ 2 * ξ‖ ≤ M2 / 2 * η ^ 3 := by
    rw [norm_mul, norm_mul, norm_div, norm_pow]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    calc ‖k2‖ / 2 * ‖h‖ ^ 2 * ‖ξ‖ ≤ M2 / 2 * η ^ 2 * η := by gcongr
      _ = M2 / 2 * η ^ 3 := by ring
  have e2 : ‖ρ * (x + ξ)‖ ≤ M * η ^ 3 * B + M * η ^ 2 * η := by
    rw [norm_mul]
    calc ‖ρ‖ * ‖x + ξ‖ ≤ ‖ρ‖ * (‖x‖ + ‖ξ‖) := by gcongr; exact norm_add_le _ _
      _ = ‖ρ‖ * ‖x‖ + ‖ρ‖ * ‖ξ‖ := by ring
      _ ≤ M * η ^ 3 * B + M * η ^ 2 * η := by
        gcongr
  unfold rest1
  rw [norm_mul]
  calc ‖c0‖ * ‖k2 / 2 * h ^ 2 * ξ + ρ * (x + ξ)‖
      ≤ M0 * (M2 / 2 * η ^ 3 + (M * η ^ 3 * B + M * η ^ 2 * η)) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add e1 e2)
    _ = M0 * (M2 / 2 + M * B + M) * η ^ 3 := by ring

theorem norm_rest2_le (hc0 : ‖c0‖ ≤ M0) (hk1 : ‖k1‖ ≤ M1) (hk2 : ‖k2‖ ≤ M2)
    (hρ2 : ‖ρ‖ ≤ M * η ^ 2) (hρ3 : ‖ρ‖ ≤ M * η ^ 3) (hh : ‖h‖ ≤ η) (hξe : ‖ξe‖ ≤ η)
    (hξf : ‖ξf‖ ≤ η) (hxe : ‖xe‖ ≤ B) (hxf : ‖xf‖ ≤ B) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hη : 0 ≤ η) :
    ‖rest2 c0 k1 k2 ρ h ξe ξf xe xf‖ ≤
      M0 * ((M1 + M2 * B + M * B ^ 2 + 2 * M * B) * η ^ 3 + (M2 / 2 + M) * η ^ 4) := by
  have hM0 : 0 ≤ M0 := (norm_nonneg _).trans hc0
  have hdP : ‖ξe * xf + xe * ξf + ξe * ξf‖ ≤ 2 * B * η + η ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖ξe‖ * ‖xf‖ + ‖xe‖ * ‖ξf‖ + ‖ξe‖ * ‖ξf‖ ≤ η * B + B * η + η * η := by gcongr
      _ = 2 * B * η + η ^ 2 := by ring
  have hP : ‖xe * xf‖ ≤ B ^ 2 := by
    rw [norm_mul]; calc ‖xe‖ * ‖xf‖ ≤ B * B := by gcongr
      _ = B ^ 2 := by ring
  have e1 : ‖k1 * h * ξe * ξf‖ ≤ M1 * η ^ 3 := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖k1‖ * ‖h‖ * ‖ξe‖ * ‖ξf‖ ≤ M1 * η * η * η := by gcongr
      _ = M1 * η ^ 3 := by ring
  have e2 : ‖k2 / 2 * h ^ 2 * (ξe * xf + xe * ξf + ξe * ξf)‖ ≤
      M2 / 2 * η ^ 2 * (2 * B * η + η ^ 2) := by
    rw [norm_mul, norm_mul, norm_div, norm_pow]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    gcongr
  have e3 : ‖ρ * (xe * xf + (ξe * xf + xe * ξf + ξe * ξf))‖ ≤
      M * η ^ 3 * B ^ 2 + M * η ^ 2 * (2 * B * η + η ^ 2) := by
    rw [norm_mul]
    calc ‖ρ‖ * ‖xe * xf + (ξe * xf + xe * ξf + ξe * ξf)‖
        ≤ ‖ρ‖ * (‖xe * xf‖ + ‖ξe * xf + xe * ξf + ξe * ξf‖) := by
          gcongr; exact norm_add_le _ _
      _ = ‖ρ‖ * ‖xe * xf‖ + ‖ρ‖ * ‖ξe * xf + xe * ξf + ξe * ξf‖ := by ring
      _ ≤ _ := by gcongr
  unfold rest2
  rw [norm_mul]
  calc _ ≤ M0 * (M1 * η ^ 3 + M2 / 2 * η ^ 2 * (2 * B * η + η ^ 2) +
        (M * η ^ 3 * B ^ 2 + M * η ^ 2 * (2 * B * η + η ^ 2))) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add e1 e2)) e3)
    _ = _ := by ring

end RestBounds

/-!
## Packaging for a generator pair
-/

theorem norm_sum_diag_le (δ : GIdx K np → ℂ) : ‖∑ k, δ (0, k, k)‖ ≤ ∑ c, ‖δ c‖ := by
  refine (norm_sum_le _ _).trans ?_
  let ι : SrcCol K (Fin np) ↪ GIdx K np := ⟨fun k => (0, k, k), fun k k' h =>
    congrArg (fun c : GIdx K np => c.2.1) h⟩
  have : ∑ k, ‖δ (0, k, k)‖ = ∑ c ∈ Finset.univ.map ι, ‖δ c‖ := by
    rw [Finset.sum_map]; rfl
  rw [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => norm_nonneg _

@[fun_prop] theorem continuous_lamA' {χ : ℝ → ℝ} (hχ : Continuous χ) (b E : ℝ) (e : GIdx K np) :
    Continuous (lamA (K := K) (np := np) χ b E e) := by
  unfold lamA; fun_prop

/-- **The Taylor data of a generator pair `(F, Λ)`**: affine coefficients `a₀, a₁, a₂` of the
exact polynomial part, the rest bound, and the generator identity with the `w²` error `Γ`. -/
structure TaylorData (χ : ℝ → ℝ) (b E : ℝ) (F : ZSt K np → ℂ)
    (Λ : GSt K np × ZSt K np → ℂ) where
  a0 : GSt K np × ZSt K np × ℝ → ℂ
  a1 : GSt K np × ZSt K np × ℝ → GIdx K np → ℂ
  a2 : GSt K np × ZSt K np × ℝ → GIdx K np → GIdx K np → ℂ
  Γ : GSt K np × ZSt K np → ℂ
  ca0 : Continuous a0
  ca1 : ∀ c, Continuous fun p => a1 p c
  ca2 : ∀ c c', Continuous fun p => a2 p c c'
  cΓ : Continuous Γ
  rest : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ (J y' : GSt K np) (z : ZSt K np) (ℓ : ℝ),
    0 ≤ ℓ → (∀ e, ‖z.2.1 e‖ ≤ B) → (∀ e, ‖lamA χ b E e (J, z.1)‖ ≤ B) →
    ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ) →
    ‖F (nextZ χ b E J y' ℓ z) - F z - (a0 (J, z, ℓ) + ip1 (a1 (J, z, ℓ)) (dlt z.1 y') +
        ip2 (a2 (J, z, ℓ)) (sq2 (dlt z.1 y')))‖ ≤
      C * ((∑ c, ‖dlt z.1 y' c‖ + ℓ * B) ^ 3 + (∑ c, ‖dlt z.1 y' c‖ + ℓ * B) ^ 4)
  gen : ∀ (J : GSt K np) (z : ZSt K np) (w : ℝ),
    a0 (J, z, w) + ip1 (a1 (J, z, w)) (fun c => (w : ℂ) * drE b E c (z.1 + J)) +
      ip2 (a2 (J, z, w)) (fun c c' => (w : ℂ) * cvE b E c c' (z.1 + J)) -
      (w : ℂ) * Λ (J, z) = (w : ℂ) ^ 2 * Γ (J, z)

theorem norm_cutC_le {g : ℝ → ℝ} {M : ℝ} (hg : ∀ x, ‖g x‖ ≤ M) (y : GSt K np) :
    ‖cutC g y‖ ≤ M := by
  unfold cutC; rw [Complex.norm_real]; exact hg _

/-- **The Taylor data exist for every generator pair.** -/
theorem IsGenPair.taylorData {χ : ℝ → ℝ} {b E : ℝ} (h3 : ContDiff ℝ 3 χ)
    (hs : HasCompactSupport χ) {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ}
    (hp : Pass.IsGenPair χ b E F Λ) : Nonempty (TaylorData χ b E F Λ) := by
  obtain ⟨hc, hd, hdd⟩ := cut_continuity h3
  obtain ⟨M, hM, hTay⟩ := taylor_cut h3 hs
  obtain ⟨M0, hM0⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨M1, hM1⟩ := hd.bounded_above_of_compact_support hs.deriv
  obtain ⟨M2, hM2⟩ := hdd.bounded_above_of_compact_support hs.deriv.deriv
  have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hM2' : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0)
  have hM0' : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  -- the common bounds on `h`, `ξ`, `ρ`
  have key : ∀ (B : ℝ), 0 ≤ B → ∀ (J y' : GSt K np) (z : ZSt K np) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ e, ‖lamA χ b E e (J, z.1)‖ ≤ B) →
      ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ) →
      let η := ∑ c, ‖dlt z.1 y' c‖ + ℓ * B
      0 ≤ η ∧ ‖∑ k, dlt z.1 y' (0, k, k)‖ ≤ η ∧
      (∀ e, ‖dlt z.1 y' e - (ℓ : ℂ) * lamA χ b E e (J, z.1)‖ ≤ η) ∧
      ‖(taylorRem χ (trRe z.1) (trRe y' - trRe z.1) : ℂ)‖ ≤ M * η ^ 2 ∧
      ‖(taylorRem χ (trRe z.1) (trRe y' - trRe z.1) : ℂ)‖ ≤ M * η ^ 3 := by
    intro B hB J y' z ℓ hℓ hla hh η
    have hη0 : 0 ≤ η := add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (mul_nonneg hℓ hB)
    have hhη : ‖∑ k, dlt z.1 y' (0, k, k)‖ ≤ η :=
      (norm_sum_diag_le _).trans (le_add_of_nonneg_right (mul_nonneg hℓ hB))
    have habs : |trRe y' - trRe z.1| ≤ η := by
      rw [hh, Complex.norm_real, Real.norm_eq_abs] at hhη; exact hhη
    refine ⟨hη0, hhη, fun e => ?_, ?_, ?_⟩
    · refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · exact Finset.single_le_sum (f := fun c => ‖dlt z.1 y' c‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ e)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hℓ]
        exact mul_le_mul_of_nonneg_left (hla e) hℓ
    · rw [Complex.norm_real, Real.norm_eq_abs]
      refine (hTay _ _).1.trans (mul_le_mul_of_nonneg_left ?_ hM)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hTay _ _).2.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) habs 3) hM)
  rcases hp with ⟨e, rfl, rfl⟩ | ⟨e, f, rfl, rfl⟩
  · refine ⟨⟨a0F1 χ b E e, a1F1 χ b E e, a2F1 χ e, gam1 χ b E e, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · unfold a0F1; fun_prop
    · intro c; unfold a1F1; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop
    · intro c c'; unfold a2F1; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop
    · unfold gam1; fun_prop
    · intro B hB
      refine ⟨M0 * (M2 / 2 + M * B + M), by positivity, fun J y' z ℓ hℓ hx hla hh => ?_⟩
      obtain ⟨hη0, hhη, hξ, hρ2, hρ3⟩ := key B hB J y' z ℓ hℓ hla hh
      rw [expand1 χ b E e J y' z ℓ hh, add_sub_cancel_left]
      refine (norm_rest1_le (norm_cutC_le hM0 _) (norm_cutC_le hM2 _) hρ2 hρ3 hhη (hξ e) (hx e)
        hM2' hM hη0).trans ?_
      have h4 : 0 ≤ (∑ c, ‖dlt z.1 y' c‖ + ℓ * B) ^ 4 := pow_nonneg hη0 4
      nlinarith [mul_nonneg (by positivity : 0 ≤ M0 * (M2 / 2 + M * B + M)) h4]
    · intro J z w; exact gen1 χ b E e J z w
  · refine ⟨⟨a0F2 χ b E e f, a1F2 χ b E e f, a2F2 χ e f, gam2 χ b E e f, ?_, ?_, ?_, ?_, ?_,
      ?_⟩⟩
    · unfold a0F2; fun_prop
    · intro c; unfold a1F2; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop
    · intro c c'; unfold a2F2; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop
    · unfold gam2; fun_prop
    · intro B hB
      refine ⟨M0 * ((M1 + M2 * B + M * B ^ 2 + 2 * M * B) + (M2 / 2 + M)), by positivity,
        fun J y' z ℓ hℓ hx hla hh => ?_⟩
      obtain ⟨hη0, hhη, hξ, hρ2, hρ3⟩ := key B hB J y' z ℓ hℓ hla hh
      rw [expand2 χ b E e f J y' z ℓ hh, add_sub_cancel_left]
      refine (norm_rest2_le (norm_cutC_le hM0 _) (norm_cutC_le hM1 _) (norm_cutC_le hM2 _) hρ2
        hρ3 hhη (hξ e) (hξ f) (hx e) (hx f) hM1' hM2' hM hB hη0).trans ?_
      have h3' : 0 ≤ (∑ c, ‖dlt z.1 y' c‖ + ℓ * B) ^ 3 := pow_nonneg hη0 3
      have h4 : 0 ≤ (∑ c, ‖dlt z.1 y' c‖ + ℓ * B) ^ 4 := pow_nonneg hη0 4
      have hA : 0 ≤ M1 + M2 * B + M * B ^ 2 + 2 * M * B := by positivity
      have hB' : 0 ≤ M2 / 2 + M := by positivity
      nlinarith [mul_nonneg (mul_nonneg hM0' hA) h4, mul_nonneg (mul_nonneg hM0' hB') h3']
    · intro J z w; exact gen2 χ b E e f J z w

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
