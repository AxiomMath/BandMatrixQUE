module

public import BlockBand.SourceProcess.ContractingWords.PosCovExp

/-!
# Reassembling contracted tensors through matrix units

`E_{ab}` is the matrix unit. With `ct = crossedTensor` (`(v₁*Gv₄)(v₃*Hv₂)`):
* `crossedTensor_units`: `ct(v₁,v₂,v₃,v₄,G,H) = Σ_{abcd} G_{ad}H_{cb}(v₁*E_{ab}v₂)(v₃*E_{cd}v₄)`;
* `pair_units`: `Σ_l c_l ct(x_{lp},y_{lp},x_{lq},y_{lq},G,H) Π_{others} x*σy
  = Σ_{abcd} G_{ad}H_{cb} posTr A (pw σ U {p,q})`, `U_p = E_{ab}`, `U_q = E_{cd}` (`p ≠ q`);
* `cross_units`: the same for two words, `= Σ G_{ad}H_{cb} posTr A(⋯E_{ab}⋯) posTr A'(⋯E_{cd}⋯)`;
* `trace_pair_units`: `Σ G_{ad}H_{cb} Tr(M E_{ab} N E_{cd}) = Tr(MG)Tr(NH)`;
* `trace_cross_units`: `Σ G_{ad}H_{cb} Tr(M E_{ab}) Tr(N E_{cd}) = Tr(MGNH)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix unit `E_{ab}`. -/
abbrev unitM (a b : n) : Matrix n n ℂ := Matrix.single a b 1

theorem bilinear_unitM (u v : n → ℂ) (a b : n) :
    bilinear u (unitM a b) v = star (u a) * v b := by
  rw [bilinear, unitM, Matrix.single_mulVec_eq]
  simp [dotProduct, Pi.single_apply]

omit [DecidableEq n] in
/-- Moving an outer sum inside four sums. -/
theorem sum_comm4 {α : Type*} [Fintype α] (f : α → n → n → n → n → ℂ) :
    ∑ l, ∑ a, ∑ b, ∑ c, ∑ d, f l a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ l, f l a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq n] in
/-- `Σ_c Σ_b Σ_a Σ_d f = Σ_b Σ_c Σ_d Σ_a f`. -/
theorem sum_perm4 (f : n → n → n → n → ℂ) :
    ∑ c, ∑ b, ∑ a, ∑ d, f c b a d = ∑ b, ∑ c, ∑ d, ∑ a, f c b a d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- `ct(v₁,v₂,v₃,v₄,G,H) = Σ_{c,b,a,d} G_{ad}H_{cb}(v₁*E_{ab}v₂)(v₃*E_{cd}v₄)`. -/
theorem crossedTensor_units (v₁ v₂ v₃ v₄ : n → ℂ) (G H : Matrix n n ℂ) :
    crossedTensor v₁ v₂ v₃ v₄ G H = ∑ c, ∑ b, ∑ a, ∑ d,
      G a d * H c b * (bilinear v₁ (unitM a b) v₂ * bilinear v₃ (unitM c d) v₄) := by
  simp only [bilinear_unitM]
  simp only [crossedTensor, bilinear, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by ring

variable {r r' : ℕ} {A : Fin r → Matrix n n ℂ} {A' : Fin r' → Matrix n n ℂ} {ι ι' : Type}
  [Fintype ι] [Fintype ι'] {c : ι → ℂ} {c' : ι' → ℂ} {x y : ι → Fin r → n → ℂ}
  {x' y' : ι' → Fin r' → n → ℂ}

/-- Two matrix units at the positions `p ≠ q`. -/
def units2 {r : ℕ} (p q : Fin r) (a b c d : n) : Fin r → Matrix n n ℂ :=
  Function.update (Function.update (fun _ => 0) p (unitM a b)) q (unitM c d)

/-- One matrix unit at the position `p`. -/
def units1 {r : ℕ} (p : Fin r) (a b : n) : Fin r → Matrix n n ℂ :=
  Function.update (fun _ => 0) p (unitM a b)

theorem pair_units (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (σ : Fin r → Matrix n n ℂ) {p q : Fin r} (hpq : p ≠ q) (G H : Matrix n n ℂ) :
    ∑ l, c l * (crossedTensor (x l p) (y l p) (x l q) (y l q) G H *
        ∏ i ∈ Finset.univ \ {p, q}, bilinear (x l i) (σ i) (y l i)) =
      ∑ c₁, ∑ b, ∑ a, ∑ d, G a d * H c₁ b * posTr A (pw σ (units2 p q a b c₁ d) {p, q}) := by
  simp only [posTr_pw hrep, Finset.prod_pair hpq, units2, Function.update_self,
    Function.update_of_ne hpq, crossedTensor_units, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm4]
  exact Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun l _ => by ring

theorem cross_units (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (hrep' : ∀ T, posTr A' T = ∑ l, c' l * ∏ p, bilinear (x' l p) (T p) (y' l p))
    (σ : Fin r → Matrix n n ℂ) (σ' : Fin r' → Matrix n n ℂ) (p : Fin r) (q : Fin r')
    (G H : Matrix n n ℂ) :
    ∑ l, ∑ l', c l * c' l' * (crossedTensor (x l p) (y l p) (x' l' q) (y' l' q) G H *
        ((∏ i ∈ Finset.univ \ {p}, bilinear (x l i) (σ i) (y l i)) *
          ∏ i ∈ Finset.univ \ {q}, bilinear (x' l' i) (σ' i) (y' l' i))) =
      ∑ c₁, ∑ b, ∑ a, ∑ d, G a d * H c₁ b *
        (posTr A (pw σ (units1 p a b) {p}) * posTr A' (pw σ' (units1 q c₁ d) {q})) := by
  rw [← Fintype.sum_prod_type']
  simp only [crossedTensor_units, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm4]
  refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  rw [posTr_pw hrep, posTr_pw hrep', Finset.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  simp only [Finset.prod_singleton, units1, Function.update_self]
  ring

theorem trace_unitM_mul (M : Matrix n n ℂ) (a b : n) : (M * unitM a b).trace = M b a := by
  rw [unitM, Matrix.trace_mul_single]; simp

theorem trace_pair_units (M N G H : Matrix n n ℂ) :
    ∑ c, ∑ b, ∑ a, ∑ d, G a d * H c b * (M * unitM a b * N * unitM c d).trace =
      (M * G).trace * (N * H).trace := by
  have e : ∀ a b c d, (M * unitM a b * N * unitM c d).trace = N b c * M d a := fun a b c d => by
    rw [unitM, unitM, Matrix.trace_mul_single]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
    ring
  simp only [e]
  rw [sum_perm4]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => by ring

theorem trace_cross_units (M N G H : Matrix n n ℂ) :
    ∑ c, ∑ b, ∑ a, ∑ d, G a d * H c b * ((M * unitM a b).trace * (N * unitM c d).trace) =
      (M * G * N * H).trace := by
  simp only [trace_unitM_mul]
  rw [sum_perm4]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => by ring

end BlockBand.SourceProcess.ContractingWords
